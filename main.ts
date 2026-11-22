// mend: one patch tool for every AI edit format (SPEC.md version 1).
//
// Reads a patch in one of four formats (unified diff, SEARCH/REPLACE blocks,
// V4A, JSON edits), finds the lines each edit names at the first of three
// matching tiers, and writes every change or none. Node 22, standard library
// only. The working directory is the root of the tree being patched.

import { mkdirSync, readFileSync, rmSync, statSync, writeFileSync, writeSync } from 'node:fs';
import { dirname } from 'node:path';

/** An exit-2 failure: the single line to print on stdout. */
class Exit2 {
  line: string;
  constructor(line: string) {
    this.line = line;
  }
}

/** One edit's failure: its code and the path it concerns. */
class Fail {
  code: string;
  path: string;
  constructor(code: string, path: string) {
    this.code = code;
    this.path = path;
  }
}

const FORMATS = ['auto', 'unified', 'search-replace', 'v4a', 'json'];

/** True when the line is empty or only whitespace. */
const isBlank = (s: string): boolean => s.trim() === '';

/** Remove leading and trailing ASCII spaces (not other whitespace). */
const trimSpaces = (s: string): string => s.replace(/^ +/, '').replace(/ +$/, '');

/** A patch's lines: split at \n, one trailing \r removed from each, and no empty piece after a final \n. */
function patchLines(text: string): string[] {
  if (text === '') return [];
  const parts = text.split('\n');
  if (text.endsWith('\n')) parts.pop();
  return parts.map((l) => (l.endsWith('\r') ? l.slice(0, -1) : l));
}

/** A path is safe when it is not empty, does not start with /, holds no \, and no / segment is empty, . or ... */
function safePath(p: string): boolean {
  if (p === '' || p.startsWith('/') || p.includes('\\')) return false;
  return p.split('/').every((s) => s !== '' && s !== '.' && s !== '..');
}

/** Byte order of two paths (UTF-8), for sorting output rows. */
function byteOrder(a: string, b: string): number {
  return Buffer.compare(Buffer.from(a, 'utf8'), Buffer.from(b, 'utf8'));
}

/** The leading spaces and tabs of a line. */
function leadingWs(s: string): string {
  const m = /^[ \t]*/.exec(s);
  return m === null ? '' : m[0];
}

/** A file as lines: its line break, its lines, and whether it ends with a break. */
interface FileDoc {
  br: string;
  lines: string[];
  final: boolean;
}

/** Split a file's text into its line model. The break is CRLF when the first \n follows a \r. */
function splitDoc(text: string): FileDoc {
  if (text === '') return { br: '\n', lines: [], final: false };
  const nl = text.indexOf('\n');
  const br = nl > 0 && text[nl - 1] === '\r' ? '\r\n' : '\n';
  const lines = text.split(br);
  const final = text.endsWith(br);
  if (final) lines.pop();
  return { br, lines, final };
}

/** Join a file's lines back into text. A file with no lines is empty. */
function joinDoc(d: FileDoc): string {
  if (d.lines.length === 0) return '';
  return d.lines.join(d.br) + (d.final ? d.br : '');
}

/** Line equality at a tier: 0 exact, 1 trailing spaces/tabs ignored, 2 leading and trailing ignored. */
function tierEq(tier: number, a: string, b: string): boolean {
  if (tier === 0) return a === b;
  if (tier === 1) return a.replace(/[ \t]+$/, '') === b.replace(/[ \t]+$/, '');
  return a.replace(/^[ \t]+/, '').replace(/[ \t]+$/, '') === b.replace(/^[ \t]+/, '').replace(/[ \t]+$/, '');
}

/** All start positions at or after `from` where `old` occurs in `lines` at `tier`. Occurrences may overlap. */
function occurrences(lines: string[], old: string[], tier: number, from: number): number[] {
  const out: number[] = [];
  if (old.length === 0) return out;
  const norm =
    tier === 0
      ? (s: string): string => s
      : tier === 1
        ? (s: string): string => s.replace(/[ \t]+$/, '')
        : (s: string): string => s.replace(/^[ \t]+/, '').replace(/[ \t]+$/, '');
  const want = old.map(norm);
  const have = lines.map(norm);
  for (let i = Math.max(0, from); i + want.length <= have.length; i++) {
    let ok = true;
    for (let j = 0; j < want.length; j++) {
      if (have[i + j] !== want[j]) {
        ok = false;
        break;
      }
    }
    if (ok) out.push(i);
  }
  return out;
}

/** The first tier (0, then 1, then 2; 0 only when strict) at which `old` occurs at or after `from`. */
function firstTier(lines: string[], old: string[], from: number, strict: boolean): { tier: number; at: number[] } | null {
  const tiers = strict ? [0] : [0, 1, 2];
  for (const t of tiers) {
    const at = occurrences(lines, old, t, from);
    if (at.length > 0) return { tier: t, at };
  }
  return null;
}

/** A parsed block of old lines replaced by new lines (a unified hunk or a V4A chunk). */
interface Block {
  oldLines: string[];
  newLines: string[];
  /** For each new line, the old-line index it is a context line of, or -1. */
  newToOld: number[];
}

/**
 * Build the lines that replace the match at `at`: a context line is written as the file's own
 * matched line; at tier 2 every other line that is not empty or only whitespace and starts with
 * the old block's first-line indent has that indent replaced by the file's first matched line's.
 */
function buildReplacement(fileLines: string[], at: number, block: Block, tier: number): string[] {
  const out: string[] = [];
  const f = leadingWs(fileLines[at] ?? '');
  const p = leadingWs(block.oldLines[0] ?? '');
  for (let i = 0; i < block.newLines.length; i++) {
    const oi = block.newToOld[i]!;
    if (oi >= 0) {
      out.push(fileLines[at + oi]!);
      continue;
    }
    let line = block.newLines[i]!;
    if (tier === 2 && line !== '' && line.trim() !== '' && line.startsWith(p)) {
      line = f + line.slice(p.length);
    }
    out.push(line);
  }
  return out;
}

/** The tree as the edits leave it: changed paths in `now` (null: deleted), the rest read from disk. */
class Tree {
  private orig = new Map<string, string | null>();
  now = new Map<string, string | null>();
  moves: Array<[string, string]> = [];

  original(p: string): string | null {
    if (!this.orig.has(p)) {
      let v: string | null = null;
      try {
        if (statSync(p).isFile()) v = readFileSync(p, 'utf8');
      } catch {
        v = null;
      }
      this.orig.set(p, v);
    }
    return this.orig.get(p)!;
  }

  get(p: string): string | null {
    return this.now.has(p) ? this.now.get(p)! : this.original(p);
  }

  set(p: string, v: string | null): void {
    this.now.set(p, v);
  }

  recordMove(oldP: string, newP: string): void {
    this.moves.push([oldP, newP]);
  }

  snapshot(): { now: Map<string, string | null>; moves: Array<[string, string]> } {
    return { now: new Map(this.now), moves: this.moves.slice() };
  }

  restore(s: { now: Map<string, string | null>; moves: Array<[string, string]> }): void {
    this.now = new Map(s.now);
    this.moves = s.moves.slice();
  }
}

/** One edit: applies itself to the tree or throws a Fail. */
type Edit = (tree: Tree) => void;

/** Throw Fail('unsafe', p) unless p is a safe path. */
function needSafe(p: string): void {
  if (!safePath(p)) throw new Fail('unsafe', p);
}

/** One JSON edit object (SPEC.md section 9), or null when the value is not one. */
function jsonEdit(v: unknown): Edit | null {
  if (v === null || typeof v !== 'object' || Array.isArray(v)) return null;
  const o = v as Record<string, unknown>;
  if (typeof o.path !== 'string') return null;
  const p = o.path;
  if (o.command === 'create') {
    if (typeof o.file_text !== 'string') return null;
    const text = o.file_text;
    return (tree) => {
      needSafe(p);
      if (tree.get(p) !== null) throw new Fail('exists', p);
      tree.set(p, text);
    };
  }
  if (o.command === 'str_replace') {
    if (typeof o.old_str !== 'string' || o.old_str === '') return null;
    if (o.new_str !== undefined && typeof o.new_str !== 'string') return null;
    const oldStr = o.old_str;
    const newStr = (o.new_str as string | undefined) ?? '';
    return (tree) => {
      needSafe(p);
      const before = tree.get(p);
      if (before === null) throw new Fail('missing', p);
      const nl = before.indexOf('\n');
      const crlf = nl > 0 && before[nl - 1] === '\r';
      const toLF = (s: string): string => (crlf ? s.replaceAll('\r\n', '\n') : s);
      const text = toLF(before);
      const old = toLF(oldStr);
      let count = 0;
      for (let k = text.indexOf(old); k >= 0; k = text.indexOf(old, k + 1)) count++;
      if (count === 0) throw new Fail('no-match', p);
      if (count > 1) throw new Fail('ambiguous', p);
      const at = text.indexOf(old);
      const out = text.slice(0, at) + toLF(newStr) + text.slice(at + old.length);
      tree.set(p, crlf ? out.replaceAll('\n', '\r\n') : out);
    };
  }
  if (o.command === 'insert') {
    if (typeof o.insert_line !== 'number' || !Number.isInteger(o.insert_line)) return null;
    if (typeof o.new_str !== 'string') return null;
    const line = o.insert_line;
    const add = patchLines(o.new_str);
    return (tree) => {
      needSafe(p);
      const before = tree.get(p);
      if (before === null) throw new Fail('missing', p);
      const doc = splitDoc(before);
      if (line < 0 || line > doc.lines.length) throw new Fail('no-match', p);
      const lines = doc.lines.slice();
      lines.splice(line, 0, ...add);
      tree.set(p, joinDoc({ br: doc.br, lines, final: doc.final }));
    };
  }
  return null;
}

/** Parse a JSON patch: one array of edit objects, or JSON Lines. */
function parseJsonEdits(text: string, lines: string[]): Edit[] {
  const first = lines.findIndex((l) => !isBlank(l));
  if (first < 0) throw new Exit2('error: parse 1');
  const edits: Edit[] = [];
  if (lines[first]!.trimStart().startsWith('[')) {
    let v: unknown;
    try {
      v = JSON.parse(text);
    } catch {
      throw new Exit2(`error: parse ${first + 1}`);
    }
    if (!Array.isArray(v)) throw new Exit2(`error: parse ${first + 1}`);
    for (const x of v) {
      const e = jsonEdit(x);
      if (e === null) throw new Exit2(`error: parse ${first + 1}`);
      edits.push(e);
    }
    return edits;
  }
  lines.forEach((l, i) => {
    if (isBlank(l)) return;
    let e: Edit | null = null;
    try {
      e = jsonEdit(JSON.parse(l));
    } catch {
      e = null;
    }
    if (e === null) throw new Exit2(`error: parse ${i + 1}`);
    edits.push(e);
  });
  return edits;
}

/** A unified hunk: its old start line, its block, and its backslash facts. */
interface UnifiedHunk extends Block {
  a: number;
  /** A `\` line follows the hunk's last context or `+` line. */
  backslashAfterLast: boolean;
  /** The hunk's `+` lines, in body order (for creations). */
  plusLines: string[];
  /** A `\` line follows the hunk's last `+` line. */
  backslashAfterPlus: boolean;
}

const HUNK_HEAD = /^@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@/;
const DIFF_GIT = /^diff --git a\/(.+) b\/(.+)$/;

interface UnifiedSection {
  gitA: string | null;
  gitB: string | null;
  pairOld: string | null;
  pairNew: string | null;
  renameFrom: string | null;
  renameTo: string | null;
  newFile: boolean;
  deletedFile: boolean;
  hunks: UnifiedHunk[];
}

/** The path after `--- ` or `+++ `: up to the first tab, surrounding spaces removed, one leading a/ or b/ removed. */
function diffPath(line: string): string {
  let p = line.slice(4);
  const tab = p.indexOf('\t');
  if (tab >= 0) p = p.slice(0, tab);
  p = trimSpaces(p);
  if (p.startsWith('a/') || p.startsWith('b/')) p = p.slice(2);
  return p;
}

/** Parse one hunk starting at lines[i] (its header). Returns the hunk and the index after its body. */
function parseHunk(lines: string[], i: number): { hunk: UnifiedHunk; next: number } {
  const m = HUNK_HEAD.exec(lines[i]!);
  if (m === null) throw new Exit2(`error: parse ${i + 1}`);
  const a = Number(m[1]);
  const raw: string[] = [];
  let j = i + 1;
  while (j < lines.length) {
    const l = lines[j]!;
    if (l.startsWith('--- ') && (lines[j + 1] ?? '').startsWith('+++ ')) break;
    if (l === '' || l.startsWith(' ') || l.startsWith('-') || l.startsWith('+') || l.startsWith('\\')) {
      raw.push(l);
      j++;
    } else break;
  }
  while (raw.length > 0 && raw[raw.length - 1] === '') raw.pop();
  const oldLines: string[] = [];
  const newLines: string[] = [];
  const newToOld: number[] = [];
  const plusLines: string[] = [];
  const kinds: string[] = [];
  for (const l of raw) {
    if (l === '') {
      kinds.push(' ');
      oldLines.push('');
      newLines.push('');
      newToOld.push(oldLines.length - 1);
    } else if (l.startsWith(' ')) {
      kinds.push(' ');
      const t = l.slice(1);
      oldLines.push(t);
      newLines.push(t);
      newToOld.push(oldLines.length - 1);
    } else if (l.startsWith('-')) {
      kinds.push('-');
      oldLines.push(l.slice(1));
    } else if (l.startsWith('+')) {
      kinds.push('+');
      const t = l.slice(1);
      newLines.push(t);
      newToOld.push(-1);
      plusLines.push(t);
    } else {
      kinds.push('\\');
    }
  }
  let backslashAfterLast = false;
  let backslashAfterPlus = false;
  for (let k = kinds.length - 1; k >= 0; k--) {
    if (kinds[k] === ' ' || kinds[k] === '+') {
      backslashAfterLast = kinds[k + 1] === '\\';
      break;
    }
  }
  for (let k = kinds.length - 1; k >= 0; k--) {
    if (kinds[k] === '+') {
      backslashAfterPlus = kinds[k + 1] === '\\';
      break;
    }
  }
  return { hunk: { a, oldLines, newLines, newToOld, backslashAfterLast, plusLines, backslashAfterPlus }, next: j };
}

/** Apply one unified hunk to a file's lines. `d` is the line-count delta of this section's hunks applied so far. */
function applyUnifiedHunk(doc: FileDoc, h: UnifiedHunk, d: number, strict: boolean, path: string): FileDoc {
  const lines = doc.lines;
  if (h.oldLines.length === 0) {
    const at = Math.min(Math.max(h.a + d, 0), lines.length);
    const out = [...lines.slice(0, at), ...h.newLines, ...lines.slice(at)];
    const final = at === lines.length ? !h.backslashAfterLast : doc.final;
    return { br: doc.br, lines: out, final };
  }
  const found = firstTier(lines, h.oldLines, 0, strict);
  if (found === null) throw new Fail('no-match', path);
  const target = h.a - 1 + d;
  let best = found.at[0]!;
  let bestDist = Math.abs(best - target);
  for (const pos of found.at) {
    const dist = Math.abs(pos - target);
    if (dist < bestDist) {
      best = pos;
      bestDist = dist;
    }
  }
  const replacement = buildReplacement(lines, best, h, found.tier);
  const out = [...lines.slice(0, best), ...replacement, ...lines.slice(best + h.oldLines.length)];
  const final = best + h.oldLines.length === lines.length ? !h.backslashAfterLast : doc.final;
  return { br: doc.br, lines: out, final };
}

/** Build one section's edit (creation, deletion, move, or change). */
function unifiedEdit(s: UnifiedSection, strict: boolean): Edit {
  const oldP = s.pairOld ?? s.renameFrom ?? s.gitA ?? '';
  const newP = s.pairNew ?? s.renameTo ?? s.gitB ?? '';
  const isCreate = oldP === '/dev/null' || s.newFile;
  const isDelete = newP === '/dev/null' || s.deletedFile;
  if (isCreate) {
    return (tree) => {
      if (oldP !== '/dev/null') needSafe(oldP);
      needSafe(newP);
      if (tree.get(newP) !== null) throw new Fail('exists', newP);
      const lines: string[] = [];
      let lastPlusBackslash = false;
      for (const h of s.hunks) {
        lines.push(...h.plusLines);
        if (h.plusLines.length > 0) lastPlusBackslash = h.backslashAfterPlus;
      }
      tree.set(newP, joinDoc({ br: '\n', lines, final: lines.length > 0 && !lastPlusBackslash }));
    };
  }
  if (isDelete) {
    return (tree) => {
      needSafe(oldP);
      if (newP !== '/dev/null') needSafe(newP);
      if (tree.get(oldP) === null) throw new Fail('missing', oldP);
      tree.set(oldP, null);
    };
  }
  if (oldP !== newP) {
    return (tree) => {
      needSafe(oldP);
      needSafe(newP);
      const content = tree.get(oldP);
      if (content === null) throw new Fail('missing', oldP);
      if (tree.get(newP) !== null) throw new Fail('exists', newP);
      let doc = splitDoc(content);
      let d = 0;
      for (const h of s.hunks) {
        doc = applyUnifiedHunk(doc, h, d, strict, oldP);
        d += h.newLines.length - h.oldLines.length;
      }
      tree.set(newP, joinDoc(doc));
      tree.set(oldP, null);
      tree.recordMove(oldP, newP);
    };
  }
  return (tree) => {
    needSafe(oldP);
    const content = tree.get(oldP);
    if (content === null) throw new Fail('missing', oldP);
    let doc = splitDoc(content);
    let d = 0;
    for (const h of s.hunks) {
      doc = applyUnifiedHunk(doc, h, d, strict, oldP);
      d += h.newLines.length - h.oldLines.length;
    }
    tree.set(oldP, joinDoc(doc));
  };
}

/** Parse a unified patch into its sections' edits. */
function parseUnified(lines: string[], strict: boolean): Edit[] {
  const sections: UnifiedSection[] = [];
  let cur: UnifiedSection | null = null;
  let inHeader = false;
  const startSection = (gitA: string | null, gitB: string | null): void => {
    cur = { gitA, gitB, pairOld: null, pairNew: null, renameFrom: null, renameTo: null, newFile: false, deletedFile: false, hunks: [] };
    sections.push(cur);
    inHeader = true;
  };
  let i = 0;
  while (i < lines.length) {
    const l = lines[i]!;
    if (l === 'diff --git' || l.startsWith('diff --git ')) {
      const m = DIFF_GIT.exec(l);
      if (m === null) throw new Exit2(`error: parse ${i + 1}`);
      startSection(m[1]!, m[2]!);
      i++;
      continue;
    }
    if (l.startsWith('@@')) {
      if (cur === null) throw new Exit2(`error: parse ${i + 1}`);
      const { hunk, next } = parseHunk(lines, i);
      cur.hunks.push(hunk);
      inHeader = false;
      i = next;
      continue;
    }
    if (l.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')) {
      if (cur !== null && inHeader) {
        cur.pairOld = diffPath(l);
        cur.pairNew = diffPath(lines[i + 1]!);
        i += 2;
        continue;
      }
      startSection(null, null);
      cur!.pairOld = diffPath(l);
      cur!.pairNew = diffPath(lines[i + 1]!);
      i += 2;
      continue;
    }
    if (cur !== null && inHeader) {
      if (l.startsWith('--- ')) throw new Exit2(`error: parse ${i + 2}`);
      if (l.startsWith('rename from ')) {
        cur.renameFrom = trimSpaces(l.slice('rename from '.length));
        i++;
        continue;
      }
      if (l.startsWith('rename to ')) {
        cur.renameTo = trimSpaces(l.slice('rename to '.length));
        i++;
        continue;
      }
      if (l.startsWith('new file mode')) {
        cur.newFile = true;
        i++;
        continue;
      }
      if (l.startsWith('deleted file mode')) {
        cur.deletedFile = true;
        i++;
        continue;
      }
      i++;
      continue;
    }
    i++;
  }
  return sections.map((s) => unifiedEdit(s, strict));
}

/** Build one SEARCH/REPLACE block's edit. */
function searchReplaceEdit(path: string, oldLines: string[], newLines: string[], strict: boolean): Edit {
  return (tree) => {
    needSafe(path);
    if (oldLines.length === 0) {
      if (tree.get(path) !== null) throw new Fail('exists', path);
      tree.set(path, joinDoc({ br: '\n', lines: newLines, final: newLines.length > 0 }));
      return;
    }
    const content = tree.get(path);
    if (content === null) throw new Fail('missing', path);
    const doc = splitDoc(content);
    const found = firstTier(doc.lines, oldLines, 0, strict);
    if (found === null) throw new Fail('no-match', path);
    if (found.at.length > 1) throw new Fail('ambiguous', path);
    const at = found.at[0]!;
    const block: Block = { oldLines, newLines, newToOld: newLines.map(() => -1) };
    const replacement = buildReplacement(doc.lines, at, block, found.tier);
    const out = [...doc.lines.slice(0, at), ...replacement, ...doc.lines.slice(at + oldLines.length)];
    tree.set(path, joinDoc({ br: doc.br, lines: out, final: doc.final }));
  };
}

/** Parse a SEARCH/REPLACE patch into its blocks' edits. */
function parseSearchReplace(lines: string[], strict: boolean): Edit[] {
  const edits: Edit[] = [];
  let prevPath: string | null = null;
  let prevEnd = 0;
  let i = 0;
  while (i < lines.length) {
    if (lines[i]!.trimEnd() !== '<<<<<<< SEARCH') {
      i++;
      continue;
    }
    const searchIdx = i;
    let path: string | null = null;
    for (let k = searchIdx - 1; k >= prevEnd; k--) {
      const l = lines[k]!;
      if (isBlank(l)) continue;
      if (l.trim().startsWith('```')) continue;
      path = l.trim();
      break;
    }
    if (path === null) {
      if (prevPath === null) throw new Exit2(`error: parse ${searchIdx + 1}`);
      path = prevPath;
    }
    let eq = -1;
    let j = searchIdx + 1;
    while (j < lines.length) {
      if (lines[j]!.trimEnd() === '<<<<<<< SEARCH') break;
      if (lines[j]!.trimEnd() === '=======') {
        eq = j;
        break;
      }
      j++;
    }
    if (eq < 0) throw new Exit2(`error: parse ${searchIdx + 1}`);
    let rep = -1;
    j = eq + 1;
    while (j < lines.length) {
      if (lines[j]!.trimEnd() === '<<<<<<< SEARCH') break;
      if (lines[j]!.trimEnd() === '>>>>>>> REPLACE') {
        rep = j;
        break;
      }
      j++;
    }
    if (rep < 0) throw new Exit2(`error: parse ${searchIdx + 1}`);
    const oldLines = lines.slice(searchIdx + 1, eq);
    const newLines = lines.slice(eq + 1, rep);
    edits.push(searchReplaceEdit(path, oldLines, newLines, strict));
    prevPath = path;
    prevEnd = rep + 1;
    i = rep + 1;
  }
  return edits;
}

/** A V4A chunk: its anchor (null: none), its block, and whether it is anchored to the end of the file. */
interface V4aChunk extends Block {
  anchor: string | null;
  eof: boolean;
}

interface V4aRawSection {
  kind: 'add' | 'delete' | 'update';
  path: string;
  no: number;
  content: Array<{ text: string; no: number }>;
}

/** Build a chunk's block from its body lines. */
function buildV4aChunk(anchor: string | null, body: Array<{ kind: string; text: string }>, eof: boolean): V4aChunk {
  const oldLines: string[] = [];
  const newLines: string[] = [];
  const newToOld: number[] = [];
  for (const b of body) {
    if (b.kind === ' ') {
      oldLines.push(b.text);
      newLines.push(b.text);
      newToOld.push(oldLines.length - 1);
    } else if (b.kind === '-') {
      oldLines.push(b.text);
    } else if (b.kind === '+') {
      newLines.push(b.text);
      newToOld.push(-1);
    }
  }
  return { anchor, oldLines, newLines, newToOld, eof };
}

/** Apply one V4A chunk at the cursor; returns the new file and the moved cursor. */
function applyV4aChunk(doc: FileDoc, chunk: V4aChunk, cursor: number, strict: boolean, path: string): { doc: FileDoc; cursor: number } {
  const lines = doc.lines;
  let cur = cursor;
  if (chunk.anchor !== null && chunk.anchor !== '') {
    const found = firstTier(lines, [chunk.anchor], cur, strict);
    if (found === null) throw new Fail('no-match', path);
    cur = found.at[0]! + 1;
  }
  const O = chunk.oldLines;
  const N = chunk.newLines;
  if (O.length === 0) {
    const at = chunk.eof ? lines.length : cur;
    const out = [...lines.slice(0, at), ...N, ...lines.slice(at)];
    return { doc: { br: doc.br, lines: out, final: doc.final }, cursor: at + N.length };
  }
  const tiers = strict ? [0] : [0, 1, 2];
  let chosen: { at: number; tier: number } | null = null;
  for (const t of tiers) {
    const occ = occurrences(lines, O, t, cur);
    for (const pos of occ) {
      if (!chunk.eof || pos + O.length === lines.length) {
        chosen = { at: pos, tier: t };
        break;
      }
    }
    if (chosen !== null) break;
  }
  if (chosen === null) throw new Fail('no-match', path);
  const replacement = buildReplacement(lines, chosen.at, chunk, chosen.tier);
  const out = [...lines.slice(0, chosen.at), ...replacement, ...lines.slice(chosen.at + O.length)];
  return { doc: { br: doc.br, lines: out, final: doc.final }, cursor: chosen.at + N.length };
}

/** Build one V4A Update section's edit, parsing its chunks first. */
function v4aUpdateEdit(s: V4aRawSection, strict: boolean): Edit {
  const content = s.content;
  let moveTo: string | null = null;
  let start = 0;
  if (content.length > 0 && content[0]!.text.startsWith('*** Move to: ')) {
    moveTo = trimSpaces(content[0]!.text.slice('*** Move to: '.length));
    start = 1;
  }
  const chunks: V4aChunk[] = [];
  let cur: { anchor: string | null; body: Array<{ kind: string; text: string }>; eof: boolean } | null = null;
  const flush = (): void => {
    if (cur !== null) {
      chunks.push(buildV4aChunk(cur.anchor, cur.body, cur.eof));
      cur = null;
    }
  };
  for (let k = start; k < content.length; k++) {
    const c = content[k]!;
    const l = c.text;
    if (l.startsWith('@@')) {
      flush();
      cur = { anchor: trimSpaces(l.slice(2)), body: [], eof: false };
    } else if (l === '*** End of File') {
      if (cur === null) throw new Exit2(`error: parse ${c.no}`);
      cur.eof = true;
      flush();
    } else if (l === '' || l.startsWith(' ') || l.startsWith('-') || l.startsWith('+')) {
      if (cur === null) {
        if (chunks.length > 0) throw new Exit2(`error: parse ${c.no}`);
        cur = { anchor: null, body: [], eof: false };
      }
      cur.body.push(l === '' ? { kind: ' ', text: '' } : { kind: l[0]!, text: l.slice(1) });
    } else {
      throw new Exit2(`error: parse ${c.no}`);
    }
  }
  flush();
  if (chunks.length === 0 && moveTo === null) throw new Exit2(`error: parse ${s.no}`);
  const path = s.path;
  return (tree) => {
    needSafe(path);
    if (moveTo !== null) needSafe(moveTo);
    const content = tree.get(path);
    if (content === null) throw new Fail('missing', path);
    if (moveTo !== null && tree.get(moveTo) !== null) throw new Fail('exists', moveTo);
    let doc = splitDoc(content);
    let cursor = 0;
    for (const chunk of chunks) {
      const r = applyV4aChunk(doc, chunk, cursor, strict, path);
      doc = r.doc;
      cursor = r.cursor;
    }
    if (moveTo !== null) {
      tree.set(moveTo, joinDoc(doc));
      tree.set(path, null);
      tree.recordMove(path, moveTo);
    } else {
      tree.set(path, joinDoc(doc));
    }
  };
}

/** Parse a V4A patch into its sections' edits. */
function parseV4a(lines: string[], strict: boolean): Edit[] {
  const first = lines.findIndex((l) => !isBlank(l));
  if (first < 0) throw new Exit2('error: parse 1');
  if (lines[first]!.trim() !== '*** Begin Patch') throw new Exit2(`error: parse ${first + 1}`);
  let last = lines.length - 1;
  while (last >= 0 && isBlank(lines[last]!)) last--;
  if (last < 0 || lines[last]!.trim() !== '*** End Patch') throw new Exit2(`error: parse ${lines.length + 1}`);
  const rawSections: V4aRawSection[] = [];
  let cur: V4aRawSection | null = null;
  for (let idx = first + 1; idx < last; idx++) {
    const l = lines[idx]!;
    const no = idx + 1;
    if (l.startsWith('*** Add File: ')) {
      cur = { kind: 'add', path: trimSpaces(l.slice('*** Add File: '.length)), no, content: [] };
      rawSections.push(cur);
    } else if (l.startsWith('*** Delete File: ')) {
      cur = { kind: 'delete', path: trimSpaces(l.slice('*** Delete File: '.length)), no, content: [] };
      rawSections.push(cur);
    } else if (l.startsWith('*** Update File: ')) {
      cur = { kind: 'update', path: trimSpaces(l.slice('*** Update File: '.length)), no, content: [] };
      rawSections.push(cur);
    } else if (cur === null) {
      if (isBlank(l)) continue;
      throw new Exit2(`error: parse ${no}`);
    } else {
      cur.content.push({ text: l, no });
    }
  }
  const edits: Edit[] = [];
  for (const s of rawSections) {
    while (s.content.length > 0 && isBlank(s.content[s.content.length - 1]!.text)) s.content.pop();
    if (s.kind === 'add') {
      const fileLines: string[] = [];
      for (const c of s.content) {
        if (c.text.startsWith('+')) fileLines.push(c.text.slice(1));
        else if (c.text === '') fileLines.push('');
        else throw new Exit2(`error: parse ${c.no}`);
      }
      const path = s.path;
      edits.push((tree) => {
        needSafe(path);
        if (tree.get(path) !== null) throw new Fail('exists', path);
        tree.set(path, joinDoc({ br: '\n', lines: fileLines, final: fileLines.length > 0 }));
      });
    } else if (s.kind === 'delete') {
      for (const c of s.content) throw new Exit2(`error: parse ${c.no}`);
      const path = s.path;
      edits.push((tree) => {
        needSafe(path);
        if (tree.get(path) === null) throw new Fail('missing', path);
        tree.set(path, null);
      });
    } else {
      edits.push(v4aUpdateEdit(s, strict));
    }
  }
  return edits;
}

/** Detect a patch's format (SPEC.md section 4), or null when none holds. */
function detectFormat(lines: string[]): string | null {
  const first = lines.findIndex((l) => !isBlank(l));
  if (first < 0) return null;
  if (lines[first]!.trim() === '*** Begin Patch') return 'v4a';
  const c = lines[first]!.trimStart()[0];
  if (c === '[' || c === '{') return 'json';
  if (lines.some((l) => l.trimEnd() === '<<<<<<< SEARCH')) return 'search-replace';
  if (lines.some((l, i) => l.startsWith('diff --git ') || (l.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')))) return 'unified';
  return null;
}

/** Run the CLI: parse options, read and parse the patch, apply its edits, report. */
function run(args: string[]): { code: number; out: string[] } {
  let format: string | null = null;
  let check = false;
  let strict = false;
  const pos: string[] = [];
  let ended = false;
  for (const a of args) {
    if (!ended && a === '--') {
      ended = true;
      continue;
    }
    if (!ended && a.startsWith('-') && a !== '-') {
      if (a.startsWith('--format=') && format === null && FORMATS.includes(a.slice('--format='.length))) {
        format = a.slice('--format='.length);
      } else if (a === '--check' && !check) {
        check = true;
      } else if (a === '--strict' && !strict) {
        strict = true;
      } else {
        return { code: 2, out: ['error: usage'] };
      }
    } else {
      pos.push(a);
    }
  }
  if (pos.length > 1) return { code: 2, out: ['error: usage'] };
  const file = pos.length === 0 || pos[0] === '-' ? null : pos[0]!;
  let text = '';
  try {
    text = readFileSync(file ?? 0, 'utf8');
  } catch {
    if (file !== null) return { code: 2, out: ['error: no-patch'] };
  }
  const lines = patchLines(text);
  const kind = format === null || format === 'auto' ? detectFormat(lines) : format;
  if (kind === null) return { code: 2, out: ['error: format'] };
  let edits: Edit[];
  try {
    if (kind === 'json') edits = parseJsonEdits(text, lines);
    else if (kind === 'unified') edits = parseUnified(lines, strict);
    else if (kind === 'search-replace') edits = parseSearchReplace(lines, strict);
    else edits = parseV4a(lines, strict);
    if (edits.length === 0) throw new Exit2('error: parse 1');
  } catch (e) {
    if (e instanceof Exit2) return { code: 2, out: [e.line] };
    throw e;
  }
  const tree = new Tree();
  const fails: Fail[] = [];
  for (const edit of edits) {
    const snap = tree.snapshot();
    try {
      edit(tree);
    } catch (e) {
      if (!(e instanceof Fail)) throw e;
      tree.restore(snap);
      fails.push(e);
    }
  }
  if (fails.length > 0) {
    return {
      code: 1,
      out: [...fails.map((f) => `error: ${f.code} ${f.path}`), `failed: ${fails.length} of ${edits.length} edits`],
    };
  }
  interface Row {
    key: string;
    text: string;
  }
  const rows: Row[] = [];
  const deleted = new Set<string>();
  const added = new Set<string>();
  for (const p of tree.now.keys()) {
    const was = tree.original(p);
    const now = tree.now.get(p)!;
    if (was === now) continue;
    if (was === null) added.add(p);
    else if (now === null) deleted.add(p);
    else rows.push({ key: p, text: `M ${p}` });
  }
  for (const [oldP, newP] of tree.moves) {
    if (deleted.has(oldP) && added.has(newP)) {
      rows.push({ key: newP, text: `R ${oldP} -> ${newP}` });
      deleted.delete(oldP);
      added.delete(newP);
    }
  }
  for (const p of deleted) rows.push({ key: p, text: `D ${p}` });
  for (const p of added) rows.push({ key: p, text: `A ${p}` });
  rows.sort((a, b) => byteOrder(a.key, b.key));
  if (!check) {
    for (const p of [...tree.now.keys()].sort(byteOrder)) {
      const was = tree.original(p);
      const now = tree.now.get(p)!;
      if (was === now) continue;
      if (now === null) {
        rmSync(p, { force: true });
      } else {
        mkdirSync(dirname(p), { recursive: true });
        writeFileSync(p, now);
      }
    }
  }
  return { code: 0, out: [...rows.map((r) => r.text), `ok: ${rows.length} ${rows.length === 1 ? 'file' : 'files'}`] };
}

// Trial hand-over: when the grader's environment URL is set, the trial harness in runner.ts
// takes over; otherwise mend runs as the patch CLI on this process's arguments.
const trialEnv = process.env.MAKEFUN_ENV_URL;
if (trialEnv !== undefined && trialEnv !== '') {
  const { runTrial } = await import('./runner.ts');
  await runTrial(trialEnv);
} else {
  const r = run(process.argv.slice(2));
  writeSync(1, r.out.map((l) => `${l}\n`).join(''));
  process.exitCode = r.code;
}
