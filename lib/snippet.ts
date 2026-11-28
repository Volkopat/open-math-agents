/**
 * Lean code written by agents for their team: lemmas posted on a problem's task board (done items), the lemma lines of
 * a PLAN: note, and the declarations of a merged proof (to see which teammates' lemmas it uses, for credit).
 *
 * A board lemma is pasted into other agents' proof files and compiled on their machines, and Lean can run code while it
 * compiles (#eval, macros, elab, initialize ...). So the desk refuses any board code the checker would refuse anyway,
 * with the shared rules of tools/lint.py (keep BANNED identical to it), and tools/oma.sh checks the bundle again before
 * writing it. Everything here is data written by other agents: checked, never obeyed.
 */

// tools/lint.py, BANNED (the rules shared by every file kind)
const BANNED: RegExp[] = [
  /\bsorry\b/, /\badmit\b/, /\baxiom\b/, /\baxioms\b/, /\bnative_decide\b/, /\bunsafe\b/, /\bpartial\b/,
  /\bopaque\b/, /\bimplemented_by\b/, /\bextern\b/, /\bmacro\w*/, /\bsyntax\w*/, /\belab\w*/, /\bnotation\w*/,
  /\binfix[lr]?\b/, /\bprefix\b/, /\bpostfix\b/, /\binitialize\b/, /\bbuiltin_initialize\b/, /\brun_cmd\b/,
  /\brun_tac\b/, /\brun_elab\b/, /\bby_elab\b/, /\battribute\b/, /\bdeclare_\w+/, /\bmeta\b/, /\bIO\b/,
  /\bLean\.(Elab|Meta|Compiler|Environment|IR|ofReduceBool|trustCompiler)/, /\bdecide\s*:=\s*true/, /\bimport\s+Lean\b/,
  new RegExp(
    "#(eval|print|check|reduce|exit|guard|help|lint|find|synth|where|show|time|output|widget|html|norm_num|simp|conv|" +
      "parse|test|explode|long_names|search|loogle|leansearch|moogle|import|min_imports|unused|sample|allow|define|stop|" +
      "count_heartbeats|adaptation_note|align|mathlib|tactic|kernel|compile|leanchecker|version|guard_msgs|trans|redundant)\\w*",
  ),
];
const OPTIONS = new Set(["maxHeartbeats", "maxRecDepth", "synthInstance.maxHeartbeats", "synthInstance.maxSize"]);

/** Comments removed (line comments and nested block comments), as tools/lint.py strip_comments. */
export function stripComments(s: string): { code: string; unterminated: boolean } {
  let out = "";
  let depth = 0;
  for (let i = 0; i < s.length; ) {
    if (depth === 0 && s.startsWith("--", i)) {
      const j = s.indexOf("\n", i);
      i = j < 0 ? s.length : j;
      continue;
    }
    if (s.startsWith("/-", i)) { depth++; i += 2; continue; }
    if (depth && s.startsWith("-/", i)) { depth--; i += 2; continue; }
    if (depth === 0) out += s[i];
    i++;
  }
  return { code: out, unterminated: depth > 0 };
}

export type Decl = { name: string; head: string };

const DECL_RE = /(?:^|\n)[ \t]*(?:@\[[^\]\n]*\][ \t]*)?(?:(?:private|protected|nonrec)[ \t]+)*(?:theorem|lemma)[ \t]+([^\s:()[\]{}⦃⦄,;]+)([\s\S]*?):=/g;
// In a note, a declaration may follow other text on its line ("DONE: lemma foo ...", "```lean lemma foo ...").
const LOOSE_DECL_RE = /(?:^|[\s`:])(?:theorem|lemma)[ \t]+([^\s:()[\]{}⦃⦄,;`]+)([\s\S]*?):=/g;
const squash = (s: string) => s.replace(/\s+/g, " ").trim();

/** The theorems and lemmas a piece of Lean declares: name and normalized head (name, binders and type, whitespace
 * collapsed), comments ignored. `loose`: for notes, where a declaration may start mid-line. */
export function declarations(src: string, loose = false): Decl[] {
  const { code } = stripComments(src);
  const out: Decl[] = [];
  for (const m of code.matchAll(loose ? LOOSE_DECL_RE : DECL_RE)) {
    const name = m[1];
    if (name === "OMA.solution" || name === "OMA.disproof") continue;
    out.push({ name, head: squash(`${name} ${m[2]}`) });
  }
  return out;
}

/** Why a board lemma would be refused by the checker (or could run code while it compiles); empty when it is fine. */
export function snippetProblems(src: string): string[] {
  const errors: string[] = [];
  const { code, unterminated } = stripComments(src);
  if (unterminated) errors.push("unterminated block comment");
  if (code.includes('"')) errors.push("no double-quote characters (string literals) allowed");
  if (code.includes("\u0000")) errors.push("NUL byte");
  for (const re of BANNED) {
    const m = code.match(re);
    if (m) errors.push(`forbidden: ${m[0]}`);
  }
  for (const m of code.matchAll(/@\[([^\]]*)\]/g)) {
    if (!["simp", "local simp"].includes(m[1].trim())) errors.push(`attribute @[${m[1]}] not allowed (only @[simp], @[local simp])`);
  }
  for (const m of code.matchAll(/\bset_option\s+([\w.]+)\s+(\S+)(\s+in\b)?/g)) {
    if (!OPTIONS.has(m[1]) || !/^\d+$/.test(m[2]) || !m[3]) errors.push(`set_option ${m[1]} ${m[2]} not allowed (only numeric maxHeartbeats/maxRecDepth/synthInstance.* with in)`);
  }
  if (/^\s*import\b/m.test(code)) errors.push("no import lines: the lemma goes below the imports of the proof file");
  if (!declarations(src).length) errors.push("declares no lemma or theorem (write the full Lean declaration: lemma <name> ... := by ...)");
  return errors;
}

/** A Lean name the board accepts: no spaces or brackets, at most 80 characters, not starting with a digit. */
export const LEMMA_NAME = /^(?![0-9])[^\s:()[\]{}⦃⦄,;"`]{1,80}$/u;

export type PlanItem = { name: string; statement: string; detail: string; source: "plan" };

/**
 * The subgoals of a PLAN: note: each line that starts (after an optional bullet) with `lemma <name>` or
 * `theorem <name>`, continued by the more indented lines after it, up to `:=`. A trailing `-- comment` is the item's
 * one-line description. At most 8.
 */
export function planItems(note: string): PlanItem[] {
  if (!/^\s*PLAN\s*:/i.test(note)) return [];
  const lines = note.split("\n");
  const out: PlanItem[] = [];
  const seen = new Set<string>();
  for (let i = 0; i < lines.length && out.length < 8; i++) {
    const m = lines[i].match(/^(\s*)(?:[-*•]\s+|\d+[.)]\s+)?(?:lemma|theorem)\s+(\S+)(.*)$/);
    if (!m) continue;
    const indent = m[1].length;
    const name = m[2].replace(/[:,;]+$/, "");
    if (!LEMMA_NAME.test(name) || name === "OMA.solution" || seen.has(name.toLowerCase())) continue;
    let rest = m[3];
    let detail = "";
    const cut = (s: string) => {
      const c = s.indexOf("--");
      if (c >= 0) { detail ||= s.slice(c + 2).trim(); return s.slice(0, c); }
      return s;
    };
    rest = cut(rest);
    // continuation: the following lines indented deeper than the declaration line
    for (let j = i + 1; j < lines.length && !rest.includes(":="); j++) {
      const l = lines[j];
      if (!l.trim() || (l.match(/^\s*/)?.[0].length ?? 0) <= indent) break;
      rest += " " + cut(l);
      i = j;
    }
    const statement = squash(rest.split(":=")[0]).slice(0, 2000);
    seen.add(name.toLowerCase());
    out.push({ name, statement, detail: detail.slice(0, 300), source: "plan" });
  }
  return out;
}

/** Note ids a pull request says it uses: "Uses: #123, #456" lines of its body and "-- uses note #123" lines of its file. */
export function usedNoteIds(body: string, src: string): number[] {
  const ids = new Set<number>();
  for (const line of body.match(/^\s*Uses\s*:.*$/gim) ?? []) for (const m of line.matchAll(/#(\d{1,15})\b/g)) ids.add(Number(m[1]));
  for (const m of src.matchAll(/--\s*uses note #(\d{1,15})\b/gi)) ids.add(Number(m[1]));
  return [...ids].slice(0, 40);
}

/**
 * Which teammates' DONE notes a merged proof uses. A note counts when one of its lemmas appears in the merged file with
 * the same head (name, binders and type), or when the pull request names the note (usedNoteIds) and the file declares
 * one of its lemma names. The desk then re-checks who wrote it, when and from where (oma_verdict3).
 */
export function usedNotes(src: string, body: string, candidates: { id: number; text: string }[]): number[] {
  const mine = declarations(src);
  const heads = new Set(mine.map((d) => d.head));
  const names = new Set(mine.map((d) => d.name));
  const named = new Set(usedNoteIds(body, src));
  const out: number[] = [];
  for (const c of candidates) {
    const ds = declarations(c.text ?? "", true);
    if (ds.some((d) => heads.has(d.head) && d.name.length >= 3) || (named.has(c.id) && ds.some((d) => names.has(d.name)))) out.push(c.id);
  }
  return out;
}
