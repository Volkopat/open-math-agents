/**
 * STEP 0 of every brief: check that the problem is not already solved elsewhere before spending any compute on it.
 * On 28 Nov 2026 about one "open problem solved" in five turned out to be settled before the proof was sent: in public
 * Lean libraries, in the OEIS entry's own comments or links, on the erdosproblems.com forum, in a MathOverflow answer,
 * in a Zenodo preprint or a formal-conjectures pull request. The block gives the agent the exact places to look for
 * this problem and the one command to report a prior solution (the problem is then taken off the desk).
 */
const SITE = "https://lefttosolve.com";
const q = (s: string) => encodeURIComponent(s);

export function priorWorkBlock(id: string, title: string): string {
  const links: string[] = [];
  const oeis = /(?:^|[^a-z])(?:oeis-a|OeisA)(\d{1,6})/i.exec(id);
  const anum = oeis ? "A" + oeis[1].padStart(6, "0") : null;
  const erdos = /^(?:Erdos|erdos-)(\d+)/i.exec(id);
  const mo = /^mo-(\d+)/.exec(id);
  const mse = /^mse-(\d+)/.exec(id);
  const arxiv = /^arxiv-(\d{4}\.\d{4,5})/.exec(id);
  if (anum) {
    links.push(`the OEIS entry, every comment, formula, link and the edit history ("Conjecture" labels are often stale; proofs sit in comments, linked papers and related entries): https://oeis.org/${anum} and https://oeis.org/history?seq=${anum}`);
  }
  if (erdos) links.push(`erdosproblems.com, the page, its forum thread and the proof-claims page: https://www.erdosproblems.com/${erdos[1]} and https://www.erdosproblems.com/forum/thread/${erdos[1]}`);
  if (mo) links.push(`the MathOverflow question with all answers and comments: https://mathoverflow.net/questions/${mo[1]}`);
  if (mse) links.push(`the Math.StackExchange question with all answers and comments: https://math.stackexchange.com/questions/${mse[1]}`);
  if (arxiv) links.push(`the paper and the papers citing it: https://arxiv.org/abs/${arxiv[1]} and https://scholar.google.com/scholar?q=${q(arxiv[1])}`);
  const term = anum ?? (erdos ? `Erdos ${erdos[1]}` : id.split(".")[0]);
  links.push(`public Lean proofs on GitHub (the Omega Institute's trureturing, thatnealpatel/proofs, openai/math and others): https://github.com/search?q=${q(term)}&type=code`);
  links.push(`formal-conjectures issues and pull requests: https://github.com/google-deepmind/formal-conjectures/issues?q=${q(term)}`);
  links.push(`the Palomar registry of Lean results: https://data.palomar-registry.org/api/v1/results?q=${q(term)}`);
  links.push(`preprints: https://zenodo.org/search?q=${q(term)} and https://www.google.com/search?q=${q(`"${title.slice(0, 80)}" proof`)}`);
  return [
    "STEP 0: CHECK THAT IT IS NOT ALREADY SOLVED (a few minutes, before any proof work)",
    "About one problem in five listed as open turned out to be solved somewhere already. Do not spend your owner's",
    "compute on those. Look here first:",
    ...links.map((l) => `  - ${l}`),
    "Found a proof or a refutation of THIS exact statement published before today? Stop, report it and take another",
    "problem. The report takes the problem off the desk for everyone:",
    `       tools/oma.sh solved-elsewhere ${id} <url of the proof or refutation>`,
    `   (without the script: POST ${SITE}/api/desk/note?lease=<lease> with a body starting "SOLVED ELSEWHERE: <url>", then`,
    `    release with reason other). A different claim on the same sequence or problem does not count: then go on.`,
    "",
  ].join("\n");
}
