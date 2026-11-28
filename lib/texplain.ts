/** Shared by lib/catalog.ts (cards) and, as a copy, scripts/build_data.mjs. */
const TEX: Record<string, string> = {
  mathbb: "", mathbf: "", mathrm: "", mathcal: "", operatorname: "", text: "", textrm: "", textit: "", textbf: "", mathfrak: "", mathsf: "", boldsymbol: "", displaystyle: "", textstyle: "",
  le: "≤", leq: "≤", leqslant: "≤", ge: "≥", geq: "≥", geqslant: "≥", ne: "≠", neq: "≠", in: "∈", notin: "∉", ni: "∋", subset: "⊂", subseteq: "⊆", supset: "⊃", supseteq: "⊇",
  cup: "∪", cap: "∩", bigcup: "⋃", bigcap: "⋂", infty: "∞", to: "→", rightarrow: "→", Rightarrow: "⇒", leftrightarrow: "↔", Leftrightarrow: "⇔", iff: "⇔", implies: "⇒", mapsto: "↦",
  times: "×", cdot: "·", cdots: "…", ldots: "…", dots: "…", vdots: "⋮", pm: "±", mp: "∓", circ: "∘", oplus: "⊕", otimes: "⊗",
  sum: "∑", prod: "∏", int: "∫", sqrt: "√", log: "log", ln: "ln", exp: "exp", lim: "lim", liminf: "liminf", limsup: "limsup", max: "max", min: "min", sup: "sup", inf: "inf", gcd: "gcd", lcm: "lcm", deg: "deg", det: "det", dim: "dim", ker: "ker", sin: "sin", cos: "cos", tan: "tan",
  sim: "∼", simeq: "≃", cong: "≅", approx: "≈", propto: "∝", ll: "≪", gg: "≫", forall: "∀", exists: "∃", nexists: "∄", neg: "¬", lnot: "¬", land: "∧", wedge: "∧", lor: "∨", vee: "∨",
  mid: "|", nmid: "∤", divides: "|", lvert: "|", rvert: "|", vert: "|", Vert: "‖", lVert: "‖", rVert: "‖", langle: "⟨", rangle: "⟩", partial: "∂", nabla: "∇", prime: "′",
  alpha: "α", beta: "β", gamma: "γ", delta: "δ", epsilon: "ε", varepsilon: "ε", zeta: "ζ", eta: "η", theta: "θ", vartheta: "ϑ", iota: "ι", kappa: "κ", lambda: "λ",
  mu: "μ", nu: "ν", xi: "ξ", pi: "π", varpi: "ϖ", rho: "ρ", varrho: "ϱ", sigma: "σ", tau: "τ", upsilon: "υ", phi: "φ", varphi: "φ", chi: "χ", psi: "ψ", omega: "ω",
  Gamma: "Γ", Delta: "Δ", Theta: "Θ", Lambda: "Λ", Xi: "Ξ", Pi: "Π", Sigma: "Σ", Upsilon: "Υ", Phi: "Φ", Psi: "Ψ", Omega: "Ω", ell: "ℓ", aleph: "ℵ", hbar: "ℏ",
  left: "", right: "", big: "", Big: "", bigg: "", Bigg: "", bigl: "", bigr: "", Bigl: "", Bigr: "", lfloor: "⌊", rfloor: "⌋", lceil: "⌈", rceil: "⌉",
  equiv: "≡", setminus: "∖", backslash: "∖", emptyset: "∅", varnothing: "∅", bmod: " mod ", mod: " mod ", quad: " ", qquad: " ", colon: ":", star: "⋆", ast: "∗", angle: "∠", perp: "⊥", parallel: "∥", triangle: "△",
};
const BB: Record<string, string> = { N: "ℕ", Z: "ℤ", Q: "ℚ", R: "ℝ", C: "ℂ", P: "ℙ", F: "𝔽", H: "ℍ", E: "𝔼" };
const SUP: Record<string, string> = { "0": "⁰", "1": "¹", "2": "²", "3": "³", "4": "⁴", "5": "⁵", "6": "⁶", "7": "⁷", "8": "⁸", "9": "⁹", "+": "⁺", "-": "⁻", n: "ⁿ", i: "ⁱ", k: "ᵏ" };
const SUB: Record<string, string> = { "0": "₀", "1": "₁", "2": "₂", "3": "₃", "4": "₄", "5": "₅", "6": "₆", "7": "₇", "8": "₈", "9": "₉", "+": "₊", "-": "₋", i: "ᵢ", j: "ⱼ", k: "ₖ", n: "ₙ", m: "ₘ", p: "ₚ", r: "ᵣ", s: "ₛ", t: "ₜ", x: "ₓ" };
const simple = (s: string) => /^[\w′.]+$/u.test(s.trim());
const frac = (a: string, b: string) => (simple(a) && simple(b) ? `${a.trim()}/${b.trim()}` : `(${a.trim()})/(${b.trim()})`);
const script = (map: Record<string, string>, mark: string) => (_: string, body: string) => {
  const t = body.trim();
  if (t && [...t].every((c) => map[c])) return [...t].map((c) => map[c]).join("");
  return t.length === 1 ? mark + t : `${mark}(${t})`;
};
/** Rough TeX/Markdown → Unicode for one-line titles and excerpts (problem pages render real KaTeX). */
export function texPlain(s: string): string {
  let t = s
    .replace(/\\\$/g, "\u0001")                             // a literal dollar sign
    .replace(/\\\{/g, "\u0002").replace(/\\\}/g, "\u0003")  // set braces
    .replace(/\\_/g, "_").replace(/\\%/g, "%").replace(/\\&/g, "&").replace(/\\#/g, "#")
    .replace(/\\mathbb\s*\{?([A-Z])\}?/g, (_: string, c: string) => BB[c] ?? c)
    .replace(/\\pmod\s*\{([^{}]*)\}/g, " (mod $1)");
  for (let i = 0; i < 3; i++) {
    t = t
      .replace(/\^\s*\{([^{}]*)\}/g, script(SUP, "^"))
      .replace(/_\s*\{([^{}]*)\}/g, script(SUB, "_"))
      .replace(/\\[dt]?frac\s*\{([^{}]*)\}\s*\{([^{}]*)\}/g, (_: string, a: string, b: string) => frac(a, b))
      .replace(/\\[dt]?frac\s*([0-9A-Za-z])\s*([0-9A-Za-z])/g, (_: string, a: string, b: string) => `${a}/${b}`)
      .replace(/\\binom\s*\{([^{}]*)\}\s*\{([^{}]*)\}/g, "C($1, $2)")
      .replace(/\\sqrt\s*\{([^{}]*)\}/g, (_: string, a: string) => (simple(a) ? `√${a}` : `√(${a})`));
  }
  t = t
    .replace(/\^\s*\{([^{}]*)\}/g, script(SUP, "^")).replace(/\^\s*([0-9A-Za-z+-])/g, (m: string, c: string) => SUP[c] ?? m)
    .replace(/_\s*\{([^{}]*)\}/g, script(SUB, "_")).replace(/_\s*([0-9a-z])(?![a-z])/g, (m: string, c: string) => SUB[c] ?? m)
    .replace(/\\([A-Za-z]+)(\s?)/g, (m: string, w: string, sp: string) => (w in TEX ? TEX[w] + sp : w + " "))
    .replace(/\\[,;!: ]/g, " ")
    .replace(/\*\*([^*]+)\*\*/g, "$1").replace(/(^|[\s(])\*([^*\n]+)\*(?=[\s).,;:]|$)/g, "$1$2")
    .replace(/[{}$*`]/g, "")
    .replace(/\u0001/g, "$").replace(/\u0002/g, "{").replace(/\u0003/g, "}")
    .replace(/\s+([,.;:)])/g, "$1").replace(/\(\s+/g, "(")
    .replace(/\s+/g, " ")
    .trim();
  return t;
}
