import Mathlib

/-!
# Erdős Problem 1156

Source: https://www.erdosproblems.com/1156
Credit: @mgv27

Let $G$ be a random graph on $n$ vertices, in which every edge is included independently with
probability $1/2$. Is there some constant $C$ such that that chromatic number $\chi(G)$ is,
almost surely, concentrated on at most $C$ values? Is it true that, if $\omega(n)\to \infty$
sufficiently slowly, then for every function $f(n)$
\[\mathbb{P}(\lvert\chi(G)-f(n)\rvert<\omega(n))<1/2\]
if $n$ is sufficiently large?

Formalization notes:
* `main` states the second question. The first has a negative answer by Heckel's result quoted on
  the page (improved by Heckel and Riordan): any concentration interval has length `> n^c`
  for infinitely many `n`.
* `G(n, 1/2)` is the uniform distribution on all simple graphs on `Fin n`, so a probability is
  the number of graphs with the property divided by `2^{n(n-1)/2}`, the total number of graphs.
* `χ(G)` is Mathlib's `chromaticNumber` (finite on `Fin n`), converted with `ENat.toNat`.
* "If `ω(n) → ∞` sufficiently slowly, then …" is read as: there exists `ω : ℕ → ℝ` with
  `ω(n) → ∞` such that, for every `f : ℕ → ℝ`, eventually `ℙ(|χ(G) - f(n)| < ω(n)) < 1/2`. The
  probability can only shrink when `ω` is made smaller, so one such `ω` gives the property for
  every smaller `ω' → ∞` too.
* Known: Shamir and Spencer, and later Alon and Spencer, give concentration on intervals of
  length about `√n / log n`. Heckel and Riordan show that for any `c < 1/2`, concentration
  forces `ω(n) > n^c` for infinitely many `n`. That is the weaker "infinitely often" form of
  the statement here.
-/

namespace OMA.S_erdos_1156

open Filter Classical

/-- The chromatic number of a graph on `Fin n`, as a natural number. -/
noncomputable def chi {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  G.chromaticNumber.toNat

/-- `ℙ(|χ(G) - a| < w)` for `G` uniform among all simple graphs on `Fin n`. -/
noncomputable def probNear (n : ℕ) (a w : ℝ) : ℝ :=
  ((Finset.univ.filter fun G : SimpleGraph (Fin n) => |(chi G : ℝ) - a| < w).card : ℝ) /
    (Fintype.card (SimpleGraph (Fin n)) : ℝ)

/-- Erdős Problem 1156: for some `ω → ∞`, every `f` has, for large `n`,
`ℙ(|χ(G(n,1/2)) - f(n)| < ω(n)) < 1/2`. -/
theorem main : ∃ ω : ℕ → ℝ, Tendsto ω atTop atTop ∧
    ∀ f : ℕ → ℝ, ∀ᶠ n : ℕ in atTop, probNear n (f n) (ω n) < 1 / 2 := by
  sorry

end OMA.S_erdos_1156
