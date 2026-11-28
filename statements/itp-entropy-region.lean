import Mathlib

/-!
# Entropy region of four or more random variables

Source: https://github.com/gokhanmergen/information-theory-problems/blob/main/problems/entropy-region.md
Credit: @nnkostov

The source poses the open problem of explicitly characterizing the closure `\bar{\Gamma}^*_n`
of the set `\Gamma^*_n` of entropic vectors of `n` jointly distributed discrete random variables
for `n ≥ 4`, and designates as its formalized open question (under *What is known →
Semialgebraicity (the formalized question)*) whether the 4-variable almost-entropic cone
`\bar{\Gamma}^*_4 ⊆ ℝ^{2^4 - 1}` is a semialgebraic set.

Conventions:
* Coordinates are indexed by nonempty subsets `S ⊆ Fin 4` (`NonemptySubset 4`, cardinality
  `2^4 - 1 = 15`), matching the `2^n - 1` joint entropies `H(X_S)` for `∅ ≠ S ⊆ {1, ..., n}`.
* Entropic vectors (`entropicVectors n`): joint entropy vectors in bits (`Real.negMulLog / Real.log 2`)
  of finitely supported joint probability distributions on `Fin n → Fin k` (`k : ℕ`). Any finite
  joint alphabet embeds into `(Fin k)^n`, and any countable discrete distribution with finite
  entropy is a limit of finite truncations, so the closure `closure (entropicVectors n)` in the
  standard product topology on `NonemptySubset n → ℝ` coincides with `\bar{\Gamma}^*_n`.
  (Changing logarithm base scales every vector by a positive constant, leaving the closed cone
  `\bar{\Gamma}^*_n` invariant.)
* Semialgebraic set (`IsSemialgebraic`): standard definition as a finite union of basic
  semialgebraic sets defined by finitely many real multivariate polynomial equations `P(x) = 0`
  and strict inequalities `0 < Q(x)` via `MvPolynomial`.
* As noted in the source, Mejía and Montoya (arXiv:1510.02658) conjecture `\bar{\Gamma}^*_4` is
  not semialgebraic, which corresponds to `¬ main` (`OMA.disproof`).
-/

namespace OMA.S_itp_entropy_region

open scoped BigOperators

/-- Nonempty subsets of `Fin n`, indexing the `2^n - 1` joint entropy coordinates. -/
abbrev NonemptySubset (n : ℕ) := {S : Finset (Fin n) // S.Nonempty}

/-- Marginal probability mass of the subvector `(X_i)_{i ∈ S}` at outcome `y : S → Fin k`,
given a joint probability mass function `p` on `Fin n → Fin k`. -/
noncomputable def marginalMass {n k : ℕ} (p : (Fin n → Fin k) → ℝ)
    (S : Finset (Fin n)) (y : S → Fin k) : ℝ :=
  ∑ x : Fin n → Fin k, if (fun i : S => x i.1) = y then p x else 0

/-- Joint Shannon entropy `H(X_S)` in bits for a subset `S ⊆ Fin n`. -/
noncomputable def subsetEntropy {n k : ℕ} (p : (Fin n → Fin k) → ℝ)
    (S : Finset (Fin n)) : ℝ :=
  (∑ y : S → Fin k, Real.negMulLog (marginalMass p S y)) / Real.log 2

/-- The set `Γ*_n` of entropic vectors of `n` jointly distributed discrete random variables
with finite alphabets, as a subset of `ℝ^{2^n - 1}`. -/
def entropicVectors (n : ℕ) : Set (NonemptySubset n → ℝ) :=
  {h | ∃ (k : ℕ) (p : (Fin n → Fin k) → ℝ),
    (∀ x, 0 ≤ p x) ∧ (∑ x, p x = 1) ∧
    ∀ S : NonemptySubset n, h S = subsetEntropy p S.1}

/-- A subset of `ℝ^ι` is semialgebraic if it is a finite union of basic semialgebraic sets
cut out by finitely many real multivariate polynomial equations and strict inequalities. -/
def IsSemialgebraic {ι : Type*} (A : Set (ι → ℝ)) : Prop :=
  ∃ (m : ℕ) (r s : Fin m → ℕ)
    (P : (i : Fin m) → Fin (r i) → MvPolynomial ι ℝ)
    (Q : (i : Fin m) → Fin (s i) → MvPolynomial ι ℝ),
    A = ⋃ i : Fin m,
      {x | (∀ j : Fin (r i), MvPolynomial.eval x (P i j) = 0) ∧
           (∀ l : Fin (s i), 0 < MvPolynomial.eval x (Q i l))}

/-- Open problem (Zhang–Yeung 1998; Matúš 2007): Is the closure `cl(Γ*_4)` of the set of
entropic vectors of four jointly distributed discrete random variables a semialgebraic set
in `ℝ^{2^4 - 1}`? -/
theorem main : IsSemialgebraic (closure (entropicVectors 4)) := by
  sorry

end OMA.S_itp_entropy_region
