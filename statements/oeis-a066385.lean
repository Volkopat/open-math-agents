import Mathlib

/-!
# OEIS A066385: smallest maximal sum of 3 consecutive terms in a circular arrangement

Source: https://oeis.org/A066385
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n)` is the smallest possible maximum of the sums of 3 consecutive terms over all
arrangements of `1, …, n` in a circle. Conjecture (Jon E. Schoenfield, in the entry): for all
odd `n > 15`, `a(n) = f(n)` where `f(n) = ⌈3n/2⌉ + 3`.

Encoding: an arrangement is a bijection `σ : Fin n ≃ Fin n`, position `i` holding `σ i + 1`;
consecutive positions are taken cyclically (`i, i+1, i+2` in `Fin n`, `n ≥ 3`).
-/

namespace OMA.S_oeis_a066385

/-- Maximum sum of three cyclically consecutive values in the arrangement `σ`. -/
def maxTriple {n : ℕ} [NeZero n] (σ : Equiv.Perm (Fin n)) : ℕ :=
  Finset.univ.sup fun i : Fin n => ((σ i : ℕ) + 1) + ((σ (i + 1) : ℕ) + 1) + ((σ (i + 2) : ℕ) + 1)

/-- `a(n)`. -/
noncomputable def a (n : ℕ) [NeZero n] : ℕ := sInf (Set.range (maxTriple (n := n)))

/-- Schoenfield's conjecture. -/
theorem main : ∀ m : ℕ, 15 < m + 1 → Odd (m + 1) →
    a (m + 1) = (3 * (m + 1) + 1) / 2 + 3 := by
  sorry

end OMA.S_oeis_a066385
