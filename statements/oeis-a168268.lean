import Mathlib

namespace OMA.S_oeis_a168268

open PowerSeries BigOperators

/-- A family `P` of subsets of `Fin n` is a set partition of `Fin n` with pairwise distinct
block sizes. -/
def isDistinctBlockSizePartition (n : ℕ) (P : Finset (Finset (Fin n))) : Prop :=
  (∀ B ∈ P, B.Nonempty) ∧
  (∀ B₁ ∈ P, ∀ B₂ ∈ P, B₁ ≠ B₂ → Disjoint B₁ B₂) ∧
  P.biUnion id = Finset.univ ∧
  (∀ B₁ ∈ P, ∀ B₂ ∈ P, B₁.card = B₂.card → B₁ = B₂)

/-- OEIS A007837: number of set partitions of an `n`-element set with distinct block sizes. -/
noncomputable def a007837 (n : ℕ) : ℕ :=
  open Classical in
  (Finset.univ.filter fun P : Finset (Finset (Fin n)) =>
    isDistinctBlockSizePartition n P).card

/-- Coefficients of `exp(∑_{n ≥ 1} A007837(n) * x^n / n)` over `ℚ`,
uniquely defined by `a(0) = 1` and `n * a(n) = ∑_{k=1}^n A007837(k) * a(n - k)` for `n ≥ 1`. -/
noncomputable def a168268Coeffs : ℕ → ℚ
  | 0 => 1
  | n + 1 =>
      (∑ k : Fin (n + 1), (a007837 (k.val + 1) : ℚ) * a168268Coeffs (n - k.val)) / ((n + 1 : ℕ) : ℚ)
termination_by n => n
decreasing_by
  have := k.isLt
  omega

/-- Conjecture on OEIS A168268:
the power series `exp(∑_{n ≥ 1} A007837(n) * x^n / n)` consists entirely of integers. -/
theorem main :
    ∀ n : ℕ, ∃ z : ℤ, a168268Coeffs n = (z : ℚ) := by
  sorry

end OMA.S_oeis_a168268
