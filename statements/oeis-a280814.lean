import Mathlib

/-!
# A280814: The maximum number of squares among the partial sums of any permutation of the integers [1..n].

Source: https://oeis.org/A280814
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A280814 (Michel Marcus, Jan 08 2017): a(n) = floor((n +
n mod 2 + (n+1/2)*sqrt(2))/4).

Conventions:
* The sequence has offset 1 (data 1, 1, 2, 2, 3, 3, 4, 5, 5, 6, 7, 7, ...).
* A permutation of [1..n] is a permutation sigma of `Fin n`, read as the arrangement sigma(0)+1,
  sigma(1)+1, ..., sigma(n-1)+1; `sq n sigma` is the number of indices k such that the partial sum
  of the first k+1 entries is a square (`IsSquare`). a(n) is the greatest value of `sq n sigma`,
  stated with `IsGreatest`.
* The formula is computed in `ℝ` (sqrt is `Real.sqrt`, n mod 2 is the natural-number remainder
  cast to `ℝ`), and the floor of this nonnegative real is the natural-number floor `Nat.floor`.
  Only the formula is formalized, not the limit that the entry derives from it. The statement is
  for n >= 1 (the offset of the sequence).
-/

namespace OMA.S_oeis_a280814

/-- The number of squares among the partial sums of the arrangement sigma(0)+1, ..., sigma(n-1)+1
of the integers 1..n. -/
noncomputable def sq (n : ℕ) (σ : Equiv.Perm (Fin n)) : ℕ :=
  Set.ncard {k : Fin n | IsSquare (∑ i ∈ Finset.Iic k, ((σ i : ℕ) + 1))}

/-- The conjecture recorded in A280814. -/
theorem main : ∀ n : ℕ, 0 < n →
    IsGreatest {c : ℕ | ∃ σ : Equiv.Perm (Fin n), c = sq n σ}
      ⌊((n : ℝ) + (n % 2 : ℕ) + ((n : ℝ) + 1 / 2) * Real.sqrt 2) / 4⌋₊ := by
  sorry

end OMA.S_oeis_a280814
