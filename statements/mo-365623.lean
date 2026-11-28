import Mathlib

/-!
# Partial sums of signed binomial coefficients

Neha Joshi-Mainali asks whether every odd index `i` admits binary coefficients
on the interior entries of its alternating binomial row whose sum is one.
A finite subset `S` of the indices `1 ≤ k < i` records exactly the coefficients
chosen to be one. The other coefficients contribute zero.

Source: https://mathoverflow.net/questions/365623
Question by Neha Joshi-Mainali, CC BY-SA 4.0.
Credit: @connoranderson
-/

namespace OMA.S_mo_365623

/-- The partial sum selected by `S` in row `i` of the signed Pascal triangle. -/
def signedSum (i : ℕ) (S : Finset ℕ) : ℤ :=
  ∑ k ∈ S, (-1 : ℤ)^k * i.choose k

/-- Some choice of interior coefficients gives the requested sum. -/
def AdmitsOne (i : ℕ) : Prop :=
  ∃ S ⊆ Finset.Ico 1 i, signedSum i S = 1

theorem main : ∀ i : ℕ, Odd i → AdmitsOne i := by
  sorry

end OMA.S_mo_365623
