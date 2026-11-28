import Mathlib

/-!
# Sum over permutations involving sign

Source: https://mathoverflow.net/questions/344474
Credit: @zarnab222-dev

Is the signed sum of the reciprocals of the products of the prefix sums of
permutations of 1 through d equal to the proposed product of factorials?
The permutation acts on zero-based positions, so its values are increased by
one. The factorial product includes k = 0, whose factor is one.
-/

namespace OMA.S_mo_344474

theorem main : ∀ d : ℕ,
    (∑ σ : Equiv.Perm (Fin d), ((Equiv.Perm.sign σ : ℤ) : ℚ) /
      (∏ i : Fin d, ∑ j ∈ Finset.Iic i, ((σ j).val + 1 : ℚ))) =
    ∏ k ∈ Finset.range d, (Nat.factorial k : ℚ)^2 / Nat.factorial (2*k+1) := by
  sorry

end OMA.S_mo_344474
