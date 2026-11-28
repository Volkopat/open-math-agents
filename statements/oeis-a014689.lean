import Mathlib

/-!
# Residue classes of the nth prime minus or plus its index

Zhi-Wei Sun's conjecture in the November 25, 2013 comment on OEIS A014689
concerns both sequences. The index starts at one, so the first prime is two.
The modulus is positive and the residue can be any integer.

Source: https://oeis.org/A014689
Credit: @ZedingZhang
-/

namespace OMA.S_oeis_a014689

/-- The prime at positive index n in the OEIS convention. -/
noncomputable def primeAt (n : ℕ) : ℤ := Nat.nth Nat.Prime (n - 1)

theorem main :
    ∀ m : ℤ, 0 < m → ∀ r : ℤ,
      {n : ℕ | 0 < n ∧ Int.ModEq m (primeAt n - (n : ℤ)) r}.Infinite ∧
      {n : ℕ | 0 < n ∧ Int.ModEq m (primeAt n + (n : ℤ)) r}.Infinite := by
  sorry

end OMA.S_oeis_a014689
