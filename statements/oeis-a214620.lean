import Mathlib

/-!
# Factor and digit collisions in OEIS A214620

Source: https://oeis.org/A214620.

The entry asks for more than half of the integers beyond a threshold
to belong to the sequence. We express this as a strict majority among
1 through N for every sufficiently large N. Partners may lie outside
that interval. Digit multiplicities are taken in base 2.
-/

namespace OMA.S_oeis_a214620

/-- Membership under the digit-permutation and prime-factor criteria of the entry. -/
def Occurs (n : ℕ) : Prop :=
  2 ≤ n ∧ ∃ m : ℕ, 2 ≤ m ∧ m ≠ n ∧ n.minFac=m.minFac ∧
    n.primeFactors.sup id=m.primeFactors.sup id ∧
    (Nat.digits 2 n).Perm (Nat.digits 2 m)

noncomputable def count (N : ℕ) : ℕ := by
  classical exact ((Finset.Icc 1 N).filter Occurs).card

theorem main : ∃ N₀ : ℕ, ∀ N ≥ N₀, N < 2 * count N := by
  sorry

end OMA.S_oeis_a214620
