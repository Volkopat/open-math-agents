import Mathlib

/-!
# A069623: Number of perfect powers <= n.

Source: https://oeis.org/A069623
Credit: @bnb9001

The perfect powers are A001597: 1, 4, 8, 9, 16, 25, 27, ..., the numbers of the form b^k with
k >= 2 (1 = 1^2 is included). a(n) counts those in [1, n] (offset 1: 1, 1, 1, 2, 2, 2, 2, 3, 4).

Conjecture (Chayim Lowen, 2015): a(n) = O(sqrt(n)). Robert Israel notes that the conjecture is
true: the squares contribute sqrt(n) + O(1) and the higher powers fewer than n^(1/3) log_2(n).
-/

namespace OMA.S_oeis_a069623

open Filter Asymptotics

/-- `m` is a perfect power (A001597): `m = b ^ k` for some `b` and some `k >= 2`. -/
def IsPerfectPower (m : ℕ) : Prop := ∃ b k : ℕ, 2 ≤ k ∧ b ^ k = m

open Classical in
/-- A069623: the number of perfect powers in `[1, n]`. -/
noncomputable def a (n : ℕ) : ℕ := ((Finset.Icc 1 n).filter IsPerfectPower).card

/-- Lowen's conjecture, proved: `a(n) = O(sqrt n)`. -/
theorem main : (fun n : ℕ => (a n : ℝ)) =O[atTop] (fun n : ℕ => Real.sqrt n) := by
  sorry

end OMA.S_oeis_a069623
