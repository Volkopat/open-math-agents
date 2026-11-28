import Mathlib

/-!
# A137225: Triangle T(k,q) of minimal q-Niven numbers: smallest number such that the sum of its digits in base q equals k, 2<=q<=k+1.

Source: https://oeis.org/A137225
Credit: @agchua

Formula line of A137225 (the entry is by R. J. Mathar, Mar 07 2008):
  T(k,2)=A000225(k). T(k,k+1)=2k-1. Conjecture: T(k,3)=A062318(k), verified up to k=23.
`T k q` is the smallest natural number whose base-q digits (Mathlib's `Nat.digits q`) sum to k.
The column q = 3 exists for k >= 2 (2 <= q <= k+1), so the claim is stated for every k >= 2.
A062318 is the list, in increasing order, of the numbers of the form 3^m - 1 or 2*3^m - 1
(m >= 0): 0, 1, 2, 5, 8, 17, 26, ... Its offset is now 1, so A062318(j) is `Nat.nth` of that
set at j - 1. Offset: in 2008 A062318 had offset 0 (a(0) = 0, a(1) = 1, a(2) = 2, a(3) = 5);
its WARNING comment says the offset was changed from 0 to 1 without correcting the formulas.
The conjecture uses the old indexing (T(2,3) = 2, T(3,3) = 5, T(4,3) = 8 are the old a(2), a(3),
a(4)), which is A062318(k+1) in the current indexing; it is stated in that form.
-/

namespace OMA.S_oeis_a137225

/-- T(k, q): the smallest number whose digits in base q sum to k. -/
noncomputable def T (k q : ℕ) : ℕ := sInf {x : ℕ | (Nat.digits q x).sum = k}

/-- x is a number of the form 3^m - 1 or 2*3^m - 1. -/
def InA062318 (x : ℕ) : Prop := ∃ m : ℕ, x = 3 ^ m - 1 ∨ x = 2 * 3 ^ m - 1

/-- A062318(j), j >= 1 (offset 1): the j-th number of the form 3^m - 1 or 2*3^m - 1. -/
noncomputable def A062318 (j : ℕ) : ℕ := Nat.nth InA062318 (j - 1)

/-- The conjecture, for every k >= 2: T(k,3) is A062318 at k in the old offset 0, that is
A062318(k+1) in the current offset 1. -/
theorem main : ∀ k : ℕ, 2 ≤ k → T k 3 = A062318 (k + 1) := by
  sorry

end OMA.S_oeis_a137225
