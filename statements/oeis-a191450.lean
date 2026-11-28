import Mathlib

/-!
# A191450: Dispersion of (3*n-1), read by antidiagonals.

Source: https://oeis.org/A191450
Credit: @bnb9001

For an increasing sequence s of positive integers whose complement t is infinite with t(1) = 1,
the dispersion of s is the array D whose n-th row is (t(n), s(t(n)), s(s(t(n))), ...). Here
s(m) = 3m - 1, t is the increasing enumeration of the positive integers not of that form, and
D(n,k) (n, k >= 1) is the k-th entry of row n. A032766 lists the numbers congruent to 0 or 1 mod 3
(offset 0) and A000244(k) = 3^k.

Conjecture (L. Edson Jeffery, with changes by Antti Karttunen, 2015):
A(n,k) = (3 + (2*A032766(n) - 1)*A000244(k))/6.
-/

namespace OMA.S_oeis_a191450

/-- The sequence `s(m) = 3m - 1`. -/
def s (x : ℕ) : ℕ := 3 * x - 1

/-- Membership in the complement `t` of `s` (positive integers not of the form `3m - 1`, `m ≥ 1`). -/
def InT (x : ℕ) : Prop := 0 < x ∧ ∀ m : ℕ, 1 ≤ m → x ≠ 3 * m - 1

/-- `t(n)`, the `n`-th element of the complement (offset 1). -/
noncomputable def t (n : ℕ) : ℕ := Nat.nth InT (n - 1)

/-- The dispersion of `s`: row `n` is `t(n), s(t(n)), s(s(t(n))), ...`; columns are indexed from 1. -/
noncomputable def D (n k : ℕ) : ℕ := s^[k - 1] (t n)

/-- A032766: numbers that are congruent to 0 or 1 mod 3 (offset 0). -/
noncomputable def A032766 (n : ℕ) : ℕ := Nat.nth (fun x => x % 3 = 0 ∨ x % 3 = 1) n

/-- The conjecture: `D(n,k) = (3 + (2 A032766(n) - 1) 3^k) / 6` for `n, k >= 1`. -/
theorem main : ∀ n k : ℕ, 1 ≤ n → 1 ≤ k →
    (D n k : ℤ) = (3 + (2 * (A032766 n : ℤ) - 1) * 3 ^ k) / 6 := by
  sorry

end OMA.S_oeis_a191450
