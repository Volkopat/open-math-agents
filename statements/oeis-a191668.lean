import Mathlib

/-!
# A191668: Dispersion of A016825 (4k+2, k>0), by antidiagonals.

Source: https://oeis.org/A191668
Credit: @bnb9001

For an increasing sequence s of positive integers whose complement t is infinite with t(1) = 1,
the dispersion of s is the array whose n-th row is (t(n), s(t(n)), s(s(t(n))), ...). Here s is
A016825 = 2, 6, 10, ... (4k+2 for k >= 0, as in the data and the entry's comment listing
A191668 = dispersion of A016825 (4k+2, k>=0); row 1 is 1, 2, 6, 22, ...), i.e. s(m) = 4m - 2.
t enumerates the positive integers not of that form, and a(n,k) (n, k >= 1) is the k-th entry of
row n.

Conjecture: a(n,k) = (8 + (3*floor((4*n + 1)/3) - 2)*4^k)/12.
-/

namespace OMA.S_oeis_a191668

/-- A016825 as a function of the index: `s(m) = 4(m-1) + 2 = 4m - 2` (2, 6, 10, ...). -/
def s (x : ℕ) : ℕ := 4 * x - 2

/-- Membership in the complement `t` of `s`: positive integers not of the form `4m - 2`, `m ≥ 1`. -/
def InT (x : ℕ) : Prop := 0 < x ∧ ∀ m : ℕ, 1 ≤ m → x ≠ 4 * m - 2

/-- `t(n)`, the `n`-th element of the complement (offset 1). -/
noncomputable def t (n : ℕ) : ℕ := Nat.nth InT (n - 1)

/-- The dispersion of `s`: row `n` is `t(n), s(t(n)), s(s(t(n))), ...`; columns are indexed from 1. -/
noncomputable def D (n k : ℕ) : ℕ := s^[k - 1] (t n)

/-- The conjecture: `a(n,k) = (8 + (3 floor((4n+1)/3) - 2) 4^k) / 12` for `n, k >= 1`. -/
theorem main : ∀ n k : ℕ, 1 ≤ n → 1 ≤ k →
    (D n k : ℤ) = (8 + (3 * (((4 * n + 1) / 3 : ℕ) : ℤ) - 2) * 4 ^ k) / 12 := by
  sorry

end OMA.S_oeis_a191668
