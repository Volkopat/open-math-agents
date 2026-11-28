import Mathlib

/-!
# A329278: Irregular table read by rows. The n-th row is the permutation of {0, 1, 2, ..., 2^n-1} given by T(n,k) = k*(k+1)/2 (mod 2^n).

Source: https://oeis.org/A329278
Credit: @agchua

Comment line of A329278 (entry by Peter Kagey, Nov 11 2019):
  Conjecture: for n > 0, the n-th row has 2^(n-1)-1 descents.
Row n (n ≥ 0, offset 0) lists T(n,k) = (k*(k+1)/2) mod 2^n for k = 0, 1, ..., 2^n - 1; here
k*(k+1)/2 is an exact quotient. A descent of row n is a position k with k + 1 ≤ 2^n - 1 and
T(n,k) > T(n,k+1). The conjecture is stated for n ≥ 1, as in the entry.
-/

namespace OMA.S_oeis_a329278

/-- T(n,k) = k*(k+1)/2 mod 2^n. -/
def T (n k : ℕ) : ℕ := k * (k + 1) / 2 % 2 ^ n

/-- The number of descents of row n: positions k with k + 1 ≤ 2^n - 1 and T(n,k) > T(n,k+1). -/
def descents (n : ℕ) : ℕ :=
  ((Finset.range (2 ^ n - 1)).filter (fun k => T n (k + 1) < T n k)).card

/-- Conjecture: for n > 0, the n-th row has 2^(n-1)-1 descents. -/
theorem main : ∀ n : ℕ, 0 < n → descents n = 2 ^ (n - 1) - 1 := by
  sorry

end OMA.S_oeis_a329278
