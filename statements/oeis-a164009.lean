import Mathlib

/-!
# A164009: Zero together with row 9 of the array in A163280.

Source: https://oeis.org/A164009
Credit: @marcelopierry

Conjecture (R. J. Mathar, Jul 31 2010, in the formulas of A164009): a(n) = A028566(n), n > 12.

Conventions:
* A163280 is the square array whose column k lists, in increasing order, the numbers j whose
  largest divisor <= sqrt(j) is k (that divisor is A033676(j)). A divisor d of j satisfies
  d <= sqrt(j) exactly when d * d <= j, so `lowerDiv j` below is A033676(j) for j >= 1; also
  `lowerDiv 0 = 0`, so 0 lies in no column k >= 1.
* `T n k` is the entry in row n (n >= 1) of column k (k >= 1): the n-th smallest j with
  `lowerDiv j = k`, i.e. `Nat.nth` at index n - 1 (this reproduces the array in A163280,
  e.g. column 1 is 1 together with the primes).
* A164009 has offset 0: a(0) = 0 and a(n) = T(9, n) for n >= 1, giving the data
  0, 19, 38, 51, 76, 75, 114, 105, 136, 162, 190, ...
* A028566(n) = n*(n+8).
-/

namespace OMA.S_oeis_a164009

/-- A033676(j): the largest divisor d of j with d * d <= j. -/
def lowerDiv (j : ℕ) : ℕ := ((Nat.divisors j).filter (fun d => d * d ≤ j)).sup id

/-- T n k: row n of column k of the array A163280. -/
noncomputable def T (n k : ℕ) : ℕ := Nat.nth (fun j => lowerDiv j = k) (n - 1)

/-- A164009: zero together with row 9 of A163280 (offset 0). -/
noncomputable def a (n : ℕ) : ℕ := if n = 0 then 0 else T 9 n

/-- Mathar's conjecture: a(n) = n*(n+8) for n > 12. -/
theorem main : ∀ n : ℕ, 12 < n → a n = n * (n + 8) := by
  sorry

end OMA.S_oeis_a164009
