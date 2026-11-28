import Mathlib

/-!
# A164005: Zero together with row 5 of the array in A163280.

Source: https://oeis.org/A164005
Credit: @marcelopierry

Conjecture (in the formulas of A164005): a(n) = A100451(n+2).

Conventions:
* A163280 is the square array whose column k lists, in increasing order, the numbers j whose
  largest divisor <= sqrt(j) is k (that divisor is A033676(j)). A divisor d of j satisfies
  d <= sqrt(j) exactly when d * d <= j, so `lowerDiv j` below is A033676(j) for j >= 1; also
  `lowerDiv 0 = 0`, so 0 lies in no column k >= 1.
* `T n k` is the entry in row n (n >= 1) of column k (k >= 1): the n-th smallest j with
  `lowerDiv j = k`, i.e. `Nat.nth` at index n - 1 (this reproduces the array in A163280,
  e.g. column 1 is 1 together with the primes).
* A164005 has offset 0: a(0) = 0 and a(n) = T(5, n) for n >= 1, giving the data
  0, 7, 14, 21, 32, 45, 60, 77, 96, ...
* A100451(m) = 0 for m <= 2 and (m-2)*floor((m^2-2)/(m-2)) for m >= 3 (offset 1; the values at
  m = 0, 1 are never used). The conjecture is stated for every n >= 0.
-/

namespace OMA.S_oeis_a164005

/-- A033676(j): the largest divisor d of j with d * d <= j. -/
def lowerDiv (j : ℕ) : ℕ := ((Nat.divisors j).filter (fun d => d * d ≤ j)).sup id

/-- T n k: row n of column k of the array A163280. -/
noncomputable def T (n k : ℕ) : ℕ := Nat.nth (fun j => lowerDiv j = k) (n - 1)

/-- A164005: zero together with row 5 of A163280 (offset 0). -/
noncomputable def a (n : ℕ) : ℕ := if n = 0 then 0 else T 5 n

/-- A100451(m). -/
def A100451 (n : ℕ) : ℕ := if n ≤ 2 then 0 else (n - 2) * ((n ^ 2 - 2) / (n - 2))

/-- Conjecture: a(n) = A100451(n+2) for all n. -/
theorem main : ∀ n : ℕ, a n = A100451 (n + 2) := by
  sorry

end OMA.S_oeis_a164005
