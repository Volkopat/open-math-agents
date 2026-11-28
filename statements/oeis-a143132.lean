import Mathlib

/-!
# A143132: Binomial transform of [1, 5, 15, 35, 70, 0, 0, 0, ...].

Source: https://oeis.org/A143132
Credit: @marcelopierry

Conjecture (in the comments of A143132): the rightmost digit of the terms is cyclic:
(1, 6, 6, 6, ... repeat).

Conventions:
* b(k) is the sequence 1, 5, 15, 35, 70, 0, 0, 0, ... (offset 0), i.e. b(k) = binomial(k + 4, 4)
  for k <= 4 (row 4 of A046899) and b(k) = 0 for k > 4.
* The sequence has offset 1 and is the binomial transform a(n) = Sum_{k=0..n-1}
  binomial(n-1, k) * b(k), which gives the data 1, 6, 26, 96, 321, 876, 2006, ...
  (e.g. a(4) = 1 + 3*5 + 3*15 + 35 = 96, as in the example of A143132).
* The rightmost digit is `a n % 10`. The cycle (1, 6, 6, 6) starting at n = 1 is stated as: for
  n >= 1, the last digit is 1 when n % 4 = 1 and 6 otherwise.
-/

namespace OMA.S_oeis_a143132

/-- The finite sequence 1, 5, 15, 35, 70, 0, 0, 0, ... -/
def b (k : ℕ) : ℕ := if k ≤ 4 then (k + 4).choose 4 else 0

/-- A143132(n), offset 1: the binomial transform of b. -/
def a (n : ℕ) : ℕ := ∑ k ∈ Finset.range n, (n - 1).choose k * b k

/-- The last digits of the terms repeat with period 4 as 1, 6, 6, 6. -/
theorem main : ∀ n : ℕ, 1 ≤ n → a n % 10 = if n % 4 = 1 then 1 else 6 := by
  sorry

end OMA.S_oeis_a143132
