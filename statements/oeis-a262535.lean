import Mathlib

/-!
# A262535: Triangle read by rows T(n,k) in which column k lists the partial sums of the k-th column of triangle A261699.

Source: https://oeis.org/A262535
Credit: @agchua

In the comments of A262535 (the entry is by Omar E. Pol, Sep 24 2015):
  Conjecture: the sum of row n gives A078471(n), the sum of all odd divisors of all positive integers <= n.

A262535 has offset 1. Row n has length A003056(n) (as the entry says), so it consists of the columns
k >= 1 with k(k+1)/2 <= n; column k starts in row A000217(k) = k(k+1)/2.
A261699 (offset 1) is taken from its name line: column k lists positive terms interleaved with k-1
zeros, starting in row k(k+1)/2; if k is odd the positive terms of column k are k's, if k is even
they are the odd numbers greater than k in increasing order. So A261699(n,k) is positive exactly
when n >= k(k+1)/2 and k divides n - k(k+1)/2, and then it is k (k odd) or k + 1 + 2i (k even),
where i = (n - k(k+1)/2)/k is the number of earlier positive terms of the column. This is `A261699`
below; it reproduces the listed data of A261699 and of A262535.
T(n,k) is the sum of A261699(j,k) over 1 <= j <= n (the rows above k(k+1)/2 contribute 0).
A078471(n) (offset 1) is, by its name line, the sum of all odd divisors of all positive
integers <= n. The conjecture is stated for every n >= 1.
-/

namespace OMA.S_oeis_a262535

/-- A261699(n,k), from its name line (see above). -/
def A261699 (n k : ℕ) : ℕ :=
  if k * (k + 1) / 2 ≤ n ∧ (n - k * (k + 1) / 2) % k = 0 then
    (if k % 2 = 1 then k else k + 1 + 2 * ((n - k * (k + 1) / 2) / k))
  else 0

/-- A262535(n,k): column k lists the partial sums of column k of A261699. -/
def T (n k : ℕ) : ℕ := ∑ j ∈ Finset.Icc 1 n, A261699 j k

/-- The sum of row n of A262535: the columns k >= 1 with k(k+1)/2 <= n. -/
def rowSum (n : ℕ) : ℕ :=
  ∑ k ∈ (Finset.Icc 1 n).filter (fun k => k * (k + 1) / 2 ≤ n), T n k

/-- A078471(n): the sum of all odd divisors of all positive integers <= n. -/
def A078471 (n : ℕ) : ℕ :=
  ∑ m ∈ Finset.Icc 1 n, ∑ d ∈ m.divisors.filter (fun d => d % 2 = 1), d

/-- Pol's conjecture: the sum of row n of A262535 is A078471(n), for every n >= 1. -/
theorem main : ∀ n : ℕ, 1 ≤ n → rowSum n = A078471 n := by
  sorry

end OMA.S_oeis_a262535
