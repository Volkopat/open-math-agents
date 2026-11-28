import Mathlib

/-!
# A281912: Kurkov's conjecture a(n) = 2*A394975(1,n)/(n+1) = n*(a(n-1) + A000522(n) - A000522(n-1))

Source: https://oeis.org/A281912
Credit: @ivillar

Status: open conjecture (Mikhail Kurkov, Apr 10 2026); the entry records it as a conjecture and notes no proof or
verification of it.

A281912 (offset 1): number of sequences of balls colored with at most n colors such that exactly one ball
is of a color seen earlier in the sequence;
data 1, 8, 57, 424, 3425, 30336, 294553, 3123632, 36003969, 448816600, 6022033721, ...

Conjecture (Mikhail Kurkov, Apr 10 2026):
a(n) = 2*A394975(1,n)/(n+1) = n*(a(n-1) + A000522(n) - A000522(n-1)).

Formalization: the three sequences are defined by the formulas of their entries.
  A281912: a(n) = n! * Sum_{k=2..n+1} binomial(k,2)/(n+1-k)! (formula of the entry; `a` below).
  A000522: a(n) = Sum_{k=0..n} n!/k! (`e` below; 1, 2, 5, 16, 65, 326, ...).
  A394975: A(n,k) = (1/(n+1)!) * Sum_{j=0..k} (n+k)! * Stirling2(n+j,j) / (k-j)! (definition of that array;
  `A` below, with `Nat.stirlingSecond` the Stirling numbers of the second kind).
All values are taken in ℚ. `main` has two parts: the first equality, for n ≥ 1 (the offset), and the second
equality, for n ≥ 2, where a(n-1) is at least the offset. They are checked by the data, for example at
n = 2: a(2) = 8, A394975(1,2) = 12 and 2*12/3 = 8, and 2*(a(1) + A000522(2) - A000522(1)) = 2*(1 + 5 - 2) = 8;
at n = 3: a(3) = 57 = 3*(8 + 16 - 5).
-/

namespace OMA.S_oeis_a281912

/-- A281912 through the formula of the entry: a(n) = n! * Sum_{k=2..n+1} binomial(k,2)/(n+1-k)!. -/
def a (n : ℕ) : ℚ :=
  (n.factorial : ℚ) * ∑ k ∈ Finset.Icc 2 (n + 1), (k.choose 2 : ℚ) / ((n + 1 - k).factorial : ℚ)

/-- A000522(n) = Sum_{k=0..n} n!/k!. -/
def e (n : ℕ) : ℚ := ∑ k ∈ Finset.range (n + 1), (n.factorial : ℚ) / (k.factorial : ℚ)

/-- A394975: A(n,k) = (1/(n+1)!) * Sum_{j=0..k} (n+k)! * Stirling2(n+j,j) / (k-j)!. -/
def A (n k : ℕ) : ℚ :=
  (1 / ((n + 1).factorial : ℚ)) *
    ∑ j ∈ Finset.range (k + 1),
      ((n + k).factorial : ℚ) * (Nat.stirlingSecond (n + j) j : ℚ) / ((k - j).factorial : ℚ)

/-- Kurkov's conjecture for A281912: a(n) = 2*A394975(1,n)/(n+1) for n ≥ 1, and
a(n) = n*(a(n-1) + A000522(n) - A000522(n-1)) for n ≥ 2. -/
theorem main :
    (∀ n : ℕ, 1 ≤ n → a n = 2 * A 1 n / ((n : ℚ) + 1)) ∧
    (∀ n : ℕ, 2 ≤ n → a n = (n : ℚ) * (a (n - 1) + e n - e (n - 1))) := by
  sorry

end OMA.S_oeis_a281912
