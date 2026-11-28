import Mathlib

/-!
# A281946: Kurkov's conjecture a(n) = 3*A394975(2,n)/binomial(n+2,2) = n*(a(n-1) + A281912(n) - A281912(n-1))

Source: https://oeis.org/A281946
Credit: @ivillar

Status: open conjecture (Mikhail Kurkov, Apr 10 2026); the entry records it as a conjecture and notes no proof or
verification of it.

A281946 (offset 1): number of sequences of balls colored with at most n colors such that exactly two balls
are of a color seen earlier in the sequence;
data 1, 16, 195, 2248, 26245, 318936, 4082071, 55289200, 793525833, 12063384640, ...

Conjecture (Mikhail Kurkov, Apr 10 2026):
a(n) = 3*A394975(2,n)/binomial(n+2,2) = n*(a(n-1) + A281912(n) - A281912(n-1)).

Formalization: the three sequences are defined by the formulas of their entries.
  A281946: a(n) = n! * Sum_{k=3..n+2} (binomial(k,3)+3*binomial(k,4))/(n+2-k)! (formula of the entry; `a` below).
  A281912: a(n) = n! * Sum_{k=2..n+1} binomial(k,2)/(n+1-k)! (formula of that entry; `b` below; 1, 8, 57, 424, ...).
  A394975: A(n,k) = (1/(n+1)!) * Sum_{j=0..k} (n+k)! * Stirling2(n+j,j) / (k-j)! (definition of that array;
  `A` below, with `Nat.stirlingSecond` the Stirling numbers of the second kind).
All values are taken in ℚ. `main` has two parts: the first equality, for n ≥ 1 (the offset), and the second
equality, for n ≥ 2, where a(n-1) and A281912(n-1) are at least the offset. They are checked by the data,
for example at n = 2: a(2) = 16, A394975(2,2) = 32 and 3*32/binomial(4,2) = 16, and
2*(a(1) + A281912(2) - A281912(1)) = 2*(1 + 8 - 1) = 16; at n = 3: a(3) = 195 = 3*(16 + 57 - 8).
-/

namespace OMA.S_oeis_a281946

/-- A281946 through the formula of the entry:
a(n) = n! * Sum_{k=3..n+2} (binomial(k,3)+3*binomial(k,4))/(n+2-k)!. -/
def a (n : ℕ) : ℚ :=
  (n.factorial : ℚ) *
    ∑ k ∈ Finset.Icc 3 (n + 2), ((k.choose 3 : ℚ) + 3 * (k.choose 4 : ℚ)) / ((n + 2 - k).factorial : ℚ)

/-- A281912(n) = n! * Sum_{k=2..n+1} binomial(k,2)/(n+1-k)!. -/
def b (n : ℕ) : ℚ :=
  (n.factorial : ℚ) * ∑ k ∈ Finset.Icc 2 (n + 1), (k.choose 2 : ℚ) / ((n + 1 - k).factorial : ℚ)

/-- A394975: A(n,k) = (1/(n+1)!) * Sum_{j=0..k} (n+k)! * Stirling2(n+j,j) / (k-j)!. -/
def A (n k : ℕ) : ℚ :=
  (1 / ((n + 1).factorial : ℚ)) *
    ∑ j ∈ Finset.range (k + 1),
      ((n + k).factorial : ℚ) * (Nat.stirlingSecond (n + j) j : ℚ) / ((k - j).factorial : ℚ)

/-- Kurkov's conjecture for A281946: a(n) = 3*A394975(2,n)/binomial(n+2,2) for n ≥ 1, and
a(n) = n*(a(n-1) + A281912(n) - A281912(n-1)) for n ≥ 2. -/
theorem main :
    (∀ n : ℕ, 1 ≤ n → a n = 3 * A 2 n / ((n + 2).choose 2 : ℚ)) ∧
    (∀ n : ℕ, 2 ≤ n → a n = (n : ℚ) * (a (n - 1) + b n - b (n - 1))) := by
  sorry

end OMA.S_oeis_a281946
