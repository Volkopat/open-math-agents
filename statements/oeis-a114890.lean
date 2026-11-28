import Mathlib

/-!
# A114890: First differences of A114889.

Source: https://oeis.org/A114890
Credit: @agchua

Formula line of A114890 (the entry is by John W. Layman, Jan 04 2006):
  Conjecture. a(1)=2 and, for n>1, a(n)=1+3+9+...+3^(k-1) + 2, if n=3^k, a(n)=a(n-3^k), if
  3^k < n < 2*3^k - 1, else a(n)=1. (This has been verified for n<=3000.)
A114890 has offset 1 and a(n) = A114889(n+1) - A114889(n). By its name, A114889 (offset 1) is:
a(1)=1 and, for n>1, a(n) is the smallest integer greater than a(n-1) such that a(n)+a(i) is not
a power of 3, for i=1,..., n-1.
This greedy rule is `IsA114889` below: a sequence s (its value at 0 is never used) satisfies it
when s(1) = 1 and, for every n >= 2, s(n) is the least m with s(n-1) < m and m + s(i) different
from 3^j for every i in 1..n-1 and every j. The first part of `main` says that such a sequence
exists, so that the second part is not vacuous; the rule determines the sequence on n >= 1, and
the second part states the conjecture for every sequence that satisfies it. The differences are
taken in the integers (`d` below). In the conjecture, 1+3+9+...+3^(k-1) is the sum of 3^i over
i < k, and a(n-3^k) in the second case is A114890 itself; the three cases are stated as three
implications for every n > 1 (the third one when n is neither a power of 3 nor in any interval
3^k < n < 2*3^k - 1).
-/

namespace OMA.S_oeis_a114890

/-- The greedy rule that defines A114889. -/
def IsA114889 (s : ℕ → ℕ) : Prop :=
  s 1 = 1 ∧ ∀ n : ℕ, 2 ≤ n →
    IsLeast {m : ℕ | s (n - 1) < m ∧ ∀ i ∈ Finset.Icc 1 (n - 1), ∀ j : ℕ, m + s i ≠ 3 ^ j} (s n)

/-- The first differences s(n+1) - s(n), in the integers. -/
def d (s : ℕ → ℕ) (n : ℕ) : ℤ := (s (n + 1) : ℤ) - (s n : ℤ)

/-- Layman's conjecture on the first differences of A114889. -/
theorem main :
    (∃ s : ℕ → ℕ, IsA114889 s) ∧
    ∀ s : ℕ → ℕ, IsA114889 s →
      d s 1 = 2 ∧
      ∀ n : ℕ, 1 < n →
        (∀ k : ℕ, n = 3 ^ k → d s n = ((∑ i ∈ Finset.range k, 3 ^ i : ℕ) : ℤ) + 2) ∧
        (∀ k : ℕ, 3 ^ k < n → n < 2 * 3 ^ k - 1 → d s n = d s (n - 3 ^ k)) ∧
        ((¬ ∃ k : ℕ, n = 3 ^ k) → (¬ ∃ k : ℕ, 3 ^ k < n ∧ n < 2 * 3 ^ k - 1) → d s n = 1) := by
  sorry

end OMA.S_oeis_a114890
