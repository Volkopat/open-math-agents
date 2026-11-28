import Mathlib

/-!
# A265942: G.f. A(x) satisfies: x = Sum_{n>=1} x^n * A(-n*x).

Source: https://oeis.org/A265942
Credit: @agchua

Formula line of A265942 (unsigned; the entry is by Paul D. Hanna, Jan 06 2016):
  a(n) = 2 (mod 4) for n>2 [conjecture].
The sequence has offset 0. The entry also gives the recursion
a(n) = Sum_{k=0..n-1} (-1)^(n-k+1) * (n-k+1)^k * a(k), for n>0 with a(0)=1,
which is the coefficient comparison of the functional equation: Sum_{m>=1} x^m * A(-m*x) =
Sum_{m>=1} Sum_{k>=0} a(k) * (-m)^k * x^(m+k), and its coefficient of x^(N+1) is
Sum_{k=0..N} a(k) * (k-N-1)^k, which must be 1 for N = 0 and 0 for N >= 1; the term k = N is
(-1)^N * a(N). The definition below is this recursion (with n = N + 1 in the second case).
The claim is stated for n > 2, as in the entry.
-/

namespace OMA.S_oeis_a265942

/-- A265942: a(0) = 1 and a(n) = Sum_{k=0..n-1} (-1)^(n-k+1) * (n-k+1)^k * a(k) for n > 0. -/
def a : ℕ → ℤ
  | 0 => 1
  | n + 1 => ∑ k : Fin (n + 1),
      (-1 : ℤ) ^ (n + 1 - (k : ℕ) + 1) * ((n + 1 - (k : ℕ) + 1 : ℕ) : ℤ) ^ (k : ℕ) * a k

/-- The formula line's conjecture: a(n) = 2 (mod 4) for n > 2. -/
theorem main : ∀ n : ℕ, 2 < n → a n % 4 = 2 := by
  sorry

end OMA.S_oeis_a265942
