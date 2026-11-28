import Mathlib

/-!
# A124753: a(3n+k) = (k+1)*binomial(4n+k, n)/(3n+k+1), where k is n reduced mod 3
Source: https://oeis.org/A124753 (R. J. Mathar, Oct 30 2014)

The sequence is defined by its title (offset 0): writing an index N as N = 3m + k with
m = N / 3 and k = N mod 3, a(N) = (k+1)*binomial(4m+k, m)/(3m+k+1).
We take the values in the rationals (they are integers, but integrality is not needed here).

Conjecture: 8019*n*(n-1)*(n+1)*a(n) + 17496*n*(n-1)*(n-3)*a(n-1)
+ 2592*(3*n-5)*(n-1)*(3*n-16)*a(n-2) + 216*(-224*n^3+48*n^2+3926*n-6331)*a(n-3)
+ 576*(-288*n^3+2448*n^2-6558*n+5443)*a(n-4) + 768*(-288*n^3+3600*n^2-14878*n+20375)*a(n-5)
- 8192*(4*n-23)*(2*n-11)*(4*n-21)*a(n-6) = 0, for every n for which all terms are defined,
i.e. n >= 6.
-/

namespace OMA.S_oeis_a124753

/-- A124753. -/
def a (N : ℕ) : ℚ :=
  (((N % 3 : ℕ) : ℚ) + 1) * ((4 * (N / 3) + N % 3).choose (N / 3) : ℚ) /
    (3 * ((N / 3 : ℕ) : ℚ) + ((N % 3 : ℕ) : ℚ) + 1)

theorem main : ∀ n : ℕ, 6 ≤ n →
    8019 * (n : ℚ) * ((n : ℚ) - 1) * ((n : ℚ) + 1) * a n
      + 17496 * (n : ℚ) * ((n : ℚ) - 1) * ((n : ℚ) - 3) * a (n - 1)
      + 2592 * (3 * (n : ℚ) - 5) * ((n : ℚ) - 1) * (3 * (n : ℚ) - 16) * a (n - 2)
      + 216 * (-224 * (n : ℚ) ^ 3 + 48 * (n : ℚ) ^ 2 + 3926 * (n : ℚ) - 6331) * a (n - 3)
      + 576 * (-288 * (n : ℚ) ^ 3 + 2448 * (n : ℚ) ^ 2 - 6558 * (n : ℚ) + 5443) * a (n - 4)
      + 768 * (-288 * (n : ℚ) ^ 3 + 3600 * (n : ℚ) ^ 2 - 14878 * (n : ℚ) + 20375) * a (n - 5)
      - 8192 * (4 * (n : ℚ) - 23) * (2 * (n : ℚ) - 11) * (4 * (n : ℚ) - 21) * a (n - 6) = 0 := by
  sorry

end OMA.S_oeis_a124753
