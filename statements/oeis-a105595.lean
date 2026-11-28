import Mathlib

/-!
# A105595: the row sums of A105594 are odd

Source: https://oeis.org/A105595
Credit: @ivillar

Status: known result. Bing Gao (Sep 22 2026) proved the conjecture in the OEIS entry: modulo 2
the n-th row sum is Sum_{j=0..n} s_j 2^j = s_0 = 1 with s_j = abs(mu(binomial(n,j))).

A105595 (offset 0): row sums of the number triangle A105594 = abs(A103447)*A047999 mod 2, where
T(n, k) = mod(Sum_{j=0..n} abs(mu(binomial(n, j)))*mod(binomial(j, k), 2), 2);
data 1, 1, 3, 1, 3, 3, 3, 1, 3, 3, 3, 3, 3, 7, 3, 9, ...
Conjecture: all terms are odd.

Formalization notes.
* mu is the Moebius function ArithmeticFunction.moebius, mod is the remainder Int.emod, and
  a(n) = Sum_{k=0..n} T(n, k), computed in ℤ.
-/

namespace OMA.S_oeis_a105595

/-- A105594: T(n, k) = (Sum_{j=0..n} |mu(binomial(n, j))| * (binomial(j, k) mod 2)) mod 2. -/
def T (n k : ℕ) : ℤ :=
  (∑ j ∈ Finset.range (n + 1),
    |ArithmeticFunction.moebius (n.choose j)| * ((j.choose k : ℤ) % 2)) % 2

/-- A105595: the row sums of A105594. -/
def a (n : ℕ) : ℤ := ∑ k ∈ Finset.range (n + 1), T n k

/-- The conjecture: all terms are odd. -/
theorem main : ∀ n : ℕ, Odd (a n) := by
  sorry

end OMA.S_oeis_a105595
