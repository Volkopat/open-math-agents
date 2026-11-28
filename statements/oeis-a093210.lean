import Mathlib

/-!
# A093210: Row sums of A092964.

Source: https://oeis.org/A093210
Credit: @agchua

Ralf Stephan (Apr 24 2004), in the formula section of A093210:
  Conjecture: a(n) = A060477(n+4) - 2.

A093210 has offset 0. A092964 (offset 0) is the triangle of the numbers > 1 in A051168, with
a(0) = 1: its row n (n >= 0) is A051168(n+4, j) for j = 2..n+2, that is T(n,k) = A051168(n+4, k+2)
for k = 0..n (as in the Mathematica program of A092964, which also gives the first row 1 =
A051168(4, 2)). A051168(h, k) is the number of binary Lyndon words with k ones and h - k zeros;
for h > 0 it equals (1/h) * Sum_{d | gcd(h, k)} mu(d) * binomial(h/d, k/d) (formula of Andrew
Howroyd in A051168), which is `L` below. A060477 (offset 1) is (1/n) * Sum_{d | n} mu(d) *
A000051(n/d) with A000051(m) = 2^m + 1. All values are integers; they are computed in ℚ because
the formulas divide. The conjecture is stated for all n >= 0 (every index n + 4 is at least 4).
-/

namespace OMA.S_oeis_a093210

/-- A051168(h, k) for h > 0: binary Lyndon words with k ones and h - k zeros (Howroyd's formula). -/
noncomputable def L (h k : ℕ) : ℚ :=
  (∑ d ∈ (Nat.gcd h k).divisors,
    (ArithmeticFunction.moebius d : ℚ) * ((Nat.choose (h / d) (k / d) : ℕ) : ℚ)) / h

/-- A092964 as a triangle: T(n, k) = A051168(n + 4, k + 2) for 0 <= k <= n. -/
noncomputable def T (n k : ℕ) : ℚ := L (n + 4) (k + 2)

/-- A093210(n): the sum of row n of A092964. -/
noncomputable def a (n : ℕ) : ℚ := ∑ k ∈ Finset.range (n + 1), T n k

/-- A060477(n) = (1/n) * Sum_{d | n} mu(d) * (2^(n/d) + 1). -/
noncomputable def A060477 (n : ℕ) : ℚ :=
  (∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℚ) * ((2 : ℚ) ^ (n / d) + 1)) / n

/-- Stephan's conjecture: a(n) = A060477(n+4) - 2 for all n >= 0. -/
theorem main : ∀ n : ℕ, a n = A060477 (n + 4) - 2 := by
  sorry

end OMA.S_oeis_a093210
