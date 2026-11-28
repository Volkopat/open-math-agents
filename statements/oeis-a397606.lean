import Mathlib

/-!
# A397606: a(n) = denominator of A069835(n)/2^n.

Source: https://oeis.org/A397606
Credit: @agchua

In the formula section of A397606 (entry by Zhuorui He, Jul 02 2026):
  Conjecture: a(2*n) = 2^A005187(n), a(2*n+1) = max(1,a(2*n)/2).
Definitions used:
* A069835(n) = Sum_{k=0..n} binomial(n,k)^2*3^k, as in the formula section of A069835 and in the
  PARI program of A397606: a(n)=denominator(sum(k=0, n, binomial(n, k)^2*3^k)/2^n).
* A005187(n) = the 2-adic valuation of (2n)!, as in the PARI program of A005187 by Michael Somos,
  valuation((2*n)!, 2); by Legendre's formula this is the sequence of its name line,
  a(n) = a(floor(n/2)) + n with a(0) = 0.
The offset of A397606 is 0, and the conjecture is stated for every n ≥ 0. The quotient a(2n)/2 is
read in ℚ, so for n = 0 the claim is a(1) = max(1, 1/2) = 1.
-/

namespace OMA.S_oeis_a397606

/-- A069835(n) = Sum_{k=0..n} binomial(n,k)^2 * 3^k. -/
def A069835 (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), (n.choose k) ^ 2 * 3 ^ k

/-- A005187(n) = the 2-adic valuation of (2n)!. -/
noncomputable def A005187 (n : ℕ) : ℕ := padicValNat 2 (2 * n).factorial

/-- A397606(n) = denominator of A069835(n)/2^n. -/
def a (n : ℕ) : ℕ := ((A069835 n : ℚ) / 2 ^ n).den

/-- The conjecture of A397606: a(2n) = 2^A005187(n) and a(2n+1) = max(1, a(2n)/2). -/
theorem main : ∀ n : ℕ, a (2 * n) = 2 ^ A005187 n ∧
    (a (2 * n + 1) : ℚ) = max 1 ((a (2 * n) : ℚ) / 2) := by
  sorry

end OMA.S_oeis_a397606
