import Mathlib

/-!
# A024199: a(n) = (2n-1)!! * Sum_{k=0..n-1}(-1)^k/(2k+1).

Source: https://oeis.org/A024199
Credit: @agchua

Peter Bala (Nov 15 2016), in the formula section of A024199:
  Conjecture: a(n) = 1/2*Sum_{k = 0..2*n-1} (-1)^(n-k+1)*k!*(2*n - 2*k - 3)!!, where the double
  factorial of an odd integer (positive or negative) may be defined in terms of the gamma function
  as (2*N - 1)!! = 2^((N+1)/2)*Gamma(N/2 + 1)/sqrt(Pi).

The gamma formula is the standard extension of the double factorial to an odd integer N, positive
or negative: N!! = 2^((N+1)/2)*Gamma(N/2+1)/sqrt(Pi). It gives 1!! = 1, 3!! = 3, 5!! = 15,
(-1)!! = 1, (-3)!! = -1, (-5)!! = 1/3, (-7)!! = -1/15. (Read with 2N-1 in place of N on the left,
as printed, it would give 3!! = 2^(3/2)/sqrt(Pi) for N = 2, so the left side is read as N!! for the
odd number N.) Below this is `dfact N`, a real number; the conjecture applies it to the odd integer
N = 2n-2k-3. The sign (-1)^(n-k+1) has an integer exponent.
Definition of a(n) (offset 0): (2n-1)!! is `Nat.doubleFactorial (2 * n - 1)` (for n = 0 the
truncated index gives 0!! = 1, and a(0) = 0 anyway because the sum is empty); the sum is taken in ℚ.
The claim is stated for every n >= 0 (for n = 0 both sides are 0).
-/

namespace OMA.S_oeis_a024199

/-- The double factorial of an odd integer N via the gamma function:
N!! = 2^((N+1)/2)*Gamma(N/2+1)/sqrt(Pi). -/
noncomputable def dfact (N : ℤ) : ℝ :=
  (2 : ℝ) ^ (((N : ℝ) + 1) / 2) * Real.Gamma ((N : ℝ) / 2 + 1) / Real.sqrt Real.pi

/-- A024199: a(n) = (2n-1)!! * Sum_{k=0..n-1} (-1)^k/(2k+1). -/
noncomputable def a (n : ℕ) : ℚ :=
  (Nat.doubleFactorial (2 * n - 1) : ℚ) * ∑ k ∈ Finset.range n, (-1 : ℚ) ^ k / (2 * k + 1)

/-- Bala's conjecture: a(n) = 1/2*Sum_{k=0..2n-1} (-1)^(n-k+1)*k!*(2n-2k-3)!!. -/
theorem main : ∀ n : ℕ, (a n : ℝ) = 1 / 2 * ∑ k ∈ Finset.range (2 * n),
    (-1 : ℝ) ^ ((n : ℤ) - k + 1) * (Nat.factorial k : ℝ) * dfact (2 * (n : ℤ) - 2 * k - 3) := by
  sorry

end OMA.S_oeis_a024199
