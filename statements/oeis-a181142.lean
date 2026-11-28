import Mathlib

/-!
# A181142: Mathar's recurrence

Source: https://oeis.org/A181142
Credit: @ivillar

Status: open conjecture (R. J. Mathar, Jan 27 2022); the entry records it as a conjecture and notes no proof or
verification of it.

A181142 (offset 1): number of permutations of {1,2,...,2n}, say x(1),x(2), ... , x(2n), such that
x(i) + x(i+1) is not equal to 2n-1 for all i, 1<=i<=2n-1;
data 2, 12, 336, 17760, 1543680, 199019520, 35611269120, 8437755432960, ...

Conjecture (R. J. Mathar, Jan 27 2022): D-finite with recurrence
(-n+1)*a(n) +2*(2*n-1)*(n^2-n-1)*a(n-1) +4*n^2*(n-2)*a(n-2) = 0.

Formalization: the entry gives the formula a(n) = Sum_{k=0}^{n-1} binomial(n-1,k) (-2)^k (2n - k)!, and this
formula is used as the definition here (`a` below, with values in ℤ). The sequence has offset 1 and the
recurrence involves a(n-2), so it is stated for n ≥ 3, where every index is at least the offset; it is
checked by the data, for example at n = 3: (-2)*(336) + (50)*(12) + (36)*(2) = 0, and at n = 4:
(-3)*(17760) + (154)*(336) + (128)*(12) = 0.
-/

namespace OMA.S_oeis_a181142

/-- A181142 through the formula of the entry: a(n) = Sum_{k=0}^{n-1} binomial(n-1,k) (-2)^k (2n-k)!. -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range n, ((n - 1).choose k : ℤ) * (-2) ^ k * ((2 * n - k).factorial : ℤ)

/-- Mathar's conjectured recurrence for A181142, for n ≥ 3. -/
theorem main : ∀ n : ℕ, 3 ≤ n →
    (-(n : ℤ) + 1) * a n + 2 * (2 * (n : ℤ) - 1) * ((n : ℤ) ^ 2 - (n : ℤ) - 1) * a (n - 1) +
      4 * (n : ℤ) ^ 2 * ((n : ℤ) - 2) * a (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a181142
