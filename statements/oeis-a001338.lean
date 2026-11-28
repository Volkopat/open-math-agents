import Mathlib

/-!
# A001338: -1 + Sum (k-1)! C(n,k), k = 1..n for n > 0, a(0) = 1

Source: https://oeis.org/A001338
Credit: @ivillar

Offset 0, data 1, 0, 2, 7, 23, 88, 414, 2371, ... As in the name, a(0) = 1 and
a(n) = -1 + Sum_{k=1..n} (k-1)! * binomial(n,k) for n > 0.

Conjecture (R. J. Mathar, Feb 16 2014):
a(n) +(-n-1)*a(n-1) +2*(n-1)*a(n-2) +(-n+2)*a(n-3)=0.
At n = 3 the left side is 7 - 8 + 0 - 1 = -2 (the value a(0) = 1 is set apart from the sum
formula), so the recurrence is read from n = 4 on (n ≥ 4); it is stated over the integers.

So `main` is the corrected recurrence (n ≥ 4): over the full defined range the recurrence as
written in the entry fails, with n = 3 a counterexample.
-/

namespace OMA.S_oeis_a001338

/-- a(0) = 1 and a(n) = -1 + Sum_{k=1..n} (k-1)! * binomial(n,k) for n > 0. -/
def a (n : ℕ) : ℤ :=
  if n = 0 then 1 else -1 + ∑ k ∈ Finset.Icc 1 n, ((k - 1).factorial : ℤ) * (n.choose k : ℤ)

/-- Mathar's conjectured recurrence, from n = 4 on. -/
theorem main : ∀ n : ℕ, 4 ≤ n →
    a n + (-(n : ℤ) - 1) * a (n - 1) + 2 * ((n : ℤ) - 1) * a (n - 2) + (-(n : ℤ) + 2) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a001338
