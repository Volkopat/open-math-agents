import Mathlib

/-!
# A133297: Peter Bala's closed form (OEIS A133297)

Source: https://oeis.org/A133297 (OEIS Foundation, CC BY-SA 4.0).
Formalization: @thomasfredrickson.

The sequence is a(n) = n! * Sum_{k=1..n} (-1)^(k+1) * n^(n-k-1) / (n-k)!
(offset 0, a(0) = 0, then 1, 1, 5, 34, 329, ...). The term k = n carries the
exponent -1, so the definition is written over the reals with an integer
exponent, exactly as in the name of the entry.

Formalized here is the conjecture of Peter Bala (Jul 23 2021) in the formula
section: for n >= 1,
  a(n) = (n-1)! * ( Sum_{k >= 0} (-1)^k * n^(n+k) / (n+k)!  -  (-1/e)^n ).
The infinite sum is Mathlib's `tsum` over the naturals. The entry reports the
conjecture as true (Thomas Scheuerle, Nov 17 2023).
-/

namespace OMA.S_oeis_a133297

noncomputable def a (n : ℕ) : ℝ :=
  (n.factorial : ℝ) * ∑ k ∈ Finset.Icc 1 n,
    (-1 : ℝ) ^ (k + 1) * (n : ℝ) ^ ((n : ℤ) - (k : ℤ) - 1) / ((n - k).factorial : ℝ)

theorem main : ∀ n : ℕ, 1 ≤ n →
    a n = ((n - 1).factorial : ℝ) *
      ((∑' k : ℕ, (-1 : ℝ) ^ k * (n : ℝ) ^ (n + k) / ((n + k).factorial : ℝ))
        - (-1 / Real.exp 1) ^ n) := by
  sorry

end OMA.S_oeis_a133297
