import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Odd-position bits of n: two closed forms (OEIS A059906)

Source: https://oeis.org/A059906 (OEIS Foundation, CC BY-SA 4.0).
Formalization: @thomasfredrickson.

A059906 (offset 0: 0, 0, 1, 1, 0, 0, 1, 1, 2, 2, 3, 3, ...) is the second
index in the decomposition n = A000695(A059905(n)) + 2*A000695(a(n)), where
A000695 lists the sums of distinct powers of 4. The entry's formula section
gives the equivalent description used here: write n = Sum b_j*2^j in binary,
then a(n) = Sum b_(2j+1)*2^j. The bit b_(2j+1) is (n / 2^(2j+1)) mod 2, and it
vanishes for j >= n, so the sum is taken over j < n.

Conjecture (V. Yanev, formula section), for every n >= 0:

  a(n) = n - (1/2)*Sum_{k=1..n} (sqrt(2)^A007814(k) + (-sqrt(2))^A007814(k))
       = -Sum_{k=1..n} (-1)^k * 2^floor(k/2) * floor(n/2^k),

where A007814(k) is the 2-adic valuation of k. The first equality is stated
in the real numbers, the second in the integers.
-/

namespace OMA.S_oeis_a059906

/-- A059906: the number whose binary digits are the odd-position binary digits of `n`. -/
def a (n : ℕ) : ℕ := ∑ j ∈ Finset.range n, (n / 2 ^ (2 * j + 1) % 2) * 2 ^ j

theorem main : ∀ n : ℕ,
    ((a n : ℝ) = (n : ℝ) - (1 / 2) * ∑ k ∈ Finset.Icc 1 n,
      (Real.sqrt 2 ^ padicValNat 2 k + (-Real.sqrt 2) ^ padicValNat 2 k)) ∧
    ((a n : ℤ) = -∑ k ∈ Finset.Icc 1 n,
      (-1 : ℤ) ^ k * 2 ^ (k / 2) * ((n / 2 ^ k : ℕ) : ℤ)) := by
  sorry

end OMA.S_oeis_a059906
