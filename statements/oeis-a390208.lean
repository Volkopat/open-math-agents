import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.Fintype.Pi

/-!
# OEIS A390208

Source: https://oeis.org/A390208
Credit: @leandrohcggo-maker

A colored partition is specified by the multiplicity of each size and color.
In degree n, only sizes and multiplicities at most n can contribute.
-/

namespace OMA.S_oeis_a390208

open scoped BigOperators

/-- Counts the colored partitions of n with total color 1 modulo 3. -/
def a (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin n → Fin 3 → Fin (n + 1))).filter fun m =>
    (∑ j : Fin n, ∑ c : Fin 3, (j.val + 1) * (m j c).val) = n ∧
    (∑ j : Fin n, ∑ c : Fin 3, c.val * (m j c).val) % 3 = 1).card

/-- The terms of 1 / (1 - x^d) with multiplicities up to n. -/
noncomputable def geometric (n d : ℕ) : Polynomial ℤ :=
  ∑ k ∈ Finset.range (n + 1), Polynomial.X ^ (d * k)

/-- The generating-function identity, coefficient by coefficient,
with the denominator 3 cleared. -/
theorem main : ∀ n : ℕ,
    3 * (a n : ℤ) =
      (∏ j ∈ Finset.range n, geometric n (j + 1) ^ 3).coeff n -
      (∏ j ∈ Finset.range n, geometric n (3 * (j + 1))).coeff n := by
  sorry

end OMA.S_oeis_a390208
