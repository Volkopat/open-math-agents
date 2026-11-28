import Mathlib

/-!
# OEIS A387957

The conjectured generating function counts partitions whose colour sum is 1 modulo 4.
Source: https://oeis.org/A387957 (Thomas Hutton)
Credit: @AShahver

In degree n, every positive part size is at most n and every multiplicity is at
most n. The two infinite Euler products can also be cut off at part size n
when taking their degree-n coefficient, since the omitted factors are 1
through degree n.
-/

namespace OMA.S_oeis_a387957

open scoped BigOperators

def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun m : Fin n → Fin 4 → Fin (n + 1) =>
    (∑ j : Fin n, ∑ c : Fin 4, (j.val + 1) * (m j c).val) = n ∧
    (∑ j : Fin n, ∑ c : Fin 4, c.val * (m j c).val) % 4 = 1)).card

theorem main : ∀ n : ℕ,
    (a n : ℚ) = (1 / 4 : ℚ) * PowerSeries.coeff n
      ((∏ j ∈ Finset.range n, ((1 - (PowerSeries.X : PowerSeries ℚ) ^ (j + 1))⁻¹) ^ 4) -
       (∏ j ∈ Finset.range n, ((1 - (PowerSeries.X : PowerSeries ℚ) ^ (2 * (j + 1)))⁻¹) ^ 2)) := by
  sorry

end OMA.S_oeis_a387957
