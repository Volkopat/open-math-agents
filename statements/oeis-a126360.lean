import Mathlib

/-!
# The recurrence and generating function recorded in OEIS A126360

Source: https://oeis.org/A126360
Source data: https://raw.githubusercontent.com/oeis/oeisdata/main/seq/A126/A126360.seq
Credit: @Heart-galaxy

Leading zeroes are allowed. We use the equivalent matrix formula recorded
by Robert Israel, with one matrix entry for each possible transition and
all six digits as possible endpoints. Index zero counts the empty word.

The denominator of Colin Barker's generating function has constant term
one. We state the generating-function identity after multiplying by this
denominator, together with the stated recurrence for n > 3.
-/

namespace OMA.S_oeis_a126360

open Finset Matrix PowerSeries

def adjacency : Matrix (Fin 6) (Fin 6) ℤ :=
  Matrix.of fun i j => if i.val ≤ j.val + 1 ∧ j.val ≤ i.val + 1 then 1 else 0

def ones : Fin 6 → ℤ := fun _ => 1

def a : ℕ → ℤ
  | 0 => 1
  | n + 1 => ∑ i : Fin 6, (adjacency ^ n *ᵥ ones) i

noncomputable def generating : PowerSeries ℤ := PowerSeries.mk a

noncomputable def denominator : PowerSeries ℤ := X ^ 3 + C 3 * X ^ 2 - C 4 * X + 1

noncomputable def numerator : PowerSeries ℤ := -X ^ 3 - C 5 * X ^ 2 + C 2 * X + 1

theorem main :
    (∀ n : ℕ, 3 < n → a n = 4 * a (n - 1) - 3 * a (n - 2) - a (n - 3)) ∧
      denominator * generating = numerator := by
  sorry

end OMA.S_oeis_a126360
