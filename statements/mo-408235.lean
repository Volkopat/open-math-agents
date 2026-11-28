import Mathlib

/-!
# Uniqueness of the circular arrangement of 1, ..., 32 with square adjacent sums

Source: https://mathoverflow.net/questions/408235
Asked by MathOverflow user Sayan Dutta.

The post shows a circular arrangement of the numbers `1, 2, ..., 32` in which any two adjacent
numbers add up to a perfect square, and asks several questions about it: whether other `n`
admit such circles, which family they form, and whether that arrangement is unique.

This file formalizes the uniqueness question for the arrangement shown, i.e. for `n = 32`.

Translation choices.
* A circular arrangement of `1, ..., n` is a map `c : Fin n → ℕ` that is injective with values
  in `[1, n]` (hence a bijection onto `{1, ..., n}`), such that `c i + c (i + 1)` is a perfect
  square for every `i`, indices taken cyclically (`finRotate`).
* Arrangements on a circle are compared up to the symmetries of the circle: rotations
  `i ↦ i + k` and reflections `i ↦ k - i` of the index set `Fin 32`.
* `main` is the affirmative answer for `n = 32`: any two such arrangements of `1, ..., 32`
  agree up to a rotation or a reflection.
-/

namespace OMA.S_mo_408235

/-- `c` is a circular arrangement of `1, ..., n` in which adjacent numbers sum to a square. -/
def IsSquareCircle (n : ℕ) (c : Fin n → ℕ) : Prop :=
  Function.Injective c ∧ (∀ i, 1 ≤ c i ∧ c i ≤ n) ∧ ∀ i, IsSquare (c i + c (finRotate n i))

theorem main :
    ∀ c d : Fin 32 → ℕ, IsSquareCircle 32 c → IsSquareCircle 32 d →
      ∃ k : Fin 32, (∀ i, d i = c (i + k)) ∨ (∀ i, d i = c (k - i)) := by
  sorry

end OMA.S_mo_408235
