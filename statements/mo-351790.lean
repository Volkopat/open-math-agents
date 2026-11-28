import Mathlib

/-!
# Special orthogonal matrices with entries of equal absolute value, beyond size 4

Source: https://mathoverflow.net/questions/351790
Asked by MathOverflow user Paul B. Slater.

The asker starts from the `4 × 4` matrix `Q ∈ SO(4)` of Li and Qiao, all of whose entries are
`± 1/2`, with positive last row and last column, and asks whether `n × n` special orthogonal
matrices, all of whose entries have the same absolute value (with the entries of the last row
and last column positive), are possible for `n ≠ 4`.

Translation choices.
* We formalize the affirmative answer for the size `n = 8` (the next size after `4` for which
  such a matrix can exist, since by Paley the size must be `1`, `2` or a multiple of `4`; size `1`
  is trivial, and size `2` is impossible with the positivity requirement).
* `Q` is a real `8 × 8` matrix indexed by `Fin 8`; special orthogonal means `Qᵀ * Q = 1` and
  `det Q = 1`; all entries have the same absolute value as the entry `Q 0 0`; and the entries of
  the last row and of the last column (index `7`) are positive, as requested in the post.
-/

namespace OMA.S_mo_351790

open Matrix

theorem main :
    ∃ Q : Matrix (Fin 8) (Fin 8) ℝ, Qᵀ * Q = 1 ∧ Q.det = 1 ∧
      (∀ i j, |Q i j| = |Q 0 0|) ∧ (∀ i, 0 < Q i 7 ∧ 0 < Q 7 i) := by
  sorry

end OMA.S_mo_351790
