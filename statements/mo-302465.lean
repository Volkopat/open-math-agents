import Mathlib

/-!
# A refinement of Lagrange's four-square theorem

Source: https://mathoverflow.net/questions/302465 (CC BY-SA 4.0).

Question (Z.-W. Sun, who conjectures a positive answer): can each positive integer be written as
`w² + x²(1 + 2y² + 2z²)` with `w, x, y, z ∈ ℤ` and `x ≠ 0`? (Since `2y² + 2z² = (y+z)² + (y-z)²`, a
positive answer implies Lagrange's theorem.)

We state the conjectured positive answer. (The two further conjectures in the post are not stated.)

Formalization notes:
* Checked for all `1 ≤ n ≤ 3000`: every `n` has such a representation.
-/

namespace OMA.S_mo_302465

/-- Every positive integer is `w² + x²(1 + 2y² + 2z²)` with `x ≠ 0`. -/
theorem main : ∀ n : ℕ, 0 < n →
    ∃ w x y z : ℤ, x ≠ 0 ∧ (n : ℤ) = w ^ 2 + x ^ 2 * (1 + 2 * y ^ 2 + 2 * z ^ 2) := by
  sorry

end OMA.S_mo_302465
