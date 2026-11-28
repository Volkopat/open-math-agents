import Mathlib

/-!
# Nontrivial integer solutions of `w^5 + x^5 + y^5 + z^5 = 1`

Source: https://mathoverflow.net/questions/515053/on-the-integer-solutions-to-w5x5y5z5-1
Credit: @shc261392

Question. Are there integers `w, x, y, z` with `w^5 + x^5 + y^5 + z^5 = 1` that are nontrivial,
where nontrivial means `|wxyz| > 1`?

Reading used here: the affirmative answer, stated as the existence of such a solution.
-/

namespace OMA.S_mo_515053

theorem main : ∃ w x y z : ℤ, w ^ 5 + x ^ 5 + y ^ 5 + z ^ 5 = 1 ∧ 1 < |w * x * y * z| := by
  sorry

end OMA.S_mo_515053
