import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Finset.Defs

/-!
# Can finitely many real polynomials generate all rational numbers?

Source: https://mathoverflow.net/questions/413085
Predecessor specifying a single trajectory: https://mathoverflow.net/questions/412923

At each step, one polynomial is selected from a fixed finite family and applied
to the current value, starting at zero. The question asks whether one such
trajectory can contain every rational number. Coefficients and intermediate
values are allowed to be arbitrary real numbers: the trajectory need not
consist exclusively of rationals.
-/

namespace OMA.S_mo_413085

def orbit (p : ℕ → Polynomial ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => (p n).eval (orbit p n)

theorem main : ∃ (F : Finset (Polynomial ℝ)) (p : ℕ → Polynomial ℝ),
    (∀ n, p n ∈ F) ∧ (∀ q : ℚ, ∃ n : ℕ, orbit p n = (q : ℝ)) := by
  sorry

end OMA.S_mo_413085
