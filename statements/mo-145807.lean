import Mathlib

/-!
# Derivatives of polynomials majorized by `max(1, |x|^d)`

Source: https://mathoverflow.net/questions/145807 (CC BY-SA 4.0).

Suppose `p` is a real polynomial with `|p(x)| ≤ max(1, |x|^d)` for all real `x`. How large can `|p'(1)|`
be? The asker conjectures `|p'(1)| = O(d)` (the optima for `d = 0, 1, 2` are `0, 1, 1 + √2`).

We state the conjecture: one constant `C` with `|p'(1)| ≤ C d` for all `d` and all such `p`.

Formalization notes:
* For `d = 0` the hypothesis forces `p` to be constant, so the bound `C · 0` is the right one there.
-/

namespace OMA.S_mo_145807

/-- `|p'(1)| = O(d)` for real polynomials with `|p(x)| ≤ max(1, |x|^d)`. -/
theorem main : ∃ C : ℝ, ∀ d : ℕ, ∀ p : Polynomial ℝ,
    (∀ x : ℝ, |p.eval x| ≤ max 1 (|x| ^ d)) → |p.derivative.eval 1| ≤ C * d := by
  sorry

end OMA.S_mo_145807
