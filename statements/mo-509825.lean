import Mathlib

/-!
# Do there exist a, b < n with both an + b and bn + a prime?

Source: https://mathoverflow.net/questions/509825 (CC BY-SA 4.0).

For every integer `n > 2`, are there positive integers `a, b < n` with `(a, b) ≠ (1, 1)` such
that both `an + b` and `bn + a` are prime? `main` states the expected yes.
-/

namespace OMA.S_mo_509825

theorem main : ∀ n : ℕ, 2 < n → ∃ a b : ℕ, 0 < a ∧ a < n ∧ 0 < b ∧ b < n ∧ (a, b) ≠ (1, 1) ∧
    (a * n + b).Prime ∧ (b * n + a).Prime := by
  sorry

end OMA.S_mo_509825
