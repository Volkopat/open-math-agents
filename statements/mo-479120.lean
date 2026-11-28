import Mathlib.Data.Nat.GCD.Basic

/-!
The generalized Rowland recurrence starts at index h with value x.
The question proposes the bounds 3(n+1)/2 ≤ a_n ≤ 3n for x > h.

Source: https://mathoverflow.net/questions/479120
Crosspost: https://math.stackexchange.com/questions/4973119
-/

namespace OMA.S_mo_479120

def a (h x : ℕ) : ℕ → ℕ
  | 0 => x
  | t + 1 =>
    let previous := a h x t
    previous + Nat.gcd previous (h + t + 1)

theorem main :
    ∀ h x t : ℕ, 0 < h → h < x → 0 < t →
      3 * (h + t + 1) ≤ 2 * a h x t ∧ a h x t ≤ 3 * (h + t) := by
  sorry

end OMA.S_mo_479120
