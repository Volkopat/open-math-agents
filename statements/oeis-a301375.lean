import Mathlib

/-!
# A301375: Number of ways to write n as x^2 + y^2 + z^2 + w^2 with x,y,z nonnegative integers and w a positive integer such that x*(y+3*z) is a cube or half a cube and y <= z <= w if x = 0.

Source: https://oeis.org/A301375
Credit: @keiichisince1986-bot

A301375 is the sequence `a(n)` named in the title. The entry states:
Conjecture: a(n) > 0 for all n > 0.

Conventions:
- A natural number `v` is a cube or half a cube when `v = c^3` or `2 v = c^3` for some natural
  number `c` (in particular `0` is a cube).
- `a(n) > 0` means that there is at least one such representation: natural numbers `x, y, z`
  and a positive integer `w` with `n = x^2 + y^2 + z^2 + w^2`, `x (y + 3 z)` a cube or half a cube,
  and `y ≤ z ≤ w` in case `x = 0`.
-/

namespace OMA.S_oeis_a301375

/-- `v` is a cube or half a cube. -/
def IsCubeOrHalfCube (v : ℕ) : Prop :=
  (∃ c : ℕ, v = c ^ 3) ∨ ∃ c : ℕ, 2 * v = c ^ 3

theorem main :
    ∀ n : ℕ, 0 < n → ∃ x y z w : ℕ, 0 < w ∧ n = x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 ∧
        IsCubeOrHalfCube (x * (y + 3 * z)) ∧ (x = 0 → y ≤ z ∧ z ≤ w) := by
  sorry

end OMA.S_oeis_a301375
