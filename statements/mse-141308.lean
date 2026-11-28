import Mathlib

/-!
# A Lucas–Lehmer type primality test for `3 · 2ⁿ + 1`

Source: https://math.stackexchange.com/questions/141308
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Let `N = 3 · 2ⁿ + 1` with `n ≡ 2, 6, 8, 10 (mod 12)` or `n ≡ 1 (mod 4)`. Let the seed `S` be
`50542` if `n ≡ 8 (mod 12)`, `32672` if `n ≡ 1 (mod 4)`, `1692` if `n ≡ 2 (mod 12)`, and `21868` if
`n ≡ 6, 10 (mod 12)`; put `S₀ = S`, `Sᵢ = S_{i-1}² - 2`. Conjecture (asker): for `n > 2`, `N` is
prime iff `S_{n-2} ≡ 0 (mod N)`.

Conventions:
* The residue classes `n ≡ 1 (mod 4)` and `n ≡ 2, 6, 8, 10 (mod 12)` are disjoint, so the seed is
  well defined. The recurrence is computed in `ZMod N`.
-/

namespace OMA.S_mse_141308

/-- The seed. -/
def seed (n : ℕ) : ℕ :=
  if n % 12 = 8 then 50542 else if n % 4 = 1 then 32672 else if n % 12 = 2 then 1692 else 21868

/-- `Sᵢ` modulo `N`. -/
def S (N : ℕ) (s : ℕ) : ℕ → ZMod N
  | 0 => s
  | i + 1 => S N s i ^ 2 - 2

/-- The conjectured primality criterion. -/
theorem main : ∀ n : ℕ, 2 < n →
    (n % 12 = 2 ∨ n % 12 = 6 ∨ n % 12 = 8 ∨ n % 12 = 10 ∨ n % 4 = 1) →
    ((3 * 2 ^ n + 1).Prime ↔ S (3 * 2 ^ n + 1) (seed n) (n - 2) = 0) := by
  sorry

end OMA.S_mse_141308
