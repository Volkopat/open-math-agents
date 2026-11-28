import Mathlib

/-!
# OEIS A050412: the Riesel problem

Source: https://oeis.org/A050412
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Start with `n` and repeatedly apply `x ↦ 2x + 1` until reaching a prime; `a(n)` is the number of
steps, or `0` if no prime is ever reached. Conjectures (OEIS entry): `509203` is the smallest
Riesel number, i.e. the least `n` with `n · 2^k - 1` composite for every `k > 0`; and if
`a(n) = 1` then `a(2n + 1) ≠ 0`.

Conventions:
* `n ≥ 1`. After `k` steps the value is `(n + 1) 2^k - 1`; `a(n)` is the least `k ≥ 1` with this
  prime, or `0` if there is none (`sInf ∅ = 0`).
* A Riesel number is an odd `n ≥ 1` with `n · 2^k - 1` not prime for all `k ≥ 1` (the standard
  definition). `main` states both conjectures.
-/

namespace OMA.S_oeis_a050412

/-- `a(n)`: least `k ≥ 1` with `(n+1) 2^k - 1` prime, else `0`. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {k : ℕ | 1 ≤ k ∧ ((n + 1) * 2 ^ k - 1).Prime}

/-- `n` is a Riesel number. -/
def IsRiesel (n : ℕ) : Prop := Odd n ∧ ∀ k : ℕ, 1 ≤ k → ¬ (n * 2 ^ k - 1).Prime

/-- `509203` is the least Riesel number, and `a(n) = 1 → a(2n+1) ≠ 0`. -/
theorem main :
    (IsRiesel 509203 ∧ ∀ n < 509203, ¬ IsRiesel n) ∧
    (∀ n : ℕ, 1 ≤ n → a n = 1 → a (2 * n + 1) ≠ 0) := by
  sorry

end OMA.S_oeis_a050412
