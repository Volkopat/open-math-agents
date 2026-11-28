import Mathlib

/-!
# OEIS A126241: Terras's coefficient stopping time conjecture

Source: https://oeis.org/A126241
With `T(n) = n/2` for even `n` and `(3n+1)/2` for odd `n`, the dropping (stopping) time of `n`
is the least `d ≥ 1` with `T^d(n) < n`. Terras's coefficient stopping time `τ(n)` is the least
`d` with `3^u / 2^d < 1`, where `u` is the number of odd steps among the first `d` steps from
`n`. Clearly `τ(n) ≤` the dropping time; Terras conjectured (Conjecture 2.9) that they are
equal for `n ≥ 2`.

Conventions. Both are stated as "least such `d`" predicates; the conjecture says that for
every `n ≥ 2` and `d`, `d` is the dropping time of `n` iff it is the coefficient stopping time
(in particular `n` has a finite dropping time iff it has a finite coefficient stopping time).

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a126241

/-- The Terras map. -/
def T (n : ℕ) : ℕ := if n % 2 = 0 then n / 2 else (3 * n + 1) / 2

/-- Number of odd iterates among `n, T n, …, T^(d-1) n`. -/
def oddSteps (n d : ℕ) : ℕ := ((Finset.range d).filter fun j => T^[j] n % 2 = 1).card

/-- `d` is the dropping time of `n`. -/
def IsDropTime (n d : ℕ) : Prop := 1 ≤ d ∧ T^[d] n < n ∧ ∀ e, 1 ≤ e → e < d → n ≤ T^[e] n

/-- `d` is the coefficient stopping time of `n`. -/
def IsCoefTime (n d : ℕ) : Prop :=
  3 ^ oddSteps n d < 2 ^ d ∧ ∀ e < d, 2 ^ e ≤ 3 ^ oddSteps n e

theorem main : ∀ n : ℕ, 2 ≤ n → ∀ d : ℕ, IsDropTime n d ↔ IsCoefTime n d := by
  sorry

end OMA.S_oeis_a126241
