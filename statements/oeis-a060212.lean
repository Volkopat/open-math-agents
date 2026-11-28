import Mathlib

/-!
# OEIS A060212: primes `q` with `6q ± 1` twin primes, growth

Source: https://oeis.org/A060212
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

A060212 lists the primes `q` such that `6q - 1` and `6q + 1` are both prime. Conjecture (OEIS
entry): `a(n) ~ n log(n) log(n log n) log(log n)`.

Conventions:
* `a(n) = Nat.nth P (n - 1)` (offset `1`); `~` is `Asymptotics.IsEquivalent` (which presupposes
  infinitely many terms).
-/

namespace OMA.S_oeis_a060212

open Filter Asymptotics

/-- `q` is prime and `6q ± 1` are prime. -/
def P (q : ℕ) : Prop := q.Prime ∧ (6 * q - 1).Prime ∧ (6 * q + 1).Prime

/-- The conjectured asymptotic. -/
theorem main : IsEquivalent atTop (fun n : ℕ => (Nat.nth P (n - 1) : ℝ))
    (fun n => n * Real.log n * Real.log (n * Real.log n) * Real.log (Real.log n)) := by
  sorry

end OMA.S_oeis_a060212
