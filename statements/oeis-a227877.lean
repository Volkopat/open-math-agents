import Mathlib

/-!
# OEIS A227877: every n > 4 is x + y + z with x*y and x*z triangular and 6y - 1, 6z + 1 prime

Source: https://oeis.org/A227877 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Zhi-Wei Sun, Oct 25 2013), offset 1: Number of ways to write n = x + y + z (x, y, z > 0)
such that x*y and x*z are triangular numbers, and 6*y-1 and 6*z+1 are both prime.
Comment: Conjecture: a(n) > 0 for all n > 4.

Formalization notes:
* `a n` counts the triples `(x, y, z)` of positive integers with `x + y + z = n` such that
  `x * y` and `x * z` are triangular and `6 * y - 1` and `6 * z + 1` are prime. The three
  coordinates play different roles (the primality conditions differ for `y` and `z`), so the
  triples are ordered; this is the reading under which the entry's examples hold (a(77) = 1 with
  77 = 1 + 10 + 66, a(90) = 1 with 90 = 45 + 22 + 23).
* A natural number `t` is triangular when `t = k(k+1)/2` for some natural `k`; here `t` is a
  product of positive integers, so `t = 0` never arises.
* `6 * y - 1` is natural subtraction; with `y ≥ 1` it is the integer `6y - 1 ≥ 5`.
* The set of triples is finite (each coordinate is at most `n`), and `a n` is its cardinality.
* `main` states the conjecture as the entry words it: `a n > 0` for every `n > 4`.
-/

namespace OMA.S_oeis_a227877

/-- `t` is a triangular number: `t = k(k+1)/2` for some natural `k`. -/
def IsTriangular (t : ℕ) : Prop := ∃ k, t = k * (k + 1) / 2

/-- OEIS A227877: `a n` is the number of ways to write `n = x + y + z` with `x, y, z > 0` such that
`x * y` and `x * z` are triangular numbers and `6y - 1` and `6z + 1` are both prime. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ × ℕ | 0 < t.1 ∧ 0 < t.2.1 ∧ 0 < t.2.2 ∧ t.1 + t.2.1 + t.2.2 = n ∧
    IsTriangular (t.1 * t.2.1) ∧ IsTriangular (t.1 * t.2.2) ∧
    (6 * t.2.1 - 1).Prime ∧ (6 * t.2.2 + 1).Prime}

/-- Sun's conjecture: `a n > 0` for every `n > 4`. -/
theorem main : ∀ n : ℕ, 4 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a227877
