import Mathlib

/-!
# OEIS A173644: the recurrence a(n) = 2*a(n-7) - a(n-14) for the least m with n^2 + 7m square

Source: https://oeis.org/A173644 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Zak Seidov, Dec 05 2010), offset 1: a(n) = smallest positive integer m such that n^2+7m is a
square. The formula section states: Conjecture: a(n)= +2*a(n-7) -a(n-14).

Formalization notes:
* a(n) is the least m > 0 such that n^2 + 7m is a perfect square (`IsSquare`); such an m exists,
  for example m = 2n + 7, since n^2 + 7(2n + 7) = (n + 7)^2.
* The recurrence has no stated range; it is taken for n >= 15, the indices for which a(n-14) is a
  term (offset 1). The identity is stated in the integers.
* Controls (checked in a scratch copy of the proof file, from its closed form 7a(n) =
  d(n)(2n + d(n))): the definition gives a(1..7) = 5, 3, 1, 12, 8, 4, 21, as in the entry.
-/

namespace OMA.S_oeis_a173644

/-- A173644(n): the least `m > 0` with `n^2 + 7m` a square. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.find (⟨2 * n + 7, by omega, ⟨n + 7, by ring⟩⟩ : ∃ m, 0 < m ∧ IsSquare (n ^ 2 + 7 * m))

/-- Seidov's conjecture: a(n) = 2*a(n-7) - a(n-14) for every n >= 15. -/
theorem main : ∀ n : ℕ, 15 ≤ n → (a n : ℤ) = 2 * a (n - 7) - a (n - 14) := by
  sorry

end OMA.S_oeis_a173644
