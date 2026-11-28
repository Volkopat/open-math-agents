import Mathlib

/-!
# OEIS A160108: a(n) = 2a(n-6) - a(n-12) for the Lodumo_8 transform of the Fibonacci numbers

Source: https://oeis.org/A160108 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Philippe Deléham, May 02 2009), offset 0: Lodumo_8 of Fibonacci numbers. Formula section:
Lodumo_8 transform of A000045 (for definition see Transforms). Conjecture: a(n) =
2*a(n-6)-a(n-12). - Colin Barker, Oct 04 2014.

Formalization notes:
* The Lodumo_m transform of a sequence s (Sloane's Transforms page) takes for a(n) the least
  nonnegative integer that is congruent to s(n) mod m and is none of a(0), ..., a(n-1). Here
  m = 8 and s(n) = F(n) is `Nat.fib n` (F(0) = 0, F(1) = 1), matching the offset 0.
* The least element is `sInf` of the set of admissible values; that set is never empty, and the
  proof file shows a(n) = (F(n) mod 8) + 8 * #{j < n : F(j) = F(n) mod 8}.
* `main` states the recurrence for every n >= 12, the range in which all three terms exist, in the
  integers.
* Controls from the entry (proved in the proof file through that closed form): a(0..14) = 0, 1, 9,
  2, 3, 5, 8, 13, 21, 10, 7, 17, 16, 25, 33.
-/

namespace OMA.S_oeis_a160108

/-- A160108: the Lodumo_8 transform of the Fibonacci numbers: a(n) is the least nonnegative
integer congruent to F(n) mod 8 that is none of a(0), ..., a(n-1). -/
noncomputable def a (n : ℕ) : ℕ := sInf {k | k % 8 = Nat.fib n % 8 ∧ ∀ j : Fin n, a j ≠ k}
decreasing_by exact j.isLt

/-- Barker's conjecture: a(n) = 2 a(n-6) - a(n-12). -/
theorem main : ∀ n : ℕ, 12 ≤ n → (a n : ℤ) = 2 * a (n - 6) - a (n - 12) := by
  sorry

end OMA.S_oeis_a160108
