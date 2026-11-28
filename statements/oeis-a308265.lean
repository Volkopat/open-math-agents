import Mathlib

/-!
# OEIS A308265: Barker's generating function and recurrence

Source: https://oeis.org/A308265 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Wesley Ivan Hurt, May 17 2019), offset 1: Sum of the largest parts in the partitions of n
into 3 parts. Data: 0, 0, 1, 2, 5, 9, 15, 22, 34, 45, 62, ... Formula lines: a(n) =
Sum_{k=1..floor(n/3)} Sum_{i=k..floor((n-k)/2)} (n-i-k). Conjectures from Colin Barker, Jul 16
2019: G.f.: x^3*(1 + 2*x + 3*x^2 + 3*x^3 + 2*x^4) / ((1 - x)^4*(1 + x)^2*(1 + x + x^2)^2).
a(n) = 2*a(n-2) + 2*a(n-3) - a(n-4) - 4*a(n-5) - a(n-6) + 2*a(n-7) + 2*a(n-8) - a(n-10) for n>10.

Formalization notes:
* A partition of n into 3 parts is a triple of positive integers a <= b <= c with a + b + c = n;
  its largest part is c. This is Hurt's double-sum formula in the entry (k = a, i = b), and it
  reproduces the data.
* The generating function is the formal power series sum_{n >= 0} a(n) x^n over the rationals
  (a(0) = 0, as 0 has no partition into 3 parts); the identity is A = num * den^(-1) in Q[[x]].
  The statement follows the one for the staged sibling A308159.
* The recurrence is stated over the integers, for every n > 10.
* Controls proved in the proof file: a(1..21) = 0, 0, 1, 2, 5, 9, 15, 22, 34, 45, 62, 81, 104,
  129, 163, 195, 237, 282, 333, 387, 454, the entry's data.
-/

namespace OMA.S_oeis_a308265

open Finset PowerSeries

/-- The partitions of n into 3 parts, as triples a <= b <= c of positive integers. -/
def tri (n : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((range (n + 1)) ×ˢ (range (n + 1)) ×ˢ (range (n + 1))).filter (fun t =>
    1 ≤ t.1 ∧ t.1 ≤ t.2.1 ∧ t.2.1 ≤ t.2.2 ∧ t.1 + t.2.1 + t.2.2 = n)

/-- A308265(n): the sum of the largest parts. -/
def a (n : ℕ) : ℕ := ∑ t ∈ tri n, t.2.2

/-- The generating function. -/
noncomputable def A : ℚ⟦X⟧ := PowerSeries.mk fun n => (a n : ℚ)

/-- Barker's numerator and denominator. -/
noncomputable def num : ℚ⟦X⟧ := X ^ 3 * (1 + 2 * X + 3 * X ^ 2 + 3 * X ^ 3 + 2 * X ^ 4)

noncomputable def den : ℚ⟦X⟧ := (1 - X) ^ 4 * (1 + X) ^ 2 * (1 + X + X ^ 2) ^ 2

/-- Barker's conjectures: the generating function and the recurrence for n > 10. -/
theorem main : A = num * den⁻¹ ∧
    ∀ n : ℕ, 10 < n →
      (a n : ℤ) = 2 * a (n - 2) + 2 * a (n - 3) - a (n - 4) - 4 * a (n - 5) - a (n - 6) +
        2 * a (n - 7) + 2 * a (n - 8) - a (n - 10) := by
  sorry

end OMA.S_oeis_a308265
