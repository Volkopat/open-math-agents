import Mathlib

/-!
# OEIS A175033: Greathouse's recurrence for the n with ceil(sqrt(n^2/2))^2 - n^2/2 = 17/2

Source: https://oeis.org/A175033 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A175033 (Ctibor O. Zizka, Nov 09 2009), offset 1: Numbers n such that
(ceiling(sqrt(n*n/2)))^2 - n*n/2 = 17/2. Data: 9, 15, 55, 89, 321, 519, 1871, 3025, 10905, ...
Comment: Conjecture: a(n) = 6*a(n-2) - a(n-4). - Charles R Greathouse IV, Apr 30 2016

Formalization notes:
* The condition is read in the reals, with sqrt the real square root and ceiling the integer
  ceiling: (ceil(sqrt(n*n/2)))^2 - n*n/2 = 17/2, for natural numbers n.
* a(n) is the n-th such number in increasing order, Nat.nth P (n - 1) for n >= 1 (offset 1).
* The recurrence is stated for n > 4, where a(n-4) is defined, in the integers.
* Controls from the entry, proved in the proof file: a(1..12) = 9, 15, 55, 89, 321, 519, 1871,
  3025, 10905, 17631, 63559, 102761.
-/

namespace OMA.S_oeis_a175033

/-- (ceiling(sqrt(n*n/2)))^2 - n*n/2 = 17/2. -/
def P (n : ℕ) : Prop :=
  ((⌈Real.sqrt ((n : ℝ) * n / 2)⌉ : ℤ) : ℝ) ^ 2 - (n : ℝ) * n / 2 = 17 / 2

/-- A175033(n), n >= 1: the n-th such number in increasing order. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth P (n - 1)

/-- Greathouse's conjecture a(n) = 6a(n-2) - a(n-4). -/
theorem main : ∀ n : ℕ, 4 < n → (a n : ℤ) = 6 * a (n - 2) - a (n - 4) := by
  sorry

end OMA.S_oeis_a175033
