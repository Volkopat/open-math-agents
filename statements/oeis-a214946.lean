import Mathlib

/-!
# OEIS A214946: Barker's conjectures

Source: https://oeis.org/A214946 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A214946 (R. H. Hardin, Jul 30 2012), offset 1: Number of squarefree words of length 7 in an (n+1)-ary alphabet.
Formula section:
Empirical: a(n) = n^7 + n^6 - 4*n^5 - 3*n^4 + 5*n^3 + 2*n^2 - 2*n.
Conjectures from Colin Barker, Jul 22 2018: (Start)
G.f.: 12*x^2*(5 + 114*x + 238*x^2 + 62*x^3 + x^4) / (1 - x)^8.
a(n) = 8*a(n-1) - 28*a(n-2) + 56*a(n-3) - 70*a(n-4) + 56*a(n-5) - 28*a(n-6) + 8*a(n-7) - a(n-8) for n>8.
(End)

Formalization notes:
* A word of length 7 in an (n+1)-ary alphabet is a function w : Fin 7 → Fin (n + 1), read as
  the list List.ofFn w.
* Squarefree: no factor (contiguous subword, the relation <:+: of Mathlib) has the form u u
  with u nonempty.
* The statement is Barker's conjectures, the problem as stated on lefttosolve.com: the
  generating function and the recurrence.
* The definition gives a(0) = 0 (over one letter every word of length at least 2 has a
  square), so the generating function is A(x) = Sum_{n >= 0} a(n) x^n, and the identity is
  stated as A(x) (1 - x)^8 = N(x) in the formal power series ring over the integers.
* Controls proved in the proof file: the definition gives 0, 60, 1848, 15960, 80040, 292740, 868560, 2218608, 5062320, 10575180, 20577480, 37769160 for n = 1..12,
  the entry's first terms.
-/

namespace OMA.S_oeis_a214946

open Finset

/-- A word is squarefree when no factor (contiguous subword) has the form u u with u
nonempty. -/
def SquarefreeWord {α : Type*} (l : List α) : Prop := ∀ u : List α, u ++ u <:+: l → u = []

/-- A214946(n): the squarefree words of length 7 over the n + 1 letters of Fin (n + 1). -/
noncomputable def a (n : ℕ) : ℕ := Nat.card {w : Fin 7 → Fin (n + 1) // SquarefreeWord (List.ofFn w)}

/-- The problem as the site states it. -/
theorem main :
    PowerSeries.mk (fun n => (a n : ℤ)) * (1 - PowerSeries.X) ^ 8 = 12 * PowerSeries.X ^ 2 * (5 + 114 * PowerSeries.X + 238 * PowerSeries.X ^ 2 + 62 * PowerSeries.X ^ 3 + PowerSeries.X ^ 4) ∧
    (∀ n : ℕ, 8 < n → (a n : ℤ) = 8 * a (n - 1) - 28 * a (n - 2) + 56 * a (n - 3) - 70 * a (n - 4) + 56 * a (n - 5) - 28 * a (n - 6) + 8 * a (n - 7) - a (n - 8)) := by
  sorry

end OMA.S_oeis_a214946
