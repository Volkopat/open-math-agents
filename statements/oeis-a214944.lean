import Mathlib

/-!
# OEIS A214944: Barker's conjectures

Source: https://oeis.org/A214944 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A214944 (R. H. Hardin, Jul 30 2012), offset 1: Number of squarefree words of length 5 in an (n+1)-ary alphabet.
Formula section:
Empirical: a(n) = n^5 + n^4 - 2*n^3 - n^2 + n.
Conjectures from Colin Barker, Jul 22 2018: (Start)
G.f.: 6*x^2*(5 + 14*x + x^2) / (1 - x)^6.
a(n) = 6*a(n-1) - 15*a(n-2) + 20*a(n-3) - 15*a(n-4) + 6*a(n-5) - a(n-6) for n>6.
(End)

Formalization notes:
* A word of length 5 in an (n+1)-ary alphabet is a function w : Fin 5 → Fin (n + 1), read as
  the list List.ofFn w.
* Squarefree: no factor (contiguous subword, the relation <:+: of Mathlib) has the form u u
  with u nonempty.
* The statement is Barker's conjectures, the problem as stated on lefttosolve.com: the
  generating function and the recurrence.
* The definition gives a(0) = 0 (over one letter every word of length at least 2 has a
  square), so the generating function is A(x) = Sum_{n >= 0} a(n) x^n, and the identity is
  stated as A(x) (1 - x)^6 = N(x) in the formal power series ring over the integers.
* Controls proved in the proof file: the definition gives 0, 30, 264, 1140, 3480, 8610, 18480, 35784, 64080, 107910, 172920, 265980 for n = 1..12,
  the entry's first terms.
-/

namespace OMA.S_oeis_a214944

open Finset

/-- A word is squarefree when no factor (contiguous subword) has the form u u with u
nonempty. -/
def SquarefreeWord {α : Type*} (l : List α) : Prop := ∀ u : List α, u ++ u <:+: l → u = []

/-- A214944(n): the squarefree words of length 5 over the n + 1 letters of Fin (n + 1). -/
noncomputable def a (n : ℕ) : ℕ := Nat.card {w : Fin 5 → Fin (n + 1) // SquarefreeWord (List.ofFn w)}

/-- The problem as the site states it. -/
theorem main :
    PowerSeries.mk (fun n => (a n : ℤ)) * (1 - PowerSeries.X) ^ 6 = 6 * PowerSeries.X ^ 2 * (5 + 14 * PowerSeries.X + PowerSeries.X ^ 2) ∧
    (∀ n : ℕ, 6 < n → (a n : ℤ) = 6 * a (n - 1) - 15 * a (n - 2) + 20 * a (n - 3) - 15 * a (n - 4) + 6 * a (n - 5) - a (n - 6)) := by
  sorry

end OMA.S_oeis_a214944
