import Mathlib

/-!
# OEIS A214945: Barker's conjectures

Source: https://oeis.org/A214945 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A214945 (R. H. Hardin, Jul 30 2012), offset 1: Number of squarefree words of length 6 in an (n+1)-ary alphabet.
Formula section:
Empirical: a(n) = n^6 + n^5 - 3*n^4 - 2*n^3 + 2*n^2 + n.
Conjectures from Colin Barker, Jul 22 2018: (Start)
G.f.: 6*x^2*(7 + 67*x + 45*x^2 + x^3) / (1 - x)^7.
a(n) = 7*a(n-1) - 21*a(n-2) + 35*a(n-3) - 35*a(n-4) + 21*a(n-5) - 7*a(n-6) + a(n-7) for n>7.
(End)

Formalization notes:
* A word of length 6 in an (n+1)-ary alphabet is a function w : Fin 6 → Fin (n + 1), read as
  the list List.ofFn w.
* Squarefree: no factor (contiguous subword, the relation <:+: of Mathlib) has the form u u
  with u nonempty.
* The statement is Barker's conjectures, the problem as stated on lefttosolve.com: the
  generating function and the recurrence.
* The definition gives a(0) = 0 (over one letter every word of length at least 2 has a
  square), so the generating function is A(x) = Sum_{n >= 0} a(n) x^n, and the identity is
  stated as A(x) (1 - x)^7 = N(x) in the formal power series ring over the integers.
* Controls proved in the proof file: the definition gives 0, 42, 696, 4260, 16680, 50190, 126672, 281736, 569520, 1068210, 1886280, 3169452 for n = 1..12,
  the entry's first terms.
-/

namespace OMA.S_oeis_a214945

open Finset

/-- A word is squarefree when no factor (contiguous subword) has the form u u with u
nonempty. -/
def SquarefreeWord {α : Type*} (l : List α) : Prop := ∀ u : List α, u ++ u <:+: l → u = []

/-- A214945(n): the squarefree words of length 6 over the n + 1 letters of Fin (n + 1). -/
noncomputable def a (n : ℕ) : ℕ := Nat.card {w : Fin 6 → Fin (n + 1) // SquarefreeWord (List.ofFn w)}

/-- The problem as the site states it. -/
theorem main :
    PowerSeries.mk (fun n => (a n : ℤ)) * (1 - PowerSeries.X) ^ 7 = 6 * PowerSeries.X ^ 2 * (7 + 67 * PowerSeries.X + 45 * PowerSeries.X ^ 2 + PowerSeries.X ^ 3) ∧
    (∀ n : ℕ, 7 < n → (a n : ℤ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4) + 21 * a (n - 5) - 7 * a (n - 6) + a (n - 7)) := by
  sorry

end OMA.S_oeis_a214945
