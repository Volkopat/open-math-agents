import Mathlib

/-!
# OEIS A212839: Barker's g.f. and recurrence for 0..n arrays of length 6 with 0 never adjacent to n

Source: https://oeis.org/A212839 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A212839 (R. H. Hardin, May 28 2012), offset 1: Number of 0..n arrays of length 6 with 0 never adjacent to n.
Formula section:
Conjectures from Colin Barker, Jul 21 2018:
G.f.: x*(2 + 225*x + 627*x^2 - 130*x^3 - 12*x^4 + 9*x^5 - x^6) / (1 - x)^7.
a(n) = 7*a(n-1) - 21*a(n-2) + 35*a(n-3) - 35*a(n-4) + 21*a(n-5) - 7*a(n-6) + a(n-7) for n>7.

Formalization notes:
* An array is a function f : Fin 6 -> Fin (n + 1), the entries in positions 0..5; two positions
  are adjacent when they are consecutive, and 0 is adjacent to n when two consecutive positions hold
  0 and n in either order. For n >= 1 (the offset) the values 0 and n differ.
* The statement is the conjunction of Barker's two conjectures: the g.f. as the identity
  A(x) (1 - x)^7 = x(2 + 225x + 627x^2 - 130x^3 - 12x^4 + 9x^5 - x^6) in the formal power series ring over the rationals, with
  A(x) = Sum_{n >= 1} a(n) x^n (offset 1, so the constant term is 0), and the recurrence in the
  integers for every n > 7, where all of a(n - 1), ..., a(n - 7) are terms of the sequence.
* Controls proved in the proof file: the definition gives 2, 239, 2258, 10727, 35954, 97127, 226274, 472943, 909602, 1637759
  for n = 1..10, the entry's data, and a(1), a(2) also by direct enumeration.
-/

namespace OMA.S_oeis_a212839

open PowerSeries Finset

/-- The values x and y of 0..n are 0 and n, in either order. -/
def zn (n : ℕ) (x y : Fin (n + 1)) : Prop := (x.val = 0 ∧ y.val = n) ∨ (x.val = n ∧ y.val = 0)

instance (n : ℕ) : DecidableRel (zn n) := fun x y => by unfold zn; infer_instance

/-- A212839(n): the number of arrays f of length 6 with entries 0..n in which 0 is never adjacent
to n: no two consecutive positions hold 0 and n, in either order. -/
def a (n : ℕ) : ℕ :=
  ((univ : Finset (Fin 6 → Fin (n + 1))).filter
    (fun f => ∀ i j : Fin 6, j.val = i.val + 1 → ¬ zn n (f i) (f j))).card

/-- Barker's conjectures: the g.f. and the recurrence for n > 7. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 7 =
      X * (2 + 225 * X + 627 * X ^ 2 - 130 * X ^ 3 - 12 * X ^ 4 + 9 * X ^ 5 - X ^ 6) ∧
    ∀ n : ℕ, 7 < n → (a n : ℤ) =
      7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4) + 21 * a (n - 5) - 7 * a (n - 6) + a (n - 7) := by
  sorry

end OMA.S_oeis_a212839
