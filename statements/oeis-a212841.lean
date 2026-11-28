import Mathlib

/-!
# OEIS A212841: Barker's g.f. and recurrence for 0..n arrays of length 8 with 0 never adjacent to n

Source: https://oeis.org/A212841 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A212841 (R. H. Hardin, May 28 2012), offset 1: Number of 0..n arrays of length 8 with 0 never adjacent to n.
Formula section:
Conjectures from Colin Barker, Jul 21 2018:
G.f.: x*(2 + 1375*x + 16177*x^2 + 23723*x^3 - 551*x^4 - 563*x^5 + 179*x^6 - 23*x^7 + x^8) / (1 - x)^9.
a(n) = 9*a(n-1) - 36*a(n-2) + 84*a(n-3) - 126*a(n-4) + 126*a(n-5) - 84*a(n-6) + 36*a(n-7) - 9*a(n-8) + a(n-9) for n>9.

Formalization notes:
* An array is a function f : Fin 8 -> Fin (n + 1), the entries in positions 0..7; two positions
  are adjacent when they are consecutive, and 0 is adjacent to n when two consecutive positions hold
  0 and n in either order. For n >= 1 (the offset) the values 0 and n differ.
* The statement is the conjunction of Barker's two conjectures: the g.f. as the identity
  A(x) (1 - x)^9 = x(2 + 1375x + 16177x^2 + 23723x^3 - 551x^4 - 563x^5 + 179x^6 - 23x^7 + x^8) in the formal power series ring over the rationals, with
  A(x) = Sum_{n >= 1} a(n) x^n (offset 1, so the constant term is 0), and the recurrence in the
  integers for every n > 9, where all of a(n - 1), ..., a(n - 9) are terms of the sequence.
* Controls proved in the proof file: the definition gives 2, 1393, 28642, 231521, 1168786, 4414417, 13667858, 36590017, 87627106, 192124721
  for n = 1..10, the entry's data, and a(1) also by direct enumeration.
-/

namespace OMA.S_oeis_a212841

open PowerSeries Finset

/-- The values x and y of 0..n are 0 and n, in either order. -/
def zn (n : ℕ) (x y : Fin (n + 1)) : Prop := (x.val = 0 ∧ y.val = n) ∨ (x.val = n ∧ y.val = 0)

instance (n : ℕ) : DecidableRel (zn n) := fun x y => by unfold zn; infer_instance

/-- A212841(n): the number of arrays f of length 8 with entries 0..n in which 0 is never adjacent
to n: no two consecutive positions hold 0 and n, in either order. -/
def a (n : ℕ) : ℕ :=
  ((univ : Finset (Fin 8 → Fin (n + 1))).filter
    (fun f => ∀ i j : Fin 8, j.val = i.val + 1 → ¬ zn n (f i) (f j))).card

/-- Barker's conjectures: the g.f. and the recurrence for n > 9. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 9 =
      X * (2 + 1375 * X + 16177 * X ^ 2 + 23723 * X ^ 3 - 551 * X ^ 4 - 563 * X ^ 5 + 179 * X ^ 6 - 23 * X ^ 7 + X ^ 8) ∧
    ∀ n : ℕ, 9 < n → (a n : ℤ) =
      9 * a (n - 1) - 36 * a (n - 2) + 84 * a (n - 3) - 126 * a (n - 4) + 126 * a (n - 5) - 84 * a (n - 6) + 36 * a (n - 7) - 9 * a (n - 8) + a (n - 9) := by
  sorry

end OMA.S_oeis_a212841
