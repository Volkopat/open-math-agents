import Mathlib

/-!
# OEIS A212837: Barker's g.f. and recurrence for 0..n arrays of length 4 with 0 never adjacent to n

Source: https://oeis.org/A212837 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A212837 (R. H. Hardin, May 28 2012), offset 1: Number of 0..n arrays of length 4 with 0 never adjacent to n.
Formula section:
Conjectures from Colin Barker, Jul 21 2018:
G.f.: x*(2 + 31*x - 7*x^2 - 3*x^3 + x^4) / (1 - x)^5.
a(n) = 5*a(n-1) - 10*a(n-2) + 10*a(n-3) - 5*a(n-4) + a(n-5) for n>5.

Formalization notes:
* An array is a function f : Fin 4 -> Fin (n + 1), the entries in positions 0..3; two positions
  are adjacent when they are consecutive, and 0 is adjacent to n when two consecutive positions hold
  0 and n in either order. For n >= 1 (the offset) the values 0 and n differ.
* The statement is the conjunction of Barker's two conjectures: the g.f. as the identity
  A(x) (1 - x)^5 = x(2 + 31x - 7x^2 - 3x^3 + x^4) in the formal power series ring over the rationals, with
  A(x) = Sum_{n >= 1} a(n) x^n (offset 1, so the constant term is 0), and the recurrence in the
  integers for every n > 5, where all of a(n - 1), ..., a(n - 5) are terms of the sequence.
* Controls proved in the proof file: the definition gives 2, 41, 178, 497, 1106, 2137, 3746, 6113, 9442, 13961
  for n = 1..10, the entry's data, and a(1), a(2) also by direct enumeration.
-/

namespace OMA.S_oeis_a212837

open PowerSeries Finset

/-- The values x and y of 0..n are 0 and n, in either order. -/
def zn (n : ℕ) (x y : Fin (n + 1)) : Prop := (x.val = 0 ∧ y.val = n) ∨ (x.val = n ∧ y.val = 0)

instance (n : ℕ) : DecidableRel (zn n) := fun x y => by unfold zn; infer_instance

/-- A212837(n): the number of arrays f of length 4 with entries 0..n in which 0 is never adjacent
to n: no two consecutive positions hold 0 and n, in either order. -/
def a (n : ℕ) : ℕ :=
  ((univ : Finset (Fin 4 → Fin (n + 1))).filter
    (fun f => ∀ i j : Fin 4, j.val = i.val + 1 → ¬ zn n (f i) (f j))).card

/-- Barker's conjectures: the g.f. and the recurrence for n > 5. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 5 =
      X * (2 + 31 * X - 7 * X ^ 2 - 3 * X ^ 3 + X ^ 4) ∧
    ∀ n : ℕ, 5 < n → (a n : ℤ) =
      5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) - 5 * a (n - 4) + a (n - 5) := by
  sorry

end OMA.S_oeis_a212837
