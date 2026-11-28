import Mathlib

/-!
# OEIS A212838: Barker's g.f. and recurrence for 0..n arrays of length 5 with 0 never adjacent to n

Source: https://oeis.org/A212838 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A212838 (R. H. Hardin, May 28 2012), offset 1: Number of 0..n arrays of length 5 with 0 never adjacent to n.
Formula section:
Conjectures from Colin Barker, Jul 21 2018:
G.f.: x*(2 + 87*x + 70*x^2 - 50*x^3 + 12*x^4 - x^5) / (1 - x)^6.
a(n) = 6*a(n-1) - 15*a(n-2) + 20*a(n-3) - 15*a(n-4) + 6*a(n-5) - a(n-6) for n>6.

Formalization notes:
* An array is a function f : Fin 5 -> Fin (n + 1), the entries in positions 0..4; two positions
  are adjacent when they are consecutive, and 0 is adjacent to n when two consecutive positions hold
  0 and n in either order. For n >= 1 (the offset) the values 0 and n differ.
* The statement is the conjunction of Barker's two conjectures: the g.f. as the identity
  A(x) (1 - x)^6 = x(2 + 87x + 70x^2 - 50x^3 + 12x^4 - x^5) in the formal power series ring over the rationals, with
  A(x) = Sum_{n >= 1} a(n) x^n (offset 1, so the constant term is 0), and the recurrence in the
  integers for every n > 6, where all of a(n - 1), ..., a(n - 6) are terms of the sequence.
* Controls proved in the proof file: the definition gives 2, 99, 634, 2309, 6306, 14407, 29114, 53769, 92674, 151211
  for n = 1..10, the entry's data, and a(1), a(2) also by direct enumeration.
-/

namespace OMA.S_oeis_a212838

open PowerSeries Finset

/-- The values x and y of 0..n are 0 and n, in either order. -/
def zn (n : ℕ) (x y : Fin (n + 1)) : Prop := (x.val = 0 ∧ y.val = n) ∨ (x.val = n ∧ y.val = 0)

instance (n : ℕ) : DecidableRel (zn n) := fun x y => by unfold zn; infer_instance

/-- A212838(n): the number of arrays f of length 5 with entries 0..n in which 0 is never adjacent
to n: no two consecutive positions hold 0 and n, in either order. -/
def a (n : ℕ) : ℕ :=
  ((univ : Finset (Fin 5 → Fin (n + 1))).filter
    (fun f => ∀ i j : Fin 5, j.val = i.val + 1 → ¬ zn n (f i) (f j))).card

/-- Barker's conjectures: the g.f. and the recurrence for n > 6. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 6 =
      X * (2 + 87 * X + 70 * X ^ 2 - 50 * X ^ 3 + 12 * X ^ 4 - X ^ 5) ∧
    ∀ n : ℕ, 6 < n → (a n : ℤ) =
      6 * a (n - 1) - 15 * a (n - 2) + 20 * a (n - 3) - 15 * a (n - 4) + 6 * a (n - 5) - a (n - 6) := by
  sorry

end OMA.S_oeis_a212838
