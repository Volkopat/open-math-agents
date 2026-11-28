import Mathlib

/-!
# OEIS A320666: Barker's conjectures for the most liberties of one Go group on an n X n board

Source: https://oeis.org/A320666 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jaredwilder.

Entry A320666 (Ton Hospel, Oct 28 2018), offset 1: a(n) is the maximum number of liberties a
single group can have on an otherwise empty n X n Go board.
Data: 0, 2, 6, 9, 14, 22, 29, 38, 51, 61, 74, 92, ...
Formula section (Barker's part):
Conjectures from Colin Barker, Jun 05 2019: (Start)
G.f.: x^2*(2 + 4*x + 3*x^2 + x^3 + x^5 + x^6 + x^7 - x^8) / ((1 - x)^3*(1 + x + x^2)^2).
a(n) = a(n-1) + 2*a(n-3) - 2*a(n-4) - a(n-6) + a(n-7) for n>9.
(End)

Formalization notes:
* The board is Fin n x Fin n; two points are adjacent when they differ by one in one coordinate
  and agree in the other. A group is a nonempty set of stones connected through adjacent stones
  of the set (the only stones on the board); its liberties are the empty points adjacent to one
  of its stones. a(n) is the largest number of liberties of a group (`sSup`; the numbers are
  bounded by n^2).
* For the 0 X 0 board there is no group and a 0 = sSup of the empty set = 0, the coefficient of
  x^0 of the g.f.; a(1) = 0 as in the entry. So the g.f. is stated for mk a over the integers as
  A * D = N (D has constant term 1).
* The statement is the conjunction of Barker's recurrence (for n > 9, in the integers) and g.f.
-/

namespace OMA.S_oeis_a320666

open PowerSeries

/-- Orthogonal adjacency on the n X n board. -/
def adj (n : ℕ) (p q : Fin n × Fin n) : Prop :=
  (p.1 = q.1 ∧ ((p.2 : ℕ) + 1 = q.2 ∨ (q.2 : ℕ) + 1 = p.2)) ∨
    (p.2 = q.2 ∧ ((p.1 : ℕ) + 1 = q.1 ∨ (q.1 : ℕ) + 1 = p.1))

/-- The stones of S are connected through adjacent stones of S. -/
def Conn (n : ℕ) (S : Finset (Fin n × Fin n)) : Prop :=
  ∀ p ∈ S, ∀ q ∈ S, Relation.ReflTransGen (fun x y => x ∈ S ∧ y ∈ S ∧ adj n x y) p q

/-- The liberties of S: the points outside S adjacent to a stone of S. -/
noncomputable def libs (n : ℕ) (S : Finset (Fin n × Fin n)) : ℕ :=
  {q : Fin n × Fin n | q ∉ S ∧ ∃ p ∈ S, adj n p q}.ncard

/-- A320666(n): the largest number of liberties of a single group on the n X n board. -/
noncomputable def a (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ S : Finset (Fin n × Fin n), S.Nonempty ∧ Conn n S ∧ libs n S = k}

/-- Barker's conjectures. -/
theorem main :
    (∀ n : ℕ, 9 < n → (a n : ℤ) = a (n - 1) + 2 * a (n - 3) - 2 * a (n - 4) - a (n - 6) + a (n - 7)) ∧
    mk (fun n => (a n : ℤ)) * ((1 - X) ^ 3 * (1 + X + X ^ 2) ^ 2) =
      (X ^ 2 * (2 + 4 * X + 3 * X ^ 2 + X ^ 3 + X ^ 5 + X ^ 6 + X ^ 7 - X ^ 8) : PowerSeries ℤ) := by
  sorry

end OMA.S_oeis_a320666
