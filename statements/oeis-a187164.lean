import Mathlib

/-!
# A187164: Number of 3-step self-avoiding walks on an n X n X n cube summed over all starting positions.

Source: https://oeis.org/A187164
Credit: @Salofe

Conjectures from Colin Barker, Apr 20 2018, quoted verbatim from the entry:
* "G.f.: 6*x^2*(8 + 25*x - 4*x^2 + x^3) / (1 - x)^4."
* "a(n) = 4*a(n-1) - 6*a(n-2) + 4*a(n-3) - a(n-4) for n>5."

The entry also lists "Empirical: a(n) = 30*n^3 - 60*n^2 + 24*n for n>1." (row 3 of A187162);
that closed form is not part of this statement, which states Barker's two conjectures only.

Formalization notes:
* Offset 1, as in the entry (data: 0, 48, 342, 1056, 2370, 4464, 7518, ...). The value of `a 0`
  (the empty cube) is never used.
* The n X n X n cube is the set `Fin n × Fin n × Fin n` of cells. Two cells are adjacent when
  they share a face: two coordinates are equal and the third differs by 1
  (`|Δi| + |Δj| + |Δk| = 1`).
* In R. H. Hardin's convention a k-step walk visits k cells (row 1 of A187162 is n^3, and the
  example labels the cells 1..3). So a 3-step self-avoiding walk is a sequence of 3 pairwise
  distinct cells, consecutive ones adjacent (two moves). This reproduces the data, e.g.
  a(2) = 48 = 8 * 3 * 2 and a(3) = 342.
* "Summed over all starting positions": every such sequence is counted, whatever its first cell,
  so a walk and its reverse count separately.
* The g.f. is the ordinary one, Sum_{n>=1} a(n) x^n, stated as an identity of formal power
  series over `ℚ` with the denominator `(1 - x)^4` cleared (it has constant coefficient 1, so it
  is invertible). The coefficient of x^0 is 0 since the sequence starts at n = 1.
* The recurrence is stated in `ℤ` for every n > 5, as in the entry.
-/

namespace OMA.S_oeis_a187164

/-- Two cells of the `n × n × n` cube are adjacent when they share a face. -/
def Adj {n : ℕ} (p q : Fin n × Fin n × Fin n) : Prop :=
  ((p.1 : ℤ) - q.1).natAbs + ((p.2.1 : ℤ) - q.2.1).natAbs + ((p.2.2 : ℤ) - q.2.2).natAbs = 1

/-- A 3-step self-avoiding walk: three distinct cells `w 0, w 1, w 2`, consecutive ones adjacent. -/
def IsWalk {n : ℕ} (w : Fin 3 → Fin n × Fin n × Fin n) : Prop :=
  Function.Injective w ∧ Adj (w 0) (w 1) ∧ Adj (w 1) (w 2)

/-- A187164(n): the number of 3-step self-avoiding walks on the `n × n × n` cube, summed over all
starting positions. -/
noncomputable def a (n : ℕ) : ℕ := by
  classical
  exact Fintype.card {w : Fin 3 → Fin n × Fin n × Fin n // IsWalk w}

open PowerSeries in
/-- Barker's conjectures: the generating function `6x^2(8 + 25x - 4x^2 + x^3)/(1 - x)^4`, and the
recurrence `a(n) = 4a(n-1) - 6a(n-2) + 4a(n-3) - a(n-4)` for `n > 5`. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 4 =
        6 * X ^ 2 * (8 + 25 * X - 4 * X ^ 2 + X ^ 3) ∧
    ∀ n : ℕ, 5 < n →
      (a n : ℤ) = 4 * a (n - 1) - 6 * a (n - 2) + 4 * a (n - 3) - a (n - 4) := by
  sorry

end OMA.S_oeis_a187164
