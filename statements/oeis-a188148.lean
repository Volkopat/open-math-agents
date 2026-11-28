import Mathlib

/-!
# A188148: Number of 3-step self-avoiding walks on an n X n square summed over all starting positions.

Source: https://oeis.org/A188148
Credit: @Salofe

Conjectures from Colin Barker, Apr 26 2018, quoted verbatim from the entry:
* "G.f.: 4*x^2*(2 + 5*x - x^2) / (1 - x)^3."
* "a(n) = 3*a(n-1) - 3*a(n-2) + a(n-3) for n>4."

The entry adds: "The above conjectures are correct. See A188147."

Formalization notes:
* Offset 1, as in the entry (data: 0, 8, 44, 104, 188, 296, 428, ...). The value of `a 0`
  (the empty board) is never used.
* The n X n square is the board `Fin n × Fin n` of cells. Two cells are adjacent when they share
  an edge: one coordinate is equal and the other differs by 1 (`|Δi| + |Δj| = 1`).
* In R. H. Hardin's convention a k-step walk visits k cells (the examples label the cells 1..3,
  and row 1 of A188147 is n^2). So a 3-step self-avoiding walk is a sequence of 3 pairwise
  distinct cells, consecutive ones adjacent (two moves). This reproduces the data, e.g.
  a(2) = 8 and a(3) = 44, whereas walks making three moves on the 3 X 3 board number 80.
* "Summed over all starting positions": every such sequence is counted, whatever its first cell,
  so a walk and its reverse count separately.
* The g.f. is the ordinary one, Sum_{n>=1} a(n) x^n, stated as an identity of formal power
  series over `ℚ` with the denominator `(1 - x)^3` cleared (it has constant coefficient 1, so it
  is invertible). The coefficient of x^0 is 0 since the sequence starts at n = 1.
* The recurrence is stated in `ℤ` for every n > 4, as in the entry.
-/

namespace OMA.S_oeis_a188148

/-- Two cells of the `n × n` board are adjacent when they share an edge. -/
def Adj {n : ℕ} (p q : Fin n × Fin n) : Prop :=
  ((p.1 : ℤ) - q.1).natAbs + ((p.2 : ℤ) - q.2).natAbs = 1

/-- A 3-step self-avoiding walk: three distinct cells `w 0, w 1, w 2`, consecutive ones adjacent. -/
def IsWalk {n : ℕ} (w : Fin 3 → Fin n × Fin n) : Prop :=
  Function.Injective w ∧ Adj (w 0) (w 1) ∧ Adj (w 1) (w 2)

/-- A188148(n): the number of 3-step self-avoiding walks on the `n × n` board, summed over all
starting positions. -/
noncomputable def a (n : ℕ) : ℕ := by
  classical
  exact Fintype.card {w : Fin 3 → Fin n × Fin n // IsWalk w}

open PowerSeries in
/-- Barker's conjectures: the generating function `4x^2(2 + 5x - x^2)/(1 - x)^3`, and the
recurrence `a(n) = 3a(n-1) - 3a(n-2) + a(n-3)` for `n > 4`. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 3 =
        4 * X ^ 2 * (2 + 5 * X - X ^ 2) ∧
    ∀ n : ℕ, 4 < n → (a n : ℤ) = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3) := by
  sorry

end OMA.S_oeis_a188148
