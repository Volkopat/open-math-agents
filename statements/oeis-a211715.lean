import Mathlib

/-!
# A211715: Number of (n+1) X (n+1) -11..11 symmetric matrices with every 2 X 2 subblock having sum zero and two or four distinct values.

Source: https://oeis.org/A211715
Credit: @agchua

Colin Barker (Jul 19 2018), in the formula section of A211715:
  Conjectures from Colin Barker, Jul 19 2018: (Start)
  G.f.: 2*x*(17 - 22*x) / ((1 - x)*(1 - 2*x)).
  a(n) = 10 + 3*2^(2+n).
  (End)
The sequence has offset 1 (a(1) = 34 counts 2 X 2 matrices). A matrix is a function
M : Fin (n+1) → Fin (n+1) → ℤ with all entries in -11..11; it is symmetric when M i j = M j i;
its 2 X 2 subblocks are the blocks of consecutive rows i, i+1 and consecutive columns j, j+1
(i, j < n), written with Fin.castSucc and Fin.succ below, and every subblock must have sum zero
and its four entries must take exactly two or exactly four distinct values. The closed form is
stated for n ≥ 1, as the offset is 1. The g.f. is stated as an identity of formal power series
over ℚ for the series of the terms, the sum of a(n) x^n over n ≥ 1 (constant coefficient 0):
(sum of a(n) x^n) * ((1 - x)(1 - 2x)) = 2x(17 - 22x).
-/

namespace OMA.S_oeis_a211715

/-- A211715(n): the number of symmetric (n+1) X (n+1) matrices with entries in -11..11 whose
2 X 2 subblocks of consecutive rows and columns all have sum zero and two or four distinct
values. (It is marked noncomputable only because Lean's code generator meets a noncomputable
order instance on ℤ; the set is finite and explicit.) -/
noncomputable def a (n : ℕ) : ℕ :=
  ((Fintype.piFinset fun _ : Fin (n + 1) =>
      Fintype.piFinset fun _ : Fin (n + 1) => Finset.Icc (-11 : ℤ) 11).filter
    (fun M => (∀ i j, M i j = M j i) ∧
      ∀ i j : Fin n, M i.castSucc j.castSucc + M i.succ j.castSucc + M i.castSucc j.succ +
        M i.succ j.succ = 0 ∧
        ({M i.castSucc j.castSucc, M i.succ j.castSucc, M i.castSucc j.succ, M i.succ j.succ} :
          Finset ℤ).card ∈ ({2, 4} : Finset ℕ))).card

/-- Barker's conjectures: the closed form and the g.f. -/
theorem main : (∀ n : ℕ, 1 ≤ n → a n = 10 + 3 * 2 ^ (2 + n)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
        ((1 - PowerSeries.X) * (1 - 2 * PowerSeries.X)) =
      2 * PowerSeries.X * (17 - 22 * PowerSeries.X) := by
  sorry

end OMA.S_oeis_a211715
