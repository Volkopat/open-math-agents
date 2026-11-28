import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Odd coefficients of A397345

Let D=X d/dX, A=1+U and L=D log A. The published exponential
definition gives DA=A L, L₁=1 and 5n Lₙ=(5n²−1)aₙ for n≥2.
If sₙ=[Xⁿ](U L), these equations say aₙ=[n=1]+5n sₙ for n>0
and Lₙ=n aₙ−sₙ. Both U and L have zero constant term, so sₙ uses
only indices below n. This is an integer form of the entry's
coefficient recurrence (formula 6), without rational division.

Source: https://oeis.org/A397345 (OEIS Foundation, CC BY-SA 4.0).
Credit: @Solitude1312
-/

namespace OMA.S_oeis_a397345

open PowerSeries

/-- At index n the pair consists of the coefficients of A−1 and D log A. -/
noncomputable def terms (n : ℕ) : ℤ × ℤ :=
  if n = 0 then (0, 0) else
    let U : PowerSeries ℤ := PowerSeries.mk fun k => if _h : k < n then (terms k).1 else 0
    let L : PowerSeries ℤ := PowerSeries.mk fun k => if _h : k < n then (terms k).2 else 0
    let s := (U * L).coeff n
    let u := (if n = 1 then 1 else 0) + 5 * (n : ℤ) * s
    (u, (n : ℤ) * u - s)
termination_by n

noncomputable def series : PowerSeries ℤ := 1 + PowerSeries.mk fun n => (terms n).1

theorem main : ∀ n : ℕ, Odd (series.coeff n) ↔ ∃ k : ℕ, n + 1 = 2 ^ k := by
  sorry

end OMA.S_oeis_a397345
