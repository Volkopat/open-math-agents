import Mathlib

/-!
# Plouffe's proposed ordinary generating function for Fibonacci Nim

Source: https://oeis.org/A001581 (OEIS Foundation, CC BY-SA 4.0).
Credit: @connoranderson

In the subtraction game a legal move removes a positive Fibonacci number. The sequence lists
the positive heap sizes with zero Grundy value. The empty heap also has zero Grundy value.
Simon Plouffe proposed the rational generating function in his 1992 dissertation. Boon Suan Ho
observed the first discrepancy at degree 27 in 2023.
-/

namespace OMA.S_oeis_a001581

/-- Generate the Fibonacci moves up to the heap size, starting at 1 and 2. -/
def fibMoves (bound : ℕ) : ℕ → ℕ → ℕ → List ℕ
  | 0, _, _ => []
  | fuel+1, a, b =>
    if a ≤ bound then a :: fibMoves bound fuel b (a+b) else []

/-- Zero-Grundy positions up to the specified heap size, in decreasing order. -/
def losingUpTo : ℕ → List ℕ
  | 0 => [0]
  | k+1 =>
    let earlier := losingUpTo k
    let legal := fibMoves (k+1) (k+1) 1 2
    if legal.any (fun d => earlier.contains (k+1-d)) then earlier else (k+1)::earlier

/-- Coefficient number zero is the first positive position, after the empty heap. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {m : ℕ | n+2 ≤ (losingUpTo m).length}

noncomputable def series : PowerSeries ℤ := PowerSeries.mk fun n => (a n : ℤ)

open PowerSeries

theorem main :
    series * ((X^6+X^5+X^4+X^3+X^2+X+1)*(X-1)^2) =
      2*(1+X)*(3*X^5+2*X^3+X^2+X+2) := by
  sorry

end OMA.S_oeis_a001581
