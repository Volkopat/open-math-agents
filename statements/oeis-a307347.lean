import Mathlib

/-!
# OEIS A307347: closed antelope paths of length `2n`

Source: https://oeis.org/A307347
Credit: @mbilenko03

An antelope is the leaper `[3, 4]`. The eight moves are the sign-and-order variants of `(3, 4)`.
`a n` counts walks of `2 * n` antelope moves on the integer lattice that start and end at the
origin. The claim is the asymptotic `a n ~ 64 ^ n / (25 * π * n)`.
-/

namespace OMA.S_oeis_a307347

/-- The eight antelope moves, the leaper `[3, 4]`. -/
def moves : Finset (ℤ × ℤ) :=
  {(3, 4), (3, -4), (-3, 4), (-3, -4), (4, 3), (4, -3), (-4, 3), (-4, -3)}

/-- Number of closed antelope walks of length `2 * n`. -/
def a (n : ℕ) : ℕ :=
  ((Fintype.piFinset fun _ : Fin (2 * n) => moves).filter (fun f => ∑ i, f i = 0)).card

theorem main :
    Filter.Tendsto
      (fun n : ℕ => (a n : ℝ) / ((64 : ℝ) ^ n / (25 * Real.pi * (n : ℝ))))
      Filter.atTop (nhds 1) := by
  sorry

end OMA.S_oeis_a307347
