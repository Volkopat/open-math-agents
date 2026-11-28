import Mathlib

/-!
# OEIS A253974

Source: https://oeis.org/A253974
Credit: @mbilenko03

A giraffe is the fairy-chess leaper `(1, 4)`. More generally, for integers `0 < r < s`, an
`(r, s)`-leaper moves by any sign and axis swap of the vector `(r, s)`. The sequence counts
closed walks of length `2n` on the infinite integer board that start and end at the origin.

OEIS records the conjecture that, whenever `gcd(r, s) = 1`, this count is asymptotic to
`2^(6n+1) / ((r^2 + s^2) π n)` if `r + s` is even, and to
`2^(6n) / ((r^2 + s^2) π n)` if `r + s` is odd.
-/

namespace OMA.S_oeis_a253974

/-- The eight signed and swapped steps of an `(r, s)`-leaper. -/
def moves (r s : ℕ) : Finset (ℤ × ℤ) :=
  {((r : ℤ), (s : ℤ)), ((r : ℤ), -(s : ℤ)), (-(r : ℤ), (s : ℤ)), (-(r : ℤ), -(s : ℤ)),
    ((s : ℤ), (r : ℤ)), ((s : ℤ), -(r : ℤ)), (-(s : ℤ), (r : ℤ)), (-(s : ℤ), -(r : ℤ))}

/-- Number of `2n`-step closed `(r, s)`-leaper walks based at the origin. -/
def closedPaths (r s n : ℕ) : ℕ :=
  ((Fintype.piFinset fun _ : Fin (2 * n) => moves r s).filter
    (fun f => ∑ i, f i = 0)).card

/-- The OEIS A253974 asymptotic for coprime leapers `(r, s)`. -/
theorem main : ∀ r s : ℕ, 0 < r → r < s → Nat.Coprime r s →
    Filter.Tendsto (fun n : ℕ => (closedPaths r s n : ℝ) /
      ((if Even (r + s) then (2 : ℝ) ^ (6 * n + 1) else (2 : ℝ) ^ (6 * n)) /
        (((r : ℝ) ^ 2 + (s : ℝ) ^ 2) * Real.pi * (n : ℝ))))
      Filter.atTop (nhds 1) := by
  sorry

end OMA.S_oeis_a253974
