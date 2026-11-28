import Mathlib

/-!
# A241807: Numerators of c(n) = (n^2+n+2)/((n+1)*(n+2)*(n+3)) as defined in A241269

Source: https://oeis.org/A241807
Credit: @jagong-cmu

Formalizes the conjectured OEIS A241807 formula (offset 0):
`a(n) = A014206(n)/period 16: repeat 2, 4, 4, 2, 2, 16, 4, 2, 2, 4, 4, 2, 2, 8, 4, 2`.

Conventions:
* `c n` is the rational number `(n^2+n+2)/((n+1)*(n+2)*(n+3))`, and `a n` is its numerator
  in lowest terms (`Rat.num`). The denominator is positive, so the numerator is positive.
* `A014206 n = n^2 + n + 2` (OEIS A014206).
* `per n` is the 16-periodic sequence `2, 4, 4, 2, 2, 16, 4, 2, 2, 4, 4, 2, 2, 8, 4, 2`,
  read at the index `n % 16`, so `per 0 = 2`.
* The claim is stated for every `n >= 0` (the offset is 0). The division is taken in `ℚ`, so
  no truncated division occurs.
-/

namespace OMA.S_oeis_a241807

/-- `c(n) = (n^2+n+2)/((n+1)*(n+2)*(n+3))`, in `ℚ`. -/
def c (n : ℕ) : ℚ :=
  ((n : ℚ) ^ 2 + n + 2) / (((n : ℚ) + 1) * ((n : ℚ) + 2) * ((n : ℚ) + 3))

/-- A241807: the numerator of `c n` in lowest terms. -/
def a (n : ℕ) : ℤ := (c n).num

/-- A014206: `n^2 + n + 2`. -/
def A014206 (n : ℕ) : ℤ := (n : ℤ) ^ 2 + n + 2

/-- The period-16 sequence `2, 4, 4, 2, 2, 16, 4, 2, 2, 4, 4, 2, 2, 8, 4, 2`. -/
def per (n : ℕ) : ℤ := [2, 4, 4, 2, 2, 16, 4, 2, 2, 4, 4, 2, 2, 8, 4, 2].getD (n % 16) 0

/-- For every `n >= 0`: `a(n) = A014206(n) / per(n)`. -/
theorem main : ∀ n : ℕ, (a n : ℚ) = (A014206 n : ℚ) / (per n : ℚ) := by
  sorry

end OMA.S_oeis_a241807
