import Mathlib

/-!
# OEIS A026572: van Hoeij's generating function and Mathar's recurrence for T(n, n - 3) of the array A026568

Source: https://oeis.org/A026572 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A026572 (Clark Kimberling), offset 3: a(n) = T(n,n-3), T given by A026568. Also a(n) = number of integer strings s(0),...,s(n) counted by T, such that s(n)=3.
Formula section:
Conjectured g.f.: (1/2)*((-3*x^2-x+1)*((x-1)/(4*x^2+x-1))^(1/2)-1+x+x^2)/x^3.  - Mark van Hoeij, Oct 30 2011
Conjecture: (n+3)*a(n) +(-3*n-5)*a(n-1) +4*(-n-1)*a(n-2) +(13*n-9)*a(n-3) +(5*n-9)*a(n-4) +6*(-2*n+7)*a(n-5)=0. - R. J. Mathar, Jun 23 2013

A026568 (Clark Kimberling): Irregular triangular array T read by rows: T(i,0) = T(i,2i) = 1 for i >= 0; T(i,1) = T(i,2i-1) = [ (i+1)/2 ] for i >= 1; and for i >= 2 and 2 <=j <= i - 2, T(i,j) = T(i-1,j-2) + T(i-1,j-1) + T(i-1,j) if i + j is even, T(i,j) = T(i-1,j-2) + T(i-1,j) if i + j is odd.

Formalization notes:
* T(i, j) is defined for 0 <= j <= 2i by the rule of A026568 and is 0 outside the row. The name
  states the parity recursion for i >= 2 and 2 <= j <= i - 2; the definition applies it for 2 <= j
  <= 2i - 2, the range that the companion array A026584 states (j = 2..2i-2) and that the data
  needs: the name's boundary values fix only j <= 1 and j >= 2i - 1, and row 4 of the data is 1,
  2, 7, 7, 13, 7, 7, 2, 1. With this range the definition reproduces the array's data.
* a(n) = T(n, n - 3) for n >= 3, the entry's offset (natural subtraction below it). The title's
  second description, the number of strings s(0), ..., s(n) counted by A026568 with s(n) = 3, is
  the same number by the comment of A026568; the statement uses the first. The block gives no
  range for the recurrence, so it is stated for every n >= 8, the smallest n for which a(n - 5) is
  a term of the entry, as an identity of integers.
* The generating function is read as the formal power series sum_{n >= 3} a(n) x^n (the entry's
  offset is 3), so the statement multiplies the block's identity by x^3. The square root of
  (x-1)/(4*x^2+x-1) is the power series with constant term 1, the binomial series (1 + X)^(1/2)
  evaluated at the radicand minus 1.
* The definition reproduces the entry's data (1, 2, 8, 19, 56, 140, ... from n = 3); the proof
  file proves all 27 listed terms as controls.
-/

namespace OMA.S_oeis_a026572

open PowerSeries

/-- A026568 T(i, j), 0 <= j <= 2i: T(i, 0) = T(i, 2i) = 1, T(i, 1) = T(i, 2i - 1) = [(i+1)/2] for
i >= 1, and for 2 <= j <= 2i - 2, T(i, j) = T(i-1, j-2) + T(i-1, j-1) + T(i-1, j) if i + j is even
and T(i, j) = T(i-1, j-2) + T(i-1, j) if i + j is odd (0 beyond the row). -/
def T : ℕ → ℕ → ℕ
  | 0, j => if j = 0 then 1 else 0
  | i + 1, j =>
    if 2 * (i + 1) < j then 0
    else if j = 0 ∨ j = 2 * (i + 1) then 1
    else if j = 1 ∨ j = 2 * (i + 1) - 1 then (i + 2) / 2
    else if (i + 1 + j) % 2 = 0 then T i (j - 2) + T i (j - 1) + T i j
    else T i (j - 2) + T i j

/-- A026572: a(n) = T(n, n - 3). -/
def a (n : ℕ) : ℕ := T n (n - 3)

/-- The square root of (x-1)/(4*x^2+x-1) with constant term 1: the binomial series
(1 + X)^(1/2) evaluated at the radicand minus 1. -/
noncomputable def S : PowerSeries ℚ :=
  (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst ((X - 1) * (4 * X ^ 2 + X - 1 : PowerSeries ℚ)⁻¹ - 1)

/-- The block: van Hoeij's generating function, as the series sum_{n >= 3} a(n) x^n,
and Mathar's recurrence. -/
theorem main :
    X ^ 3 * mk (fun n => if 3 ≤ n then (a n : ℚ) else 0) =
        C (1 / 2 : ℚ) * ((-3 * X ^ 2 - X + 1) * S - 1 + X + X ^ 2) ∧
    ∀ n : ℕ, 8 ≤ n →
      ((n : ℤ) + 3) * (a n : ℤ) + (-3 * (n : ℤ) - 5) * (a (n - 1) : ℤ) + 4 * (-(n : ℤ) - 1) * (a (n - 2) : ℤ) + (13 * (n : ℤ) - 9) * (a (n - 3) : ℤ) + (5 * (n : ℤ) - 9) * (a (n - 4) : ℤ) + 6 * (-2 * (n : ℤ) + 7) * (a (n - 5) : ℤ) = 0 := by
  sorry

end OMA.S_oeis_a026572
