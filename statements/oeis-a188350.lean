import Mathlib

/-!
# OEIS A188350: Smirnov's generating function and recurrence for the words of zero adjacent-product sum

Source: https://oeis.org/A188350 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A188350 (R. H. Hardin), offset 1: Number of arrangements of n+1 numbers x(i) in -1..1 with the sum of x(i)*x(i+1) equal to zero.
Formula section:
Conjectures from Mikhail Smirnov, Oct 15 2026: (Start)
G.f.: (2/sqrt((1-3*x)*(1+x-4*x^2)) - 2 + 3*x)/(1-x).
D-finite with recurrence n*a(n) - (3*n-1)*a(n-1) - (5*n-6)*a(n-2) + (19*n-25)*a(n-3) - 6*(2*n-3)*a(n-4) = 0 for n >= 5. (End)

Formalization notes:
* a(n) counts the functions x : Fin (n+1) → ℤ with every value x(i) in -1..1 (the Finset
  Fintype.piFinset of {-1, 0, 1}) and x(0) x(1) + x(1) x(2) + ... + x(n-1) x(n) = 0, for n >= 1,
  the entry's offset.
* The generating function is the formal power series sum_{n >= 1} a(n) x^n (the entry's offset is
  1). The block's 2/sqrt((1-3*x)*(1+x-4*x^2)) is 2 times the inverse of the power series square
  root of (1-3x)(1+x-4x^2) with constant term 1, the binomial series (1 + X)^(1/2) evaluated at the
  radicand minus 1; the division by 1 - x is multiplication by its inverse.
* The recurrence is stated for n >= 5, the block's range, as an identity of integers.
* The definition reproduces the entry's data (5, 15, 29, 91, 197, 627, ... from n = 1); the proof
  file proves all 26 listed terms as controls.
-/

namespace OMA.S_oeis_a188350

open PowerSeries

/-- A188350: the arrangements x(0), ..., x(n) of n + 1 numbers in -1..1 with
x(0) x(1) + x(1) x(2) + ... + x(n-1) x(n) = 0. -/
def a (n : ℕ) : ℕ :=
  ((Fintype.piFinset fun _ : Fin (n + 1) => ({-1, 0, 1} : Finset ℤ)).filter
    (fun x => ∑ i : Fin n, x i.castSucc * x i.succ = 0)).card

/-- The square root of (1-3x)(1+x-4x^2) with constant term 1: the binomial series (1 + X)^(1/2)
evaluated at the radicand minus 1. -/
noncomputable def S : PowerSeries ℚ :=
  (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst
    ((1 - 3 * X) * (1 + X - 4 * X ^ 2) - 1 : PowerSeries ℚ)

/-- Smirnov's conjectures: the generating function, as the series sum_{n >= 1} a(n) x^n, and the
recurrence for n >= 5. -/
theorem main :
    mk (fun n => if 1 ≤ n then (a n : ℚ) else 0) =
        (2 * S⁻¹ - 2 + 3 * X) * (1 - X : PowerSeries ℚ)⁻¹ ∧
    ∀ n : ℕ, 5 ≤ n →
      (n : ℤ) * (a n : ℤ) - (3 * (n : ℤ) - 1) * (a (n - 1) : ℤ) - (5 * (n : ℤ) - 6) * (a (n - 2) : ℤ) +
        (19 * (n : ℤ) - 25) * (a (n - 3) : ℤ) - 6 * (2 * (n : ℤ) - 3) * (a (n - 4) : ℤ) = 0 := by
  sorry

end OMA.S_oeis_a188350
