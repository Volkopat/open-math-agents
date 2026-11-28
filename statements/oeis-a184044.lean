import Mathlib

/-!
# OEIS A184044: Barker's g.f. and closed forms for (n+1) X 6 arrays with equal 2 X 2 subblocks

Source: https://oeis.org/A184044 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A184044 (R. H. Hardin, Jan 08 2011), offset 1: 1/9 the number of (n+1) X 6 0..2 arrays with
all 2 X 2 subblocks having the same four values.
Formula section:
Empirical: a(n) = 3*a(n-1) - 6*a(n-3) + 4*a(n-4).
Conjectures from Colin Barker, Apr 10 2018: (Start)
G.f.: x*(81 - 156*x - 164*x^2 + 312*x^3) / ((1 - x)*(1 - 2*x)*(1 - 2*x^2)).
a(n) = 3*2^(n/2) + 2^(n+1) + 73 for n even.
a(n) = 2^(n+1) + 2^((n+3)/2) + 73 for n odd. (End)
Conjectured e.g.f.: 2*cosh(2*x) + 3*cosh(sqrt(2)*x) + 73*sinh(x) + cosh(x)*(73 + 4*sinh(x)) + 2*sqrt(2)*sinh(sqrt(2)*x) - 78. - Stefano Spezia, Aug 01 2025

Formalization notes:
* An array is a function f : Fin (n + 1) -> Fin 6 -> Fin 3, f i j the entry in row i and column j,
  so the arrays are (n+1) X 6 with entries 0..2. Its 2 X 2 subblocks are those with upper left
  corner (i, j), i < n, j < 5; `blk f i j` is the multiset of their four values.
* Having the same four values is read as carrying the same multiset of four values (values with
  their multiplicities); every two subblocks are compared. The entry's data agree with this reading,
  and the proof file proves the first twelve terms.
* a(n) is the count divided by 9 in the natural numbers; the proof shows the count is 9 times the
  closed form, so the division is exact.
* The g.f. is the identity A(x) (1 - x)(1 - 2x)(1 - 2x^2) = x(81 - 156x - 164x^2 + 312x^3) in the
  formal power series ring over the rationals, with A(x) = Sum_{n >= 1} a(n) x^n (offset 1, so the
  constant term is 0).
* The closed forms are identities of natural numbers: for n even means every even n >= 2 (the offset
  is 1) and for n odd every odd n >= 1; all exponents are exact for these n.
* Spezia's conjectured e.g.f. is stated as: for every n >= 1, a(n) is n! times the coefficient of
  x^n in the power series egf over the reals, where cosh(c x) and sinh(c x) are written as their
  power series `coshS c` and `sinhS c` (coefficients c^n / n! on even, respectively odd, n) and the
  constants 2, 3, 73, 4, 78 and 2 sqrt(2) are constant series; the constant term of egf is 0,
  matching the offset 1. The statement is the conjunction of Barker's three conjectures and the
  e.g.f.
* Controls proved in the proof file: the definition gives 81, 87, 97, 117, 153, 225, 361, 633, 1161,
  2217, 4297, 8457 for n = 1..12, the entry's data.
-/

namespace OMA.S_oeis_a184044

open PowerSeries Finset

/-- The multiset of the four values of the 2 X 2 subblock with upper left corner (i, j). -/
def blk {n : ℕ} (f : Fin (n + 1) → Fin 6 → Fin 3) (i : Fin n) (j : Fin 5) : Multiset (Fin 3) :=
  {f i.castSucc j.castSucc, f i.castSucc j.succ, f i.succ j.castSucc, f i.succ j.succ}

/-- A184044: 1/9 the number of (n+1) X 6 arrays of 0..2 (row i, column j) with all 2 X 2
subblocks having the same four values. -/
def a (n : ℕ) : ℕ :=
  ((univ : Finset (Fin (n + 1) → Fin 6 → Fin 3)).filter
    (fun f => ∀ i i' : Fin n, ∀ j j' : Fin 5, blk f i j = blk f i' j')).card / 9

/-- cosh(c x) as a power series over the reals: x^n has coefficient c^n / n! for even n, 0 for odd
n. -/
noncomputable def coshS (c : ℝ) : PowerSeries ℝ :=
  PowerSeries.mk (fun n => if n % 2 = 0 then c ^ n / (n.factorial : ℝ) else 0)

/-- sinh(c x) as a power series over the reals: x^n has coefficient c^n / n! for odd n, 0 for even
n. -/
noncomputable def sinhS (c : ℝ) : PowerSeries ℝ :=
  PowerSeries.mk (fun n => if n % 2 = 1 then c ^ n / (n.factorial : ℝ) else 0)

/-- Spezia's conjectured e.g.f. 2 cosh(2x) + 3 cosh(sqrt(2) x) + 73 sinh(x) + cosh(x) (73 + 4 sinh(x))
+ 2 sqrt(2) sinh(sqrt(2) x) - 78, as a power series over the reals. -/
noncomputable def egf : PowerSeries ℝ :=
  2 * coshS 2 + 3 * coshS (Real.sqrt 2) + 73 * sinhS 1 + coshS 1 * (73 + 4 * sinhS 1) +
    C (2 * Real.sqrt 2) * sinhS (Real.sqrt 2) - 78

/-- Barker's conjectures (the g.f. and the closed forms for even and odd n) and Spezia's e.g.f. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      ((1 - X) * (1 - 2 * X) * (1 - 2 * X ^ 2)) =
      X * (81 - 156 * X - 164 * X ^ 2 + 312 * X ^ 3) ∧
    (∀ n : ℕ, 1 ≤ n → n % 2 = 0 → a n = 3 * 2 ^ (n / 2) + 2 ^ (n + 1) + 73) ∧
    (∀ n : ℕ, n % 2 = 1 → a n = 2 ^ (n + 1) + 2 ^ ((n + 3) / 2) + 73) ∧
    (∀ n : ℕ, 1 ≤ n → (a n : ℝ) = (n.factorial : ℝ) * coeff n egf) := by
  sorry

end OMA.S_oeis_a184044
