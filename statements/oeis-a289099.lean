import Mathlib

/-!
# OEIS A289099: Wu's and Spezia's conjectures for the diagonal (origin to corner, base 2) of Rule 545

Source: https://oeis.org/A289099
Conjectures: Chai Wah Wu, Jun 13 2025; Stefano Spezia, Jun 14 2025.
Formalization: @longling12 (drafted with AI assistance)

Entry A289099 (Robert Price, Jun 23 2017), offset 0: Decimal representation of the diagonal from
the origin to the corner of the n-th stage of growth of the two-dimensional cellular automaton
defined by Rule 545, based on the 5-celled von Neumann neighborhood. Initialized with a single
black (ON) cell at stage zero.
Conjectures from Chai Wah Wu, Jun 13 2025:
a(n) = a(n-1) + 4*a(n-2) - 4*a(n-3) for n > 5.
G.f.: (8*x^5 - 8*x^4 + 2*x^2 + 1)/((x - 1)*(2*x - 1)*(2*x + 1)).
Conjectured e.g.f.: x^2 + (1 + 3*cosh(2*x))/2 - cosh(x) - sinh(x) + sinh(2*x). - Stefano Spezia,
Jun 14 2025.

Modeling notes:
* Rule 545 uses Wolfram's outer totalistic code on the 5-cell von Neumann neighborhood (kernel
  {{0,2,0},{2,1,2},{0,2,0}}): a cell's next state is bit c + 2*s of 545, where c is its current
  state and s is the number of ON orthogonal neighbors.
* At stage 0 only the origin (0, 0) in Z^2 is ON; every stage updates all cells of Z^2.
* Following %N and the sequence data, a(n) reads the diagonal cells (0, 0), ..., (n, n) of the
  central (2n+1) x (2n+1) square as binary digits with (0, 0) most significant and (n, n) least
  significant (the last line of %t in the OEIS entry extracts an x-axis row in base 10 instead).
* The ordinary generating function denominator (x - 1)*(2*x - 1)*(2*x + 1) has constant term 1, so
  the identity is stated as A(x) * D(x) = N(x) in PowerSeries Z.
* The exponential generating function Sum_{n >= 0} a(n) * x^n / n! is stated in PowerSeries Q
  using the Maclaurin series of sinh and cosh together with PowerSeries.rescale 2.
-/

namespace OMA.S_oeis_a289099

open PowerSeries

/-- One step of the two-dimensional outer totalistic Rule 545 on the von Neumann neighborhood. -/
def step (s : ℤ → ℤ → Bool) (x y : ℤ) : Bool :=
  Nat.testBit 545 ((s x y).toNat + 2 * ((s (x - 1) y).toNat + (s (x + 1) y).toNat +
    (s x (y - 1)).toNat + (s x (y + 1)).toNat))

/-- Stage n of Rule 545 started from a single ON cell at the origin. -/
def state : ℕ → ℤ → ℤ → Bool
  | 0 => fun x y => decide (x = 0 ∧ y = 0)
  | n + 1 => step (state n)

/-- A289099(n): the diagonal cells (0, 0)..(n, n) of stage n read in binary. -/
def a (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (n + 1), (state n (i : ℤ) (i : ℤ)).toNat * 2 ^ (n - i)

/-- The Maclaurin series of sinh: Sum_{n odd} x^n / n!. -/
noncomputable def sinhSeries : PowerSeries ℚ :=
  PowerSeries.mk fun n => if Even n then 0 else 1 / (n.factorial : ℚ)

/-- The Maclaurin series of cosh: Sum_{n even} x^n / n!. -/
noncomputable def coshSeries : PowerSeries ℚ :=
  PowerSeries.mk fun n => if Even n then 1 / (n.factorial : ℚ) else 0

/-- Wu's recurrence and o.g.f., and Spezia's e.g.f. conjectures for A289099. -/
theorem main :
    (∀ n : ℕ, 5 < n → (a n : ℤ) = a (n - 1) + 4 * a (n - 2) - 4 * a (n - 3)) ∧
    PowerSeries.mk (fun n => (a n : ℤ)) * ((X - 1) * (2 * X - 1) * (2 * X + 1)) =
      8 * X ^ 5 - 8 * X ^ 4 + 2 * X ^ 2 + 1 ∧
    PowerSeries.mk (fun n => (a n : ℚ) / (n.factorial : ℚ)) =
      X ^ 2 + C (1 / 2 : ℚ) * (1 + 3 * rescale (2 : ℚ) coshSeries) -
        coshSeries - sinhSeries + rescale (2 : ℚ) sinhSeries := by
  sorry

end OMA.S_oeis_a289099
