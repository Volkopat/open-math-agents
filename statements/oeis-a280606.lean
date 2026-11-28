import Mathlib

/-!
# OEIS A280606: Barker's conjectures for the x-axis (left edge to origin, base 10) of Rule 294

Source: https://oeis.org/A280606
Formalization: @longling12 (drafted with AI assistance)

Entry A280606 (Robert Price, Jan 06 2017), offset 0: Binary representation of the x-axis, from
the left edge to the origin, of the n-th stage of growth of the two-dimensional cellular
automaton defined by Rule 294, based on the 5-celled von Neumann neighborhood. Initialized with
a single black (ON) cell at stage zero.
Conjectures from Colin Barker, Jan 07 2017:
a(n) = (200 - 11*(-10)^n + 211*10^n) / 200 for n>3.
a(n) = a(n-1) + 100*a(n-2) - 100*a(n-3) for n>4.

Modeling notes:
* Rule 294 uses Wolfram's outer totalistic code on the 5-cell von Neumann neighborhood (kernel
  {{0,2,0},{2,1,2},{0,2,0}}): a cell's next state is bit c + 2*s of 294, where c is its current
  state and s is the number of ON orthogonal neighbors.
* At stage 0 only the origin (0, 0) in Z^2 is ON; every stage updates all cells of Z^2.
* At stage n, a(n) reads the cells (-n, 0), (-n+1, 0), ..., (0, 0) as digits in base 10 with
  (-n, 0) most significant and (0, 0) least significant, matching FromDigits[..., 10] in the
  entry's Mathematica program.
* Note that only Colin Barker's conjectures appear on the problem statement page (Gutkovskiy's
  empirical g.f. is omitted there). For n > 3, 200 divides 10^n, so integer division over Z in
  the closed form is exact.
-/

namespace OMA.S_oeis_a280606

/-- One step of the two-dimensional outer totalistic Rule 294 on the von Neumann neighborhood. -/
def step (s : ℤ → ℤ → Bool) (x y : ℤ) : Bool :=
  Nat.testBit 294 ((s x y).toNat + 2 * ((s (x - 1) y).toNat + (s (x + 1) y).toNat +
    (s x (y - 1)).toNat + (s x (y + 1)).toNat))

/-- Stage n of Rule 294 started from a single ON cell at the origin. -/
def state : ℕ → ℤ → ℤ → Bool
  | 0 => fun x y => decide (x = 0 ∧ y = 0)
  | n + 1 => step (state n)

/-- A280606(n): the cells (-n, 0)..(0, 0) of stage n read in base 10 from left edge to origin. -/
def a (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (n + 1), (state n ((i : ℤ) - n) 0).toNat * 10 ^ (n - i)

/-- Barker's closed-form and recurrence conjectures for A280606. -/
theorem main :
    (∀ n : ℕ, 3 < n → (a n : ℤ) = (200 - 11 * (-10 : ℤ) ^ n + 211 * 10 ^ n) / 200) ∧
    (∀ n : ℕ, 4 < n → (a n : ℤ) = a (n - 1) + 100 * a (n - 2) - 100 * a (n - 3)) := by
  sorry

end OMA.S_oeis_a280606
