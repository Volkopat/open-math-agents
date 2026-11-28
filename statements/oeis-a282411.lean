import Mathlib

/-!
# OEIS A282411: Barker's and Mathar's conjectures for the x-axis (left edge to origin, base 10) of Rule 467

Source: https://oeis.org/A282411
Conjectures: Colin Barker, Feb 15 2017; R. J. Mathar, Jun 21 2025.
Formalization: @longling12 (drafted with AI assistance)

Entry A282411 (Robert Price, Feb 14 2017), offset 0: Binary representation of the x-axis, from
the left edge to the origin, of the n-th stage of growth of the two-dimensional cellular
automaton defined by Rule 467, based on the 5-celled von Neumann neighborhood, initialized with
a single black (ON) cell at stage zero.
Conjectures from Colin Barker, Feb 15 2017:
a(n) = (1 + (-1)^n) * (10^(1+n)-1)/18 for n>1.
a(n) = 101*a(n-2) - 100*a(n-4) for n>3.
G.f.: (1 + x + 10*x^2 - 101*x^3 + 100*x^5) / ((1 - x)*(1 + x)*(1 - 10*x)*(1 + 10*x)).
Equivalent conjecture: a(n) = A279118(n) for n>=2. - R. J. Mathar, Jun 21 2025.
Entry A279118 (Robert Price, Dec 21 2016), offset 0, reads the x-axis from the left edge to the
origin in base 10 for Rule 209.

Modeling notes:
* Outer-totalistic 5-cell von Neumann Rules 467 and 209 on Z^2 started from a single ON cell at
  (0, 0).
* At stage n, cells (-n, 0), (-n + 1, 0), ..., (0, 0) are read as digits in base 10 with (-n, 0)
  most significant, matching FromDigits[..., 10] in the entries' Mathematica programs.
* Since 2 divides 1 + (-1)^n and 9 divides 10^(1+n) - 1 for every n, integer division by 18 over
  Z is exact.
-/

namespace OMA.S_oeis_a282411

open PowerSeries

/-- One step of outer-totalistic Rule r on the 5-cell von Neumann neighborhood. -/
def step (r : ℕ) (s : ℤ → ℤ → Bool) (x y : ℤ) : Bool :=
  Nat.testBit r ((s x y).toNat + 2 * ((s (x - 1) y).toNat + (s (x + 1) y).toNat +
    (s x (y - 1)).toNat + (s x (y + 1)).toNat))

/-- Stage n of Rule r started from a single ON cell at the origin. -/
def state (r : ℕ) : ℕ → ℤ → ℤ → Bool
  | 0 => fun x y => decide (x = 0 ∧ y = 0)
  | n + 1 => step r (state r n)

/-- Cells (-n, 0)..(0, 0) of stage n of Rule r read in base 10 from left edge to origin. -/
def xaxisLeft10 (r n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (n + 1), (state r n ((i : ℤ) - n) 0).toNat * 10 ^ (n - i)

/-- A282411(n): x-axis from left edge to origin in base 10 for Rule 467. -/
def a (n : ℕ) : ℕ := xaxisLeft10 467 n

/-- A279118(n): x-axis from left edge to origin in base 10 for Rule 209. -/
def A279118 (n : ℕ) : ℕ := xaxisLeft10 209 n

/-- Barker's and Mathar's conjectures for A282411. -/
theorem main :
    (∀ n : ℕ, 1 < n → (a n : ℤ) = (1 + (-1 : ℤ) ^ n) * (10 ^ (1 + n) - 1) / 18) ∧
    (∀ n : ℕ, 3 < n → (a n : ℤ) = 101 * a (n - 2) - 100 * a (n - 4)) ∧
    PowerSeries.mk (fun n => (a n : ℤ)) *
      ((1 - X) * (1 + X) * (1 - 10 * X) * (1 + 10 * X)) =
      1 + X + 10 * X ^ 2 - 101 * X ^ 3 + 100 * X ^ 5 ∧
    (∀ n : ℕ, 2 ≤ n → a n = A279118 n) := by
  sorry

end OMA.S_oeis_a282411
