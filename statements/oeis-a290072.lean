import Mathlib

/-!
# OEIS A290072: Barker's conjectures for the diagonal (origin to corner, base 10) of Rule 641

Source: https://oeis.org/A290072
Conjectures: Colin Barker, Jul 20 2017.
Formalization: @longling12 (drafted with AI assistance)

Entry A290072 (Robert Price, Jul 19 2017), offset 0: Binary representation of the diagonal from
the origin to the corner of the n-th stage of growth of the two-dimensional cellular automaton
defined by Rule 641, based on the 5-celled von Neumann neighborhood, initialized with a single
black (ON) cell at stage zero.
Conjectures from Colin Barker, Jul 20 2017:
G.f.: (1 - 90*x^3 + 100*x^4) / ((1 - x)*(1 - 10*x)*(1 + 10*x)).
a(n) = a(n-1) + 100*a(n-2) - 100*a(n-3) = A283505(n) for n>4.
Entry A283505 (Robert Price, Mar 09 2017), offset 0: Binary representation of the x-axis, from
the origin to the right edge, of the n-th stage of growth of Rule 641.

Modeling notes:
* Outer-totalistic 5-cell von Neumann Rule 641 on Z^2 started from a single ON cell at (0, 0).
* In entry A290072, the last line of %t extracts the central row (giving 0 at n = 1), which does
  not match the published data 1, 1, 101, 11, 10111, ...; following %N and the published data,
  a(n) reads the diagonal cells (0, 0), (1, 1), ..., (n, n) in base 10 with (0, 0) most
  significant.
* Following %N and %t of A283505, A283505(n) reads the x-axis cells (0, 0), (1, 0), ..., (n, 0)
  in base 10 with (0, 0) most significant, reproducing 1, 0, 101, 11, 10111, ...
-/

namespace OMA.S_oeis_a290072

open PowerSeries

/-- One step of outer-totalistic Rule 641 on the 5-cell von Neumann neighborhood. -/
def step (s : ℤ → ℤ → Bool) (x y : ℤ) : Bool :=
  Nat.testBit 641 ((s x y).toNat + 2 * ((s (x - 1) y).toNat + (s (x + 1) y).toNat +
    (s x (y - 1)).toNat + (s x (y + 1)).toNat))

/-- Stage n of Rule 641 started from a single ON cell at the origin. -/
def state : ℕ → ℤ → ℤ → Bool
  | 0 => fun x y => decide (x = 0 ∧ y = 0)
  | n + 1 => step (state n)

/-- A290072(n): diagonal cells (0, 0)..(n, n) of stage n read in base 10 from origin to corner. -/
def a (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (n + 1), (state n (i : ℤ) (i : ℤ)).toNat * 10 ^ (n - i)

/-- A283505(n): x-axis cells (0, 0)..(n, 0) of stage n read in base 10 from origin to right edge. -/
def A283505 (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (n + 1), (state n (i : ℤ) 0).toNat * 10 ^ (n - i)

/-- Barker's generating function, recurrence, and cross-sequence equality for A290072. -/
theorem main :
    PowerSeries.mk (fun n => (a n : ℤ)) * ((1 - X) * (1 - 10 * X) * (1 + 10 * X)) =
      1 - 90 * X ^ 3 + 100 * X ^ 4 ∧
    (∀ n : ℕ, 4 < n → (a n : ℤ) = a (n - 1) + 100 * a (n - 2) - 100 * a (n - 3)) ∧
    (∀ n : ℕ, 4 < n → a n = A283505 n) := by
  sorry

end OMA.S_oeis_a290072
