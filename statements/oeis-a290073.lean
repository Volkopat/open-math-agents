import Mathlib

/-!
# OEIS A290073: Barker's conjectures for the diagonal (corner to origin, base 2) of Rule 641

Source: https://oeis.org/A290073
Conjectures: Colin Barker, Jul 20 2017.
Formalization: @longling12 (drafted with AI assistance)

Entry A290073 (Robert Price, Jul 19 2017), offset 0: Decimal representation of the diagonal from
the corner to the origin of the n-th stage of growth of the two-dimensional cellular automaton
defined by Rule 641, based on the 5-celled von Neumann neighborhood, initialized with a single
black (ON) cell at stage zero.
Conjectures from Colin Barker, Jul 20 2017:
G.f.: (1 + 2*x^3 + 4*x^4) / ((1 - x)*(1 + x)*(1 - 2*x)).
a(n) = 2^(n+1) - 3 = A283506(n) for n>1 and even.
a(n) = 2^(n+1) - 4 = A283506(n) for n>1 and odd.
a(n) = 2*a(n-1) + a(n-2) - 2*a(n-3) for n>4.
Entry A283506 (Robert Price, Mar 09 2017), offset 0: Decimal representation of the x-axis, from
the left edge to the origin, of the n-th stage of growth of Rule 641.

Modeling notes:
* Outer-totalistic 5-cell von Neumann Rule 641 on Z^2 started from a single ON cell at (0, 0).
* In entry A290073, the last line of %t extracts the central row in base 10, which does not match
  the published data 1, 2, 5, 12, 29, 60, ...; following %N and the published data, a(n) reads
  the diagonal cells (-n, -n), (-n + 1, -n + 1), ..., (0, 0) in base 2 with (-n, -n) most
  significant.
* Following %N and %t of A283506, A283506(n) reads the x-axis cells (-n, 0), (-n + 1, 0), ...,
  (0, 0) in base 2 with (-n, 0) most significant, reproducing 1, 0, 5, 12, 29, 60, ...
-/

namespace OMA.S_oeis_a290073

open PowerSeries

/-- One step of outer-totalistic Rule 641 on the 5-cell von Neumann neighborhood. -/
def step (s : ℤ → ℤ → Bool) (x y : ℤ) : Bool :=
  Nat.testBit 641 ((s x y).toNat + 2 * ((s (x - 1) y).toNat + (s (x + 1) y).toNat +
    (s x (y - 1)).toNat + (s x (y + 1)).toNat))

/-- Stage n of Rule 641 started from a single ON cell at the origin. -/
def state : ℕ → ℤ → ℤ → Bool
  | 0 => fun x y => decide (x = 0 ∧ y = 0)
  | n + 1 => step (state n)

/-- A290073(n): diagonal cells (-n, -n)..(0, 0) of stage n read in base 2 from corner to origin. -/
def a (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (n + 1), (state n ((i : ℤ) - n) ((i : ℤ) - n)).toNat * 2 ^ (n - i)

/-- A283506(n): x-axis cells (-n, 0)..(0, 0) of stage n read in base 2 from left edge to origin. -/
def A283506 (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (n + 1), (state n ((i : ℤ) - n) 0).toNat * 2 ^ (n - i)

/-- Barker's generating function, parity closed forms, cross-sequence equalities, and recurrence. -/
theorem main :
    PowerSeries.mk (fun n => (a n : ℤ)) * ((1 - X) * (1 + X) * (1 - 2 * X)) =
      1 + 2 * X ^ 3 + 4 * X ^ 4 ∧
    (∀ n : ℕ, 1 < n → n % 2 = 0 → (a n : ℤ) = 2 ^ (n + 1) - 3 ∧ a n = A283506 n) ∧
    (∀ n : ℕ, 1 < n → n % 2 = 1 → (a n : ℤ) = 2 ^ (n + 1) - 4 ∧ a n = A283506 n) ∧
    (∀ n : ℕ, 4 < n → (a n : ℤ) = 2 * a (n - 1) + a (n - 2) - 2 * a (n - 3)) := by
  sorry

end OMA.S_oeis_a290073
