import Mathlib

/-!
# OEIS A238806: Barker's conjectures for n X 2 0..2 arrays with no element equal to one plus the sum of elements to its left or one plus the sum of the sum of elements above it, modulo 3

Source: https://oeis.org/A238806 (OEIS Foundation, CC BY-SA 4.0).

Entry A238806 (R. H. Hardin), offset 1: Number of n X 2 0..2 arrays with no element equal to one plus the sum of elements to its left or one plus the sum of the sum of elements above it, modulo 3.
Formula section:
Conjectures from Colin Barker, Oct 24 2018: (Start)
G.f.: (3 - 4*x + x^2 + x^3) / (1 - x)^4.
a(n) = 4*a(n-1) - 6*a(n-2) + 4*a(n-3) - a(n-4) for n>4.
(End)

Formalization notes:
* An n X 2 array with entries 0..2 is a map x : Fin n -> Fin 2 -> Fin 3, with x i j the entry in
  row i and column j (row 0 at the top, column 0 at the left).
* The elements to the left of (i, j) are x i j' with j' < j, the elements above it are x i' j with
  i' < i.
  Empty sums are 0. "Equal to one plus the sum ... modulo 3" means x i j = (1 + sum) mod 3, the entry
  being read as a number in 0..2.
* The entry's name says "one plus the sum of the sum of elements above it"; this is read as one plus
  the sum of the elements above it, as in the companion entries with more columns; this reading
  reproduces every listed term.
* The entry starts at n = 1 and its g.f. has a nonzero constant term, so the g.f. is the series
  A(x) = Sum_{n >= 0} a(n+1) x^n; it is stated as the identity A(x) * (denominator) = (numerator)
  in the formal power series ring over the rationals; the recurrence is stated for every n > 4 as an identity
  of integers. The statement is the conjunction of the two conjectures.
* The definition reproduces every listed term of the entry (3, 8, 15, 25, 39, 58, ... from
  n = 1), checked by direct enumeration for small n and by a transfer-matrix count for all 45 terms.
-/

namespace OMA.S_oeis_a238806

open PowerSeries Finset

/-- The sum of the elements to the left of (i, j) in its row. -/
def leftSum {n : ℕ} (x : Fin n → Fin 2 → Fin 3) (i : Fin n) (j : Fin 2) : ℕ :=
  ∑ j' ∈ univ.filter (· < j), (x i j' : ℕ)

/-- The sum of the elements above (i, j) in its column. -/
def aboveSum {n : ℕ} (x : Fin n → Fin 2 → Fin 3) (i : Fin n) (j : Fin 2) : ℕ :=
  ∑ i' ∈ univ.filter (· < i), (x i' j : ℕ)

/-- No element equals one plus either of these sums, modulo 3. -/
def good {n : ℕ} (x : Fin n → Fin 2 → Fin 3) : Prop :=
  ∀ i j, (x i j : ℕ) ≠ (1 + leftSum x i j) % 3 ∧ (x i j : ℕ) ≠ (1 + aboveSum x i j) % 3

instance {n : ℕ} : DecidablePred (@good n) := fun x => by unfold good; infer_instance

/-- A238806: number of n X 2 0..2 arrays with no element equal to one plus the sum of elements to its left or one plus the sum of the sum of elements above it, modulo 3. -/
def a (n : ℕ) : ℕ := ((univ : Finset (Fin n → Fin 2 → Fin 3)).filter good).card

/-- Barker's conjectures. -/
theorem main :
    PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * (1 - X) ^ 4 =
      (3 - 4 * X + X ^ 2 + X ^ 3) ∧
    ∀ n : ℕ, 4 < n → (a n : ℤ) = 4 * a (n - 1) - 6 * a (n - 2) + 4 * a (n - 3) - a (n - 4) := by
  sorry

end OMA.S_oeis_a238806
