import Mathlib

/-!
# OEIS A239358: Barker's conjectures for n X 5 0..2 arrays with no element equal to one plus the sum of elements to its left or one plus the sum of elements above it or one plus the sum of the elements diagonally to its northwest, modulo 3

Source: https://oeis.org/A239358 (OEIS Foundation, CC BY-SA 4.0).

Entry A239358 (R. H. Hardin), offset 1: Number of n X 5 0..2 arrays with no element equal to one plus the sum of elements to its left or one plus the sum of elements above it or one plus the sum of the elements diagonally to its northwest, modulo 3.
Formula section:
Conjectures from Colin Barker, Oct 25 2018: (Start)
G.f.: x*(6 - 8*x + 4*x^2 + 4*x^3 - 20*x^5 + 22*x^6 - x^7 - 7*x^8 + 6*x^9 + x^11) / (1 - x)^4.
a(n) = 4*a(n-1) - 6*a(n-2) + 4*a(n-3) - a(n-4) for n>4.
(End)

Formalization notes:
* An n X 5 array with entries 0..2 is a map x : Fin n -> Fin 5 -> Fin 3, with x i j the entry in
  row i and column j (row 0 at the top, column 0 at the left).
* The elements to the left of (i, j) are x i j' with j' < j, the elements above it are x i' j with
  i' < i, and the elements diagonally to its northwest are x (i - k) (j - k) for k >= 1,
  that is the cells (i', j') with i' < i and i - i' = j - j'.
  Empty sums are 0. "Equal to one plus the sum ... modulo 3" means x i j = (1 + sum) mod 3, the entry
  being read as a number in 0..2.
* a(n) is defined for every n; the entry starts at n = 1, so the g.f. is stated with
  A(x) = Sum_{n >= 1} a(n) x^n, as the identity A(x) * (denominator) = (numerator) in the formal
  power series ring over the rationals; the recurrence is stated for every n > 4 as an identity
  of integers. The statement is the conjunction of the two conjectures.
* The recurrence is stated for n > 4 exactly as printed in the entry. Direct computation gives
  a(6) = 156, while the right side of the recurrence at n = 6 is 176, so the recurrence as printed
  fails for some n; the stated conjunction is therefore false, and the g.f. alone agrees with all listed terms.
* The definition reproduces every listed term of the entry (6, 16, 32, 60, 106, 156, ... from
  n = 1), checked by direct enumeration for small n and by a transfer-matrix count for all 42 terms.
-/

namespace OMA.S_oeis_a239358

open PowerSeries Finset

/-- The sum of the elements to the left of (i, j) in its row. -/
def leftSum {n : ℕ} (x : Fin n → Fin 5 → Fin 3) (i : Fin n) (j : Fin 5) : ℕ :=
  ∑ j' ∈ univ.filter (· < j), (x i j' : ℕ)

/-- The sum of the elements above (i, j) in its column. -/
def aboveSum {n : ℕ} (x : Fin n → Fin 5 → Fin 3) (i : Fin n) (j : Fin 5) : ℕ :=
  ∑ i' ∈ univ.filter (· < i), (x i' j : ℕ)

/-- The sum of the elements diagonally to the northwest of (i, j): the cells (i', j') with i' < i and
i - i' = j - j'. -/
def nwSum {n : ℕ} (x : Fin n → Fin 5 → Fin 3) (i : Fin n) (j : Fin 5) : ℕ :=
  ∑ p ∈ univ.filter (fun p : Fin n × Fin 5 => p.1 < i ∧ (p.1 : ℕ) + j = p.2 + i), (x p.1 p.2 : ℕ)

/-- No element equals one plus any of these sums, modulo 3. -/
def good {n : ℕ} (x : Fin n → Fin 5 → Fin 3) : Prop :=
  ∀ i j, (x i j : ℕ) ≠ (1 + leftSum x i j) % 3 ∧ (x i j : ℕ) ≠ (1 + aboveSum x i j) % 3 ∧
    (x i j : ℕ) ≠ (1 + nwSum x i j) % 3

instance {n : ℕ} : DecidablePred (@good n) := fun x => by unfold good; infer_instance

/-- A239358: number of n X 5 0..2 arrays with no element equal to one plus the sum of elements to its left or one plus the sum of elements above it or one plus the sum of the elements diagonally to its northwest, modulo 3. -/
def a (n : ℕ) : ℕ := ((univ : Finset (Fin n → Fin 5 → Fin 3)).filter good).card

/-- Barker's conjectures. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 4 =
      X * (6 - 8 * X + 4 * X ^ 2 + 4 * X ^ 3 - 20 * X ^ 5 + 22 * X ^ 6 - X ^ 7 - 7 * X ^ 8 + 6 * X ^ 9 + X ^ 11) ∧
    ∀ n : ℕ, 4 < n → (a n : ℤ) = 4 * a (n - 1) - 6 * a (n - 2) + 4 * a (n - 3) - a (n - 4) := by
  sorry

end OMA.S_oeis_a239358
