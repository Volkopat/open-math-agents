import Mathlib

/-!
# OEIS A253505: Barker's conjectures for (n+2) X (3+2) 0..1 arrays with every 2 X 2 and 3 X 3 subblock diagonal maximum minus antidiagonal minimum nondecreasing horizontally and vertically

Source: https://oeis.org/A253505 (OEIS Foundation, CC BY-SA 4.0).

Entry A253505 (R. H. Hardin), offset 1: Number of (n+2) X (3+2) 0..1 arrays with every 2 X 2 and 3 X 3 subblock diagonal maximum minus antidiagonal minimum nondecreasing horizontally and vertically.
Formula section:
Conjectures from Colin Barker, Dec 16 2018: (Start)
G.f.: 4*x*(107 - 232*x + 191*x^2 - 62*x^3 - 4*x^4 + 6*x^5 - 2*x^6 + x^7) / (1 - x)^4.
a(n) = 4*a(n-1) - 6*a(n-2) + 4*a(n-3) - a(n-4) for n>8.
(End)

Formalization notes:
* An (n+2) X 5 array with entries 0..1 is a map x : Fin (n + 2) -> Fin 5 -> Fin 2, with x i j the entry
  in row i and column j (row 0 at the top, column 0 at the left); `e x i j` is that entry as a natural
  number, and 0 outside the array (only entries inside the array are ever used).
* The 2 X 2 subblock with top left cell (i, j) has diagonal (i, j), (i+1, j+1) and antidiagonal
  (i, j+1), (i+1, j); the 3 X 3 subblock has diagonal (i, j), (i+1, j+1), (i+2, j+2) and antidiagonal
  (i, j+2), (i+1, j+1), (i+2, j). Its value is the diagonal maximum minus the antidiagonal minimum
  (`v2`, `v3`, as integers).
* "Nondecreasing horizontally and vertically": for subblocks of the same size, the value of every
  subblock is at most the value of its right neighbour (one column further) and of its lower
  neighbour (one row further), whenever that neighbour lies inside the array.
* a(n) is defined for every n; the entry starts at n = 1, so the g.f. is stated with
  A(x) = Sum_{n >= 1} a(n) x^n, as the identity A(x) * (denominator) = (numerator) in the formal
  power series ring over the rationals; the recurrence is stated for every n > 8 as an identity
  of integers. The statement is the conjunction of the two conjectures.
* The definition reproduces every listed term of the entry (428, 784, 1332, 2088, 3052, ... from
  n = 1), checked by direct enumeration for n = 1 and by a transfer-matrix count for all 35 terms.
-/

namespace OMA.S_oeis_a253505

open PowerSeries Finset

/-- Entry (i, j) of x as a natural number, and 0 outside the array. -/
def e {n : ℕ} (x : Fin (n + 2) → Fin 5 → Fin 2) (i j : ℕ) : ℕ :=
  if h : i < n + 2 ∧ j < 5 then (x ⟨i, h.1⟩ ⟨j, h.2⟩ : ℕ) else 0

/-- Diagonal maximum minus antidiagonal minimum of the 2 X 2 subblock with top left cell (i, j). -/
def v2 {n : ℕ} (x : Fin (n + 2) → Fin 5 → Fin 2) (i j : ℕ) : ℤ :=
  max (e x i j : ℤ) (e x (i + 1) (j + 1)) - min (e x i (j + 1) : ℤ) (e x (i + 1) j)

/-- Diagonal maximum minus antidiagonal minimum of the 3 X 3 subblock with top left cell (i, j). -/
def v3 {n : ℕ} (x : Fin (n + 2) → Fin 5 → Fin 2) (i j : ℕ) : ℤ :=
  max (max (e x i j : ℤ) (e x (i + 1) (j + 1))) (e x (i + 2) (j + 2)) -
    min (min (e x i (j + 2) : ℤ) (e x (i + 1) (j + 1))) (e x (i + 2) j)

/-- Every 2 X 2 and every 3 X 3 subblock value is at most that of its right and lower neighbours. -/
def good {n : ℕ} (x : Fin (n + 2) → Fin 5 → Fin 2) : Prop :=
  (∀ i < n + 2, ∀ j < 5, i + 1 < n + 2 → j + 2 < 5 → v2 x i j ≤ v2 x i (j + 1)) ∧
  (∀ i < n + 2, ∀ j < 5, i + 2 < n + 2 → j + 1 < 5 → v2 x i j ≤ v2 x (i + 1) j) ∧
  (∀ i < n + 2, ∀ j < 5, i + 2 < n + 2 → j + 3 < 5 → v3 x i j ≤ v3 x i (j + 1)) ∧
  (∀ i < n + 2, ∀ j < 5, i + 3 < n + 2 → j + 2 < 5 → v3 x i j ≤ v3 x (i + 1) j)

instance {n : ℕ} : DecidablePred (@good n) := fun x => by
  unfold good
  refine @instDecidableAnd _ _ ?_ (@instDecidableAnd _ _ ?_ (@instDecidableAnd _ _ ?_ ?_)) <;> infer_instance

/-- A253505: number of (n+2) X (3+2) 0..1 arrays with every 2 X 2 and 3 X 3 subblock diagonal maximum minus antidiagonal minimum nondecreasing horizontally and vertically. -/
def a (n : ℕ) : ℕ := ((univ : Finset (Fin (n + 2) → Fin 5 → Fin 2)).filter good).card

/-- Barker's conjectures. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 4 =
      4 * X * (107 - 232 * X + 191 * X ^ 2 - 62 * X ^ 3 - 4 * X ^ 4 + 6 * X ^ 5 - 2 * X ^ 6 + X ^ 7) ∧
    ∀ n : ℕ, 8 < n → (a n : ℤ) = 4 * a (n - 1) - 6 * a (n - 2) + 4 * a (n - 3) - a (n - 4) := by
  sorry

end OMA.S_oeis_a253505
