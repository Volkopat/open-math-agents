import Mathlib

/-!
# A282523: Number of n X 3 0..1 arrays with no 1 equal to more than two of its king-move neighbors.

Source: https://oeis.org/A282523
Credit: @physbuzz

The conjectures listed in the entry, all stated below as one conjunction:
* Empirical (R. H. Hardin): a(n) = 5*a(n-1) + 2*a(n-2) - a(n-3) - 24*a(n-4) + 13*a(n-5)
  - 2*a(n-7) + 6*a(n-8), stated for n > 8 (the first index where it involves only terms a(1), ...).
* Conjectured g.f. (R. J. Mathar):
  -x*(8+3*x-25*x^2-11*x^3+13*x^4-2*x^5+4*x^6+6*x^7)/(-1+5*x+2*x^2-x^3-24*x^4+13*x^5-2*x^7+6*x^8),
  stated after multiplying by the denominator, as `Sum_{n>=1} a(n) x^n` times
  `1 - 5x - 2x^2 + x^3 + 24x^4 - 13x^5 + 2x^7 - 6x^8`.

Conventions:
* An n X 3 array is `x : Fin n → Fin 3 → Fin 2`, with `x i j` the entry in row `i`, column `j`.
* The king-move neighbors of cell `(i, j)` are the cells `(i', j') ≠ (i, j)` of the array with
  `|i - i'| ≤ 1` and `|j - j'| ≤ 1`. Entries are 0 or 1, so the number of king-move neighbors equal
  to 1 is the sum of their entries; `get` reads an entry as a natural number and returns 0 outside
  the array, so the sum over all eight offsets counts exactly the neighbors in the array equal to 1.
* Offset 1 as in the OEIS: the series has coefficient 0 at index 0.
This reading reproduces the listed terms 8, 43, 206, 1097, 5675, 29433 (brute force).
-/

namespace OMA.S_oeis_a282523

open PowerSeries

/-- The entry of `x` in row `i`, column `j` as a natural number, and `0` outside the array. -/
def get {n : ℕ} (x : Fin n → Fin 3 → Fin 2) (i j : ℤ) : ℕ :=
  if h : 0 ≤ i ∧ i < n ∧ 0 ≤ j ∧ j < 3 then
    (x ⟨i.toNat, by omega⟩ ⟨j.toNat, by omega⟩ : ℕ)
  else 0

/-- The number of king-move neighbors of cell `(i, j)` equal to 1. -/
def kingOnes {n : ℕ} (x : Fin n → Fin 3 → Fin 2) (i j : ℤ) : ℕ :=
  ∑ di : Fin 3, ∑ dj : Fin 3,
    if di = 1 ∧ dj = 1 then 0 else get x (i + di - 1) (j + dj - 1)

/-- No 1 is equal to more than two of its king-move neighbors. -/
def Valid {n : ℕ} (x : Fin n → Fin 3 → Fin 2) : Prop :=
  ∀ i : Fin n, ∀ j : Fin 3, x i j = 1 → kingOnes x i j ≤ 2

instance {n : ℕ} (x : Fin n → Fin 3 → Fin 2) : Decidable (Valid x) := by
  unfold Valid; infer_instance

/-- A282523(n): the number of valid n X 3 arrays. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter fun x : Fin n → Fin 3 → Fin 2 => Valid x).card

theorem main :
    (∀ n : ℕ, 8 < n → (a n : ℤ) = 5 * a (n - 1) + 2 * a (n - 2) - a (n - 3) - 24 * a (n - 4) +
      13 * a (n - 5) - 2 * a (n - 7) + 6 * a (n - 8)) ∧
    (PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) *
        (1 - 5 * X - 2 * X ^ 2 + X ^ 3 + 24 * X ^ 4 - 13 * X ^ 5 + 2 * X ^ 7 - 6 * X ^ 8) =
      X * (8 + 3 * X - 25 * X ^ 2 - 11 * X ^ 3 + 13 * X ^ 4 - 2 * X ^ 5 + 4 * X ^ 6 + 6 * X ^ 7)) := by
  sorry

end OMA.S_oeis_a282523
