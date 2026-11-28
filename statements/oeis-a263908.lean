import Mathlib

/-!
# OEIS A263908: Barker's generating function and closed form

Source: https://oeis.org/A263908 (OEIS Foundation, CC BY-SA 4.0).
Credit: @ceejcake

Entry (R. H. Hardin), offset 1: Number of (2n+1) X (3+2) 0..1 arrays with each row and column
modulo 3 equal to 1, read as a binary number with top and left being the most significant bits.
Data: 33, 2399, 252097, 29452071, 3532758473, ...
Formula section: Conjectures from Colin Barker, Jan 03 2019:
G.f.: x*(33 - 3178*x + 57437*x^2 - 195052*x^3) / ((1 - 4*x)*(1 - 13*x)*(1 - 31*x)*(1 - 121*x)).
a(n) = (5*2^(1+2*n) + 11^(1+2*n) + 31*13^n + 29*31^n) / 81.

Formalization notes:
* A (2n+1) X 5 array over 0..1 is `A : Fin (2 * n + 1) → Fin 5 → Fin 2`, with `A i j` the entry
  in row `i`, column `j`.
* Row `i` read as a binary number with the left entry most significant is
  `Sum_j A i j * 2^(4 - j)`; column `j` read as a binary number with the top entry most
  significant is `Sum_i A i j * 2^(2n - i)`. Every row value and every column value must be
  congruent to 1 modulo 3.
* This reading reproduces all 12 data terms of the entry (a row by row transfer count).
* The g.f. is Sum_(n >= 1) a(n) x^n (offset 1, so the constant coefficient is 0). Since the
  denominator has constant term 1, the identity is stated as denominator times series equals
  numerator in the formal power series ring over the integers. The closed form is stated for
  n >= 1 (the offset) in the integers, multiplied by 81.
* `main` is the conjunction of Barker's two conjectures.
-/

namespace OMA.S_oeis_a263908

open PowerSeries

/-- A row of 5 entries read as a binary number, the left entry being the most significant bit. -/
def rowVal (r : Fin 5 → Fin 2) : ℕ :=
  ∑ j : Fin 5, (r j : ℕ) * 2 ^ (4 - (j : ℕ))

/-- Column `j` of an `m X 5` array read as a binary number, the top entry being the most
significant bit. -/
def colVal {m : ℕ} (A : Fin m → Fin 5 → Fin 2) (j : Fin 5) : ℕ :=
  ∑ i : Fin m, (A i j : ℕ) * 2 ^ (m - 1 - (i : ℕ))

/-- Every row and every column of the array, read as a binary number, is 1 modulo 3. -/
def Valid {m : ℕ} (A : Fin m → Fin 5 → Fin 2) : Prop :=
  (∀ i, rowVal (A i) % 3 = 1) ∧ ∀ j, colVal A j % 3 = 1

instance {m : ℕ} (A : Fin m → Fin 5 → Fin 2) : Decidable (Valid A) := by
  unfold Valid; infer_instance

/-- A263908(n): the number of valid (2n+1) X 5 arrays over 0..1. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter fun A : Fin (2 * n + 1) → Fin 5 → Fin 2 => Valid A).card

/-- Barker's conjectures for A263908 (offset 1): the generating function
x(33 - 3178x + 57437x^2 - 195052x^3) / ((1 - 4x)(1 - 13x)(1 - 31x)(1 - 121x)), and the closed
form (5*2^(1+2n) + 11^(1+2n) + 31*13^n + 29*31^n) / 81 for n >= 1. -/
theorem main :
    (1 - 4 * X) * (1 - 13 * X) * (1 - 31 * X) * (1 - 121 * X) *
        mk (fun n => if n = 0 then 0 else (a n : ℤ)) =
      (X * (33 - 3178 * X + 57437 * X ^ 2 - 195052 * X ^ 3) : PowerSeries ℤ) ∧
    ∀ n : ℕ, 1 ≤ n →
      81 * (a n : ℤ) = 5 * 2 ^ (1 + 2 * n) + 11 ^ (1 + 2 * n) + 31 * 13 ^ n + 29 * 31 ^ n := by
  sorry

end OMA.S_oeis_a263908
