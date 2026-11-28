import Mathlib

/-!
# OEIS A263907: Barker's generating function and closed form

Source: https://oeis.org/A263907 (OEIS Foundation, CC BY-SA 4.0).
Credit: @ceejcake

Entry (R. H. Hardin), offset 1: Number of (2n+2) X (2+2) 0..1 arrays with each row and column
modulo 3 equal to 1, read as a binary number with top and left being the most significant bits.
Data: 16, 528, 14112, 359200, 9024816, ...
Formula section: Conjectures from Colin Barker, Jan 03 2019:
G.f.: 16*x / ((1 - x)*(1 - 7*x)*(1 - 25*x)).
a(n) = (3 - 4*7^(1+n) + 25^(1+n)) / 27.

Formalization notes:
* A (2n+2) X 4 array over 0..1 is `A : Fin (2 * n + 2) → Fin 4 → Fin 2`, with `A i j` the entry
  in row `i`, column `j`.
* Row `i` read as a binary number with the left entry most significant is
  `Sum_j A i j * 2^(3 - j)`; column `j` read as a binary number with the top entry most
  significant is `Sum_i A i j * 2^(2n+1 - i)`. Every row value and every column value must be
  congruent to 1 modulo 3.
* This reading reproduces all 15 data terms of the entry (a row by row transfer count).
* The g.f. is Sum_(n >= 1) a(n) x^n (offset 1, so the constant coefficient is 0). Since the
  denominator has constant term 1, the identity is stated as denominator times series equals
  numerator in the formal power series ring over the integers. The closed form is stated for
  n >= 1 (the offset) in the integers, multiplied by 27.
* `main` is the conjunction of Barker's two conjectures.
-/

namespace OMA.S_oeis_a263907

open PowerSeries

/-- A row of 4 entries read as a binary number, the left entry being the most significant bit. -/
def rowVal (r : Fin 4 → Fin 2) : ℕ :=
  ∑ j : Fin 4, (r j : ℕ) * 2 ^ (3 - (j : ℕ))

/-- Column `j` of an `m X 4` array read as a binary number, the top entry being the most
significant bit. -/
def colVal {m : ℕ} (A : Fin m → Fin 4 → Fin 2) (j : Fin 4) : ℕ :=
  ∑ i : Fin m, (A i j : ℕ) * 2 ^ (m - 1 - (i : ℕ))

/-- Every row and every column of the array, read as a binary number, is 1 modulo 3. -/
def Valid {m : ℕ} (A : Fin m → Fin 4 → Fin 2) : Prop :=
  (∀ i, rowVal (A i) % 3 = 1) ∧ ∀ j, colVal A j % 3 = 1

instance {m : ℕ} (A : Fin m → Fin 4 → Fin 2) : Decidable (Valid A) := by
  unfold Valid; infer_instance

/-- A263907(n): the number of valid (2n+2) X 4 arrays over 0..1. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter fun A : Fin (2 * n + 2) → Fin 4 → Fin 2 => Valid A).card

/-- Barker's conjectures for A263907 (offset 1): the generating function
16x / ((1 - x)(1 - 7x)(1 - 25x)), and the closed form (3 - 4*7^(1+n) + 25^(1+n)) / 27 for
n >= 1. -/
theorem main :
    (1 - X) * (1 - 7 * X) * (1 - 25 * X) * mk (fun n => if n = 0 then 0 else (a n : ℤ)) =
      (16 * X : PowerSeries ℤ) ∧
    ∀ n : ℕ, 1 ≤ n → 27 * (a n : ℤ) = 3 - 4 * 7 ^ (1 + n) + 25 ^ (1 + n) := by
  sorry

end OMA.S_oeis_a263907
