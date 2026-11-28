import Mathlib

/-!
# OEIS A253490: Barker's g.f. and closed form for (n+1) X 4 arrays over 0..2 with 2 X 2 diagonal minus antidiagonal sums nondecreasing horizontally, vertically and ne-to-sw antidiagonally

Source: https://oeis.org/A253490 (OEIS Foundation, CC BY-SA 4.0).

Entry A253490 (R. H. Hardin, Jan 02 2015), offset 1: Number of (n+1) X (3+1) 0..2 arrays with
every 2 X 2 subblock diagonal minus antidiagonal sum nondecreasing horizontally, vertically and
ne-to-sw antidiagonally. Column 3 of A253495. Data: 1388, 3090, 4196, 6931, 13528, 29370, 68992,
172050, ... Formula section: Conjectures from Colin Barker, Dec 15 2018: (Start)
G.f.: x*(1388 - 5238*x + 924*x^2 + 7417*x^3 - 442*x^4 - 733*x^5 - 6*x^6) /
((1 - x)*(1 - 2*x)*(1 - 3*x)).
a(n) = 1655 + 247*2^n + 49*3^(n-1) for n>4. (End)

Formalization notes:
* An array is a function x : Fin (n + 1) -> Fin 4 -> Fin 3, x i j being the element in row i and
  column j. For the 2 X 2 subblock B(i,j) with rows i, i' = i + 1 and columns j, j' = j + 1 the
  value is the diagonal sum minus the antidiagonal sum, x(i,j) + x(i',j') - x(i,j') - x(i',j),
  computed in Z (`blockValue`).
* Nondecreasing horizontally: B(i,j) <= B(i,j+1). Nondecreasing vertically: B(i,j) <= B(i+1,j).
  Nondecreasing ne-to-sw antidiagonally: going from the block B(i,j+1) to its south-west neighbour
  B(i+1,j), B(i,j+1) <= B(i+1,j). This reading reproduces the entry's data a(1..8) = 1388, 3090,
  4196, 6931, 13528, 29370, 68992, 172050 (a transfer on pairs of rows; the reversed antidiagonal
  reading or dropping it gives different numbers).
* The g.f. is A(x) = Sum_{n >= 1} a(n) x^n (offset 1), stated as A(x) times the denominator equal
  to the numerator in Q[[x]], which is equivalent to the quotient form because the denominator has
  constant term 1. The closed form is stated in Q for n > 4, the range given in the source.
* `main` is the conjunction of Barker's two conjectures.
-/

namespace OMA.S_oeis_a253490

open PowerSeries

/-- The diagonal sum minus the antidiagonal sum of the 2 X 2 subblock with rows i, i' and
columns j, j' of the array x: x(i,j) + x(i',j') - x(i,j') - x(i',j), in Z. -/
def blockValue {m : ℕ} (x : Fin m → Fin 4 → Fin 3) (i i' : Fin m) (j j' : Fin 4) : ℤ :=
  ((x i j).val : ℤ) + ((x i' j').val : ℤ) - ((x i j').val : ℤ) - ((x i' j).val : ℤ)

/-- The subblock values B(i,j) = blockValue x i (i+1) j (j+1) are nondecreasing horizontally:
B(i,j) <= B(i,j+1). -/
def Horizontal {m : ℕ} (x : Fin m → Fin 4 → Fin 3) : Prop :=
  ∀ i i' : Fin m, i'.val = i.val + 1 →
    ∀ j j' j'' : Fin 4, j'.val = j.val + 1 → j''.val = j'.val + 1 →
      blockValue x i i' j j' ≤ blockValue x i i' j' j''

/-- The subblock values are nondecreasing vertically: B(i,j) <= B(i+1,j). -/
def Vertical {m : ℕ} (x : Fin m → Fin 4 → Fin 3) : Prop :=
  ∀ i i' i'' : Fin m, i'.val = i.val + 1 → i''.val = i'.val + 1 →
    ∀ j j' : Fin 4, j'.val = j.val + 1 →
      blockValue x i i' j j' ≤ blockValue x i' i'' j j'

/-- The subblock values are nondecreasing ne-to-sw antidiagonally: from B(i,j+1) to its
south-west neighbour B(i+1,j), B(i,j+1) <= B(i+1,j). -/
def Antidiagonal {m : ℕ} (x : Fin m → Fin 4 → Fin 3) : Prop :=
  ∀ i i' i'' : Fin m, i'.val = i.val + 1 → i''.val = i'.val + 1 →
    ∀ j j' j'' : Fin 4, j'.val = j.val + 1 → j''.val = j'.val + 1 →
      blockValue x i i' j' j'' ≤ blockValue x i' i'' j j'

instance {m : ℕ} (x : Fin m → Fin 4 → Fin 3) : Decidable (Horizontal x) := by
  unfold Horizontal; infer_instance

instance {m : ℕ} (x : Fin m → Fin 4 → Fin 3) : Decidable (Vertical x) := by
  unfold Vertical; infer_instance

instance {m : ℕ} (x : Fin m → Fin 4 → Fin 3) : Decidable (Antidiagonal x) := by
  unfold Antidiagonal; infer_instance

/-- A253490(n): the number of (n+1) X 4 arrays with entries 0..2 whose 2 X 2 subblock values are
nondecreasing horizontally, vertically and ne-to-sw antidiagonally. -/
def a (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin (n + 1) → Fin 4 → Fin 3)).filter (fun x =>
    Horizontal x ∧ Vertical x ∧ Antidiagonal x)).card

/-- Barker's conjectures: the g.f. and the closed form for n > 4. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      ((1 - X) * (1 - 2 * X) * (1 - 3 * X)) =
        X * (1388 - 5238 * X + 924 * X ^ 2 + 7417 * X ^ 3 - 442 * X ^ 4 - 733 * X ^ 5 -
          6 * X ^ 6) ∧
      ∀ n : ℕ, 4 < n → (a n : ℚ) = 1655 + 247 * 2 ^ n + 49 * 3 ^ (n - 1) := by
  sorry

end OMA.S_oeis_a253490
