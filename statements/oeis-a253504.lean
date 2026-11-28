import Mathlib

/-!
# OEIS A253504: Barker's g.f. and recurrence for (n+2) X 4 binary arrays with 2 X 2 and 3 X 3 diagonal maximum minus antidiagonal minimum nondecreasing horizontally and vertically

Source: https://oeis.org/A253504 (OEIS Foundation, CC BY-SA 4.0).

Entry A253504 (R. H. Hardin, Jan 02 2015), offset 1: Number of (n+2) X (2+2) 0..1 arrays with
every 2 X 2 and 3X3 subblock diagonal maximum minus antidiagonal minimum nondecreasing
horizontally and vertically. Column 2 of A253510. Data: 260, 472, 784, 1196, 1712, 2340, 3088,
3964, 4976, 6132, ... Formula section: Conjectures from Colin Barker, Dec 16 2018: (Start)
G.f.: 4*x*(65 - 142*x + 114*x^2 - 37*x^3 + x^4 + x^5) / (1 - x)^4.
a(n) = 4*a(n-1) - 6*a(n-2) + 4*a(n-3) - a(n-4) for n>6. (End)

Formalization notes:
* An array is a function x : Fin (n + 2) -> Fin 4 -> Fin 2, x i j being the element in row i and
  column j.
* For the 2 X 2 subblock with rows i, i' = i + 1 and columns j, j' = j + 1 the value is the
  diagonal maximum minus the antidiagonal minimum, max(x(i,j), x(i',j')) - min(x(i,j'), x(i',j))
  (`value2`). For the 3 X 3 subblock with rows i, i + 1, i + 2 and columns j, j + 1, j + 2 the
  diagonal is x(i,j), x(i+1,j+1), x(i+2,j+2) and the antidiagonal x(i,j+2), x(i+1,j+1), x(i+2,j);
  its value is the diagonal maximum minus the antidiagonal minimum (`value3`). Values are in Z.
* Nondecreasing horizontally compares each subblock with the subblock of the same size one column
  to the right, nondecreasing vertically with the one one row below; this is required for the
  2 X 2 and for the 3 X 3 subblocks. This reading reproduces the entry's data a(1..15) (a transfer
  on triples of rows).
* The g.f. is A(x) = Sum_{n >= 1} a(n) x^n (offset 1), stated as A(x) times the denominator equal
  to the numerator in Q[[x]], which is equivalent to the quotient form because the denominator has
  constant term 1. The recurrence is stated in Q for n > 6, the range given in the source.
* `main` is the conjunction of Barker's two conjectures.
-/

namespace OMA.S_oeis_a253504

open PowerSeries

/-- The diagonal maximum minus the antidiagonal minimum of the 2 X 2 subblock with rows i, i' and
columns j, j' of x: max(x(i,j), x(i',j')) - min(x(i,j'), x(i',j)), in Z. -/
def value2 {m : ℕ} (x : Fin m → Fin 4 → Fin 2) (i i' : Fin m) (j j' : Fin 4) : ℤ :=
  max ((x i j).val : ℤ) ((x i' j').val : ℤ) - min ((x i j').val : ℤ) ((x i' j).val : ℤ)

/-- The diagonal maximum minus the antidiagonal minimum of the 3 X 3 subblock with rows i, i', i''
and columns j, j', j'' of x: max(x(i,j), x(i',j'), x(i'',j'')) - min(x(i,j''), x(i',j'), x(i'',j)),
in Z. -/
def value3 {m : ℕ} (x : Fin m → Fin 4 → Fin 2) (i i' i'' : Fin m) (j j' j'' : Fin 4) : ℤ :=
  max (max ((x i j).val : ℤ) ((x i' j').val : ℤ)) ((x i'' j'').val : ℤ) -
    min (min ((x i j'').val : ℤ) ((x i' j').val : ℤ)) ((x i'' j).val : ℤ)

/-- The 2 X 2 subblock values are nondecreasing horizontally. -/
def Horizontal2 {m : ℕ} (x : Fin m → Fin 4 → Fin 2) : Prop :=
  ∀ i i' : Fin m, i'.val = i.val + 1 →
    ∀ j j' j'' : Fin 4, j'.val = j.val + 1 → j''.val = j'.val + 1 →
      value2 x i i' j j' ≤ value2 x i i' j' j''

/-- The 2 X 2 subblock values are nondecreasing vertically. -/
def Vertical2 {m : ℕ} (x : Fin m → Fin 4 → Fin 2) : Prop :=
  ∀ i i' i'' : Fin m, i'.val = i.val + 1 → i''.val = i'.val + 1 →
    ∀ j j' : Fin 4, j'.val = j.val + 1 →
      value2 x i i' j j' ≤ value2 x i' i'' j j'

/-- The 3 X 3 subblock values are nondecreasing horizontally. -/
def Horizontal3 {m : ℕ} (x : Fin m → Fin 4 → Fin 2) : Prop :=
  ∀ i i' i'' : Fin m, i'.val = i.val + 1 → i''.val = i'.val + 1 →
    ∀ j j' j'' j''' : Fin 4, j'.val = j.val + 1 → j''.val = j'.val + 1 → j'''.val = j''.val + 1 →
      value3 x i i' i'' j j' j'' ≤ value3 x i i' i'' j' j'' j'''

/-- Between the 3 X 3 subblocks with rows i, i', i'' and rows i', i'', i''', the values are
nondecreasing vertically. -/
def Vertical3At {m : ℕ} (x : Fin m → Fin 4 → Fin 2) (i i' i'' i''' : Fin m) : Prop :=
  ∀ j j' j'' : Fin 4, j'.val = j.val + 1 → j''.val = j'.val + 1 →
    value3 x i i' i'' j j' j'' ≤ value3 x i' i'' i''' j j' j''

instance {m : ℕ} (x : Fin m → Fin 4 → Fin 2) (i i' i'' i''' : Fin m) :
    Decidable (Vertical3At x i i' i'' i''') := by
  unfold Vertical3At; infer_instance

/-- The 3 X 3 subblock values are nondecreasing vertically. -/
def Vertical3 {m : ℕ} (x : Fin m → Fin 4 → Fin 2) : Prop :=
  ∀ i i' i'' i''' : Fin m, i'.val = i.val + 1 → i''.val = i'.val + 1 → i'''.val = i''.val + 1 →
    Vertical3At x i i' i'' i'''

instance {m : ℕ} (x : Fin m → Fin 4 → Fin 2) : Decidable (Horizontal2 x) := by
  unfold Horizontal2; infer_instance

instance {m : ℕ} (x : Fin m → Fin 4 → Fin 2) : Decidable (Vertical2 x) := by
  unfold Vertical2; infer_instance

instance {m : ℕ} (x : Fin m → Fin 4 → Fin 2) : Decidable (Horizontal3 x) := by
  unfold Horizontal3; infer_instance

instance {m : ℕ} (x : Fin m → Fin 4 → Fin 2) : Decidable (Vertical3 x) := by
  unfold Vertical3; infer_instance

/-- A253504(n): the number of (n+2) X 4 arrays with entries 0..1 whose 2 X 2 and 3 X 3 subblock
values (diagonal maximum minus antidiagonal minimum) are nondecreasing horizontally and
vertically. -/
def a (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin (n + 2) → Fin 4 → Fin 2)).filter (fun x =>
    Horizontal2 x ∧ Vertical2 x ∧ Horizontal3 x ∧ Vertical3 x)).card

/-- Barker's conjectures: the g.f. and the recurrence for n > 6. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * ((1 - X) ^ 4) =
        4 * X * (65 - 142 * X + 114 * X ^ 2 - 37 * X ^ 3 + X ^ 4 + X ^ 5) ∧
      ∀ n : ℕ, 6 < n →
        (a n : ℚ) = 4 * a (n - 1) - 6 * a (n - 2) + 4 * a (n - 3) - a (n - 4) := by
  sorry

end OMA.S_oeis_a253504
