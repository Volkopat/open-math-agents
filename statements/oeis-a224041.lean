import Mathlib

/-!
# A224041: Number of 5 X n 0..1 arrays with antidiagonals unimodal and rows and diagonals nondecreasing.

Source: https://oeis.org/A224041

The formulas listed in the entry, stated below as one conjunction:
* Empirical: a(n) = (1/120)*n^5 + (1/24)*n^4 + (25/24)*n^3 + (227/24)*n^2 + (1289/20)*n - 7 for n>3.
* Conjectures from Colin Barker, Aug 26 2018:
  G.f.: x*(32 - 48*x - 86*x^2 + 220*x^3 - 124*x^4 - 12*x^5 + 9*x^6 + 17*x^7 - 7*x^8) / (1 - x)^6.
  a(n) = 6*a(n-1) - 15*a(n-2) + 20*a(n-3) - 15*a(n-4) + 6*a(n-5) - a(n-6) for n>9.

Conventions. Offset 1: a(n) counts the arrays `x : Fin 5 → Fin n → Fin 2` (5 rows, n columns,
entries 0..1, `x i j` in row `i` and column `j`) such that
* every row is nondecreasing: `x i j ≤ x i (j+1)`;
* every diagonal (direction down-right) is nondecreasing: `x i j ≤ x (i+1) (j+1)`;
* every antidiagonal (the cells with a fixed `i + j`) is unimodal. A finite sequence is unimodal
  when it is weakly increasing up to some position and weakly decreasing after it; equivalently
  no entry is strictly smaller than both an earlier and a later entry (this form, which does not
  depend on the direction of reading, is used below).
The closed form is stated for n > 3, the recurrence for n > 9, and the g.f. as an identity
of formal power series over the rationals for the series `Sum_{n >= 1} a(n) x^n` (coefficient 0
set to 0), with the denominator multiplied out. The definition reproduces the listed terms
32, 144, 298, 488, 734, ...; all three formulas were checked against it for every n <= 30.
-/

namespace OMA.S_oeis_a224041

/-- The conditions on a `5 × n` array over `0..1`. -/
def Good {n : ℕ} (x : Fin 5 → Fin n → Fin 2) : Prop :=
  (∀ i : Fin 5, ∀ j j' : Fin n, j'.val = j.val + 1 → x i j ≤ x i j') ∧
  (∀ i i' : Fin 5, ∀ j j' : Fin n, i'.val = i.val + 1 → j'.val = j.val + 1 → x i j ≤ x i' j') ∧
  (∀ i₁ i₂ i₃ : Fin 5, ∀ j₁ j₂ j₃ : Fin n, i₁ < i₂ → i₂ < i₃ → i₁.val + j₁.val = i₂.val + j₂.val →
    i₂.val + j₂.val = i₃.val + j₃.val → ¬ (x i₂ j₂ < x i₁ j₁ ∧ x i₂ j₂ < x i₃ j₃))

instance {n : ℕ} (x : Fin 5 → Fin n → Fin 2) : Decidable (Good x) := by
  unfold Good; infer_instance

/-- A224041(n): the number of such arrays with `n` columns. -/
def a (n : ℕ) : ℕ := ((Finset.univ : Finset (Fin 5 → Fin n → Fin 2)).filter Good).card

open PowerSeries in
theorem main :
    (∀ n : ℕ, 3 < n → (a n : ℚ) = 1 / 120 * n ^ 5 + 1 / 24 * n ^ 4 + 25 / 24 * n ^ 3 + 227 / 24 * n ^ 2 + 1289 / 20 * n - 7) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 6 =
      X * (32 - 48 * X - 86 * X ^ 2 + 220 * X ^ 3 - 124 * X ^ 4 - 12 * X ^ 5 + 9 * X ^ 6 + 17 * X ^ 7 - 7 * X ^ 8) ∧
    (∀ n : ℕ, 9 < n → (a n : ℤ) = 6 * a (n - 1) - 15 * a (n - 2) + 20 * a (n - 3) - 15 * a (n - 4) + 6 * a (n - 5) - a (n - 6)) := by
  sorry

end OMA.S_oeis_a224041
