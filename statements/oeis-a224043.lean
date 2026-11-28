import Mathlib

/-!
# A224043: Number of 7 X n 0..1 arrays with antidiagonals unimodal and rows and diagonals nondecreasing.

Source: https://oeis.org/A224043

The formulas listed in the entry, stated below as one conjunction:
* Empirical: a(n) = (1/5040)*n^7 + (17/360)*n^5 + (13/24)*n^4 + (5767/720)*n^3 + (1919/24)*n^2 + (37901/70)*n + 143 for n>5.
* Conjectures from Colin Barker, Aug 26 2018:
  G.f.: x*(128 - 37*x - 1893*x^2 + 5276*x^3 - 5539*x^4 + 1495*x^5 + 1526*x^6 - 1101*x^7 + 65*x^8 + 155*x^9 - 160*x^10 + 117*x^11 - 31*x^12) / (1 - x)^8.
  a(n) = 8*a(n-1) - 28*a(n-2) + 56*a(n-3) - 70*a(n-4) + 56*a(n-5) - 28*a(n-6) + 8*a(n-7) - a(n-8) for n>13.

Conventions. Offset 1: a(n) counts the arrays `x : Fin 7 → Fin n → Fin 2` (7 rows, n columns,
entries 0..1, `x i j` in row `i` and column `j`) such that
* every row is nondecreasing: `x i j ≤ x i (j+1)`;
* every diagonal (direction down-right) is nondecreasing: `x i j ≤ x (i+1) (j+1)`;
* every antidiagonal (the cells with a fixed `i + j`) is unimodal. A finite sequence is unimodal
  when it is weakly increasing up to some position and weakly decreasing after it; equivalently
  no entry is strictly smaller than both an earlier and a later entry (this form, which does not
  depend on the direction of reading, is used below).
The closed form is stated for n > 5, the recurrence for n > 13, and the g.f. as an identity
of formal power series over the rationals for the series `Sum_{n >= 1} a(n) x^n` (coefficient 0
set to 0), with the denominator multiplied out. The definition reproduces the listed terms
128, 987, 2419, 4160, 6321, ...; all three formulas were checked against it for every n <= 30.
-/

namespace OMA.S_oeis_a224043

/-- The conditions on a `7 × n` array over `0..1`. -/
def Good {n : ℕ} (x : Fin 7 → Fin n → Fin 2) : Prop :=
  (∀ i : Fin 7, ∀ j j' : Fin n, j'.val = j.val + 1 → x i j ≤ x i j') ∧
  (∀ i i' : Fin 7, ∀ j j' : Fin n, i'.val = i.val + 1 → j'.val = j.val + 1 → x i j ≤ x i' j') ∧
  (∀ i₁ i₂ i₃ : Fin 7, ∀ j₁ j₂ j₃ : Fin n, i₁ < i₂ → i₂ < i₃ → i₁.val + j₁.val = i₂.val + j₂.val →
    i₂.val + j₂.val = i₃.val + j₃.val → ¬ (x i₂ j₂ < x i₁ j₁ ∧ x i₂ j₂ < x i₃ j₃))

instance {n : ℕ} (x : Fin 7 → Fin n → Fin 2) : Decidable (Good x) := by
  unfold Good; infer_instance

/-- A224043(n): the number of such arrays with `n` columns. -/
def a (n : ℕ) : ℕ := ((Finset.univ : Finset (Fin 7 → Fin n → Fin 2)).filter Good).card

open PowerSeries in
theorem main :
    (∀ n : ℕ, 5 < n → (a n : ℚ) = 1 / 5040 * n ^ 7 + 17 / 360 * n ^ 5 + 13 / 24 * n ^ 4 + 5767 / 720 * n ^ 3 + 1919 / 24 * n ^ 2 + 37901 / 70 * n + 143) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 8 =
      X * (128 - 37 * X - 1893 * X ^ 2 + 5276 * X ^ 3 - 5539 * X ^ 4 + 1495 * X ^ 5 + 1526 * X ^ 6 - 1101 * X ^ 7 + 65 * X ^ 8 + 155 * X ^ 9 - 160 * X ^ 10 + 117 * X ^ 11 - 31 * X ^ 12) ∧
    (∀ n : ℕ, 13 < n → (a n : ℤ) = 8 * a (n - 1) - 28 * a (n - 2) + 56 * a (n - 3) - 70 * a (n - 4) + 56 * a (n - 5) - 28 * a (n - 6) + 8 * a (n - 7) - a (n - 8)) := by
  sorry

end OMA.S_oeis_a224043
