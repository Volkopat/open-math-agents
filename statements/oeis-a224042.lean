import Mathlib

/-!
# A224042: Number of 6 X n 0..1 arrays with antidiagonals unimodal and rows and diagonals nondecreasing.

Source: https://oeis.org/A224042

The formulas listed in the entry, stated below as one conjunction:
* Empirical: a(n) = (1/720)*n^6 + (1/240)*n^5 + (35/144)*n^4 + (127/48)*n^3 + (1249/45)*n^2 + (3727/20)*n + 6 for n>4.
* Conjectures from Colin Barker, Aug 26 2018:
  G.f.: x*(64 - 71*x - 447*x^2 + 1163*x^3 - 952*x^4 + 97*x^5 + 216*x^6 - 72*x^7 + 33*x^8 - 45*x^9 + 15*x^10) / (1 - x)^7.
  a(n) = 7*a(n-1) - 21*a(n-2) + 35*a(n-3) - 35*a(n-4) + 21*a(n-5) - 7*a(n-6) + a(n-7) for n>11.

Conventions. Offset 1: a(n) counts the arrays `x : Fin 6 → Fin n → Fin 2` (6 rows, n columns,
entries 0..1, `x i j` in row `i` and column `j`) such that
* every row is nondecreasing: `x i j ≤ x i (j+1)`;
* every diagonal (direction down-right) is nondecreasing: `x i j ≤ x (i+1) (j+1)`;
* every antidiagonal (the cells with a fixed `i + j`) is unimodal. A finite sequence is unimodal
  when it is weakly increasing up to some position and weakly decreasing after it; equivalently
  no entry is strictly smaller than both an earlier and a later entry (this form, which does not
  depend on the direction of reading, is used below).
The closed form is stated for n > 4, the recurrence for n > 11, and the g.f. as an identity
of formal power series over the rationals for the series `Sum_{n >= 1} a(n) x^n` (coefficient 0
set to 0), with the denominator multiplied out. The definition reproduces the listed terms
64, 377, 848, 1422, 2149, ...; all three formulas were checked against it for every n <= 30.
-/

namespace OMA.S_oeis_a224042

/-- The conditions on a `6 × n` array over `0..1`. -/
def Good {n : ℕ} (x : Fin 6 → Fin n → Fin 2) : Prop :=
  (∀ i : Fin 6, ∀ j j' : Fin n, j'.val = j.val + 1 → x i j ≤ x i j') ∧
  (∀ i i' : Fin 6, ∀ j j' : Fin n, i'.val = i.val + 1 → j'.val = j.val + 1 → x i j ≤ x i' j') ∧
  (∀ i₁ i₂ i₃ : Fin 6, ∀ j₁ j₂ j₃ : Fin n, i₁ < i₂ → i₂ < i₃ → i₁.val + j₁.val = i₂.val + j₂.val →
    i₂.val + j₂.val = i₃.val + j₃.val → ¬ (x i₂ j₂ < x i₁ j₁ ∧ x i₂ j₂ < x i₃ j₃))

instance {n : ℕ} (x : Fin 6 → Fin n → Fin 2) : Decidable (Good x) := by
  unfold Good; infer_instance

/-- A224042(n): the number of such arrays with `n` columns. -/
def a (n : ℕ) : ℕ := ((Finset.univ : Finset (Fin 6 → Fin n → Fin 2)).filter Good).card

open PowerSeries in
theorem main :
    (∀ n : ℕ, 4 < n → (a n : ℚ) = 1 / 720 * n ^ 6 + 1 / 240 * n ^ 5 + 35 / 144 * n ^ 4 + 127 / 48 * n ^ 3 + 1249 / 45 * n ^ 2 + 3727 / 20 * n + 6) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 7 =
      X * (64 - 71 * X - 447 * X ^ 2 + 1163 * X ^ 3 - 952 * X ^ 4 + 97 * X ^ 5 + 216 * X ^ 6 - 72 * X ^ 7 + 33 * X ^ 8 - 45 * X ^ 9 + 15 * X ^ 10) ∧
    (∀ n : ℕ, 11 < n → (a n : ℤ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4) + 21 * a (n - 5) - 7 * a (n - 6) + a (n - 7)) := by
  sorry

end OMA.S_oeis_a224042
