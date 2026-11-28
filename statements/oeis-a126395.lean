import Mathlib

/-!
# A126395: Number of base 8 n-digit numbers with adjacent digits differing by two or less

Source: https://oeis.org/A126395
Credit: @Dariusthedoggie

OEIS Foundation and contributors, CC BY-SA 4.0. Retrieved 2026-11-27.
Offset 0 (data 1, 8, 34, 150, 668, 2986, ...).

Conventions:
* An n-digit base 8 number is a word `x : Fin n → Fin 8` of digits `0..7`; leading zeros are
  allowed, as the data `a(1) = 8` shows. For `n = 0` there is exactly one (empty) word.
* Adjacent digits are `x i` and `x j` with `j = i + 1`.
* Differing by two or less: `x i ≤ x j + 2` and `x j ≤ x i + 2` as natural numbers.
* The generating function is stated after multiplication by its denominator, whose constant
  term is one.

Conjectures from Colin Barker, as stated in the formula section:
Conjectures from Colin Barker, Jun 01 2017: (Start)
G.f.: (1 + 3*x - 5*x^2 - 6*x^3) / (1 - 5*x + x^2 + 6*x^3).
a(n) = 5*a(n-1) - a(n-2) - 6*a(n-3) for n>3.
(End)
-/

namespace OMA.S_oeis_a126395

open PowerSeries

/-- Two digits differ by two or less. -/
def close (d e : Fin 8) : Prop := (d : ℕ) ≤ (e : ℕ) + 2 ∧ (e : ℕ) ≤ (d : ℕ) + 2

instance (d e : Fin 8) : Decidable (close d e) := by
  unfold close
  infer_instance

/-- A126395: the number of words of length `n` over the digits `0..7` in which adjacent digits
differ by two or less. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun x : Fin n → Fin 8 =>
    ∀ i j : Fin n, (j : ℕ) = (i : ℕ) + 1 → close (x i) (x j))).card

theorem main :
    (PowerSeries.mk (fun n => (a n : ℚ)) * (1 - 5 * X + X ^ 2 + 6 * X ^ 3) =
      1 + 3 * X - 5 * X ^ 2 - 6 * X ^ 3) ∧
    (∀ n : ℕ, 3 < n → (a n : ℤ) = 5 * a (n - 1) - a (n - 2) - 6 * a (n - 3)) := by
  sorry

end OMA.S_oeis_a126395
