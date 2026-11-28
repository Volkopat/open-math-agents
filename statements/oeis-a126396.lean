import Mathlib

/-!
# A126396: Number of base 9 n-digit numbers with adjacent digits differing by two or less

Source: https://oeis.org/A126396
Credit: @Dariusthedoggie

OEIS Foundation and contributors, CC BY-SA 4.0. Retrieved 2026-11-27.
Offset 0 (data 1, 9, 39, 175, 793, 3611, ...).

Conventions:
* An n-digit base 9 number is a word `x : Fin n → Fin 9` of digits `0..8`; leading zeros are
  allowed, as the data `a(1) = 9` shows. For `n = 0` there is exactly one (empty) word.
* Adjacent digits are `x i` and `x j` with `j = i + 1`.
* Differing by two or less: `x i ≤ x j + 2` and `x j ≤ x i + 2` as natural numbers.
* The generating function is stated after multiplication by its denominator, whose constant
  term is one.

Conjectures from Colin Barker, as stated in the formula section:
Conjectures from Colin Barker, Jun 01 2017: (Start)
G.f.: (1 + 3*x - 10*x^2 - 6*x^3 + 6*x^4 + 2*x^5) / (1 - 6*x + 5*x^2 + 8*x^3 - 4*x^4 - 2*x^5).
a(n) = 6*a(n-1) - 5*a(n-2) - 8*a(n-3) + 4*a(n-4) + 2*a(n-5) for n>5.
(End)
-/

namespace OMA.S_oeis_a126396

open PowerSeries

/-- Two digits differ by two or less. -/
def close (d e : Fin 9) : Prop := (d : ℕ) ≤ (e : ℕ) + 2 ∧ (e : ℕ) ≤ (d : ℕ) + 2

instance (d e : Fin 9) : Decidable (close d e) := by
  unfold close
  infer_instance

/-- A126396: the number of words of length `n` over the digits `0..8` in which adjacent digits
differ by two or less. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun x : Fin n → Fin 9 =>
    ∀ i j : Fin n, (j : ℕ) = (i : ℕ) + 1 → close (x i) (x j))).card

theorem main :
    (PowerSeries.mk (fun n => (a n : ℚ)) * (1 - 6 * X + 5 * X ^ 2 + 8 * X ^ 3 - 4 * X ^ 4 - 2 * X ^ 5) =
      1 + 3 * X - 10 * X ^ 2 - 6 * X ^ 3 + 6 * X ^ 4 + 2 * X ^ 5) ∧
    (∀ n : ℕ, 5 < n → (a n : ℤ) = 6 * a (n - 1) - 5 * a (n - 2) - 8 * a (n - 3) + 4 * a (n - 4) + 2 * a (n - 5)) := by
  sorry

end OMA.S_oeis_a126396
