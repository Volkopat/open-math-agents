import Mathlib

/-!
# A126478: Number of base 10 n-digit numbers with adjacent digits differing by three or less

Source: https://oeis.org/A126478
Credit: @Dariusthedoggie

OEIS Foundation and contributors, CC BY-SA 4.0. Retrieved 2026-11-27.
Offset 0 (data 1, 10, 58, 350, 2130, 12990, ...).

Conventions:
* An n-digit base 10 number is a word `x : Fin n → Fin 10` of digits `0..9`; leading zeros are
  allowed, as the data `a(1) = 10` shows. For `n = 0` there is exactly one (empty) word.
* Adjacent digits are `x i` and `x j` with `j = i + 1`.
* Differing by three or less: `x i ≤ x j + 3` and `x j ≤ x i + 3` as natural numbers.
* The generating function is stated after multiplication by its denominator, whose constant
  term is one.

Conjectures from Colin Barker, as stated in the formula section:
Conjectures from Colin Barker, May 31 2017: (Start)
G.f.: (1 + 3*x - 8*x^2 - 6*x^3 + 6*x^4) / (1 - 7*x + 4*x^2 + 10*x^3 - 6*x^4).
a(n) = 7*a(n-1) - 4*a(n-2) - 10*a(n-3) + 6*a(n-4) for n>4.
(End)
-/

namespace OMA.S_oeis_a126478

open PowerSeries

/-- Two digits differ by three or less. -/
def close (d e : Fin 10) : Prop := (d : ℕ) ≤ (e : ℕ) + 3 ∧ (e : ℕ) ≤ (d : ℕ) + 3

instance (d e : Fin 10) : Decidable (close d e) := by
  unfold close
  infer_instance

/-- A126478: the number of words of length `n` over the digits `0..9` in which adjacent digits
differ by three or less. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun x : Fin n → Fin 10 =>
    ∀ i j : Fin n, (j : ℕ) = (i : ℕ) + 1 → close (x i) (x j))).card

theorem main :
    (PowerSeries.mk (fun n => (a n : ℚ)) * (1 - 7 * X + 4 * X ^ 2 + 10 * X ^ 3 - 6 * X ^ 4) =
      1 + 3 * X - 8 * X ^ 2 - 6 * X ^ 3 + 6 * X ^ 4) ∧
    (∀ n : ℕ, 4 < n → (a n : ℤ) = 7 * a (n - 1) - 4 * a (n - 2) - 10 * a (n - 3) + 6 * a (n - 4)) := by
  sorry

end OMA.S_oeis_a126478
