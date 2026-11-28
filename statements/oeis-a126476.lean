import Mathlib

/-!
# A126476: Number of base 8 n-digit numbers with adjacent digits differing by three or less

Source: https://oeis.org/A126476
Credit: @Dariusthedoggie

OEIS Foundation and contributors, CC BY-SA 4.0. Retrieved 2026-11-27.
Offset 0 (data 1, 8, 44, 252, 1446, 8300, ...).

Conventions:
* An n-digit base 8 number is a word `x : Fin n → Fin 8` of digits `0..7`; leading zeros are
  allowed, as the data `a(1) = 8` shows. For `n = 0` there is exactly one (empty) word.
* Adjacent digits are `x i` and `x j` with `j = i + 1`.
* Differing by three or less: `x i ≤ x j + 3` and `x j ≤ x i + 3` as natural numbers.
* The generating function is stated after multiplication by its denominator, whose constant
  term is one.
* The numerator and denominator of the g.f. are expanded (and both negated if needed)
  so that the denominator has constant term one.

Conjectures from Colin Barker, as stated in the formula section:
Conjectures from Colin Barker, Jun 01 2017: (Start)
G.f.: (1 - x)*(1 + 3*x - x^3) / (1 - 6*x + x^2 + 3*x^3 - x^4).
a(n) = 6*a(n-1) - a(n-2) - 3*a(n-3) + a(n-4) for n>4.
(End)
-/

namespace OMA.S_oeis_a126476

open PowerSeries

/-- Two digits differ by three or less. -/
def close (d e : Fin 8) : Prop := (d : ℕ) ≤ (e : ℕ) + 3 ∧ (e : ℕ) ≤ (d : ℕ) + 3

instance (d e : Fin 8) : Decidable (close d e) := by
  unfold close
  infer_instance

/-- A126476: the number of words of length `n` over the digits `0..7` in which adjacent digits
differ by three or less. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun x : Fin n → Fin 8 =>
    ∀ i j : Fin n, (j : ℕ) = (i : ℕ) + 1 → close (x i) (x j))).card

theorem main :
    (PowerSeries.mk (fun n => (a n : ℚ)) * (1 - 6 * X + X ^ 2 + 3 * X ^ 3 - X ^ 4) =
      1 + 2 * X - 3 * X ^ 2 - X ^ 3 + X ^ 4) ∧
    (∀ n : ℕ, 4 < n → (a n : ℤ) = 6 * a (n - 1) - a (n - 2) - 3 * a (n - 3) + a (n - 4)) := by
  sorry

end OMA.S_oeis_a126476
