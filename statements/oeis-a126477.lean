import Mathlib

/-!
# A126477: Number of base 9 n-digit numbers with adjacent digits differing by three or less

Source: https://oeis.org/A126477
Credit: @Dariusthedoggie

OEIS Foundation and contributors, CC BY-SA 4.0. Retrieved 2026-11-27.
Offset 0 (data 1, 9, 51, 301, 1787, 10619, ...).

Conventions:
* An n-digit base 9 number is a word `x : Fin n → Fin 9` of digits `0..8`; leading zeros are
  allowed, as the data `a(1) = 9` shows. For `n = 0` there is exactly one (empty) word.
* Adjacent digits are `x i` and `x j` with `j = i + 1`.
* Differing by three or less: `x i ≤ x j + 3` and `x j ≤ x i + 3` as natural numbers.
* The generating function is stated after multiplication by its denominator, whose constant
  term is one.
* The numerator and denominator of the g.f. are expanded (and both negated if needed)
  so that the denominator has constant term one.

Conjectures from Colin Barker, as stated in the formula section:
Conjectures from Colin Barker, Jun 01 2017: (Start)
G.f.: (1 + 2*x - 6*x^2 + 2*x^4) / ((1 - x)*(1 - 6*x + 2*x^3)).
a(n) = 7*a(n-1) - 6*a(n-2) - 2*a(n-3) + 2*a(n-4) for n>4.
(End)
-/

namespace OMA.S_oeis_a126477

open PowerSeries

/-- Two digits differ by three or less. -/
def close (d e : Fin 9) : Prop := (d : ℕ) ≤ (e : ℕ) + 3 ∧ (e : ℕ) ≤ (d : ℕ) + 3

instance (d e : Fin 9) : Decidable (close d e) := by
  unfold close
  infer_instance

/-- A126477: the number of words of length `n` over the digits `0..8` in which adjacent digits
differ by three or less. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun x : Fin n → Fin 9 =>
    ∀ i j : Fin n, (j : ℕ) = (i : ℕ) + 1 → close (x i) (x j))).card

theorem main :
    (PowerSeries.mk (fun n => (a n : ℚ)) * (1 - 7 * X + 6 * X ^ 2 + 2 * X ^ 3 - 2 * X ^ 4) =
      1 + 2 * X - 6 * X ^ 2 + 2 * X ^ 4) ∧
    (∀ n : ℕ, 4 < n → (a n : ℤ) = 7 * a (n - 1) - 6 * a (n - 2) - 2 * a (n - 3) + 2 * a (n - 4)) := by
  sorry

end OMA.S_oeis_a126477
