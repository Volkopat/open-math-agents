import Mathlib

/-!
# A125421: Number of base 9 circular n-digit numbers with adjacent digits differing by 7 or less.

Source: https://oeis.org/A125421
Credit: @Dariusthedoggie

OEIS Foundation and contributors, CC BY-SA 4.0. Retrieved 2026-11-27.
Offset 0 (data 1, 9, 79, 681, 5987, 52649, ...).

Conventions:
* A base 9 circular n-digit number (with leading zeros allowed, matching `a 0 = 1`, `a 1 = 9`,
  `a 2 = 79`) is a word `w : Fin n → Fin 9`.
* Circular adjacency requires that for every `i : Fin n`, `w i` and `w ((i + 1) % n)` differ
  by at most 7, expressed as `((w i : ℤ) - (w ((i + 1) % n) : ℤ)).natAbs ≤ 7`.
* At `n = 0`, the unique empty word vacuously satisfies the condition, giving `a 0 = 1`.
  At `n = 1`, `w 0` is adjacent to itself with difference `0 ≤ 7`, giving `a 1 = 9`.

Conjectures (Colin Barker, Jun 02 2017):
G.f.: (1 - x^2 - 14*x^3) / ((1 - x)*(1 - 8*x - 7*x^2)).
a(n) = 1 + (4-sqrt(23))^n + (4+sqrt(23))^n for n>0.
a(n) = 9*a(n-1) - a(n-2) - 7*a(n-3) for n>3.
The generating function is stated after multiplication by its denominator, whose constant
term is one.
-/

namespace OMA.S_oeis_a125421

open PowerSeries

/-- Two base-9 digits differ by at most 7. -/
def adjOk (x y : Fin 9) : Prop :=
  ((x : ℤ) - (y : ℤ)).natAbs ≤ 7

instance (x y : Fin 9) : Decidable (adjOk x y) :=
  inferInstanceAs (Decidable (_ ≤ _))

/-- A circular word of length `n` over `Fin 9` has all circularly adjacent digits differing
by at most 7. -/
def isValid (n : ℕ) (w : Fin n → Fin 9) : Prop :=
  ∀ i : Fin n, adjOk (w i) (w ⟨(i.val + 1) % n, Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩)

instance (n : ℕ) (w : Fin n → Fin 9) : Decidable (isValid n w) :=
  inferInstanceAs (Decidable (∀ _, _))

/-- A125421: the number of base 9 circular n-digit numbers with adjacent digits differing
by 7 or less. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (isValid n)).card

theorem main :
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) * (1 - 8 * X - 7 * X ^ 2)) =
      1 - X ^ 2 - 14 * X ^ 3) ∧
    (∀ n : ℕ, 1 ≤ n → (a n : ℝ) = 1 + (4 - Real.sqrt 23) ^ n + (4 + Real.sqrt 23) ^ n) ∧
    (∀ n : ℕ, 4 ≤ n → (a n : ℤ) = 9 * a (n - 1) - a (n - 2) - 7 * a (n - 3)) := by
  sorry

end OMA.S_oeis_a125421
