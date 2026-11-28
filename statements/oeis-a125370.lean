import Mathlib

/-!
# A125370: Number of base 7 circular n-digit numbers with adjacent digits differing by 5 or less.

Source: https://oeis.org/A125370
Credit: @Dariusthedoggie

OEIS Foundation and contributors, CC BY-SA 4.0. Retrieved 2026-11-27.
Offset 0 (data 1, 7, 47, 307, 2067, 13927, ...).

Conventions:
* A base 7 circular n-digit number (with leading zeros allowed, matching `a 0 = 1`, `a 1 = 7`,
  `a 2 = 47`) is a word `w : Fin n → Fin 7`.
* Circular adjacency requires that for every `i : Fin n`, `w i` and `w ((i + 1) % n)` differ
  by at most 5, expressed as `((w i : ℤ) - (w ((i + 1) % n) : ℤ)).natAbs ≤ 5`.
* At `n = 0`, the unique empty word vacuously satisfies the condition, giving `a 0 = 1`.
  At `n = 1`, `w 0` is adjacent to itself with difference `0 ≤ 5`, giving `a 1 = 7`.

Conjectures (Colin Barker, Jun 02 2017):
G.f.: (1 - x^2 - 10*x^3) / ((1 - x)*(1 - 6*x - 5*x^2)).
a(n) = 1 + (3-sqrt(14))^n + (3+sqrt(14))^n for n>0.
a(n) = 7*a(n-1) - a(n-2) - 5*a(n-3) for n>3.
The generating function is stated after multiplication by its denominator, whose constant
term is one.
-/

namespace OMA.S_oeis_a125370

open PowerSeries

/-- Two base-7 digits differ by at most 5. -/
def adjOk (x y : Fin 7) : Prop :=
  ((x : ℤ) - (y : ℤ)).natAbs ≤ 5

instance (x y : Fin 7) : Decidable (adjOk x y) :=
  inferInstanceAs (Decidable (_ ≤ _))

/-- A circular word of length `n` over `Fin 7` has all circularly adjacent digits differing
by at most 5. -/
def isValid (n : ℕ) (w : Fin n → Fin 7) : Prop :=
  ∀ i : Fin n, adjOk (w i) (w ⟨(i.val + 1) % n, Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩)

instance (n : ℕ) (w : Fin n → Fin 7) : Decidable (isValid n w) :=
  inferInstanceAs (Decidable (∀ _, _))

/-- A125370: the number of base 7 circular n-digit numbers with adjacent digits differing
by 5 or less. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (isValid n)).card

theorem main :
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) * (1 - 6 * X - 5 * X ^ 2)) =
      1 - X ^ 2 - 10 * X ^ 3) ∧
    (∀ n : ℕ, 1 ≤ n → (a n : ℝ) = 1 + (3 - Real.sqrt 14) ^ n + (3 + Real.sqrt 14) ^ n) ∧
    (∀ n : ℕ, 4 ≤ n → (a n : ℤ) = 7 * a (n - 1) - a (n - 2) - 5 * a (n - 3)) := by
  sorry

end OMA.S_oeis_a125370
