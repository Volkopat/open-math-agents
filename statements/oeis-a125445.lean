import Mathlib

/-!
# A125445: Number of base 10 circular n-digit numbers with adjacent digits differing by 8 or less.

Source: https://oeis.org/A125445
Credit: @Dariusthedoggie

OEIS Foundation and contributors, CC BY-SA 4.0. Retrieved 2026-11-27.
Offset 0 (data 1, 10, 98, 946, 9282, 91090, ...).

Conventions:
* A base 10 circular n-digit number (with leading zeros allowed, matching `a 0 = 1`, `a 1 = 10`,
  `a 2 = 98`) is a word `w : Fin n → Fin 10`.
* Circular adjacency requires that for every `i : Fin n`, `w i` and `w ((i + 1) % n)` differ
  by at most 8, expressed as `((w i : ℤ) - (w ((i + 1) % n) : ℤ)).natAbs ≤ 8`.
* At `n = 0`, the unique empty word vacuously satisfies the condition, giving `a 0 = 1`.
  At `n = 1`, `w 0` is adjacent to itself with difference `0 ≤ 8`, giving `a 1 = 10`.

Conjectures (Colin Barker, Jun 01 2017):
G.f.: (1 - x^2 - 16*x^3) / ((1 - x)*(1 - 9*x - 8*x^2)).
a(n) = 1 + ((9-sqrt(113))/2)^n + ((9+sqrt(113))/2)^n for n>0.
a(n) = 10*a(n-1) - a(n-2) - 8*a(n-3) for n>3.
The generating function is stated after multiplication by its denominator, whose constant
term is one.
-/

namespace OMA.S_oeis_a125445

open PowerSeries

/-- Two base-10 digits differ by at most 8. -/
def adjOk (x y : Fin 10) : Prop :=
  ((x : ℤ) - (y : ℤ)).natAbs ≤ 8

instance (x y : Fin 10) : Decidable (adjOk x y) :=
  inferInstanceAs (Decidable (_ ≤ _))

/-- A circular word of length `n` over `Fin 10` has all circularly adjacent digits differing
by at most 8. -/
def isValid (n : ℕ) (w : Fin n → Fin 10) : Prop :=
  ∀ i : Fin n, adjOk (w i) (w ⟨(i.val + 1) % n, Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩)

instance (n : ℕ) (w : Fin n → Fin 10) : Decidable (isValid n w) :=
  inferInstanceAs (Decidable (∀ _, _))

/-- A125445: the number of base 10 circular n-digit numbers with adjacent digits differing
by 8 or less. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (isValid n)).card

theorem main :
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) * (1 - 9 * X - 8 * X ^ 2)) =
      1 - X ^ 2 - 16 * X ^ 3) ∧
    (∀ n : ℕ, 1 ≤ n → (a n : ℝ) = 1 + ((9 - Real.sqrt 113) / 2) ^ n + ((9 + Real.sqrt 113) / 2) ^ n) ∧
    (∀ n : ℕ, 4 ≤ n → (a n : ℤ) = 10 * a (n - 1) - a (n - 2) - 8 * a (n - 3)) := by
  sorry

end OMA.S_oeis_a125445
