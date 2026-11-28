import Mathlib

/-!
# A124999: Number of base 5 circular n-digit numbers with adjacent digits differing by 3 or less.

Source: https://oeis.org/A124999
Credit: @Dariusthedoggie

OEIS Foundation and contributors, CC BY-SA 4.0. Retrieved 2026-11-27.
Offset 0 (data 1, 5, 23, 101, 467, 2165, ...).

Conventions:
* A base 5 circular n-digit number (with leading zeros allowed, matching `a 0 = 1`, `a 1 = 5`,
  `a 2 = 23`) is a word `w : Fin n → Fin 5`.
* Circular adjacency requires that for every `i : Fin n`, `w i` and `w ((i + 1) % n)` differ
  by at most 3, expressed as `((w i : ℤ) - (w ((i + 1) % n) : ℤ)).natAbs ≤ 3`.
* At `n = 0`, the unique empty word vacuously satisfies the condition, giving `a 0 = 1`.
  At `n = 1`, `w 0` is adjacent to itself with difference `0 ≤ 3`, giving `a 1 = 5`.

Conjectures (Colin Barker, Jun 02 2017):
G.f.: (1 - 2*x)*(1 + 2*x + 3*x^2) / ((1 - x)*(1 - 4*x - 3*x^2)).
a(n) = 1 + (2-sqrt(7))^n + (2+sqrt(7))^n for n>0.
a(n) = 5*a(n-1) - a(n-2) - 3*a(n-3) for n>3.
The generating function is stated after multiplication by its denominator, whose constant
term is one.
-/

namespace OMA.S_oeis_a124999

open PowerSeries

/-- Two base-5 digits differ by at most 3. -/
def adjOk (x y : Fin 5) : Prop :=
  ((x : ℤ) - (y : ℤ)).natAbs ≤ 3

instance (x y : Fin 5) : Decidable (adjOk x y) :=
  inferInstanceAs (Decidable (_ ≤ _))

/-- A circular word of length `n` over `Fin 5` has all circularly adjacent digits differing
by at most 3. -/
def isValid (n : ℕ) (w : Fin n → Fin 5) : Prop :=
  ∀ i : Fin n, adjOk (w i) (w ⟨(i.val + 1) % n, Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩)

instance (n : ℕ) (w : Fin n → Fin 5) : Decidable (isValid n w) :=
  inferInstanceAs (Decidable (∀ _, _))

/-- A124999: the number of base 5 circular n-digit numbers with adjacent digits differing
by 3 or less. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (isValid n)).card

theorem main :
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) * (1 - 4 * X - 3 * X ^ 2)) =
      (1 - 2 * X) * (1 + 2 * X + 3 * X ^ 2)) ∧
    (∀ n : ℕ, 1 ≤ n → (a n : ℝ) = 1 + (2 - Real.sqrt 7) ^ n + (2 + Real.sqrt 7) ^ n) ∧
    (∀ n : ℕ, 4 ≤ n → (a n : ℤ) = 5 * a (n - 1) - a (n - 2) - 3 * a (n - 3)) := by
  sorry

end OMA.S_oeis_a124999
