import Mathlib

/-!
# A083178: Numbers with a digit sum of n and a maximum product of digits.

Source: https://oeis.org/A083178
Credit: @esracummings31-blip

Numbers with a digit sum of n and a maximum product of digits. In case of two identical products
choose the largest number. Offset 1: a(1), a(2), ... = 1, 2, 3, 22, 32, 33, 322, 332, 333, ...

Conjecture (Colin Barker, Oct 14 2014): a(n) = 10*a(n-3) + a(n-6) - 10*a(n-9) for n > 10.
-/

namespace OMA.S_oeis_a083178

/-- Sum of the decimal digits of `m`. -/
def digitSum (m : ℕ) : ℕ := (Nat.digits 10 m).sum

/-- Product of the decimal digits of `m`. -/
def digitProd (m : ℕ) : ℕ := (Nat.digits 10 m).prod

/-- `m` has digit sum `n`, and no number with digit sum `n` has a larger product of digits. -/
def IsMaxProd (n m : ℕ) : Prop :=
  digitSum m = n ∧ ∀ m' : ℕ, digitSum m' = n → digitProd m' ≤ digitProd m

/-- A083178(n): the largest number with digit sum `n` and maximum product of digits. -/
noncomputable def a (n : ℕ) : ℕ := sSup {m : ℕ | IsMaxProd n m}

/-- Colin Barker's conjectured recurrence. -/
theorem main : ∀ n : ℕ, 10 < n →
    (a n : ℤ) = 10 * (a (n - 3) : ℤ) + (a (n - 6) : ℤ) - 10 * (a (n - 9) : ℤ) := by
  sorry

end OMA.S_oeis_a083178
