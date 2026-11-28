import Mathlib

/-!
# Every decimal digit-power orbit eventually repeats (OEIS A182160)

Michel Lagneau's generalization fixes a positive integer exponent and allows
the starting value to vary independently. Two equal iterates at distinct
times mark a repetition, including a fixed point as a cycle of length one.

Source: https://oeis.org/A182160 (OEIS Foundation, CC BY-SA 4.0).
Credit: @chuyeow
-/

namespace OMA.S_oeis_a182160

/-- Sum the fixed exponent's powers of the decimal digits of the current value. -/
def digitPowerSum (exponent value : ℕ) : ℕ :=
  ((Nat.digits 10 value).map (fun digit => digit ^ exponent)).sum

theorem main : ∀ exponent : ℕ, 0 < exponent → ∀ start : ℕ,
    ∃ i j : ℕ, i < j ∧ (digitPowerSum exponent)^[i] start =
      (digitPowerSum exponent)^[j] start := by
  sorry

end OMA.S_oeis_a182160
