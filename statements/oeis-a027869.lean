import Mathlib

/-!
# A027869: Number of 0's in the decimal expansion of n!

Source: https://oeis.org/A027869
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Conjecture:
  a(n) ~ (9 * A027868(n) + A034886(n)) / 10  as n -> ∞,
where a(n) is the number of 0's in the base-10 representation of n!, A027868(n) is the number
of trailing 0's of n! (equal to v_5(n!)), and A034886(n) is the total number of base-10 digits
of n!.
-/

namespace OMA.S_oeis_a027869

open Filter

/-- Number of decimal 0 digits in n!. -/
def zeroCount (n : ℕ) : ℕ :=
  (Nat.digits 10 (Nat.factorial n)).count 0

/-- Number of trailing zeros in n! (equals v_5(n!)). -/
def trailingZeros (n : ℕ) : ℕ :=
  (Nat.factorial n).factorization 5

/-- Total number of decimal digits in n!. -/
def totalDigits (n : ℕ) : ℕ :=
  (Nat.digits 10 (Nat.factorial n)).length

/-- Conjecture: zeroCount(n) ~ (9 * trailingZeros(n) + totalDigits(n)) / 10. -/
theorem main :
    Tendsto
      (fun n : ℕ =>
        (zeroCount n : ℝ) / ((9 * (trailingZeros n : ℝ) + (totalDigits n : ℝ)) / 10))
      atTop (nhds 1) := by
  sorry

end OMA.S_oeis_a027869
