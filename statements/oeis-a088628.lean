import Mathlib

/-!
# A088628: Smallest prime using all the digits of first n numbers

Source: https://oeis.org/A088628
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Smallest prime using all the digits of first n numbers. If necessary, extra digits
can be used.
Conjecture: There exists a number k such that for all m > k, m not == 0 or 2 (mod 3),
a(m) does not use any extra digit.
-/

namespace OMA.S_oeis_a088628

/-- The multiset of base-10 digits of the integers 1, 2, ..., m. -/
def firstNumbersDigits (m : ℕ) : Multiset ℕ :=
  (Finset.Icc 1 m).sum (fun i => Multiset.ofList (Nat.digits 10 i))

theorem main :
    ∃ k : ℕ, ∀ m : ℕ, k < m → m % 3 = 1 →
      ∃ p : ℕ, Nat.Prime p ∧ Multiset.ofList (Nat.digits 10 p) = firstNumbersDigits m := by
  sorry

end OMA.S_oeis_a088628
