import Mathlib

/-!
# A071234: Existence of primes beginning and ending in the decimal digits of 2n+1

Source: https://oeis.org/A071234
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Title: A071234: Smallest prime beginning and ending in 2n+1 or 0 if no such prime exists.

Statement:
Conjecture: a(n) = 0 if and only if n > 2 and n == 2 (mod 5) (which makes 2*n+1 == 0 mod 5).

Conventions:
- A natural number `p` begins and ends in `m` in base 10 if `(Nat.digits 10 m).reverse` is
  both a prefix and a suffix of `(Nat.digits 10 p).reverse` (the most-significant-first
  decimal digit list of `p`).
-/

namespace OMA.S_oeis_a071234

/-- Base-10 digits of `m` in most-significant-digit-first order. -/
def msbDigits (m : ℕ) : List ℕ :=
  (Nat.digits 10 m).reverse

/-- `p` begins and ends with the decimal representation of `m`. -/
def BeginsAndEndsWith (p m : ℕ) : Prop :=
  (msbDigits m).IsPrefix (msbDigits p) ∧ (msbDigits m).IsSuffix (msbDigits p)

theorem main :
    ∀ n : ℕ,
      (¬ ∃ p : ℕ, Nat.Prime p ∧ BeginsAndEndsWith p (2 * n + 1)) ↔
        (2 < n ∧ n % 5 = 2) := by
  sorry

end OMA.S_oeis_a071234
