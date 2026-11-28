import Mathlib

/-!
# A224832: Numbers k such that the sum of reciprocals of even divisors of k is an integer.

Source: https://oeis.org/A224832
Credit: @esracummings31-blip

Conjecture (OEIS): if a(n) is a non-twice even perfect number, the sum of reciprocals of
even divisors equals 2.

Conventions.
* `recipEven k = ∑_{d ∣ k, d even} 1/d` (in `ℚ`).
* Terms of the sequence are the positive even `k` with `recipEven k` an integer. (For odd `k`
  the sum is empty; the listed terms 12, 56, 992, ... are all even, so the empty-sum case is
  not part of the sequence.)
* "twice even perfect number": `k = 2 * P` with `P` an even perfect number (A139256).

The statement below records that the conjecture is false (`main : ¬ Conjecture`); the
conjecture itself is the `Prop` `Conjecture`, transcribed from the OEIS comment.
-/

namespace OMA.S_oeis_a224832

/-- Sum of reciprocals of the even divisors of `k`. -/
def recipEven (k : ℕ) : ℚ := ∑ d ∈ k.divisors.filter Even, (1 : ℚ) / d

/-- `k` is a term of A224832. -/
def InSeq (k : ℕ) : Prop := 0 < k ∧ Even k ∧ ∃ z : ℤ, recipEven k = z

/-- `k` is twice an even perfect number (A139256). -/
def TwiceEvenPerfect (k : ℕ) : Prop := ∃ P : ℕ, Even P ∧ Nat.Perfect P ∧ k = 2 * P

/-- The OEIS conjecture. -/
def Conjecture : Prop := ∀ k : ℕ, InSeq k → ¬ TwiceEvenPerfect k → recipEven k = 2

theorem main : ¬ Conjecture := by
  sorry

end OMA.S_oeis_a224832
