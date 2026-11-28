import Mathlib

/-!
# OEIS A082935: palindromes beginning with n whose digit sum reaches n

Meenakshi Srikanth's sequence takes the smallest palindrome m which begins
with the decimal expansion of n and whose iterated sum of digits equals n
at some stage k >= 1 (the term is zero by convention when no such m
exists). Positional digits in Mathlib are little-endian, so the
begins-with condition checks the low digits of m.

Conjecture (unsigned comment on the OEIS entry, checked to n = 100 by
Robert G. Wilson v): in all cases except n = 19 the digit sum in the
first round itself is n; for n = 19 the first round of digit sum is 199
and the second round digit sum is 19.

Source: https://oeis.org/A082935
-/

namespace OMA.S_oeis_a082935

/-- Base-10 digit sum. -/
def sigma10' (m : ℕ) : ℕ := (Nat.digits 10 m).sum

/-- `m` begins with `n` in decimal: the little-endian digits of `n` are a
suffix of those of `m`. -/
def beginsWith10 (n m : ℕ) : Prop :=
  Nat.digits 10 n <:+ Nat.digits 10 m

/-- `m` is a decimal palindrome. -/
def isPalindrome10 (m : ℕ) : Prop :=
  List.Palindrome (Nat.digits 10 m)

/-- The digit-sum iteration of `m` reaches `n` at some stage `k >= 1`. -/
def reachesDigitSum (n m : ℕ) : Prop :=
  ∃ k : ℕ, 1 ≤ k ∧ sigma10'^[k] m = n

/-- OEIS A082935 (sInf of the empty set is 0 by convention). -/
noncomputable def a082935 (n : ℕ) : ℕ :=
  sInf {m : ℕ | isPalindrome10 m ∧ beginsWith10 n m ∧ reachesDigitSum n m}

/-- The OEIS conjecture: the first-round digit sum of `a082935 n` equals
`n` for every `n >= 1` different from 19; at `n = 19` the first round is
199 and the second round is 19. -/
theorem main :
    (∀ n : ℕ, 1 ≤ n → n ≠ 19 → sigma10' (a082935 n) = n) ∧
    sigma10' (a082935 19) = 199 ∧
    sigma10'^[2] (a082935 19) = 19 := by
  sorry

end OMA.S_oeis_a082935
