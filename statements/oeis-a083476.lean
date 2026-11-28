import Mathlib

/-!
# A083476: Positions of 0's in A083475.

Source: https://oeis.org/A083476
Credit: @gblacher2

Conjecture (comment in A083476): "Strong conjecture: There are only finitely many terms in this
sequence not divisible by 10."

A083475 (https://oeis.org/A083475), offset 1: "Consider the set of all the numbers n*k where
1 <= k <= n. Then a(n) = number of palindromic members of this set." Palindromes are in base 10,
as in the examples there (a(22) = 6: 22, 44, 66, 88, 242, 484). For a fixed `n ≥ 1` the numbers
`n*k`, `1 ≤ k ≤ n`, are distinct, so A083475(n) counts the `k ∈ [1, n]` with `n*k` a palindrome.

A083476 (offset 1) lists the `n ≥ 1` with A083475(n) = 0. The conjecture says that only finitely
many of them are not multiples of 10. (A083475 notes that a(10k) = 0, so every positive multiple
of 10 is a term.)
-/

namespace OMA.S_oeis_a083476

/-- `x` is a palindrome in base 10. -/
def palindrome (x : ℕ) : Prop := (Nat.digits 10 x).reverse = Nat.digits 10 x

instance : DecidablePred palindrome := fun x =>
  inferInstanceAs (Decidable ((Nat.digits 10 x).reverse = Nat.digits 10 x))

/-- A083475(n): the number of palindromes among `n*1, n*2, ..., n*n`. -/
def a083475 (n : ℕ) : ℕ := ((Finset.Icc 1 n).filter (fun k => palindrome (n * k))).card

/-- `n` is a term of A083476: `n ≥ 1` and A083475(n) = 0. -/
def IsA083476 (n : ℕ) : Prop := 1 ≤ n ∧ a083475 n = 0

/-- The conjecture: only finitely many terms of A083476 are not divisible by 10. -/
theorem main : {n : ℕ | IsA083476 n ∧ ¬ 10 ∣ n}.Finite := by
  sorry

end OMA.S_oeis_a083476
