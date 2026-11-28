import Mathlib

/-!
# A393460: least prime `p` such that `n - p` is the reverse of a prime

Source: https://oeis.org/A393460
Credit: @Lenqth

A393460(n) (offset 4) is the least prime `p` such that `n - p` is the reverse of a prime, where
leading zeros are not allowed, or `-1` if there is no such `p`. Following the programs in the
entry, this means: `p < n`, the difference `d = n - p` does not end in the digit `0` (otherwise its
reversal would have a leading zero), and the number obtained by reversing the decimal digits of
`d` is prime. For example `a(15) = 2`, since `15 - 2 = 13` is the reverse of the prime `31`.

Formalizes the conjecture in the comments of A393460: `a(n) = -1` only for `n = 11`, i.e. among
the `n ≥ 4`, the only one with no such prime `p` is `11`.
-/

namespace OMA.S_oeis_a393460

/-- The number whose decimal digits are those of `d` in reverse order. -/
def reverseDigits (d : ℕ) : ℕ := Nat.ofDigits 10 (Nat.digits 10 d).reverse

/-- `p` witnesses A393460(n) ≠ -1: `p` is a prime below `n`, `n - p` does not end in `0`, and
the reversal of `n - p` is prime. -/
def IsWitness (n p : ℕ) : Prop :=
  p.Prime ∧ p < n ∧ (n - p) % 10 ≠ 0 ∧ (reverseDigits (n - p)).Prime

/-- Among the `n ≥ 4`, the only one without a witness is `11`. -/
theorem main : {n : ℕ | 4 ≤ n ∧ ¬ ∃ p, IsWitness n p} = {11} := by
  sorry

end OMA.S_oeis_a393460
