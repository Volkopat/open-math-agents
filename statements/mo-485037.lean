import Mathlib

/-!
# Perfect powers as products of two Fibonacci or Lucas numbers

Source: https://mathoverflow.net/questions/485037
Formalization: @llostinthesauce
-/

namespace OMA.S_mo_485037

def lucas : ℕ → ℕ
  | 0 => 2
  | 1 => 1
  | n + 2 => lucas (n + 1) + lucas n

def IsPerfectPower (x : ℕ) : Prop :=
  ∃ k e : ℕ, 2 ≤ k ∧ 2 ≤ e ∧ x = k ^ e

/-- The conjecture lists the possible product values. The ranges of the two
indices are part of the definition of each set. -/
theorem main :
    {x : ℕ | IsPerfectPower x ∧
      ∃ m n : ℕ, 2 < m ∧ m < n ∧ x = Nat.fib m * Nat.fib n} = {2 ^ 4} ∧
    {x : ℕ | IsPerfectPower x ∧
      ∃ m n : ℕ, m < n ∧ x = lucas m * lucas n} = {2 ^ 3, 6 ^ 2, 2 ^ 2} := by
  sorry

end OMA.S_mo_485037
