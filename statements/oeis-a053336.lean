import Mathlib.Data.Nat.Digits.Defs

namespace OMA.S_oeis_a053336

/-- `IsA053336 n m` holds iff `m` has `n` base-10 digits, each equal to `5` or `6`,
and `2 ^ n` divides `m`. -/
def IsA053336 (n m : ℕ) : Prop :=
  (Nat.digits 10 m).length = n ∧ (∀ d ∈ Nat.digits 10 m, d = 5 ∨ d = 6) ∧ 2 ^ n ∣ m

/-- `IsA035014 n m` holds iff `m` has `n` base-10 digits, each equal to `3` or `4`,
and `2 ^ n` divides `m`. -/
def IsA035014 (n m : ℕ) : Prop :=
  (Nat.digits 10 m).length = n ∧ (∀ d ∈ Nat.digits 10 m, d = 3 ∨ d = 4) ∧ 2 ^ n ∣ m

/-- OEIS A053336 conjecture (J. Lowell, Nov 16 2020): for every `n ≥ 1`, there exist unique
`n`-digit numbers `A053336(n)` (with digits in `{5, 6}`) and `A035014(n)` (with digits in
`{3, 4}`) divisible by `2 ^ n`, and they satisfy `A053336(n) = 10 ^ n - A035014(n)`. -/
theorem main :
    ∀ n : ℕ, 1 ≤ n →
      (∃! m, IsA053336 n m) ∧
      (∃! m, IsA035014 n m) ∧
      (∀ m₁ m₂, IsA053336 n m₁ → IsA035014 n m₂ → m₁ = 10 ^ n - m₂) := by
  sorry

end OMA.S_oeis_a053336
