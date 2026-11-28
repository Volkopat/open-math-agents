import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Set.Finite.Basic

/-!
# Prime sums of Lucas numbers and powers of two

Source: https://oeis.org/A392575
Credit: @luciusacarr

A nonnegative sequence term means some exponent works. A positive
term also requires that exponent zero fails.
-/

namespace OMA.S_oeis_a392575

def lucas : ℕ → ℕ
  | 0 => 2
  | 1 => 1
  | n + 2 => lucas (n + 1) + lucas n

theorem main :
    (∀ m : ℕ, ∃ n : ℕ, m < n ∧ ∃ k : ℕ, (lucas (3 * n) + 2 ^ k).Prime) ∧
    Set.Infinite {n : ℕ | ¬ (lucas n + 1).Prime ∧
      ∃ k : ℕ, 0 < k ∧ (lucas n + 2 ^ k).Prime} := by
  sorry

end OMA.S_oeis_a392575
