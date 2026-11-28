import Mathlib

/-!
# The greedy sequence A377362

Source: https://mathoverflow.net/questions/481310
Sequence: https://oeis.org/A377362
-/

namespace OMA.S_mo_481310

/-- A positive candidate must be unused and satisfy the coprimality test
against each term already chosen. The sequence is indexed from 1. -/
def Eligible (a : ℕ → ℕ) (n m : ℕ) : Prop :=
  0 < m ∧ ∀ i : ℕ, 1 ≤ i → i ≤ n →
    m ≠ a i ∧ Nat.gcd (m * a n + 1) (a i) = 1

/-- Does every positive integer occur in the sequence obtained by starting
with 1 and repeatedly choosing the least eligible candidate? -/
theorem main :
    ∀ a : ℕ → ℕ, a 1 = 1 →
      (∀ n : ℕ, 1 ≤ n → IsLeast {m : ℕ | Eligible a n m} (a (n + 1))) →
      ∀ m : ℕ, 0 < m → ∃ n : ℕ, 1 ≤ n ∧ a n = m := by
  sorry

end OMA.S_mo_481310
