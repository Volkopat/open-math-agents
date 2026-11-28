import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.Data.Nat.Totient

/-!
Peter Bala's conjecture appears in OEIS A143138.
The sequence is defined by its published Stirling-number formula.
The eventual period can be chosen to be `Nat.totient k`.

Source: https://oeis.org/A143138
-/

namespace OMA.S_oeis_a143138

def sequence (n : ℕ) : ℕ :=
  ∑ j ∈ Finset.range n,
    ((2 * j).factorial / j.factorial) * Nat.stirlingSecond (n - 1 + j) (2 * j)

theorem main : ∀ k : ℕ, 0 < k →
    ∃ N : ℕ, ∀ n ≥ N, (sequence (n + Nat.totient k)) % k = sequence n % k := by
  sorry

end OMA.S_oeis_a143138
