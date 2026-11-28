import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Order.Bounds.Defs

/-!
# OEIS A257662

Zhi-Wei Sun conjectures that for each positive integer `n` there is a least
prime `q` for which the partition number at `q * n` is prime.

Source: https://oeis.org/A257662
Credit: @jacklarmer
-/

namespace OMA.S_oeis_a257662

theorem main :
    ∀ n : ℕ, 0 < n →
      ∃ q : ℕ, IsLeast {r : ℕ | r.Prime ∧ (Fintype.card (Nat.Partition (r * n))).Prime} q := by
  sorry

end OMA.S_oeis_a257662
