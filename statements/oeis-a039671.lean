import Mathlib

/-!
# Row sums in the postage-stamp array

Richard Ollerton's array, described in A007059, has F(0,k)=1 and
F(n,k) equal to the sum of the previous k entries of its column.
Values at negative row indices are zero, so the recurrence can stop at
the row-zero entry. A039671 sums each row through its main diagonal.
Independently, A126198(n,k) counts ordered compositions of n whose
parts are at most k. L. Edson Jeffery proposed the row-sum identity.

https://oeis.org/A039671 · https://oeis.org/A007059 · https://oeis.org/A126198
Formalization: @KoaOkano
-/

namespace OMA.S_oeis_a039671

def postage (k : ℕ) : ℕ → ℕ
  | 0 => 1
  | n+1 => ∑ j : Fin (min (n+1) k), postage k (n-j.val)
termination_by n => n
decreasing_by omega

abbrev Bounded (n k : ℕ) := {c : Composition n // ∀ a ∈ c.blocks, a ≤ k}

theorem main : ∀ n : ℕ, 0 < n →
    (∑ k ∈ Finset.range (n+1), postage k n) =
      ∑ j ∈ Finset.range n, Nat.card (Bounded n (j+1)) := by
  sorry

end OMA.S_oeis_a039671
