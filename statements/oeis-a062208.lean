import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Data.Nat.Totient

/-!
Peter Bala's eventual-period conjecture for OEIS A062208.
The A062208 entry identifies its sequence as the row sums of A299041.
The finite formula below is the coefficient formula from A299041, summed over
each row's support, with the same value 1 at index zero.

Sources: https://oeis.org/A062208 and https://oeis.org/A299041
-/

namespace OMA.S_oeis_a062208

def coefficient (n r : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (r + 1), (-1 : ℤ) ^ (r - i) * (r.choose i : ℤ) * (i.choose 3 : ℤ) ^ n

def sequence (n : ℕ) : ℤ := ∑ r ∈ Finset.range (3 * n + 1), coefficient n r

theorem main : ∀ k : ℕ, 0 < k →
    ∃ N : ℕ, ∀ n ≥ N, sequence (n + Nat.totient k) ≡ sequence n [ZMOD (k : ℤ)] := by
  sorry

end OMA.S_oeis_a062208
