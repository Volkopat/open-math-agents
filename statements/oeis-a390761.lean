import Mathlib

/-!
# A390761: The largest least self-digit-divisible representative

Source: https://oeis.org/A390761

For a positive integer n, a valid representative is a positive k having
exactly the decimal digits of n, with no restriction on multiplicities, and
divisible by every nonzero digit of n. The OEIS takes a(n) to be the least
valid representative, or -1 if there is none.

The conjecture states that a(709) = 707777779779 is the maximum. We use
the equivalent least-element formulation. A nonexistent representative
has the OEIS value -1 and does not contribute a case to the upper bound.
Michael S. Branicky reported the exhaustive resolution in the OEIS entry.
-/

namespace OMA.S_oeis_a390761

/-- A positive integer with the required digit set and divisibility. -/
def Valid (n k : ℕ) : Prop :=
  0 < k ∧ (Nat.digits 10 k).toFinset = (Nat.digits 10 n).toFinset ∧
    ∀ d ∈ Nat.digits 10 n, d ≠ 0 → d ∣ k

/-- The specified value is attained at 709 and is an upper bound for every term. -/
theorem main : IsLeast {k : ℕ | Valid 709 k} 707777779779 ∧
    ∀ n k : ℕ, 0 < n → IsLeast {j : ℕ | Valid n j} k → k ≤ 707777779779 := by
  sorry

end OMA.S_oeis_a390761
