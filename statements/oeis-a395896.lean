import Mathlib.Data.Nat.BitIndices
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.RingTheory.Radical.NatInt

/-!
# OEIS A395896: Consecutive integers with radicals dividing a squarefree number

Source: https://oeis.org/A395896
Indexing of the squarefree numbers: https://oeis.org/A019565
Credit: Michael De Vlieger (conjecture).

The term of A019565 at index n is the product of the primes at the indices of
the set bits of n, using zero-based prime indices. In particular, index zero
gives the empty product, 1. For this term m, A395896 counts positive integers k
strictly below m² for which rad(k) and rad(k + 1) both divide m.
The conjecture states that the resulting count is zero at every even index.
-/

namespace OMA.S_oeis_a395896

open UniqueFactorizationMonoid

/-- The A019565 term at the zero-based index n. -/
noncomputable def squarefreeTerm (n : ℕ) : ℕ :=
  ∏ i ∈ n.bitIndices.toFinset, Nat.nth Nat.Prime i

/-- The A395896 term at the zero-based index n. -/
noncomputable def a (n : ℕ) : ℕ :=
  let m := squarefreeTerm n
  ((Finset.Ico 1 (m ^ 2)).filter (fun k => radical k ∣ m ∧ radical (k + 1) ∣ m)).card

theorem main : ∀ n : ℕ, Even n → a n = 0 := by
  sorry

end OMA.S_oeis_a395896
