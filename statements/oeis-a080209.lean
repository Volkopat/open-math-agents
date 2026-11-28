import Mathlib

/-!
# A080209: Gilbreath transform of the sequence of Sophie Germain primes (A005384), i.e., the diagonal of leading successive absolute differences of A005384.

Source: https://oeis.org/A080209
Credit: @divmxnd0x

Conjecture (stated in A080209): the diagonal of leading successive absolute differences of the
Sophie Germain primes consists, except for the initial 2, only of 1's and 3's.

Formalization notes:
* Row `0` is the sequence of Sophie Germain primes `2, 3, 5, 11, 23, 29, ...` (primes `p` with
  `2p + 1` prime), enumerated by `Nat.nth`; row `k + 1` lists the absolute differences of
  consecutive terms of row `k`. The diagonal is `T k 0`; `T 0 0 = 2` is the initial 2.
-/

namespace OMA.S_oeis_a080209

/-- `p` is a Sophie Germain prime. -/
def IsSophieGermain (p : ℕ) : Prop := p.Prime ∧ (2 * p + 1).Prime

/-- The Gilbreath array of the Sophie Germain primes. -/
noncomputable def T : ℕ → ℕ → ℕ
  | 0, j => Nat.nth IsSophieGermain j
  | k + 1, j => Nat.dist (T k (j + 1)) (T k j)

/-- Every leading term after the initial `2` is `1` or `3`. -/
theorem main : ∀ k : ℕ, 1 ≤ k → T k 0 = 1 ∨ T k 0 = 3 := by
  sorry

end OMA.S_oeis_a080209
