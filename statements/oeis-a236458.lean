import Mathlib

/-!
# A236458: Primes p with p + 2 and prime(p) + 2 both prime

Source: https://oeis.org/A236458
Credit: @gblacher2

`prime(k)` is the `k`-th prime with `prime(1) = 2`, i.e. `Nat.nth Nat.Prime (k - 1)` in Mathlib's
0-indexed convention. The entry states that, according to the conjecture in A236470 (Zhi-Wei Sun),
the sequence should have infinitely many terms.
-/

namespace OMA.S_oeis_a236458

/-- `prime k`: the `k`-th prime, 1-indexed, so `prime 1 = 2`. -/
noncomputable def prime (k : ℕ) : ℕ := Nat.nth Nat.Prime (k - 1)

/-- There are infinitely many primes `p` such that `p + 2` and `prime(p) + 2` are both prime. -/
theorem main : {p : ℕ | p.Prime ∧ (p + 2).Prime ∧ (prime p + 2).Prime}.Infinite := by
  sorry

end OMA.S_oeis_a236458
