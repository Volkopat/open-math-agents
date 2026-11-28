import Mathlib

/-!
# A259539: Numbers m with m-1, m+1 and prime(m)+2 all prime

Source: https://oeis.org/A259539
Credit: @gblacher2

`prime(k)` is the `k`-th prime with `prime(1) = 2`, i.e. `Nat.nth Nat.Prime (k - 1)` in Mathlib's
0-indexed convention. Zhi-Wei Sun's conjecture in the entry: the sequence contains infinitely many
terms. (The entry notes that this is stronger than the Twin Prime Conjecture and weaker than the
conjecture in A259540.)

Since `m - 1` must be prime, every term has `m ≥ 3`, so `prime m` is never evaluated at `0`.
-/

namespace OMA.S_oeis_a259539

/-- `prime k`: the `k`-th prime, 1-indexed, so `prime 1 = 2`. -/
noncomputable def prime (k : ℕ) : ℕ := Nat.nth Nat.Prime (k - 1)

/-- There are infinitely many numbers `m` such that `m - 1`, `m + 1` and `prime(m) + 2` are all
prime. -/
theorem main : {m : ℕ | (m - 1).Prime ∧ (m + 1).Prime ∧ (prime m + 2).Prime}.Infinite := by
  sorry

end OMA.S_oeis_a259539
