import Mathlib

/-!
# A396527: a(n) is the least number that is the sum of two distinct upper twin primes in exactly n ways, or -1 if there is no such number.

Source: https://oeis.org/A396527
Credit: @gblacher2

Conjecture (OEIS A396527): a(n) > 0 for all n (offset 1), that is, for every `n ≥ 1`
some number is the sum of two distinct upper twin primes in exactly `n` ways.
Upper twin primes are the greater members of twin prime pairs (A006512: 5, 7, 13, 19, ...).
Ways are unordered, so each is counted once as a pair `p < q`.
-/

namespace OMA.S_oeis_a396527

/-- `p` is an upper twin prime: `p` and `p - 2` are both prime (A006512). -/
def IsUpperTwinPrime (p : ℕ) : Prop :=
  p.Prime ∧ (p - 2).Prime

/-- The number of ways to write `m = p + q` with `p < q` both upper twin primes. -/
noncomputable def ways (m : ℕ) : ℕ :=
  {pq : ℕ × ℕ | pq.1 < pq.2 ∧ IsUpperTwinPrime pq.1 ∧ IsUpperTwinPrime pq.2 ∧
    pq.1 + pq.2 = m}.ncard

theorem main : ∀ n : ℕ, 1 ≤ n → ∃ m : ℕ, ways m = n := by
  sorry

end OMA.S_oeis_a396527
