import Mathlib

/-!
# A242193: primitive prime divisors of Bernoulli numbers

Source: https://oeis.org/A242193
Credit: @coleman415

The sequence (Zhi-Wei Sun) is: `a(n)` = least prime `p` such that `B_{2n} == 0 (mod p)` but there
is no `k < n` with `B_{2k} == 0 (mod p)`, or `1` if such a prime `p` does not exist, where `B_m`
denotes the `m`-th Bernoulli number. The sequence has offset 1.
The entry records: *Conjecture: a(n) is prime for any n > 4.*

So the conjecture says: for every `n > 4` such a prime `p` exists.

Conventions:
- A rational number `x` is `≡ 0 (mod p)` when `p` divides the numerator of `x` in lowest terms
  (the denominator is then prime to `p`). Example from the entry: the numerator of `|B_28|` is
  `7 * 9349 * 362903`.
- `bernoulli m` is Mathlib's `B_m`. Only even indices occur, so the sign convention for `B_1`
  does not matter.
- `k` ranges over `0 < k < n` (the offset of the sequence is 1). Allowing `k = 0` changes
  nothing, since `B_0 = 1`.
-/

namespace OMA.S_oeis_a242193

/-- The rational number `x` is congruent to 0 modulo `p`: `p` divides its reduced numerator. -/
def RatModZero (x : ℚ) (p : ℕ) : Prop := (p : ℤ) ∣ x.num

/-- The conjecture of OEIS A242193. -/
theorem main :
    ∀ n : ℕ, 4 < n → ∃ p : ℕ, p.Prime ∧ RatModZero (bernoulli (2 * n)) p ∧
      ∀ k : ℕ, 0 < k → k < n → ¬ RatModZero (bernoulli (2 * k)) p := by
  sorry

end OMA.S_oeis_a242193
