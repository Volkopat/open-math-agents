import Mathlib

/-!
# A005384: Sophie Germain primes

Source: https://oeis.org/A005384
Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Let `a(1) = 2, a(2) = 3, a(3) = 5, a(4) = 11, …` be the Sophie Germain primes (primes `p` with
`2p + 1` prime). Conjecture (OEIS comment): for any integers `n ≥ m > 0` there are infinitely
many integers `b > a(n)` such that `∑_{k=m}^{n} a(k) · b^(n-k)` is prime.

## Encoding

* `a k` uses the OEIS offset `1`: `a k = Nat.nth (Sophie Germain prime) (k - 1)`.
* `b` ranges over natural numbers (the conditions force `b > a(n) ≥ 2`).
-/

namespace OMA.S_oeis_a005384

/-- `p` is a Sophie Germain prime. -/
def IsSophieGermain (p : ℕ) : Prop := p.Prime ∧ (2 * p + 1).Prime

/-- `a k`, the `k`-th Sophie Germain prime (offset `1`). -/
noncomputable def a (k : ℕ) : ℕ := Nat.nth IsSophieGermain (k - 1)

theorem main :
    ∀ m n : ℕ, 0 < m → m ≤ n →
      {b : ℕ | a n < b ∧ (∑ k ∈ Finset.Icc m n, a k * b ^ (n - k)).Prime}.Infinite := by
  sorry

end OMA.S_oeis_a005384
