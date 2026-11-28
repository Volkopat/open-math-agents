import Mathlib

/-!
# OEIS A351373: least prime starting 2n consecutive primes with sum 6 * prime

Source: https://oeis.org/A351373
Credit: @unserus

OEIS: "Conjecture: each odd prime occurs infinitely many times."

a(n) (n ≥ 1) is the least prime `p` that begins a run of `2n` consecutive primes
whose sum is 6 times a prime. With `Nat.nth Nat.Prime i` the `i`-th prime
(0-indexed), a prime `p = Nat.nth Nat.Prime i` qualifies for `n` when
`∑ j ∈ Finset.range (2n), Nat.nth Nat.Prime (i + j) = 6 * q` for a prime `q`.

The conjecture: for every odd prime `ℓ` there are infinitely many `n ≥ 1` such
that `ℓ` is the least qualifying prime for `n`, i.e. `a(n) = ℓ`. Stating it with
`IsLeast` avoids any convention for an `n` with no qualifying prime.
-/

namespace OMA.S_oeis_a351373

/-- `p` begins a run of `2n` consecutive primes whose sum is 6 times a prime. -/
def Starts (n p : ℕ) : Prop :=
  ∃ i, p = Nat.nth Nat.Prime i ∧ ∃ q : ℕ, q.Prime ∧
    ∑ j ∈ Finset.range (2 * n), Nat.nth Nat.Prime (i + j) = 6 * q

/-- Every odd prime equals a(n) for infinitely many `n`. -/
theorem main :
    ∀ ℓ : ℕ, ℓ.Prime → Odd ℓ → {n : ℕ | 1 ≤ n ∧ IsLeast {p | Starts n p} ℓ}.Infinite := by
  sorry

end OMA.S_oeis_a351373
