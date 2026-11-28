import Mathlib

/-!
# A395284: Semiprime chains under concatenation of the prime factors

`a(n)` is the smallest semiprime that produces a chain of exactly `n` semiprimes when
repeatedly replacing `m = p*q` (with primes `p ≤ q`) by the decimal concatenation of `p`
followed by `q`, stopping when the result is not semiprime. The first term of each chain is
the initial `m`, and the last term is the final semiprime before termination.

Conjecture (OEIS A395284): `a(n)` exists for all `n` (the offset is 1).

Source: https://oeis.org/A395284
Credit: @gblacher2
-/

namespace OMA.S_oeis_a395284

/-- `m` is a semiprime: a product of two (not necessarily distinct) primes. -/
def IsSemiprime (m : ℕ) : Prop := ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ m = p * q

/-- For a semiprime `m = p*q` with primes `p ≤ q` (so `p = m.minFac` and `q = m / m.minFac`),
the decimal concatenation of `p` followed by `q`. -/
def concatStep (m : ℕ) : ℕ :=
  Nat.ofDigits 10 (Nat.digits 10 (m / m.minFac) ++ Nat.digits 10 m.minFac)

/-- Starting from `m`, the chain consists of exactly `n` semiprimes: the first `n` iterates
`m, concatStep m, …` are semiprimes and the next one is not. -/
def HasChainLength (m n : ℕ) : Prop :=
  (∀ i < n, IsSemiprime (concatStep^[i] m)) ∧ ¬ IsSemiprime (concatStep^[n] m)

/-- For every `n ≥ 1` some semiprime produces a chain of exactly `n` semiprimes, so `a(n)`
exists. -/
theorem main : ∀ n : ℕ, 1 ≤ n → ∃ m : ℕ, IsSemiprime m ∧ HasChainLength m n := by
  sorry

end OMA.S_oeis_a395284
