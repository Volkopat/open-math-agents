import Mathlib

/-!
# A237838: a(n) = |{0 < k <= n: the number of Sophie Germain primes among 1, ..., k*n is a Sophie Germain prime}|

Source: https://oeis.org/A237838
Credit: @ceejcake

Conjecture (Zhi-Wei Sun, 2014, OEIS A237838): `a(n) > 0` for all `n > 1`.

Formalization notes:
* The sequence has offset `1`; `a(1) = 0`, which is why the conjecture starts at `n = 2`.
* A Sophie Germain prime is a prime `p` such that `2 * p + 1` is also prime (OEIS A005384).
* `sgCount m` is the number of Sophie Germain primes in `{1, ..., m}`; it is computed over
  `Finset.range (m + 1)`, which only adds `0`, and `0` is not prime.
* `a n` is the number of `k` with `1 ≤ k ≤ n` such that `sgCount (k * n)` is a Sophie Germain prime.
* Initial values for `n = 1, ..., 12`: `a(n) = 0, 1, 3, 2, 3, 2, 2, 2, 2, 1, 1, 2`.
-/

namespace OMA.S_oeis_a237838

/-- `p` is a Sophie Germain prime: both `p` and `2 * p + 1` are prime. -/
def IsSophieGermain (p : ℕ) : Prop :=
  p.Prime ∧ (2 * p + 1).Prime

instance : DecidablePred IsSophieGermain := fun p => by
  unfold IsSophieGermain
  infer_instance

/-- The number of Sophie Germain primes among `1, ..., m`. -/
def sgCount (m : ℕ) : ℕ :=
  ((Finset.range (m + 1)).filter IsSophieGermain).card

/-- `a n` is the number of `k` with `0 < k ≤ n` such that the number of Sophie Germain primes
among `1, ..., k * n` is itself a Sophie Germain prime. -/
def a (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).filter fun k => IsSophieGermain (sgCount (k * n))).card

/-- OEIS A237838 conjecture (Zhi-Wei Sun): `a n > 0` for every `n > 1`. -/
theorem main : ∀ n : ℕ, 1 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a237838
