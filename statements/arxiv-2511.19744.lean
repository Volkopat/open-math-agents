import Mathlib

/-!
# Toda primes

Source: https://arxiv.org/abs/2511.19744
(S. McKean, Toda primes, Conjecture 1.3)
Credit: @SulkBash

## The problem, as the source states it

Definition 1.1. Let `n` be an integer. A Toda prime of `n` is an odd prime `p` such that
`p - 1 ∣ 4n` and `gcd(p, 4n / (p - 1)) = 1`. Denote the set of Toda primes of `n` by `T(n)`, and
let `t(n) := |T(n)|`.

Conjecture 1.3. If `n` is a positive integer, then `t(n) ≥ 2`.

Equivalently (abstract): a Toda prime of `n` is an odd prime `p` such that `4n = (p - 1) k` with
`k` coprime to `p`. For example `T(1) = {3, 5}`, `T(3) = {5, 7, 13}` and `T(17) = {3, 5}`.

The motivation is homotopy theory: by a theorem of Toda, `ℤ/p ⊆ π_{2(p-1)k+1}(S³)` whenever
`gcd(p, k) = 1`, so a Toda prime of every positive integer would give a short proof that
`π_n(S³) ≠ 0` for all `n ≡ 1 (mod 8)`. Even the weaker question whether every positive integer
has at least one Toda prime (Question 1.2, attributed to Roman Mikhailov on MathOverflow) is
open; the paper proves it only conditionally on a further conjecture (Theorem 1.5).

## Formalization notes

* `IsTodaPrime n p` is Definition 1.1 verbatim: `p` is prime, `p` is odd, `p - 1 ∣ 4 * n`, and
  `p` is coprime to `4 * n / (p - 1)`. An odd prime is at least `3`, so the natural-number
  subtraction `p - 1` is exact and positive, and the division `4 * n / (p - 1)` is exact because
  of the divisibility; it is the `k` of the abstract's formulation.
* `n` ranges over the positive natural numbers, as in Conjecture 1.3.
* `t(n) ≥ 2` is stated as: there are two distinct Toda primes of `n`. This is the same as
  `|T(n)| ≥ 2` and avoids taking the cardinality of a set (which is finite here, since
  `p - 1 ∣ 4n` forces `p ≤ 4n + 1`).
* `main` is Conjecture 1.3. A disproof is a positive integer with at most one Toda prime.
-/

namespace OMA.S_arxiv_2511_19744

/-- `p` is a Toda prime of `n`: an odd prime with `p - 1 ∣ 4n` and `gcd(p, 4n / (p - 1)) = 1`. -/
def IsTodaPrime (n p : ℕ) : Prop :=
  p.Prime ∧ Odd p ∧ (p - 1) ∣ 4 * n ∧ Nat.Coprime p (4 * n / (p - 1))

/-- Conjecture 1.3: every positive integer has at least two Toda primes. -/
theorem main : ∀ n : ℕ, 0 < n → ∃ p q : ℕ, p ≠ q ∧ IsTodaPrime n p ∧ IsTodaPrime n q := by
  sorry

end OMA.S_arxiv_2511_19744
