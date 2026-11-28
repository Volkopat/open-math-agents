import Mathlib

/-!
# Are there infinitely many non-Wolstenholme primes?

Source: https://mathoverflow.net/questions/85383 (CC BY-SA 4.0).

For a prime `p` the following are equivalent: `binom(2p-1, p-1) ≡ 1 (mod p⁴)`; `p³` divides the
numerator of `∑_{n=1}^{p-1} 1/n`; `p` divides the numerator of `B_{p-3}`. A prime satisfying them
is a Wolstenholme prime; only two are known (16843 and 2124679). It is conjectured that there are
infinitely many, of density 0. The question: is it known that there are infinitely many primes
that are NOT Wolstenholme primes? (This would follow from the infinitude of regular primes.)

We state the affirmative answer.

Formalization notes:
* A Wolstenholme prime is defined by the first condition of the source,
  `Nat.choose (2p - 1) (p - 1) ≡ 1 [MOD p ^ 4]`. Under this literal definition the small primes
  `2` and `3` are not Wolstenholme primes either; finitely many primes do not affect the question.
* Checked numerically: every prime below `200` is a non-Wolstenholme prime.
-/

namespace OMA.S_mo_85383

/-- A Wolstenholme prime: a prime `p` with `binom(2p-1, p-1) ≡ 1 (mod p⁴)`. -/
def IsWolstenholmePrime (p : ℕ) : Prop :=
  p.Prime ∧ Nat.choose (2 * p - 1) (p - 1) ≡ 1 [MOD p ^ 4]

/-- There are infinitely many primes that are not Wolstenholme primes. -/
theorem main : {p : ℕ | p.Prime ∧ ¬ IsWolstenholmePrime p}.Infinite := by
  sorry

end OMA.S_mo_85383
