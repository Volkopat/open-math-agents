import FormalConjectures.ErdosProblems.«430»

/-!
# Erdős 430: reduction to semiprimes just below a shifted prime

The sequence of the problem for `n` is the set `terms n` of integers `1 < m < n` all of whose
prime factors exceed `n - m`. Its largest element is `n - 1`, so when `n - 1` is composite the
sequence already contains a composite. The question is therefore only about `n = P + 1` with
`P` prime.

A semiprime `p q` with `p ≤ q` lies in `terms n` as soon as `p q < n < p q + p`: both prime
factors are at least `p`, and `n - p q < p`. So it is enough that every large `n` with `n - 1`
prime has a semiprime `p q` in the window `(n - p, n)`, where `p` is its smaller prime factor.
Equivalently, some prime `p` with `p ^ 2 < n` and `p ∤ n` has `⌊(n - 1) / p⌋` prime.

* `H1` is this statement about semiprimes below shifted primes. It is the open core. It is
  sufficient for the problem and not known to be equivalent to it.
* `H2` is the elementary fact that such a semiprime belongs to `terms n`.

Numerical evidence (a machine search, not part of the proof): for `n ≤ 6 · 10^7` with `n - 1`
prime, `H1` fails for exactly 121 values of `n`, the largest being `267680`, and all terms are
prime for exactly 101 values of `n`, the largest again `267680`.
-/

open Filter

namespace OMA.R_Erdos430_erdos_430_R1

/-- Every large `n` with `n - 1` prime has a semiprime `p q`, `p ≤ q`, with `p q < n < p q + p`. -/
def H1 : Prop := ∀ᶠ n : ℕ in atTop, (n - 1).Prime →
  ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≤ q ∧ p * q < n ∧ n < p * q + p

/-- A semiprime `p q`, `p ≤ q`, with `p q < n < p q + p` is a term of the sequence for `n`. -/
def H2 : Prop := ∀ n p q : ℕ, p.Prime → q.Prime → p ≤ q → p * q < n → n < p * q + p →
  p * q ∈ Erdos430.terms n

theorem main : H1 → H2 → type_of% @Erdos430.erdos_430 := by
  intro h1 h2
  filter_upwards [h1, eventually_ge_atTop 3] with n hn h3 hall
  by_cases hp : (n - 1).Prime
  · obtain ⟨p, q, hp', hq, hpq, hlt, hgt⟩ := hn hp
    exact Nat.not_prime_mul hp'.one_lt.ne' hq.one_lt.ne'
      (hall _ (h2 n p q hp' hq hpq hlt hgt))
  · exact hp (hall _ (Erdos430.isGreatest_sub_one h3).1)

end OMA.R_Erdos430_erdos_430_R1
