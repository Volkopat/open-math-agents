import Mathlib

/-!
# A337945: Numbers m with a solution (s,t,k) such that s^2 + t^2 = k*m, s + t = m, 1 <= s <= t and 1 <= k <= m - 1.

Source: https://oeis.org/A337945
Credit: @avivorly

A337945 (offset 1): the numbers `m` for which some `s, t, k` satisfy `s^2 + t^2 = k*m`, `s + t = m`,
`1 ≤ s ≤ t` and `1 ≤ k ≤ m - 1`: 2, 4, 6, 8, 9, 10, 12, 14, 16, 18, 20, 22, 24, 25, 26, 27, ...
For example 9 is a term, with `(s, t, k) = (3, 6, 5)`.

Conjecture (Peter Luschny, Jun 08 2023): `k` is a term iff `k * Clausen(k, 1) ≠ 2 * Clausen(k, 0)`
(Clausen = A160014). In other words: `k` is in this sequence iff it is not an odd squarefree number.

Both sentences of the conjecture are stated, as a conjunction; the variable is called `m` here, as in
the definition of the sequence, and ranges over the positive integers.

Conventions:
- A160014: `Clausen(n, k)` is the product of the primes `p` such that `(p - k)` divides `n`. Only
  `k = 0` and `k = 1` occur here, where `p - k ≥ 1` for every prime `p`, so the truncated subtraction
  in `ℕ` is exact; for `n ≥ 1` every such prime satisfies `p ≤ n + k`, so the product over the primes
  below `n + k + 1` is the full product. `Clausen(n, 0)` is the squarefree kernel of `n` and
  `Clausen(n, 1)` is the classical Clausen number (the denominator of the Bernoulli number `B_n`
  for even `n`).
- `Odd` and `Squarefree` are Mathlib's.
-/

namespace OMA.S_oeis_a337945

/-- A160014: the product of the primes `p` with `(p - k) ∣ n` (all of them are `≤ n + k` when `n ≥ 1`). -/
def clausen (n k : ℕ) : ℕ :=
  ∏ p ∈ (Finset.range (n + k + 1)).filter (fun p => p.Prime ∧ (p - k) ∣ n), p

/-- `m` is a term of A337945. -/
def IsTerm (m : ℕ) : Prop :=
  ∃ s t k : ℕ, s ^ 2 + t ^ 2 = k * m ∧ s + t = m ∧ 1 ≤ s ∧ s ≤ t ∧ 1 ≤ k ∧ k ≤ m - 1

theorem main :
    (∀ m : ℕ, 1 ≤ m → (IsTerm m ↔ m * clausen m 1 ≠ 2 * clausen m 0)) ∧
    (∀ m : ℕ, 1 ≤ m → (IsTerm m ↔ ¬ (Odd m ∧ Squarefree m))) := by
  sorry

end OMA.S_oeis_a337945
