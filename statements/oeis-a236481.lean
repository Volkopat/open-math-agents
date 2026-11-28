import Mathlib

/-!
# A236481: Primes p with p + 2, prime(p) + 2 and prime(prime(p)) + 2 all prime.

Source: https://oeis.org/A236481
Credit: @gblacher2

Conjecture (Zhi-Wei Sun, comment in A236481): For any positive integer m, there are infinitely
many chains p(1) < p(2) < ... < p(m) of m primes with p(k) + 2 prime for all k = 1,...,m such
that p(k + 1) = prime(p(k)) for every 0 < k < m.

`prime(k)` is the `k`-th prime with `prime(1) = 2`, i.e. `Nat.nth Nat.Prime (k - 1)` in Mathlib's
0-indexed convention. A chain of length `m` is a function `p : Fin m → ℕ`: the source index
`k ∈ {1, ..., m}` corresponds to `⟨k - 1, _⟩ : Fin m`, so the condition for `0 < k < m` becomes
one condition for each pair of consecutive indices of `Fin m`. The sequence A236481 itself lists
the first elements `p(1)` of the chains with `m = 3`.
-/

namespace OMA.S_oeis_a236481

/-- `prime k`: the `k`-th prime, 1-indexed, so `prime 1 = 2`. -/
noncomputable def prime (k : ℕ) : ℕ := Nat.nth Nat.Prime (k - 1)

/-- For every positive integer `m` there are infinitely many chains `p(1) < ... < p(m)` of `m`
primes with `p(k) + 2` prime for all `k` and `p(k + 1) = prime(p(k))` for every `0 < k < m`. -/
theorem main : ∀ m : ℕ, 0 < m →
    {p : Fin m → ℕ | StrictMono p ∧ (∀ k, (p k).Prime ∧ (p k + 2).Prime) ∧
      ∀ (k : Fin m) (h : k.val + 1 < m), p ⟨k.val + 1, h⟩ = prime (p k)}.Infinite := by
  sorry

end OMA.S_oeis_a236481
