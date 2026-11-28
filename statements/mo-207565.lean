import Mathlib

/-!
# Differences associated with differences of primes: are they all 1, 2, 3?

Source: https://mathoverflow.net/questions/207565 (CC BY-SA 3.0).

Let `P_i` be the `i`-th prime (`P_1 = 2`) and `d_k = ∑_{i=0}^{k} (-1)^i binom(k, i) P_{k+1-i}`, the
`k`-th difference of the primes at `P_1` (`d_1 = 1, d_2 = 1, d_3 = -1, d_4 = 3, …`; OEIS A007442).
Let `(s_n)` be the increasing sequence of all `k ≥ 1` with `d_k > 0`, so
`(s_n) = (1, 2, 4, 6, 8, 10, 12, 14, 15, 17, 19, …)`. Question: is `s_{n+1} - s_n ∈ {1, 2, 3}`
for every `n`? Consecutive terms always differ by at least `1`, so this says: after every `k ≥ 1`
with `d_k > 0` one of `d_{k+1}, d_{k+2}, d_{k+3}` is positive. `main` states the expected yes.
Here `P_{j+1} = Nat.nth Nat.Prime j`.
-/

namespace OMA.S_mo_207565

/-- The `k`-th difference `d_k` of the sequence of primes. -/
noncomputable def d (k : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (k + 1), (-1) ^ i * (k.choose i : ℤ) * (Nat.nth Nat.Prime (k - i) : ℤ)

theorem main : ∀ k : ℕ, 1 ≤ k → 0 < d k → ∃ j ∈ ({1, 2, 3} : Finset ℕ), 0 < d (k + j) := by
  sorry

end OMA.S_mo_207565
