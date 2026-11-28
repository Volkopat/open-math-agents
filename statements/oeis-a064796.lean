import Mathlib

/-!
# OEIS A064796: the min-max of adjacent products around a circular permutation

Source: https://oeis.org/A064796
Credit: @sntntHb

A064796: largest integer `m` such that every permutation `(p_1, ..., p_n)` of `(1, ..., n)`
satisfies `p_i * p_{i+1} >= m` for some `i`, `1 <= i <= n`, where `p_{n+1} = p_1`
(offset 1: 1, 2, 6, 8, 12, 15, 20, 24, 30, ...).

Conjecture (Jud McCranie, Oct 25 2001): `a(n) = (n+1)*(n+3)/4` for odd `n`, `a(n) = n*(n+4)/4`
for even `n`.

Formalized: a permutation of `(1, ..., n)` is `σ : Equiv.Perm (Fin n)` with `p_i = σ i + 1`, and
the cyclic successor of position `i` is `finRotate n i`. `main` states that the formula is the
greatest element of the set of such `m`, for every `n >= 3` (for `n = 1, 2` the formula gives
2 and 3, while the sequence starts 1, 2).
-/

namespace OMA.S_oeis_a064796

/-- McCranie's conjectured closed form. -/
def f (n : ℕ) : ℕ := if n % 2 = 1 then (n + 1) * (n + 3) / 4 else n * (n + 4) / 4

theorem main : ∀ n : ℕ, 3 ≤ n →
    IsGreatest {m : ℕ | ∀ σ : Equiv.Perm (Fin n), ∃ i : Fin n,
      m ≤ ((σ i : ℕ) + 1) * ((σ (finRotate n i) : ℕ) + 1)} (f n) := by
  sorry

end OMA.S_oeis_a064796
