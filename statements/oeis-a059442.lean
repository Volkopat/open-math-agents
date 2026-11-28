import Mathlib

/-!
# A059442: Ramsey numbers R(n, k) — the fence conjecture

Source: https://oeis.org/A059442
Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Fence conjecture (Jianglin Luo, OEIS comment): for `n ≥ m ≥ 3`,
`R(m, n) ≤ (2m - 1) · T(2m - 6 + n, m) + m + 1`, where `T(N, k)` (A008284) is the number of
partitions of `N` into exactly `k` positive parts.

## Encoding

* `R(m, n)` is the least `N` such that every simple graph on `N` vertices contains a clique of
  size `m` or an independent set of size `n` (an `n`-clique of the complement).
* `T(N, k)` counts `Nat.Partition N` with exactly `k` parts.
* The second remark of the same comment (`R(3, n) mod 5`) is not stated here.
-/

namespace OMA.S_oeis_a059442

/-- The Ramsey number `R(m, n)`. -/
noncomputable def ramsey (m n : ℕ) : ℕ :=
  sInf {N : ℕ | ∀ G : SimpleGraph (Fin N), ¬ G.CliqueFree m ∨ ¬ Gᶜ.CliqueFree n}

/-- `T(N, k)`: partitions of `N` into exactly `k` parts. -/
def T (N k : ℕ) : ℕ :=
  (Finset.univ.filter fun p : Nat.Partition N => p.parts.card = k).card

theorem main :
    ∀ m n : ℕ, 3 ≤ m → m ≤ n → ramsey m n ≤ (2 * m - 1) * T (2 * m - 6 + n) m + m + 1 := by
  sorry

end OMA.S_oeis_a059442
