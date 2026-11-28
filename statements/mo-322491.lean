import Mathlib

/-!
# MathOverflow 322491: does the primes snake-product converge?

Source: https://mathoverflow.net/questions/322491 (Joseph O'Rourke, CC BY-SA 4.0).

Question: does the infinite product
`(2/3) · (7/5) · (11/13) · (19/17) · (23/29) · (37/31) · ⋯`
converge? The primes are taken in consecutive pairs `(p₁, p₂), (p₃, p₄), …`, and the `k`-th factor
(from `k = 0`) is the smaller prime of the pair over the larger for even `k` and the larger over
the smaller for odd `k`. Numerically the partial products are `≈ 0.9048` out to primes of size
`10¹⁰`.

Convergence is meant in the usual sense for infinite products: the partial products (after
each factor) tend to a finite nonzero limit, which here is positive since all factors are.
`main` asserts that the product converges; a disproof shows it does not. Here `p_{j+1}` is
`Nat.nth Nat.Prime j`.
-/

namespace OMA.S_mo_322491

open Filter Topology

/-- The `(j+1)`-th prime, as a real number. -/
noncomputable def q (j : ℕ) : ℝ := (Nat.nth Nat.Prime j : ℝ)

/-- The `k`-th factor of the snake-product. -/
noncomputable def factor (k : ℕ) : ℝ :=
  if Even k then q (2 * k) / q (2 * k + 1) else q (2 * k + 1) / q (2 * k)

theorem main : ∃ L : ℝ, 0 < L ∧
    Tendsto (fun N => ∏ k ∈ Finset.range N, factor k) atTop (𝓝 L) := by
  sorry

end OMA.S_mo_322491
