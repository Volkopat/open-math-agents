import Mathlib

/-!
# Is `∑ n / L(2n)` transcendental?

Source: AI Science Tracker (Marcello Pichini); preprint hexagon:2611.00639
(https://hexagonmath.org/2611.00639v1).
Credit: @jagraj28

Let `L_m` be the Lucas numbers: `L₀ = 2`, `L₁ = 1`, `L_{m+1} = L_m + L_{m-1}`, so that
`L_{2n} = φ^{2n} + φ^{-2n}` with `φ = (1 + √5) / 2`. The question asks whether
`S = ∑_{n ≥ 1} n / L_{2n}` is transcendental. The sums `∑ 1 / L_{2n}` and `∑ n² / L_{2n}` are
known to be transcendental (Duverney, Nishioka, Nishioka and Shiokawa, 1997); the preprint proves
only that `S ∉ ℚ(√5)`.

`main` states that `S` is transcendental over `ℚ`. A proof of `¬ main` would show that `S` is
algebraic.

Conventions.
* `lucas` is defined by the recursion above, with values in `ℕ`.
* The sum runs over `n ≥ 1`, written as `∑' n : ℕ, (n + 1) / L_{2(n+1)}` in `ℝ`. The terms decay
  like `n φ^{-2n}`, so the series converges absolutely and `tsum` is its sum.
* Transcendence is Mathlib's `Transcendental ℚ S`.
-/

namespace OMA.S_aist_transcendence_sum_n_over_lucas_2n

/-- The Lucas numbers: `L₀ = 2`, `L₁ = 1`, `L_{m+2} = L_{m+1} + L_m`. -/
def lucas : ℕ → ℕ
  | 0 => 2
  | 1 => 1
  | m + 2 => lucas (m + 1) + lucas m

/-- `∑_{n ≥ 1} n / L_{2n}` is transcendental. -/
theorem main :
    Transcendental ℚ (∑' n : ℕ, ((n + 1 : ℕ) : ℝ) / (lucas (2 * (n + 1)) : ℝ)) := by
  sorry

end OMA.S_aist_transcendence_sum_n_over_lucas_2n
