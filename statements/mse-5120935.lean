import Mathlib

/-!
# Behavior of polynomial roots when removing a single term.

Source: https://math.stackexchange.com/questions/5120935/behavior-of-polynomial-roots-when-removing-a-single-term
(cross-posted to MathOverflow: https://mathoverflow.net/questions/507464)
Credit: @Caliko06

Fix `C > 0` (named `B` in the code, since `C` is `Polynomial.C`). `𝒫ₙ(C)` is the set of monic complex polynomials `P` of degree `n` whose lower
coefficients satisfy `|a_j| ≤ C` for `j < n`. For `k ∈ {0, …, n}`, `P_k = P - a_k z^k` is `P` with
its `k`-th term removed (`P - C (P.coeff k) * X ^ k`). The modified roots form the multiset sum
`𝒵_mod = Z(P_0) + ⋯ + Z(P_n)` (union of multisets, counted with multiplicity), and
`N_total = |𝒵_mod|`. A modified root `ζ` is far when `dist(ζ, Z(P)) = min_{w ∈ Z(P)} |ζ - w| > ε`.

Conjecture (as stated in the source): for every `ε > 0` and every sequence `P⁽ⁿ⁾ ∈ 𝒫ₙ(C)`,
`#{ζ ∈ 𝒵_mod : dist(ζ, Z(P⁽ⁿ⁾)) > ε} / N_total → 0` as `n → ∞`.

Conventions:
* `Z(P)` is `Polynomial.roots`, a multiset with multiplicity. Over `ℂ` a nonzero polynomial
  splits, so this is the full root multiset. The only zero `P_k` is `P_0` for `n = 0`
  (`P = 1`), whose root multiset is empty; this does not affect the limit.
* `dist(ζ, Z(P)) > ε` is written as `∀ w ∈ Z(P), ε < ‖ζ - w‖`. For `n ≥ 1`, `Z(P)` is a nonempty
  finite set, so this is exactly `min_{w ∈ Z(P)} |ζ - w| > ε`.
* The far roots are counted with multiplicity, as in the source (and its numerical script).
* The ratio is taken in `ℝ`; for `n ≥ 1`, `N_total ≥ n² > 0`, so there is no division by zero
  in the range that matters for the limit.
-/

namespace OMA.S_mse_5120935

open Polynomial Filter Topology

/-- `𝒫ₙ(C)`: monic complex polynomials of degree `n` with `|a_j| ≤ C` for all `j < n`. -/
def BoundedMonic (n : ℕ) (B : ℝ) (P : ℂ[X]) : Prop :=
  P.Monic ∧ P.natDegree = n ∧ ∀ j < n, ‖P.coeff j‖ ≤ B

/-- `𝒵_mod`: the multiset sum of the roots of `P_k = P - a_k z^k`, for `k = 0, …, deg P`. -/
noncomputable def modRoots (P : ℂ[X]) : Multiset ℂ :=
  ∑ k ∈ Finset.range (P.natDegree + 1), (P - C (P.coeff k) * X ^ k).roots

/-- `ζ` is far from the roots of `P`: `dist(ζ, Z(P)) > ε`. -/
def IsFar (P : ℂ[X]) (ε : ℝ) (ζ : ℂ) : Prop :=
  ∀ w ∈ P.roots, ε < ‖ζ - w‖

open Classical in
/-- The proportion of far modified roots: `#{ζ ∈ 𝒵_mod : dist(ζ, Z(P)) > ε} / N_total`. -/
noncomputable def farProportion (P : ℂ[X]) (ε : ℝ) : ℝ :=
  (((modRoots P).filter (IsFar P ε)).card : ℝ) / ((modRoots P).card : ℝ)

/-- For every `C > 0`, `ε > 0` and every sequence `P⁽ⁿ⁾ ∈ 𝒫ₙ(C)`, the proportion of modified
roots at distance more than `ε` from the roots of `P⁽ⁿ⁾` tends to `0` as `n → ∞`. -/
theorem main : ∀ B : ℝ, 0 < B → ∀ ε : ℝ, 0 < ε → ∀ P : ℕ → ℂ[X],
    (∀ n, BoundedMonic n B (P n)) →
    Tendsto (fun n => farProportion (P n) ε) atTop (𝓝 0) := by
  sorry

end OMA.S_mse_5120935
