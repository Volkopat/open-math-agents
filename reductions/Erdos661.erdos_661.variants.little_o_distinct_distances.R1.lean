import FormalConjectures.ErdosProblems.«661»

/-!
Reduction `Erdos661.erdos_661.variants.little_o_distinct_distances.R1` of Erdős Problem 661
(`little_o_distinct_distances`, USD 50 open Erdős prize problem in discrete geometry).
Credit: @B221393

- `H1`: Main Erdős Problem 661 cross-distance conjecture:
  `minimalCrossDistances R^2 n = o(n / sqrt(log n))`.
- `H2`: Erdős Problem 89 distinct-distances lower bound conjecture:
  `n / sqrt(log n) << minimalDistinctDistances R^2 (2 * n)`.
- `main`: Converts the explicit asymptotic lower bound `H2` into a `Filter.atTop` `IsBigO`
  bound with constant `c⁻¹` (for `n >= 2` where `n / sqrt(log n) >= 0`), and composes with
  `H1` via `Asymptotics.IsLittleO.trans_isBigO`.
-/

namespace OMA.R_Erdos661_erdos_661_variants_little_o_distinct_distances_R1

open Filter Asymptotics

/-- Main Erdős Problem 661 cross-distance conjecture: there exist bipartite configurations
of `n + n` distinct points in `R^2` determining `o(n / sqrt(log n))` cross-distances. -/
def H1 : Prop :=
  (fun n : ℕ => (Erdos661.minimalCrossDistances (EuclideanSpace ℝ (Fin 2)) n : ℝ)) =o[atTop]
    (fun n : ℕ => (n : ℝ) / (n : ℝ).log.sqrt)

/-- Erdős Problem 89 distinct-distances lower bound conjecture: any `2n` points in `R^2`
determine at least `c * n / sqrt(log n)` distinct distances for a positive constant `c`. -/
def H2 : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
    c * ((n : ℝ) / (n : ℝ).log.sqrt) ≤
      (minimalDistinctDistances (EuclideanSpace ℝ (Fin 2)) (2 * n) : ℝ)

theorem main : H1 → H2 → type_of% @Erdos661.erdos_661.variants.little_o_distinct_distances := by
  intro h1 h2
  rcases h2 with ⟨c, hc_pos, hev⟩
  have hbigO : (fun n : ℕ => (n : ℝ) / (n : ℝ).log.sqrt) =O[atTop]
      (fun n : ℕ => (minimalDistinctDistances (EuclideanSpace ℝ (Fin 2)) (2 * n) : ℝ)) := by
    rw [Asymptotics.isBigO_iff]
    refine ⟨c⁻¹, ?_⟩
    filter_upwards [hev, Filter.eventually_ge_atTop (2 : ℕ)] with n hn h2n
    have hlog_nn : 0 ≤ (n : ℝ).log := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
    have hq_nn : 0 ≤ (n : ℝ) / (n : ℝ).log.sqrt :=
      div_nonneg (Nat.cast_nonneg n) (Real.sqrt_nonneg _)
    have hf_nn : 0 ≤ (minimalDistinctDistances (EuclideanSpace ℝ (Fin 2)) (2 * n) : ℝ) :=
      Nat.cast_nonneg _
    rw [Real.norm_of_nonneg hq_nn, Real.norm_of_nonneg hf_nn]
    have hmul : (n : ℝ) / (n : ℝ).log.sqrt ≤
        c⁻¹ * (minimalDistinctDistances (EuclideanSpace ℝ (Fin 2)) (2 * n) : ℝ) := by
      have h1' : c * ((n : ℝ) / (n : ℝ).log.sqrt) ≤
          (minimalDistinctDistances (EuclideanSpace ℝ (Fin 2)) (2 * n) : ℝ) := hn
      have h2' := mul_le_mul_of_nonneg_left h1' (inv_nonneg.mpr (le_of_lt hc_pos))
      rwa [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hc_pos), one_mul] at h2'
    exact hmul
  exact h1.trans_isBigO hbigO

end OMA.R_Erdos661_erdos_661_variants_little_o_distinct_distances_R1
