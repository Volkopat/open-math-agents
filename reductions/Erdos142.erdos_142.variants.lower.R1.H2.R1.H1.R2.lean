import OMAReductions.R_Erdos142_erdos_142_variants_lower_R1_H2_R1

-- Credit: @PianothShaveck

namespace OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R1_H1_R2

open Erdos142 Filter

/-- A log-power saving gives a summable density on the scales 4^j. -/
theorem summable_four_pow_of_log_saving (k : ℕ)
    (h : ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ N : ℕ in atTop,
      (r k N : ℝ) ≤ (N : ℝ) / (Real.log (N : ℝ)) ^ (1 + ε)) :
    Summable (fun j : ℕ ↦ (r k (4 ^ j) : ℝ) / (4 : ℝ) ^ j) := by
  obtain ⟨ε, hε, hb⟩ := h
  have hs := (Real.summable_nat_rpow_inv.mpr (show 1 < 1 + ε by linarith)).mul_right
    ((Real.log 4 ^ (1 + ε))⁻¹)
  apply hs.of_norm_bounded_eventually_nat
  filter_upwards [(tendsto_pow_atTop_atTop_of_one_lt (by decide : 1 < (4 : ℕ))).eventually hb]
    with j hj
  change (r k (4 ^ j) : ℝ) ≤ ((4 ^ j : ℕ) : ℝ) / _ at hj
  push_cast at hj
  rw [Real.log_pow, Real.mul_rpow (Nat.cast_nonneg _) (Real.log_pos (by norm_num : (1 : ℝ) < 4)).le] at hj
  rw [Real.norm_of_nonneg (by positivity), div_le_iff₀ (by positivity)]
  simpa only [div_eq_mul_inv, mul_inv_rev, mul_comm, mul_left_comm, mul_assoc] using hj

/-- The endpoint and higher-length log savings together control every requested series. -/
theorem summable_four_pow_of_length_cases
    (h5 : ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ N : ℕ in atTop,
      (r 5 N : ℝ) ≤ (N : ℝ) / (Real.log (N : ℝ)) ^ (1 + ε))
    (h6 : ∀ k : ℕ, 6 ≤ k → ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ N : ℕ in atTop,
      (r k N : ℝ) ≤ (N : ℝ) / (Real.log (N : ℝ)) ^ (1 + ε)) :
    ∀ k : ℕ, 5 ≤ k → Summable (fun j : ℕ ↦ (r k (4 ^ j) : ℝ) / (4 : ℝ) ^ j) := by
  intro k hk
  apply summable_four_pow_of_log_saving
  rcases eq_or_lt_of_le hk with rfl | hlt
  · exact h5
  · exact h6 k hlt

/-- A square-root density increment at length five, with explicit control of interval loss. -/
def H1 : Prop :=
  ∃ D L T : ℝ, 0 < D ∧ ∀ (N : ℕ) (S : Finset ℕ),
    2 ≤ N → S ⊆ Finset.Icc 1 N → 0 < S.card →
    (¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < 5, a + i * d ∈ S) →
    let p := max 2 (Real.log (2 * (N : ℝ) / (S.card : ℝ)))
    T < p → L * Real.sqrt p ≤ Real.log (Real.log (N : ℝ)) →
    ∃ a q M : ℕ, 0 < q ∧ 2 ≤ M ∧
      (∀ i ∈ Finset.Icc 1 M, a + (i - 1) * q ∈ Finset.Icc 1 N) ∧
      let U := (Finset.Icc 1 M).filter (fun i ↦ a + (i - 1) * q ∈ S)
      let p' := max 2 (Real.log (2 * (M : ℝ) / (U.card : ℝ)))
      0 < U.card ∧ p' ≤ p / 2 ∧
        Real.log (Real.log (N : ℝ)) ≤ Real.log (Real.log (M : ℝ)) + D * Real.sqrt p

/-- The same increment for each length at least six. -/
def H2 : Prop :=
  ∀ k : ℕ, 6 ≤ k → ∃ D L T : ℝ, 0 < D ∧ ∀ (N : ℕ) (S : Finset ℕ),
    2 ≤ N → S ⊆ Finset.Icc 1 N → 0 < S.card →
    (¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ S) →
    let p := max 2 (Real.log (2 * (N : ℝ) / (S.card : ℝ)))
    T < p → L * Real.sqrt p ≤ Real.log (Real.log (N : ℝ)) →
    ∃ a q M : ℕ, 0 < q ∧ 2 ≤ M ∧
      (∀ i ∈ Finset.Icc 1 M, a + (i - 1) * q ∈ Finset.Icc 1 N) ∧
      let U := (Finset.Icc 1 M).filter (fun i ↦ a + (i - 1) * q ∈ S)
      let p' := max 2 (Real.log (2 * (M : ℝ) / (U.card : ℝ)))
      0 < U.card ∧ p' ≤ p / 2 ∧
        Real.log (Real.log (N : ℝ)) ≤ Real.log (Real.log (M : ℝ)) + D * Real.sqrt p

/-- Halving the logarithmic density parameter pays for the loss on the log-log scale. -/
lemma sqrt_budget {p s D C : ℝ} (hp : 2 ≤ p) (hs : 0 ≤ s) (hhalf : s ≤ p / 2)
    (hD : 0 < D) (hC : 4 * D ≤ C) :
    s + 1 ≤ p ∧ C * Real.sqrt s + D * Real.sqrt p ≤ C * Real.sqrt p := by
  have hp0 : 0 ≤ p := by linarith
  have hroot : Real.sqrt s ≤ (3 / 4) * Real.sqrt p := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith [Real.sq_sqrt hp0]
  constructor
  · linarith
  · nlinarith only [mul_le_mul_of_nonneg_left hroot (by linarith : 0 ≤ C),
      mul_le_mul_of_nonneg_right hC (Real.sqrt_nonneg p)]

theorem main : H1 → H2 → OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R1.H1 := by
  intro h5 h6 k hk
  let m := max k 5
  have hm : ∃ D L T : ℝ, 0 < D ∧ ∀ (N : ℕ) (S : Finset ℕ),
    2 ≤ N → S ⊆ Finset.Icc 1 N → 0 < S.card →
    (¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < m, a + i * d ∈ S) →
    let p := max 2 (Real.log (2 * (N : ℝ) / (S.card : ℝ)))
    T < p → L * Real.sqrt p ≤ Real.log (Real.log (N : ℝ)) →
    ∃ a q M : ℕ, 0 < q ∧ 2 ≤ M ∧
      (∀ i ∈ Finset.Icc 1 M, a + (i - 1) * q ∈ Finset.Icc 1 N) ∧
      let U := (Finset.Icc 1 M).filter (fun i ↦ a + (i - 1) * q ∈ S)
      let p' := max 2 (Real.log (2 * (M : ℝ) / (U.card : ℝ)))
      0 < U.card ∧ p' ≤ p / 2 ∧
        Real.log (Real.log (N : ℝ)) ≤ Real.log (Real.log (M : ℝ)) + D * Real.sqrt p := by
    by_cases he : m = 5
    · rw [he]; exact h5
    · exact h6 m (by dsimp [m] at he ⊢; omega)
  obtain ⟨D, L, T, hD, hstep⟩ := hm
  let C := max L (4 * D)
  have hCD : 4 * D ≤ C := le_max_right _ _
  refine ⟨1 / 2, C, T, 0, by norm_num, by norm_num, by linarith, ?_⟩
  intro R hR N S hN hS hcard hfree p hT hbudget
  rw [← Real.sqrt_eq_rpow] at hbudget
  have hfree' : ¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < m, a + i * d ∈ S := by
    rintro ⟨a, d, hd, ha⟩
    exact hfree ⟨a, d, hd, fun i hi ↦ ha i (hi.trans_le (le_max_left _ _))⟩
  have hsize : L * Real.sqrt p ≤ Real.log (Real.log (N : ℝ)) := by
    linarith [mul_le_mul_of_nonneg_right (show L ≤ C from le_max_left _ _) (Real.sqrt_nonneg p)]
  obtain ⟨a, q, M, hq, hM, hsub, hU, hhalf, hloss⟩ :=
    hstep N S hN hS hcard hfree' hT hsize
  refine ⟨a, q, M, hq, hM, hsub, hU, ?_⟩
  obtain ⟨hdrop, hpay⟩ := sqrt_budget (show 2 ≤ p from le_max_left _ _)
    (zero_le_two.trans (le_max_left _ _)) hhalf hD hCD
  refine ⟨hdrop, ?_⟩
  rw [← Real.sqrt_eq_rpow]
  linarith

end OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R1_H1_R2

