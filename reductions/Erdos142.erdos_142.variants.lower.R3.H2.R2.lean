import OMAReductions.R_Erdos142_erdos_142_variants_lower_R3

/-!
# Window decay for long progressions from the super-polylogarithmic density bound

The target is the reciprocal-mass decay on windows of geometric blocks for sets without
k-term progressions, for every k at least four. It is reduced to the two density statements
r k N ≤ N exp(-c (log log N)^A) with A > 1, for k = 4 and for k at least five. They are word
for word the hypotheses H1 and H2 of reduction R1 of the step lower.R1.H2.R1.H1 (pull request
29521), so proofs of those two bounds close this branch as well. Both follow from the
quantitative theorem of OpenAI, Quasipolynomial Bounds for Arithmetic Progressions (2026).

Everything else is proved here. A set in the window is split into its blocks. The part in the
block (4 * 4^j, 5 * 4^j] lies in [1, 5 * 4^j], so its size is at most r k (5 * 4^j), and each
reciprocal is at most 1 / (4 * 4^j). Hence the reciprocal mass of the block is at most 5/4
times the saving at scale 5 * 4^j. The saving is summable along these scales
(saving_summable), and the sum over j in [n, 2n) is a difference of partial sums of a
convergent series (window_tendsto_zero).
-/

namespace OMA.R_Erdos142_erdos_142_variants_lower_R3_H2_R2

open Erdos142 Filter
open scoped Topology

/-- A super-polylogarithmic saving for 4-term progressions. -/
def H1 : Prop :=
  ∃ A c : ℝ, 1 < A ∧ 0 < c ∧ ∀ᶠ N : ℕ in atTop,
    (r 4 N : ℝ) ≤ (N : ℝ) * Real.exp (-c * Real.log (Real.log (N : ℝ)) ^ A)

/-- The same saving for every progression length at least five. -/
def H2 : Prop :=
  ∀ k : ℕ, 5 ≤ k → ∃ A c : ℝ, 1 < A ∧ 0 < c ∧ ∀ᶠ N : ℕ in atTop,
    (r k N : ℝ) ≤ (N : ℝ) * Real.exp (-c * Real.log (Real.log (N : ℝ)) ^ A)

/-- The saving is summable along the scales 5 * 4^j. -/
lemma saving_summable : ∀ c η : ℝ, 0 < c → 0 < η →
    Summable (fun j : ℕ ↦ Real.exp (-c * (Real.log (Real.log (5 * (4 : ℝ) ^ j))) ^ (1 + η))) := by
  intro c η hc hη
  have hg : Summable (fun j : ℕ ↦ 1 / (j : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  refine Summable.of_norm_bounded_eventually_nat hg ?_
  have hlog : Tendsto (fun j : ℕ => Real.log (j : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hp := (tendsto_rpow_atTop hη).comp hlog
  filter_upwards [eventually_ge_atTop 1, hp.eventually_ge_atTop (2 / c)] with j hj hjη
  simp only [Function.comp] at hjη
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hl0 : 0 ≤ Real.log (j : ℝ) := Real.log_nonneg hj1
  have h4 : (1 : ℝ) ≤ Real.log 4 := by
    have h : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    linarith [Real.log_two_gt_d9]
  have hbig : (j : ℝ) ≤ Real.log (5 * (4 : ℝ) ^ j) := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    have h5 : 0 ≤ Real.log 5 := Real.log_nonneg (by norm_num)
    nlinarith
  have hL : Real.log j ≤ Real.log (Real.log (5 * (4 : ℝ) ^ j)) := Real.log_le_log hj0 hbig
  have hrp : Real.log j ^ (1 + η) ≤ (Real.log (Real.log (5 * (4 : ℝ) ^ j))) ^ (1 + η) :=
    Real.rpow_le_rpow hl0 hL (by linarith)
  have hsplit : Real.log j ^ (1 + η) = Real.log j * Real.log j ^ η := by
    rcases hl0.eq_or_lt with h | h
    · rw [← h, Real.zero_rpow (by linarith), zero_mul]
    · rw [Real.rpow_add h, Real.rpow_one]
  have h2 : 2 * Real.log j ≤ c * Real.log j ^ (1 + η) := by
    rw [hsplit]
    have h2' : 2 ≤ Real.log j ^ η * c := (div_le_iff₀ hc).mp hjη
    nlinarith
  have h3 := mul_le_mul_of_nonneg_left hrp hc.le
  rw [Real.norm_of_nonneg (Real.exp_nonneg _)]
  calc Real.exp (-c * (Real.log (Real.log (5 * (4 : ℝ) ^ j))) ^ (1 + η))
      ≤ Real.exp (-(2 * Real.log j)) := Real.exp_le_exp.mpr (by linarith)
    _ = 1 / (j : ℝ) ^ 2 := by
      rw [Real.exp_neg, mul_comm, Real.exp_mul, Real.exp_log hj0, Real.rpow_two, one_div]

/-- Sums of a summable sequence over the windows [n, 2n) tend to zero. -/
lemma window_tendsto_zero {f : ℕ → ℝ} (hf : Summable f) :
    Tendsto (fun n : ℕ ↦ ∑ j ∈ Finset.Ico n (2 * n), f j) atTop (𝓝 0) := by
  have h := hf.hasSum.tendsto_sum_nat
  have hdouble : Tendsto (fun n : ℕ ↦ 2 * n) atTop atTop :=
    tendsto_atTop_mono (fun n ↦ (by omega : n ≤ 2 * n)) tendsto_id
  have hsub := (h.comp hdouble).sub h
  rw [sub_self] at hsub
  refine hsub.congr (fun n ↦ ?_)
  rw [Finset.sum_Ico_eq_sub _ (by omega : n ≤ 2 * n)]
  rfl

/-- A set in the block (4 * 4^j, 5 * 4^j] with at most C * (5 * 4^j) * E elements has reciprocal
mass at most (5/4) * C * E. -/
lemma block_mass_le {j : ℕ} {T : Finset ℕ} {C E : ℝ}
    (hT : ∀ x ∈ T, 4 * 4 ^ j < x ∧ x ≤ 5 * 4 ^ j)
    (hcard : (T.card : ℝ) ≤ C * (5 * (4 : ℝ) ^ j) * E) :
    (∑ x ∈ T, (x : ℝ)⁻¹) ≤ 5 / 4 * C * E := by
  have hpos : (0 : ℝ) < 4 * (4 : ℝ) ^ j := by positivity
  have hterm : ∀ x ∈ T, (x : ℝ)⁻¹ ≤ (4 * (4 : ℝ) ^ j)⁻¹ := by
    intro x hx
    apply inv_anti₀ hpos
    exact_mod_cast (hT x hx).1.le
  calc (∑ x ∈ T, (x : ℝ)⁻¹) ≤ T.card • (4 * (4 : ℝ) ^ j)⁻¹ := Finset.sum_le_card_nsmul _ _ _ hterm
    _ = (T.card : ℝ) * (4 * (4 : ℝ) ^ j)⁻¹ := by rw [nsmul_eq_mul]
    _ ≤ C * (5 * (4 : ℝ) ^ j) * E * (4 * (4 : ℝ) ^ j)⁻¹ :=
        mul_le_mul_of_nonneg_right hcard (inv_nonneg.mpr hpos.le)
    _ = 5 / 4 * C * E := by field_simp

theorem main : H1 → H2 → OMA.R_Erdos142_erdos_142_variants_lower_R3.H2 := by
  intro h4 h5 k hk ε hε
  obtain ⟨A, c, hA, hc, hb⟩ : ∃ A c : ℝ, 1 < A ∧ 0 < c ∧ ∀ᶠ N : ℕ in atTop,
      (r k N : ℝ) ≤ (N : ℝ) * Real.exp (-c * Real.log (Real.log (N : ℝ)) ^ A) := by
    rcases eq_or_lt_of_le hk with rfl | hlt
    · exact h4
    · exact h5 k hlt
  obtain ⟨η, rfl⟩ : ∃ η : ℝ, A = 1 + η := ⟨A - 1, by ring⟩
  have hη : 0 < η := by linarith
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hb
  have htail := window_tendsto_zero (saving_summable c η hc hη)
  have hδ : (0 : ℝ) < ε / (5 / 4 * 1) := by positivity
  filter_upwards [(tendsto_order.1 htail).2 _ hδ, eventually_ge_atTop N₀] with n hn hnN S hS hfree
  have hblock : ∀ j : ℕ, n ≤ j →
      (∑ x ∈ S.filter (fun x ↦ 4 * 4 ^ j < x ∧ x ≤ 5 * 4 ^ j), (x : ℝ)⁻¹) ≤
      5 / 4 * 1 * Real.exp (-c * Real.log (Real.log (5 * (4 : ℝ) ^ j)) ^ (1 + η)) := by
    intro j hj
    refine block_mass_le (fun x hx ↦ (Finset.mem_filter.mp hx).2) ?_
    have hbig : N₀ ≤ 5 * 4 ^ j := by
      have : j < 4 ^ j := Nat.lt_pow_self (by norm_num)
      omega
    have hsub : S.filter (fun x ↦ 4 * 4 ^ j < x ∧ x ≤ 5 * 4 ^ j) ⊆ Finset.Icc 1 (5 * 4 ^ j) := by
      intro x hx
      have := (Finset.mem_filter.mp hx).2
      exact Finset.mem_Icc.mpr ⟨by omega, this.2⟩
    have hno : ¬ ∃ a d : ℕ, 0 < d ∧
        ∀ i < k, a + i * d ∈ S.filter (fun x ↦ 4 * 4 ^ j < x ∧ x ≤ 5 * 4 ^ j) := by
      rintro ⟨a, d, hd, h⟩
      exact hfree ⟨a, d, hd, fun i hi ↦ (Finset.mem_filter.mp (h i hi)).1⟩
    have hcard : ((S.filter (fun x ↦ 4 * 4 ^ j < x ∧ x ≤ 5 * 4 ^ j)).card : ℝ) ≤
        (r k (5 * 4 ^ j) : ℝ) := by
      have hfr : ((S.filter (fun x ↦ 4 * 4 ^ j < x ∧ x ≤ 5 * 4 ^ j) : Finset ℕ) : Set ℕ).IsAPOfLengthFree k :=
        (OMA.R_Erdos142_erdos_142_variants_lower_R3.apFree_iff (by omega)).mpr (by exact_mod_cast hno)
      exact_mod_cast OMA.R_Erdos142_erdos_142_variants_lower_R3.card_le_r hsub hfr
    have := hcard.trans (hN₀ (5 * 4 ^ j) hbig)
    push_cast at this
    linarith
  calc (∑ x ∈ S, (x : ℝ)⁻¹)
      ≤ ∑ x ∈ S, ∑ j ∈ Finset.Ico n (2 * n),
          (if 4 * 4 ^ j < x ∧ x ≤ 5 * 4 ^ j then (x : ℝ)⁻¹ else 0) := by
        refine Finset.sum_le_sum (fun x hx ↦ ?_)
        obtain ⟨j, hj, hP⟩ := hS x hx
        calc (x : ℝ)⁻¹ = (if 4 * 4 ^ j < x ∧ x ≤ 5 * 4 ^ j then (x : ℝ)⁻¹ else 0) := by
              rw [if_pos hP]
          _ ≤ _ := Finset.single_le_sum
              (f := fun j ↦ if 4 * 4 ^ j < x ∧ x ≤ 5 * 4 ^ j then (x : ℝ)⁻¹ else 0)
              (fun i _ ↦ by split_ifs <;> positivity) hj
    _ = ∑ j ∈ Finset.Ico n (2 * n),
          ∑ x ∈ S.filter (fun x ↦ 4 * 4 ^ j < x ∧ x ≤ 5 * 4 ^ j), (x : ℝ)⁻¹ := by
        rw [Finset.sum_comm]
        simp only [Finset.sum_filter]
    _ ≤ ∑ j ∈ Finset.Ico n (2 * n),
          5 / 4 * 1 * Real.exp (-c * Real.log (Real.log (5 * (4 : ℝ) ^ j)) ^ (1 + η)) :=
        Finset.sum_le_sum (fun j hj ↦ hblock j (Finset.mem_Ico.mp hj).1)
    _ = 5 / 4 * 1 * ∑ j ∈ Finset.Ico n (2 * n),
          Real.exp (-c * Real.log (Real.log (5 * (4 : ℝ) ^ j)) ^ (1 + η)) := by
        rw [Finset.mul_sum]
    _ ≤ 5 / 4 * 1 * (ε / (5 / 4 * 1)) := mul_le_mul_of_nonneg_left hn.le (by norm_num)
    _ = ε := by field_simp

end OMA.R_Erdos142_erdos_142_variants_lower_R3_H2_R2
