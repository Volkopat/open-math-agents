import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2
import Mathlib.NumberTheory.Bertrand
import Mathlib.Data.ZMod.Basic

/-!
# Prime-cyclic reduction at the convergent-Bertrand density threshold

This reduction proves `OMA.R_Erdos142_erdos_142_variants_lower_R2.H1` from two purely
finite-field (`ZMod p`) density bounds at the sharp convergent-Bertrand threshold
`C * p / (log p * (log log p)^2)`, split into `k = 3` (`H1`, known by Bloom-Sisask /
Kelley-Meka) and `k >= 4` (`H2`), via:
1. Elementary telescoping convergence of `∑ ((j + 3) * (log (j + 3))^2)⁻¹`.
2. Divergent reciprocal sum on 4-adic blocks forcing infinitely many dense block slices.
3. Bertrand-prime (`2 * 4^j < p <= 4 * 4^j`) Freiman embedding `[1, 4^j] ↪ ZMod p`.
-/

namespace OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R3

open Filter Real
open scoped Topology

/-- Prime-cyclic 3-AP-free density bound at the convergent-Bertrand threshold. -/
def H1 : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ᶠ p : ℕ in atTop, p.Prime → ∀ E : Finset (ZMod p),
    (¬ ∃ a d : ZMod p, d ≠ 0 ∧ ∀ i : ℕ, i < 3 → a + (i : ZMod p) * d ∈ E) →
    (E.card : ℝ) ≤ C * (p : ℝ) / (Real.log (p : ℝ) * Real.log (Real.log (p : ℝ)) ^ 2)

/-- Prime-cyclic k-AP-free density bound for k >= 4 at the convergent-Bertrand threshold. -/
def H2 : Prop :=
  ∀ k : ℕ, 4 ≤ k → ∃ C : ℝ, 0 < C ∧ ∀ᶠ p : ℕ in atTop, p.Prime → ∀ E : Finset (ZMod p),
    (¬ ∃ a d : ZMod p, d ≠ 0 ∧ ∀ i : ℕ, i < k → a + (i : ZMod p) * d ∈ E) →
    (E.card : ℝ) ≤ C * (p : ℝ) / (Real.log (p : ℝ) * Real.log (Real.log (p : ℝ)) ^ 2)

lemma bertrand_series_summable :
    Summable (fun j : ℕ => (((j : ℝ) + 3) * Real.log ((j : ℝ) + 3) ^ 2)⁻¹) := by
  refine summable_of_sum_range_le (c := (Real.log 2)⁻¹) (fun j => ?_) (fun N => ?_)
  · have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    have h1 : (1 : ℝ) ≤ (j : ℝ) + 3 := by linarith
    have hl : 0 ≤ Real.log ((j : ℝ) + 3) := Real.log_nonneg h1
    positivity
  · have hstep : ∀ j : ℕ,
        (((j : ℝ) + 3) * Real.log ((j : ℝ) + 3) ^ 2)⁻¹ ≤
          (Real.log ((j : ℝ) + 2))⁻¹ - (Real.log (((j + 1 : ℕ) : ℝ) + 2))⁻¹ := by
      intro j
      set x : ℝ := (j : ℝ) + 2
      have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
      have hx2 : 2 ≤ x := by dsimp [x]; linarith
      have hx_pos : 0 < x := by linarith
      have hx1_pos : 0 < x + 1 := by linarith
      have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
      have hlogx1 : 0 < Real.log (x + 1) := Real.log_pos (by linarith)
      have hexp : x / (x + 1) ≤ Real.exp (- (1 / (x + 1))) := by
        have h := Real.add_one_le_exp (- (1 / (x + 1)))
        have heq : - (1 / (x + 1)) + 1 = x / (x + 1) := by
          field_simp [hx1_pos.ne']
          ring
        rwa [heq] at h
      have hlog_div : Real.log (x / (x + 1)) ≤ - (1 / (x + 1)) := by
        have h := Real.log_le_log (div_pos hx_pos hx1_pos) hexp
        rwa [Real.log_exp] at h
      have hdiff : 1 / (x + 1) ≤ Real.log (x + 1) - Real.log x := by
        rw [Real.log_div hx_pos.ne' hx1_pos.ne'] at hlog_div
        linarith
      have hprod_pos : 0 < Real.log x * Real.log (x + 1) := mul_pos hlogx hlogx1
      have hle1 : 1 / ((x + 1) * Real.log (x + 1) ^ 2) ≤
          1 / ((x + 1) * (Real.log x * Real.log (x + 1))) := by
        apply one_div_le_one_div_of_le (mul_pos hx1_pos hprod_pos)
        have hll : Real.log x ≤ Real.log (x + 1) := Real.log_le_log hx_pos (by linarith)
        rw [sq]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hll hlogx1.le) hx1_pos.le
      have hle2 : 1 / ((x + 1) * (Real.log x * Real.log (x + 1))) ≤
          (Real.log (x + 1) - Real.log x) / (Real.log x * Real.log (x + 1)) := by
        have hsplit : 1 / ((x + 1) * (Real.log x * Real.log (x + 1))) =
            (1 / (x + 1)) / (Real.log x * Real.log (x + 1)) := by
          field_simp [hx1_pos.ne', hlogx.ne', hlogx1.ne']
        rw [hsplit]
        exact div_le_div_of_nonneg_right hdiff hprod_pos.le
      have htel : (Real.log (x + 1) - Real.log x) / (Real.log x * Real.log (x + 1)) =
          (Real.log x)⁻¹ - (Real.log (x + 1))⁻¹ := by
        field_simp [hlogx.ne', hlogx1.ne']
      have hx_succ : ((j + 1 : ℕ) : ℝ) + 2 = x + 1 := by dsimp [x]; push_cast; ring
      have hx_three : (j : ℝ) + 3 = x + 1 := by dsimp [x]; ring
      rw [hx_three, hx_succ, ← one_div]
      exact (hle1.trans hle2).trans_eq htel
    calc
      ∑ j ∈ Finset.range N, (((j : ℝ) + 3) * Real.log ((j : ℝ) + 3) ^ 2)⁻¹
        ≤ ∑ j ∈ Finset.range N,
            ((Real.log ((j : ℝ) + 2))⁻¹ - (Real.log (((j + 1 : ℕ) : ℝ) + 2))⁻¹) :=
          Finset.sum_le_sum fun j _ => hstep j
      _ = (Real.log (((0 : ℕ) : ℝ) + 2))⁻¹ - (Real.log ((N : ℝ) + 2))⁻¹ :=
          Finset.sum_range_sub' (fun j : ℕ => (Real.log ((j : ℝ) + 2))⁻¹) N
      _ ≤ (Real.log 2)⁻¹ := by
          have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
          have hNlog : 0 ≤ (Real.log ((N : ℝ) + 2))⁻¹ :=
            inv_nonneg.mpr (Real.log_nonneg (by linarith))
          simp only [Nat.cast_zero, zero_add]
          linarith

lemma sum_biUnion_image_inv_le (N : ℕ) (B : ℕ → Finset ℕ) :
    ∑ n ∈ (Finset.range N).biUnion (fun j => (B j).image (fun b : ℕ => 4 * 4 ^ j + b)),
        (n : ℝ)⁻¹ ≤
      ∑ j ∈ Finset.range N, ((B j).card : ℝ) / (4 : ℝ) ^ j := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.range_add_one, Finset.biUnion_insert, Finset.sum_insert Finset.notMem_range_self]
    have hunion :
        ∑ n ∈ (B N).image (fun b : ℕ => 4 * 4 ^ N + b) ∪
            (Finset.range N).biUnion (fun j => (B j).image (fun b : ℕ => 4 * 4 ^ j + b)),
              (n : ℝ)⁻¹ ≤
          (∑ n ∈ (B N).image (fun b : ℕ => 4 * 4 ^ N + b), (n : ℝ)⁻¹) +
            ∑ n ∈ (Finset.range N).biUnion (fun j => (B j).image (fun b : ℕ => 4 * 4 ^ j + b)),
              (n : ℝ)⁻¹ := by
      let s := (B N).image (fun b : ℕ => 4 * 4 ^ N + b)
      let t := (Finset.range N).biUnion (fun j => (B j).image (fun b : ℕ => 4 * 4 ^ j + b))
      change ∑ n ∈ s ∪ t, (n : ℝ)⁻¹ ≤ (∑ n ∈ s, (n : ℝ)⁻¹) + ∑ n ∈ t, (n : ℝ)⁻¹
      rw [← Finset.union_sdiff_self_eq_union, Finset.sum_union disjoint_sdiff_self_right]
      have hsub : ∑ n ∈ t \ s, (n : ℝ)⁻¹ ≤ ∑ n ∈ t, (n : ℝ)⁻¹ :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset (fun _ _ _ => by positivity)
      linarith
    have himg : ∑ n ∈ (B N).image (fun b : ℕ => 4 * 4 ^ N + b), (n : ℝ)⁻¹ ≤
        ((B N).card : ℝ) / (4 : ℝ) ^ N := by
      calc
        ∑ n ∈ (B N).image (fun b : ℕ => 4 * 4 ^ N + b), (n : ℝ)⁻¹
          ≤ ∑ b ∈ B N, ((4 * 4 ^ N + b : ℕ) : ℝ)⁻¹ :=
            Finset.sum_image_le_of_nonneg (fun _ _ => by positivity)
        _ ≤ ∑ _b ∈ B N, ((4 : ℝ) ^ N)⁻¹ := by
            refine Finset.sum_le_sum fun b _ => ?_
            have hpos : (0 : ℝ) < (4 : ℝ) ^ N := by positivity
            have h1 : 4 ^ N ≤ 4 * 4 ^ N + b := by omega
            exact inv_anti₀ hpos (by exact_mod_cast h1)
        _ = ((B N).card : ℝ) / (4 : ℝ) ^ N := by simp [div_eq_mul_inv]
    linarith

lemma not_summable_slices_of_not_summable_indicator
    {A : Set ℕ}
    (hdiv : ¬ Summable (A.indicator (fun n : ℕ => (n : ℝ)⁻¹)))
    (B : ℕ → Finset ℕ)
    (hB_mem : ∀ x ∈ A, ∃ j : ℕ, ∃ b ∈ B j, x = 4 * 4 ^ j + b) :
    ¬ Summable (fun j : ℕ => ((B j).card : ℝ) / (4 : ℝ) ^ j) := by
  intro hsum
  apply hdiv
  refine summable_of_sum_range_le (c := ∑' j : ℕ, ((B j).card : ℝ) / (4 : ℝ) ^ j)
    (fun n => Set.indicator_nonneg (fun _ _ => by positivity) n) (fun N => ?_)
  let U : Finset ℕ :=
    (Finset.range N).biUnion (fun j => (B j).image (fun b : ℕ => 4 * 4 ^ j + b))
  have hpt : ∀ n ∈ Finset.range N,
      A.indicator (fun m : ℕ => (m : ℝ)⁻¹) n ≤ if n ∈ U then (n : ℝ)⁻¹ else 0 := by
    intro n hnN
    by_cases hnA : n ∈ A
    · obtain ⟨j, b, hb, hneq⟩ := hB_mem n hnA
      have hjlt : j < 4 ^ j := Nat.lt_pow_self (by decide : 1 < 4)
      have hnlt : n < N := Finset.mem_range.mp hnN
      have hjN : j < N := by omega
      have hnU : n ∈ U := Finset.mem_biUnion.mpr
        ⟨j, Finset.mem_range.mpr hjN, hneq ▸ Finset.mem_image_of_mem _ hb⟩
      simp [Set.indicator_of_mem hnA, hnU]
    · simp only [Set.indicator_of_notMem hnA]
      split_ifs <;> positivity
  calc
    ∑ n ∈ Finset.range N, A.indicator (fun m : ℕ => (m : ℝ)⁻¹) n
      ≤ ∑ n ∈ Finset.range N, (if n ∈ U then (n : ℝ)⁻¹ else 0) :=
        Finset.sum_le_sum hpt
    _ = ∑ n ∈ (Finset.range N).filter (· ∈ U), (n : ℝ)⁻¹ :=
        (Finset.sum_filter (· ∈ U) (fun n : ℕ => (n : ℝ)⁻¹)).symm
    _ ≤ ∑ n ∈ U, (n : ℝ)⁻¹ := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
        intro x hx
        exact (Finset.mem_filter.mp hx).2
    _ ≤ ∑ j ∈ Finset.range N, ((B j).card : ℝ) / (4 : ℝ) ^ j :=
        sum_biUnion_image_inv_le N B
    _ ≤ ∑' j : ℕ, ((B j).card : ℝ) / (4 : ℝ) ^ j :=
        hsum.sum_le_tsum (Finset.range N) (fun _ _ => by positivity)

lemma exists_large_index_of_not_summable
    {d w : ℕ → ℝ} (hd_nonneg : ∀ j, 0 ≤ d j) (hd_div : ¬ Summable d)
    (hw : Summable w) (K : ℝ) (J₀ : ℕ) :
    ∃ j : ℕ, J₀ ≤ j ∧ K * w j < d j := by
  by_contra! hle
  apply hd_div
  refine Summable.of_norm_bounded_eventually_nat (hw.mul_left K) ?_
  filter_upwards [eventually_ge_atTop J₀] with j hj
  rw [Real.norm_of_nonneg (hd_nonneg j)]
  exact hle j hj

lemma cyclic_freiman_embed {k N p : ℕ} (hk : 3 ≤ k) (hp2N : 2 * N < p)
    {S : Finset ℕ} (hS : S ⊆ Finset.Icc 1 N)
    (hno : ¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ S) :
    ∃ E : Finset (ZMod p), E.card = S.card ∧
      ¬ ∃ a d : ZMod p, d ≠ 0 ∧ ∀ i : ℕ, i < k → a + (i : ZMod p) * d ∈ E := by
  classical
  have _hp : NeZero p := ⟨by omega⟩
  let E : Finset (ZMod p) := S.image (fun x : ℕ => (x : ZMod p))
  have hinj : Set.InjOn (fun x : ℕ => (x : ZMod p)) (S : Set ℕ) := by
    intro x hx y hy hxy
    have hxN : x < p := by have := (Finset.mem_Icc.mp (hS hx)).2; omega
    have hyN : y < p := by have := (Finset.mem_Icc.mp (hS hy)).2; omega
    have hv := congrArg ZMod.val hxy
    rwa [ZMod.val_natCast_of_lt hxN, ZMod.val_natCast_of_lt hyN] at hv
  refine ⟨E, Finset.card_image_of_injOn hinj, ?_⟩
  rintro ⟨a, d, hd, hmem⟩
  let x : ℕ → ℕ := fun i => if hi : i < k then (Finset.mem_image.mp (hmem i hi)).choose else 0
  have hx_spec (i : ℕ) (hi : i < k) : x i ∈ S ∧ (x i : ZMod p) = a + (i : ZMod p) * d := by
    simpa only [x, dif_pos hi] using (Finset.mem_image.mp (hmem i hi)).choose_spec
  have hx_le (i : ℕ) (hi : i < k) : x i ≤ N := (Finset.mem_Icc.mp (hS (hx_spec i hi).1)).2
  have hx01 : x 0 ≠ x 1 := by
    intro heq
    have h0 := (hx_spec 0 (by omega)).2
    have h1 := (hx_spec 1 (by omega)).2
    rw [heq] at h0
    have hd0 : d = 0 := by
      have hsub : a + (0 : ℕ) * d = a + (1 : ℕ) * d := h0.symm.trans h1
      exact (by simpa using add_left_cancel hsub : 0 = d).symm
    exact hd hd0
  have hmid (i : ℕ) (hi2 : i + 1 + 1 < k) : x (i + 1 + 1) + x i = 2 * x (i + 1) := by
    have h0 := (hx_spec i (by omega)).2
    have h1 := (hx_spec (i + 1) (by omega)).2
    have h2 := (hx_spec (i + 1 + 1) hi2).2
    have hmod : ((x (i + 1 + 1) + x i : ℕ) : ZMod p) = ((2 * x (i + 1) : ℕ) : ZMod p) := by
      push_cast
      rw [h2, h0, h1]
      push_cast
      ring
    have hltL : x (i + 1 + 1) + x i < p := by
      have := hx_le (i + 1 + 1) hi2; have := hx_le i (by omega); omega
    have hltR : 2 * x (i + 1) < p := by
      have := hx_le (i + 1) (by omega); omega
    have hv := congrArg ZMod.val hmod
    rwa [ZMod.val_natCast_of_lt hltL, ZMod.val_natCast_of_lt hltR] at hv
  rcases lt_or_gt_of_ne hx01 with hlt | hgt
  · let δ := x 1 - x 0
    have hstep : ∀ i, (i < k → x i = x 0 + i * δ) ∧
        (i + 1 < k → x (i + 1) = x 0 + (i + 1) * δ) := by
      intro i
      induction i with
      | zero =>
        refine ⟨fun _ => by simp, fun _ => ?_⟩
        simp [δ]
        omega
      | succ i ih =>
        refine ⟨ih.2, fun hi2 => ?_⟩
        have e0 := ih.1 (by omega)
        have e1 := ih.2 (by omega)
        have em := hmid i hi2
        have hmul1 : (i + 1) * δ = i * δ + δ := Nat.succ_mul i δ
        have hmul2 : (i + 1 + 1) * δ = (i + 1) * δ + δ := Nat.succ_mul (i + 1) δ
        omega
    exact hno ⟨x 0, δ, by omega, fun i hi => (hstep i).1 hi ▸ (hx_spec i hi).1⟩
  · let δ := x 0 - x 1
    have hstep : ∀ i, (i < k → x i + i * δ = x 0) ∧
        (i + 1 < k → x (i + 1) + (i + 1) * δ = x 0) := by
      intro i
      induction i with
      | zero =>
        refine ⟨fun _ => by simp, fun _ => ?_⟩
        simp [δ]
        omega
      | succ i ih =>
        refine ⟨ih.2, fun hi2 => ?_⟩
        have e0 := ih.1 (by omega)
        have e1 := ih.2 (by omega)
        have em := hmid i hi2
        have hmul1 : (i + 1) * δ = i * δ + δ := Nat.succ_mul i δ
        have hmul2 : (i + 1 + 1) * δ = (i + 1) * δ + δ := Nat.succ_mul (i + 1) δ
        omega
    refine hno ⟨x (k - 1), δ, by omega, fun j hj => ?_⟩
    have elast := (hstep (k - 1)).1 (by omega)
    have erev := (hstep (k - 1 - j)).1 (by omega)
    have hsplit : j * δ + (k - 1 - j) * δ = (k - 1) * δ := by
      rw [← Nat.add_mul, Nat.add_sub_of_le (by omega : j ≤ k - 1)]
    have heq : x (k - 1) + j * δ = x (k - 1 - j) := by omega
    exact heq ▸ (hx_spec (k - 1 - j) (by omega)).1

theorem main : H1 → H2 → OMA.R_Erdos142_erdos_142_variants_lower_R2.H1 := by
  classical
  intro h3 h4 A hsupp hdiv k hk
  have hcyc : ∃ C : ℝ, 0 < C ∧ ∀ᶠ p : ℕ in atTop, p.Prime → ∀ E : Finset (ZMod p),
      (¬ ∃ a d : ZMod p, d ≠ 0 ∧ ∀ i : ℕ, i < k → a + (i : ZMod p) * d ∈ E) →
      (E.card : ℝ) ≤ C * (p : ℝ) / (Real.log (p : ℝ) * Real.log (Real.log (p : ℝ)) ^ 2) := by
    rcases eq_or_lt_of_le hk with rfl | hk4
    · exact h3
    · exact h4 k hk4
  obtain ⟨C, hC, hP⟩ := hcyc
  obtain ⟨P₀, hP₀⟩ := eventually_atTop.mp hP
  by_contra hnoA
  let B : ℕ → Finset ℕ := fun j => (Finset.Icc 1 (4 ^ j)).filter (fun b => 4 * 4 ^ j + b ∈ A)
  have hB_sub (j : ℕ) : B j ⊆ Finset.Icc 1 (4 ^ j) := Finset.filter_subset _ _
  have hB_mem : ∀ x ∈ A, ∃ j : ℕ, ∃ b ∈ B j, x = 4 * 4 ^ j + b := by
    intro x hx
    obtain ⟨j, hlo, hhi⟩ := hsupp x hx
    refine ⟨j, x - 4 * 4 ^ j, ?_, by omega⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
    simpa [Nat.add_sub_of_le hlo.le] using hx
  have hB_no (j : ℕ) : ¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ B j := by
    rintro ⟨a, d, hd, hmem⟩
    refine hnoA ⟨4 * 4 ^ j + a, d, hd, fun i hi => ?_⟩
    have hb := (Finset.mem_filter.mp (hmem i hi)).2
    simpa [Nat.add_assoc] using hb
  have hd_div := not_summable_slices_of_not_summable_indicator hdiv B hB_mem
  obtain ⟨j, hj, hdense⟩ := exists_large_index_of_not_summable
    (fun j => by positivity) hd_div bertrand_series_summable (32 * C) (max P₀ 3)
  have hjP : P₀ ≤ j := (le_max_left _ _).trans hj
  have hj3 : 3 ≤ j := (le_max_right _ _).trans hj
  obtain ⟨p, hp, hp2N, hp4N⟩ := Nat.exists_prime_lt_and_le_two_mul (2 * 4 ^ j) (by positivity)
  have hpP₀ : P₀ ≤ p := by
    have hjlt : j < 4 ^ j := Nat.lt_pow_self (by decide : 1 < 4)
    omega
  obtain ⟨E, hEcard, hEno⟩ := cyclic_freiman_embed hk hp2N (hB_sub j) (hB_no j)
  have hE_upper := hP₀ p hpP₀ hp E hEno
  set x : ℝ := (j : ℝ) + 3
  have hx6 : 6 ≤ x := by
    dsimp [x]
    have : (3 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj3
    linarith
  have hx_pos : 0 < x := by linarith
  have hlog4 : 1 < Real.log 4 := by
    have h4 : Real.exp 1 < (4 : ℝ) := lt_trans Real.exp_one_lt_d9 (by norm_num)
    simpa [Real.log_exp] using Real.log_lt_log (Real.exp_pos 1) h4
  have hp_ge_4j : (4 : ℝ) ^ j < (p : ℝ) := by
    have : 4 ^ j < p := by omega
    exact_mod_cast this
  have hlogp_ge : x / 2 ≤ Real.log (p : ℝ) := by
    have h4j_pos : (0 : ℝ) < (4 : ℝ) ^ j := by positivity
    have hl1 : Real.log ((4 : ℝ) ^ j) ≤ Real.log (p : ℝ) := Real.log_le_log h4j_pos hp_ge_4j.le
    rw [Real.log_pow] at hl1
    have hj3' : (3 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj3
    have hxle : x / 2 ≤ (j : ℝ) := by dsimp [x]; linarith
    have hjle : (j : ℝ) ≤ (j : ℝ) * Real.log 4 := by nlinarith
    linarith
  have hlogp_pos : 0 < Real.log (p : ℝ) := lt_of_lt_of_le (by linarith) hlogp_ge
  have hloglogp_ge : Real.log x / 2 ≤ Real.log (Real.log (p : ℝ)) := by
    have hsq : x ≤ (x / 2) ^ 2 := by nlinarith
    have hlsq : Real.log x ≤ Real.log ((x / 2) ^ 2) := Real.log_le_log hx_pos hsq
    rw [Real.log_pow, Nat.cast_ofNat] at hlsq
    have hlmono : Real.log (x / 2) ≤ Real.log (Real.log (p : ℝ)) :=
      Real.log_le_log (by linarith) hlogp_ge
    linarith
  have hlogx_pos : 0 < Real.log x := Real.log_pos (by linarith)
  have hloglogp_pos : 0 < Real.log (Real.log (p : ℝ)) := lt_of_lt_of_le (by linarith) hloglogp_ge
  have hden_ge : x * Real.log x ^ 2 / 8 ≤ Real.log (p : ℝ) * Real.log (Real.log (p : ℝ)) ^ 2 := by
    have hsq_ge : (Real.log x / 2) ^ 2 ≤ Real.log (Real.log (p : ℝ)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hloglogp_ge 2
    calc
      x * Real.log x ^ 2 / 8 = (x / 2) * (Real.log x / 2) ^ 2 := by ring
      _ ≤ Real.log (p : ℝ) * Real.log (Real.log (p : ℝ)) ^ 2 :=
          mul_le_mul hlogp_ge hsq_ge (by positivity) hlogp_pos.le
  have hp_le : (p : ℝ) ≤ 4 * (4 : ℝ) ^ j := by
    have : p ≤ 4 * 4 ^ j := by omega
    exact_mod_cast this
  have hcard_eq : (E.card : ℝ) = ((B j).card : ℝ) := by exact_mod_cast hEcard
  have hupper_B : ((B j).card : ℝ) / (4 : ℝ) ^ j ≤ 32 * C * (x * Real.log x ^ 2)⁻¹ := by
    have h4j_pos : (0 : ℝ) < (4 : ℝ) ^ j := by positivity
    rw [← hcard_eq, div_le_iff₀ h4j_pos]
    have hden_pos : 0 < x * Real.log x ^ 2 / 8 := by positivity
    calc
      (E.card : ℝ)
        ≤ C * (p : ℝ) / (Real.log (p : ℝ) * Real.log (Real.log (p : ℝ)) ^ 2) := hE_upper
      _ ≤ C * (4 * (4 : ℝ) ^ j) / (x * Real.log x ^ 2 / 8) := by
          exact div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hp_le hC.le) hden_pos hden_ge
      _ = 32 * C * (x * Real.log x ^ 2)⁻¹ * (4 : ℝ) ^ j := by
          field_simp [(show x * Real.log x ^ 2 ≠ 0 by positivity)]
          ring
  exact (not_le_of_gt hdense) hupper_B

end OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R3
