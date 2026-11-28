import OMAReductions.R_Erdos142_erdos_142_variants_lower_R3
import Mathlib.NumberTheory.Bertrand
import Mathlib.Data.ZMod.Basic

/-!
# Window reciprocal decay from the sharp o(p / log p) bound in ZMod p

This reduction proves `OMA.R_Erdos142_erdos_142_variants_lower_R3.H2` from two purely
finite-field (`ZMod p`) logarithmic-saving bounds `(E.card : ℝ) <= δ * p / log p`, split into
`k = 4` (`H1`) and `k >= 5` (`H2`), via:
1. Block-slice reciprocal upper bound `∑ x ∈ S, x⁻¹ <= (n / 4) * (r k (4^n) / 4^n)` using
   pairwise disjointness and `blockDensity_antitone` from `R3`.
2. Bertrand-prime (`2 * 4^n < p <= 4 * 4^n`) Freiman embedding `[1, 4^n] ↪ ZMod p` with exact
   logarithmic cancellation `(n / 4) * (4 * δ / (n * log 4)) = ε` at `δ = ε * log 4`.
-/

namespace OMA.R_Erdos142_erdos_142_variants_lower_R3_H2_R3

open Erdos142 Finset Filter Real
open OMA.R_Erdos142_erdos_142_variants_lower_R3
open scoped Topology

/-- Sharp o(p / log p) bound in ZMod p for 4-AP-free subsets. -/
def H1 : Prop :=
  ∀ δ : ℝ, 0 < δ → ∀ᶠ p : ℕ in atTop, p.Prime → ∀ E : Finset (ZMod p),
    (¬ ∃ a d : ZMod p, d ≠ 0 ∧ ∀ i : ℕ, i < 4 → a + (i : ZMod p) * d ∈ E) →
    (E.card : ℝ) ≤ δ * (p : ℝ) / Real.log (p : ℝ)

/-- Sharp o(p / log p) bound in ZMod p for k-AP-free subsets (k >= 5). -/
def H2 : Prop :=
  ∀ k : ℕ, 5 ≤ k → ∀ δ : ℝ, 0 < δ → ∀ᶠ p : ℕ in atTop, p.Prime → ∀ E : Finset (ZMod p),
    (¬ ∃ a d : ZMod p, d ≠ 0 ∧ ∀ i : ℕ, i < k → a + (i : ZMod p) * d ∈ E) →
    (E.card : ℝ) ≤ δ * (p : ℝ) / Real.log (p : ℝ)

lemma window_reciprocal_le {k n : ℕ} (hk : 1 < k) (S : Finset ℕ)
    (hw : ∀ x ∈ S, ∃ j ∈ Finset.Ico n (2 * n), 4 * 4 ^ j < x ∧ x ≤ 5 * 4 ^ j)
    (hf : ¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ S) :
    (∑ x ∈ S, (x : ℝ)⁻¹) ≤ (n : ℝ) * ((r k (4 ^ n) : ℝ) / (4 : ℝ) ^ n) / 4 := by
  let B : ℕ → Finset ℕ := fun j => (Finset.Icc 1 (4 ^ j)).filter (fun b => 4 * 4 ^ j + b ∈ S)
  have hsub (j : ℕ) : B j ⊆ Finset.Icc 1 (4 ^ j) := Finset.filter_subset _ _
  let block : ℕ → Finset ℕ := fun j => (B j).map (addLeftEmbedding (4 * 4 ^ j))
  have hcover : S ⊆ (Finset.Ico n (2 * n)).biUnion block := by
    intro x hx
    obtain ⟨j, hj, hlo, hhi⟩ := hw x hx
    refine Finset.mem_biUnion.mpr ⟨j, hj, Finset.mem_map.mpr ⟨x - 4 * 4 ^ j, ?_, ?_⟩⟩
    · refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
      simpa [Nat.add_sub_of_le hlo.le] using hx
    · change 4 * 4 ^ j + (x - 4 * 4 ^ j) = x
      omega
  have hsize (j : ℕ) : (B j).card ≤ r k (4 ^ j) := by
    apply card_le_r (hsub j) ((apFree_iff hk).mpr ?_)
    rintro ⟨a, d, hd, hmem⟩
    refine hf ⟨4 * 4 ^ j + a, d, hd, fun i hi => ?_⟩
    simpa [Nat.add_assoc] using (Finset.mem_filter.mp (hmem i hi)).2
  have hblock_sum (j : ℕ) (hj : j ∈ Finset.Ico n (2 * n)) :
      (∑ x ∈ block j, (x : ℝ)⁻¹) ≤ ((r k (4 ^ n) : ℝ) / (4 : ℝ) ^ n) / 4 := by
    have hnj : n ≤ j := (Finset.mem_Ico.mp hj).1
    have h4j_pos : (0 : ℝ) < 4 * (4 : ℝ) ^ j := by positivity
    calc
      (∑ x ∈ block j, (x : ℝ)⁻¹)
        ≤ ∑ _x ∈ block j, (4 * (4 : ℝ) ^ j)⁻¹ := by
          refine Finset.sum_le_sum fun x hx => ?_
          have hb := mem_shiftBlock_bounds (hsub j) hx
          have hle : 4 * (4 : ℝ) ^ j ≤ (x : ℝ) := by exact_mod_cast hb.1.le
          exact inv_anti₀ h4j_pos hle
      _ = ((B j).card : ℝ) / (4 * (4 : ℝ) ^ j) := by
          simp [block, div_eq_mul_inv]
      _ ≤ (r k (4 ^ j) : ℝ) / (4 * (4 : ℝ) ^ j) := by
          have hc : ((B j).card : ℝ) ≤ (r k (4 ^ j) : ℝ) := by exact_mod_cast hsize j
          exact div_le_div_of_nonneg_right hc h4j_pos.le
      _ = ((r k (4 ^ j) : ℝ) / (4 : ℝ) ^ j) / 4 := by ring
      _ ≤ ((r k (4 ^ n) : ℝ) / (4 : ℝ) ^ n) / 4 :=
          div_le_div_of_nonneg_right (blockDensity_antitone hk hnj) (by norm_num)
  have hcardI : (Finset.Ico n (2 * n)).card = n := by
    rw [Nat.card_Ico]
    omega
  calc
    (∑ x ∈ S, (x : ℝ)⁻¹)
      ≤ ∑ x ∈ (Finset.Ico n (2 * n)).biUnion block, (x : ℝ)⁻¹ :=
        Finset.sum_le_sum_of_subset_of_nonneg hcover (fun _ _ _ => by positivity)
    _ = ∑ j ∈ Finset.Ico n (2 * n), ∑ x ∈ block j, (x : ℝ)⁻¹ :=
        Finset.sum_biUnion (shiftBlocks_pairwiseDisjoint (Finset.Ico n (2 * n)) B hsub)
    _ ≤ ∑ _j ∈ Finset.Ico n (2 * n), ((r k (4 ^ n) : ℝ) / (4 : ℝ) ^ n) / 4 :=
        Finset.sum_le_sum hblock_sum
    _ = (n : ℝ) * ((r k (4 ^ n) : ℝ) / (4 : ℝ) ^ n) / 4 := by
        simp [hcardI, mul_div_assoc]

lemma cyclic_freiman_embed {k N p : ℕ} (hk : 4 ≤ k) (hp2N : 2 * N < p)
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

theorem main : H1 → H2 → OMA.R_Erdos142_erdos_142_variants_lower_R3.H2 := by
  intro h4 h5 k hk ε hε
  have hk1 : 1 < k := by omega
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  let δ : ℝ := ε * Real.log 4
  have hδ : 0 < δ := mul_pos hε hlog4
  have hcyc : ∀ᶠ p : ℕ in atTop, p.Prime → ∀ E : Finset (ZMod p),
      (¬ ∃ a d : ZMod p, d ≠ 0 ∧ ∀ i : ℕ, i < k → a + (i : ZMod p) * d ∈ E) →
      (E.card : ℝ) ≤ δ * (p : ℝ) / Real.log (p : ℝ) := by
    rcases eq_or_lt_of_le hk with rfl | hk5
    · exact h4 δ hδ
    · exact h5 k hk5 δ hδ
  obtain ⟨P₀, hP₀⟩ := eventually_atTop.mp hcyc
  filter_upwards [eventually_ge_atTop (max P₀ 1)] with n hn S hw hf
  have hnP : P₀ ≤ n := (le_max_left _ _).trans hn
  have hn1 : 1 ≤ n := (le_max_right _ _).trans hn
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  obtain ⟨p, hp, hp2N, hp4N⟩ := Nat.exists_prime_lt_and_le_two_mul (2 * 4 ^ n) (by positivity)
  have hpP₀ : P₀ ≤ p := by
    have hnlt : n < 4 ^ n := Nat.lt_pow_self (by decide : 1 < 4)
    omega
  obtain ⟨T, hTsub, hTfree, hTcard⟩ := exists_maximizer hk1 (4 ^ n)
  obtain ⟨E, hEcard, hEno⟩ := cyclic_freiman_embed hk hp2N hTsub ((apFree_iff hk1).mp hTfree)
  have hE := hP₀ p hpP₀ hp E hEno
  have hr_eq : (r k (4 ^ n) : ℝ) = (E.card : ℝ) := by
    exact_mod_cast hTcard.trans hEcard.symm
  have hp_ge_4n : (4 : ℝ) ^ n ≤ (p : ℝ) := by
    have : 4 ^ n ≤ p := by omega
    exact_mod_cast this
  have h4n_pos : (0 : ℝ) < (4 : ℝ) ^ n := by positivity
  have hlogp_ge : (n : ℝ) * Real.log 4 ≤ Real.log (p : ℝ) := by
    simpa [Real.log_pow] using Real.log_le_log h4n_pos hp_ge_4n
  have hnlog4_pos : 0 < (n : ℝ) * Real.log 4 := mul_pos hn_pos hlog4
  have hp_le : (p : ℝ) ≤ 4 * (4 : ℝ) ^ n := by
    have : p ≤ 4 * 4 ^ n := by omega
    exact_mod_cast this
  have hr_bound : (r k (4 ^ n) : ℝ) / (4 : ℝ) ^ n ≤ 4 * ε / (n : ℝ) := by
    rw [hr_eq, div_le_iff₀ h4n_pos]
    calc
      (E.card : ℝ)
        ≤ δ * (p : ℝ) / Real.log (p : ℝ) := hE
      _ ≤ δ * (4 * (4 : ℝ) ^ n) / ((n : ℝ) * Real.log 4) :=
          div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hp_le hδ.le) hnlog4_pos hlogp_ge
      _ = 4 * ε / (n : ℝ) * (4 : ℝ) ^ n := by
          dsimp [δ]
          field_simp [hn_pos.ne', hlog4.ne']
  calc
    (∑ x ∈ S, (x : ℝ)⁻¹)
      ≤ (n : ℝ) * ((r k (4 ^ n) : ℝ) / (4 : ℝ) ^ n) / 4 := window_reciprocal_le hk1 S hw hf
    _ ≤ (n : ℝ) * (4 * ε / (n : ℝ)) / 4 := by
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hr_bound hn_pos.le) (by norm_num)
    _ = ε := by
        field_simp [hn_pos.ne']

end OMA.R_Erdos142_erdos_142_variants_lower_R3_H2_R3
