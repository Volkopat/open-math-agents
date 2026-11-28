import OMAReductions.R_Erdos142_erdos_142_variants_lower_R1_H2_R2
import Mathlib

-- Reduction Erdos142.erdos_142.variants.lower.R1.H2.R2.H1.R2 of step Erdos142.erdos_142.variants.lower.R1.H2.R2.H1
-- Credit: @mijuny
-- Connects the polylogarithmic coloring step of lower.R1.H2.R2 directly to the subquadratic
-- log-log affine density increment and qualitative Szemerédi hypotheses of lower.R1.H2.R1.

/-!
# Polylogarithmic monochromatic progressions from subquadratic affine density increment

We reduce step `lower.R1.H2.R2.H1` (monochromatic `k`-term progressions under `(⌈log N⌉₊ + 1) ^ 4`
colors for `k ≥ 4`) to:

* `H1`: subquadratic log-log budget affine density increment for sparse `k`-AP-free sets,
* `H2`: qualitative Szemerédi terminal step at fixed positive density.

Inside this file we prove:
1. Finite descent (`no_budget`) ruling out `C * p ^ β + R ≤ log (log N)`.
2. Eventual fifth-power logarithmic density saving `r k N ≤ N / (log N) ^ 5`.
3. Asymptotic ceiling comparison `((⌈log N⌉₊ + 1) ^ 4 : ℝ) < (log N) ^ 5` for `log N ≥ 16`.
4. Fiberwise coloring pigeonhole over `Fin q` on `Finset.Icc 1 N`.
5. Extraction of a positive-step monochromatic `k`-term progression from the largest color class.
-/

namespace OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R2_H1_R2

open Erdos142 Filter Finset Real
open scoped Classical Topology

/-- Sparse finite sets admit an affine density increment preserving the log-log budget. -/
def H1 : Prop :=
  ∀ k : ℕ, 4 ≤ k →
    ∃ (β C T R₀ : ℝ), 0 < β ∧ β < 1 ∧ 0 < C ∧
      ∀ R : ℝ, R₀ ≤ R → ∀ (N : ℕ) (S : Finset ℕ),
        2 ≤ N → S ⊆ Finset.Icc 1 N → 0 < S.card →
          (¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ S) →
        let p := max 2 (Real.log (2 * (N : ℝ) / (S.card : ℝ)))
        T < p → C * p ^ β + R ≤ Real.log (Real.log (N : ℝ)) →
          ∃ (a q M : ℕ), 0 < q ∧ 2 ≤ M ∧
            (∀ i ∈ Finset.Icc 1 M, a + (i - 1) * q ∈ Finset.Icc 1 N) ∧
            let U := (Finset.Icc 1 M).filter (fun i ↦ a + (i - 1) * q ∈ S)
            let p' := max 2 (Real.log (2 * (M : ℝ) / (U.card : ℝ)))
            0 < U.card ∧ p' + 1 ≤ p ∧ C * p' ^ β + R ≤ Real.log (Real.log (M : ℝ))

/-- Fixed positive density forces a progression once the interval is long enough. -/
def H2 : Prop :=
  ∀ k : ℕ, 4 ≤ k → ∀ T : ℝ, ∃ Q : ℝ, ∀ (N : ℕ) (S : Finset ℕ),
    2 ≤ N → S ⊆ Finset.Icc 1 N → 0 < S.card →
    (¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ S) →
    max 2 (Real.log (2 * (N : ℝ) / (S.card : ℝ))) ≤ T →
      Real.log (Real.log (N : ℝ)) < Q

lemma apFree_iff {A : Set ℕ} {k : ℕ} (hk : 1 < k) :
    A.IsAPOfLengthFree k ↔ ¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ A := by
  have hk' : (1 : ℕ∞) < (k : ℕ∞) := by exact_mod_cast hk
  constructor
  · rintro hA ⟨a, d, hd, hterms⟩
    let f (i : ℕ) := a + i * d
    let T := (Finset.range k).image f
    have hf : Function.Injective f := fun i j hij =>
      Nat.eq_of_mul_eq_mul_right hd (Nat.add_left_cancel hij)
    have hT : ((T : Finset ℕ) : Set ℕ) = {a + n • d | (n : ℕ) (_ : n < (k : ℕ∞))} := by
      ext x
      simp [T, f]
    have hcard : T.card = k := by simp [T, Finset.card_image_of_injective _ hf]
    have hsub : (T : Set ℕ) ⊆ A := by
      intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      exact hterms i (Finset.mem_range.mp hi)
    exact hk'.not_ge (hA _ hsub ⟨a, d, by simp [hcard], hT⟩)
  · intro hno T hsub hT
    obtain ⟨a, d, hcard, hterms⟩ := hT
    have hmem (i : ℕ) (hi : i < k) : a + i * d ∈ T := by
      rw [hterms]
      exact ⟨i, by exact_mod_cast hi, by simp⟩
    have hd : 0 < d := by
      by_contra! h
      have he : d = 0 := Nat.eq_zero_of_le_zero h
      have hs : T = {a} := by
        apply Set.Subset.antisymm
        · rw [hterms, he]
          rintro _ ⟨i, -, rfl⟩
          simp
        · apply Set.singleton_subset_iff.mpr
          simpa using hmem 0 (by omega)
      rw [hs] at hcard
      exact hk'.ne (by simpa using hcard)
    exact (hno ⟨a, d, hd, fun i hi => hsub (hmem i hi)⟩).elim

lemma card_le_r {k N : ℕ} {S : Finset ℕ} (hS : S ⊆ Finset.Icc 1 N)
    (hf : (S : Set ℕ).IsAPOfLengthFree k) : S.card ≤ r k N := by
  unfold r Set.IsAPOfLengthFree.maxCard
  refine le_csSup ?_ ⟨S, hS, hf, rfl⟩
  refine ⟨N, ?_⟩
  rintro _ ⟨U, hU, -, rfl⟩
  simpa using Finset.card_le_card hU

lemma extremizer {k : ℕ} (hk : 1 < k) (N : ℕ) :
    ∃ S : Finset ℕ, S ⊆ Finset.Icc 1 N ∧ (S : Set ℕ).IsAPOfLengthFree k ∧
      S.card = r k N := by
  let c : Set ℕ := {Finset.card S | (S) (_ : S ⊆ Finset.Icc 1 N)
    (_ : (S : Set ℕ).IsAPOfLengthFree k)}
  have hnon : c.Nonempty := by
    refine ⟨0, ∅, by simp, ?_, by simp⟩
    intro t ht hprogression
    have ht' : t = ∅ := Set.subset_empty_iff.mp (by simpa using ht)
    have hpos : 0 < (k : ℕ∞) := by exact_mod_cast (show 0 < k by omega)
    exact (Set.not_isAPOfLength_empty hpos (ht' ▸ hprogression)).elim
  have hbound : BddAbove c := by
    refine ⟨N, ?_⟩
    rintro _ ⟨S, hs, _, rfl⟩
    exact (Finset.card_mono hs).trans_eq (Nat.card_Icc 1 N)
  obtain ⟨S, hS, hfree, hcard⟩ := Nat.sSup_mem hnon hbound
  exact ⟨S, hS, hfree, hcard⟩

lemma eliminate_descent {X : Type} (p : X → ℝ) (P : X → Prop)
    (hp : ∀ x, 0 ≤ p x)
    (decrease : ∀ x, P x → ∃ y, P y ∧ p y + 1 ≤ p x) :
    ∀ x, ¬ P x := by
  suffices H : ∀ n : ℕ, ∀ x, P x → ⌊p x⌋₊ = n → False from
    fun x hx ↦ H _ x hx rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro x hx he
    obtain ⟨y, hy, hdrop⟩ := decrease x hx
    have hlt : ⌊p y⌋₊ < ⌊p x⌋₊ := (Nat.floor_lt (hp y)).mpr (by
      linarith [Nat.lt_floor_add_one (p x)])
    exact ih _ (by simpa only [he] using hlt) y hy rfl

lemma progression_preimage_free {k a q M : ℕ} {S : Finset ℕ}
    (hk : 4 ≤ k) (hq : 0 < q)
    (hfree : ¬ ∃ b d : ℕ, 0 < d ∧ ∀ i < k, b + i * d ∈ S) :
    ¬ ∃ b d : ℕ, 0 < d ∧ ∀ i < k,
      b + i * d ∈ (Finset.Icc 1 M).filter (fun j ↦ a + (j - 1) * q ∈ S) := by
  rintro ⟨b, d, hd, hAP⟩
  have hbase : b ∈ Finset.Icc 1 M := by
    simpa only [zero_mul, add_zero] using (Finset.mem_filter.mp (hAP 0 (by omega))).1
  have hb : 1 ≤ b := (Finset.mem_Icc.mp hbase).1
  refine hfree ⟨a + (b - 1) * q, d * q, Nat.mul_pos hd hq, fun i hi ↦ ?_⟩
  have hmem := (Finset.mem_filter.mp (hAP i hi)).2
  have he : b + i * d - 1 = b - 1 + i * d := by omega
  rw [he] at hmem
  simpa only [add_mul, Nat.add_assoc, Nat.mul_assoc] using hmem

lemma no_budget (hdesc : H1) (hterm : H2) {k : ℕ} (hk : 4 ≤ k) :
    ∃ (β C R : ℝ), 0 < β ∧ β < 1 ∧ 0 < C ∧
      ∀ (N : ℕ) (S : Finset ℕ), 2 ≤ N → S ⊆ Finset.Icc 1 N → 0 < S.card →
        (¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ S) →
        ¬ C * (max 2 (Real.log (2 * (N : ℝ) / (S.card : ℝ)))) ^ β + R ≤
          Real.log (Real.log (N : ℝ)) := by
  obtain ⟨β, C, T, R₀, hβ, hβ1, hC, hstep⟩ := hdesc k hk
  obtain ⟨Q, hstop⟩ := hterm k hk T
  let R := max R₀ Q
  refine ⟨β, C, R, hβ, hβ1, hC, ?_⟩
  let X := ℕ × Finset ℕ
  let p (x : X) := max 2 (Real.log (2 * (x.1 : ℝ) / (x.2.card : ℝ)))
  let admissible (x : X) :=
    2 ≤ x.1 ∧ x.2 ⊆ Finset.Icc 1 x.1 ∧ 0 < x.2.card ∧
      (¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ x.2) ∧
      C * (p x) ^ β + R ≤ Real.log (Real.log (x.1 : ℝ))
  have hp (x : X) : 0 ≤ p x := (by norm_num : (0 : ℝ) ≤ 2).trans (le_max_left _ _)
  have decrease (x : X) (hx : admissible x) :
      ∃ y, admissible y ∧ p y + 1 ≤ p x := by
    obtain ⟨hN, hS, hcard, hfree, hbudget⟩ := hx
    have hlarge : T < p x := by
      by_contra! hsmall
      have hlt := hstop x.1 x.2 hN hS hcard hfree hsmall
      have hnonneg := mul_nonneg hC.le (Real.rpow_nonneg (hp x) β)
      have hQR : Q ≤ R := le_max_right _ _
      linarith
    obtain ⟨a, q, M, hq, hM, _, hcard', hdrop, hbudget'⟩ :=
      hstep R (le_max_left _ _) x.1 x.2 hN hS hcard hfree hlarge hbudget
    let U := (Finset.Icc 1 M).filter (fun i ↦ a + (i - 1) * q ∈ x.2)
    refine ⟨(M, U), ⟨hM, Finset.filter_subset _ _, hcard', ?_, hbudget'⟩, hdrop⟩
    exact progression_preimage_free hk hq hfree
  intro N S hN hS hcard hfree hbudget
  exact eliminate_descent p admissible hp decrease (N, S) ⟨hN, hS, hcard, hfree, hbudget⟩

lemma eventually_budget_six (β C R : ℝ) (hβ : β < 1) :
    ∀ᶠ t : ℝ in atTop, 1 ≤ t ∧ C * (6 * t) ^ β + R ≤ t := by
  have hlim : Tendsto (fun t : ℝ ↦ (C * (6 : ℝ) ^ β) * t ^ (β - 1)) atTop (𝓝 0) := by
    simpa only [neg_sub, mul_zero] using
      (tendsto_rpow_neg_atTop (sub_pos.mpr hβ)).const_mul (C * (6 : ℝ) ^ β)
  filter_upwards [eventually_ge_atTop (max 1 (2 * R)),
    hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with t ht hs
  have ht1 : 1 ≤ t := (le_max_left _ _).trans ht
  have ht0 : 0 < t := by linarith
  have hR : R ≤ t / 2 := by linarith [(le_max_right 1 (2 * R)).trans ht]
  refine ⟨ht1, ?_⟩
  have he : t ^ (β - 1) * t = t ^ β := by
    calc
      t ^ (β - 1) * t = t ^ (β - 1) * t ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = t ^ β := by rw [← Real.rpow_add ht0]; congr 1; ring
  have hm : C * (6 * t) ^ β = ((C * (6 : ℝ) ^ β) * t ^ (β - 1)) * t := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 6) ht0.le]
    rw [mul_assoc (C * (6 : ℝ) ^ β), he, ← mul_assoc]
  rw [hm]
  linarith [mul_le_mul_of_nonneg_right hs.le ht0.le]

lemma parameter_le_six_of_large_card {N : ℕ} {S : Finset ℕ}
    (hN : 0 < (N : ℝ)) (hL : 0 < Real.log (N : ℝ))
    (ht : 1 ≤ Real.log (Real.log (N : ℝ)))
    (hS : (N : ℝ) / Real.log (N : ℝ) ^ 5 < (S.card : ℝ)) :
    max 2 (Real.log (2 * (N : ℝ) / (S.card : ℝ))) ≤
      6 * Real.log (Real.log (N : ℝ)) := by
  have hpow_pos : 0 < Real.log (N : ℝ) ^ 5 := pow_pos hL 5
  have hcard : 0 < (S.card : ℝ) := (div_pos hN hpow_pos).trans hS
  have hcross := (div_lt_iff₀ hpow_pos).mp hS
  have hratio : 2 * (N : ℝ) / (S.card : ℝ) ≤ 2 * Real.log (N : ℝ) ^ 5 := by
    apply (div_le_iff₀ hcard).mpr
    nlinarith only [hcross]
  have hlog := Real.log_le_log (div_pos (by positivity) hcard) hratio
  have h2 : Real.log 2 < 1 := by
    have h := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)
    norm_num at h ⊢
    exact h
  rw [Real.log_mul (by norm_num) hpow_pos.ne', Real.log_pow] at hlog
  push_cast at hlog
  exact max_le (by linarith) (by linarith)

lemma eventual_log_pow_five_bound (hdesc : H1) (hterm : H2) {k : ℕ} (hk : 4 ≤ k) :
    ∀ᶠ N : ℕ in atTop, (r k N : ℝ) ≤ (N : ℝ) / Real.log (N : ℝ) ^ 5 := by
  obtain ⟨β, C, R, hβ, hβ1, hC, hno⟩ := no_budget hdesc hterm hk
  have hlog : Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hloglog : Tendsto (fun N : ℕ ↦ Real.log (Real.log (N : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp hlog
  filter_upwards [eventually_ge_atTop (2 : ℕ), hlog.eventually (eventually_gt_atTop 0),
    hloglog.eventually (eventually_budget_six β C R hβ1)] with N hN hL hbudget
  obtain ⟨S, hS, hfree, hcard⟩ := extremizer (by omega : 1 < k) N
  rw [← hcard]
  by_contra! hlarge
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hSpos : 0 < S.card := by
    exact_mod_cast (div_pos hNpos (pow_pos hL 5)).trans hlarge
  have hp := parameter_le_six_of_large_card hNpos hL hbudget.1 hlarge
  apply hno N S hN hS hSpos ((apFree_iff (by omega)).mp hfree)
  refine le_trans ?_ hbudget.2
  gcongr

lemma ceil_pow_four_lt_pow_five {x : ℝ} (hx : 16 ≤ x) :
    (((⌈x⌉₊ + 1) ^ 4 : ℕ) : ℝ) < x ^ 5 := by
  have hx0 : 0 ≤ x := by linarith
  have hceil : (⌈x⌉₊ : ℝ) < x + 1 := Nat.ceil_lt_add_one hx0
  have hlt : ((⌈x⌉₊ + 1 : ℕ) : ℝ) < 2 * x := by
    push_cast
    linarith
  have hpow4 : (((⌈x⌉₊ + 1) ^ 4 : ℕ) : ℝ) < (2 * x) ^ 4 := by
    have hc : (((⌈x⌉₊ + 1) ^ 4 : ℕ) : ℝ) = ((⌈x⌉₊ + 1 : ℕ) : ℝ) ^ 4 := by push_cast; rfl
    rw [hc]
    exact pow_lt_pow_left₀ hlt (by positivity) (by decide)
  have h16 : (2 * x) ^ 4 ≤ x ^ 5 := by
    calc (2 * x) ^ 4 = 16 * x ^ 4 := by ring
      _ ≤ x * x ^ 4 := mul_le_mul_of_nonneg_right hx (by positivity)
      _ = x ^ 5 := by ring
  exact hpow4.trans_le h16

lemma exists_large_color_class {N q : ℕ} (hq : 0 < q) (c : ℕ → Fin q) :
    ∃ col : Fin q, N ≤ q * ((Finset.Icc 1 N).filter (fun x => c x = col)).card := by
  classical
  have hne : (Finset.univ : Finset (Fin q)).Nonempty := ⟨⟨0, hq⟩, Finset.mem_univ _⟩
  obtain ⟨col, _, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun t : Fin q => ((Finset.Icc 1 N).filter (fun x => c x = t)).card) hne
  have hsum : ∑ t ∈ (Finset.univ : Finset (Fin q)),
      ((Finset.Icc 1 N).filter (fun x => c x = t)).card = N := by
    rw [Finset.sum_card_fiberwise_eq_card_filter,
      Finset.filter_eq_self.mpr (fun _ _ => Finset.mem_univ _), Nat.card_Icc]
    omega
  refine ⟨col, ?_⟩
  calc N = ∑ t ∈ (Finset.univ : Finset (Fin q)),
            ((Finset.Icc 1 N).filter (fun x => c x = t)).card := hsum.symm
    _ ≤ ∑ _t ∈ (Finset.univ : Finset (Fin q)),
          ((Finset.Icc 1 N).filter (fun x => c x = col)).card := Finset.sum_le_sum hmax
    _ = q * ((Finset.Icc 1 N).filter (fun x => c x = col)).card := by
          simp [Finset.card_univ, Fintype.card_fin]

theorem main : H1 → H2 → OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R2.H1 := by
  intro hdesc hterm k hk
  have hlog : Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventual_log_pow_five_bound hdesc hterm hk,
    hlog.eventually_ge_atTop (16 : ℝ), eventually_gt_atTop (0 : ℕ)] with N hr hx16 hN c
  let q : ℕ := (⌈Real.log (N : ℝ)⌉₊ + 1) ^ 4
  have hq : 0 < q := by dsimp [q]; positivity
  obtain ⟨col, hcol⟩ := exists_large_color_class hq c
  let S : Finset ℕ := (Finset.Icc 1 N).filter (fun x => c x = col)
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast hN
  have hLpos : 0 < Real.log (N : ℝ) := by linarith
  have hpow5_pos : 0 < Real.log (N : ℝ) ^ 5 := pow_pos hLpos 5
  have hq_lt : (q : ℝ) < Real.log (N : ℝ) ^ 5 := ceil_pow_four_lt_pow_five hx16
  have hqr_lt : (q : ℝ) * (r k N : ℝ) < (N : ℝ) := by
    calc (q : ℝ) * (r k N : ℝ)
        ≤ (q : ℝ) * ((N : ℝ) / Real.log (N : ℝ) ^ 5) :=
            mul_le_mul_of_nonneg_left hr (Nat.cast_nonneg q)
      _ < Real.log (N : ℝ) ^ 5 * ((N : ℝ) / Real.log (N : ℝ) ^ 5) :=
            mul_lt_mul_of_pos_right hq_lt (div_pos hNpos hpow5_pos)
      _ = (N : ℝ) := by field_simp [hpow5_pos.ne']
  have hN_le : (N : ℝ) ≤ (q : ℝ) * (S.card : ℝ) := by exact_mod_cast hcol
  have hr_lt_S : r k N < S.card := by
    by_contra! hle
    have hleR : (S.card : ℝ) ≤ (r k N : ℝ) := by exact_mod_cast hle
    have : (q : ℝ) * (S.card : ℝ) ≤ (q : ℝ) * (r k N : ℝ) :=
      mul_le_mul_of_nonneg_left hleR (Nat.cast_nonneg q)
    linarith
  have hnot_free : ¬ (S : Set ℕ).IsAPOfLengthFree k := by
    intro hfree
    exact (not_le_of_gt hr_lt_S) (card_le_r (Finset.filter_subset _ _) hfree)
  have hex : ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ S := by
    by_contra hno
    exact hnot_free ((apFree_iff (by omega : 1 < k)).mpr hno)
  obtain ⟨a, d, hd, hmem⟩ := hex
  have ha_col : c a = col := by
    have h0 := (Finset.mem_filter.mp (hmem 0 (by omega))).2
    simpa only [zero_mul, add_zero] using h0
  refine ⟨a, d, hd, fun i hi => ?_⟩
  obtain ⟨hIcc, hci⟩ := Finset.mem_filter.mp (hmem i hi)
  exact ⟨hIcc, hci.trans ha_col.symm⟩

end OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R2_H1_R2
