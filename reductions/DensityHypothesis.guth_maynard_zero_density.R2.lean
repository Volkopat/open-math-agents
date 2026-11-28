import FormalConjectures.Wikipedia.DensityHypothesis
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Pointwise band estimates for the Guth–Maynard zero-density bound

A logarithmic estimate for unit-height windows at abscissa one half handles
the range up to 17/30. Above that cutoff it suffices to estimate one dyadic
band at each fixed rational abscissa strictly below one. Its constant and
starting height can both depend on the abscissa and the exponent allowance.

The finite-support, rectangle inclusion, and rectangle splitting arguments
adapt the merged reduction by dk8827 (open-math-agents PR 1603).
-/

namespace OMA.R_DensityHypothesis_guth_maynard_zero_density_R2

open DensityHypothesis

private theorem finite_zero_support {S : Set ℂ} {σ T : ℝ}
    (hS : S ⊆ {z : ℂ | σ ≤ z.re ∧ z.re ≤ 1 ∧ 0 < z.im ∧ z.im ≤ T}) :
    (S ∩ Function.support (analyticOrderNatAt riemannZeta)).Finite :=
  (zetaZeroSet_finite σ T).subset fun z hz => by
    have hh := hS hz.1
    have hzero : riemannZeta z = 0 := by
      by_contra hn
      exact hz.2 (Complex.analyticOrderNatAt_eq_zero_of_ne_zero hn)
    exact ⟨hh.1, hh.2.1, hh.2.2.1, hh.2.2.2, hzero⟩

private theorem count_mono {σ τ T U : ℝ} (hσ : σ ≤ τ) (hT : T ≤ U) :
    zetaZeroCount τ T ≤ zetaZeroCount σ U := by
  let A := {z : ℂ | τ ≤ z.re ∧ z.re ≤ 1 ∧ 0 < z.im ∧ z.im ≤ T}
  let B := {z : ℂ | σ ≤ z.re ∧ z.re ≤ 1 ∧ 0 < z.im ∧ z.im ≤ U}
  have hAB : A ⊆ B := fun z hz => ⟨hσ.trans hz.1, hz.2.1, hz.2.2.1, hz.2.2.2.trans hT⟩
  have hB := finite_zero_support (σ := σ) (T := U) (S := B) Set.Subset.rfl
  have hA := finite_zero_support hAB
  change Complex.zeroCountOn riemannZeta A ≤ Complex.zeroCountOn riemannZeta B
  unfold Complex.zeroCountOn
  rw [finsum_mem_eq_sum _ hA, finsum_mem_eq_sum _ hB]
  apply Finset.sum_le_sum_of_subset
  intro z hz
  rw [Set.Finite.mem_toFinset] at hz ⊢
  exact ⟨hAB hz.1, hz.2⟩

private theorem count_split (σ T U : ℝ) (hT : 0 ≤ T) (hTU : T ≤ U) :
    zetaZeroCount σ U = zetaZeroCount σ T +
      Complex.zeroCountOn riemannZeta {z : ℂ | σ ≤ z.re ∧ z.re ≤ 1 ∧ T < z.im ∧ z.im ≤ U} := by
  let A := {z : ℂ | σ ≤ z.re ∧ z.re ≤ 1 ∧ 0 < z.im ∧ z.im ≤ T}
  let B := {z : ℂ | σ ≤ z.re ∧ z.re ≤ 1 ∧ T < z.im ∧ z.im ≤ U}
  let C := {z : ℂ | σ ≤ z.re ∧ z.re ≤ 1 ∧ 0 < z.im ∧ z.im ≤ U}
  have hAC : A ⊆ C := fun z hz => ⟨hz.1, hz.2.1, hz.2.2.1, hz.2.2.2.trans hTU⟩
  have hBC : B ⊆ C := fun z hz => ⟨hz.1, hz.2.1, hT.trans_lt hz.2.2.1, hz.2.2.2⟩
  have hC : C = A ∪ B := by
    ext z
    constructor
    · intro hz
      by_cases hzT : z.im ≤ T
      · exact Or.inl ⟨hz.1, hz.2.1, hz.2.2.1, hzT⟩
      · exact Or.inr ⟨hz.1, hz.2.1, lt_of_not_ge hzT, hz.2.2.2⟩
    · rintro (hz | hz)
      · exact hAC hz
      · exact hBC hz
  have hAB : Disjoint A B := Set.disjoint_left.mpr fun z ha hb =>
    (not_lt_of_ge ha.2.2.2) hb.2.2.1
  change Complex.zeroCountOn riemannZeta C = Complex.zeroCountOn riemannZeta A +
    Complex.zeroCountOn riemannZeta B
  unfold Complex.zeroCountOn
  rw [hC, finsum_mem_union' hAB (finite_zero_support hAC) (finite_zero_support hBC)]

/-- A unit-window total bound, stated abstractly to apply to different zero counters. -/
theorem total_from_unit (F : ℝ → ℕ) (mono : Monotone F) (hzero : F 0 = 0)
    (C : ℝ) (hC : 0 < C)
    (unit : ∀ k : ℕ, (F (k+1) : ℝ) ≤ F k + C*Real.log (k+3)) :
    ∀ T : ℝ, 2 ≤ T → (F T : ℝ) ≤ (6*C)*T*Real.log T := by
  intro T hT
  let m := ⌈T⌉₊
  have hm : T ≤ (m:ℝ) := Nat.le_ceil T
  have hm' : (m:ℝ) ≤ T+1 := (Nat.ceil_lt_add_one (by linarith : 0 ≤ T)).le
  have sum (k : ℕ) (hk : k ≤ m) : (F k : ℝ) ≤ k*(C*Real.log (T+3)) := by
    induction k with
    | zero => simp [hzero]
    | succ k ih =>
      have hkt : (k:ℝ)+1 ≤ m := by exact_mod_cast hk
      have hlog := Real.log_le_log (by positivity : 0 < (k:ℝ)+3) (by linarith : (k:ℝ)+3 ≤ T+3)
      have hs := (unit k).trans (add_le_add (ih (Nat.le_of_succ_le hk))
        (mul_le_mul_of_nonneg_left hlog hC.le))
      simpa only [Nat.cast_succ, add_mul, one_mul] using hs
  have hlog : Real.log (T+3) ≤ 3 * Real.log T := by
    rw [show (3:ℝ) * Real.log T = Real.log (T^3) by rw [Real.log_pow]; norm_num]
    apply Real.log_le_log (by linarith)
    nlinarith [mul_nonneg (by linarith : 0 ≤ T-2) (sq_nonneg T), sq_nonneg (T-2)]
  have hmT : (m:ℝ) ≤ 2*T := by linarith
  have hsum := sum m le_rfl
  have h₁ := mul_le_mul_of_nonneg_left hlog hC.le
  have h₂ := mul_le_mul hmT h₁ (mul_nonneg hC.le (Real.log_nonneg (by linarith))) (by linarith)
  have hf : (F T : ℝ) ≤ (F m : ℝ) := by exact_mod_cast mono hm
  calc (F T : ℝ) ≤ m * (C * Real.log (T+3)) := hf.trans hsum
    _ ≤ (2*T) * (C*(3*Real.log T)) := h₂
    _ = _ := by ring

/-- Up to sigma = 17/30 the uniform exponent dominates the linear power of T. -/
theorem low_sigma_of_total (F : ℝ → ℝ → ℕ)
    (hmono : ∀ {σ τ T : ℝ}, σ ≤ τ → F τ T ≤ F σ T)
    (hcount : ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      (F (1/2) T : ℝ) ≤ C*T*Real.log T) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, 1/2 ≤ σ → σ ≤ 17/30 → 2 ≤ T →
      (F σ T : ℝ) ≤ C * T^((30/13 : ℝ)*(1-σ)+ε) := by
  obtain ⟨K,hK,hbound⟩ := hcount
  refine ⟨K/ε, div_pos hK hε, ?_⟩
  intro σ T half small height
  have hm : (F σ T : ℝ) ≤ F (1/2) T := by exact_mod_cast hmono half
  have hT : 0 < T := by linarith
  have hpow := Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ T)
    (by linarith : 1+ε ≤ (30/13)*(1-σ)+ε)
  calc (F σ T : ℝ) ≤ K*T*Real.log T := hm.trans (hbound _ height)
    _ ≤ K*T*(T^ε/ε) := mul_le_mul_of_nonneg_left (Real.log_le_rpow_div hT.le hε) (by positivity)
    _ = (K/ε)*T^(1+ε) := by rw [Real.rpow_add hT, Real.rpow_one]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hpow (div_pos hK hε).le

/-- Summing dyadic bands with positive exponent preserves that exponent, starting at the
same threshold as the band estimate. -/
lemma cumulative_of_eventual_bands (F B : ℕ → ℝ) (a : ℝ) (ha : 0 < a)
    (hrec : ∀ k, F (k+1) ≤ F k + B k) {K : ℕ} {C : ℝ} (hC : 0 < C)
    (hband : ∀ k ≥ K, B k ≤ C * ((2:ℝ)^k)^a) :
    ∃ D : ℝ, 0 < D ∧ ∀ k ≥ K, F k ≤ D * ((2:ℝ)^k)^a := by
  have hr : 0 < (2:ℝ)^a-1 := sub_pos.mpr (Real.one_lt_rpow (by norm_num) ha)
  let D := max (F K) (C/((2:ℝ)^a-1))
  have hratio : C/((2:ℝ)^a-1) ≤ D := le_max_right _ _
  have hD : 0 < D := (div_pos hC hr).trans_le hratio
  have hstep : D + C ≤ D * (2:ℝ)^a := by
    have hx := (div_le_iff₀ hr).mp hratio
    linarith
  refine ⟨D, hD, ?_⟩
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
    exact (le_max_left _ _).trans (le_mul_of_one_le_right hD.le
      (Real.one_le_rpow (one_le_pow₀ (by norm_num)) ha.le))
  | succ k hk ih =>
    calc
      F (k+1) ≤ F k + B k := hrec k
      _ ≤ D * ((2:ℝ)^k)^a + C * ((2:ℝ)^k)^a := add_le_add ih (hband k hk)
      _ = (D+C) * ((2:ℝ)^k)^a := (add_mul _ _ _).symm
      _ ≤ (D*(2:ℝ)^a) * ((2:ℝ)^k)^a := mul_le_mul_of_nonneg_right hstep (by positivity)
      _ = D * ((2:ℝ)^(k+1))^a := by
        rw [pow_succ, Real.mul_rpow (by positivity) (by norm_num)]
        ac_rfl

/-- A finite rational grid on the closed sigma range. All its sample points lie below one. -/
lemma lower_rational_grid (δ : ℝ) (hδ : 0 < δ) :
    ∃ S : Finset ℚ, (∀ q ∈ S, 1/2 ≤ q ∧ q < 1) ∧
      ∀ σ : ℝ, 1/2 ≤ σ → σ ≤ 1 → ∃ q ∈ S, (q : ℝ) ≤ σ ∧ σ - q < δ := by
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ
  let D : ℝ := 2*((m:ℝ)+1)
  let q (i : ℕ) : ℚ := 1/2 + (i:ℚ)/(2*((m:ℚ)+1))
  have hD : 0 < D := by dsimp [D]; positivity
  have hq (i : ℕ) : (q i : ℝ) = 1/2 + (i:ℝ)/D := by dsimp [D,q]; push_cast; rfl
  refine ⟨(Finset.range (m+1)).image q, ?_, ?_⟩
  · intro u hu
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hu
    have him : i ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    have hi' : (i:ℚ) ≤ m := by exact_mod_cast him
    dsimp [q]
    constructor
    · exact le_add_of_nonneg_right (by positivity)
    · have : (i:ℚ)/(2*((m:ℚ)+1)) < 1/2 := (div_lt_iff₀ (by positivity)).mpr (by linarith)
      linarith
  · intro σ hσ hσ'
    let t := (σ-1/2)*D
    let i := min ⌊t⌋₊ m
    have hti : 0 ≤ t := mul_nonneg (sub_nonneg.mpr hσ) hD.le
    have him : i ≤ m := min_le_right _ _
    have hiFloor : (i:ℝ) ≤ t :=
      (show (i:ℝ) ≤ (⌊t⌋₊:ℝ) by exact_mod_cast (min_le_left ⌊t⌋₊ m)).trans (Nat.floor_le hti)
    have hclose : t ≤ (i:ℝ) + 1 := by
      by_cases h : ⌊t⌋₊ ≤ m
      · dsimp [i]; rw [min_eq_left h]; exact (Nat.lt_floor_add_one t).le
      · dsimp [i]; rw [min_eq_right (le_of_not_ge h)]
        dsimp [t,D]
        nlinarith [mul_nonneg (sub_nonneg.mpr hσ') (show 0 ≤ (m:ℝ)+1 by positivity)]
    refine ⟨q i, Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (Nat.lt_succ_of_le him), rfl⟩, ?_, ?_⟩
    · rw [hq]; have := (div_le_iff₀ hD).mpr hiFloor; linarith
    · rw [hq]
      have hmesh : 1/D < δ := lt_of_le_of_lt (by
        apply one_div_le_one_div_of_le (by positivity); dsimp [D]; linarith) hm
      have hh : σ - (1/2 + (i:ℝ)/D) ≤ 1/D := by
        have hh' : σ-1/2 ≤ ((i:ℝ)+1)/D := (le_div_iff₀ hD).mpr hclose
        rw [add_div] at hh'; linarith
      exact hh.trans_lt hmesh

/-- A fixed rational abscissa admits an all-height bound once its finite initial range is absorbed. -/
lemma absorb_initial_dyadic_heights (f : ℕ → ℝ) (a : ℝ) (ha : 0 ≤ a)
    (h : ∃ C : ℝ, 0 < C ∧ ∃ K : ℕ, ∀ k ≥ K, f k ≤ C * ((2:ℝ)^k)^a) :
    ∃ C : ℝ, 0 < C ∧ ∀ k, f k ≤ C * ((2:ℝ)^k)^a := by
  obtain ⟨C, hC, K, hK⟩ := h
  let B := ∑ k ∈ Finset.range K, |f k|
  have hB : 0 ≤ B := Finset.sum_nonneg (fun k _ => abs_nonneg (f k))
  refine ⟨C + B, by positivity, ?_⟩
  intro k
  by_cases hk : K ≤ k
  · exact (hK k hk).trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
  · have hs : |f k| ≤ B := Finset.single_le_sum (fun j _ => abs_nonneg (f j))
        (Finset.mem_range.mpr (lt_of_not_ge hk))
    have hpow : (1:ℝ) ≤ ((2:ℝ)^k)^a := Real.one_le_rpow (one_le_pow₀ (by norm_num)) ha
    exact ((le_abs_self (f k)).trans hs).trans ((by linarith : B ≤ C+B).trans
      (le_mul_of_one_le_right (by positivity) hpow))

/-- Pointwise eventual rational bounds imply uniform bounds at every dyadic height. -/
lemma uniform_dyadic_bound (F : ℝ → ℕ → ℝ) (hmono : ∀ k, Antitone (fun σ => F σ k))
    (hpoint : ∀ q : ℚ, 1/2 ≤ q → q < 1 → ∀ δ : ℝ, 0 < δ →
      ∃ C : ℝ, 0 < C ∧ ∃ K : ℕ, ∀ k ≥ K,
        F q k ≤ C * ((2:ℝ)^k)^((30/13:ℝ)*(1-(q:ℝ))+δ)) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ : ℝ, 1/2 ≤ σ → σ ≤ 1 → ∀ k : ℕ,
      F σ k ≤ C * ((2:ℝ)^k)^((30/13:ℝ)*(1-σ)+ε) := by
  classical
  obtain ⟨S, hS, hcover⟩ := lower_rational_grid (13*ε/60) (by positivity)
  have hfixed (q : {q : ℚ // q ∈ S}) : ∃ C : ℝ, 0 < C ∧ ∀ k,
      F (q.val:ℝ) k ≤ C * ((2:ℝ)^k)^((30/13:ℝ)*(1-(q.val:ℝ))+ε/2) := by
    obtain ⟨hl,hu⟩ := hS q.val q.property
    have hq : (q.val:ℝ) < 1 := by exact_mod_cast hu
    apply absorb_initial_dyadic_heights
    · linarith
    · exact hpoint q.val hl hu (ε/2) (by positivity)
  choose c hc hb using hfixed
  let M := ∑ q : {q : ℚ // q ∈ S}, c q
  have hM : 0 ≤ M := Finset.sum_nonneg fun q _ => (hc q).le
  refine ⟨1+M, by positivity, ?_⟩
  intro σ hσl hσu k
  obtain ⟨q, hq, hqσ, hgap⟩ := hcover σ hσl hσu
  let u : {q : ℚ // q ∈ S} := ⟨q,hq⟩
  have hcM : c u ≤ M := Finset.single_le_sum (fun i _ => (hc i).le) (Finset.mem_univ u)
  have hexp : (30/13:ℝ)*(1-(q:ℝ))+ε/2 ≤ (30/13:ℝ)*(1-σ)+ε := by linarith
  exact ((hmono k hqσ).trans (hb u k)).trans
    (mul_le_mul (by linarith) (Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num)) hexp)
      (by positivity) (by positivity))

/-- A height-monotone density bound at powers of two extends to all real heights,
with one constant valid on the whole closed abscissa range. -/
theorem all_heights_of_dyadic (F : ℝ → ℝ → ℝ) (hmono : ∀ σ, Monotone (F σ))
    (ε : ℝ) (hε : 0 < ε)
    (hdy : ∃ C : ℝ, 0 < C ∧ ∀ σ : ℝ, 1/2 ≤ σ → σ ≤ 1 → ∀ k : ℕ,
      F σ ((2 : ℝ)^k) ≤ C * ((2 : ℝ)^k)^((30/13 : ℝ)*(1-σ)+ε)) :
    ∃ D : ℝ, 0 < D ∧ ∀ σ T : ℝ, 1/2 ≤ σ → σ ≤ 1 → 2 ≤ T →
      F σ T ≤ D * T^((30/13 : ℝ)*(1-σ)+ε) := by
  obtain ⟨C,hC,hdy⟩ := hdy
  refine ⟨C * (2 : ℝ)^((15/13 : ℝ)+ε), by positivity, ?_⟩
  intro σ T hl hu hT
  let a := (30/13 : ℝ)*(1-σ)+ε
  have ha : 0 ≤ a := by dsimp [a]; linarith
  have hau : a ≤ 15/13 + ε := by dsimp [a]; linarith
  obtain ⟨k,hk,hk'⟩ := exists_nat_pow_near (by linarith : 1 ≤ T) (by norm_num : (1 : ℝ) < 2)
  have hpow : (2 : ℝ)^(k+1) ≤ 2*T := by rw [pow_succ]; linarith
  calc
    F σ T ≤ F σ ((2 : ℝ)^(k+1)) := hmono σ hk'.le
    _ ≤ C * ((2 : ℝ)^(k+1))^a := hdy σ hl hu (k+1)
    _ ≤ C * (2*T)^a := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hpow ha) hC.le
    _ = C * (2 : ℝ)^a * T^a := by rw [Real.mul_rpow (by norm_num) (by linarith : 0 ≤ T), mul_assoc]
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (by norm_num) hau) hC.le) (Real.rpow_nonneg (by linarith) _)

/-- Compactness gives a canonical finite zero set for the symmetric rectangle
in `of_pointwise_symmetric`, including both horizontal edges. -/
theorem symmetric_rectangle_zeros_finite (σ T : ℝ) :
    ({z : ℂ | σ ≤ z.re ∧ z.re ≤ 1 ∧ -T ≤ z.im ∧ z.im ≤ T} ∩
      {z : ℂ | riemannZeta z = 0}).Finite := by
  have hK : IsCompact ((fun p : ℝ × ℝ => (p.1 : ℂ) + Complex.I * (p.2 : ℂ)) ''
      (Set.Icc σ 1 ×ˢ Set.Icc (-T) T)) :=
    (isCompact_Icc.prod isCompact_Icc).image (by fun_prop)
  refine hK.inter_riemannZetaZeros_finite.subset fun z hz => ?_
  exact ⟨⟨(z.re, z.im), ⟨⟨hz.1.1, hz.1.2.1⟩, hz.1.2.2⟩,
    by simp [mul_comm Complex.I, Complex.re_add_im]⟩, hz.2⟩

open Filter Asymptotics

/-- The positive-height count is bounded by the finite symmetric-rectangle
count used in McColm's `GuthMaynard.ZeroCount`. Both use analytic multiplicity. -/
theorem positive_count_le_symmetric_sum (f : ℂ → ℂ) (σ T : ℝ)
    (hfin : ({z : ℂ | σ ≤ z.re ∧ z.re ≤ 1 ∧ -T ≤ z.im ∧ z.im ≤ T}
      ∩ {z : ℂ | f z = 0}).Finite) :
    (∑ᶠ z ∈ {z : ℂ | σ ≤ z.re ∧ z.re ≤ 1 ∧ 0 < z.im ∧ z.im ≤ T}, analyticOrderNatAt f z)
      ≤ ∑ z ∈ hfin.toFinset, analyticOrderNatAt f z := by
  classical
  let P := {z : ℂ | σ ≤ z.re ∧ z.re ≤ 1 ∧ 0 < z.im ∧ z.im ≤ T}
  have hsub : P ∩ Function.support (analyticOrderNatAt f) ⊆
      {z : ℂ | σ ≤ z.re ∧ z.re ≤ 1 ∧ -T ≤ z.im ∧ z.im ≤ T} ∩ {z : ℂ | f z = 0} := by
    intro z hz
    obtain ⟨hl,hr,hz0,hzT⟩ := hz.1
    refine ⟨⟨hl,hr, by linarith, hzT⟩, ?_⟩
    by_contra hn
    exact hz.2 (by simp [analyticOrderNatAt, analyticOrderAt_eq_zero.mpr (Or.inr hn)])
  rw [finsum_mem_eq_sum _ (hfin.subset hsub)]
  apply Finset.sum_le_sum_of_subset
  intro z hz
  rw [Set.Finite.mem_toFinset] at hz ⊢
  exact hsub hz

/-- A fixed-abscissa cumulative real-height Big-O bound controls each positive
dyadic band, with the height endpoint `2^(k+1)` absorbed into the constant.
The input matches the symmetric zero-count convention used by McColm. -/
theorem dyadic_band_of_symmetric_bound (N : ℝ → ℕ) (B : ℕ → ℕ) (σ δ : ℝ)
    (hband : ∀ k : ℕ, B k ≤ N ((2:ℝ)^(k+1)))
    (h : (fun T : ℝ => |(N T : ℝ)|) =O[atTop]
      (fun T : ℝ => T^δ * |T^(30*(1-σ)/13)|)) :
    ∃ C : ℝ, 0 < C ∧ ∃ K : ℕ, ∀ k ≥ K,
      (B k : ℝ) ≤ C * ((2:ℝ)^k)^((30/13:ℝ)*(1-σ)+δ) := by
  obtain ⟨D, hD, hbig⟩ := h.exists_pos
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp hbig.bound
  obtain ⟨K, hK⟩ := pow_unbounded_of_one_lt T₀ (by norm_num : (1:ℝ) < 2)
  let a := (30/13:ℝ)*(1-σ)+δ
  refine ⟨D * (2:ℝ)^a, by positivity, K, ?_⟩
  intro k hk
  let T : ℝ := (2:ℝ)^(k+1)
  have hT : 0 < T := by dsimp [T]; positivity
  have hTk : T₀ ≤ T := hK.le.trans <| pow_le_pow_right₀ (by norm_num) (hk.trans (Nat.le_succ k))
  have hx := hT₀ T hTk
  simp only [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg (N T) : (0 : ℝ) ≤ (N T : ℝ)),
    abs_of_nonneg (Real.rpow_nonneg hT.le _),
    abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hT.le _) (Real.rpow_nonneg hT.le _))] at hx
  calc
    (B k : ℝ) ≤ (N T : ℝ) := Nat.cast_le.mpr (hband k)
    _ ≤ D * (T^δ * T^(30*(1-σ)/13)) := hx
    _ = D * T^a := by rw [← Real.rpow_add hT]; congr 2; dsimp [a]; ring
    _ = (D*(2:ℝ)^a) * ((2:ℝ)^k)^a := by
      dsimp [T]
      rw [pow_succ, Real.mul_rpow (by positivity) (by norm_num)]
      ring

/-- A symmetric multiplicity-weighted fixed-abscissa estimate of McColm's
shape implies the uniform positive-height Guth–Maynard estimate. -/
theorem of_pointwise_symmetric
    (density : ∀ σ : ℝ, 1/2 ≤ σ → σ ≤ 1 → ∀ δ : ℝ, 0 < δ →
      (fun T : ℝ => |((∑ z ∈ (symmetric_rectangle_zeros_finite σ T).toFinset,
        analyticOrderNatAt riemannZeta z : ℕ) : ℝ)|) =O[Filter.atTop]
        (fun T : ℝ => T^δ * |T^(30*(1-σ)/13)|))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, 1/2 ≤ σ → σ ≤ 1 → 2 ≤ T →
      (zetaZeroCount σ T : ℝ) ≤ C * T^((30/13:ℝ)*(1-σ)+ε) := by
  let N (σ T : ℝ) := ∑ z ∈ (symmetric_rectangle_zeros_finite σ T).toFinset,
    analyticOrderNatAt riemannZeta z
  apply all_heights_of_dyadic (fun σ T => (zetaZeroCount σ T : ℝ))
    (fun _ _ _ hh => Nat.cast_le.mpr (count_mono le_rfl hh)) ε hε
  apply uniform_dyadic_bound (fun σ k => (zetaZeroCount σ ((2:ℝ)^k) : ℝ))
    (fun _ _ _ hh => Nat.cast_le.mpr (count_mono hh le_rfl)) _ ε hε
  intro q hq hq1 δ hδ
  have hlo : 1/2 ≤ (q:ℝ) := by simpa using (Rat.cast_le (K := ℝ)).mpr hq
  have hhi : (q:ℝ) ≤ 1 := by exact_mod_cast hq1.le
  apply dyadic_band_of_symmetric_bound (N q) (fun k => zetaZeroCount q ((2:ℝ)^k)) q δ _
    (density q hlo hhi δ hδ)
  intro k
  refine (count_mono (σ := (q:ℝ)) le_rfl
    (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (Nat.le_succ k))).trans ?_
  exact positive_count_le_symmetric_sum riemannZeta q _ (symmetric_rectangle_zeros_finite q _)


/-- A logarithmic bound for each unit-height window, with multiplicity. -/
def H1 : Prop :=
  ∃ A : ℝ, 0 < A ∧ ∀ k : ℕ,
    (Complex.zeroCountOn riemannZeta
      {z : ℂ | 1/2 ≤ z.re ∧ z.re ≤ 1 ∧ (k : ℝ) < z.im ∧ z.im ≤ k+1} : ℝ)
      ≤ A * Real.log (k+3)

/-- A pointwise, eventual estimate for an individual dyadic band. Both C and K
may depend on the rational abscissa and the positive exponent allowance. -/
def H2 : Prop :=
  ∀ q : ℚ, 17/30 < q → q < 1 → ∀ δ : ℝ, 0 < δ →
    ∃ C : ℝ, 0 < C ∧ ∃ K : ℕ, ∀ k ≥ K,
    (Complex.zeroCountOn riemannZeta
      {z : ℂ | (q : ℝ) ≤ z.re ∧ z.re ≤ 1 ∧ (2:ℝ)^k < z.im ∧ z.im ≤ (2:ℝ)^(k+1)} : ℝ)
      ≤ C * ((2:ℝ)^k)^((30/13:ℝ)*(1-(q:ℝ))+δ)

theorem main : H1 → H2 → type_of% @DensityHypothesis.guth_maynard_zero_density := by
  rintro ⟨A,hA,hunit⟩ hbands ε hε
  have hm {σ τ t : ℝ} (hle : σ ≤ τ) : zetaZeroCount τ t ≤ zetaZeroCount σ t :=
    count_mono hle le_rfl
  have ht (σ : ℝ) : Monotone (zetaZeroCount σ) := fun _ _ h => count_mono le_rfl h
  have htotal := total_from_unit (zetaZeroCount (1/2)) (ht _) (zetaZeroCount_eq_zero_of_nonpos le_rfl)
    A hA (by
      intro k
      rw [count_split (1/2) k (k+1) (Nat.cast_nonneg _) (by linarith), Nat.cast_add]
      exact add_le_add le_rfl (hunit k))
  apply all_heights_of_dyadic (fun σ T => (zetaZeroCount σ T : ℝ))
    (fun σ _ _ htu => Nat.cast_le.mpr (ht σ htu)) ε hε
  apply uniform_dyadic_bound (fun σ k => (zetaZeroCount σ ((2:ℝ)^k) : ℝ))
    (fun _ _ _ hst => Nat.cast_le.mpr (hm hst)) _ ε hε
  intro q hhalf hlt δ hδ
  by_cases hlo : q ≤ 17/30
  · obtain ⟨C,hC,hB⟩ := low_sigma_of_total zetaZeroCount hm ⟨6*A, by positivity, htotal⟩ δ hδ
    refine ⟨C,hC,1,fun k hk => hB q _ (by simpa using (Rat.cast_le (K := ℝ)).mpr hhalf) (by simpa using (Rat.cast_le (K := ℝ)).mpr hlo) ?_⟩
    simpa using pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hk
  · obtain ⟨C,hC,K,hB⟩ := hbands q (lt_of_not_ge hlo) hlt δ hδ
    have hq : (q:ℝ) < 1 := by exact_mod_cast hlt
    obtain ⟨D,hD,hK⟩ := cumulative_of_eventual_bands
      (fun k => (zetaZeroCount q ((2:ℝ)^k) : ℝ)) _ ((30/13:ℝ)*(1-(q:ℝ))+δ)
      (by linarith) (fun k => by
        rw [count_split q ((2:ℝ)^k) ((2:ℝ)^(k+1)) (by positivity)
          (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (Nat.le_succ k)), Nat.cast_add])
      hC hB
    exact ⟨D,hD,K,hK⟩

end OMA.R_DensityHypothesis_guth_maynard_zero_density_R2
