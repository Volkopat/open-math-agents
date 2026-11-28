import FormalConjectures.ErdosProblems.«626»

/-!
# A dyadic criterion for the limit in Erdős 626(i)

Credit: @Pixelstorm44. Padding witnesses by isolated vertices makes the extremal
threshold monotone. A bounded loss under combining dyadic orders gives a
subadditive sequence after changing sign and shifting by that loss. A linear
bound gives a finite Fekete limit, and adjacent powers of two bracket every order.
-/

open SimpleGraph Erdos626 Filter Set
open scoped Topology

namespace OMA.R_Erdos626_erdos_626_parts_i_R1

/-- A copy of a graph without isolated vertices cannot use any padding vertex. -/
private lemma unpad_copy {U V W : Type*} {K : SimpleGraph U} {G : SimpleGraph V}
    (f : V ↪ W) (hK : ∀ u, ∃ v, K.Adj u v) (h : K ⊑ G.map f) : K ⊑ G := by
  classical
  let c := h.some
  have hr (x : U) : ∃ y, f y = c x := by
    obtain ⟨z, hz⟩ := hK x
    obtain ⟨a, b, _, ha, _⟩ := (map_adj f G _ _).mp (c.toHom.map_adj hz)
    exact ⟨a, ha⟩
  choose lift hLift using hr
  refine ⟨⟨⟨lift, ?_⟩, ?_⟩⟩
  · intro a b hab
    apply (map_adj_apply (f := f)).mp
    rw [hLift, hLift]
    exact c.toHom.map_adj hab
  · intro a b hab
    change lift a = lift b at hab
    apply c.injective
    exact (hLift a).symm.trans ((congrArg f hab).trans (hLift b))

private lemma unpad_girth {V W : Type*} (G : SimpleGraph V) (f : V ↪ W) :
    G.egirth ≤ (G.map f).egirth := by
  apply le_egirth.mpr
  intro a w hw
  have hl := hw.three_le_length
  have hc := (cycleGraph_isContained_iff (by omega : 2 < w.length)).mpr ⟨a,w,hw,rfl⟩
  have hn : ∀ u, ∃ v, (cycleGraph w.length).Adj u v := by
    generalize w.length = t at hl ⊢
    obtain ⟨d, rfl⟩ : ∃ d, t = d + 2 := ⟨t - 2, by omega⟩
    intro u
    exact ⟨u + 1, cycleGraph_adj.mpr (Or.inr (by abel))⟩
  obtain ⟨b, p, hp, he⟩ := (cycleGraph_isContained_iff (by omega : 2 < w.length)).mp
    (unpad_copy f hn hc)
  rw [← he]
  exact egirth_le_length hp

private lemma bounded_thresholds (k n : ℕ) (hk : 3 ≤ k) :
    BddAbove {m : ℕ | ∃ G : SimpleGraph (Fin n), G.chromaticNumber = k ∧ (m : ℕ∞) < G.egirth} := by
  refine ⟨n, ?_⟩
  rintro m ⟨G,hG,hm⟩
  have hcyc : ¬ G.IsAcyclic := by
    intro hA
    have hc := hA.colorable_two.chromaticNumber_le
    rw [hG] at hc
    have : k ≤ 2 := by exact_mod_cast hc
    omega
  obtain ⟨a,w,hw,he⟩ := exists_egirth_eq_length.mpr hcyc
  have hl := hw.three_le_length
  obtain ⟨c⟩ := (cycleGraph_isContained_iff (by omega : 2 < w.length)).mpr ⟨a,w,hw,rfl⟩
  have hc : w.length ≤ n := by simpa using Fintype.card_le_of_injective _ c.injective
  rw [he] at hm
  have : m < w.length := by exact_mod_cast hm
  omega

private lemma girth_monotone (k : ℕ) (hk : 3 ≤ k) : Monotone (g k) := by
  intro n m hnm
  apply csSup_le_csSup' (bounded_thresholds k m hk)
  rintro t ⟨G,hG,ht⟩
  let f := Fin.castLEEmb hnm
  have : NeZero k := ⟨by omega⟩
  refine ⟨G.map f, le_antisymm ?_ ?_, ht.trans_le (unpad_girth G f)⟩
  · exact ((chromaticNumber_le_iff_colorable.mp hG.le).map f).chromaticNumber_le
  · rw [← hG]
    exact chromaticNumber_mono_of_hom (Embedding.map f G).toHom

/-- Combining two dyadic vertex budgets adds their girth thresholds up to a fixed loss. -/
def H1 : Prop := ∀ k : ℕ, 4 ≤ k → ∃ C : ℕ, ∀ i j : ℕ,
    g k (2^i) + g k (2^j) ≤ g k (2^(i+j)) + C

/-- A linear upper bound in the dyadic exponent, a weak Moore-type estimate. -/
def H2 : Prop := ∀ k : ℕ, 4 ≤ k → ∃ B : ℝ, ∀ i : ℕ, 0 < i →
    (g k (2^i) : ℝ) ≤ B * i

lemma dyadic_slope (k : ℕ) (hk : 4 ≤ k) (h₁ : H1) (h₂ : H2) :
    ∃ S : ℝ, Tendsto (fun i : ℕ ↦ (g k (2^i) : ℝ) / i) atTop (𝓝 S) := by
  obtain ⟨C,hC⟩ := h₁ k hk
  obtain ⟨B,hB⟩ := h₂ k hk
  let u (i : ℕ) : ℝ := C - (g k (2^i) : ℝ)
  have hu : Subadditive u := by
    intro i j
    have h : (g k (2^i) : ℝ) + g k (2^j) ≤ g k (2^(i+j)) + (C : ℝ) := by
      exact_mod_cast hC i j
    dsimp [u]
    linarith
  have hb : BddBelow (range (fun i : ℕ ↦ u i / i)) := by
    refine ⟨min 0 (-B), ?_⟩
    rintro _ ⟨i,rfl⟩
    rcases i.eq_zero_or_pos with rfl | hi
    · simpa using min_le_left (0 : ℝ) (-B)
    · apply (min_le_right 0 (-B)).trans
      apply (le_div_iff₀ (by exact_mod_cast hi : (0 : ℝ) < i)).mpr
      dsimp [u]
      have hc : (0 : ℝ) ≤ C := by positivity
      linarith [hB i hi]
  refine ⟨-hu.lim, ?_⟩
  have h := (tendsto_const_div_atTop_nhds_zero_nat (C : ℝ)).sub (hu.tendsto_lim hb)
  simpa only [u, sub_div, sub_sub_cancel, zero_sub] using h

/-- Interpolation between consecutive powers of two only uses monotonicity. -/
private lemma interpolate (a : ℕ → ℕ) (ha : Monotone a) (S : ℝ)
    (hs : Tendsto (fun i : ℕ ↦ (a (2^i) : ℝ) / i) atTop (𝓝 S)) :
    Tendsto (fun n : ℕ ↦ (a n : ℝ) / Real.log n) atTop (𝓝 (S * (Real.log 2)⁻¹)) := by
  let d := Nat.log 2
  have hlog : Tendsto (fun n : ℕ ↦ Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hd : Tendsto d atTop atTop := by
    have h := tendsto_nat_floor_atTop.comp
      ((Real.tendsto_logb_atTop (by norm_num : (1 : ℝ) < 2)).comp tendsto_natCast_atTop_atTop)
    simpa only [Function.comp_def, ← Nat.cast_ofNat (R := ℝ) (n := 2), Real.natFloor_logb_natCast] using h
  have hscale : Tendsto (fun n : ℕ ↦ (d n : ℝ) / Real.log n) atTop (𝓝 (Real.log 2)⁻¹) := by
    have h := (tendsto_nat_floor_mul_div_atTop (a := (Real.log 2)⁻¹) (by positivity)).comp hlog
    refine h.congr fun n ↦ ?_
    dsimp [Function.comp_def, d]
    rw [mul_comm, ← div_eq_mul_inv, ← Real.logb]
    congr 2
    exact Real.natFloor_logb_natCast 2 n
  have hsucc : Tendsto (fun n ↦ d n + 1) atTop atTop := (tendsto_add_atTop_nat 1).comp hd
  have hplus : Tendsto (fun n : ℕ ↦ ((d n + 1 : ℕ) : ℝ) / Real.log n) atTop
      (𝓝 (Real.log 2)⁻¹) := by
    have h := hscale.add ((tendsto_const_nhds (x := (1 : ℝ))).div_atTop hlog)
    simpa only [add_zero, Nat.cast_add_one, add_div] using h
  have bound (e : ℕ → ℕ) (he : Tendsto e atTop atTop)
      (h : Tendsto (fun n : ℕ ↦ (e n : ℝ) / Real.log n) atTop (𝓝 (Real.log 2)⁻¹)) :
      Tendsto (fun n : ℕ ↦ (a (2^(e n)) : ℝ) / Real.log n) atTop (𝓝 (S * (Real.log 2)⁻¹)) := by
    refine ((hs.comp he).mul h).congr' ?_
    filter_upwards [he.eventually (eventually_ge_atTop 1)] with n hn
    dsimp
    have hn' : (e n : ℝ) ≠ 0 := by exact_mod_cast (by omega : e n ≠ 0)
    field_simp
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (bound d hd hscale) (bound _ hsucc hplus)
  · filter_upwards [eventually_ge_atTop 2] with n hn
    apply div_le_div_of_nonneg_right _ (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n)))
    exact_mod_cast ha (Nat.pow_log_le_self 2 (by omega : n ≠ 0))
  · filter_upwards [eventually_ge_atTop 2] with n hn
    apply div_le_div_of_nonneg_right _ (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n)))
    exact_mod_cast ha (Nat.lt_pow_succ_log_self (by decide : 1 < 2) n).le

theorem main : H1 → H2 → type_of% @Erdos626.erdos_626.parts.i := by
  intro h₁ h₂ k hk
  obtain ⟨S,hs⟩ := dyadic_slope k hk h₁ h₂
  exact ⟨_, interpolate _ (girth_monotone k (by omega)) S hs⟩

end OMA.R_Erdos626_erdos_626_parts_i_R1
