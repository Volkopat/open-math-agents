import OMAStatements.S_mo_122908

namespace Mo122908

open OMA.S_mo_122908
open scoped InnerProductSpace Classical

noncomputable section

private lemma negativePolar_antitone {d : ℕ} {c : ℝ} {A B : Set (Space d)} (h : A ⊆ B) :
    negativePolar c B ⊆ negativePolar c A :=
  fun _ hy x hx => hy x (h hx)

private lemma convex_negativePolar {d : ℕ} (c : ℝ) (A : Set (Space d)) :
    Convex ℝ (negativePolar c A) := by
  intro y1 hy1 y2 hy2 a b ha hb hab x hx
  have h1 := hy1 x hx
  have h2 := hy2 x hx
  rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
  calc -c = (a + b) * (-c) := by rw [hab, one_mul]
    _ = a * (-c) + b * (-c) := add_mul a b (-c)
    _ ≤ a * ⟪y1, x⟫_ℝ + b * ⟪y2, x⟫_ℝ :=
        add_le_add (mul_le_mul_of_nonneg_left h1 ha) (mul_le_mul_of_nonneg_left h2 hb)

private lemma negativePolar_convexHull {d : ℕ} (c : ℝ) (S : Set (Space d)) :
    negativePolar c (convexHull ℝ S) = negativePolar c S := by
  apply Set.Subset.antisymm
  · exact negativePolar_antitone (subset_convexHull ℝ S)
  · intro y hy x hx
    have hconv : Convex ℝ {z : Space d | -c ≤ ⟪y, z⟫_ℝ} := by
      intro z1 hz1 z2 hz2 a b ha hb hab
      change -c ≤ ⟪y, a • z1 + b • z2⟫_ℝ
      have h1 : -c ≤ ⟪y, z1⟫_ℝ := hz1
      have h2 : -c ≤ ⟪y, z2⟫_ℝ := hz2
      rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
      calc -c = (a + b) * (-c) := by rw [hab, one_mul]
        _ = a * (-c) + b * (-c) := add_mul a b (-c)
        _ ≤ a * ⟪y, z1⟫_ℝ + b * ⟪y, z2⟫_ℝ :=
            add_le_add (mul_le_mul_of_nonneg_left h1 ha) (mul_le_mul_of_nonneg_left h2 hb)
    exact convexHull_min (fun s hs => hy s hs) hconv hx

private lemma convexHull_subset_negativePolar_iff {d : ℕ} (c : ℝ) (S : Set (Space d)) :
    convexHull ℝ S ⊆ negativePolar c (convexHull ℝ S) ↔
      ∀ x ∈ S, ∀ y ∈ S, -c ≤ ⟪x, y⟫_ℝ := by
  rw [negativePolar_convexHull]
  constructor
  · intro h x hx y hy
    exact h (subset_convexHull ℝ S hx) y hy
  · intro h
    exact convexHull_min (fun x hx y hy => h x hx y hy) (convex_negativePolar c S)

private def stdVec {d : ℕ} (k : Fin d) : Space d :=
  WithLp.toLp 2 (Pi.single k (1 : ℝ))

private lemma inner_stdVec {d : ℕ} (y : Space d) (k : Fin d) :
    ⟪y, stdVec k⟫_ℝ = y.ofLp k := by
  rw [PiLp.inner_apply]
  rw [Finset.sum_eq_single k]
  · simp [stdVec]
  · intro i _ hik
    simp [stdVec, hik]
  · intro hk
    exact absurd (Finset.mem_univ k) hk

private lemma norm_stdVec {d : ℕ} (k : Fin d) : ‖stdVec k‖ = 1 := by
  have hsq : ‖stdVec k‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq, inner_stdVec]
    simp [stdVec]
  have hnn : 0 ≤ ‖stdVec k‖ := norm_nonneg _
  nlinarith

private lemma isPolytope_of_bounded_halfspaces {d : ℕ} (J : Finset (Space d × ℝ))
    (hK_ne : {y : Space d | ∀ p ∈ J, p.2 ≤ ⟪y, p.1⟫_ℝ}.Nonempty)
    (hK_bdd : Bornology.IsBounded {y : Space d | ∀ p ∈ J, p.2 ≤ ⟪y, p.1⟫_ℝ}) :
    IsPolytope {y : Space d | ∀ p ∈ J, p.2 ≤ ⟪y, p.1⟫_ℝ} := by
  set K : Set (Space d) := {y : Space d | ∀ p ∈ J, p.2 ≤ ⟪y, p.1⟫_ℝ}
  have hK_closed : IsClosed K := by
    have hEq : K = ⋂ p ∈ (J : Set (Space d × ℝ)), {y : Space d | p.2 ≤ ⟪y, p.1⟫_ℝ} := by
      ext y; simp [K]
    rw [hEq]
    exact isClosed_biInter fun p _ => isClosed_le continuous_const (continuous_id.inner continuous_const)
  have hK_compact : IsCompact K := Metric.isCompact_of_isClosed_isBounded hK_closed hK_bdd
  have hK_convex : Convex ℝ K := by
    intro y1 hy1 y2 hy2 a b ha hb hab p hp
    have h1 := hy1 p hp
    have h2 := hy2 p hp
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
    calc p.2 = (a + b) * p.2 := by rw [hab, one_mul]
      _ = a * p.2 + b * p.2 := add_mul a b p.2
      _ ≤ a * ⟪y1, p.1⟫_ℝ + b * ⟪y2, p.1⟫_ℝ :=
          add_le_add (mul_le_mul_of_nonneg_left h1 ha) (mul_le_mul_of_nonneg_left h2 hb)
  set E : Set (Space d) := Set.extremePoints ℝ K
  let act : E → {s : Finset (Space d × ℝ) // s ∈ J.powerset} :=
    fun x => ⟨J.filter (fun p => ⟪x.val, p.1⟫_ℝ = p.2),
      Finset.mem_powerset.mpr (Finset.filter_subset _ _)⟩
  have hact_inj : Function.Injective act := by
    intro x y hxy
    by_contra hne
    have hne' : x.val ≠ y.val := fun h => hne (Subtype.ext h)
    set v : Space d := y.val - x.val
    have hv : v ≠ 0 := sub_ne_zero.mpr hne'.symm
    have hfilt : J.filter (fun p => ⟪x.val, p.1⟫_ℝ = p.2) =
        J.filter (fun p => ⟪y.val, p.1⟫_ℝ = p.2) := congrArg Subtype.val hxy
    have hact_eq : ∀ p ∈ J, ⟪x.val, p.1⟫_ℝ = p.2 → ⟪v, p.1⟫_ℝ = 0 := by
      intro p hp hx0
      have hmem : p ∈ J.filter (fun q => ⟪y.val, q.1⟫_ℝ = q.2) := by
        rw [← hfilt]; exact Finset.mem_filter.mpr ⟨hp, hx0⟩
      have hy0 : ⟪y.val, p.1⟫_ℝ = p.2 := (Finset.mem_filter.mp hmem).2
      rw [show v = y.val - x.val from rfl, inner_sub_left, hy0, hx0, sub_self]
    let term : (Space d × ℝ) → ℝ := fun p =>
      if ⟪x.val, p.1⟫_ℝ = p.2 then 0 else |⟪v, p.1⟫_ℝ| / (⟪x.val, p.1⟫_ℝ - p.2)
    have hterm_nn : ∀ p ∈ J, 0 ≤ term p := by
      intro p hp
      dsimp only [term]
      split_ifs with heq
      · exact le_rfl
      · have hle : p.2 ≤ ⟪x.val, p.1⟫_ℝ := x.prop.1 p hp
        have hpos : 0 < ⟪x.val, p.1⟫_ℝ - p.2 := sub_pos.mpr (lt_of_le_of_ne hle (Ne.symm heq))
        exact div_nonneg (abs_nonneg _) hpos.le
    let D : ℝ := 1 + ∑ p ∈ J, term p
    have hD_ge1 : 1 ≤ D := by
      have hsum_nn : 0 ≤ ∑ p ∈ J, term p := Finset.sum_nonneg hterm_nn
      linarith
    have hD_pos : 0 < D := by linarith
    let t : ℝ := 1 / D
    have ht_pos : 0 < t := one_div_pos.mpr hD_pos
    have hmem_pm : ∀ s : ℝ, s = t ∨ s = -t → x.val + s • v ∈ K := by
      intro s hs p hp
      rw [inner_add_left, real_inner_smul_left]
      by_cases heq : ⟪x.val, p.1⟫_ℝ = p.2
      · rw [hact_eq p hp heq, mul_zero, add_zero, heq]
      · have hle : p.2 ≤ ⟪x.val, p.1⟫_ℝ := x.prop.1 p hp
        have hgap : 0 < ⟪x.val, p.1⟫_ℝ - p.2 := sub_pos.mpr (lt_of_le_of_ne hle (Ne.symm heq))
        have hle_sum : term p ≤ ∑ q ∈ J, term q := Finset.single_le_sum hterm_nn hp
        have hterm_eq : term p = |⟪v, p.1⟫_ℝ| / (⟪x.val, p.1⟫_ℝ - p.2) := if_neg heq
        have hleD : |⟪v, p.1⟫_ℝ| / (⟪x.val, p.1⟫_ℝ - p.2) ≤ D := by linarith
        have hmul : |⟪v, p.1⟫_ℝ| ≤ D * (⟪x.val, p.1⟫_ℝ - p.2) := (div_le_iff₀ hgap).mp hleD
        have ht_bound : t * |⟪v, p.1⟫_ℝ| ≤ ⟪x.val, p.1⟫_ℝ - p.2 := by
          rw [show t = 1 / D from rfl, one_div, inv_mul_le_iff₀ hD_pos]
          exact hmul
        have habs_s : |s * ⟪v, p.1⟫_ℝ| ≤ ⟪x.val, p.1⟫_ℝ - p.2 := by
          rw [abs_mul]
          have hsabs : |s| = t := by
            rcases hs with rfl | rfl
            · exact abs_of_pos ht_pos
            · rw [abs_neg, abs_of_pos ht_pos]
          rw [hsabs]
          exact ht_bound
        have hneg := neg_abs_le (s * ⟪v, p.1⟫_ℝ)
        linarith
    have hxp : x.val + t • v ∈ K := hmem_pm t (Or.inl rfl)
    have hxm : x.val + (-t) • v ∈ K := hmem_pm (-t) (Or.inr rfl)
    have hseg : x.val ∈ openSegment ℝ (x.val + (-t) • v) (x.val + t • v) := by
      refine ⟨(1 : ℝ) / 2, (1 : ℝ) / 2, by norm_num, by norm_num, by norm_num, ?_⟩
      module
    have hEq := x.prop.2 hxm hxp hseg
    have htv : (-t) • v = 0 := add_eq_left.mp hEq
    rcases smul_eq_zero.mp htv with ht0 | hv0
    · linarith
    · exact hv hv0
  have hE_fin : E.Finite := by
    have : Finite E := Finite.of_injective act hact_inj
    exact Set.toFinite E
  have hconv_eq : convexHull ℝ E = K := by
    have hcl := closure_convexHull_extremePoints hK_compact hK_convex
    have hcomp : IsCompact (convexHull ℝ E) := hE_fin.isCompact_convexHull ℝ
    rw [hcomp.isClosed.closure_eq] at hcl
    exact hcl
  refine ⟨hE_fin.toFinset, ?_, ?_⟩
  · by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    have hE_empty : E = ∅ := by
      ext z
      have := hE_fin.mem_toFinset (a := z)
      rw [hempty] at this
      simpa using this
    rw [hE_empty, convexHull_empty] at hconv_eq
    exact Set.Nonempty.ne_empty hK_ne hconv_eq.symm
  · rw [Set.Finite.coe_toFinset, hconv_eq]

private lemma enlarge_with_cross {d : ℕ} {c : ℝ} (hc : 0 < c) {S : Finset (Space d)}
    (hSne : S.Nonempty) (hS : ∀ x ∈ S, ∀ y ∈ S, -c ≤ ⟪x, y⟫_ℝ) :
    ∃ S0 : Finset (Space d), S ⊆ S0 ∧ S0.Nonempty ∧
      (∀ x ∈ S0, ∀ y ∈ S0, -c ≤ ⟪x, y⟫_ℝ) ∧
      Bornology.IsBounded (negativePolar c (S0 : Set (Space d))) := by
  let M : ℝ := 1 + ∑ x ∈ S, ‖x‖
  have hM_ge1 : 1 ≤ M := by
    have : 0 ≤ ∑ x ∈ S, ‖x‖ := Finset.sum_nonneg fun x _ => norm_nonneg x
    linarith
  have hM_pos : 0 < M := by linarith
  have hnorm_le_M : ∀ x ∈ S, ‖x‖ ≤ M := fun x hx => by
    have h1 : ‖x‖ ≤ ∑ y ∈ S, ‖y‖ := Finset.single_le_sum (fun y _ => norm_nonneg y) hx
    linarith
  let ε : ℝ := min (c / M) (min 1 c)
  have hε_pos : 0 < ε := lt_min (div_pos hc hM_pos) (lt_min zero_lt_one hc)
  have hεM : ε * M ≤ c := (le_div_iff₀ hM_pos).mp (min_le_left _ _)
  have hε1 : ε ≤ 1 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hεc : ε ≤ c := le_trans (min_le_right _ _) (min_le_right _ _)
  have hεsq : ε * ε ≤ c := by nlinarith
  let Cp : Finset (Space d) := Finset.univ.image fun k : Fin d => ε • stdVec k
  let Cm : Finset (Space d) := Finset.univ.image fun k : Fin d => (-ε) • stdVec k
  let S0 : Finset (Space d) := S ∪ (Cp ∪ Cm)
  have hnorm_C : ∀ z ∈ Cp ∪ Cm, ‖z‖ = ε := by
    intro z hz
    rcases Finset.mem_union.mp hz with hzp | hzm
    · rcases Finset.mem_image.mp hzp with ⟨k, _, rfl⟩
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hε_pos, norm_stdVec, mul_one]
    · rcases Finset.mem_image.mp hzm with ⟨k, _, rfl⟩
      rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos hε_pos, norm_stdVec, mul_one]
  refine ⟨S0, Finset.subset_union_left, hSne.mono Finset.subset_union_left, ?_, ?_⟩
  · intro x hx y hy
    rcases Finset.mem_union.mp hx with hxS | hxC <;> rcases Finset.mem_union.mp hy with hyS | hyC
    · exact hS x hxS y hyS
    · have hcs := abs_real_inner_le_norm x y
      rw [hnorm_C y hyC] at hcs
      have h1 : ‖x‖ * ε ≤ c := by nlinarith [hnorm_le_M x hxS]
      linarith [neg_abs_le ⟪x, y⟫_ℝ]
    · have hcs := abs_real_inner_le_norm x y
      rw [hnorm_C x hxC] at hcs
      have h1 : ε * ‖y‖ ≤ c := by nlinarith [hnorm_le_M y hyS]
      linarith [neg_abs_le ⟪x, y⟫_ℝ]
    · have hcs := abs_real_inner_le_norm x y
      rw [hnorm_C x hxC, hnorm_C y hyC] at hcs
      linarith [neg_abs_le ⟪x, y⟫_ℝ]
  · rw [Metric.isBounded_iff_subset_closedBall (0 : Space d)]
    refine ⟨(d : ℝ) * (c / ε) + 1, fun y hy => ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    have hcoord : ∀ k : Fin d, |y.ofLp k| ≤ c / ε := by
      intro k
      have hp : ε • stdVec k ∈ S0 :=
        Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩))
      have hm : (-ε) • stdVec k ∈ S0 :=
        Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩))
      have h1 : -c ≤ ⟪y, ε • stdVec k⟫_ℝ := hy (ε • stdVec k) hp
      have h2 : -c ≤ ⟪y, (-ε) • stdVec k⟫_ℝ := hy ((-ε) • stdVec k) hm
      rw [real_inner_smul_right, inner_stdVec] at h1 h2
      rw [abs_le]
      constructor
      · rw [← neg_div, div_le_iff₀ hε_pos]; linarith
      · rw [le_div_iff₀ hε_pos]; linarith
    have hsq : ‖y‖ ^ 2 ≤ ((d : ℝ) * (c / ε) + 1) ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply]
      have hsum : ∑ k : Fin d, inner ℝ (y.ofLp k) (y.ofLp k) ≤ (d : ℝ) * (c / ε) ^ 2 := by
        calc ∑ k : Fin d, inner ℝ (y.ofLp k) (y.ofLp k)
            = ∑ k : Fin d, (y.ofLp k) ^ 2 := by
              refine Finset.sum_congr rfl fun k _ => ?_
              simp [sq]
          _ ≤ ∑ _k : Fin d, (c / ε) ^ 2 := by
              refine Finset.sum_le_sum fun k _ => ?_
              have hk := hcoord k
              have hnn : 0 ≤ c / ε := div_nonneg hc.le hε_pos.le
              rw [← sq_abs]
              exact sq_le_sq' (by linarith [abs_nonneg (y.ofLp k)]) hk
          _ = (d : ℝ) * (c / ε) ^ 2 := by simp
      have hce_nn : 0 ≤ c / ε := div_nonneg hc.le hε_pos.le
      have hd_cases : d = 0 ∨ 1 ≤ d := by omega
      rcases hd_cases with rfl | hd1
      · simp at hsum ⊢
      · have hd_ge1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd1
        have hdd : (d : ℝ) ≤ (d : ℝ) ^ 2 := by nlinarith
        nlinarith [sq_nonneg (c / ε)]
    have hR_nn : 0 ≤ (d : ℝ) * (c / ε) + 1 := by positivity
    nlinarith [norm_nonneg y]

private def signVec {d : ℕ} (σ : Fin d → Bool) (k : Fin d) : Space d :=
  (if σ k then (1 : ℝ) else -1) • stdVec k

private def orthant {d : ℕ} (σ : Fin d → Bool) : Set (Space d) :=
  {y : Space d | ∀ k : Fin d, 0 ≤ ⟪y, signVec σ k⟫_ℝ}

private lemma mem_orthant_self {d : ℕ} (y : Space d) :
    y ∈ orthant (fun k => decide (0 ≤ y.ofLp k)) := by
  intro k
  dsimp only [signVec]
  rw [real_inner_smul_right, inner_stdVec]
  by_cases h : 0 ≤ y.ofLp k
  · simp [h]
  · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte]; linarith

private lemma inner_nonneg_of_mem_orthant {d : ℕ} {σ : Fin d → Bool} {x y : Space d}
    (hx : x ∈ orthant σ) (hy : y ∈ orthant σ) : 0 ≤ ⟪x, y⟫_ℝ := by
  rw [PiLp.inner_apply]
  refine Finset.sum_nonneg fun k _ => ?_
  have hxk := hx k
  have hyk := hy k
  dsimp only [signVec] at hxk hyk
  rw [real_inner_smul_right, inner_stdVec] at hxk hyk
  simp only [RCLike.inner_apply, conj_trivial]
  cases hσ : σ k <;> simp [hσ] at hxk hyk <;> nlinarith

private lemma orthant_step {d : ℕ} {c : ℝ} (hc : 0 < c) (σ : Fin d → Bool)
    {V : Finset (Space d)} (hVne : V.Nonempty)
    (hV : ∀ x ∈ V, ∀ y ∈ V, -c ≤ ⟪x, y⟫_ℝ)
    (hVbdd : Bornology.IsBounded (negativePolar c (V : Set (Space d)))) :
    ∃ V' : Finset (Space d), V ⊆ V' ∧ V'.Nonempty ∧
      (∀ x ∈ V', ∀ y ∈ V', -c ≤ ⟪x, y⟫_ℝ) ∧
      negativePolar c (V : Set (Space d)) ∩ orthant σ ⊆ convexHull ℝ (V' : Set (Space d)) := by
  let J : Finset (Space d × ℝ) :=
    (V.image fun v => (v, -c)) ∪ (Finset.univ.image fun k : Fin d => (signVec σ k, (0 : ℝ)))
  have hK_eq : {y : Space d | ∀ p ∈ J, p.2 ≤ ⟪y, p.1⟫_ℝ} =
      negativePolar c (V : Set (Space d)) ∩ orthant σ := by
    ext y
    simp only [Set.mem_ofPred_eq, J, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and,
      Set.mem_inter_iff, negativePolar, Finset.mem_coe, orthant]
    constructor
    · intro h
      exact ⟨fun x hx => h (x, -c) (Or.inl ⟨x, hx, rfl⟩),
        fun k => h (signVec σ k, 0) (Or.inr ⟨k, rfl⟩)⟩
    · rintro ⟨h1, h2⟩ p (⟨x, hx, rfl⟩ | ⟨k, rfl⟩)
      · exact h1 x hx
      · exact h2 k
  have h0_mem : (0 : Space d) ∈ negativePolar c (V : Set (Space d)) ∩ orthant σ :=
    ⟨fun x _ => by rw [inner_zero_left]; linarith, fun k => by rw [inner_zero_left]⟩
  have hpoly : IsPolytope (negativePolar c (V : Set (Space d)) ∩ orthant σ) := by
    rw [← hK_eq]
    exact isPolytope_of_bounded_halfspaces J
      (by rw [hK_eq]; exact ⟨0, h0_mem⟩)
      (by rw [hK_eq]; exact hVbdd.subset Set.inter_subset_left)
  rcases hpoly with ⟨W, _, hWconv⟩
  refine ⟨V ∪ W, Finset.subset_union_left, hVne.mono Finset.subset_union_left, ?_, ?_⟩
  · have hWsub : (W : Set (Space d)) ⊆ negativePolar c (V : Set (Space d)) ∩ orthant σ := by
      rw [hWconv]; exact subset_convexHull ℝ _
    intro x hx y hy
    rcases Finset.mem_union.mp hx with hxV | hxW <;> rcases Finset.mem_union.mp hy with hyV | hyW
    · exact hV x hxV y hyV
    · rw [real_inner_comm]
      exact (hWsub hyW).1 x hxV
    · exact (hWsub hxW).1 y hyV
    · linarith [inner_nonneg_of_mem_orthant (hWsub hxW).2 (hWsub hyW).2]
  · rw [hWconv]
    exact convexHull_mono (by intro x hx; exact Finset.mem_coe.mpr (Finset.mem_union_right _ hx))

private lemma orthant_fold {d : ℕ} {c : ℝ} (hc : 0 < c) :
    ∀ (L : List (Fin d → Bool)) (V : Finset (Space d)),
      V.Nonempty →
      (∀ x ∈ V, ∀ y ∈ V, -c ≤ ⟪x, y⟫_ℝ) →
      Bornology.IsBounded (negativePolar c (V : Set (Space d))) →
      ∃ V' : Finset (Space d), V ⊆ V' ∧ V'.Nonempty ∧
        (∀ x ∈ V', ∀ y ∈ V', -c ≤ ⟪x, y⟫_ℝ) ∧
        ∀ σ ∈ L, negativePolar c (V' : Set (Space d)) ∩ orthant σ ⊆ convexHull ℝ (V' : Set (Space d))
  | [], V, hVne, hV, _ => ⟨V, Finset.Subset.rfl, hVne, hV, fun _ h => absurd h (List.not_mem_nil)⟩
  | σ :: rest, V, hVne, hV, hVbdd => by
    obtain ⟨V1, hVV1, hV1ne, hV1, hσ⟩ := orthant_step hc σ hVne hV hVbdd
    have hV1bdd : Bornology.IsBounded (negativePolar c (V1 : Set (Space d))) :=
      hVbdd.subset (negativePolar_antitone (Finset.coe_subset.mpr hVV1))
    obtain ⟨V', hV1V', hV'ne, hV', hrest⟩ := orthant_fold hc rest V1 hV1ne hV1 hV1bdd
    refine ⟨V', Finset.Subset.trans hVV1 hV1V', hV'ne, hV', fun τ hτ => ?_⟩
    rcases List.mem_cons.mp hτ with hτσ | hτrest
    · rw [hτσ]
      intro y hy
      have hy1 : y ∈ negativePolar c (V : Set (Space d)) ∩ orthant σ :=
        ⟨negativePolar_antitone (Finset.coe_subset.mpr (Finset.Subset.trans hVV1 hV1V')) hy.1, hy.2⟩
      exact convexHull_mono (Finset.coe_subset.mpr hV1V') (hσ hy1)
    · exact hrest τ hτrest

end

end Mo122908

theorem OMA.solution : type_of% @OMA.S_mo_122908.main := by
  intro d c P hc hpoly hsub
  rcases hpoly with ⟨S, hSne, rfl⟩
  have hS := (Mo122908.convexHull_subset_negativePolar_iff c (S : Set (OMA.S_mo_122908.Space d))).mp hsub
  obtain ⟨S0, hSS0, hS0ne, hS0, hS0bdd⟩ := Mo122908.enlarge_with_cross hc hSne hS
  let L : List (Fin d → Bool) := (Finset.univ : Finset (Fin d → Bool)).toList
  obtain ⟨Qverts, hS0Q, hQne, hQ, hcov⟩ := Mo122908.orthant_fold hc L S0 hS0ne hS0 hS0bdd
  refine ⟨convexHull ℝ (Qverts : Set (OMA.S_mo_122908.Space d)), ⟨Qverts, hQne, rfl⟩,
    convexHull_mono (Finset.coe_subset.mpr (Finset.Subset.trans hSS0 hS0Q)), ?_⟩
  apply Set.Subset.antisymm
  · exact (Mo122908.convexHull_subset_negativePolar_iff c _).mpr hQ
  · intro y hy
    rw [Mo122908.negativePolar_convexHull] at hy
    let σ : Fin d → Bool := fun k => decide (0 ≤ y.ofLp k)
    have hσL : σ ∈ L := Finset.mem_toList.mpr (Finset.mem_univ σ)
    exact hcov σ hσL ⟨hy, Mo122908.mem_orthant_self y⟩
