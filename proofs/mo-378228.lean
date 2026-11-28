import OMAStatements.S_mo_378228

open Set BigOperators
open OMA.S_mo_378228

namespace OMA.P_mo_378228

private lemma embed_zero (n : ℕ) : embed (0 : Fin n → ℚ) = 0 := by
  ext j
  simp [embed]

private lemma embed_add {n : ℕ} (a b : Fin n → ℚ) :
    embed (a + b) = embed a + embed b := by
  ext j
  simp [embed]

private lemma embed_sub {n : ℕ} (a b : Fin n → ℚ) :
    embed (a - b) = embed a - embed b := by
  ext j
  simp [embed]

private lemma embed_smul {n : ℕ} (c : ℚ) (a : Fin n → ℚ) :
    embed (c • a) = (c : ℝ) • embed a := by
  ext j
  simp [embed]

private lemma inner_embed {n : ℕ} (a b : Fin n → ℚ) :
    inner ℝ (embed a) (embed b) = ((∑ j : Fin n, a j * b j : ℚ) : ℝ) := by
  rw [PiLp.inner_apply]
  push_cast
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [embed, RCLike.inner_apply, mul_comm]

private lemma norm_sq_embed {n : ℕ} (a : Fin n → ℚ) :
    ‖embed a‖ ^ 2 = ((∑ j : Fin n, (a j) ^ 2 : ℚ) : ℝ) := by
  rw [← real_inner_self_eq_norm_sq, inner_embed]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

end OMA.P_mo_378228

open OMA.P_mo_378228 in
theorem OMA.solution : type_of% @OMA.S_mo_378228.main := by
  intro n k hk V q
  let v : Fin k → E n := fun i => embed (V i)
  let K : Set (E n) := poly V
  have hK_conv : Convex ℝ K := convex_convexHull ℝ _
  have hK_ne : K.Nonempty := ⟨v ⟨0, hk⟩, subset_convexHull ℝ _ ⟨⟨0, hk⟩, rfl⟩⟩
  have hK_compact : IsCompact K := (Set.finite_range v).isCompact_convexHull ℝ
  have hcont : ContinuousOn (fun x : E n => ‖embed q - x‖) K :=
    (continuous_const.sub continuous_id).norm.continuousOn
  obtain ⟨p, hpK, hp_min⟩ := hK_compact.exists_isMinOn hK_ne hcont
  have h_inner : ∀ x ∈ K, inner ℝ (embed q - p) (x - p) ≤ 0 := by
    intro x hx
    by_contra hnot
    have hpos : 0 < inner ℝ (embed q - p) (x - p) := lt_of_not_ge hnot
    set c : ℝ := inner ℝ (embed q - p) (x - p)
    set d : ℝ := ‖x - p‖ ^ 2 + 1
    have hd_pos : 0 < d := by positivity
    set t : ℝ := min 1 (c / d)
    have ht_pos : 0 < t := lt_min zero_lt_one (div_pos hpos hd_pos)
    have ht_le_one : t ≤ 1 := min_le_left _ _
    have ht_le_cd : t ≤ c / d := min_le_right _ _
    have hyt_mem : (1 - t) • p + t • x ∈ K :=
      hK_conv hpK hx (by linarith) (le_of_lt ht_pos) (by ring)
    have hmin_le : ‖embed q - p‖ ≤ ‖embed q - ((1 - t) • p + t • x)‖ := hp_min hyt_mem
    have hsq_le : ‖embed q - p‖ ^ 2 ≤ ‖embed q - ((1 - t) • p + t • x)‖ ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hmin_le 2
    have hrew : embed q - ((1 - t) • p + t • x) = (embed q - p) - t • (x - p) := by
      rw [sub_smul, one_smul, smul_sub]
      abel
    have hrhs : ‖embed q - ((1 - t) • p + t • x)‖ ^ 2 =
        ‖embed q - p‖ ^ 2 - 2 * (t * c) + t ^ 2 * ‖x - p‖ ^ 2 := by
      rw [hrew, norm_sub_sq_real, inner_smul_right, norm_smul, Real.norm_of_nonneg (le_of_lt ht_pos),
        mul_pow]
    rw [hrhs] at hsq_le
    have h2tc : 2 * t * c ≤ t ^ 2 * ‖x - p‖ ^ 2 := by linarith
    have h2c : 2 * c ≤ t * ‖x - p‖ ^ 2 := by
      nlinarith
    have htd : t * d ≤ c := (le_div_iff₀ hd_pos).mp ht_le_cd
    have hlt : t * ‖x - p‖ ^ 2 < c := by
      have : t * ‖x - p‖ ^ 2 + t = t * d := by ring
      linarith
    linarith
  have hpyth : ∀ x ∈ K, ‖embed q - p‖ ^ 2 + ‖x - p‖ ^ 2 ≤ ‖embed q - x‖ ^ 2 := by
    intro x hx
    have hsub : embed q - x = (embed q - p) - (x - p) := by abel
    have hrhs : ‖embed q - x‖ ^ 2 =
        ‖embed q - p‖ ^ 2 - 2 * inner ℝ (embed q - p) (x - p) + ‖x - p‖ ^ 2 := by
      rw [hsub, norm_sub_sq_real]
    have hi := h_inner x hx
    linarith
  let C : Set (E n) :=
    { x | ∃ w : Fin k → ℝ, (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 1) ∧ ∑ i, w i • v i = x }
  have hC_sub : range v ⊆ C := by
    rintro _ ⟨i, rfl⟩
    refine ⟨fun j => if j = i then 1 else 0, ?_, ?_, ?_⟩
    · intro j; dsimp; split_ifs <;> norm_num
    · simp
    · simp
  have hC_conv : Convex ℝ C := by
    rintro x ⟨wx, hwx0, hwx1, hwx⟩ y ⟨wy, hwy0, hwy1, hwy⟩ a b ha hb hab
    refine ⟨fun i => a * wx i + b * wy i, ?_, ?_, ?_⟩
    · intro i; exact add_nonneg (mul_nonneg ha (hwx0 i)) (mul_nonneg hb (hwy0 i))
    · simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum, hwx1, hwy1]
      linarith
    · simp_rw [add_smul, Finset.sum_add_distrib, mul_smul, ← Finset.smul_sum, hwx, hwy]
  have hKC : K ⊆ C := convexHull_min hC_sub hC_conv
  obtain ⟨w, hw0, hw1, hwp⟩ := hKC hpK
  let S : Finset (Fin k) := Finset.univ.filter (fun i => 0 < w i)
  have hS_ne : S.Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    have hw_zero : ∀ i : Fin k, w i = 0 := by
      intro i
      have hi : i ∉ S := by rw [hne]; simp
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hi
      exact le_antisymm hi (hw0 i)
    have hsum0 : ∑ i : Fin k, w i = 0 := Finset.sum_eq_zero fun i _ => hw_zero i
    linarith
  obtain ⟨i0, hi0⟩ := hS_ne
  have h_orth_vert : ∀ i ∈ S, inner ℝ (embed q - p) (v i - p) = 0 := by
    have hsum_zero : ∑ i : Fin k, -(w i * inner ℝ (embed q - p) (v i - p)) = 0 := by
      rw [Finset.sum_neg_distrib]
      have hsum_inner : ∑ i : Fin k, w i * inner ℝ (embed q - p) (v i - p) = 0 := by
        have h1 : ∑ i : Fin k, w i * inner ℝ (embed q - p) (v i - p) =
            inner ℝ (embed q - p) (∑ i : Fin k, w i • (v i - p)) := by
          rw [inner_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [inner_smul_right]
        rw [h1]
        have h2 : ∑ i : Fin k, w i • (v i - p) = 0 := by
          simp_rw [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hwp, hw1, one_smul, sub_self]
        rw [h2, inner_zero_right]
      linarith
    have hnonneg : ∀ i ∈ Finset.univ, 0 ≤ -(w i * inner ℝ (embed q - p) (v i - p)) := by
      intro i _
      have hvi : v i ∈ K := subset_convexHull ℝ _ ⟨i, rfl⟩
      have hi := h_inner (v i) hvi
      have hwi := hw0 i
      nlinarith
    have hall := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum_zero
    intro i hiS
    have hi0' := hall i (Finset.mem_univ i)
    have hwi_pos : 0 < w i := (Finset.mem_filter.mp hiS).2
    have hmul0 : w i * inner ℝ (embed q - p) (v i - p) = 0 := by linarith
    exact (mul_eq_zero.mp hmul0).resolve_left (ne_of_gt hwi_pos)
  have h_orth_diff : ∀ i ∈ S, inner ℝ (embed q - p) (v i - v i0) = 0 := by
    intro i hi
    have hrew : v i - v i0 = (v i - p) - (v i0 - p) := by abel
    rw [hrew, inner_sub_right, h_orth_vert i hi, h_orth_vert i0 hi0, sub_self]
  let WQ : Submodule ℚ (Fin n → ℚ) :=
    Submodule.span ℚ ((fun i => V i - V i0) '' (S : Set (Fin k)))
  let WR : Submodule ℝ (E n) :=
    Submodule.span ℝ ((fun i => v i - v i0) '' (S : Set (Fin k)))
  have hp_mem_WR : p - v i0 ∈ WR := by
    have hw_zero_outside : ∀ i ∈ Finset.univ, i ∉ S → w i = 0 := by
      intro i _ hiS
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hiS
      exact le_antisymm hiS (hw0 i)
    have hsumS1 : ∑ i ∈ S, w i = 1 := by
      rw [Finset.sum_subset (Finset.subset_univ S) hw_zero_outside, hw1]
    have hsumSp : ∑ i ∈ S, w i • v i = p := by
      have hsub_zero : ∀ i ∈ Finset.univ, i ∉ S → w i • v i = 0 := by
        intro i hi hiS
        rw [hw_zero_outside i hi hiS, zero_smul]
      rw [Finset.sum_subset (Finset.subset_univ S) hsub_zero, hwp]
    have hdecomp : p - v i0 = ∑ i ∈ S, w i • (v i - v i0) := by
      simp_rw [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hsumSp, hsumS1, one_smul]
    rw [hdecomp]
    refine WR.sum_mem fun i hi => WR.smul_mem _ ?_
    exact Submodule.subset_span ⟨i, hi, rfl⟩
  have h_orth_WR : ∀ y ∈ WR, inner ℝ (embed q - p) y = 0 := by
    intro y hy
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
    · rintro _ ⟨i, hi, rfl⟩
      exact h_orth_diff i hi
    · exact inner_zero_right _
    · intro x z _ _ hx hz
      rw [inner_add_right, hx, hz, add_zero]
    · intro c x _ hx
      rw [inner_smul_right, hx, mul_zero]
  have hembed_WQ : ∀ u ∈ WQ, embed u ∈ WR := by
    intro u hu
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hu
    · rintro _ ⟨i, hi, rfl⟩
      rw [embed_sub]
      exact Submodule.subset_span ⟨i, hi, rfl⟩
    · rw [embed_zero]
      exact WR.zero_mem
    · intro x z _ _ hx hz
      rw [embed_add]
      exact WR.add_mem hx hz
    · intro c x _ hx
      rw [embed_smul]
      exact WR.smul_mem (c : ℝ) hx
  let ψ : WQ →ₗ[ℚ] Module.Dual ℚ WQ :=
    { toFun := fun u =>
        { toFun := fun z => ∑ j : Fin n, u.1 j * z.1 j
          map_add' := fun z1 z2 => by
            simp only [Submodule.coe_add, Pi.add_apply, mul_add, Finset.sum_add_distrib]
          map_smul' := fun c z => by
            simp only [SetLike.val_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
              Finset.mul_sum]
            refine Finset.sum_congr rfl fun j _ => by ring }
      map_add' := fun u1 u2 => by
        ext z
        simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply, Submodule.coe_add,
          Pi.add_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := fun c u => by
        ext z
        simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, SetLike.val_smul,
          Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => by ring }
  have hψ_inj : Function.Injective ψ := by
    rw [injective_iff_map_eq_zero]
    intro u hu
    have h0 : ∑ j : Fin n, u.1 j * u.1 j = 0 := by
      have := LinearMap.congr_fun hu u
      simpa [ψ] using this
    have hnonneg : ∀ j ∈ Finset.univ, 0 ≤ u.1 j * u.1 j := fun j _ => mul_self_nonneg (u.1 j)
    have hall := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp h0
    ext j
    exact mul_self_eq_zero.mp (hall j (Finset.mem_univ j))
  have hψ_surj : Function.Surjective ψ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank Subspace.dual_finrank_eq.symm).mp hψ_inj
  let f : Module.Dual ℚ WQ :=
    { toFun := fun z => ∑ j : Fin n, (q j - V i0 j) * z.1 j
      map_add' := fun z1 z2 => by
        simp only [Submodule.coe_add, Pi.add_apply, mul_add, Finset.sum_add_distrib]
      map_smul' := fun c z => by
        simp only [SetLike.val_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => by ring }
  obtain ⟨u, hu⟩ := hψ_surj f
  let r : Fin n → ℚ := V i0 + u.1
  have hr_mem_WR : embed r - v i0 ∈ WR := by
    have hrew : embed r - v i0 = embed u.1 := by
      rw [← embed_sub]
      congr 1
      ext j
      simp [r]
    rw [hrew]
    exact hembed_WQ u.1 u.2
  have h_orth_r_WR : ∀ y ∈ WR, inner ℝ (embed q - embed r) y = 0 := by
    intro y hy
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
    · rintro _ ⟨i, hi, rfl⟩
      change inner ℝ (embed q - embed r) (embed (V i) - embed (V i0)) = 0
      rw [← embed_sub, ← embed_sub, inner_embed]
      let z : WQ := ⟨V i - V i0, Submodule.subset_span ⟨i, hi, rfl⟩⟩
      have hz := LinearMap.congr_fun hu z
      have hdot : ∑ j : Fin n, (q - r) j * (V i - V i0) j = 0 := by
        have hz' : ∑ j : Fin n, u.1 j * (V i j - V i0 j) =
            ∑ j : Fin n, (q j - V i0 j) * (V i j - V i0 j) := by
          simpa [ψ, f, z] using hz
        have hdiff : ∑ j : Fin n, (q - r) j * (V i - V i0) j =
            (∑ j : Fin n, (q j - V i0 j) * (V i j - V i0 j)) -
            (∑ j : Fin n, u.1 j * (V i j - V i0 j)) := by
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun j _ => ?_
          simp only [Pi.sub_apply, Pi.add_apply, r]
          ring
        rw [hdiff, hz', sub_self]
      rw [hdot]
      norm_num
    · exact inner_zero_right _
    · intro x z _ _ hx hz
      rw [inner_add_right, hx, hz, add_zero]
    · intro c x _ hx
      rw [inner_smul_right, hx, mul_zero]
  have hp_eq : p = embed r := by
    have hd_mem : p - embed r ∈ WR := by
      have hrew : p - embed r = (p - v i0) - (embed r - v i0) := by abel
      rw [hrew]
      exact WR.sub_mem hp_mem_WR hr_mem_WR
    have hd_inner : inner ℝ (p - embed r) (p - embed r) = 0 := by
      have hrew : p - embed r = (embed q - embed r) - (embed q - p) := by abel
      calc inner ℝ (p - embed r) (p - embed r)
          = inner ℝ ((embed q - embed r) - (embed q - p)) (p - embed r) := by rw [← hrew]
        _ = inner ℝ (embed q - embed r) (p - embed r) - inner ℝ (embed q - p) (p - embed r) :=
            inner_sub_left _ _ _
        _ = 0 := by rw [h_orth_r_WR _ hd_mem, h_orth_WR _ hd_mem, sub_self]
    exact sub_eq_zero.mp (inner_self_eq_zero.mp hd_inner)
  refine ⟨r, ?_, ?_, ?_⟩
  · rw [← hp_eq]
    exact hpK
  · rw [← embed_sub, norm_sq_embed]
    congr 1
  · rw [← hp_eq]
    exact hpyth
