import OMAReductions.R_mo_273976_R1

-- Step mo-273976.R1.H3: hypothesis H3 of reduction mo-273976.R1
-- Credit: @lettucrisp

namespace OMA.P_mo_273976_R1_H3

private def IsNilpotentNumber (n : ℕ) : Prop :=
  ∀ q r k : ℕ, q.Prime → r.Prime → q ≠ r → q ∣ n →
    0 < k → r ^ k ∣ n → ¬ q ∣ r ^ k - 1

private lemma isNilpotentNumber_of_dvd {m n : ℕ} (hmn : m ∣ n) (hn : IsNilpotentNumber n) :
    IsNilpotentNumber m :=
  fun q r k hq hr hne hqm hk hrk => hn q r k hq hr hne (hqm.trans hmn) hk (hrk.trans hmn)

private lemma card_lt_card_of_lt {G : Type*} [Group G] [Finite G] {H K : Subgroup G}
    (hHK : H < K) : Nat.card H < Nat.card K := by
  classical
  have _ := Fintype.ofFinite G
  have _ := Fintype.ofFinite H
  have _ := Fintype.ofFinite K
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  have h1 : (Set.toFinset (H : Set G)).card = Fintype.card H := Set.toFinset_card _
  have h2 : (Set.toFinset (K : Set G)).card = Fintype.card K := Set.toFinset_card _
  rw [← h1, ← h2]
  refine Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩)
  · intro x hx
    exact Set.mem_toFinset.mpr (hHK.le (Set.mem_toFinset.mp hx))
  · intro heq
    apply hHK.ne
    ext x
    have := Finset.ext_iff.mp heq x
    simpa using this

private lemma card_lt_of_lt_top {G : Type*} [Group G] [Finite G] {H : Subgroup G}
    (hH : H < ⊤) : Nat.card H < Nat.card G := by
  have h := card_lt_card_of_lt hH
  rwa [Nat.card_congr Subgroup.topEquiv.toEquiv] at h

private lemma card_le_of_le {G : Type*} [Group G] [Finite G] {H K : Subgroup G}
    (hHK : H ≤ K) : Nat.card H ≤ Nat.card K := by
  rcases eq_or_lt_of_le hHK with rfl | hlt
  · exact le_rfl
  · exact (card_lt_card_of_lt hlt).le

private lemma card_le_top {G : Type*} [Group G] [Finite G] (H : Subgroup G) :
    Nat.card H ≤ Nat.card G := by
  have h := card_le_of_le (le_top : H ≤ ⊤)
  rwa [Nat.card_congr Subgroup.topEquiv.toEquiv] at h

private def IsMaxSub {G : Type*} [Group G] (M : Subgroup G) : Prop :=
  M < ⊤ ∧ ∀ L : Subgroup G, M < L → L = ⊤

private lemma exists_maxSub_ge {G : Type*} [Group G] [Finite G] :
    ∀ n : ℕ, ∀ K : Subgroup G, K < ⊤ → Nat.card G - Nat.card K ≤ n →
      ∃ M : Subgroup G, K ≤ M ∧ IsMaxSub M := by
  intro n
  induction n with
  | zero =>
    intro K hK hle
    have hlt := card_lt_of_lt_top hK
    omega
  | succ n ih =>
    intro K hK hle
    by_cases hmax : ∀ L : Subgroup G, K < L → L = ⊤
    · exact ⟨K, le_rfl, hK, hmax⟩
    · push Not at hmax
      obtain ⟨L, hKL, hLne⟩ := hmax
      have hLlt : L < ⊤ := lt_top_iff_ne_top.mpr hLne
      have hcard_lt : Nat.card K < Nat.card L := card_lt_card_of_lt hKL
      have hcard_L : Nat.card L < Nat.card G := card_lt_of_lt_top hLlt
      obtain ⟨M, hLM, hM⟩ := ih L hLlt (by omega)
      exact ⟨M, hKL.le.trans hLM, hM⟩

private lemma isMaxSub_map_conj {G : Type*} [Group G] {M : Subgroup G} (hM : IsMaxSub M) (g : G) :
    IsMaxSub (M.map (MulAut.conj g).toMonoidHom) := by
  let e := MulAut.conj g
  constructor
  · rw [lt_top_iff_ne_top]
    intro htop
    apply hM.1.ne
    ext x
    simp only [Subgroup.mem_top, iff_true]
    have hx : e x ∈ M.map e.toMonoidHom := by rw [htop]; trivial
    rcases Subgroup.mem_map.mp hx with ⟨y, hyM, hyx⟩
    have : y = x := e.injective hyx
    rwa [← this]
  · intro L hL
    have hpre : M < L.comap e.toMonoidHom := by
      refine lt_of_le_of_ne ?_ ?_
      · intro x hx
        exact hL.le (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
      · intro heq
        apply hL.ne
        ext y
        constructor
        · intro hy; exact hL.le hy
        · intro hy
          have h1 : e.symm y ∈ L.comap e.toMonoidHom := by
            change e (e.symm y) ∈ L
            simpa using hy
          rw [← heq] at h1
          exact Subgroup.mem_map.mpr ⟨e.symm y, h1, by change g * (g⁻¹ * y * g) * g⁻¹ = y; group⟩
    have htop := hM.2 (L.comap e.toMonoidHom) hpre
    ext y
    simp only [Subgroup.mem_top, iff_true]
    have h1 : e (e.symm y) ∈ L := by
      have : e.symm y ∈ L.comap e.toMonoidHom := by rw [htop]; trivial
      exact this
    simpa using h1

private lemma map_conj_eq_iff {G : Type*} [Group G] (M : Subgroup G) (g₁ g₂ : G) :
    M.map (MulAut.conj g₁).toMonoidHom = M.map (MulAut.conj g₂).toMonoidHom ↔
      g₁⁻¹ * g₂ ∈ Subgroup.normalizer (M : Set G) := by
  constructor
  · intro heq
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have hiff : ∀ x, x ∈ M.map (MulAut.conj g₁).toMonoidHom ↔
        x ∈ M.map (MulAut.conj g₂).toMonoidHom := fun x => by rw [heq]
    have h1 : g₂ * h * g₂⁻¹ ∈ M.map (MulAut.conj g₁).toMonoidHom ↔
        g₂ * h * g₂⁻¹ ∈ M.map (MulAut.conj g₂).toMonoidHom := hiff _
    have hrhs : g₂ * h * g₂⁻¹ ∈ M.map (MulAut.conj g₂).toMonoidHom ↔ h ∈ M := by
      constructor
      · rintro ⟨m, hm, hmeq⟩
        have : m = h := (MulAut.conj g₂).injective hmeq
        rwa [← this]
      · intro hm
        exact ⟨h, hm, rfl⟩
    have hlhs : g₂ * h * g₂⁻¹ ∈ M.map (MulAut.conj g₁).toMonoidHom ↔
        g₁⁻¹ * g₂ * h * (g₁⁻¹ * g₂)⁻¹ ∈ M := by
      constructor
      · rintro ⟨m, hm, hmeq⟩
        have hmeq' : g₁ * m * g₁⁻¹ = g₂ * h * g₂⁻¹ := hmeq
        have : g₁⁻¹ * g₂ * h * (g₁⁻¹ * g₂)⁻¹ = m := by
          calc
            g₁⁻¹ * g₂ * h * (g₁⁻¹ * g₂)⁻¹ = g₁⁻¹ * (g₂ * h * g₂⁻¹) * g₁ := by group
            _ = g₁⁻¹ * (g₁ * m * g₁⁻¹) * g₁ := by rw [← hmeq']
            _ = m := by group
        rwa [this]
      · intro hm
        refine ⟨g₁⁻¹ * g₂ * h * (g₁⁻¹ * g₂)⁻¹, hm, ?_⟩
        change g₁ * (g₁⁻¹ * g₂ * h * (g₁⁻¹ * g₂)⁻¹) * g₁⁻¹ = g₂ * h * g₂⁻¹
        group
    rw [hlhs, hrhs] at h1
    exact h1.symm
  · intro hmem
    ext x
    simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · rintro ⟨m, hm, rfl⟩
      refine ⟨(g₁⁻¹ * g₂)⁻¹ * m * (g₁⁻¹ * g₂), ?_, ?_⟩
      · have hinv : (g₁⁻¹ * g₂)⁻¹ ∈ Subgroup.normalizer (M : Set G) :=
          (Subgroup.normalizer (M : Set G)).inv_mem hmem
        simpa using ((Subgroup.mem_normalizer_iff.mp hinv) m).mp hm
      · group
    · rintro ⟨m, hm, rfl⟩
      refine ⟨(g₁⁻¹ * g₂) * m * (g₁⁻¹ * g₂)⁻¹, ?_, ?_⟩
      · exact ((Subgroup.mem_normalizer_iff.mp hmem) m).mp hm
      · group

private lemma comm_of_zpowers_eq_top {G : Type*} [Group G] {x : G}
    (hx : Subgroup.zpowers x = ⊤) : Group.IsNilpotent G := by
  let _ : CommGroup G := {
    (inferInstance : Group G) with
    mul_comm := by
      intro a b
      have ha : a ∈ Subgroup.zpowers x := by rw [hx]; trivial
      have hb : b ∈ Subgroup.zpowers x := by rw [hx]; trivial
      rcases ha with ⟨i, rfl⟩
      rcases hb with ⟨j, rfl⟩
      rw [← zpow_add, ← zpow_add, add_comm]
  }
  infer_instance

private lemma exists_proper_nontrivial_normal {G : Type*} [Group G] [Finite G]
    (hnot : ¬ Group.IsNilpotent G)
    (hsub : ∀ H : Subgroup G, H < ⊤ → Group.IsNilpotent H) :
    ∃ N : Subgroup G, N.Normal ∧ N ≠ ⊥ ∧ N ≠ ⊤ := by
  classical
  have _ : Fintype G := Fintype.ofFinite G
  have hG_nontriv : Nontrivial G := by
    by_contra hsubg
    rw [not_nontrivial_iff_subsingleton] at hsubg
    have _ : CommGroup G := { (inferInstance : Group G) with mul_comm := fun _ _ => Subsingleton.elim _ _ }
    exact hnot inferInstance
  have hnot_cyc : ∀ x : G, Subgroup.zpowers x < ⊤ := by
    intro x
    rw [lt_top_iff_ne_top]
    intro htop
    exact hnot (comm_of_zpowers_eq_top htop)
  -- Case 1: there exist two distinct maximal subgroups with nontrivial intersection
  by_cases hcase1 : ∃ M₁ M₂ : Subgroup G, IsMaxSub M₁ ∧ IsMaxSub M₂ ∧ M₁ ≠ M₂ ∧ M₁ ⊓ M₂ ≠ ⊥
  · let P : ℕ → Prop := fun d =>
      ∃ M₁ M₂ : Subgroup G, IsMaxSub M₁ ∧ IsMaxSub M₂ ∧ M₁ ≠ M₂ ∧ M₁ ⊓ M₂ ≠ ⊥ ∧
        Nat.card (M₁ ⊓ M₂ : Subgroup G) = d
    obtain ⟨M₀₁, M₀₂, hM₀₁, hM₀₂, hne₀, hbot₀⟩ := hcase1
    let d := Nat.findGreatest P (Nat.card G)
    have hPd : P d := Nat.findGreatest_spec (card_le_top (M₀₁ ⊓ M₀₂))
      ⟨M₀₁, M₀₂, hM₀₁, hM₀₂, hne₀, hbot₀, rfl⟩
    obtain ⟨M₁, M₂, hM₁, hM₂, hne, hDne, hDcard⟩ := hPd
    set D : Subgroup G := M₁ ⊓ M₂
    have hD_lt_M₁ : D < M₁ := by
      refine lt_of_le_of_ne inf_le_left ?_
      intro heq
      have hle : M₁ ≤ M₂ := heq ▸ inf_le_right
      rcases eq_or_lt_of_le hle with rfl | hlt
      · exact hne rfl
      · exact hM₂.1.ne (hM₁.2 M₂ hlt)
    have hD_lt_M₂ : D < M₂ := by
      refine lt_of_le_of_ne inf_le_right ?_
      intro heq
      have hle : M₂ ≤ M₁ := heq ▸ inf_le_left
      rcases eq_or_lt_of_le hle with rfl | hlt
      · exact hne rfl
      · exact hM₁.1.ne (hM₂.2 M₁ hlt)
    have hgrow : ∀ M : Subgroup G, M < ⊤ → D < M → D < Subgroup.normalizer (D : Set G) ⊓ M := by
      intro M hMlt hDM
      have _ : Group.IsNilpotent M := hsub M hMlt
      have hnc : NormalizerCondition M := Group.normalizerCondition_of_isNilpotent
      let D' : Subgroup M := D.subgroupOf M
      have hD'lt : D' < ⊤ := by
        rw [lt_top_iff_ne_top]
        intro htop
        apply hDM.ne
        refine le_antisymm hDM.le ?_
        intro x hxM
        have : (⟨x, hxM⟩ : M) ∈ D' := by rw [htop]; trivial
        exact this
      have hlt_norm : D' < Subgroup.normalizer (D' : Set M) := hnc D' hD'lt
      obtain ⟨x, hx_norm, hx_not⟩ := SetLike.exists_of_lt hlt_norm
      have hxD : x.1 ∉ D := hx_not
      have hxNorm : x.1 ∈ Subgroup.normalizer (D : Set G) := by
        rw [Subgroup.mem_normalizer_iff]
        intro g
        constructor
        · intro hgD
          have hgM : g ∈ M := hDM.le hgD
          exact (Subgroup.mem_normalizer_iff.mp hx_norm ⟨g, hgM⟩).mp hgD
        · intro hconj
          have hgM : g ∈ M := by
            have h1 : x.1 * g * x.1⁻¹ ∈ M := hDM.le hconj
            have h2 : x.1⁻¹ * (x.1 * g * x.1⁻¹) * x.1 ∈ M :=
              M.mul_mem (M.mul_mem (M.inv_mem x.2) h1) x.2
            simpa [mul_assoc] using h2
          exact (Subgroup.mem_normalizer_iff.mp hx_norm ⟨g, hgM⟩).mpr hconj
      refine lt_of_le_of_ne (le_inf Subgroup.le_normalizer hDM.le) ?_
      intro heq
      have hx_in : x.1 ∈ Subgroup.normalizer (D : Set G) ⊓ M := ⟨hxNorm, x.2⟩
      rw [← heq] at hx_in
      exact hxD hx_in
    have hgrow₁ : D < Subgroup.normalizer (D : Set G) ⊓ M₁ := hgrow M₁ hM₁.1 hD_lt_M₁
    have hgrow₂ : D < Subgroup.normalizer (D : Set G) ⊓ M₂ := hgrow M₂ hM₂.1 hD_lt_M₂
    by_cases hnorm_top : Subgroup.normalizer (D : Set G) = ⊤
    · refine ⟨D, Subgroup.normalizer_eq_top_iff.mp hnorm_top, hDne, (hD_lt_M₁.trans hM₁.1).ne⟩
    · have hnorm_lt : Subgroup.normalizer (D : Set G) < ⊤ := lt_top_iff_ne_top.mpr hnorm_top
      obtain ⟨M₃, hNle, hM₃⟩ :=
        exists_maxSub_ge (Nat.card G) (Subgroup.normalizer (D : Set G)) hnorm_lt (Nat.sub_le _ _)
      exfalso
      by_cases h31 : M₃ ≠ M₁
      · have hlt : D < M₁ ⊓ M₃ := lt_of_lt_of_le hgrow₁ (le_inf inf_le_right (inf_le_left.trans hNle))
        have hbot' : M₁ ⊓ M₃ ≠ ⊥ := fun h0 => hDne (le_bot_iff.mp (h0 ▸ hlt.le))
        have hcard_gt : d < Nat.card (M₁ ⊓ M₃ : Subgroup G) := by
          rw [← hDcard]; exact card_lt_card_of_lt hlt
        have hle_d : Nat.card (M₁ ⊓ M₃ : Subgroup G) ≤ d :=
          Nat.le_findGreatest (card_le_top _) ⟨M₁, M₃, hM₁, hM₃, h31.symm, hbot', rfl⟩
        omega
      · push Not at h31
        have h32 : M₃ ≠ M₂ := h31 ▸ hne
        have hlt : D < M₂ ⊓ M₃ := lt_of_lt_of_le hgrow₂ (le_inf inf_le_right (inf_le_left.trans hNle))
        have hbot' : M₂ ⊓ M₃ ≠ ⊥ := fun h0 => hDne (le_bot_iff.mp (h0 ▸ hlt.le))
        have hcard_gt : d < Nat.card (M₂ ⊓ M₃ : Subgroup G) := by
          rw [← hDcard]; exact card_lt_card_of_lt hlt
        have hle_d : Nat.card (M₂ ⊓ M₃ : Subgroup G) ≤ d :=
          Nat.le_findGreatest (card_le_top _) ⟨M₂, M₃, hM₂, hM₃, h32.symm, hbot', rfl⟩
        omega
  -- Case 2: distinct maximal subgroups have trivial intersection
  · push Not at hcase1
    by_cases hnorm_ex : ∃ M : Subgroup G, IsMaxSub M ∧ M.Normal
    · obtain ⟨M, hM, hMn⟩ := hnorm_ex
      by_cases hMbot : M = ⊥
      · exfalso
        obtain ⟨x, hx1⟩ := exists_ne (1 : G)
        have hlt : M < Subgroup.zpowers x := by
          rw [hMbot, bot_lt_iff_ne_bot]
          intro h0
          have hx : x ∈ (⊥ : Subgroup G) := h0 ▸ Subgroup.mem_zpowers x
          exact hx1 (Subgroup.mem_bot.mp hx)
        exact (hnot_cyc x).ne (hM.2 _ hlt)
      · exact ⟨M, hMn, hMbot, hM.1.ne⟩
    · push Not at hnorm_ex
      have hself_norm : ∀ M : Subgroup G, IsMaxSub M → Subgroup.normalizer (M : Set G) = M := by
        intro M hM
        refine le_antisymm ?_ Subgroup.le_normalizer
        by_contra hnotle
        have hlt : M < Subgroup.normalizer (M : Set G) :=
          lt_of_le_of_ne Subgroup.le_normalizer (fun h => hnotle h.ge)
        exact hnorm_ex M hM (Subgroup.normalizer_eq_top_iff.mp (hM.2 _ hlt))
      have hne_bot : ∀ M : Subgroup G, IsMaxSub M → M ≠ ⊥ := by
        intro M hM hbot
        apply hnorm_ex M hM
        rw [hbot]
        infer_instance
      have hcard_ge2 : ∀ M : Subgroup G, IsMaxSub M → 2 ≤ Nat.card M := by
        intro M hM
        have hbot := hne_bot M hM
        have _ : Nontrivial M := (Subgroup.nontrivial_iff_ne_bot M).mpr hbot
        exact Finite.one_lt_card
      let Φ : ∀ (M : Subgroup G), (G ⧸ M) × {x : M // x.1 ≠ 1} → {y : G // y ≠ 1} :=
        fun M p =>
          ⟨p.1.out * p.2.1.1 * p.1.out⁻¹, by
            intro h1
            apply p.2.2
            have : p.1.out⁻¹ * (p.1.out * p.2.1.1 * p.1.out⁻¹) * p.1.out = p.1.out⁻¹ * 1 * p.1.out := by
              rw [h1]
            simpa [mul_assoc] using this⟩
      have hΦ_inj : ∀ M : Subgroup G, IsMaxSub M → Function.Injective (Φ M) := by
        intro M hM ⟨q₁, x₁⟩ ⟨q₂, x₂⟩ heq
        have hval : q₁.out * x₁.1.1 * q₁.out⁻¹ = q₂.out * x₂.1.1 * q₂.out⁻¹ :=
          congrArg Subtype.val heq
        let M₁ := M.map (MulAut.conj q₁.out).toMonoidHom
        let M₂ := M.map (MulAut.conj q₂.out).toMonoidHom
        have hmem₁ : q₁.out * x₁.1.1 * q₁.out⁻¹ ∈ M₁ := ⟨x₁.1.1, x₁.1.2, rfl⟩
        have hmem₂ : q₁.out * x₁.1.1 * q₁.out⁻¹ ∈ M₂ := by rw [hval]; exact ⟨x₂.1.1, x₂.1.2, rfl⟩
        have hne1 : q₁.out * x₁.1.1 * q₁.out⁻¹ ≠ 1 := (Φ M (q₁, x₁)).2
        have hMeq : M₁ = M₂ := by
          by_contra hMne
          have hbot := hcase1 M₁ M₂ (isMaxSub_map_conj hM _) (isMaxSub_map_conj hM _) hMne
          have hmem : q₁.out * x₁.1.1 * q₁.out⁻¹ ∈ (⊥ : Subgroup G) := hbot ▸ ⟨hmem₁, hmem₂⟩
          exact hne1 (Subgroup.mem_bot.mp hmem)
        have hinv_norm : q₁.out⁻¹ * q₂.out ∈ Subgroup.normalizer (M : Set G) :=
          (map_conj_eq_iff M q₁.out q₂.out).mp hMeq
        have hinv : q₁.out⁻¹ * q₂.out ∈ M := by
          rwa [hself_norm M hM] at hinv_norm
        have hq : q₁ = q₂ := by
          rw [← Quotient.out_eq q₁, ← Quotient.out_eq q₂]
          exact (QuotientGroup.eq).mpr hinv
        subst hq
        have hx : x₁ = x₂ := by
          apply Subtype.ext
          apply Subtype.ext
          exact (MulAut.conj q₁.out).injective hval
        exact Prod.ext rfl hx
      have hdom_card : ∀ M : Subgroup G,
          Nat.card ((G ⧸ M) × {x : M // x.1 ≠ 1}) = Nat.card G - M.index := by
        intro M
        rw [Nat.card_prod]
        have hq : Nat.card (G ⧸ M) = M.index := rfl
        have hs : Nat.card {x : M // x.1 ≠ 1} = Nat.card M - 1 := by
          have _ := Fintype.ofFinite M
          rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
          have hbij : Fintype.card {x : M // x.1 ≠ 1} = Fintype.card {x : M // x ≠ (1 : M)} :=
            Fintype.card_congr (Equiv.subtypeEquivRight fun x =>
              not_congr ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩)
          rw [hbij, Fintype.card_subtype_compl, Fintype.card_subtype_eq]
        rw [hq, hs, Nat.mul_sub_left_distrib, mul_one]
        have hlag := M.card_mul_index
        rw [mul_comm] at hlag
        rw [hlag]
      have hbot_lt : (⊥ : Subgroup G) < ⊤ := bot_lt_top
      obtain ⟨M₁, _, hM₁⟩ := exists_maxSub_ge (Nat.card G) ⊥ hbot_lt (Nat.sub_le _ _)
      have hind₁_ge2 : 2 ≤ M₁.index := by
        have hne1 : M₁.index ≠ 1 := fun h => hM₁.1.ne (Subgroup.index_eq_one.mp h)
        have hpos : 0 < M₁.index := Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)
        omega
      have hne1_card : Nat.card {y : G // y ≠ 1} = Nat.card G - 1 := by
        rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
          Fintype.card_subtype_compl, Fintype.card_subtype_eq]
      have hnot_surj : ¬ Function.Surjective (Φ M₁) := by
        intro hsurj
        have hbij := Equiv.ofBijective (Φ M₁) ⟨hΦ_inj M₁ hM₁, hsurj⟩
        have hcard_eq := Nat.card_congr hbij
        rw [hdom_card M₁, hne1_card] at hcard_eq
        have hpos : 0 < Nat.card M₁ := Nat.card_pos
        have hlag : Nat.card M₁ * M₁.index = Nat.card G := M₁.card_mul_index
        have hle : M₁.index ≤ Nat.card G := by
          rw [← hlag]; exact Nat.le_mul_of_pos_left _ hpos
        omega
      have hex_y : ∃ y : {y : G // y ≠ 1}, y ∉ Set.range (Φ M₁) := by
        by_contra hall
        push Not at hall
        exact hnot_surj hall
      obtain ⟨y, hy_not⟩ := hex_y
      obtain ⟨M₂, hyM₂, hM₂⟩ := exists_maxSub_ge (Nat.card G) (Subgroup.zpowers y.1)
        (hnot_cyc y.1) (Nat.sub_le _ _)
      have hdisj : Disjoint (Set.range (Φ M₁)) (Set.range (Φ M₂)) := by
        rw [Set.disjoint_iff]
        rintro z ⟨⟨⟨q₁, x₁⟩, hz₁⟩, ⟨⟨q₂, x₂⟩, hz₂⟩⟩
        have hval₁ : q₁.out * x₁.1.1 * q₁.out⁻¹ = z.1 := congrArg Subtype.val hz₁
        have hval₂ : q₂.out * x₂.1.1 * q₂.out⁻¹ = z.1 := congrArg Subtype.val hz₂
        let C₁ := M₁.map (MulAut.conj q₁.out).toMonoidHom
        let C₂ := M₂.map (MulAut.conj q₂.out).toMonoidHom
        have hCeq : C₁ = C₂ := by
          by_contra hneC
          have hbot := hcase1 C₁ C₂ (isMaxSub_map_conj hM₁ _) (isMaxSub_map_conj hM₂ _) hneC
          have h1 : z.1 ∈ C₁ := by rw [← hval₁]; exact ⟨x₁.1.1, x₁.1.2, rfl⟩
          have h2 : z.1 ∈ C₂ := by rw [← hval₂]; exact ⟨x₂.1.1, x₂.1.2, rfl⟩
          exact z.2 (Subgroup.mem_bot.mp (hbot ▸ ⟨h1, h2⟩))
        have hy_in_M₂ : y.1 ∈ M₂ := hyM₂ (Subgroup.mem_zpowers y.1)
        have hconj_y : q₂.out * y.1 * q₂.out⁻¹ ∈ C₁ := by
          rw [hCeq]; exact ⟨y.1, hy_in_M₂, rfl⟩
        rcases hconj_y with ⟨m, hmM₁, hm_eq⟩
        have hm_eq' : q₁.out * m * q₁.out⁻¹ = q₂.out * y.1 * q₂.out⁻¹ := hm_eq
        let g : G := q₂.out⁻¹ * q₁.out
        have hyg : y.1 = g * m * g⁻¹ := by
          calc
            y.1 = q₂.out⁻¹ * (q₂.out * y.1 * q₂.out⁻¹) * q₂.out := by group
            _ = q₂.out⁻¹ * (q₁.out * m * q₁.out⁻¹) * q₂.out := by rw [← hm_eq']
            _ = g * m * g⁻¹ := by simp only [g]; group
        let q : G ⧸ M₁ := QuotientGroup.mk g
        have hdiff : q.out⁻¹ * g ∈ M₁ := (QuotientGroup.eq).mp (Quotient.out_eq q)
        let m' : M₁ := ⟨(q.out⁻¹ * g) * m * (q.out⁻¹ * g)⁻¹,
          M₁.mul_mem (M₁.mul_mem hdiff hmM₁) (M₁.inv_mem hdiff)⟩
        have hy_eq : q.out * m'.1 * q.out⁻¹ = y.1 := by
          rw [hyg]; simp only [m']; group
        have hm'_ne : m'.1 ≠ 1 := by
          intro h1
          apply y.2
          rw [← hy_eq, h1]
          group
        exact hy_not ⟨(q, ⟨m', hm'_ne⟩), Subtype.ext hy_eq⟩
      let A₁ := Finset.univ.image (Φ M₁)
      let A₂ := Finset.univ.image (Φ M₂)
      have hA₁ : A₁.card = Nat.card G - M₁.index := by
        rw [Finset.card_image_of_injective _ (hΦ_inj M₁ hM₁), Finset.card_univ,
          ← Nat.card_eq_fintype_card, hdom_card M₁]
      have hA₂ : A₂.card = Nat.card G - M₂.index := by
        rw [Finset.card_image_of_injective _ (hΦ_inj M₂ hM₂), Finset.card_univ,
          ← Nat.card_eq_fintype_card, hdom_card M₂]
      have hdisj_fin : Disjoint A₁ A₂ := by
        rw [Finset.disjoint_left]
        intro a ha₁ ha₂
        rcases Finset.mem_image.mp ha₁ with ⟨x₁, _, rfl⟩
        rcases Finset.mem_image.mp ha₂ with ⟨x₂, _, hx₂⟩
        exact Set.disjoint_left.mp hdisj ⟨x₁, rfl⟩ ⟨x₂, hx₂⟩
      have hcard_le : A₁.card + A₂.card ≤ Nat.card G - 1 := by
        rw [← Finset.card_union_of_disjoint hdisj_fin, ← hne1_card, Nat.card_eq_fintype_card]
        exact Finset.card_le_univ _
      rw [hA₁, hA₂] at hcard_le
      have hm₁ : 2 ≤ Nat.card M₁ := hcard_ge2 M₁ hM₁
      have hm₂ : 2 ≤ Nat.card M₂ := hcard_ge2 M₂ hM₂
      have hlag₁ : Nat.card M₁ * M₁.index = Nat.card G := M₁.card_mul_index
      have hlag₂ : Nat.card M₂ * M₂.index = Nat.card G := M₂.card_mul_index
      have h2i₁ : 2 * M₁.index ≤ Nat.card G := by
        calc 2 * M₁.index ≤ Nat.card M₁ * M₁.index := Nat.mul_le_mul_right _ hm₁
          _ = Nat.card G := hlag₁
      have h2i₂ : 2 * M₂.index ≤ Nat.card G := by
        calc 2 * M₂.index ≤ Nat.card M₂ * M₂.index := Nat.mul_le_mul_right _ hm₂
          _ = Nat.card G := hlag₂
      omega

private lemma isPGroup_of_all_prime_dvd_eq {G : Type*} [Group G] [Finite G] (r : ℕ)
    [Fact r.Prime] (hall : ∀ q : ℕ, q.Prime → q ∣ Nat.card G → q = r) :
    IsPGroup r G := by
  rw [IsPGroup.iff_card]
  have hpos : 0 < Nat.card G := Nat.card_pos
  have aux : ∀ n : ℕ, 0 < n → (∀ q : ℕ, q.Prime → q ∣ n → q = r) → ∃ k : ℕ, n = r ^ k := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn hdiv
      by_cases h1 : n = 1
      · exact ⟨0, by simp [h1]⟩
      · obtain ⟨q, hq, hqn⟩ := Nat.exists_prime_and_dvd h1
        have hqr : q = r := hdiv q hq hqn
        subst hqr
        obtain ⟨m, rfl⟩ := hqn
        have hmpos : 0 < m := by
          rcases Nat.eq_zero_or_pos m with rfl | h
          · simp at hn
          · exact h
        have hmlt : m < q * m := lt_mul_of_one_lt_left hmpos hq.one_lt
        obtain ⟨k, rfl⟩ := ih m hmlt hmpos (fun p hp hpm => hdiv p hp (dvd_mul_of_dvd_right hpm q))
        exact ⟨k + 1, by ring⟩
  exact aux (Nat.card G) hpos hall

private lemma main_ind : ∀ n : ℕ, ∀ (G : Type) [Group G] [Finite G],
    Nat.card G ≤ n → IsNilpotentNumber (Nat.card G) → Group.IsNilpotent G := by
  intro n
  induction n with
  | zero =>
    intro G _ _ hcard _
    have hpos : 0 < Nat.card G := Nat.card_pos
    omega
  | succ n ih =>
    intro G _ _ hcard hnn
    by_contra hnot
    have hsub : ∀ H : Subgroup G, H < ⊤ → Group.IsNilpotent H := by
      intro H hH
      have hlt : Nat.card H < Nat.card G := card_lt_of_lt_top hH
      have hdvd : Nat.card H ∣ Nat.card G := Subgroup.card_subgroup_dvd_card H
      exact ih H (by omega) (isNilpotentNumber_of_dvd hdvd hnn)
    have hquot : ∀ N : Subgroup G, [N.Normal] → N ≠ ⊥ → Group.IsNilpotent (G ⧸ N) := by
      intro N _ hNne
      have hNgt : 1 < Nat.card N := by
        have _ : Nontrivial N := (Subgroup.nontrivial_iff_ne_bot N).mpr hNne
        exact Finite.one_lt_card
      have hlag : Nat.card (G ⧸ N) * Nat.card N = Nat.card G := by
        rw [mul_comm]
        exact N.card_mul_index
      have hposQ : 0 < Nat.card (G ⧸ N) := Nat.card_pos
      have hlt : Nat.card (G ⧸ N) < Nat.card G := by
        calc Nat.card (G ⧸ N) = Nat.card (G ⧸ N) * 1 := (mul_one _).symm
          _ < Nat.card (G ⧸ N) * Nat.card N := Nat.mul_lt_mul_of_pos_left hNgt hposQ
          _ = Nat.card G := hlag
      have hdvd : Nat.card (G ⧸ N) ∣ Nat.card G := ⟨Nat.card N, hlag.symm⟩
      exact ih (G ⧸ N) (by omega) (isNilpotentNumber_of_dvd hdvd hnn)
    obtain ⟨N₀, hN₀n, hN₀b, hN₀t⟩ := exists_proper_nontrivial_normal hnot hsub
    classical
    let Q : ℕ → Prop := fun d =>
      ∃ N : Subgroup G, N.Normal ∧ N ≠ ⊥ ∧ N ≠ ⊤ ∧ Nat.card N = d
    have hQex : ∃ d, Q d := ⟨Nat.card N₀, N₀, hN₀n, hN₀b, hN₀t, rfl⟩
    let d := Nat.find hQex
    obtain ⟨N, hNn, hNb, hNt, hNd⟩ := Nat.find_spec hQex
    have _ : N.Normal := hNn
    have hNmin : ∀ K : Subgroup G, K.Normal → K ≠ ⊥ → K ≤ N → K = N := by
      intro K hKn hKb hKN
      by_contra hKne
      have hKlt : K < N := lt_of_le_of_ne hKN hKne
      have hKcard : Nat.card K < Nat.find hQex := by rw [← hNd]; exact card_lt_card_of_lt hKlt
      have hKt : K ≠ ⊤ := (lt_of_lt_of_le hKlt (le_top)).ne
      exact Nat.find_min hQex hKcard ⟨K, hKn, hKb, hKt, rfl⟩
    have _ : Group.IsNilpotent N := hsub N (lt_top_iff_ne_top.mpr hNt)
    have _ : Nontrivial N := (Subgroup.nontrivial_iff_ne_bot N).mpr hNb
    have hZN_ne : Subgroup.center N ≠ ⊥ := Group.IsNilpotent.center_ne_bot N
    let Z : Subgroup G := (Subgroup.center N).map N.subtype
    have hZN_le : Z ≤ N := by
      rintro x ⟨y, _, rfl⟩; exact y.2
    have hZN_bot : Z ≠ ⊥ := by
      intro hbot
      apply hZN_ne
      ext y
      simp only [Subgroup.mem_bot]
      constructor
      · intro hy
        have : y.1 ∈ Z := ⟨y, hy, rfl⟩
        rw [hbot] at this
        exact Subtype.ext (Subgroup.mem_bot.mp this)
      · rintro rfl; exact Subgroup.one_mem _
    have hZN_norm : Z.Normal := by
      constructor
      intro z hz g
      rcases hz with ⟨y, hyZ, rfl⟩
      refine ⟨⟨g * y.1 * g⁻¹, hNn.conj_mem y.1 y.2 g⟩, ?_, rfl⟩
      change y ∈ Subgroup.center N at hyZ
      change (⟨g * y.1 * g⁻¹, hNn.conj_mem y.1 y.2 g⟩ : N) ∈ Subgroup.center N
      rw [Subgroup.mem_center_iff] at hyZ ⊢
      intro w
      apply Subtype.ext
      have hw : g⁻¹ * w.1 * g ∈ N := by
        simpa using hNn.conj_mem w.1 w.2 g⁻¹
      have hcomm := congrArg Subtype.val (hyZ ⟨g⁻¹ * w.1 * g, hw⟩)
      change g⁻¹ * w.1 * g * y.1 = y.1 * (g⁻¹ * w.1 * g) at hcomm
      calc
        w.1 * (g * y.1 * g⁻¹) = g * (g⁻¹ * w.1 * g * y.1) * g⁻¹ := by group
        _ = g * (y.1 * (g⁻¹ * w.1 * g)) * g⁻¹ := by rw [hcomm]
        _ = g * y.1 * g⁻¹ * w.1 := by group
    have hZeq : Z = N := hNmin Z hZN_norm hZN_bot hZN_le
    have hN_comm : ∀ a b : G, a ∈ N → b ∈ N → a * b = b * a := by
      intro a b ha hb
      rw [← hZeq] at ha
      rcases ha with ⟨y, hyZ, rfl⟩
      change y ∈ Subgroup.center N at hyZ
      have := congrArg Subtype.val ((Subgroup.mem_center_iff.mp hyZ) ⟨b, hb⟩)
      exact this.symm
    have hNcard_ne1 : Nat.card N ≠ 1 := (Finite.one_lt_card (α := N)).ne'
    obtain ⟨r, hr, hrN⟩ := Nat.exists_prime_and_dvd hNcard_ne1
    have _ : Fact r.Prime := ⟨hr⟩
    let Nr : Subgroup G := {
      carrier := {x : G | x ∈ N ∧ x ^ r = 1}
      one_mem' := ⟨N.one_mem, one_pow r⟩
      mul_mem' := by
        rintro a b ⟨haN, har⟩ ⟨hbN, hbr⟩
        refine ⟨N.mul_mem haN hbN, ?_⟩
        have hcomm : Commute a b := hN_comm a b haN hbN
        rw [hcomm.mul_pow, har, hbr, one_mul]
      inv_mem' := by
        rintro a ⟨haN, har⟩
        exact ⟨N.inv_mem haN, by rw [inv_pow, har, inv_one]⟩
    }
    have hNr_le : Nr ≤ N := fun _ hx => hx.1
    have hNr_norm : Nr.Normal := by
      constructor
      rintro x ⟨hxN, hxr⟩ g
      refine ⟨hNn.conj_mem x hxN g, ?_⟩
      rw [conj_pow, hxr, mul_one, mul_inv_cancel]
    have hNr_bot : Nr ≠ ⊥ := by
      have _ := Fintype.ofFinite N
      rw [Nat.card_eq_fintype_card] at hrN
      obtain ⟨x, hxord⟩ := exists_prime_orderOf_dvd_card r hrN
      intro hbot
      have hx_in : x.1 ∈ Nr := ⟨x.2, by
        have h1 : x ^ r = 1 := hxord ▸ pow_orderOf_eq_one x
        exact congrArg Subtype.val h1⟩
      rw [hbot] at hx_in
      have hx1 : x = 1 := Subtype.ext (Subgroup.mem_bot.mp hx_in)
      rw [hx1, orderOf_one] at hxord
      exact hr.ne_one hxord.symm
    have hNr_eq : Nr = N := hNmin Nr hNr_norm hNr_bot hNr_le
    have hN_pgroup : IsPGroup r N := by
      rw [isPGroup_iff_pow_pow_eq_one]
      intro x
      refine ⟨1, ?_⟩
      apply Subtype.ext
      have hx : x.1 ∈ Nr := hNr_eq.symm ▸ x.2
      simpa using hx.2
    obtain ⟨k, hk_eq⟩ := (IsPGroup.iff_card).mp hN_pgroup
    have hk_pos : 0 < k := by
      by_contra h0
      have hk0 : k = 0 := by omega
      rw [hk0, pow_zero] at hk_eq
      exact hNcard_ne1 hk_eq
    let C : Subgroup G := Subgroup.centralizer (N : Set G)
    have hCn : C.Normal := by
      constructor
      intro c hc g
      rw [Subgroup.mem_centralizer_iff] at hc ⊢
      intro n hn
      have hgn : g⁻¹ * n * g ∈ N := by simpa using hNn.conj_mem n hn g⁻¹
      have hcomm := hc (g⁻¹ * n * g) hgn
      calc
        n * (g * c * g⁻¹) = g * (g⁻¹ * n * g * c) * g⁻¹ := by group
        _ = g * (c * (g⁻¹ * n * g)) * g⁻¹ := by rw [hcomm]
        _ = g * c * g⁻¹ * n := by group
    have _ : C.Normal := hCn
    by_cases hCtop : C = ⊤
    · have hN_le_Z : N ≤ Subgroup.center G := by
        intro x hxN
        rw [Subgroup.mem_center_iff]
        intro g
        have hgC : g ∈ C := by rw [hCtop]; trivial
        exact (Subgroup.mem_centralizer_iff.mp hgC x hxN).symm
      have _ : Group.IsNilpotent (G ⧸ N) := hquot N hNb
      have hker : (QuotientGroup.mk' N).ker ≤ Subgroup.center G := by
        simpa [QuotientGroup.ker_mk'] using hN_le_Z
      exact hnot (Subgroup.isNilpotent_of_ker_le_center (QuotientGroup.mk' N) hker)
    · let conjOnN : G →* MulAut N := {
        toFun := fun g => {
          toFun := fun x => ⟨g * x.1 * g⁻¹, hNn.conj_mem x.1 x.2 g⟩
          invFun := fun x => ⟨g⁻¹ * x.1 * g, by simpa using hNn.conj_mem x.1 x.2 g⁻¹⟩
          left_inv := fun x => Subtype.ext (by group)
          right_inv := fun x => Subtype.ext (by group)
          map_mul' := fun x y => Subtype.ext (by
            change g * (x.1 * y.1) * g⁻¹ = (g * x.1 * g⁻¹) * (g * y.1 * g⁻¹)
            group)
        }
        map_one' := by ext x; simp
        map_mul' := fun g₁ g₂ => by ext x; change (g₁ * g₂) * x.1 * (g₁ * g₂)⁻¹ = g₁ * (g₂ * x.1 * g₂⁻¹) * g₁⁻¹; group
      }
      have hC_le_ker : C ≤ conjOnN.ker := by
        intro c hc
        rw [MonoidHom.mem_ker]
        ext x
        have hcomm := Subgroup.mem_centralizer_iff.mp hc x.1 x.2
        change c * x.1 * c⁻¹ = x.1
        rw [← hcomm, mul_inv_cancel_right]
      let actHom : (G ⧸ C) →* MulAut N := QuotientGroup.lift C conjOnN hC_le_ker
      let _ : MulAction (G ⧸ C) N := MulAction.compHom N actHom
      by_cases hGC_r : IsPGroup r (G ⧸ C)
      · have hmod := hGC_r.card_modEq_card_fixedPoints N
        have hr_dvd_N : r ∣ Nat.card N := by
          rw [hk_eq]; exact dvd_pow_self r (by omega)
        have hr_dvd_fix : r ∣ Nat.card (MulAction.fixedPoints (G ⧸ C) N) :=
          (Nat.ModEq.dvd_iff hmod dvd_rfl).mp hr_dvd_N
        have h1_fix : (1 : N) ∈ MulAction.fixedPoints (G ⧸ C) N := by
          intro q
          change (actHom q) (1 : N) = 1
          exact map_one _
        have hfix_pos : 0 < Nat.card (MulAction.fixedPoints (G ⧸ C) N) := by
          have _ : Nonempty (MulAction.fixedPoints (G ⧸ C) N) := ⟨⟨1, h1_fix⟩⟩
          exact Nat.card_pos
        have hfix_ge : r ≤ Nat.card (MulAction.fixedPoints (G ⧸ C) N) :=
          Nat.le_of_dvd hfix_pos hr_dvd_fix
        have _ : Nontrivial (MulAction.fixedPoints (G ⧸ C) N) := by
          have _ := Fintype.ofFinite (MulAction.fixedPoints (G ⧸ C) N)
          rw [Nat.card_eq_fintype_card] at hfix_ge
          exact Fintype.one_lt_card_iff_nontrivial.mp (lt_of_lt_of_le hr.one_lt hfix_ge)
        obtain ⟨⟨x, hx_fix⟩, hxne⟩ := exists_ne (⟨1, h1_fix⟩ : MulAction.fixedPoints (G ⧸ C) N)
        have hx1 : x ≠ 1 := fun h => hxne (Subtype.ext h)
        have hx_center : x.1 ∈ Subgroup.center G := by
          rw [Subgroup.mem_center_iff]
          intro g
          have hf := hx_fix (QuotientGroup.mk g)
          have hval : g * x.1 * g⁻¹ = x.1 := congrArg Subtype.val hf
          calc g * x.1 = g * x.1 * g⁻¹ * g := by group
            _ = x.1 * g := by rw [hval]
        let K : Subgroup G := N ⊓ Subgroup.center G
        have hK_norm : K.Normal := Subgroup.normal_inf_normal N (Subgroup.center G)
        have hK_bot : K ≠ ⊥ := by
          intro hbot
          have hxK : x.1 ∈ K := ⟨x.2, hx_center⟩
          rw [hbot] at hxK
          exact hx1 (Subtype.ext (Subgroup.mem_bot.mp hxK))
        have hKeq : K = N := hNmin K hK_norm hK_bot inf_le_left
        have hN_le_Z : N ≤ Subgroup.center G := hKeq ▸ inf_le_right
        apply hCtop
        ext g
        simp only [Subgroup.mem_top, iff_true]
        rw [Subgroup.mem_centralizer_iff]
        intro n hn
        exact ((Subgroup.mem_center_iff.mp (hN_le_Z hn)) g).symm
      · have hex_q : ∃ q : ℕ, q.Prime ∧ q ≠ r ∧ q ∣ Nat.card (G ⧸ C) := by
          by_contra hnone
          push Not at hnone
          apply hGC_r
          refine isPGroup_of_all_prime_dvd_eq r ?_
          intro q hq hqdvd
          by_contra hne
          exact hnone q hq hne hqdvd
        obtain ⟨q, hq, hqr, hqGC⟩ := hex_q
        have _ : Fact q.Prime := ⟨hq⟩
        have _ := Fintype.ofFinite (G ⧸ C)
        have hqGC' : q ∣ Fintype.card (G ⧸ C) := by rwa [← Nat.card_eq_fintype_card]
        obtain ⟨y, hyord⟩ := exists_prime_orderOf_dvd_card q hqGC'
        let Q : Subgroup (G ⧸ C) := Subgroup.zpowers y
        have hQcard : Nat.card Q = q := by
          rw [Nat.card_zpowers, hyord]
        have hQ_pgroup : IsPGroup q Q := IsPGroup.of_card (n := 1) (by simpa using hQcard)
        let _ : MulAction Q N := MulAction.compHom N (actHom.comp Q.subtype)
        let F : Subgroup N := {
          carrier := MulAction.fixedPoints Q N
          one_mem' := fun a => map_one (actHom a.1)
          mul_mem' := fun {u v} hu hv a => by
            have hu' : (actHom a.1) u = u := hu a
            have hv' : (actHom a.1) v = v := hv a
            change (actHom a.1) (u * v) = u * v
            rw [map_mul, hu', hv']
          inv_mem' := fun {u} hu a => by
            have hu' : (actHom a.1) u = u := hu a
            change (actHom a.1) u⁻¹ = u⁻¹
            rw [map_inv, hu']
        }
        have hF_card_eq : Nat.card (MulAction.fixedPoints Q N) = Nat.card F := rfl
        have hF_dvd : Nat.card F ∣ r ^ k := by
          rw [← hk_eq]; exact Subgroup.card_subgroup_dvd_card F
        obtain ⟨j, hjk, hj_eq⟩ := (Nat.dvd_prime_pow hr).mp hF_dvd
        have hj_lt : j < k := by
          rcases lt_or_eq_of_le hjk with hlt | rfl
          · exact hlt
          · exfalso
            have hFtop : F = ⊤ := by
              by_contra hne
              have hlt := card_lt_of_lt_top (lt_top_iff_ne_top.mpr hne)
              omega
            obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
            have hgC : g ∈ C := by
              rw [Subgroup.mem_centralizer_iff]
              intro n hn
              have hmem : (⟨n, hn⟩ : N) ∈ F := by rw [hFtop]; trivial
              have hfix := hmem ⟨QuotientGroup.mk g, Subgroup.mem_zpowers _⟩
              have hval : g * n * g⁻¹ = n := congrArg Subtype.val hfix
              calc n * g = g * n * g⁻¹ * g := by rw [hval]
                _ = g * n := by group
            have hy1 : (QuotientGroup.mk g : G ⧸ C) = 1 :=
              (QuotientGroup.eq_one_iff g).mpr hgC
            rw [hy1, orderOf_one] at hyord
            exact hq.ne_one hyord.symm
        have hmod : r ^ k ≡ r ^ j [MOD q] := by
          have hm := hQ_pgroup.card_modEq_card_fixedPoints N
          rwa [hk_eq, hF_card_eq, hj_eq] at hm
        have hle_pow : r ^ j ≤ r ^ k := Nat.pow_le_pow_right hr.pos hj_lt.le
        have hdvd_sub : q ∣ r ^ k - r ^ j := (Nat.modEq_iff_dvd' hle_pow).mp hmod.symm
        have hfac : r ^ k - r ^ j = r ^ j * (r ^ (k - j) - 1) := by
          have hk_split : r ^ k = r ^ j * r ^ (k - j) := by
            rw [← pow_add, Nat.add_sub_of_le hj_lt.le]
          rw [hk_split, Nat.mul_sub_left_distrib, mul_one]
        rw [hfac] at hdvd_sub
        have hcop : Nat.Coprime q (r ^ j) :=
          ((Nat.coprime_primes hq hr).mpr hqr).pow_right j
        have hdvd_m : q ∣ r ^ (k - j) - 1 := hcop.dvd_of_dvd_mul_left hdvd_sub
        have hqG : q ∣ Nat.card G := by
          have hlag : Nat.card (G ⧸ C) * Nat.card C = Nat.card G := by
            rw [mul_comm]; exact C.card_mul_index
          exact hqGC.trans ⟨Nat.card C, hlag.symm⟩
        have hrG : r ^ (k - j) ∣ Nat.card G := by
          have h1 : r ^ (k - j) ∣ r ^ k := pow_dvd_pow r (Nat.sub_le k j)
          have h2 : r ^ k ∣ Nat.card G := hk_eq ▸ Subgroup.card_subgroup_dvd_card N
          exact h1.trans h2
        exact hnn q r (k - j) hq hr hqr hqG (by omega) hrG hdvd_m

theorem H3_proof : ∀ (G : Type) [Group G] [Finite G],
    (∀ q r k : ℕ, q.Prime → r.Prime → q ≠ r → q ∣ Nat.card G →
      0 < k → r ^ k ∣ Nat.card G → ¬ q ∣ r ^ k - 1) → Group.IsNilpotent G :=
  fun G _ _ h => main_ind (Nat.card G) G le_rfl h

end OMA.P_mo_273976_R1_H3

theorem OMA.solution : OMA.R_mo_273976_R1.H3 :=
  OMA.P_mo_273976_R1_H3.H3_proof
