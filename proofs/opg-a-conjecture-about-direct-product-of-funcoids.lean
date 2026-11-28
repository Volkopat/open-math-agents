import OMAStatements.S_opg_a_conjecture_about_direct_product_of_funcoids

namespace OpgDirectProductFuncoids

open OMA.S_opg_a_conjecture_about_direct_product_of_funcoids
open Filter

/-! Section 1: Elementary Filter and Funcoid Primitives -/

private lemma mem_iff_not_overlap_compl {α : Type*} (x : Filter α) (S : Set α) :
    S ∈ x ↔ ¬ Overlap x (𝓟 Sᶜ) := by
  unfold Overlap
  constructor
  · intro hS hne
    have hempty : (∅ : Set α) ∈ x ⊓ 𝓟 Sᶜ := by
      have hinter : S ∩ Sᶜ ∈ x ⊓ 𝓟 Sᶜ := Filter.inter_mem_inf hS (Filter.mem_principal_self Sᶜ)
      simp only [Set.inter_compl_self] at hinter
      exact hinter
    exact hne.ne (Filter.empty_mem_iff_bot.mp hempty)
  · intro hnot
    have hbot : x ⊓ 𝓟 Sᶜ = ⊥ := Filter.not_neBot.mp hnot
    have hempty : (∅ : Set α) ∈ x ⊓ 𝓟 Sᶜ := Filter.empty_mem_iff_bot.mpr hbot
    obtain ⟨U, hU, V, hV, hUV⟩ := Filter.mem_inf_iff.mp hempty
    rw [Filter.mem_principal] at hV
    have hsub : U ⊆ S := by
      intro a haU
      by_contra haS
      have hmem : a ∈ U ∩ V := ⟨haU, hV haS⟩
      rw [← hUV] at hmem
      exact hmem
    exact Filter.mem_of_superset hU hsub

private lemma overlap_symm {α : Type*} {x y : Filter α} : Overlap x y ↔ Overlap y x := by
  unfold Overlap
  rw [inf_comm]

private lemma overlap_mono {α : Type*} {x y z : Filter α} (hxy : x ≤ y) (h : Overlap x z) :
    Overlap y z :=
  Filter.NeBot.mono h (inf_le_inf_right z hxy)

private lemma filter_le_of_overlap {α : Type*} {x y : Filter α}
    (h : ∀ z : Filter α, Overlap x z → Overlap y z) : x ≤ y := by
  intro S hSy
  by_contra hSx
  have hovx : Overlap x (𝓟 Sᶜ) := by
    by_contra hnot
    exact hSx ((mem_iff_not_overlap_compl x S).mpr hnot)
  have hovy : Overlap y (𝓟 Sᶜ) := h (𝓟 Sᶜ) hovx
  exact (mem_iff_not_overlap_compl y S).mp hSy hovy

private lemma filter_le_of_ultrafilter {α : Type*} {x y : Filter α}
    (h : ∀ u : Ultrafilter α, (u : Filter α) ≤ x → (u : Filter α) ≤ y) : x ≤ y := by
  intro S hSy
  by_contra hSx
  have hovx : (x ⊓ 𝓟 Sᶜ).NeBot := by
    by_contra hnot
    exact hSx ((mem_iff_not_overlap_compl x S).mpr hnot)
  obtain ⟨u, hu⟩ := @Ultrafilter.exists_le α (x ⊓ 𝓟 Sᶜ) hovx
  have hux : (u : Filter α) ≤ x := hu.trans inf_le_left
  have huSc : Sᶜ ∈ (u : Filter α) := Filter.le_principal_iff.mp (hu.trans inf_le_right)
  have huS : S ∈ (u : Filter α) := h u hux hSy
  have hempty : (∅ : Set α) ∈ (u : Filter α) := by
    have hinter := Filter.inter_mem huS huSc
    simp only [Set.inter_compl_self] at hinter
    exact hinter
  exact u.neBot.ne (Filter.empty_mem_iff_bot.mp hempty)

private lemma ultrafilter_overlap_iff_le {α : Type*} (u : Ultrafilter α) (x : Filter α) :
    Overlap (u : Filter α) x ↔ (u : Filter α) ≤ x := by
  constructor
  · intro hov S hSx
    rcases u.mem_or_compl_mem S with hS | hSc
    · exact hS
    · exfalso
      have hempty : (∅ : Set α) ∈ (u : Filter α) ⊓ x := by
        have := Filter.inter_mem_inf hSc hSx
        simpa using this
      exact hov.ne (Filter.empty_mem_iff_bot.mp hempty)
  · intro hle
    unfold Overlap
    rw [inf_eq_left.mpr hle]
    exact u.neBot

private lemma funcoid_forward_mono {α β : Type*} (h : Funcoid α β) {x₁ x₂ : Filter α}
    (hle : x₁ ≤ x₂) : h.forward x₁ ≤ h.forward x₂ := by
  apply filter_le_of_overlap
  intro z hov
  exact (h.compatible x₂ z).mpr (overlap_mono hle ((h.compatible x₁ z).mp hov))

private lemma funcoid_reverse_mono {α β : Type*} (h : Funcoid α β) {y₁ y₂ : Filter β}
    (hle : y₁ ≤ y₂) : h.reverse y₁ ≤ h.reverse y₂ := by
  apply filter_le_of_overlap
  intro z hov
  have h1 : Overlap (h.forward z) y₁ := (h.compatible z y₁).mpr (overlap_symm.mp hov)
  have h2 : Overlap (h.forward z) y₂ := overlap_symm.mp (overlap_mono hle (overlap_symm.mp h1))
  exact overlap_symm.mp ((h.compatible z y₂).mp h2)

private lemma funcoid_forward_bot {α β : Type*} (h : Funcoid α β) : h.forward ⊥ = ⊥ := by
  rw [← Filter.not_neBot]
  intro hne
  have hov : Overlap (h.forward ⊥) ⊤ := by
    unfold Overlap; simpa using hne
  have hov' : Overlap ⊥ (h.reverse ⊤) := (h.compatible ⊥ ⊤).mp hov
  unfold Overlap at hov'
  simp only [bot_inf_eq] at hov'
  exact hov'.ne rfl

private lemma funcoid_reverse_bot {α β : Type*} (h : Funcoid α β) : h.reverse ⊥ = ⊥ := by
  rw [← Filter.not_neBot]
  intro hne
  have hov : Overlap ⊤ (h.reverse ⊥) := by
    unfold Overlap; simpa using hne
  have hov' : Overlap (h.forward ⊤) ⊥ := (h.compatible ⊤ ⊥).mpr hov
  unfold Overlap at hov'
  simp only [inf_bot_eq] at hov'
  exact hov'.ne rfl

/-! Section 2: Ultrafilter Action of Monovalued Entire Funcoids -/

private lemma entire_reverse_top {α β : Type*} {h : Funcoid α β} (he : Entire h) :
    h.reverse ⊤ = ⊤ :=
  top_unique ((he ⊤).trans (funcoid_reverse_mono h le_top))

private lemma entire_forward_neBot {α β : Type*} {h : Funcoid α β} (he : Entire h)
    {x : Filter α} (hx : x.NeBot) : (h.forward x).NeBot := by
  rw [Filter.neBot_iff]
  intro hbot
  have hle : x ≤ ⊥ := by
    calc
      x ≤ h.reverse (h.forward x) := he x
      _ = h.reverse ⊥ := by rw [hbot]
      _ = ⊥ := funcoid_reverse_bot h
  exact hx.ne (le_bot_iff.mp hle)

private lemma monovalued_entire_forward_eq {α β : Type*} {h : Funcoid α β}
    (hm : Monovalued h) (he : Entire h) (u : Ultrafilter α) (b : Ultrafilter β)
    (hle : (u : Filter α) ≤ h.reverse (b : Filter β)) :
    h.forward (u : Filter α) = (b : Filter β) := by
  have hle1 : h.forward (u : Filter α) ≤ (b : Filter β) :=
    (funcoid_forward_mono h hle).trans (hm (b : Filter β))
  have hne : (h.forward (u : Filter α)).NeBot := entire_forward_neBot he u.neBot
  apply le_antisymm hle1
  intro S hS
  rcases b.mem_or_compl_mem S with hSb | hScb
  · exact hSb
  · exfalso
    have hSc : Sᶜ ∈ h.forward (u : Filter α) := hle1 hScb
    have hempty : (∅ : Set β) ∈ h.forward (u : Filter α) := by
      have hinter := Filter.inter_mem hS hSc
      simp only [Set.inter_compl_self] at hinter
      exact hinter
    exact hne.ne (Filter.empty_mem_iff_bot.mp hempty)

private lemma monovalued_entire_forward_ultrafilter {α β : Type*} {h : Funcoid α β}
    (hm : Monovalued h) (he : Entire h) (u : Ultrafilter α) :
    ∃ b : Ultrafilter β, (b : Filter β) = h.forward (u : Filter α) := by
  have hne : (h.forward (u : Filter α)).NeBot := entire_forward_neBot he u.neBot
  obtain ⟨b, hb⟩ := @Ultrafilter.exists_le β (h.forward (u : Filter α)) hne
  have hov1 : Overlap (h.forward (u : Filter α)) (b : Filter β) :=
    overlap_symm.mp ((ultrafilter_overlap_iff_le b (h.forward u)).mpr hb)
  have hov2 : Overlap (u : Filter α) (h.reverse (b : Filter β)) :=
    (h.compatible (u : Filter α) (b : Filter β)).mp hov1
  have hle : (u : Filter α) ≤ h.reverse (b : Filter β) :=
    (ultrafilter_overlap_iff_le u (h.reverse b)).mp hov2
  exact ⟨b, (monovalued_entire_forward_eq hm he u b hle).symm⟩

/-! Section 3: Construction of dForward and Monotonicity -/

private def dForward {A B C : Type*} (f : Funcoid A B) (g : Funcoid A C)
    (x : Filter A) : Funcoid B C where
  forward y := g.forward (x ⊓ f.reverse y)
  reverse z := f.forward (x ⊓ g.reverse z)
  compatible y z := by
    rw [g.compatible]
    have hinf : Overlap (x ⊓ f.reverse y) (g.reverse z) ↔ Overlap (x ⊓ g.reverse z) (f.reverse y) := by
      unfold Overlap
      rw [inf_assoc, inf_comm (f.reverse y) (g.reverse z), ← inf_assoc]
    rw [hinf, ← f.compatible, overlap_symm]

private lemma dForward_mono {A B C : Type*} (f : Funcoid A B) (g : Funcoid A C)
    {x₁ x₂ : Filter A} (hx : x₁ ≤ x₂) : Below (dForward f g x₁) (dForward f g x₂) := by
  intro y
  exact funcoid_forward_mono g (inf_le_inf_right (f.reverse y) hx)

/-! Section 4: Universal Join Property of dForward -/

private lemma below_dForward_iff {A B C : Type*} (f : Funcoid A B) (g : Funcoid A C)
    (hmg : Monovalued g) (heg : Entire g)
    (x : Filter A) (r : Funcoid B C) :
    Below (dForward f g x) r ↔
      ∀ u : Ultrafilter A, (u : Filter A) ≤ x →
        ∀ y : Filter B, productAction (f.forward u) (g.forward u) y ≤ r.forward y := by
  constructor
  · intro hbelow u hux y
    unfold productAction
    split_ifs with hov
    · have hov1 : Overlap (u : Filter A) (f.reverse y) :=
        (f.compatible (u : Filter A) y).mp (overlap_symm.mp hov)
      have huf : (u : Filter A) ≤ f.reverse y :=
        (ultrafilter_overlap_iff_le u (f.reverse y)).mp hov1
      exact (funcoid_forward_mono g (le_inf hux huf)).trans (hbelow y)
    · exact bot_le
  · intro hr y
    apply filter_le_of_ultrafilter
    intro c hc
    have hovc : Overlap (g.forward (x ⊓ f.reverse y)) (c : Filter C) :=
      overlap_symm.mp ((ultrafilter_overlap_iff_le c _).mpr hc)
    have hne : (x ⊓ f.reverse y ⊓ g.reverse (c : Filter C)).NeBot :=
      (g.compatible (x ⊓ f.reverse y) (c : Filter C)).mp hovc
    obtain ⟨u, hu⟩ := @Ultrafilter.exists_le A (x ⊓ f.reverse y ⊓ g.reverse (c : Filter C)) hne
    have hux : (u : Filter A) ≤ x := hu.trans (inf_le_left.trans inf_le_left)
    have huf : (u : Filter A) ≤ f.reverse y := hu.trans (inf_le_left.trans inf_le_right)
    have hug : (u : Filter A) ≤ g.reverse (c : Filter C) := hu.trans inf_le_right
    have hovf : Overlap y (f.forward (u : Filter A)) :=
      overlap_symm.mp ((f.compatible (u : Filter A) y).mpr ((ultrafilter_overlap_iff_le u _).mpr huf))
    have hgu : g.forward (u : Filter A) = (c : Filter C) :=
      monovalued_entire_forward_eq hmg heg u c hug
    have hstep := hr u hux y
    unfold productAction at hstep
    rw [if_pos hovf, hgu] at hstep
    exact hstep

/-! Section 5: Construction of dReverse, Closedness Lemma, and d.compatible -/

private noncomputable def dReverse {A B C : Type*} (f : Funcoid A B) (g : Funcoid A C)
    (r : Funcoid B C) : Filter A :=
  ⨆ (u : Ultrafilter A) (_ : g.forward (u : Filter A) ≤ r.forward (f.forward (u : Filter A))),
    (u : Filter A)

private lemma meetNonzero_imp_overlap {A B C : Type*} (f : Funcoid A B) (g : Funcoid A C)
    (hmf : Monovalued f) (hef : Entire f) (hmg : Monovalued g) (heg : Entire g)
    (x : Filter A) (r : Funcoid B C)
    (hmn : MeetNonzero (dForward f g x) r) : Overlap x (dReverse f g r) := by
  obtain ⟨k, hkd, hkr, y₀, hy₀⟩ := hmn
  obtain ⟨c₀, hc₀⟩ := @Ultrafilter.exists_le C (k.forward y₀) hy₀
  have hov_ky₀ : Overlap (k.forward y₀) (c₀ : Filter C) :=
    overlap_symm.mp ((ultrafilter_overlap_iff_le c₀ _).mpr hc₀)
  have hne_b : (y₀ ⊓ k.reverse (c₀ : Filter C)).NeBot := (k.compatible y₀ c₀).mp hov_ky₀
  obtain ⟨b₀, hb₀⟩ := @Ultrafilter.exists_le B (y₀ ⊓ k.reverse (c₀ : Filter C)) hne_b
  have hb₀_k : (b₀ : Filter B) ≤ k.reverse (c₀ : Filter C) := hb₀.trans inf_le_right
  have hov_kb₀ : Overlap (k.forward (b₀ : Filter B)) (c₀ : Filter C) :=
    (k.compatible b₀ c₀).mpr ((ultrafilter_overlap_iff_le b₀ _).mpr hb₀_k)
  have hov_db₀ : Overlap (g.forward (x ⊓ f.reverse (b₀ : Filter B))) (c₀ : Filter C) :=
    overlap_mono (hkd b₀) hov_kb₀
  have hne_u : (x ⊓ f.reverse (b₀ : Filter B) ⊓ g.reverse (c₀ : Filter C)).NeBot :=
    (g.compatible (x ⊓ f.reverse b₀) c₀).mp hov_db₀
  obtain ⟨u, hu⟩ := @Ultrafilter.exists_le A (x ⊓ f.reverse b₀ ⊓ g.reverse c₀) hne_u
  have hux : (u : Filter A) ≤ x := hu.trans (inf_le_left.trans inf_le_left)
  have hfu : f.forward (u : Filter A) = (b₀ : Filter B) :=
    monovalued_entire_forward_eq hmf hef u b₀ (hu.trans (inf_le_left.trans inf_le_right))
  have hgu : g.forward (u : Filter A) = (c₀ : Filter C) :=
    monovalued_entire_forward_eq hmg heg u c₀ (hu.trans inf_le_right)
  have hov_rc : Overlap (c₀ : Filter C) (r.forward (b₀ : Filter B)) :=
    overlap_symm.mp (overlap_mono (hkr b₀) hov_kb₀)
  have hle_rc : g.forward (u : Filter A) ≤ r.forward (f.forward (u : Filter A)) := by
    rw [hgu, hfu]
    exact (ultrafilter_overlap_iff_le c₀ (r.forward b₀)).mp hov_rc
  have hu_rev : (u : Filter A) ≤ dReverse f g r := by
    intro S hS
    unfold dReverse at hS
    rw [Filter.mem_iSup] at hS
    have hSu := hS u
    rw [Filter.mem_iSup] at hSu
    exact hSu hle_rc
  exact Filter.NeBot.mono u.neBot (le_inf hux hu_rev)

private lemma not_overlap_exists_compl_mem {α : Type*} {x y : Filter α}
    (hnot : ¬ Overlap x y) : ∃ U ∈ x, Uᶜ ∈ y := by
  have hbot : x ⊓ y = ⊥ := Filter.not_neBot.mp hnot
  have hempty : (∅ : Set α) ∈ x ⊓ y := Filter.empty_mem_iff_bot.mpr hbot
  obtain ⟨U, hU, V, hV, hUV⟩ := Filter.mem_inf_iff.mp hempty
  have hsub : V ⊆ Uᶜ := by
    intro a haV haU
    have hmem : a ∈ U ∩ V := ⟨haU, haV⟩
    rw [← hUV] at hmem
    exact hmem
  exact ⟨U, hU, Filter.mem_of_superset hV hsub⟩

private lemma ultrafilter_le_dReverse_imp {A B C : Type*} (f : Funcoid A B) (g : Funcoid A C)
    (hmg : Monovalued g) (heg : Entire g)
    (r : Funcoid B C) (w : Ultrafilter A)
    (hw : (w : Filter A) ≤ dReverse f g r) :
    g.forward (w : Filter A) ≤ r.forward (f.forward (w : Filter A)) := by
  by_contra hnot
  have hexT : ∃ T : Set C, T ∈ r.forward (f.forward (w : Filter A)) ∧ T ∉ g.forward (w : Filter A) := by
    by_contra hall
    apply hnot
    intro T hT
    by_contra hTg
    exact hall ⟨T, hT, hTg⟩
  obtain ⟨T, hTr, hTg⟩ := hexT
  obtain ⟨cw, hcw⟩ := monovalued_entire_forward_ultrafilter hmg heg w
  have hTc_g : Tᶜ ∈ g.forward (w : Filter A) := by
    rw [← hcw] at hTg ⊢
    exact (cw.mem_or_compl_mem T).resolve_left hTg
  have hnot_r : ¬ Overlap (f.forward (w : Filter A)) (r.reverse (𝓟 Tᶜ)) := by
    rw [← r.compatible]
    exact (mem_iff_not_overlap_compl _ T).mp hTr
  obtain ⟨S, hSfw, hSc_r⟩ := not_overlap_exists_compl_mem hnot_r
  have hdag : ¬ Overlap (r.forward (𝓟 S)) (𝓟 Tᶜ) := by
    rw [r.compatible]
    intro hov
    have hempty : (∅ : Set B) ∈ 𝓟 S ⊓ r.reverse (𝓟 Tᶜ) := by
      have := Filter.inter_mem_inf (Filter.mem_principal_self S) hSc_r
      simpa using this
    exact hov.ne (Filter.empty_mem_iff_bot.mp hempty)
  have hnot_f : ¬ Overlap (w : Filter A) (f.reverse (𝓟 Sᶜ)) := by
    rw [← f.compatible]
    exact (mem_iff_not_overlap_compl _ S).mp hSfw
  obtain ⟨A₁, hA₁w, hA₁c_f⟩ := not_overlap_exists_compl_mem hnot_f
  have hnot_g : ¬ Overlap (w : Filter A) (g.reverse (𝓟 T)) := by
    rw [← g.compatible]
    have hTcc : (Tᶜ)ᶜ = T := compl_compl T
    rw [← hTcc]
    exact (mem_iff_not_overlap_compl _ Tᶜ).mp hTc_g
  obtain ⟨A₂, hA₂w, hA₂c_g⟩ := not_overlap_exists_compl_mem hnot_g
  let A₀ : Set A := A₁ ∩ A₂
  have hA₀w : A₀ ∈ (w : Filter A) := Filter.inter_mem hA₁w hA₂w
  have hA₀c_all : ∀ (u : Ultrafilter A),
      g.forward (u : Filter A) ≤ r.forward (f.forward (u : Filter A)) → A₀ᶜ ∈ (u : Filter A) := by
    intro u hu
    rcases u.mem_or_compl_mem A₀ with hA₀u | hA₀cu
    · exfalso
      have hA₁u : A₁ ∈ (u : Filter A) := Filter.mem_of_superset hA₀u Set.inter_subset_left
      have hA₂u : A₂ ∈ (u : Filter A) := Filter.mem_of_superset hA₀u Set.inter_subset_right
      have hSfu : S ∈ f.forward (u : Filter A) := by
        rw [mem_iff_not_overlap_compl, f.compatible]
        intro hov
        have hempty : (∅ : Set A) ∈ (u : Filter A) ⊓ f.reverse (𝓟 Sᶜ) := by
          have := Filter.inter_mem_inf hA₁u hA₁c_f
          simpa using this
        exact hov.ne (Filter.empty_mem_iff_bot.mp hempty)
      have hTcgu : Tᶜ ∈ g.forward (u : Filter A) := by
        rw [mem_iff_not_overlap_compl, compl_compl, g.compatible]
        intro hov
        have hempty : (∅ : Set A) ∈ (u : Filter A) ⊓ g.reverse (𝓟 T) := by
          have := Filter.inter_mem_inf hA₂u hA₂c_g
          simpa using this
        exact hov.ne (Filter.empty_mem_iff_bot.mp hempty)
      have hle_r : g.forward (u : Filter A) ≤ r.forward (𝓟 S) :=
        hu.trans (funcoid_forward_mono r (Filter.le_principal_iff.mpr hSfu))
      have hle_T : g.forward (u : Filter A) ≤ 𝓟 Tᶜ := Filter.le_principal_iff.mpr hTcgu
      have hne_gu : (g.forward (u : Filter A)).NeBot := entire_forward_neBot heg u.neBot
      exact hdag (Filter.NeBot.mono hne_gu (le_inf hle_r hle_T))
    · exact hA₀cu
  have hA₀c_rev : A₀ᶜ ∈ dReverse f g r := by
    unfold dReverse
    rw [Filter.mem_iSup]
    intro u
    rw [Filter.mem_iSup]
    intro hu
    exact hA₀c_all u hu
  have hA₀c_w : A₀ᶜ ∈ (w : Filter A) := hw hA₀c_rev
  have hempty : (∅ : Set A) ∈ (w : Filter A) := by
    have hinter := Filter.inter_mem hA₀w hA₀c_w
    simp only [Set.inter_compl_self] at hinter
    exact hinter
  exact w.neBot.ne (Filter.empty_mem_iff_bot.mp hempty)

private lemma overlap_imp_meetNonzero {A B C : Type*} (f : Funcoid A B) (g : Funcoid A C)
    (hmf : Monovalued f) (hef : Entire f) (hmg : Monovalued g) (heg : Entire g)
    (x : Filter A) (r : Funcoid B C)
    (hov : Overlap x (dReverse f g r)) : MeetNonzero (dForward f g x) r := by
  obtain ⟨w, hw⟩ := @Ultrafilter.exists_le A (x ⊓ dReverse f g r) hov
  have hwx : (w : Filter A) ≤ x := hw.trans inf_le_left
  have hw_rev : (w : Filter A) ≤ dReverse f g r := hw.trans inf_le_right
  have hgw : g.forward (w : Filter A) ≤ r.forward (f.forward (w : Filter A)) :=
    ultrafilter_le_dReverse_imp f g hmg heg r w hw_rev
  refine ⟨dForward f g (w : Filter A), dForward_mono f g hwx, ?_, ⊤, ?_⟩
  · rw [below_dForward_iff f g hmg heg]
    intro u huw y
    have hueq : (u : Filter A) = (w : Filter A) := by
      apply le_antisymm huw
      have hov_wu : Overlap (w : Filter A) (u : Filter A) :=
        overlap_symm.mp ((ultrafilter_overlap_iff_le u (w : Filter A)).mpr huw)
      exact (ultrafilter_overlap_iff_le w (u : Filter A)).mp hov_wu
    rw [hueq]
    unfold productAction
    split_ifs with hovy
    · obtain ⟨bw, hbw⟩ := monovalued_entire_forward_ultrafilter hmf hef w
      have hfw_y : f.forward (w : Filter A) ≤ y := by
        rw [← hbw] at hovy ⊢
        exact (ultrafilter_overlap_iff_le bw y).mp (overlap_symm.mp hovy)
      exact hgw.trans (funcoid_forward_mono r hfw_y)
    · exact bot_le
  · change (g.forward ((w : Filter A) ⊓ f.reverse ⊤)).NeBot
    rw [entire_reverse_top hef, inf_top_eq]
    exact entire_forward_neBot heg w.neBot

/-! Section 6: Main Theorem Assembly -/

theorem main_proof :
    ∀ (A B C : Type*) (f : Funcoid A B) (g : Funcoid A C),
      Monovalued f → Entire f → Monovalued g → Entire g →
      ∃ d : Pointfree (Filter A) (Funcoid B C) Overlap MeetNonzero,
        ∀ (x : Filter A) (r : Funcoid B C), Below (d.forward x) r ↔
          ∀ u : Ultrafilter A, (u : Filter A) ≤ x →
            ∀ y : Filter B, productAction (f.forward u) (g.forward u) y ≤ r.forward y := by
  intro A B C f g hmf hef hmg heg
  let d : Pointfree (Filter A) (Funcoid B C) Overlap MeetNonzero :=
    { forward := dForward f g
      reverse := dReverse f g
      compatible := fun x r =>
        ⟨meetNonzero_imp_overlap f g hmf hef hmg heg x r,
         overlap_imp_meetNonzero f g hmf hef hmg heg x r⟩ }
  exact ⟨d, fun x r => below_dForward_iff f g hmg heg x r⟩

end OpgDirectProductFuncoids

theorem OMA.solution : type_of% @OMA.S_opg_a_conjecture_about_direct_product_of_funcoids.main :=
  OpgDirectProductFuncoids.main_proof
