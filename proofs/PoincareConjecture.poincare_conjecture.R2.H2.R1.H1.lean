import OMAReductions.R_PoincareConjecture_poincare_conjecture_R2_H2_R1
import Mathlib

/-!
Construction of the universal covering space for a connected 3-manifold with finite
fundamental group, proving that it is simply connected and has finite fibers.
-/

open Set TopologicalSpace Topology
open scoped unitInterval

namespace PoincareUniversalCoverProof

private abbrev Model3 := EuclideanSpace ℝ (Fin 3)

/- ### Path-homotopy quotient algebra -/

private lemma q_trans_assoc {X : Type*} [TopologicalSpace X] {a b c d : X}
    (p : Path.Homotopic.Quotient a b) (q : Path.Homotopic.Quotient b c)
    (r : Path.Homotopic.Quotient c d) :
    (p.trans q).trans r = p.trans (q.trans r) := by
  let p' : FundamentalGroupoid.mk a ⟶ FundamentalGroupoid.mk b := p
  let q' : FundamentalGroupoid.mk b ⟶ FundamentalGroupoid.mk c := q
  let r' : FundamentalGroupoid.mk c ⟶ FundamentalGroupoid.mk d := r
  exact CategoryTheory.Category.assoc p' q' r'

private lemma q_refl_trans {X : Type*} [TopologicalSpace X] {a b : X}
    (p : Path.Homotopic.Quotient a b) :
    (Path.Homotopic.Quotient.refl a).trans p = p := by
  let p' : FundamentalGroupoid.mk a ⟶ FundamentalGroupoid.mk b := p
  exact CategoryTheory.Category.id_comp p'

private lemma q_trans_refl {X : Type*} [TopologicalSpace X] {a b : X}
    (p : Path.Homotopic.Quotient a b) :
    p.trans (Path.Homotopic.Quotient.refl b) = p := by
  let p' : FundamentalGroupoid.mk a ⟶ FundamentalGroupoid.mk b := p
  exact CategoryTheory.Category.comp_id p'

private lemma q_trans_symm {X : Type*} [TopologicalSpace X] {a b : X}
    (p : Path.Homotopic.Quotient a b) :
    p.trans p.symm = Path.Homotopic.Quotient.refl a := by
  let p' : FundamentalGroupoid.mk a ⟶ FundamentalGroupoid.mk b := p
  exact CategoryTheory.Groupoid.comp_inv p'

private lemma q_symm_trans {X : Type*} [TopologicalSpace X] {a b : X}
    (p : Path.Homotopic.Quotient a b) :
    p.symm.trans p = Path.Homotopic.Quotient.refl b := by
  let p' : FundamentalGroupoid.mk a ⟶ FundamentalGroupoid.mk b := p
  exact CategoryTheory.Groupoid.inv_comp p'

private lemma q_cancel_left {X : Type*} [TopologicalSpace X] {a b c : X}
    (p : Path.Homotopic.Quotient a b) {q₁ q₂ : Path.Homotopic.Quotient b c}
    (h : p.trans q₁ = p.trans q₂) : q₁ = q₂ := by
  have h1 := congrArg (fun r => p.symm.trans r) h
  simpa [← q_trans_assoc, q_symm_trans, q_refl_trans] using h1

private lemma q_cancel_right {X : Type*} [TopologicalSpace X] {a b c : X}
    {p₁ p₂ : Path.Homotopic.Quotient a b} (q : Path.Homotopic.Quotient b c)
    (h : p₁.trans q = p₂.trans q) : p₁ = p₂ := by
  have h1 := congrArg (fun r => r.trans q.symm) h
  simpa [q_trans_assoc, q_trans_symm, q_trans_refl] using h1

/- ### Good open neighborhoods (open, path-connected, relatively simply connected) -/

private def IsGood {M : Type} [TopologicalSpace M] (U : Set M) : Prop :=
  IsOpen U ∧ IsPathConnected U ∧
    ∀ {a b : M} (γ₁ γ₂ : Path a b),
      (∀ t, γ₁ t ∈ U) → (∀ t, γ₂ t ∈ U) → Path.Homotopic γ₁ γ₂

private lemma exists_isGood_subset {M : Type} [TopologicalSpace M]
    [ChartedSpace Model3 M] {x : M} {W : Set M} (hW : IsOpen W) (hxW : x ∈ W) :
    ∃ U : Set M, IsGood U ∧ x ∈ U ∧ U ⊆ W := by
  let φ := chartAt Model3 x
  have hxS : x ∈ φ.source := mem_chart_source Model3 x
  have hT_open : IsOpen (φ.target ∩ φ.symm ⁻¹' W) :=
    φ.continuousOn_invFun.isOpen_inter_preimage φ.open_target hW
  have hT_mem : φ x ∈ φ.target ∩ φ.symm ⁻¹' W :=
    ⟨φ.map_source hxS, by simpa [Set.mem_preimage, φ.left_inv hxS] using hxW⟩
  obtain ⟨r, hrpos, hball⟩ := Metric.isOpen_iff.mp hT_open (φ x) hT_mem
  let B : Set Model3 := Metric.ball (φ x) r
  let U : Set M := φ.source ∩ φ ⁻¹' B
  have hU_open : IsOpen U := φ.continuousOn.isOpen_inter_preimage φ.open_source Metric.isOpen_ball
  have hxU : x ∈ U := ⟨hxS, Metric.mem_ball_self hrpos⟩
  have hU_sub : U ⊆ W := by
    intro y hy
    have hmem : φ y ∈ φ.target ∩ φ.symm ⁻¹' W := hball hy.2
    have hinv : φ.symm (φ y) = y := φ.left_inv hy.1
    simpa [Set.mem_preimage, hinv] using hmem.2
  have hB_sub : B ⊆ φ.target := fun z hz => (hball hz).1
  let e : U ≃ₜ B :=
    { toFun := fun y => ⟨φ y.1, y.2.2⟩
      invFun := fun z =>
        ⟨φ.symm z.1, φ.map_target (hB_sub z.2), by
          show φ (φ.symm z.1) ∈ B
          rw [φ.right_inv (hB_sub z.2)]
          exact z.2⟩
      left_inv := fun y => Subtype.ext (φ.left_inv y.2.1)
      right_inv := fun z => Subtype.ext (φ.right_inv (hB_sub z.2))
      continuous_toFun :=
        (φ.continuousOn.comp_continuous continuous_subtype_val (fun y => y.2.1)).subtype_mk _
      continuous_invFun :=
        (φ.continuousOn_invFun.comp_continuous continuous_subtype_val
          (fun z => hB_sub z.2)).subtype_mk _ }
  have hB_contract : ContractibleSpace B :=
    (convex_ball (φ x) r).contractibleSpace ⟨φ x, Metric.mem_ball_self hrpos⟩
  have hB_sc : SimplyConnectedSpace B := SimplyConnectedSpace.ofContractible B
  have hU_sc : SimplyConnectedSpace U := e.toHomotopyEquiv.simplyConnectedSpace
  have hU_pc_type : PathConnectedSpace U := inferInstance
  have hU_pc : IsPathConnected U := by
    refine ⟨x, hxU, fun y hy => ?_⟩
    obtain ⟨γ⟩ := PathConnectedSpace.joined (⟨x, hxU⟩ : U) (⟨y, hy⟩ : U)
    exact ⟨γ.map continuous_subtype_val, fun t => (γ t).2⟩
  have hU_hom : ∀ {a b : M} (γ₁ γ₂ : Path a b),
      (∀ t, γ₁ t ∈ U) → (∀ t, γ₂ t ∈ U) → Path.Homotopic γ₁ γ₂ := by
    intro a b γ₁ γ₂ hγ₁ hγ₂
    have ha : a ∈ U := by simpa using hγ₁ 0
    have hb : b ∈ U := by simpa using hγ₁ 1
    let γ₁' : Path (⟨a, ha⟩ : U) (⟨b, hb⟩ : U) :=
      { toFun := fun t => ⟨γ₁ t, hγ₁ t⟩
        continuous_toFun := γ₁.continuous.subtype_mk hγ₁
        source' := Subtype.ext γ₁.source
        target' := Subtype.ext γ₁.target }
    let γ₂' : Path (⟨a, ha⟩ : U) (⟨b, hb⟩ : U) :=
      { toFun := fun t => ⟨γ₂ t, hγ₂ t⟩
        continuous_toFun := γ₂.continuous.subtype_mk hγ₂
        source' := Subtype.ext γ₂.source
        target' := Subtype.ext γ₂.target }
    obtain ⟨F⟩ := SimplyConnectedSpace.paths_homotopic γ₁' γ₂'
    exact ⟨F.map ⟨Subtype.val, continuous_subtype_val⟩⟩
  exact ⟨U, ⟨hU_open, hU_pc, hU_hom⟩, hxU, hU_sub⟩

private lemma pathConnectedSpace_of_charted {M : Type} [TopologicalSpace M]
    [ConnectedSpace M] [ChartedSpace Model3 M] : PathConnectedSpace M := by
  obtain ⟨x₀⟩ := (inferInstance : Nonempty M)
  let S : Set M := {y | Joined x₀ y}
  have hS_open : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    intro y hy
    obtain ⟨U, hU, hyU, _⟩ := exists_isGood_subset isOpen_univ (Set.mem_univ y)
    refine Filter.mem_of_superset (hU.1.mem_nhds hyU) fun z hz => ?_
    exact hy.trans (hU.2.1.joinedIn y hyU z hz).joined
  have hSc_open : IsOpen Sᶜ := by
    rw [isOpen_iff_mem_nhds]
    intro y hy
    obtain ⟨U, hU, hyU, _⟩ := exists_isGood_subset isOpen_univ (Set.mem_univ y)
    refine Filter.mem_of_superset (hU.1.mem_nhds hyU) fun z hz hzx => ?_
    exact hy (hzx.trans (hU.2.1.joinedIn z hz y hyU).joined)
  have hS_clopen : IsClopen S := ⟨isOpen_compl_iff.mp hSc_open, hS_open⟩
  have hS_ne : S.Nonempty := ⟨x₀, Joined.refl x₀⟩
  have hS_univ : S = Set.univ := hS_clopen.eq_univ hS_ne
  refine ⟨⟨x₀⟩, fun a b => ?_⟩
  have ha : Joined x₀ a := by
    change a ∈ S; rw [hS_univ]; exact Set.mem_univ a
  have hb : Joined x₀ b := by
    change b ∈ S; rw [hS_univ]; exact Set.mem_univ b
  exact ha.symm.trans hb

private noncomputable def seg {M : Type} [TopologicalSpace M] {U : Set M}
    (hU : IsGood U) {a b : M} (ha : a ∈ U) (hb : b ∈ U) :
    Path.Homotopic.Quotient a b :=
  Path.Homotopic.Quotient.mk (hU.2.1.joinedIn a ha b hb).somePath

private lemma seg_eq_mk {M : Type} [TopologicalSpace M] {U : Set M}
    (hU : IsGood U) {a b : M} (ha : a ∈ U) (hb : b ∈ U)
    (γ : Path a b) (hγ : ∀ t, γ t ∈ U) :
    seg hU ha hb = Path.Homotopic.Quotient.mk γ := by
  dsimp [seg]
  rw [Path.Homotopic.Quotient.eq]
  exact hU.2.2 _ γ (fun t => (hU.2.1.joinedIn a ha b hb).somePath_mem t) hγ

private lemma seg_self {M : Type} [TopologicalSpace M] {U : Set M}
    (hU : IsGood U) {a : M} (ha : a ∈ U) :
    seg hU ha ha = Path.Homotopic.Quotient.refl a := by
  rw [← Path.Homotopic.Quotient.mk_refl]
  exact seg_eq_mk hU ha ha (Path.refl a) (fun _ => ha)

private lemma seg_trans {M : Type} [TopologicalSpace M] {U : Set M}
    (hU : IsGood U) {a b c : M} (ha : a ∈ U) (hb : b ∈ U) (hc : c ∈ U) :
    (seg hU ha hb).trans (seg hU hb hc) = seg hU ha hc := by
  let γ₁ := (hU.2.1.joinedIn a ha b hb).somePath
  let γ₂ := (hU.2.1.joinedIn b hb c hc).somePath
  have h1 : ∀ t, γ₁ t ∈ U := fun t => (hU.2.1.joinedIn a ha b hb).somePath_mem t
  have h2 : ∀ t, γ₂ t ∈ U := fun t => (hU.2.1.joinedIn b hb c hc).somePath_mem t
  have h12 : ∀ t, (γ₁.trans γ₂) t ∈ U := by
    intro t
    rw [Path.trans_apply]
    split_ifs
    · exact h1 _
    · exact h2 _
  rw [seg_eq_mk hU ha hb γ₁ h1, seg_eq_mk hU hb hc γ₂ h2,
      ← Path.Homotopic.Quotient.mk_trans, seg_eq_mk hU ha hc (γ₁.trans γ₂) h12]

private lemma seg_subset {M : Type} [TopologicalSpace M] {V U : Set M}
    (hV : IsGood V) (hU : IsGood U) (hVU : V ⊆ U) {a b : M} (ha : a ∈ V) (hb : b ∈ V) :
    seg hV ha hb = seg hU (hVU ha) (hVU hb) := by
  let γ := (hV.2.1.joinedIn a ha b hb).somePath
  have hγ : ∀ t, γ t ∈ V := fun t => (hV.2.1.joinedIn a ha b hb).somePath_mem t
  rw [seg_eq_mk hV ha hb γ hγ, seg_eq_mk hU (hVU ha) (hVU hb) γ (fun t => hVU (hγ t))]

/- ### Universal cover carrier and basis topology -/

private structure UCover (M : Type) [TopologicalSpace M] (x₀ : M) where
  pt : M
  cls : Path.Homotopic.Quotient x₀ pt

private lemma UCover.ext_iff {M : Type} [TopologicalSpace M] {x₀ : M}
    {e₁ e₂ : UCover M x₀} :
    e₁ = e₂ ↔ ∃ h : e₁.pt = e₂.pt, e₁.cls.cast rfl h.symm = e₂.cls := by
  rcases e₁ with ⟨p₁, c₁⟩
  rcases e₂ with ⟨p₂, c₂⟩
  constructor
  · intro h; cases h; exact ⟨rfl, Path.Homotopic.Quotient.cast_rfl_rfl _⟩
  · rintro ⟨hpt, hc⟩
    dsimp at hpt hc
    subst hpt
    rw [Path.Homotopic.Quotient.cast_rfl_rfl] at hc
    subst hc; rfl

private lemma UCover.ext_of_pt_eq {M : Type} [TopologicalSpace M] {x₀ : M}
    {e₁ e₂ : UCover M x₀} (hpt : e₁.pt = e₂.pt)
    (hcls : e₁.cls.cast rfl hpt.symm = e₂.cls) : e₁ = e₂ :=
  UCover.ext_iff.mpr ⟨hpt, hcls⟩

private def sheet {M : Type} [TopologicalSpace M] {x₀ : M}
    (e : UCover M x₀) (U : Set M) (hU : IsGood U) (he : e.pt ∈ U) : Set (UCover M x₀) :=
  {e' | ∃ hy : e'.pt ∈ U, e'.cls = e.cls.trans (seg hU he hy)}

private lemma mem_sheet_self {M : Type} [TopologicalSpace M] {x₀ : M}
    (e : UCover M x₀) {U : Set M} (hU : IsGood U) (he : e.pt ∈ U) :
    e ∈ sheet e U hU he :=
  ⟨he, by rw [seg_self, q_trans_refl]⟩

private lemma sheet_eq_of_mem {M : Type} [TopologicalSpace M] {x₀ : M}
    {e e' : UCover M x₀} {U : Set M} (hU : IsGood U) (he : e.pt ∈ U)
    (he' : e'.pt ∈ U) (hcls' : e'.cls = e.cls.trans (seg hU he he')) :
    sheet e' U hU he' = sheet e U hU he := by
  ext e''
  constructor
  · rintro ⟨he'', hcls''⟩
    refine ⟨he'', ?_⟩
    rw [hcls'', hcls', q_trans_assoc, seg_trans hU he he' he'']
  · rintro ⟨he'', hcls''⟩
    refine ⟨he'', ?_⟩
    rw [hcls'', hcls', q_trans_assoc, seg_trans hU he he' he'']

private lemma sheet_injOn_pt {M : Type} [TopologicalSpace M] {x₀ : M}
    (e : UCover M x₀) {U : Set M} (hU : IsGood U) (he : e.pt ∈ U)
    {e₁ e₂ : UCover M x₀} (h1 : e₁ ∈ sheet e U hU he) (h2 : e₂ ∈ sheet e U hU he)
    (hpt : e₁.pt = e₂.pt) : e₁ = e₂ := by
  rcases e₁ with ⟨x₁, c₁⟩
  rcases e₂ with ⟨x₂, c₂⟩
  dsimp at hpt
  subst hpt
  rcases h1 with ⟨hx, hc1⟩
  rcases h2 with ⟨_, hc2⟩
  dsimp at hc1 hc2
  rw [hc1, hc2]

private lemma sheet_disjoint {M : Type} [TopologicalSpace M] {x₀ : M}
    {e₁ e₂ : UCover M x₀} {U : Set M} (hU : IsGood U) (he₁ : e₁.pt ∈ U) (he₂ : e₂.pt ∈ U)
    (hpt : e₁.pt = e₂.pt) (hne : e₁ ≠ e₂) :
    Disjoint (sheet e₁ U hU he₁) (sheet e₂ U hU he₂) := by
  rw [Set.disjoint_left]
  intro e' h1 h2
  have h1' := sheet_eq_of_mem hU he₁ h1.1 h1.2
  have h2' := sheet_eq_of_mem hU he₂ h2.1 h2.2
  have heq : sheet e₁ U hU he₁ = sheet e₂ U hU he₂ := h1'.symm.trans h2'
  have h2_in_1 : e₂ ∈ sheet e₁ U hU he₁ := heq ▸ mem_sheet_self e₂ hU he₂
  exact hne (sheet_injOn_pt e₁ hU he₁ (mem_sheet_self e₁ hU he₁) h2_in_1 hpt)

private def basisSets (M : Type) [TopologicalSpace M] (x₀ : M) : Set (Set (UCover M x₀)) :=
  {S | ∃ (e : UCover M x₀) (U : Set M) (hU : IsGood U) (he : e.pt ∈ U), S = sheet e U hU he}

private def ucoverTop (M : Type) [TopologicalSpace M] (x₀ : M) :
    TopologicalSpace (UCover M x₀) :=
  TopologicalSpace.generateFrom (basisSets M x₀)

private lemma isTopologicalBasis_basisSets {M : Type} [TopologicalSpace M]
    [ChartedSpace Model3 M] (x₀ : M) :
    @TopologicalSpace.IsTopologicalBasis (UCover M x₀) (ucoverTop M x₀) (basisSets M x₀) := by
  let _ : TopologicalSpace (UCover M x₀) := ucoverTop M x₀
  refine ⟨?_, ?_, rfl⟩
  · rintro _ ⟨e₁, U₁, hU₁, he₁, rfl⟩ _ ⟨e₂, U₂, hU₂, he₂, rfl⟩ e' ⟨h1, h2⟩
    obtain ⟨V, hV, he'V, hVsub⟩ :=
      exists_isGood_subset (hU₁.1.inter hU₂.1) ⟨h1.1, h2.1⟩
    refine ⟨sheet e' V hV he'V, ⟨e', V, hV, he'V, rfl⟩, mem_sheet_self e' hV he'V, ?_⟩
    intro e'' he''
    rcases he'' with ⟨he''V, hcls''⟩
    constructor
    · refine ⟨(hVsub he''V).1, ?_⟩
      rw [hcls'', h1.2, q_trans_assoc,
          seg_subset hV hU₁ (fun z hz => (hVsub hz).1) he'V he''V,
          seg_trans hU₁ he₁ h1.1 (hVsub he''V).1]
    · refine ⟨(hVsub he''V).2, ?_⟩
      rw [hcls'', h2.2, q_trans_assoc,
          seg_subset hV hU₂ (fun z hz => (hVsub hz).2) he'V he''V,
          seg_trans hU₂ he₂ h2.1 (hVsub he''V).2]
  · ext e
    simp only [Set.mem_sUnion, Set.mem_univ, iff_true]
    obtain ⟨U, hU, heU, _⟩ := exists_isGood_subset isOpen_univ (Set.mem_univ e.pt)
    exact ⟨sheet e U hU heU, ⟨e, U, hU, heU, rfl⟩, mem_sheet_self e hU heU⟩

private lemma isOpen_sheet {M : Type} [TopologicalSpace M] [ChartedSpace Model3 M]
    {x₀ : M} (e : UCover M x₀) {U : Set M} (hU : IsGood U) (he : e.pt ∈ U) :
    @IsOpen (UCover M x₀) (ucoverTop M x₀) (sheet e U hU he) := by
  let _ : TopologicalSpace (UCover M x₀) := ucoverTop M x₀
  exact (isTopologicalBasis_basisSets x₀).isOpen ⟨e, U, hU, he, rfl⟩

private lemma continuous_pt {M : Type} [TopologicalSpace M] [ChartedSpace Model3 M]
    (x₀ : M) :
    @Continuous (UCover M x₀) M (ucoverTop M x₀) _ UCover.pt := by
  let _ : TopologicalSpace (UCover M x₀) := ucoverTop M x₀
  rw [continuous_def]
  intro W hW
  rw [isOpen_iff_forall_mem_open]
  intro e heW
  obtain ⟨U, hU, heU, hUW⟩ := exists_isGood_subset hW heW
  exact ⟨sheet e U hU heU, fun e' he' => hUW he'.1, isOpen_sheet e hU heU, mem_sheet_self e hU heU⟩

/- ### Covering map property and finite fibers -/

private lemma isCoveringMap_pt {M : Type} [TopologicalSpace M] [ChartedSpace Model3 M]
    (x₀ : M) :
    @IsCoveringMap (UCover M x₀) M (ucoverTop M x₀) _ UCover.pt := by
  let _ : TopologicalSpace (UCover M x₀) := ucoverTop M x₀
  have hcont : Continuous (UCover.pt : UCover M x₀ → M) := continuous_pt x₀
  intro x
  obtain ⟨U, hU, hxU, _⟩ := exists_isGood_subset isOpen_univ (Set.mem_univ x)
  have hdisc : DiscreteTopology (UCover.pt ⁻¹' {x} : Set (UCover M x₀)) := by
    rw [discreteTopology_iff_isOpen_singleton]
    intro f
    have hfx : f.1.pt = x := f.2
    have hfU : f.1.pt ∈ U := hfx.symm ▸ hxU
    have heq : ({f} : Set (UCover.pt ⁻¹' {x})) =
        Subtype.val ⁻¹' (sheet f.1 U hU hfU) := by
      ext g
      constructor
      · intro hgf
        rw [Set.mem_singleton_iff] at hgf
        rw [hgf]
        exact mem_sheet_self f.1 hU hfU
      · intro hg
        have hgx : g.1.pt = x := g.2
        exact Subtype.ext (sheet_injOn_pt f.1 hU hfU hg (mem_sheet_self f.1 hU hfU)
          (hgx.trans hfx.symm))
    rw [heq]
    exact (isOpen_sheet f.1 hU hfU).preimage continuous_subtype_val
  have hpre_open : IsOpen (UCover.pt ⁻¹' U : Set (UCover M x₀)) := hU.1.preimage hcont
  let toF : (UCover.pt ⁻¹' U : Set (UCover M x₀)) → U × (UCover.pt ⁻¹' {x} : Set (UCover M x₀)) :=
    fun e => (⟨e.1.pt, e.2⟩, ⟨⟨x, e.1.cls.trans (seg hU e.2 hxU)⟩, rfl⟩)
  let invF : U × (UCover.pt ⁻¹' {x} : Set (UCover M x₀)) → (UCover.pt ⁻¹' U : Set (UCover M x₀)) :=
    fun yf => ⟨⟨yf.1.1, yf.2.1.cls.trans (seg hU (yf.2.2.symm ▸ hxU) yf.1.2)⟩, yf.1.2⟩
  have hleft : Function.LeftInverse invF toF := by
    intro e
    apply Subtype.ext
    rcases e with ⟨⟨y, c⟩, hy⟩
    dsimp [invF, toF]
    congr 1
    rw [q_trans_assoc, seg_trans hU hy hxU hy, seg_self hU hy, q_trans_refl]
  have hright : Function.RightInverse invF toF := by
    rintro ⟨⟨y, hy⟩, ⟨⟨z, c⟩, hz⟩⟩
    have hzx : z = x := hz
    subst hzx
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      dsimp [invF, toF]
      congr 1
      rw [q_trans_assoc, seg_trans hU hxU hy hxU, seg_self hU hxU, q_trans_refl]
  have hcont_to : Continuous toF := by
    refine Continuous.prodMk ?_ ?_
    · exact (hcont.comp continuous_subtype_val).subtype_mk _
    · rw [continuous_discrete_rng]
      intro f
      have hfx : f.1.pt = x := f.2
      have hfU : f.1.pt ∈ U := hfx.symm ▸ hxU
      have hpre : (fun e : (UCover.pt ⁻¹' U : Set (UCover M x₀)) => (toF e).2) ⁻¹' {f} =
          Subtype.val ⁻¹' (sheet f.1 U hU hfU) := by
        ext ⟨e, he⟩
        rcases f with ⟨⟨z, cf⟩, hz⟩
        have hzx : z = x := hz
        subst hzx
        constructor
        · intro hEq
          have hcls_eq : e.cls.trans (seg hU he hxU) = cf := by
            have h1 : (⟨z, e.cls.trans (seg hU he hxU)⟩ : UCover M x₀) = ⟨z, cf⟩ :=
              congrArg Subtype.val hEq
            have h2 := (UCover.ext_iff.mp h1).2
            simpa [Path.Homotopic.Quotient.cast_rfl_rfl] using h2
          refine ⟨he, ?_⟩
          have h2 := congrArg (fun r => r.trans (seg hU hxU he)) hcls_eq
          rw [q_trans_assoc, seg_trans hU he hxU he, seg_self hU he, q_trans_refl] at h2
          exact h2
        · rintro ⟨_, hcls_eq⟩
          apply Subtype.ext
          dsimp [toF]
          congr 1
          rw [hcls_eq, q_trans_assoc, seg_trans hU hxU he hxU, seg_self hU hxU, q_trans_refl]
      rw [hpre]
      exact (isOpen_sheet f.1 hU hfU).preimage continuous_subtype_val
  have hcont_inv : Continuous invF := by
    rw [continuous_iff_continuousAt]
    rintro ⟨⟨y, hy⟩, f⟩
    have hfx : f.1.pt = x := f.2
    have hfU : f.1.pt ∈ U := hfx.symm ▸ hxU
    have hcont_slice : Continuous (fun z : U => (invF (z, f)).1) := by
      rw [(isTopologicalBasis_basisSets x₀).continuous_iff]
      rintro _ ⟨e₀, V, hV, he₀V, rfl⟩
      rw [isOpen_iff_forall_mem_open]
      intro z hz
      obtain ⟨W, hW, hzW, hWsub⟩ :=
        exists_isGood_subset (hU.1.inter hV.1) ⟨z.2, hz.1⟩
      refine ⟨Subtype.val ⁻¹' W, ?_, hW.1.preimage continuous_subtype_val, hzW⟩
      intro w hw
      have hwU : w.1 ∈ U := (hWsub hw).1
      have hwV : w.1 ∈ V := (hWsub hw).2
      refine ⟨hwV, ?_⟩
      dsimp [invF]
      have hseg_eq : seg hU hfU hwU = (seg hU hfU z.2).trans (seg hU z.2 hwU) :=
        (seg_trans hU hfU z.2 hwU).symm
      rw [hseg_eq, ← q_trans_assoc]
      have hz_cls : f.1.cls.trans (seg hU hfU z.2) = e₀.cls.trans (seg hV he₀V hz.1) := hz.2
      rw [hz_cls, q_trans_assoc,
          ← seg_subset hW hU (fun a ha => (hWsub ha).1) hzW hw,
          seg_subset hW hV (fun a ha => (hWsub ha).2) hzW hw,
          seg_trans hV he₀V hz.1 hwV]
    have hcont_prod : Continuous (fun p : U × (UCover.pt ⁻¹' {x} : Set (UCover M x₀)) =>
        invF (p.1, f)) :=
      (hcont_slice.comp continuous_fst).subtype_mk _
    have heq_ev : invF =ᶠ[𝓝 ((⟨y, hy⟩ : U), f)] fun p => invF (p.1, f) := by
      have hnb : (Set.univ ×ˢ ({f} : Set (UCover.pt ⁻¹' {x} : Set (UCover M x₀)))) ∈
          𝓝 ((⟨y, hy⟩ : U), f) :=
        prod_mem_nhds Filter.univ_mem ((isOpen_discrete {f}).mem_nhds rfl)
      filter_upwards [hnb] with p hp
      have hp2 : p.2 = f := hp.2
      exact congrArg invF (Prod.ext rfl hp2)
    exact hcont_prod.continuousAt.congr heq_ev.symm
  exact ⟨hdisc, U, hxU, hU.1, hpre_open,
    { toEquiv := ⟨toF, invF, hleft, hright⟩
      continuous_toFun := hcont_to
      continuous_invFun := hcont_inv }, fun _ => rfl⟩

private lemma finite_fiber {M : Type} [TopologicalSpace M] [ConnectedSpace M]
    [ChartedSpace Model3 M] (x₀ : M) (hfin : Finite (FundamentalGroup M x₀)) (x : M) :
    Finite (UCover.pt ⁻¹' {x} : Set (UCover M x₀)) := by
  have hpc : PathConnectedSpace M := pathConnectedSpace_of_charted
  let γ : Path x₀ x := PathConnectedSpace.somePath x₀ x
  let qγ : Path.Homotopic.Quotient x₀ x := Path.Homotopic.Quotient.mk γ
  let e : (UCover.pt ⁻¹' {x} : Set (UCover M x₀)) ≃ FundamentalGroup M x₀ :=
    { toFun := fun f =>
        FundamentalGroup.fromPath ((f.1.cls.cast rfl f.2.symm).trans qγ.symm)
      invFun := fun g =>
        ⟨⟨x, (FundamentalGroup.toPath g).trans qγ⟩, Set.mem_preimage.mpr (Set.mem_singleton x)⟩
      left_inv := fun ⟨⟨y, c⟩, hy⟩ => by
        have hyx : y = x := hy
        subst hyx
        apply Subtype.ext
        dsimp [FundamentalGroup.toPath, FundamentalGroup.fromPath]
        congr 1
        rw [Path.Homotopic.Quotient.cast_rfl_rfl, q_trans_assoc, q_symm_trans, q_trans_refl]
      right_inv := fun g => by
        dsimp [FundamentalGroup.toPath, FundamentalGroup.fromPath]
        rw [Path.Homotopic.Quotient.cast_rfl_rfl, q_trans_assoc, q_trans_symm, q_trans_refl] }
  exact Finite.of_equiv (FundamentalGroup M x₀) e.symm

/- ### Explicit homotopy and path lifting with zero Lebesgue numbers -/

private def prefixPath {M : Type} [TopologicalSpace M] {a : M}
    (F : C(I × I, M)) (hF0 : ∀ u : I, F (u, 0) = a) (u t : I) : Path a (F (u, t)) where
  toFun s := F (u, ⟨(t : ℝ) * (s : ℝ),
    mul_nonneg t.2.1 s.2.1,
    mul_le_one₀ t.2.2 s.2.1 s.2.2⟩)
  continuous_toFun := by
    refine F.continuous.comp (Continuous.prodMk continuous_const ?_)
    exact (continuous_const.mul continuous_subtype_val).subtype_mk _
  source' := by
    have h0 : (⟨(t : ℝ) * ((0 : I) : ℝ), mul_nonneg t.2.1 (0 : I).2.1,
        mul_le_one₀ t.2.2 (0 : I).2.1 (0 : I).2.2⟩ : I) = 0 := Subtype.ext (by simp)
    rw [h0]
    exact hF0 u
  target' := by
    have h1 : (⟨(t : ℝ) * ((1 : I) : ℝ), mul_nonneg t.2.1 (1 : I).2.1,
        mul_le_one₀ t.2.2 (1 : I).2.1 (1 : I).2.2⟩ : I) = t := Subtype.ext (by simp)
    rw [h1]

private noncomputable def liftSquare {M : Type} [TopologicalSpace M] {x₀ : M}
    (e₀ : UCover M x₀) (F : C(I × I, M)) (hF0 : ∀ u : I, F (u, 0) = e₀.pt) :
    I × I → UCover M x₀ :=
  fun p => ⟨F p, e₀.cls.trans (Path.Homotopic.Quotient.mk (prefixPath F hF0 p.1 p.2))⟩

private lemma continuous_liftSquare {M : Type} [TopologicalSpace M] [ChartedSpace Model3 M]
    {x₀ : M} (e₀ : UCover M x₀) (F : C(I × I, M)) (hF0 : ∀ u : I, F (u, 0) = e₀.pt) :
    @Continuous (I × I) (UCover M x₀) _ (ucoverTop M x₀) (liftSquare e₀ F hF0) := by
  let _ : TopologicalSpace (UCover M x₀) := ucoverTop M x₀
  rw [continuous_iff_continuousAt]
  rintro ⟨u₀, t₀⟩
  rw [ContinuousAt, ((isTopologicalBasis_basisSets x₀).nhds_hasBasis).tendsto_right_iff]
  rintro _ ⟨⟨e₁, U, hU, he₁, rfl⟩, hmem⟩
  have hU_mem : F (u₀, t₀) ∈ U := hmem.1
  have hsheet_eq : sheet e₁ U hU he₁ = sheet (liftSquare e₀ F hF0 (u₀, t₀)) U hU hU_mem :=
    (sheet_eq_of_mem hU he₁ hmem.1 hmem.2).symm
  rw [hsheet_eq]
  have hpre_nhds : F ⁻¹' U ∈ 𝓝 (u₀, t₀) := (hU.1.preimage F.continuous).mem_nhds hU_mem
  obtain ⟨δ, hδpos, hball⟩ := Metric.mem_nhds_iff.mp hpre_nhds
  refine Filter.mem_of_superset (Metric.ball_mem_nhds (u₀, t₀) hδpos) ?_
  rintro ⟨u, t⟩ hdist
  have hdist_u : |(u : ℝ) - (u₀ : ℝ)| < δ := by
    have h1 := (Prod.dist_eq (x := (u, t)) (y := (u₀, t₀))).le
    have h2 : dist u u₀ < δ := lt_of_le_of_lt (le_max_left _ _) (Metric.mem_ball.mp hdist)
    simpa [Subtype.dist_eq, Real.dist_eq] using h2
  have hdist_t : |(t : ℝ) - (t₀ : ℝ)| < δ := by
    have h2 : dist t t₀ < δ := lt_of_le_of_lt (le_max_right _ _) (Metric.mem_ball.mp hdist)
    simpa [Subtype.dist_eq, Real.dist_eq] using h2
  have hlin_mem : ∀ s : I,
      ((⟨(1 - (s : ℝ)) * (u₀ : ℝ) + (s : ℝ) * (u : ℝ), by nlinarith [s.2.1, s.2.2, u₀.2.1, u.2.1],
          by nlinarith [s.2.1, s.2.2, u₀.2.2, u.2.2]⟩ : I),
       (⟨(1 - (s : ℝ)) * (t₀ : ℝ) + (s : ℝ) * (t : ℝ), by nlinarith [s.2.1, s.2.2, t₀.2.1, t.2.1],
          by nlinarith [s.2.1, s.2.2, t₀.2.2, t.2.2]⟩ : I)) ∈ Metric.ball (u₀, t₀) δ := by
    intro s
    rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
    constructor
    · show |((1 - (s : ℝ)) * (u₀ : ℝ) + (s : ℝ) * (u : ℝ)) - (u₀ : ℝ)| < δ
      have hrew : (1 - (s : ℝ)) * (u₀ : ℝ) + (s : ℝ) * (u : ℝ) - (u₀ : ℝ) =
          (s : ℝ) * ((u : ℝ) - (u₀ : ℝ)) := by ring
      rw [hrew, abs_mul, abs_of_nonneg s.2.1]
      exact lt_of_le_of_lt (mul_le_of_le_one_left (abs_nonneg _) s.2.2) hdist_u
    · show |((1 - (s : ℝ)) * (t₀ : ℝ) + (s : ℝ) * (t : ℝ)) - (t₀ : ℝ)| < δ
      have hrew : (1 - (s : ℝ)) * (t₀ : ℝ) + (s : ℝ) * (t : ℝ) - (t₀ : ℝ) =
          (s : ℝ) * ((t : ℝ) - (t₀ : ℝ)) := by ring
      rw [hrew, abs_mul, abs_of_nonneg s.2.1]
      exact lt_of_le_of_lt (mul_le_of_le_one_left (abs_nonneg _) s.2.2) hdist_t
  let segPath : Path (F (u₀, t₀)) (F (u, t)) :=
    { toFun := fun s => F
        (⟨(1 - (s : ℝ)) * (u₀ : ℝ) + (s : ℝ) * (u : ℝ), by nlinarith [s.2.1, s.2.2, u₀.2.1, u.2.1],
            by nlinarith [s.2.1, s.2.2, u₀.2.2, u.2.2]⟩,
         ⟨(1 - (s : ℝ)) * (t₀ : ℝ) + (s : ℝ) * (t : ℝ), by nlinarith [s.2.1, s.2.2, t₀.2.1, t.2.1],
            by nlinarith [s.2.1, s.2.2, t₀.2.2, t.2.2]⟩)
      continuous_toFun := F.continuous.comp (Continuous.prodMk
        (Continuous.subtype_mk (by fun_prop) _) (Continuous.subtype_mk (by fun_prop) _))
      source' := by
        congr 1
        exact Prod.ext (Subtype.ext (by simp)) (Subtype.ext (by simp))
      target' := by
        congr 1
        exact Prod.ext (Subtype.ext (by simp)) (Subtype.ext (by simp)) }
  have hsegPath_U : ∀ s : I, segPath s ∈ U := fun s => hball (hlin_mem s)
  have hFut_U : F (u, t) ∈ U := hball hdist
  -- Convex linear homotopy in I × I from prefixPath u t to (prefixPath u₀ t₀).trans segPath
  let q2u : ℝ → ℝ := fun s =>
    if s ≤ 1 / 2 then (u₀ : ℝ) else (1 - (2 * s - 1)) * (u₀ : ℝ) + (2 * s - 1) * (u : ℝ)
  let q2t : ℝ → ℝ := fun s =>
    if s ≤ 1 / 2 then (t₀ : ℝ) * (2 * s) else (1 - (2 * s - 1)) * (t₀ : ℝ) + (2 * s - 1) * (t : ℝ)
  have hq2u_cont : Continuous q2u := by
    refine continuous_if_le continuous_id continuous_const continuousOn_const (by fun_prop) ?_
    intro x hx; rw [hx]; ring
  have hq2t_cont : Continuous q2t := by
    refine continuous_if_le continuous_id continuous_const (by fun_prop) (by fun_prop) ?_
    intro x hx; rw [hx]; ring
  have hq2u_mem : ∀ s : I, q2u (s : ℝ) ∈ I := by
    intro s
    dsimp [q2u]
    split_ifs with hs
    · exact u₀.2
    · exact ⟨by nlinarith [s.2.1, s.2.2, u₀.2.1, u.2.1, hs],
             by nlinarith [s.2.1, s.2.2, u₀.2.2, u.2.2, hs]⟩
  have hq2t_mem : ∀ s : I, q2t (s : ℝ) ∈ I := by
    intro s
    dsimp [q2t]
    split_ifs with hs
    · exact ⟨by nlinarith [s.2.1, t₀.2.1], by nlinarith [s.2.2, t₀.2.1, t₀.2.2, hs]⟩
    · exact ⟨by nlinarith [s.2.1, s.2.2, t₀.2.1, t.2.1, hs],
             by nlinarith [s.2.1, s.2.2, t₀.2.2, t.2.2, hs]⟩
  let H : Path.Homotopy (prefixPath F hF0 u t) ((prefixPath F hF0 u₀ t₀).trans segPath) :=
    { toFun := fun rs => F
        (⟨(1 - (rs.1 : ℝ)) * (u : ℝ) + (rs.1 : ℝ) * q2u (rs.2 : ℝ),
          by
            have hmem := hq2u_mem rs.2
            nlinarith [rs.1.2.1, rs.1.2.2, u.2.1, hmem.1],
          by
            have hmem := hq2u_mem rs.2
            nlinarith [rs.1.2.1, rs.1.2.2, u.2.2, hmem.2]⟩,
         ⟨(1 - (rs.1 : ℝ)) * ((t : ℝ) * (rs.2 : ℝ)) + (rs.1 : ℝ) * q2t (rs.2 : ℝ),
          by
            have hmem := hq2t_mem rs.2
            have hts : 0 ≤ (t : ℝ) * (rs.2 : ℝ) := mul_nonneg t.2.1 rs.2.2.1
            nlinarith [rs.1.2.1, rs.1.2.2, hts, hmem.1],
          by
            have hmem := hq2t_mem rs.2
            have hts : (t : ℝ) * (rs.2 : ℝ) ≤ 1 := mul_le_one₀ t.2.2 rs.2.2.1 rs.2.2.2
            nlinarith [rs.1.2.1, rs.1.2.2, hts, hmem.2]⟩)
      continuous_toFun := by
        refine F.continuous.comp (Continuous.prodMk ?_ ?_)
        · refine Continuous.subtype_mk ?_ _
          have h1 : Continuous (fun rs : I × I => (rs.1 : ℝ)) :=
            continuous_subtype_val.comp continuous_fst
          have h2 : Continuous (fun rs : I × I => q2u (rs.2 : ℝ)) :=
            hq2u_cont.comp (continuous_subtype_val.comp continuous_snd)
          exact ((continuous_const.sub h1).mul continuous_const).add (h1.mul h2)
        · refine Continuous.subtype_mk ?_ _
          have h1 : Continuous (fun rs : I × I => (rs.1 : ℝ)) :=
            continuous_subtype_val.comp continuous_fst
          have h2 : Continuous (fun rs : I × I => (rs.2 : ℝ)) :=
            continuous_subtype_val.comp continuous_snd
          have h3 : Continuous (fun rs : I × I => q2t (rs.2 : ℝ)) :=
            hq2t_cont.comp h2
          exact ((continuous_const.sub h1).mul (continuous_const.mul h2)).add (h1.mul h3)
      map_zero_left := fun s => by
        change F (_, _) = F (u, _)
        congr 1
        exact Prod.ext (Subtype.ext (by simp)) (Subtype.ext (by simp))
      map_one_left := fun s => by
        change F (_, _) = ((prefixPath F hF0 u₀ t₀).trans segPath) s
        rw [Path.trans_apply]
        dsimp [q2u, q2t, prefixPath, segPath]
        split_ifs with hs
        · congr 1
          exact Prod.ext (Subtype.ext (by simp)) (Subtype.ext (by simp))
        · congr 1
          exact Prod.ext (Subtype.ext (by simp)) (Subtype.ext (by simp))
      prop' := fun r s hs => by
        rcases hs with rfl | rfl
        · have h0 : (⟨(1 - (r : ℝ)) * ((t : ℝ) * ((0 : I) : ℝ)) + (r : ℝ) * q2t ((0 : I) : ℝ),
              by
                have hmem := hq2t_mem 0
                have hts : 0 ≤ (t : ℝ) * ((0 : I) : ℝ) := mul_nonneg t.2.1 (0 : I).2.1
                nlinarith [r.2.1, r.2.2, hts, hmem.1],
              by
                have hmem := hq2t_mem 0
                have hts : (t : ℝ) * ((0 : I) : ℝ) ≤ 1 := mul_le_one₀ t.2.2 (0 : I).2.1 (0 : I).2.2
                nlinarith [r.2.1, r.2.2, hts, hmem.2]⟩ : I) = 0 := by
            apply Subtype.ext
            dsimp [q2t]
            rw [if_pos (by norm_num : (0 : ℝ) ≤ 1 / 2)]
            simp
          change F (_, _) = (prefixPath F hF0 u t) 0
          rw [(prefixPath F hF0 u t).source, h0]
          exact hF0 _
        · have h1u : (1 - (r : ℝ)) * (u : ℝ) + (r : ℝ) * q2u ((1 : I) : ℝ) = (u : ℝ) := by
            dsimp [q2u]
            change (1 - (r : ℝ)) * (u : ℝ) + (r : ℝ) *
              (if (1 : ℝ) ≤ 1 / 2 then (u₀ : ℝ)
               else (1 - (2 * 1 - 1)) * (u₀ : ℝ) + (2 * 1 - 1) * (u : ℝ)) = (u : ℝ)
            rw [if_neg (by norm_num : ¬ ((1 : ℝ) ≤ 1 / 2))]
            ring
          have h1t : (1 - (r : ℝ)) * ((t : ℝ) * ((1 : I) : ℝ)) + (r : ℝ) * q2t ((1 : I) : ℝ) =
              (t : ℝ) := by
            dsimp [q2t]
            change (1 - (r : ℝ)) * ((t : ℝ) * 1) + (r : ℝ) *
              (if (1 : ℝ) ≤ 1 / 2 then (t₀ : ℝ) * (2 * 1)
               else (1 - (2 * 1 - 1)) * (t₀ : ℝ) + (2 * 1 - 1) * (t : ℝ)) = (t : ℝ)
            rw [if_neg (by norm_num : ¬ ((1 : ℝ) ≤ 1 / 2))]
            ring
          change F (_, _) = (prefixPath F hF0 u t) 1
          rw [(prefixPath F hF0 u t).target]
          congr 1
          exact Prod.ext (Subtype.ext h1u) (Subtype.ext h1t) }
  have hhom : Path.Homotopic (prefixPath F hF0 u t) ((prefixPath F hF0 u₀ t₀).trans segPath) := ⟨H⟩
  refine ⟨hFut_U, ?_⟩
  dsimp [liftSquare]
  rw [Path.Homotopic.Quotient.eq.mpr hhom, Path.Homotopic.Quotient.mk_trans,
      ← q_trans_assoc, ← seg_eq_mk hU hU_mem hFut_U segPath hsegPath_U]

private lemma q_trans_cast {X : Type*} [TopologicalSpace X] {a b c c' : X}
    (p : Path.Homotopic.Quotient a b) (q : Path.Homotopic.Quotient b c) (hc : c' = c) :
    (p.trans q).cast rfl hc = p.trans (q.cast rfl hc) := by
  subst hc
  simp [Path.Homotopic.Quotient.cast_rfl_rfl]

private lemma liftSquare_zero {M : Type} [TopologicalSpace M] {x₀ : M}
    (e₀ : UCover M x₀) (F : C(I × I, M)) (hF0 : ∀ u : I, F (u, 0) = e₀.pt) (u : I) :
    liftSquare e₀ F hF0 (u, 0) = e₀ := by
  dsimp only [liftSquare]
  apply UCover.ext_of_pt_eq (hF0 u)
  rw [q_trans_cast, ← Path.Homotopic.Quotient.mk_cast]
  have heq : (prefixPath F hF0 u 0).cast rfl (hF0 u).symm = Path.refl e₀.pt := by
    ext s
    change F (u, _) = e₀.pt
    rw [← hF0 u]
    congr 1
    exact Prod.ext rfl (Subtype.ext (by simp))
  rw [heq, Path.Homotopic.Quotient.mk_refl, q_trans_refl]

private noncomputable def liftPath {M : Type} [TopologicalSpace M] [ChartedSpace Model3 M]
    {x₀ : M} (e₀ : UCover M x₀) {b : M} (γ : Path e₀.pt b) :
    @Path (UCover M x₀) (ucoverTop M x₀) e₀ ⟨b, e₀.cls.trans (Path.Homotopic.Quotient.mk γ)⟩ :=
  let F : C(I × I, M) := ⟨fun p => γ p.2, γ.continuous.comp continuous_snd⟩
  let hF0 : ∀ u : I, F (u, 0) = e₀.pt := fun _ => γ.source
  @Path.mk (UCover M x₀) (ucoverTop M x₀) e₀ ⟨b, e₀.cls.trans (Path.Homotopic.Quotient.mk γ)⟩
    (let _ : TopologicalSpace (UCover M x₀) := ucoverTop M x₀
     ⟨fun t => liftSquare e₀ F hF0 (0, t),
      (continuous_liftSquare e₀ F hF0).comp (Continuous.prodMk continuous_const continuous_id)⟩)
    (liftSquare_zero e₀ F hF0 0)
    (by
      dsimp only [liftSquare]
      apply UCover.ext_of_pt_eq γ.target
      rw [q_trans_cast, ← Path.Homotopic.Quotient.mk_cast]
      have heq : (prefixPath F hF0 0 1).cast rfl γ.target.symm = γ := by
        ext s
        dsimp [prefixPath, F]
        congr 1
        exact Subtype.ext (by simp)
      rw [heq])

private lemma liftPath_pt {M : Type} [TopologicalSpace M] [ChartedSpace Model3 M]
    {x₀ : M} (e₀ : UCover M x₀) {b : M} (γ : Path e₀.pt b) (t : I) :
    (liftPath e₀ γ t).pt = γ t := rfl

private lemma lift_unique {M : Type} [TopologicalSpace M] [ChartedSpace Model3 M]
    {x₀ : M} {e₁ e₂ e₂' : UCover M x₀}
    (α : @Path (UCover M x₀) (ucoverTop M x₀) e₁ e₂)
    (β : @Path (UCover M x₀) (ucoverTop M x₀) e₁ e₂')
    (hpt : ∀ t : I, (α t).pt = (β t).pt) :
    ∀ t : I, α t = β t := by
  let _ : TopologicalSpace (UCover M x₀) := ucoverTop M x₀
  let S : Set I := {t : I | α t = β t}
  have hS_open : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    intro t ht
    obtain ⟨U, hU, htU, _⟩ := exists_isGood_subset isOpen_univ (Set.mem_univ (α t).pt)
    have hα_nhds : α ⁻¹' (sheet (α t) U hU htU) ∈ 𝓝 t :=
      ((isOpen_sheet (α t) hU htU).preimage α.continuous).mem_nhds (mem_sheet_self (α t) hU htU)
    have hβ_nhds : β ⁻¹' (sheet (α t) U hU htU) ∈ 𝓝 t :=
      ((isOpen_sheet (α t) hU htU).preimage β.continuous).mem_nhds (by
        show β t ∈ sheet (α t) U hU htU
        rw [← ht]
        exact mem_sheet_self (α t) hU htU)
    filter_upwards [Filter.inter_mem hα_nhds hβ_nhds] with t' ht'
    exact sheet_injOn_pt (α t) hU htU ht'.1 ht'.2 (hpt t')
  have hSc_open : IsOpen Sᶜ := by
    rw [isOpen_iff_mem_nhds]
    intro t ht
    obtain ⟨U, hU, htU, _⟩ := exists_isGood_subset isOpen_univ (Set.mem_univ (α t).pt)
    have htU' : (β t).pt ∈ U := (hpt t) ▸ htU
    have hdisj : Disjoint (sheet (α t) U hU htU) (sheet (β t) U hU htU') :=
      sheet_disjoint hU htU htU' (hpt t) ht
    have hα_nhds : α ⁻¹' (sheet (α t) U hU htU) ∈ 𝓝 t :=
      ((isOpen_sheet (α t) hU htU).preimage α.continuous).mem_nhds (mem_sheet_self (α t) hU htU)
    have hβ_nhds : β ⁻¹' (sheet (β t) U hU htU') ∈ 𝓝 t :=
      ((isOpen_sheet (β t) hU htU').preimage β.continuous).mem_nhds (mem_sheet_self (β t) hU htU')
    filter_upwards [Filter.inter_mem hα_nhds hβ_nhds] with t' ht' heq
    exact Set.disjoint_left.mp hdisj ht'.1 (heq ▸ ht'.2)
  have hS_clopen : IsClopen S := ⟨isOpen_compl_iff.mp hSc_open, hS_open⟩
  have hS_ne : S.Nonempty := ⟨0, by simp [S, α.source, β.source]⟩
  have hS_univ : S = Set.univ := hS_clopen.eq_univ hS_ne
  intro t
  have : t ∈ S := by rw [hS_univ]; exact Set.mem_univ t
  exact this

private lemma pathConnectedSpace_ucover {M : Type} [TopologicalSpace M]
    [ChartedSpace Model3 M] (x₀ : M) :
    @PathConnectedSpace (UCover M x₀) (ucoverTop M x₀) := by
  let _ : TopologicalSpace (UCover M x₀) := ucoverTop M x₀
  let base : UCover M x₀ := ⟨x₀, Path.Homotopic.Quotient.refl x₀⟩
  have hjoin_base : ∀ e : UCover M x₀, Joined base e := by
    rintro ⟨x, c⟩
    obtain ⟨γ, rfl⟩ := Path.Homotopic.Quotient.mk_surjective c
    have hpath := liftPath base γ
    have htarget : (⟨x, base.cls.trans (Path.Homotopic.Quotient.mk γ)⟩ : UCover M x₀) =
        ⟨x, Path.Homotopic.Quotient.mk γ⟩ := by
      congr 1
      exact q_refl_trans _
    exact ⟨hpath.cast rfl htarget.symm⟩
  exact ⟨⟨base⟩, fun e₁ e₂ => (hjoin_base e₁).symm.trans (hjoin_base e₂)⟩

private lemma simplyConnectedSpace_ucover {M : Type} [TopologicalSpace M]
    [ChartedSpace Model3 M] (x₀ : M) :
    @SimplyConnectedSpace (UCover M x₀) (ucoverTop M x₀) := by
  let _ : TopologicalSpace (UCover M x₀) := ucoverTop M x₀
  rw [simply_connected_iff_paths_homotopic]
  refine ⟨pathConnectedSpace_ucover x₀, fun e₁ e₂ => ⟨fun q₁ q₂ => ?_⟩⟩
  obtain ⟨α, rfl⟩ := Path.Homotopic.Quotient.mk_surjective q₁
  obtain ⟨β, rfl⟩ := Path.Homotopic.Quotient.mk_surjective q₂
  rw [Path.Homotopic.Quotient.eq]
  have hcont : Continuous (UCover.pt : UCover M x₀ → M) := continuous_pt x₀
  let pα : Path e₁.pt e₂.pt := α.map hcont
  let pβ : Path e₁.pt e₂.pt := β.map hcont
  have hα_lift : ∀ t : I, α t = liftPath e₁ pα t :=
    lift_unique α (liftPath e₁ pα) (fun _ => rfl)
  have hβ_lift : ∀ t : I, β t = liftPath e₁ pβ t :=
    lift_unique β (liftPath e₁ pβ) (fun _ => rfl)
  have he₂_α : e₂ = ⟨e₂.pt, e₁.cls.trans (Path.Homotopic.Quotient.mk pα)⟩ := by
    have h1 := hα_lift 1
    rw [α.target, (liftPath e₁ pα).target] at h1
    exact h1
  have he₂_β : e₂ = ⟨e₂.pt, e₁.cls.trans (Path.Homotopic.Quotient.mk pβ)⟩ := by
    have h1 := hβ_lift 1
    rw [β.target, (liftPath e₁ pβ).target] at h1
    exact h1
  have hcls_eq : e₁.cls.trans (Path.Homotopic.Quotient.mk pα) =
      e₁.cls.trans (Path.Homotopic.Quotient.mk pβ) := by
    have h1 := he₂_α.symm.trans he₂_β
    exact (UCover.ext_iff.mp h1).2 |> fun hc => by
      simpa [Path.Homotopic.Quotient.cast_rfl_rfl] using hc
  have hhom_base : Path.Homotopic pα pβ :=
    Path.Homotopic.Quotient.eq.mp (q_cancel_left e₁.cls hcls_eq)
  obtain ⟨F⟩ := hhom_base
  have hF0 : ∀ u : I, F.toContinuousMap (u, 0) = e₁.pt := fun u => F.source u
  have hF1 : ∀ u : I, F.toContinuousMap (u, 1) = e₂.pt := fun u => F.target u
  let Ftilde : Path.Homotopy α β :=
    { toFun := liftSquare e₁ F.toContinuousMap hF0
      continuous_toFun := continuous_liftSquare e₁ F.toContinuousMap hF0
      map_zero_left := fun t => by
        let γ0 : Path e₁ (liftSquare e₁ F.toContinuousMap hF0 (0, 1)) :=
          { toFun := fun s => liftSquare e₁ F.toContinuousMap hF0 (0, s)
            continuous_toFun := (continuous_liftSquare e₁ F.toContinuousMap hF0).comp
              (Continuous.prodMk continuous_const continuous_id)
            source' := liftSquare_zero e₁ F.toContinuousMap hF0 0
            target' := rfl }
        exact lift_unique γ0 α (fun s => by
          change F (0, s) = (α s).pt
          exact F.map_zero_left s) t
      map_one_left := fun t => by
        let γ1 : Path e₁ (liftSquare e₁ F.toContinuousMap hF0 (1, 1)) :=
          { toFun := fun s => liftSquare e₁ F.toContinuousMap hF0 (1, s)
            continuous_toFun := (continuous_liftSquare e₁ F.toContinuousMap hF0).comp
              (Continuous.prodMk continuous_const continuous_id)
            source' := liftSquare_zero e₁ F.toContinuousMap hF0 1
            target' := rfl }
        exact lift_unique γ1 β (fun s => by
          change F (1, s) = (β s).pt
          exact F.map_one_left s) t
      prop' := fun u t ht => by
        rcases ht with rfl | rfl
        · exact (liftSquare_zero e₁ F.toContinuousMap hF0 u).trans α.source.symm
        · change liftSquare e₁ F.toContinuousMap hF0 (u, 1) = α 1
          rw [α.target]
          refine Eq.trans ?_ he₂_α.symm
          dsimp only [liftSquare]
          apply UCover.ext_of_pt_eq (hF1 u)
          rw [q_trans_cast, ← Path.Homotopic.Quotient.mk_cast]
          congr 1
          rw [Path.Homotopic.Quotient.eq]
          let G : Path.Homotopy ((prefixPath F.toContinuousMap hF0 u 1).cast rfl (hF1 u).symm) pα :=
            { toFun := fun rs => F (⟨(1 - (rs.1 : ℝ)) * (u : ℝ),
                mul_nonneg (sub_nonneg.mpr rs.1.2.2) u.2.1,
                mul_le_one₀ (sub_le_self 1 rs.1.2.1) u.2.1 u.2.2⟩, rs.2)
              continuous_toFun := F.continuous.comp (Continuous.prodMk
                (Continuous.subtype_mk
                  ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
                    continuous_const) _)
                continuous_snd)
              map_zero_left := fun s => by
                dsimp [prefixPath]
                congr 1
                exact Prod.ext (Subtype.ext (by simp)) (Subtype.ext (by simp))
              map_one_left := fun s => by
                have h0 : (⟨(1 - ((1 : I) : ℝ)) * (u : ℝ),
                    mul_nonneg (sub_nonneg.mpr (1 : I).2.2) u.2.1,
                    mul_le_one₀ (sub_le_self 1 (1 : I).2.1) u.2.1 u.2.2⟩ : I) = 0 :=
                  Subtype.ext (by simp)
                rw [h0]
                exact F.map_zero_left s
              prop' := fun r s hs => by
                rcases hs with rfl | rfl
                · change F (_, 0) = ((prefixPath F.toContinuousMap hF0 u 1).cast rfl (hF1 u).symm) 0
                  rw [Path.source]
                  exact F.source _
                · change F (_, 1) = ((prefixPath F.toContinuousMap hF0 u 1).cast rfl (hF1 u).symm) 1
                  rw [Path.target]
                  exact F.target _ }
          exact ⟨G⟩ }
  exact ⟨Ftilde⟩

end PoincareUniversalCoverProof

theorem OMA.solution : OMA.R_PoincareConjecture_poincare_conjecture_R2_H2_R1.H1 := by
  intro M _ _ _ _ hfin
  obtain ⟨x₀⟩ := (inferInstance : Nonempty M)
  refine ⟨PoincareUniversalCoverProof.UCover M x₀,
    PoincareUniversalCoverProof.ucoverTop M x₀,
    PoincareUniversalCoverProof.simplyConnectedSpace_ucover x₀,
    PoincareUniversalCoverProof.UCover.pt,
    PoincareUniversalCoverProof.isCoveringMap_pt x₀,
    PoincareUniversalCoverProof.finite_fiber x₀ (hfin x₀)⟩
