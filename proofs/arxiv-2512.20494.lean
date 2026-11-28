import OMAStatements.S_arxiv_2512_20494
namespace OMA.P_arxiv_2512_20494

open OMA.S_arxiv_2512_20494

/-! ### Generic digraph / tournament isomorphism helpers -/

private structure TourIso {α β : Type} (R : α → α → Prop) (S : β → β → Prop) where
  toEquiv : α ≃ β
  map_rel : ∀ x y, R x y ↔ S (toEquiv x) (toEquiv y)

private def TourIso.symm {α β : Type} {R : α → α → Prop} {S : β → β → Prop}
    (e : TourIso R S) : TourIso S R where
  toEquiv := e.toEquiv.symm
  map_rel := by
    intro x y
    have h := e.map_rel (e.toEquiv.symm x) (e.toEquiv.symm y)
    simp only [Equiv.apply_symm_apply] at h
    exact h.symm

private def TourIso.trans {α β γ : Type} {R : α → α → Prop} {S : β → β → Prop}
    {U : γ → γ → Prop} (e₁ : TourIso R S) (e₂ : TourIso S U) : TourIso R U where
  toEquiv := e₁.toEquiv.trans e₂.toEquiv
  map_rel := fun x y => (e₁.map_rel x y).trans (e₂.map_rel _ _)

/-- Out-degree of a vertex `x` under a relation `R` on a finite type `α`. -/
private noncomputable def outDegRel {α : Type} [Fintype α] (R : α → α → Prop) (x : α) : ℕ := by
  classical
  exact (Finset.univ.filter (fun y => R x y)).card

private lemma outDegRel_map {α β : Type} [Fintype α] [Fintype β]
    {R : α → α → Prop} {S : β → β → Prop} (e : TourIso R S) (x : α) :
    outDegRel S (e.toEquiv x) = outDegRel R x := by
  classical
  unfold outDegRel
  apply Finset.card_bij (fun y _ => e.toEquiv.symm y)
  · intro y hy
    rw [Finset.mem_filter] at hy ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    exact (e.map_rel x (e.toEquiv.symm y)).mpr (by simpa [Equiv.apply_symm_apply] using hy.2)
  · intro y₁ _ y₂ _ h
    exact e.toEquiv.symm.injective h
  · intro z hz
    rw [Finset.mem_filter] at hz
    refine ⟨e.toEquiv z, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (e.map_rel x z).mp hz.2⟩,
      e.toEquiv.symm_apply_apply z⟩

private lemma count_outDeg_ge_map {α β : Type} [Fintype α] [Fintype β]
    {R : α → α → Prop} {S : β → β → Prop} (e : TourIso R S) (k : ℕ) :
    (Finset.univ.filter (fun y : β => k ≤ outDegRel S y)).card =
      (Finset.univ.filter (fun x : α => k ≤ outDegRel R x)).card := by
  apply Finset.card_bij (fun y _ => e.toEquiv.symm y)
  · intro y hy
    rw [Finset.mem_filter] at hy ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    have := outDegRel_map e (e.toEquiv.symm y)
    simp only [Equiv.apply_symm_apply] at this
    omega
  · intro y₁ _ y₂ _ h
    exact e.toEquiv.symm.injective h
  · intro x hx
    rw [Finset.mem_filter] at hx
    refine ⟨e.toEquiv x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, e.toEquiv.symm_apply_apply x⟩
    rw [outDegRel_map]
    exact hx.2

private lemma count_outDeg_eq_map {α β : Type} [Fintype α] [Fintype β]
    {R : α → α → Prop} {S : β → β → Prop} (e : TourIso R S) (k : ℕ) :
    (Finset.univ.filter (fun y : β => outDegRel S y = k)).card =
      (Finset.univ.filter (fun x : α => outDegRel R x = k)).card := by
  apply Finset.card_bij (fun y _ => e.toEquiv.symm y)
  · intro y hy
    rw [Finset.mem_filter] at hy ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    have := outDegRel_map e (e.toEquiv.symm y)
    simp only [Equiv.apply_symm_apply] at this
    omega
  · intro y₁ _ y₂ _ h
    exact e.toEquiv.symm.injective h
  · intro x hx
    rw [Finset.mem_filter] at hx
    refine ⟨e.toEquiv x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, e.toEquiv.symm_apply_apply x⟩
    rw [outDegRel_map]
    exact hx.2

/-- Polynomial isomorphism invariant for finite tournaments (used to distinguish all
deleted subtournaments of the base cases `n = 6, 7, 8`). -/
private noncomputable def polyInv {α : Type} [Fintype α] (R : α → α → Prop) : ℕ := by
  classical
  exact ∑ u : α,
    let d := outDegRel R u
    let s1 := ∑ w ∈ Finset.univ.filter (fun w => R u w), outDegRel R w
    let s2 := ∑ w ∈ Finset.univ.filter (fun w => R u w), outDegRel R w * outDegRel R w
    (d + 1) * (s1 + 1) * (s2 + 7) + (d + 2) ^ 3

private lemma polyInv_map {α β : Type} [Fintype α] [Fintype β]
    {R : α → α → Prop} {S : β → β → Prop} (e : TourIso R S) :
    polyInv S = polyInv R := by
  classical
  unfold polyInv
  apply Finset.sum_bij (fun y _ => e.toEquiv.symm y)
  · intro _ _; exact Finset.mem_univ _
  · intro y₁ _ y₂ _ h; exact e.toEquiv.symm.injective h
  · intro x _; exact ⟨e.toEquiv x, Finset.mem_univ _, e.toEquiv.symm_apply_apply x⟩
  · intro y _
    dsimp only
    let x := e.toEquiv.symm y
    have hyx : e.toEquiv x = y := e.toEquiv.apply_symm_apply y
    have hd : outDegRel S y = outDegRel R x := by rw [← hyx]; exact outDegRel_map e x
    have hs1 : ∑ w ∈ Finset.univ.filter (fun w => S y w), outDegRel S w =
        ∑ w ∈ Finset.univ.filter (fun w => R x w), outDegRel R w := by
      apply Finset.sum_bij (fun w _ => e.toEquiv.symm w)
      · intro w hw
        rw [Finset.mem_filter] at hw ⊢
        refine ⟨Finset.mem_univ _, (e.map_rel x (e.toEquiv.symm w)).mpr ?_⟩
        simpa [hyx] using hw.2
      · intro w₁ _ w₂ _ h; exact e.toEquiv.symm.injective h
      · intro z hz
        rw [Finset.mem_filter] at hz
        refine ⟨e.toEquiv z, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩,
          e.toEquiv.symm_apply_apply z⟩
        rw [← hyx]; exact (e.map_rel x z).mp hz.2
      · intro w _
        have := outDegRel_map e (e.toEquiv.symm w)
        simpa [Equiv.apply_symm_apply] using this
    have hs2 : ∑ w ∈ Finset.univ.filter (fun w => S y w), outDegRel S w * outDegRel S w =
        ∑ w ∈ Finset.univ.filter (fun w => R x w), outDegRel R w * outDegRel R w := by
      apply Finset.sum_bij (fun w _ => e.toEquiv.symm w)
      · intro w hw
        rw [Finset.mem_filter] at hw ⊢
        refine ⟨Finset.mem_univ _, (e.map_rel x (e.toEquiv.symm w)).mpr ?_⟩
        simpa [hyx] using hw.2
      · intro w₁ _ w₂ _ h; exact e.toEquiv.symm.injective h
      · intro z hz
        rw [Finset.mem_filter] at hz
        refine ⟨e.toEquiv z, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩,
          e.toEquiv.symm_apply_apply z⟩
        rw [← hyx]; exact (e.map_rel x z).mp hz.2
      · intro w _
        have := outDegRel_map e (e.toEquiv.symm w)
        simp only [Equiv.apply_symm_apply] at this
        rw [this]
    rw [hd, hs1, hs2]

/-! ### Part 1: No link-irregular tournament exists for `n ∈ {2, 3, 4, 5}` -/

private lemma fin3_perm_inj :
    ∀ (p0 p1 p2 i j : Fin 3), p0 ≠ p1 → p0 ≠ p2 → p1 ≠ p2 →
    ((if i = p0 then (0 : Fin 3) else if i = p1 then 1 else 2) =
     (if j = p0 then (0 : Fin 3) else if j = p1 then 1 else 2)) → i = j := by
  decide

private lemma fin3_exhaustive :
    ∀ (p0 p1 p2 z : Fin 3), p0 ≠ p1 → p0 ≠ p2 → p1 ≠ p2 →
    z = p0 ∨ z = p1 ∨ z = p2 := by
  decide

private lemma no_linkIrreg_2 (T : Tournament 2) : ¬ IsLinkIrregular T := by
  intro h
  apply h 0 1 (by decide)
  have h1 : ∀ x : {x : Fin 2 // x ≠ 0}, x.1 = 1 := by
    rintro ⟨v, hv⟩; match v with | 0 => exact absurd rfl hv | 1 => rfl
  have h0 : ∀ y : {y : Fin 2 // y ≠ 1}, y.1 = 0 := by
    rintro ⟨v, hv⟩; match v with | 0 => rfl | 1 => exact absurd rfl hv
  refine ⟨⟨fun _ => ⟨0, by decide⟩, fun _ => ⟨1, by decide⟩, ?_, ?_⟩, ?_⟩
  · intro x; exact Subtype.ext (h1 x).symm
  · intro y; exact Subtype.ext (h0 y).symm
  · intro x y; simp [h1 x, h1 y, T.irrefl]

private lemma no_linkIrreg_3 (T : Tournament 3) : ¬ IsLinkIrregular T := by
  intro h
  apply h 0 1 (by decide)
  have hx12 : ∀ x : {x : Fin 3 // x ≠ 0}, x.1 = 1 ∨ x.1 = 2 := by
    rintro ⟨v, hv⟩; match v with | 0 => exact absurd rfl hv | 1 => exact Or.inl rfl | 2 => exact Or.inr rfl
  have hy02 : ∀ y : {y : Fin 3 // y ≠ 1}, y.1 = 0 ∨ y.1 = 2 := by
    rintro ⟨v, hv⟩; match v with | 0 => exact Or.inl rfl | 1 => exact absurd rfl hv | 2 => exact Or.inr rfl
  by_cases h12 : T.adj 1 2
  · have h21 : ¬ T.adj 2 1 := (T.total_asym 1 2 (by decide)).mp h12
    by_cases h02 : T.adj 0 2
    · have h20 : ¬ T.adj 2 0 := (T.total_asym 0 2 (by decide)).mp h02
      refine ⟨⟨fun x => if x.1 = 1 then ⟨0, by decide⟩ else ⟨2, by decide⟩,
        fun y => if y.1 = 0 then ⟨1, by decide⟩ else ⟨2, by decide⟩, ?_, ?_⟩, ?_⟩
      · intro x; apply Subtype.ext; rcases hx12 x with h' | h' <;> simp [h']
      · intro y; apply Subtype.ext; rcases hy02 y with h' | h' <;> simp [h']
      · intro x y
        rcases hx12 x with hx | hx <;> rcases hx12 y with hy | hy <;>
          simp [hx, hy, T.irrefl, h12, h21, h02, h20]
    · have h20 : T.adj 2 0 := (T.total_asym 2 0 (by decide)).mpr h02
      refine ⟨⟨fun x => if x.1 = 1 then ⟨2, by decide⟩ else ⟨0, by decide⟩,
        fun y => if y.1 = 2 then ⟨1, by decide⟩ else ⟨2, by decide⟩, ?_, ?_⟩, ?_⟩
      · intro x; apply Subtype.ext; rcases hx12 x with h' | h' <;> simp [h']
      · intro y; apply Subtype.ext; rcases hy02 y with h' | h' <;> simp [h']
      · intro x y
        rcases hx12 x with hx | hx <;> rcases hx12 y with hy | hy <;>
          simp [hx, hy, T.irrefl, h12, h21, h02, h20]
  · have h21 : T.adj 2 1 := (T.total_asym 2 1 (by decide)).mpr h12
    by_cases h02 : T.adj 0 2
    · have h20 : ¬ T.adj 2 0 := (T.total_asym 0 2 (by decide)).mp h02
      refine ⟨⟨fun x => if x.1 = 1 then ⟨2, by decide⟩ else ⟨0, by decide⟩,
        fun y => if y.1 = 2 then ⟨1, by decide⟩ else ⟨2, by decide⟩, ?_, ?_⟩, ?_⟩
      · intro x; apply Subtype.ext; rcases hx12 x with h' | h' <;> simp [h']
      · intro y; apply Subtype.ext; rcases hy02 y with h' | h' <;> simp [h']
      · intro x y
        rcases hx12 x with hx | hx <;> rcases hx12 y with hy | hy <;>
          simp [hx, hy, T.irrefl, h12, h21, h02, h20]
    · have h20 : T.adj 2 0 := (T.total_asym 2 0 (by decide)).mpr h02
      refine ⟨⟨fun x => if x.1 = 1 then ⟨0, by decide⟩ else ⟨2, by decide⟩,
        fun y => if y.1 = 0 then ⟨1, by decide⟩ else ⟨2, by decide⟩, ?_, ?_⟩, ?_⟩
      · intro x; apply Subtype.ext; rcases hx12 x with h' | h' <;> simp [h']
      · intro y; apply Subtype.ext; rcases hy02 y with h' | h' <;> simp [h']
      · intro x y
        rcases hx12 x with hx | hx <;> rcases hx12 y with hy | hy <;>
          simp [hx, hy, T.irrefl, h12, h21, h02, h20]

/-- Helper: every tournament on `Fin 3` is isomorphic to either transitive `0 → 1 → 2, 0 → 2`
or cyclic `0 → 1 → 2 → 0`, according to whether it has a source (`∃ s, ∀ y ≠ s, R s y`). -/
private def canon3 (hasSrc : Bool) (i j : Fin 3) : Prop :=
  if hasSrc then i.val < j.val
  else (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 0)

private instance (b : Bool) (i j : Fin 3) : Decidable (canon3 b i j) := by
  unfold canon3; infer_instance

private lemma canon3_irrefl (b : Bool) (i : Fin 3) : ¬ canon3 b i i := by
  revert b i; decide

private lemma canon3_tot (b : Bool) (i j : Fin 3) : i ≠ j → (canon3 b i j ↔ ¬ canon3 b j i) := by
  revert b i j; decide

private lemma tour3_iso_canon {α : Type} [Fintype α] [DecidableEq α]
    (hcard : Fintype.card α = 3)
    (R : α → α → Prop)
    (hirr : ∀ x, ¬ R x x)
    (htot : ∀ x y, x ≠ y → (R x y ↔ ¬ R y x)) :
    ∃ b : Bool, Nonempty (TourIso R (canon3 b)) := by
  classical
  let e0 : α ≃ Fin 3 := Fintype.equivFinOfCardEq hcard
  let R' : Fin 3 → Fin 3 → Prop := fun i j => R (e0.symm i) (e0.symm j)
  have hiso0 : TourIso R R' := ⟨e0, by intro x y; simp [R']⟩
  suffices h : ∃ b : Bool, Nonempty (TourIso R' (canon3 b)) by
    rcases h with ⟨b, ⟨e1⟩⟩
    exact ⟨b, ⟨hiso0.trans e1⟩⟩
  have hirr' : ∀ i, ¬ R' i i := fun i => hirr _
  have htot' : ∀ i j, i ≠ j → (R' i j ↔ ¬ R' j i) := fun i j h =>
    htot _ _ (fun heq => h (e0.symm.injective heq))
  -- Exhaust the 8 possible orientations of the 3 edges `(0,1), (0,2), (1,2)`!
  have mkPerm : ∀ (p0 p1 p2 : Fin 3), p0 ≠ p1 → p0 ≠ p2 → p1 ≠ p2 →
      ∃ e : Fin 3 ≃ Fin 3, e p0 = 0 ∧ e p1 = 1 ∧ e p2 = 2 := by
    intro p0 p1 p2 h01 h02 h12
    let f : Fin 3 → Fin 3 := fun i => if i = p0 then 0 else if i = p1 then 1 else 2
    have hinj : Function.Injective f := fun i j hij => fin3_perm_inj p0 p1 p2 i j h01 h02 h12 hij
    exact ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj),
      by simp [f], by simp [f, h01.symm], by simp [f, h02.symm, h12.symm]⟩
  have build : ∀ (b : Bool) (p0 p1 p2 : Fin 3), p0 ≠ p1 → p0 ≠ p2 → p1 ≠ p2 →
      (R' p0 p1 ↔ canon3 b 0 1) → (R' p0 p2 ↔ canon3 b 0 2) → (R' p1 p2 ↔ canon3 b 1 2) →
      Nonempty (TourIso R' (canon3 b)) := by
    intro b p0 p1 p2 h01 h02 h12 hA hB hC
    rcases mkPerm p0 p1 p2 h01 h02 h12 with ⟨e, he0, he1, he2⟩
    refine ⟨⟨e, ?_⟩⟩
    have hcanon_irr : ∀ i, ¬ canon3 b i i := canon3_irrefl b
    have hcanon_tot : ∀ i j, i ≠ j → (canon3 b i j ↔ ¬ canon3 b j i) := canon3_tot b
    intro x y
    have hmem : ∀ z : Fin 3, z = p0 ∨ z = p1 ∨ z = p2 := fun z => fin3_exhaustive p0 p1 p2 z h01 h02 h12
    rcases hmem x with hx | hx | hx <;> rcases hmem y with hy | hy | hy <;> rw [hx, hy]
    · simp [hirr', hcanon_irr]
    · rwa [he0, he1]
    · rwa [he0, he2]
    · rw [he1, he0, htot' p1 p0 h01.symm, hcanon_tot 1 0 (by decide)]; exact not_congr hA
    · simp [hirr', hcanon_irr]
    · rwa [he1, he2]
    · rw [he2, he0, htot' p2 p0 h02.symm, hcanon_tot 2 0 (by decide)]; exact not_congr hB
    · rw [he2, he1, htot' p2 p1 h12.symm, hcanon_tot 2 1 (by decide)]; exact not_congr hC
    · simp [hirr', hcanon_irr]
  by_cases h01 : R' 0 1 <;> by_cases h02 : R' 0 2 <;> by_cases h12 : R' 1 2
  · exact ⟨true, build true 0 1 2 (by decide) (by decide) (by decide)
      (by simp [canon3, h01]) (by simp [canon3, h02]) (by simp [canon3, h12])⟩
  · have h21 : R' 2 1 := (htot' 2 1 (by decide)).mpr h12
    exact ⟨true, build true 0 2 1 (by decide) (by decide) (by decide)
      (by simp [canon3, h02]) (by simp [canon3, h01]) (by simp [canon3, h21])⟩
  · have h20 : R' 2 0 := (htot' 2 0 (by decide)).mpr h02
    exact ⟨false, build false 0 1 2 (by decide) (by decide) (by decide)
      (by simp [canon3, h01]) (by simp [canon3, h02]) (by simp [canon3, h12])⟩
  · have h20 : R' 2 0 := (htot' 2 0 (by decide)).mpr h02
    have h21 : R' 2 1 := (htot' 2 1 (by decide)).mpr h12
    exact ⟨true, build true 2 0 1 (by decide) (by decide) (by decide)
      (by simp [canon3, h20]) (by simp [canon3, h21]) (by simp [canon3, h01])⟩
  · have h10 : R' 1 0 := (htot' 1 0 (by decide)).mpr h01
    exact ⟨true, build true 1 0 2 (by decide) (by decide) (by decide)
      (by simp [canon3, h10]) (by simp [canon3, h12]) (by simp [canon3, h02])⟩
  · have h10 : R' 1 0 := (htot' 1 0 (by decide)).mpr h01
    have h21 : R' 2 1 := (htot' 2 1 (by decide)).mpr h12
    exact ⟨false, build false 0 2 1 (by decide) (by decide) (by decide)
      (by simp [canon3, h02]) (by simp [canon3, h01]) (by simp [canon3, h21])⟩
  · have h10 : R' 1 0 := (htot' 1 0 (by decide)).mpr h01
    have h20 : R' 2 0 := (htot' 2 0 (by decide)).mpr h02
    exact ⟨true, build true 1 2 0 (by decide) (by decide) (by decide)
      (by simp [canon3, h12]) (by simp [canon3, h10]) (by simp [canon3, h20])⟩
  · have h10 : R' 1 0 := (htot' 1 0 (by decide)).mpr h01
    have h20 : R' 2 0 := (htot' 2 0 (by decide)).mpr h02
    have h21 : R' 2 1 := (htot' 2 1 (by decide)).mpr h12
    exact ⟨true, build true 2 1 0 (by decide) (by decide) (by decide)
      (by simp [canon3, h21]) (by simp [canon3, h20]) (by simp [canon3, h10])⟩

private lemma no_linkIrreg_4 (T : Tournament 4) : ¬ IsLinkIrregular T := by
  intro hirr
  have hcls : ∀ v : Fin 4, ∃ b : Bool,
      Nonempty (TourIso (fun x y : {u : Fin 4 // u ≠ v} => T.adj x.1 y.1) (canon3 b)) := by
    intro v
    have hcard : Fintype.card {u : Fin 4 // u ≠ v} = 3 := by
      simp [Fintype.card_subtype_compl]
    exact tour3_iso_canon hcard _ (fun x => T.irrefl x.1)
      (fun x y hxy => T.total_asym x.1 y.1 (fun h => hxy (Subtype.ext h)))
  choose cls hcls_iso using hcls
  have hlt : Fintype.card Bool < Fintype.card (Fin 4) := by decide
  obtain ⟨u, v, huv, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt cls hlt
  rcases hcls_iso u with ⟨eu⟩
  rcases hcls_iso v with ⟨ev⟩
  rw [heq] at eu
  let e := eu.trans ev.symm
  exact hirr u v huv ⟨e.toEquiv, e.map_rel⟩

/-- The 4 isomorphism types of 4-vertex tournaments, indexed by `Fin 4`:
- `0`: transitive (`0 → 1, 0 → 2, 0 → 3, 1 → 2, 1 → 3, 2 → 3`)
- `1`: source `0` beating 3-cycle `1 → 2 → 3 → 1`
- `2`: 3-cycle `0 → 1 → 2 → 0` beating sink `3`
- `3`: strong 4-tournament (`0 → 1, 0 → 2, 1 → 2, 1 → 3, 2 → 3, 3 → 0`) -/
private def canon4 (k : Fin 4) (i j : Fin 4) : Prop :=
  match k with
  | 0 => i.val < j.val
  | 1 => (i = 0 ∧ j ≠ 0) ∨ (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 1)
  | 2 => (i ≠ 3 ∧ j = 3) ∨ (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 0)
  | 3 => (i = 0 ∧ (j = 1 ∨ j = 2)) ∨ (i = 1 ∧ (j = 2 ∨ j = 3)) ∨
         (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 0)

private instance (k i j : Fin 4) : Decidable (canon4 k i j) := by
  unfold canon4; match k with | 0 => infer_instance | 1 => infer_instance | 2 => infer_instance | 3 => infer_instance

private lemma canon4_irrefl (k i : Fin 4) : ¬ canon4 k i i := by
  revert k i; decide

private lemma canon4_tot (k i j : Fin 4) : i ≠ j → (canon4 k i j ↔ ¬ canon4 k j i) := by
  revert k i j; decide

private lemma tour4_iso_canon {α : Type} [Fintype α] [DecidableEq α]
    (hcard : Fintype.card α = 4)
    (R : α → α → Prop)
    (hirr : ∀ x, ¬ R x x)
    (htot : ∀ x y, x ≠ y → (R x y ↔ ¬ R y x)) :
    ∃ k : Fin 4, Nonempty (TourIso R (canon4 k)) := by
  classical
  -- Helper: build an isomorphism `Fin 4 ≃ α` given 4 pairwise distinct elements!
  have mkIso : ∀ (k : Fin 4) (a b c d : α),
      a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
      (R a b ↔ canon4 k 0 1) → (R a c ↔ canon4 k 0 2) → (R a d ↔ canon4 k 0 3) →
      (R b c ↔ canon4 k 1 2) → (R b d ↔ canon4 k 1 3) → (R c d ↔ canon4 k 2 3) →
      Nonempty (TourIso R (canon4 k)) := by
    intro k a b c d hab hac had hbc hbd hcd h01 h02 h03 h12 h13 h23
    let g : Fin 4 → α := ![a, b, c, d]
    have hginj : Function.Injective g := by
      intro i j hij
      match i, j with
      | 0, 0 => rfl | 1, 1 => rfl | 2, 2 => rfl | 3, 3 => rfl
      | 0, 1 => exact absurd hij hab | 0, 2 => exact absurd hij hac | 0, 3 => exact absurd hij had
      | 1, 0 => exact absurd hij hab.symm | 1, 2 => exact absurd hij hbc | 1, 3 => exact absurd hij hbd
      | 2, 0 => exact absurd hij hac.symm | 2, 1 => exact absurd hij hbc.symm | 2, 3 => exact absurd hij hcd
      | 3, 0 => exact absurd hij had.symm | 3, 1 => exact absurd hij hbd.symm | 3, 2 => exact absurd hij hcd.symm
    have hgbij : Function.Bijective g :=
      (Fintype.bijective_iff_injective_and_card g).mpr ⟨hginj, by simp [hcard]⟩
    let eg : Fin 4 ≃ α := Equiv.ofBijective g hgbij
    have hcirr : ∀ i, ¬ canon4 k i i := canon4_irrefl k
    have hctot : ∀ i j, i ≠ j → (canon4 k i j ↔ ¬ canon4 k j i) := canon4_tot k
    have hrel_g : ∀ i j : Fin 4, canon4 k i j ↔ R (eg i) (eg j) := by
      intro i j
      have he0 : eg 0 = a := rfl
      have he1 : eg 1 = b := rfl
      have he2 : eg 2 = c := rfl
      have he3 : eg 3 = d := rfl
      match i, j with
      | 0, 0 => simp [hcirr, hirr]
      | 0, 1 => rw [he0, he1]; exact h01.symm
      | 0, 2 => rw [he0, he2]; exact h02.symm
      | 0, 3 => rw [he0, he3]; exact h03.symm
      | 1, 0 => rw [he1, he0, hctot 1 0 (by decide), htot b a hab.symm]; exact not_congr h01.symm
      | 1, 1 => simp [hcirr, hirr]
      | 1, 2 => rw [he1, he2]; exact h12.symm
      | 1, 3 => rw [he1, he3]; exact h13.symm
      | 2, 0 => rw [he2, he0, hctot 2 0 (by decide), htot c a hac.symm]; exact not_congr h02.symm
      | 2, 1 => rw [he2, he1, hctot 2 1 (by decide), htot c b hbc.symm]; exact not_congr h12.symm
      | 2, 2 => simp [hcirr, hirr]
      | 2, 3 => rw [he2, he3]; exact h23.symm
      | 3, 0 => rw [he3, he0, hctot 3 0 (by decide), htot d a had.symm]; exact not_congr h03.symm
      | 3, 1 => rw [he3, he1, hctot 3 1 (by decide), htot d b hbd.symm]; exact not_congr h13.symm
      | 3, 2 => rw [he3, he2, hctot 3 2 (by decide), htot d c hcd.symm]; exact not_congr h23.symm
      | 3, 3 => simp [hcirr, hirr]
    exact ⟨(TourIso.mk eg hrel_g).symm⟩
  -- Check whether `R` has a source or a sink!
  by_cases hsrc : ∃ s : α, ∀ x : α, x ≠ s → R s x
  · rcases hsrc with ⟨s, hs⟩
    -- Classify the remaining 3 vertices `{x : α // x ≠ s}` via `tour3_iso_canon`!
    have hcard3 : Fintype.card {x : α // x ≠ s} = 3 := by
      rw [Fintype.card_subtype_compl, hcard]; simp
    rcases tour3_iso_canon hcard3 (fun x y : {x : α // x ≠ s} => R x.1 y.1)
      (fun x => hirr x.1) (fun x y hxy => htot x.1 y.1 (fun h => hxy (Subtype.ext h))) with ⟨b3, ⟨e3⟩⟩
    let p1 := (e3.toEquiv.symm 0).1
    let p2 := (e3.toEquiv.symm 1).1
    let p3 := (e3.toEquiv.symm 2).1
    have hp1s : p1 ≠ s := (e3.toEquiv.symm 0).2
    have hp2s : p2 ≠ s := (e3.toEquiv.symm 1).2
    have hp3s : p3 ≠ s := (e3.toEquiv.symm 2).2
    have hp12 : p1 ≠ p2 := fun h => by
      have := e3.toEquiv.symm.injective (Subtype.ext h); exact absurd this (by decide)
    have hp13 : p1 ≠ p3 := fun h => by
      have := e3.toEquiv.symm.injective (Subtype.ext h); exact absurd this (by decide)
    have hp23 : p2 ≠ p3 := fun h => by
      have := e3.toEquiv.symm.injective (Subtype.ext h); exact absurd this (by decide)
    have hr12 : R p1 p2 ↔ canon3 b3 0 1 := by
      have := e3.map_rel (e3.toEquiv.symm 0) (e3.toEquiv.symm 1)
      simpa [p1, p2] using this
    have hr13 : R p1 p3 ↔ canon3 b3 0 2 := by
      have := e3.map_rel (e3.toEquiv.symm 0) (e3.toEquiv.symm 2)
      simpa [p1, p3] using this
    have hr23 : R p2 p3 ↔ canon3 b3 1 2 := by
      have := e3.map_rel (e3.toEquiv.symm 1) (e3.toEquiv.symm 2)
      simpa [p2, p3] using this
    cases b3
    · -- `b3 = false` (3-cycle on remaining 3 vertices) → `canon4 1`!
      refine ⟨1, mkIso 1 s p1 p2 p3 hp1s.symm hp2s.symm hp3s.symm hp12 hp13 hp23 ?_ ?_ ?_ ?_ ?_ ?_⟩
      · exact ⟨fun _ => by simp [canon4], fun _ => hs p1 hp1s⟩
      · exact ⟨fun _ => by simp [canon4], fun _ => hs p2 hp2s⟩
      · exact ⟨fun _ => by simp [canon4], fun _ => hs p3 hp3s⟩
      · rw [hr12]; simp [canon3, canon4]
      · rw [hr13]; simp [canon3, canon4]
      · rw [hr23]; simp [canon3, canon4]
    · -- `b3 = true` (transitive on remaining 3 vertices) → `canon4 0`!
      refine ⟨0, mkIso 0 s p1 p2 p3 hp1s.symm hp2s.symm hp3s.symm hp12 hp13 hp23 ?_ ?_ ?_ ?_ ?_ ?_⟩
      · exact ⟨fun _ => by simp [canon4], fun _ => hs p1 hp1s⟩
      · exact ⟨fun _ => by simp [canon4], fun _ => hs p2 hp2s⟩
      · exact ⟨fun _ => by simp [canon4], fun _ => hs p3 hp3s⟩
      · rw [hr12]; simp [canon3, canon4]
      · rw [hr13]; simp [canon3, canon4]
      · rw [hr23]; simp [canon3, canon4]
  · by_cases hsnk : ∃ t : α, ∀ x : α, x ≠ t → R x t
    · rcases hsnk with ⟨t, ht⟩
      have hcard3 : Fintype.card {x : α // x ≠ t} = 3 := by
        rw [Fintype.card_subtype_compl, hcard]; simp
      rcases tour3_iso_canon hcard3 (fun x y : {x : α // x ≠ t} => R x.1 y.1)
        (fun x => hirr x.1) (fun x y hxy => htot x.1 y.1 (fun h => hxy (Subtype.ext h))) with ⟨b3, ⟨e3⟩⟩
      let p0 := (e3.toEquiv.symm 0).1
      let p1 := (e3.toEquiv.symm 1).1
      let p2 := (e3.toEquiv.symm 2).1
      have hp0t : p0 ≠ t := (e3.toEquiv.symm 0).2
      have hp1t : p1 ≠ t := (e3.toEquiv.symm 1).2
      have hp2t : p2 ≠ t := (e3.toEquiv.symm 2).2
      have hp01 : p0 ≠ p1 := fun h => by
        have := e3.toEquiv.symm.injective (Subtype.ext h); exact absurd this (by decide)
      have hp02 : p0 ≠ p2 := fun h => by
        have := e3.toEquiv.symm.injective (Subtype.ext h); exact absurd this (by decide)
      have hp12 : p1 ≠ p2 := fun h => by
        have := e3.toEquiv.symm.injective (Subtype.ext h); exact absurd this (by decide)
      have hr01 : R p0 p1 ↔ canon3 b3 0 1 := by
        have := e3.map_rel (e3.toEquiv.symm 0) (e3.toEquiv.symm 1)
        simpa [p0, p1] using this
      have hr02 : R p0 p2 ↔ canon3 b3 0 2 := by
        have := e3.map_rel (e3.toEquiv.symm 0) (e3.toEquiv.symm 2)
        simpa [p0, p2] using this
      have hr12 : R p1 p2 ↔ canon3 b3 1 2 := by
        have := e3.map_rel (e3.toEquiv.symm 1) (e3.toEquiv.symm 2)
        simpa [p1, p2] using this
      cases b3
      · -- `b3 = false` (3-cycle beating sink `t`) → `canon4 2`!
        refine ⟨2, mkIso 2 p0 p1 p2 t hp01 hp02 hp0t hp12 hp1t hp2t ?_ ?_ ?_ ?_ ?_ ?_⟩
        · rw [hr01]; simp [canon3, canon4]
        · rw [hr02]; simp [canon3, canon4]
        · exact ⟨fun _ => by simp [canon4], fun _ => ht p0 hp0t⟩
        · rw [hr12]; simp [canon3, canon4]
        · exact ⟨fun _ => by simp [canon4], fun _ => ht p1 hp1t⟩
        · exact ⟨fun _ => by simp [canon4], fun _ => ht p2 hp2t⟩
      · -- `b3 = true`: then `p0` beats `p1, p2, t`, so `p0` is a source, contradicting `hsrc`!
        exfalso
        apply hsrc
        refine ⟨p0, fun x hx => ?_⟩
        by_cases hxt : x = t
        · subst hxt; exact ht p0 hp0t
        · have hx' : e3.toEquiv ⟨x, hxt⟩ ≠ 0 := fun h => hx (by
            have := congrArg (fun z => (e3.toEquiv.symm z).1) h
            simpa [p0] using this)
          have hlt : (0 : Fin 3).val < (e3.toEquiv ⟨x, hxt⟩).val :=
            Nat.pos_of_ne_zero (fun hv => hx' (Fin.ext hv))
          have hc : canon3 true 0 (e3.toEquiv ⟨x, hxt⟩) := hlt
          have := (e3.map_rel (e3.toEquiv.symm 0) ⟨x, hxt⟩).mpr (by simpa using hc)
          simpa [p0] using this
    · -- No source and no sink → every vertex has out-degree 1 or 2, sum = 6, so two of deg 2 and two of deg 1 → `canon4 3`!
      have hd_bounds : ∀ x : α, 1 ≤ outDegRel R x ∧ outDegRel R x ≤ 2 := by
        intro x
        constructor
        · by_contra h0
          have h0' : outDegRel R x = 0 := by omega
          apply hsnk
          refine ⟨x, fun y hy => ?_⟩
          have hnx : ¬ R x y := by
            intro hxy
            have hmem : y ∈ Finset.univ.filter (fun z => R x z) :=
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxy⟩
            have hpos : 0 < outDegRel R x := Finset.card_pos.mpr ⟨y, hmem⟩
            omega
          exact (htot y x hy).mpr hnx
        · by_contra h3
          have hle3 : outDegRel R x ≤ 3 := by
            have hsub : Finset.univ.filter (fun z => R x z) ⊆ Finset.univ.erase x := by
              intro z hz
              rw [Finset.mem_filter] at hz
              exact Finset.mem_erase.mpr ⟨fun h => hirr x (h ▸ hz.2), Finset.mem_univ _⟩
            have hc := Finset.card_le_card hsub
            rw [Finset.card_erase_of_mem (Finset.mem_univ x), Finset.card_univ, hcard] at hc
            exact hc
          have h3' : outDegRel R x = 3 := by omega
          apply hsrc
          refine ⟨x, fun y hy => ?_⟩
          have hsub : Finset.univ.filter (fun z => R x z) ⊆ Finset.univ.erase x := by
            intro z hz
            rw [Finset.mem_filter] at hz
            exact Finset.mem_erase.mpr ⟨fun h => hirr x (h ▸ hz.2), Finset.mem_univ _⟩
          have heq : Finset.univ.filter (fun z => R x z) = Finset.univ.erase x :=
            Finset.eq_of_subset_of_card_le hsub (by
              rw [Finset.card_erase_of_mem (Finset.mem_univ x), Finset.card_univ, hcard]; exact h3'.ge)
          have hmem : y ∈ Finset.univ.filter (fun z => R x z) := by
            rw [heq]; exact Finset.mem_erase.mpr ⟨hy, Finset.mem_univ _⟩
          exact (Finset.mem_filter.mp hmem).2
      -- Sum of out-degrees = 6 (`2 * ∑ outDeg = 4 * 3 = 12`):
      have hsum_deg : ∑ x : α, outDegRel R x = 6 := by
        have h2 : 2 * ∑ x : α, outDegRel R x = 12 := by
          have hpair : ∑ x : α, ∑ y : α, (if R x y then 1 else 0) +
              ∑ x : α, ∑ y : α, (if R y x then 1 else 0) =
              ∑ x : α, ∑ y : α, (if x = y then 0 else 1) := by
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl; intro x _
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl; intro y _
            by_cases hxy : x = y
            · subst hxy; simp [hirr]
            · by_cases hr : R x y
              · have hnr : ¬ R y x := (htot x y hxy).mp hr
                simp [hxy, hr, hnr]
              · have hry : R y x := (htot y x (Ne.symm hxy)).mpr hr
                simp [hxy, hr, hry]
          have hswap : ∑ x : α, ∑ y : α, (if R y x then 1 else 0) =
              ∑ x : α, ∑ y : α, (if R x y then 1 else 0) := Finset.sum_comm
          have hdeg : ∀ x : α, ∑ y : α, (if R x y then 1 else 0) = outDegRel R x := by
            intro x; simp [outDegRel]
          have hrhs : ∑ x : α, ∑ y : α, (if x = y then 0 else 1) = 12 := by
            have hinner : ∀ x : α, ∑ y : α, (if x = y then 0 else 1) = 3 := by
              intro x
              have h1 : ∑ y : α, (if x = y then 0 else 1) =
                  (Finset.univ.filter (fun y => x ≠ y)).card := by
                rw [Finset.card_filter]
                apply Finset.sum_congr rfl; intro y _
                by_cases h : x = y <;> simp [h]
              rw [h1]
              have h2 : Finset.univ.filter (fun y => x ≠ y) = Finset.univ.erase x := by
                ext y; simp [ne_comm]
              rw [h2, Finset.card_erase_of_mem (Finset.mem_univ x), Finset.card_univ, hcard]
            simp [hinner, hcard]
          simp_rw [hswap, hdeg] at hpair
          omega
        omega
      -- Let `D2 = {x | outDeg = 2}` and `D1 = {x | outDeg = 1}`; both have card 2!
      let D2 := Finset.univ.filter (fun x : α => outDegRel R x = 2)
      let D1 := Finset.univ.filter (fun x : α => outDegRel R x = 1)
      have hdisj21 : Disjoint D2 D1 := by
        rw [Finset.disjoint_left]; intro x hx2 hx1
        simp only [D2, D1, Finset.mem_filter] at hx2 hx1; omega
      have hunion21 : D2 ∪ D1 = Finset.univ := by
        ext x
        simp only [D2, D1, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
        have := hd_bounds x; omega
      have htot_card : D2.card + D1.card = 4 := by
        rw [← Finset.card_union_of_disjoint hdisj21, hunion21, Finset.card_univ, hcard]
      have hD2_card : D2.card = 2 := by
        have hsum_split : ∑ x : α, outDegRel R x = 2 * D2.card + 1 * D1.card := by
          rw [← hunion21, Finset.sum_union hdisj21]
          have h2 : ∑ x ∈ D2, outDegRel R x = 2 * D2.card := by
            rw [Finset.sum_congr rfl (fun x hx => (Finset.mem_filter.mp hx).2),
              Finset.sum_const, smul_eq_mul, mul_comm]
          have h1 : ∑ x ∈ D1, outDegRel R x = 1 * D1.card := by
            rw [Finset.sum_congr rfl (fun x hx => (Finset.mem_filter.mp hx).2),
              Finset.sum_const, smul_eq_mul, mul_comm]
          rw [h2, h1]
        omega
      have hD1_card : D1.card = 2 := by omega
      obtain ⟨u, v, huv, hD2eq⟩ := Finset.card_eq_two.mp hD2_card
      obtain ⟨w, z, hwz, hD1eq⟩ := Finset.card_eq_two.mp hD1_card
      -- Order `u, v` so `a → b`!
      have hex_ab : ∃ a b : α, a ≠ b ∧ D2 = {a, b} ∧ R a b := by
        by_cases hr : R u v
        · exact ⟨u, v, huv, hD2eq, hr⟩
        · exact ⟨v, u, huv.symm, by rw [hD2eq, Finset.pair_comm], (htot v u huv.symm).mpr hr⟩
      rcases hex_ab with ⟨a, b, hab, hD2ab, hrab⟩
      have ha_deg : outDegRel R a = 2 := by
        have h : a ∈ D2 := hD2ab ▸ Finset.mem_insert_self a {b}
        exact (Finset.mem_filter.mp h).2
      have hb_deg : outDegRel R b = 2 := by
        have h : b ∈ D2 := hD2ab ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self b)
        exact (Finset.mem_filter.mp h).2
      have hw_deg : outDegRel R w = 1 := by
        have h : w ∈ D1 := hD1eq ▸ Finset.mem_insert_self w {z}
        exact (Finset.mem_filter.mp h).2
      have hz_deg : outDegRel R z = 1 := by
        have h : z ∈ D1 := hD1eq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self z)
        exact (Finset.mem_filter.mp h).2
      have haw : a ≠ w := fun h => by rw [h] at ha_deg; omega
      have haz : a ≠ z := fun h => by rw [h] at ha_deg; omega
      have hbw : b ≠ w := fun h => by rw [h] at hb_deg; omega
      have hbz : b ≠ z := fun h => by rw [h] at hb_deg; omega
      -- `b` loses to `a` and has `outDeg = 2`, so `b` beats both `w` and `z`!
      have hb_sub : Finset.univ.filter (fun x => R b x) ⊆ ({w, z} : Finset α) := by
        intro x hx
        have hbx := (Finset.mem_filter.mp hx).2
        have hxne_b : x ≠ b := fun h => hirr b (h ▸ hbx)
        have hxne_a : x ≠ a := fun h => (htot a b hab).mp hrab (h ▸ hbx)
        have hx_in : x ∈ D2 ∪ D1 := by
          have := hd_bounds x
          simp only [D2, D1, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]; omega
        rw [hD2ab, hD1eq] at hx_in
        simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hx_in
        rcases hx_in with (hxe | hxe) | (hxe | hxe)
        · exact absurd hxe hxne_a
        · exact absurd hxe hxne_b
        · rw [hxe]; exact Finset.mem_insert_self w {z}
        · rw [hxe]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self z)
      have hb_eq : Finset.univ.filter (fun x => R b x) = {w, z} :=
        Finset.eq_of_subset_of_card_le hb_sub (by rw [Finset.card_pair hwz]; exact hb_deg.ge)
      have hrbw : R b w := (Finset.mem_filter.mp (hb_eq ▸ Finset.mem_insert_self w {z})).2
      have hrbz : R b z := (Finset.mem_filter.mp (hb_eq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self z))).2
      -- `a` beats `b` and has `outDeg = 2`, so `a` beats exactly one of `w, z` and loses to the other!
      have hex_cd : ∃ c d : α, c ≠ d ∧ D1 = {c, d} ∧ R a c ∧ ¬ R a d ∧ R b c ∧ R b d := by
        by_cases hraw : R a w
        · have hnaz : ¬ R a z := by
            intro hraz
            have h3 : ({b, w, z} : Finset α) ⊆ Finset.univ.filter (fun x => R a x) := by
              intro x hx
              simp only [Finset.mem_insert, Finset.mem_singleton] at hx
              rcases hx with rfl | rfl | rfl <;>
                exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by assumption⟩
            have hc := Finset.card_le_card h3
            rw [Finset.card_insert_of_notMem (by simp [hbw, hbz]), Finset.card_pair hwz] at hc
            have : outDegRel R a ≥ 3 := hc
            omega
          exact ⟨w, z, hwz, hD1eq, hraw, hnaz, hrbw, hrbz⟩
        · have hraz : R a z := by
            by_contra hnaz
            have hsub : Finset.univ.filter (fun x => R a x) ⊆ ({b} : Finset α) := by
              intro x hx
              have hax := (Finset.mem_filter.mp hx).2
              have hxne_a : x ≠ a := fun h => hirr a (h ▸ hax)
              have hx_in : x ∈ D2 ∪ D1 := by
                have := hd_bounds x
                simp only [D2, D1, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]; omega
              rw [hD2ab, hD1eq] at hx_in
              simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hx_in
              rcases hx_in with (hxe | hxe) | (hxe | hxe)
              · exact absurd hxe hxne_a
              · rw [hxe]; exact Finset.mem_singleton_self b
              · rw [hxe] at hax; exact absurd hax hraw
              · rw [hxe] at hax; exact absurd hax hnaz
            have hc := Finset.card_le_card hsub
            simp only [Finset.card_singleton] at hc
            have : outDegRel R a ≤ 1 := hc
            omega
          exact ⟨z, w, hwz.symm, by rw [hD1eq, Finset.pair_comm], hraz, hraw, hrbz, hrbw⟩
      rcases hex_cd with ⟨c, d, hcd, hD1cd, hrac, hnad, hrbc, hrbd⟩
      have hd_deg : outDegRel R d = 1 := by
        have h : d ∈ D1 := hD1cd ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self d)
        exact (Finset.mem_filter.mp h).2
      have hac : a ≠ c := fun h => hirr a (h ▸ hrac)
      have had : a ≠ d := fun h => by rw [h] at ha_deg; omega
      have hbc : b ≠ c := fun h => hirr b (h ▸ hrbc)
      have hbd : b ≠ d := fun h => hirr b (h ▸ hrbd)
      -- Since `d` beats `a` and `outDeg R d = 1`, `d` loses to `c`, hence `c → d`!
      have hrda : R d a := (htot d a had.symm).mpr hnad
      have hrcd : R c d := by
        apply (htot c d hcd).mpr
        intro hrdc
        have h2 : ({a, c} : Finset α) ⊆ Finset.univ.filter (fun x => R d x) := by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl <;>
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by assumption⟩
        have hc := Finset.card_le_card h2
        rw [Finset.card_pair hac] at hc
        have : outDegRel R d ≥ 2 := hc
        omega
      refine ⟨3, mkIso 3 a b c d hab hac had hbc hbd hcd ?_ ?_ ?_ ?_ ?_ ?_⟩
      · simp [canon4, hrab]
      · simp [canon4, hrac]
      · simp [canon4, hnad]
      · simp [canon4, hrbc]
      · simp [canon4, hrbd]
      · simp [canon4, hrcd]

private lemma no_linkIrreg_5 (T : Tournament 5) : ¬ IsLinkIrregular T := by
  intro hirr
  have hcls : ∀ v : Fin 5, ∃ k : Fin 4,
      Nonempty (TourIso (fun x y : {u : Fin 5 // u ≠ v} => T.adj x.1 y.1) (canon4 k)) := by
    intro v
    have hcard : Fintype.card {u : Fin 5 // u ≠ v} = 4 := by
      simp [Fintype.card_subtype_compl]
    exact tour4_iso_canon hcard _ (fun x => T.irrefl x.1)
      (fun x y hxy => T.total_asym x.1 y.1 (fun h => hxy (Subtype.ext h)))
  choose cls hcls_iso using hcls
  have hlt : Fintype.card (Fin 4) < Fintype.card (Fin 5) := by decide
  obtain ⟨u, v, huv, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt cls hlt
  rcases hcls_iso u with ⟨eu⟩
  rcases hcls_iso v with ⟨ev⟩
  rw [heq] at eu
  let e := eu.trans ev.symm
  exact hirr u v huv ⟨e.toEquiv, e.map_rel⟩

/-! ### Part 2: Base link-irregular tournaments for `n = 6, 7, 8` with `outDeg ≤ n - 2` -/

private def bitAdj {n : ℕ} (rows : Fin n → ℕ) (i j : Fin n) : Bool :=
  Nat.testBit (rows i) j.val

private def mkBitTour {n : ℕ} (rows : Fin n → ℕ)
    (hirr : ∀ i : Fin n, bitAdj rows i i = false)
    (htot : ∀ i j : Fin n, i ≠ j → bitAdj rows i j = !bitAdj rows j i) : Tournament n where
  adj i j := bitAdj rows i j = true
  irrefl i := by simp [hirr i]
  total_asym i j hij := by
    have h := htot i j hij
    cases hji : bitAdj rows j i <;> simp [h, hji]

/-- Computable polynomial invariant matching `polyInv` on `T - v` for decidable `bitAdj`. -/
private def delDeg {n : ℕ} (rows : Fin n → ℕ) (v u : Fin n) : ℕ :=
  (Finset.univ.filter (fun w : Fin n => w ≠ v ∧ bitAdj rows u w = true)).card

private def delPolyInv {n : ℕ} (rows : Fin n → ℕ) (v : Fin n) : ℕ :=
  ∑ u ∈ Finset.univ.filter (fun u : Fin n => u ≠ v),
    let d := delDeg rows v u
    let s1 := ∑ w ∈ Finset.univ.filter (fun w : Fin n => w ≠ v ∧ bitAdj rows u w = true),
      delDeg rows v w
    let s2 := ∑ w ∈ Finset.univ.filter (fun w : Fin n => w ≠ v ∧ bitAdj rows u w = true),
      delDeg rows v w * delDeg rows v w
    (d + 1) * (s1 + 1) * (s2 + 7) + (d + 2) ^ 3

private lemma delDeg_eq_outDegRel {n : ℕ} (rows : Fin n → ℕ)
    (hirr : ∀ i, bitAdj rows i i = false)
    (htot : ∀ i j, i ≠ j → bitAdj rows i j = !bitAdj rows j i)
    (v : Fin n) (x : {u : Fin n // u ≠ v}) :
    outDegRel (fun a b : {u : Fin n // u ≠ v} => (mkBitTour rows hirr htot).adj a.1 b.1) x =
      delDeg rows v x.1 := by
  classical
  unfold outDegRel delDeg
  apply Finset.card_bij (fun y _ => y.1)
  · intro y hy
    rw [Finset.mem_filter] at hy ⊢
    exact ⟨Finset.mem_univ _, y.2, hy.2⟩
  · intro y₁ _ y₂ _ h; exact Subtype.ext h
  · intro w hw
    rw [Finset.mem_filter] at hw
    exact ⟨⟨w, hw.2.1⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw.2.2⟩, rfl⟩

private lemma polyInv_eq_delPolyInv {n : ℕ} (rows : Fin n → ℕ)
    (hirr : ∀ i, bitAdj rows i i = false)
    (htot : ∀ i j, i ≠ j → bitAdj rows i j = !bitAdj rows j i)
    (v : Fin n) :
    polyInv (fun a b : {u : Fin n // u ≠ v} => (mkBitTour rows hirr htot).adj a.1 b.1) =
      delPolyInv rows v := by
  classical
  unfold polyInv delPolyInv
  apply Finset.sum_bij (fun x _ => x.1)
  · intro x _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, x.2⟩
  · intro x₁ _ x₂ _ h; exact Subtype.ext h
  · intro u hu; exact ⟨⟨u, (Finset.mem_filter.mp hu).2⟩, Finset.mem_univ _, rfl⟩
  · intro x _
    dsimp only
    have hd := delDeg_eq_outDegRel rows hirr htot v x
    have hs1 : ∑ w ∈ Finset.univ.filter (fun w : {u : Fin n // u ≠ v} =>
          (mkBitTour rows hirr htot).adj x.1 w.1),
          outDegRel (fun a b : {u : Fin n // u ≠ v} => (mkBitTour rows hirr htot).adj a.1 b.1) w =
        ∑ w ∈ Finset.univ.filter (fun w : Fin n => w ≠ v ∧ bitAdj rows x.1 w = true),
          delDeg rows v w := by
      apply Finset.sum_bij (fun y _ => y.1)
      · intro y hy
        rw [Finset.mem_filter] at hy ⊢
        exact ⟨Finset.mem_univ _, y.2, hy.2⟩
      · intro y₁ _ y₂ _ h; exact Subtype.ext h
      · intro w hw
        rw [Finset.mem_filter] at hw
        exact ⟨⟨w, hw.2.1⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw.2.2⟩, rfl⟩
      · intro y _; exact delDeg_eq_outDegRel rows hirr htot v y
    have hs2 : ∑ w ∈ Finset.univ.filter (fun w : {u : Fin n // u ≠ v} =>
          (mkBitTour rows hirr htot).adj x.1 w.1),
          outDegRel (fun a b : {u : Fin n // u ≠ v} => (mkBitTour rows hirr htot).adj a.1 b.1) w *
          outDegRel (fun a b : {u : Fin n // u ≠ v} => (mkBitTour rows hirr htot).adj a.1 b.1) w =
        ∑ w ∈ Finset.univ.filter (fun w : Fin n => w ≠ v ∧ bitAdj rows x.1 w = true),
          delDeg rows v w * delDeg rows v w := by
      apply Finset.sum_bij (fun y _ => y.1)
      · intro y hy
        rw [Finset.mem_filter] at hy ⊢
        exact ⟨Finset.mem_univ _, y.2, hy.2⟩
      · intro y₁ _ y₂ _ h; exact Subtype.ext h
      · intro w hw
        rw [Finset.mem_filter] at hw
        exact ⟨⟨w, hw.2.1⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw.2.2⟩, rfl⟩
      · intro y _
        have := delDeg_eq_outDegRel rows hirr htot v y
        rw [this]
    rw [hd, hs1, hs2]

private lemma linkIrreg_of_delPolyInv {n : ℕ} (rows : Fin n → ℕ)
    (hirr : ∀ i, bitAdj rows i i = false)
    (htot : ∀ i j, i ≠ j → bitAdj rows i j = !bitAdj rows j i)
    (hinv : ∀ u v : Fin n, u ≠ v → delPolyInv rows u ≠ delPolyInv rows v) :
    IsLinkIrregular (mkBitTour rows hirr htot) := by
  intro u v huv ⟨e, he⟩
  let iso : TourIso
      (fun a b : {x : Fin n // x ≠ u} => (mkBitTour rows hirr htot).adj a.1 b.1)
      (fun a b : {x : Fin n // x ≠ v} => (mkBitTour rows hirr htot).adj a.1 b.1) := ⟨e, he⟩
  have hmap := polyInv_map iso
  rw [polyInv_eq_delPolyInv, polyInv_eq_delPolyInv] at hmap
  exact hinv u v huv hmap.symm

private lemma outDeg_mkBitTour_le {n : ℕ} (rows : Fin n → ℕ)
    (hirr : ∀ i, bitAdj rows i i = false)
    (htot : ∀ i j, i ≠ j → bitAdj rows i j = !bitAdj rows j i)
    (hdeg : ∀ u : Fin n, (Finset.univ.filter (fun w : Fin n => bitAdj rows u w = true)).card ≤ n - 2) :
    ∀ u : Fin n, outDegRel (mkBitTour rows hirr htot).adj u ≤ n - 2 := by
  intro u
  classical
  unfold outDegRel
  have heq : Finset.univ.filter (fun y : Fin n => (mkBitTour rows hirr htot).adj u y) =
      Finset.univ.filter (fun w : Fin n => bitAdj rows u w = true) := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rfl
  rw [heq]
  exact hdeg u

private def rows6 : Fin 6 → ℕ := ![24, 33, 43, 34, 14, 17]
private def rows7 : Fin 7 → ℕ := ![80, 105, 83, 117, 66, 21, 32]
private def rows8 : Fin 8 → ℕ := ![108, 69, 128, 22, 135, 222, 28, 75]

private lemma base6_exists :
    ∃ T : Tournament 6, IsLinkIrregular T ∧ ∀ u : Fin 6, outDegRel T.adj u ≤ 4 :=
  ⟨mkBitTour rows6 (by decide) (by decide),
   linkIrreg_of_delPolyInv rows6 (by decide) (by decide) (by decide),
   outDeg_mkBitTour_le rows6 (by decide) (by decide) (by decide)⟩

private lemma base7_exists :
    ∃ T : Tournament 7, IsLinkIrregular T ∧ ∀ u : Fin 7, outDegRel T.adj u ≤ 5 :=
  ⟨mkBitTour rows7 (by decide) (by decide),
   linkIrreg_of_delPolyInv rows7 (by decide) (by decide) (by decide),
   outDeg_mkBitTour_le rows7 (by decide) (by decide) (by decide)⟩

private lemma base8_exists :
    ∃ T : Tournament 8, IsLinkIrregular T ∧ ∀ u : Fin 8, outDegRel T.adj u ≤ 6 :=
  ⟨mkBitTour rows8 (by decide) (by decide),
   linkIrreg_of_delPolyInv rows8 (by decide) (by decide) (by decide),
   outDeg_mkBitTour_le rows8 (by decide) (by decide) (by decide)⟩

/-! ### Part 3: The 3-vertex inductive step `n → n + 3` -/

private lemma exists_low_outDeg {n : ℕ} (hn : 6 ≤ n) (T : Tournament n) :
    ∃ x : Fin n, outDegRel T.adj x ≤ n - 3 := by
  classical
  by_contra hall
  push Not at hall
  have hsum_lb : n * (n - 2) ≤ ∑ u : Fin n, outDegRel T.adj u := by
    calc n * (n - 2)
        = ∑ _u : Fin n, (n - 2) := by simp
      _ ≤ ∑ u : Fin n, outDegRel T.adj u := Finset.sum_le_sum (fun u _ => by have := hall u; omega)
  have h2sum : 2 * ∑ u : Fin n, outDegRel T.adj u = n * (n - 1) := by
    have hpair : ∑ u : Fin n, ∑ v : Fin n, (if T.adj u v then 1 else 0) +
        ∑ u : Fin n, ∑ v : Fin n, (if T.adj v u then 1 else 0) =
        ∑ u : Fin n, ∑ v : Fin n, (if u = v then 0 else 1) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro u _
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro v _
      by_cases huv : u = v
      · subst huv; simp [T.irrefl]
      · by_cases hr : T.adj u v
        · have hnr : ¬ T.adj v u := (T.total_asym u v huv).mp hr
          simp [huv, hr, hnr]
        · have hrv : T.adj v u := (T.total_asym v u (Ne.symm huv)).mpr hr
          simp [huv, hr, hrv]
    have hswap : ∑ u : Fin n, ∑ v : Fin n, (if T.adj v u then 1 else 0) =
        ∑ u : Fin n, ∑ v : Fin n, (if T.adj u v then 1 else 0) := Finset.sum_comm
    have hdeg : ∀ u : Fin n, ∑ v : Fin n, (if T.adj u v then 1 else 0) = outDegRel T.adj u := by
      intro u; simp [outDegRel]
    have hrhs : ∑ u : Fin n, ∑ v : Fin n, (if u = v then 0 else 1) = n * (n - 1) := by
      have hinner : ∀ u : Fin n, ∑ v : Fin n, (if u = v then 0 else 1) = n - 1 := by
        intro u
        have h1 : ∑ v : Fin n, (if u = v then 0 else 1) =
            (Finset.univ.filter (fun v : Fin n => u ≠ v)).card := by
          rw [Finset.card_filter]
          apply Finset.sum_congr rfl; intro v _
          by_cases h : u = v <;> simp [h]
        rw [h1]
        have h2 : Finset.univ.filter (fun v : Fin n => u ≠ v) = Finset.univ.erase u := by
          ext v; simp [ne_comm]
        rw [h2, Finset.card_erase_of_mem (Finset.mem_univ u), Finset.card_univ, Fintype.card_fin]
      simp [hinner]
    simp_rw [hswap, hdeg] at hpair
    omega
  have hm1 : 2 * (n * (n - 2)) ≤ n * (n - 1) := by omega
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 6 := ⟨n - 6, by omega⟩
  have hk1 : (k + 6) - 2 = k + 4 := by omega
  have hk2 : (k + 6) - 1 = k + 5 := by omega
  rw [hk1, hk2] at hm1
  nlinarith

/-- Given a tournament `T` on `n` vertices and a chosen vertex `x0 : Fin n`, form `T'` on
`n + 3` vertices by adding a 3-cycle `a → b → c → a` (`a = n, b = n + 1, c = n + 2`) on top
of `T`, where `a, b` beat all of `T`, and `c` beats all of `T \ {x0}` while `x0 → c`. -/
private def liftAdj {n : ℕ} (T : Tournament n) (x0 : Fin n) (i j : Fin (n + 3)) : Prop :=
  if hi : i.val < n then
    if hj : j.val < n then T.adj ⟨i.val, hi⟩ ⟨j.val, hj⟩
    else i.val = x0.val ∧ j.val = n + 2
  else
    if j.val < n then
      i.val = n ∨ i.val = n + 1 ∨ (i.val = n + 2 ∧ j.val ≠ x0.val)
    else
      (i.val = n ∧ j.val = n + 1) ∨ (i.val = n + 1 ∧ j.val = n + 2) ∨ (i.val = n + 2 ∧ j.val = n)

private def liftTour {n : ℕ} (T : Tournament n) (x0 : Fin n) : Tournament (n + 3) where
  adj := liftAdj T x0
  irrefl i := by
    unfold liftAdj
    by_cases hi : i.val < n
    · simp [hi, T.irrefl]
    · simp [hi]; omega
  total_asym i j hij := by
    have hval : i.val ≠ j.val := fun h => hij (Fin.ext h)
    unfold liftAdj
    by_cases hi : i.val < n
    · by_cases hj : j.val < n
      · simp only [hi, hj, ↓reduceDIte]
        exact T.total_asym ⟨i.val, hi⟩ ⟨j.val, hj⟩ (fun h => hval (congrArg (Fin.val : Fin n → ℕ) h))
      · simp only [hi, hj, ↓reduceDIte]
        have hj' : j.val = n ∨ j.val = n + 1 ∨ j.val = n + 2 := by omega
        rcases hj' with h1 | h1 | h1 <;> simp [h1]
    · by_cases hj : j.val < n
      · simp only [hi, hj, ↓reduceDIte]
        have hi' : i.val = n ∨ i.val = n + 1 ∨ i.val = n + 2 := by omega
        rcases hi' with h1 | h1 | h1 <;> simp [h1]
      · simp only [hi, hj, ↓reduceDIte]
        have hi' : i.val = n ∨ i.val = n + 1 ∨ i.val = n + 2 := by omega
        have hj' : j.val = n ∨ j.val = n + 1 ∨ j.val = n + 2 := by omega
        rcases hi' with h1 | h1 | h1 <;> rcases hj' with h2 | h2 | h2 <;> simp_all

private lemma step3 {n : ℕ} (hn : 6 ≤ n) (T : Tournament n)
    (hirr : IsLinkIrregular T) (hmax : ∀ u : Fin n, outDegRel T.adj u ≤ n - 2) :
    ∃ T' : Tournament (n + 3), IsLinkIrregular T' ∧ ∀ u : Fin (n + 3), outDegRel T'.adj u ≤ n + 1 := by
  classical
  obtain ⟨x0, hx0⟩ := exists_low_outDeg hn T
  let T' := liftTour T x0
  let va : Fin (n + 3) := ⟨n, by omega⟩
  let vb : Fin (n + 3) := ⟨n + 1, by omega⟩
  let vc : Fin (n + 3) := ⟨n + 2, by omega⟩
  -- Helper: out-degree of any `i < n` in `T'` is `≤ n - 2`!
  have hdeg_old : ∀ i : Fin (n + 3), i.val < n → outDegRel T'.adj i ≤ n - 2 := by
    intro i hi
    let iu : Fin n := ⟨i.val, hi⟩
    by_cases hix : i.val = x0.val
    · -- `i = x0`: out-neighbors are `T`-out-neighbors plus `vc`!
      have hcard_eq : outDegRel T'.adj i = outDegRel T.adj x0 + 1 := by
        unfold outDegRel
        have hvc_mem : vc ∈ Finset.univ.filter (fun j : Fin (n + 3) => T'.adj i j) := by
          rw [Finset.mem_filter]
          refine ⟨Finset.mem_univ _, ?_⟩
          change liftAdj T x0 i vc
          unfold liftAdj
          simp [vc, hix]
        rw [← Finset.card_erase_add_one hvc_mem]
        congr 1
        apply Finset.card_bij (fun j hj => ⟨j.val, by
          rw [Finset.mem_erase, Finset.mem_filter] at hj
          have hadj : liftAdj T x0 i j := hj.2.2
          unfold liftAdj at hadj
          by_cases hjn : j.val < n
          · exact hjn
          · simp only [hi, hjn, ↓reduceDIte] at hadj
            exact absurd (Fin.ext hadj.2) hj.1⟩)
        · intro j hj
          rw [Finset.mem_erase, Finset.mem_filter] at hj
          have hadj : liftAdj T x0 i j := hj.2.2
          unfold liftAdj at hadj
          have hjn : j.val < n := by
            by_contra hjn
            simp only [hi, hjn, ↓reduceDIte] at hadj
            exact hj.1 (Fin.ext hadj.2)
          simp only [hi, hjn, ↓reduceDIte] at hadj
          rw [Finset.mem_filter]
          refine ⟨Finset.mem_univ _, ?_⟩
          have hieq : (⟨i.val, hi⟩ : Fin n) = x0 := Fin.ext hix
          exact hieq ▸ hadj
        · intro j₁ _ j₂ _ h; exact Fin.ext (congrArg (Fin.val : Fin n → ℕ) h)
        · intro w hw
          rw [Finset.mem_filter] at hw
          refine ⟨⟨w.val, by omega⟩, ?_, Fin.ext rfl⟩
          rw [Finset.mem_erase, Finset.mem_filter]
          refine ⟨fun h => by have := congrArg Fin.val h; dsimp [vc] at this; omega,
            Finset.mem_univ _, ?_⟩
          change liftAdj T x0 i ⟨w.val, by omega⟩
          unfold liftAdj
          have hieq : (⟨i.val, hi⟩ : Fin n) = x0 := Fin.ext hix
          simp only [hi, w.isLt, ↓reduceDIte, hieq]
          exact hw.2
      omega
    · -- `i ≠ x0`: out-neighbors are purely inside `T`!
      have hcard_eq : outDegRel T'.adj i = outDegRel T.adj iu := by
        unfold outDegRel
        apply Finset.card_bij (fun j hj => ⟨j.val, by
          rw [Finset.mem_filter] at hj
          have hadj : liftAdj T x0 i j := hj.2
          unfold liftAdj at hadj
          by_cases hjn : j.val < n
          · exact hjn
          · simp only [hi, hjn, ↓reduceDIte] at hadj
            exact absurd hadj.1 hix⟩)
        · intro j hj
          rw [Finset.mem_filter] at hj
          have hadj : liftAdj T x0 i j := hj.2
          unfold liftAdj at hadj
          have hjn : j.val < n := by
            by_contra hjn
            simp only [hi, hjn, ↓reduceDIte] at hadj
            exact hix hadj.1
          simp only [hi, hjn, ↓reduceDIte] at hadj
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hadj⟩
        · intro j₁ _ j₂ _ h; exact Fin.ext (congrArg (Fin.val : Fin n → ℕ) h)
        · intro w hw
          rw [Finset.mem_filter] at hw
          refine ⟨⟨w.val, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, Fin.ext rfl⟩
          change liftAdj T x0 i ⟨w.val, by omega⟩
          unfold liftAdj
          simp only [hi, w.isLt, ↓reduceDIte]
          exact hw.2
      rw [hcard_eq]
      exact hmax iu
  -- Out-degrees of `va, vb, vc` in `T'`: all `≤ n + 1`!
  have hmax' : ∀ u : Fin (n + 3), outDegRel T'.adj u ≤ n + 1 := by
    intro u
    by_cases hu : u.val < n
    · have := hdeg_old u hu; omega
    · -- Any `u ≥ n` loses to at least one of `{va, vb, vc}` and is irreflexive, so `outDeg ≤ n + 1`!
      let loser : Fin (n + 3) := if u = va then vc else if u = vb then va else vb
      have hlu : loser ≠ u := by
        dsimp [loser]
        split_ifs with h1 h2
        · intro h; rw [h1] at h; have := congrArg Fin.val h; dsimp [va, vc] at this; omega
        · intro h; rw [h2] at h; have := congrArg Fin.val h; dsimp [va, vb] at this; omega
        · intro h; have huc : u = vc := Fin.ext (by
            have h1' : u.val ≠ n := fun hv => h1 (Fin.ext hv)
            have h2' : u.val ≠ n + 1 := fun hv => h2 (Fin.ext hv)
            dsimp [vc]; omega)
          rw [huc] at h; have := congrArg Fin.val h; dsimp [vb, vc] at this; omega
      have hnl : ¬ T'.adj u loser := by
        change ¬ liftAdj T x0 u loser
        unfold liftAdj
        have hl_n : ¬ loser.val < n := by
          dsimp [loser]; split_ifs <;> dsimp [va, vb, vc] <;> omega
        simp only [hu, hl_n, ↓reduceDIte]
        have hu' : u = va ∨ u = vb ∨ u = vc := by
          by_cases h1 : u.val = n
          · exact Or.inl (Fin.ext h1)
          · by_cases h2 : u.val = n + 1
            · exact Or.inr (Or.inl (Fin.ext h2))
            · exact Or.inr (Or.inr (Fin.ext (by dsimp [vc]; omega)))
        rcases hu' with rfl | rfl | rfl <;>
          simp [loser, va, vb, vc]
      have hsub : Finset.univ.filter (fun j : Fin (n + 3) => T'.adj u j) ⊆
          (Finset.univ.erase u).erase loser := by
        intro j hj
        rw [Finset.mem_filter] at hj
        rw [Finset.mem_erase, Finset.mem_erase]
        refine ⟨fun h => hnl (h ▸ hj.2), fun h => T'.irrefl u (h ▸ hj.2), Finset.mem_univ _⟩
      have hc := Finset.card_le_card hsub
      rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hlu, Finset.mem_univ _⟩),
          Finset.card_erase_of_mem (Finset.mem_univ u), Finset.card_univ, Fintype.card_fin] at hc
      exact hc
  -- Helper: compute out-degree in `T' - v` for any `x ≠ v`!
  let delRel (v : Fin (n + 3)) : {u : Fin (n + 3) // u ≠ v} → {u : Fin (n + 3) // u ≠ v} → Prop :=
    fun a b => T'.adj a.1 b.1
  have hdel_le : ∀ (v : Fin (n + 3)) (x : {u : Fin (n + 3) // u ≠ v}),
      outDegRel (delRel v) x ≤ outDegRel T'.adj x.1 := by
    intro v x
    unfold outDegRel
    apply Finset.card_le_card_of_injOn Subtype.val
    · intro y hy
      rw [Finset.mem_coe, Finset.mem_filter] at hy ⊢
      exact ⟨Finset.mem_univ _, hy.2⟩
    · intro y₁ _ y₂ _ h; exact Subtype.ext h
  -- Exact out-degree of `x` in `T' - v` via explicit target set on `Fin (n + 3)`:
  have hdel_card : ∀ (v : Fin (n + 3)) (x : {u : Fin (n + 3) // u ≠ v}),
      outDegRel (delRel v) x =
        (Finset.univ.filter (fun w : Fin (n + 3) => w ≠ v ∧ T'.adj x.1 w)).card := by
    intro v x
    unfold outDegRel
    apply Finset.card_bij (fun y _ => y.1)
    · intro y hy
      rw [Finset.mem_filter] at hy ⊢
      exact ⟨Finset.mem_univ _, y.2, hy.2⟩
    · intro y₁ _ y₂ _ h; exact Subtype.ext h
    · intro w hw
      rw [Finset.mem_filter] at hw
      exact ⟨⟨w, hw.2.1⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw.2.2⟩, rfl⟩
  -- Exact out-degrees of `va, vb, vc` in `T' - v` for every `v`!
  have hdeg_va_in : ∀ (v : Fin (n + 3)) (hv : va ≠ v),
      outDegRel (delRel v) ⟨va, hv⟩ = if v = vc then n + 1 else n := by
    intro v hv
    rw [hdel_card]
    have hset : Finset.univ.filter (fun w : Fin (n + 3) => w ≠ v ∧ T'.adj va w) =
        ((Finset.univ.erase va).erase vc).erase v := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, and_true]
      change (w ≠ v ∧ liftAdj T x0 va w) ↔ (w ≠ v ∧ w ≠ vc ∧ w ≠ va)
      unfold liftAdj
      have hva_n : ¬ va.val < n := by dsimp [va]; omega
      simp only [hva_n, ↓reduceDIte]
      by_cases hwn : w.val < n
      · simp only [hwn]
        constructor
        · rintro ⟨hwv, _⟩
          exact ⟨hwv, fun h => by have := congrArg Fin.val h; dsimp [vc] at this; omega,
            fun h => by have := congrArg Fin.val h; dsimp [va] at this; omega⟩
        · rintro ⟨hwv, _, _⟩; exact ⟨hwv, Or.inl rfl⟩
      · simp only [hwn]
        constructor
        · rintro ⟨hwv, h⟩
          have hw1 : w.val = n + 1 := by
            rcases h with ⟨_, h2⟩ | ⟨h1, _⟩ | ⟨h1, _⟩
            · exact h2
            · change n = n + 1 at h1; omega
            · change n = n + 2 at h1; omega
          exact ⟨hwv, fun h' => by have := congrArg Fin.val h'; dsimp [vc] at this; omega,
            fun h' => by have := congrArg Fin.val h'; dsimp [va] at this; omega⟩
        · rintro ⟨hwv, hwc, hwa⟩
          have hwc' : w.val ≠ n + 2 := fun h => hwc (Fin.ext h)
          have hwa' : w.val ≠ n := fun h => hwa (Fin.ext h)
          exact ⟨hwv, Or.inl ⟨rfl, by omega⟩⟩
    rw [hset]
    have hca : vc ≠ va := fun h => by have := congrArg Fin.val h; dsimp [va, vc] at this; omega
    by_cases hvc : v = vc
    · subst hvc
      rw [if_pos rfl, Finset.erase_idem,
          Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hca, Finset.mem_univ _⟩),
          Finset.card_erase_of_mem (Finset.mem_univ va), Finset.card_univ, Fintype.card_fin]
      omega
    · rw [if_neg hvc,
          Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hvc, Finset.mem_erase.mpr ⟨hv.symm, Finset.mem_univ _⟩⟩),
          Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hca, Finset.mem_univ _⟩),
          Finset.card_erase_of_mem (Finset.mem_univ va), Finset.card_univ, Fintype.card_fin]
      omega
  have hdeg_vb_in : ∀ (v : Fin (n + 3)) (hv : vb ≠ v),
      outDegRel (delRel v) ⟨vb, hv⟩ = if v = va then n + 1 else n := by
    intro v hv
    rw [hdel_card]
    have hset : Finset.univ.filter (fun w : Fin (n + 3) => w ≠ v ∧ T'.adj vb w) =
        ((Finset.univ.erase vb).erase va).erase v := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, and_true]
      change (w ≠ v ∧ liftAdj T x0 vb w) ↔ (w ≠ v ∧ w ≠ va ∧ w ≠ vb)
      unfold liftAdj
      have hvb_n : ¬ vb.val < n := by dsimp [vb]; omega
      simp only [hvb_n, ↓reduceDIte]
      by_cases hwn : w.val < n
      · simp only [hwn]
        constructor
        · rintro ⟨hwv, _⟩
          exact ⟨hwv, fun h => by have := congrArg Fin.val h; dsimp [va] at this; omega,
            fun h => by have := congrArg Fin.val h; dsimp [vb] at this; omega⟩
        · rintro ⟨hwv, _, _⟩; exact ⟨hwv, Or.inr (Or.inl rfl)⟩
      · simp only [hwn]
        constructor
        · rintro ⟨hwv, h⟩
          have hw2 : w.val = n + 2 := by
            rcases h with ⟨h1, _⟩ | ⟨_, h2⟩ | ⟨h1, _⟩
            · change n + 1 = n at h1; omega
            · exact h2
            · change n + 1 = n + 2 at h1; omega
          exact ⟨hwv, fun h' => by have := congrArg Fin.val h'; dsimp [va] at this; omega,
            fun h' => by have := congrArg Fin.val h'; dsimp [vb] at this; omega⟩
        · rintro ⟨hwv, hwa, hwb⟩
          have hwa' : w.val ≠ n := fun h => hwa (Fin.ext h)
          have hwb' : w.val ≠ n + 1 := fun h => hwb (Fin.ext h)
          exact ⟨hwv, Or.inr (Or.inl ⟨rfl, by omega⟩)⟩
    rw [hset]
    have hab : va ≠ vb := fun h => by have := congrArg Fin.val h; dsimp [va, vb] at this; omega
    by_cases hva : v = va
    · subst hva
      rw [if_pos rfl, Finset.erase_idem,
          Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hab, Finset.mem_univ _⟩),
          Finset.card_erase_of_mem (Finset.mem_univ vb), Finset.card_univ, Fintype.card_fin]
      omega
    · rw [if_neg hva,
          Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hva, Finset.mem_erase.mpr ⟨hv.symm, Finset.mem_univ _⟩⟩),
          Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hab, Finset.mem_univ _⟩),
          Finset.card_erase_of_mem (Finset.mem_univ vb), Finset.card_univ, Fintype.card_fin]
      omega
  let vx0 : Fin (n + 3) := ⟨x0.val, by omega⟩
  have hdeg_vc_in : ∀ (v : Fin (n + 3)) (hv : vc ≠ v),
      outDegRel (delRel v) ⟨vc, hv⟩ = if (v = vb ∨ v = vx0) then n else n - 1 := by
    intro v hv
    rw [hdel_card]
    have hset : Finset.univ.filter (fun w : Fin (n + 3) => w ≠ v ∧ T'.adj vc w) =
        (((Finset.univ.erase vc).erase vb).erase vx0).erase v := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, and_true]
      change (w ≠ v ∧ liftAdj T x0 vc w) ↔ (w ≠ v ∧ w ≠ vx0 ∧ w ≠ vb ∧ w ≠ vc)
      unfold liftAdj
      have hvc_n : ¬ vc.val < n := by dsimp [vc]; omega
      simp only [hvc_n, ↓reduceDIte]
      by_cases hwn : w.val < n
      · simp only [hwn]
        constructor
        · rintro ⟨hwv, h⟩
          have hwx : w.val ≠ x0.val := by
            rcases h with h1 | h1 | ⟨_, h2⟩
            · change n + 2 = n at h1; omega
            · change n + 2 = n + 1 at h1; omega
            · exact h2
          exact ⟨hwv, fun h' => hwx (by have := congrArg Fin.val h'; dsimp [vx0] at this; exact this),
            fun h' => by have := congrArg Fin.val h'; dsimp [vb] at this; omega,
            fun h' => by have := congrArg Fin.val h'; dsimp [vc] at this; omega⟩
        · rintro ⟨hwv, hwx, _, _⟩
          exact ⟨hwv, Or.inr (Or.inr ⟨rfl, fun h => hwx (Fin.ext h)⟩)⟩
      · simp only [hwn]
        constructor
        · rintro ⟨hwv, h⟩
          have hw0 : w.val = n := by
            rcases h with ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨_, h2⟩
            · change n + 2 = n at h1; omega
            · change n + 2 = n + 1 at h1; omega
            · exact h2
          exact ⟨hwv, fun h' => by have := congrArg Fin.val h'; dsimp [vx0] at this; omega,
            fun h' => by have := congrArg Fin.val h'; dsimp [vb] at this; omega,
            fun h' => by have := congrArg Fin.val h'; dsimp [vc] at this; omega⟩
        · rintro ⟨hwv, _, hwb, hwc⟩
          have hwb' : w.val ≠ n + 1 := fun h => hwb (Fin.ext h)
          have hwc' : w.val ≠ n + 2 := fun h => hwc (Fin.ext h)
          exact ⟨hwv, Or.inr (Or.inr ⟨rfl, by omega⟩)⟩
    rw [hset]
    have hbc : vb ≠ vc := fun h => by have := congrArg Fin.val h; dsimp [vb, vc] at this; omega
    have hxc : vx0 ≠ vc := fun h => by have := congrArg Fin.val h; dsimp [vx0, vc] at this; omega
    have hxb : vx0 ≠ vb := fun h => by have := congrArg Fin.val h; dsimp [vx0, vb] at this; omega
    by_cases hvbx : v = vb ∨ v = vx0
    · rw [if_pos hvbx]
      rcases hvbx with rfl | rfl
      · have : (((Finset.univ.erase vc).erase vb).erase vx0).erase vb =
            ((Finset.univ.erase vc).erase vb).erase vx0 := by
          ext w; simp only [Finset.mem_erase]; tauto
        rw [this,
            Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hxb, Finset.mem_erase.mpr ⟨hxc, Finset.mem_univ _⟩⟩),
            Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hbc, Finset.mem_univ _⟩),
            Finset.card_erase_of_mem (Finset.mem_univ vc), Finset.card_univ, Fintype.card_fin]
        omega
      · rw [Finset.erase_idem,
            Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hxb, Finset.mem_erase.mpr ⟨hxc, Finset.mem_univ _⟩⟩),
            Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hbc, Finset.mem_univ _⟩),
            Finset.card_erase_of_mem (Finset.mem_univ vc), Finset.card_univ, Fintype.card_fin]
        omega
    · rw [if_neg hvbx]
      push Not at hvbx
      rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hvbx.2,
            Finset.mem_erase.mpr ⟨hvbx.1, Finset.mem_erase.mpr ⟨hv.symm, Finset.mem_univ _⟩⟩⟩),
          Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hxb, Finset.mem_erase.mpr ⟨hxc, Finset.mem_univ _⟩⟩),
          Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hbc, Finset.mem_univ _⟩),
          Finset.card_erase_of_mem (Finset.mem_univ vc), Finset.card_univ, Fintype.card_fin]
      omega
  -- Now prove `IsLinkIrregular T'`!
  refine ⟨T', ?_, hmax'⟩
  intro u v huv ⟨e, he⟩
  let iso : TourIso (delRel u) (delRel v) := ⟨e, he⟩
  -- Compute high-degree count (`outDeg ≥ n - 1`) for `u` and `v`!
  have hhigh_iff : ∀ (w : Fin (n + 3)) (x : {y : Fin (n + 3) // y ≠ w}),
      n - 1 ≤ outDegRel (delRel w) x ↔ n ≤ x.1.val := by
    intro w x
    constructor
    · intro hge
      by_contra hlt
      push Not at hlt
      have h1 := hdel_le w x
      have h2 := hdeg_old x.1 hlt
      omega
    · intro hge
      have hx_cases : x.1 = va ∨ x.1 = vb ∨ x.1 = vc := by
        by_cases h1 : x.1.val = n
        · exact Or.inl (Fin.ext h1)
        · by_cases h2 : x.1.val = n + 1
          · exact Or.inr (Or.inl (Fin.ext h2))
          · exact Or.inr (Or.inr (Fin.ext (by dsimp [vc]; omega)))
      rcases hx_cases with hxa | hxb | hxc
      · have hval := hdeg_va_in w (hxa ▸ x.2)
        have hxeq : x = ⟨va, hxa ▸ x.2⟩ := Subtype.ext hxa
        rw [hxeq, hval]; split_ifs <;> omega
      · have hval := hdeg_vb_in w (hxb ▸ x.2)
        have hxeq : x = ⟨vb, hxb ▸ x.2⟩ := Subtype.ext hxb
        rw [hxeq, hval]; split_ifs <;> omega
      · have hval := hdeg_vc_in w (hxc ▸ x.2)
        have hxeq : x = ⟨vc, hxc ▸ x.2⟩ := Subtype.ext hxc
        rw [hxeq, hval]; split_ifs <;> omega
  have hhigh_count : ∀ w : Fin (n + 3),
      (Finset.univ.filter (fun x : {y : Fin (n + 3) // y ≠ w} => n - 1 ≤ outDegRel (delRel w) x)).card =
      if w.val < n then 3 else 2 := by
    intro w
    have hfilt : Finset.univ.filter (fun x : {y : Fin (n + 3) // y ≠ w} => n - 1 ≤ outDegRel (delRel w) x) =
        Finset.univ.filter (fun x : {y : Fin (n + 3) // y ≠ w} => n ≤ x.1.val) := by
      ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hhigh_iff w x
    rw [hfilt]
    have hbij : (Finset.univ.filter (fun x : {y : Fin (n + 3) // y ≠ w} => n ≤ x.1.val)).card =
        (({va, vb, vc} : Finset (Fin (n + 3))).erase w).card := by
      apply Finset.card_bij (fun x _ => x.1)
      · intro x hx
        rw [Finset.mem_filter] at hx
        rw [Finset.mem_erase]
        refine ⟨x.2, ?_⟩
        simp only [Finset.mem_insert, Finset.mem_singleton]
        by_cases h1 : x.1.val = n
        · exact Or.inl (Fin.ext h1)
        · by_cases h2 : x.1.val = n + 1
          · exact Or.inr (Or.inl (Fin.ext h2))
          · exact Or.inr (Or.inr (Fin.ext (by dsimp [vc]; omega)))
      · intro x₁ _ x₂ _ h; exact Subtype.ext h
      · intro y hy
        rw [Finset.mem_erase] at hy
        refine ⟨⟨y, hy.1⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
        simp only [Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy.2 with rfl | rfl | rfl <;> dsimp [va, vb, vc] <;> omega
    rw [hbij]
    have hab : va ≠ vb := fun h => by have := congrArg Fin.val h; dsimp [va, vb] at this; omega
    have hac : va ≠ vc := fun h => by have := congrArg Fin.val h; dsimp [va, vc] at this; omega
    have hbc : vb ≠ vc := fun h => by have := congrArg Fin.val h; dsimp [vb, vc] at this; omega
    have hcard3 : ({va, vb, vc} : Finset (Fin (n + 3))).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [hab, hac]), Finset.card_pair hbc]
    by_cases hw : w.val < n
    · rw [if_pos hw]
      have hnot : w ∉ ({va, vb, vc} : Finset (Fin (n + 3))) := by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨fun h => by rw [h] at hw; dsimp [va] at hw; omega,
               fun h => by rw [h] at hw; dsimp [vb] at hw; omega,
               fun h => by rw [h] at hw; dsimp [vc] at hw; omega⟩
      rw [Finset.erase_eq_of_notMem hnot, hcard3]
    · rw [if_neg hw]
      have hmem : w ∈ ({va, vb, vc} : Finset (Fin (n + 3))) := by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        by_cases h1 : w.val = n
        · exact Or.inl (Fin.ext h1)
        · by_cases h2 : w.val = n + 1
          · exact Or.inr (Or.inl (Fin.ext h2))
          · exact Or.inr (Or.inr (Fin.ext (by dsimp [vc]; omega)))
      rw [Finset.card_erase_of_mem hmem, hcard3]
  have hcount_eq := count_outDeg_ge_map iso (n - 1)
  rw [hhigh_count u, hhigh_count v] at hcount_eq
  by_cases hu : u.val < n
  · have hv : v.val < n := by
      by_contra hv; simp [hu, hv] at hcount_eq
    -- Both `u, v < n`! `e` preserves `{x | n ≤ x.val}`, hence restricts to `{x < n | x ≠ u} ≃ {y < n | y ≠ v}`!
    have he_old : ∀ x : {y : Fin (n + 3) // y ≠ u}, x.1.val < n → (e x).1.val < n := by
      intro x hx
      by_contra hge
      push Not at hge
      have h1 : n - 1 ≤ outDegRel (delRel v) (e x) := (hhigh_iff v (e x)).mpr hge
      rw [outDegRel_map iso x] at h1
      have h2 := (hhigh_iff u x).mp h1
      omega
    have he_symm_old : ∀ y : {z : Fin (n + 3) // z ≠ v}, y.1.val < n → (e.symm y).1.val < n := by
      intro y hy
      by_contra hge
      push Not at hge
      have h1 : n - 1 ≤ outDegRel (delRel u) (e.symm y) := (hhigh_iff u (e.symm y)).mpr hge
      have h2 := outDegRel_map iso (e.symm y)
      simp only [iso, Equiv.apply_symm_apply] at h2
      have h3 : n - 1 ≤ outDegRel (delRel v) y := h2 ▸ h1
      have h4 := (hhigh_iff v y).mp h3
      omega
    let u0 : Fin n := ⟨u.val, hu⟩
    let v0 : Fin n := ⟨v.val, hv⟩
    have huv0 : u0 ≠ v0 := fun h => huv (Fin.ext (congrArg (Fin.val : Fin n → ℕ) h))
    let embU : {x : Fin n // x ≠ u0} → {y : Fin (n + 3) // y ≠ u} :=
      fun x => ⟨⟨x.1.val, by omega⟩, fun h => x.2 (Fin.ext (congrArg (Fin.val : Fin (n + 3) → ℕ) h))⟩
    let embV : {y : Fin n // y ≠ v0} → {z : Fin (n + 3) // z ≠ v} :=
      fun y => ⟨⟨y.1.val, by omega⟩, fun h => y.2 (Fin.ext (congrArg (Fin.val : Fin (n + 3) → ℕ) h))⟩
    apply hirr u0 v0 huv0
    refine ⟨⟨
      fun x =>
        let y := e (embU x)
        ⟨⟨y.1.val, he_old _ x.1.isLt⟩, fun h => y.2 (Fin.ext (congrArg (Fin.val : Fin n → ℕ) h))⟩,
      fun y =>
        let x := e.symm (embV y)
        ⟨⟨x.1.val, he_symm_old _ y.1.isLt⟩, fun h => x.2 (Fin.ext (congrArg (Fin.val : Fin n → ℕ) h))⟩,
      ?_, ?_⟩, ?_⟩
    · intro x
      apply Subtype.ext; apply Fin.ext
      dsimp only [embV]
      have heqV : (⟨⟨(e (embU x)).1.val, by omega⟩,
          fun h => (e (embU x)).2 (Fin.ext (congrArg (Fin.val : Fin (n + 3) → ℕ) h))⟩ :
          {z : Fin (n + 3) // z ≠ v}) = e (embU x) := by
        apply Subtype.ext; apply Fin.ext; rfl
      have hstep : e.symm (e (embU x)) = embU x := e.symm_apply_apply (embU x)
      rw [heqV, hstep]
    · intro y
      apply Subtype.ext; apply Fin.ext
      dsimp only [embU]
      have heqU : (⟨⟨(e.symm (embV y)).1.val, by omega⟩,
          fun h => (e.symm (embV y)).2 (Fin.ext (congrArg (Fin.val : Fin (n + 3) → ℕ) h))⟩ :
          {z : Fin (n + 3) // z ≠ u}) = e.symm (embV y) := by
        apply Subtype.ext; apply Fin.ext; rfl
      have hstep : e (e.symm (embV y)) = embV y := e.apply_symm_apply (embV y)
      rw [heqU, hstep]
    · intro x y
      have h := he (embU x) (embU y)
      change liftAdj T x0 (embU x).1 (embU y).1 ↔ liftAdj T x0 (e (embU x)).1 (e (embU y)).1 at h
      unfold liftAdj at h
      have hx' : (e (embU x)).1.val < n := he_old _ x.1.isLt
      have hy' : (e (embU y)).1.val < n := he_old _ y.1.isLt
      simp only [embU, x.1.isLt, y.1.isLt, hx', hy', ↓reduceDIte, Fin.eta] at h
      exact h
  · have hv : ¬ v.val < n := by
      intro hv; simp [hu, hv] at hcount_eq
    -- Both `u, v ∈ {va, vb, vc}`! Distinguish them by the count of vertices of out-degree `n` (`0`, `2`, `1`)!
    have hdegN_count : ∀ w : Fin (n + 3), ¬ w.val < n →
        (Finset.univ.filter (fun x : {y : Fin (n + 3) // y ≠ w} => outDegRel (delRel w) x = n)).card =
        if w = va then 0 else if w = vb then 2 else 1 := by
      intro w hw
      have hab : va ≠ vb := fun h => by have := congrArg Fin.val h; dsimp [va, vb] at this; omega
      have hac : va ≠ vc := fun h => by have := congrArg Fin.val h; dsimp [va, vc] at this; omega
      have hbc : vb ≠ vc := fun h => by have := congrArg Fin.val h; dsimp [vb, vc] at this; omega
      have h_old_ne : ∀ x : {y : Fin (n + 3) // y ≠ w}, x.1.val < n → outDegRel (delRel w) x ≠ n := by
        intro x hx; have h1 := hdel_le w x; have h2 := hdeg_old x.1 hx; omega
      have hw_cases : w = va ∨ w = vb ∨ w = vc := by
        by_cases h1 : w.val = n
        · exact Or.inl (Fin.ext h1)
        · by_cases h2 : w.val = n + 1
          · exact Or.inr (Or.inl (Fin.ext h2))
          · exact Or.inr (Or.inr (Fin.ext (by dsimp [vc]; omega)))
      rcases hw_cases with rfl | rfl | rfl
      · rw [if_pos rfl]
        apply Finset.card_eq_zero.mpr
        rw [Finset.filter_eq_empty_iff]
        intro x _
        by_cases hxn : x.1.val < n
        · exact h_old_ne x hxn
        · by_cases hxb : x.1 = vb
          · have hxeq : x = ⟨vb, hab.symm⟩ := Subtype.ext hxb
            rw [hxeq, hdeg_vb_in va hab.symm]; simp
          · have hxc : x.1 = vc := Fin.ext (by
              have hxa : x.1.val ≠ n := fun h => x.2 (Fin.ext h)
              have hxb' : x.1.val ≠ n + 1 := fun h => hxb (Fin.ext h)
              dsimp [vc]; omega)
            have hxeq : x = ⟨vc, hac.symm⟩ := Subtype.ext hxc
            rw [hxeq, hdeg_vc_in va hac.symm]
            have hnv : ¬ (va = vb ∨ va = vx0) := by
              rintro (h | h)
              · exact hab h
              · have := congrArg Fin.val h; dsimp [va, vx0] at this; omega
            rw [if_neg hnv]; omega
      · rw [if_neg hab.symm, if_pos rfl]
        have hset : Finset.univ.filter (fun x : {y : Fin (n + 3) // y ≠ vb} => outDegRel (delRel vb) x = n) =
            ({⟨va, hab⟩, ⟨vc, hbc.symm⟩} : Finset {y : Fin (n + 3) // y ≠ vb}) := by
          ext x
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
          constructor
          · intro hdn
            by_cases hxn : x.1.val < n
            · exact absurd hdn (h_old_ne x hxn)
            · by_cases hxa : x.1 = va
              · exact Or.inl (Subtype.ext hxa)
              · exact Or.inr (Subtype.ext (Fin.ext (by
                  have hxa' : x.1.val ≠ n := fun h => hxa (Fin.ext h)
                  have hxb' : x.1.val ≠ n + 1 := fun h => x.2 (Fin.ext h)
                  dsimp [vc]; omega)))
          · rintro (rfl | rfl)
            · rw [hdeg_va_in vb hab, if_neg hbc]
            · rw [hdeg_vc_in vb hbc.symm, if_pos (Or.inl rfl)]
        rw [hset, Finset.card_pair (fun h => hac (congrArg Subtype.val h))]
      · rw [if_neg hac.symm, if_neg hbc.symm]
        have hset : Finset.univ.filter (fun x : {y : Fin (n + 3) // y ≠ vc} => outDegRel (delRel vc) x = n) =
            ({⟨vb, hbc⟩} : Finset {y : Fin (n + 3) // y ≠ vc}) := by
          ext x
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
          constructor
          · intro hdn
            by_cases hxn : x.1.val < n
            · exact absurd hdn (h_old_ne x hxn)
            · by_cases hxb : x.1 = vb
              · exact Subtype.ext hxb
              · have hxa : x.1 = va := Fin.ext (by
                  have hxb' : x.1.val ≠ n + 1 := fun h => hxb (Fin.ext h)
                  have hxc' : x.1.val ≠ n + 2 := fun h => x.2 (Fin.ext h)
                  dsimp [va]; omega)
                have hxeq : x = ⟨va, hac⟩ := Subtype.ext hxa
                rw [hxeq, hdeg_va_in vc hac, if_pos rfl] at hdn
                omega
          · rintro rfl
            rw [hdeg_vb_in vc hbc, if_neg hac.symm]
        rw [hset, Finset.card_singleton]
    have hN_eq := count_outDeg_eq_map iso n
    rw [hdegN_count u hu, hdegN_count v hv] at hN_eq
    have hu_cases : u = va ∨ u = vb ∨ u = vc := by
      by_cases h1 : u.val = n
      · exact Or.inl (Fin.ext h1)
      · by_cases h2 : u.val = n + 1
        · exact Or.inr (Or.inl (Fin.ext h2))
        · exact Or.inr (Or.inr (Fin.ext (by dsimp [vc]; omega)))
    have hv_cases : v = va ∨ v = vb ∨ v = vc := by
      by_cases h1 : v.val = n
      · exact Or.inl (Fin.ext h1)
      · by_cases h2 : v.val = n + 1
        · exact Or.inr (Or.inl (Fin.ext h2))
        · exact Or.inr (Or.inr (Fin.ext (by dsimp [vc]; omega)))
    have hab : va ≠ vb := fun h => by have := congrArg Fin.val h; dsimp [va, vb] at this; omega
    have hac : va ≠ vc := fun h => by have := congrArg Fin.val h; dsimp [va, vc] at this; omega
    have hbc : vb ≠ vc := fun h => by have := congrArg Fin.val h; dsimp [vb, vc] at this; omega
    rcases hu_cases with rfl | rfl | rfl <;> rcases hv_cases with rfl | rfl | rfl
    · exact huv rfl
    · rw [if_pos rfl, if_neg hab.symm, if_pos rfl] at hN_eq; omega
    · rw [if_pos rfl, if_neg hac.symm, if_neg hbc.symm] at hN_eq; omega
    · rw [if_neg hab.symm, if_pos rfl, if_pos rfl] at hN_eq; omega
    · exact huv rfl
    · rw [if_neg hab.symm, if_pos rfl, if_neg hac.symm, if_neg hbc.symm] at hN_eq; omega
    · rw [if_neg hac.symm, if_neg hbc.symm, if_pos rfl] at hN_eq; omega
    · rw [if_neg hac.symm, if_neg hbc.symm, if_neg hab.symm, if_pos rfl] at hN_eq; omega
    · exact huv rfl

private lemma exists_linkIrreg_ge_6 :
    ∀ n : ℕ, 6 ≤ n → ∃ T : Tournament n, IsLinkIrregular T ∧ ∀ u : Fin n, outDegRel T.adj u ≤ n - 2 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    by_cases h6 : n = 6
    · subst h6; exact base6_exists
    · by_cases h7 : n = 7
      · subst h7; exact base7_exists
      · by_cases h8 : n = 8
        · subst h8; exact base8_exists
        · obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
          have hm : 6 ≤ m := by omega
          rcases ih m (by omega) hm with ⟨T, hirr, hmax⟩
          rcases step3 hm T hirr hmax with ⟨T', hirr', hmax'⟩
          exact ⟨T', hirr', fun u => by have := hmax' u; omega⟩

private lemma main_proof :
    ∀ n : ℕ, 2 ≤ n → ((∃ T : Tournament n, IsLinkIrregular T) ↔ 6 ≤ n) := by
  intro n hn
  constructor
  · rintro ⟨T, hT⟩
    by_contra hlt
    push Not at hlt
    have hcases : n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 := by omega
    rcases hcases with rfl | rfl | rfl | rfl
    · exact no_linkIrreg_2 T hT
    · exact no_linkIrreg_3 T hT
    · exact no_linkIrreg_4 T hT
    · exact no_linkIrreg_5 T hT
  · intro h6
    rcases exists_linkIrreg_ge_6 n h6 with ⟨T, hT, _⟩
    exact ⟨T, hT⟩

end OMA.P_arxiv_2512_20494

theorem OMA.solution : type_of% @OMA.S_arxiv_2512_20494.main :=
  OMA.P_arxiv_2512_20494.main_proof
