import OMAReductions.R_ReconstructionConjecture_reconstruction_conjecture_R2
import Mathlib

namespace OMA.KellyDisc

open SimpleGraph Finset ReconstructionConjecture

open Classical

section general

variable {X Y : Type} [Fintype X] [Fintype Y]

/-- A component: a vertex set inducing a connected graph and closed under adjacency. -/
def IsComp (K : SimpleGraph X) (S : Finset X) : Prop :=
  (K.induce (S : Set X)).Connected ∧ ∀ x y, x ∈ S → K.Adj x y → y ∈ S

/-- Number of induced copies of `F`. -/
noncomputable def sC {k : ℕ} (K : SimpleGraph X) (F : SimpleGraph (Fin k)) : ℕ :=
  Finset.card (univ.filter fun S : Finset X => Nonempty (K.induce (S : Set X) ≃g F))

/-- Number of components isomorphic to `F`. -/
noncomputable def cC {k : ℕ} (K : SimpleGraph X) (F : SimpleGraph (Fin k)) : ℕ :=
  Finset.card (univ.filter fun S : Finset X => IsComp K S ∧ Nonempty (K.induce (S : Set X) ≃g F))

/-- The vertex set of the component of `x`. -/
noncomputable def R (K : SimpleGraph X) (x : X) : Finset X := univ.filter (K.Reachable x)

theorem nonempty_iso_congr {A B C : Type} {G : SimpleGraph A} {H : SimpleGraph B}
    {F : SimpleGraph C} (e : G ≃g H) : Nonempty (G ≃g F) ↔ Nonempty (H ≃g F) :=
  ⟨fun ⟨f⟩ => ⟨e.symm.trans f⟩, fun ⟨f⟩ => ⟨e.trans f⟩⟩

noncomputable def isoEq (K : SimpleGraph X) {s t : Set X} (h : s = t) :
    K.induce s ≃g K.induce t := by
  subst h
  exact Iso.refl

noncomputable def indInd (K : SimpleGraph X) (U : Set X) (T : Set U) :
    (K.induce U).induce T ≃g K.induce (Subtype.val '' T) where
  toEquiv := Equiv.Set.image Subtype.val T Subtype.val_injective
  map_rel_iff' := Iff.rfl

noncomputable def indMap (K : SimpleGraph X) (U : Set X) (T : Finset U) :
    (K.induce U).induce (T : Set U) ≃g
      K.induce ((T.map (Function.Embedding.subtype _) : Finset X) : Set X) :=
  (indInd K U (T : Set U)).trans (isoEq K (by rw [Finset.coe_map]; rfl))

theorem reach_of_induce {K : SimpleGraph X} {s : Set X} {a b : s}
    (h : (K.induce s).Reachable a b) : K.Reachable a b :=
  h.map (Embedding.induce s).toHom

theorem closed_reach {K : SimpleGraph X} {S : Finset X}
    (hS : ∀ x y, x ∈ S → K.Adj x y → y ∈ S) {x y : X} (hx : x ∈ S) (h : K.Reachable x y) :
    y ∈ S := by
  obtain ⟨p⟩ := h
  revert hx
  induction p with
  | nil => exact id
  | cons h' _ ih => exact fun hx => ih (hS _ _ hx h')

theorem comp_mem_iff {K : SimpleGraph X} {S : Finset X} (hS : IsComp K S) {x : X} (hx : x ∈ S)
    (y : X) : y ∈ S ↔ K.Reachable x y := by
  constructor
  · intro hy
    exact reach_of_induce (hS.1.preconnected ⟨x, Finset.mem_coe.mpr hx⟩ ⟨y, Finset.mem_coe.mpr hy⟩)
  · exact closed_reach hS.2 hx

theorem mem_R {K : SimpleGraph X} {x y : X} : y ∈ R K x ↔ K.Reachable x y := by
  simp [R]

theorem R_eq {K : SimpleGraph X} {S : Finset X} (hS : IsComp K S) {x : X} (hx : x ∈ S) :
    R K x = S := by
  ext y
  rw [mem_R, comp_mem_iff hS hx]

theorem R_comp (K : SimpleGraph X) (x : X) : IsComp K (R K x) := by
  refine ⟨?_, ?_⟩
  · have hset : ((R K x : Finset X) : Set X) = (K.connectedComponentMk x).supp := by
      ext y
      rw [ConnectedComponent.mem_supp_iff, ConnectedComponent.eq, Finset.mem_coe, mem_R]
      exact ⟨fun h => h.symm, fun h => h.symm⟩
    rw [hset]
    exact (K.connectedComponentMk x).connected_toSimpleGraph
  · intro a b ha hab
    rw [mem_R] at ha ⊢
    exact ha.trans hab.reachable

theorem R_adj {K : SimpleGraph X} {a b : X} (h : K.Adj a b) : R K a = R K b := by
  ext y
  rw [mem_R, mem_R]
  exact ⟨fun h' => h.symm.reachable.trans h', fun h' => h.reachable.trans h'⟩

theorem comp_nonempty {K : SimpleGraph X} {S : Finset X} (hS : IsComp K S) : ∃ x, x ∈ S := by
  obtain ⟨⟨x, hx⟩⟩ := hS.1.nonempty
  exact ⟨x, Finset.mem_coe.mp hx⟩

theorem sC_card {k : ℕ} {K : SimpleGraph X} {F : SimpleGraph (Fin k)} {S : Finset X}
    (h : Nonempty (K.induce (S : Set X) ≃g F)) : S.card = k := by
  obtain ⟨f⟩ := h
  have := Fintype.card_congr f.toEquiv
  simpa using this

theorem card_restrict (U : Set X) [Fintype U] (P : Finset X → Prop) :
    Finset.card (univ.filter fun T : Finset U => P (T.map (Function.Embedding.subtype _))) =
      Finset.card (univ.filter fun S : Finset X => (∀ x ∈ S, x ∈ U) ∧ P S) := by
  refine card_bij (fun T _ => T.map (Function.Embedding.subtype _)) ?_ ?_ ?_
  · intro T hT
    simp only [mem_filter, mem_univ, true_and] at hT ⊢
    refine ⟨?_, hT⟩
    intro x hx
    rw [mem_map] at hx
    obtain ⟨y, _, rfl⟩ := hx
    exact y.2
  · intro a _ b _ h
    exact map_injective _ h
  · intro S hS
    simp only [mem_filter, mem_univ, true_and] at hS
    have e : (S.subtype (· ∈ U)).map (Function.Embedding.subtype _) = S := by
      rw [subtype_map]
      exact filter_true_of_mem hS.1
    refine ⟨S.subtype (· ∈ U), ?_, e⟩
    simp only [mem_filter, mem_univ, true_and]
    rw [e]
    exact hS.2

theorem sC_induce {k : ℕ} (K : SimpleGraph X) (U : Set X) [Fintype U] (F : SimpleGraph (Fin k)) :
    sC (K.induce U) F = Finset.card (univ.filter fun S : Finset X =>
      (∀ x ∈ S, x ∈ U) ∧ Nonempty (K.induce (S : Set X) ≃g F)) := by
  have h := card_restrict U (fun S => Nonempty (K.induce (S : Set X) ≃g F))
  unfold sC
  refine Eq.trans ?_ (h.trans ?_)
  · congr 1
    ext T
    simp only [mem_filter, mem_univ, true_and]
    exact nonempty_iso_congr (indMap K U T)
  · congr 1

noncomputable def isoImg {K : SimpleGraph X} {L : SimpleGraph Y} (e : K ≃g L) (S : Finset X) :
    K.induce (S : Set X) ≃g L.induce ((S.map e.toEquiv.toEmbedding : Finset Y) : Set Y) :=
  e.induce (by rw [Finset.coe_map]; exact e.injective.injOn.bijOn_image)

theorem sC_iso {k : ℕ} {K : SimpleGraph X} {L : SimpleGraph Y} (e : K ≃g L)
    (F : SimpleGraph (Fin k)) : sC K F = sC L F := by
  unfold sC
  refine card_bij (fun S _ => S.map e.toEquiv.toEmbedding) ?_ ?_ ?_
  · intro S hS
    simp only [mem_filter, mem_univ, true_and] at hS ⊢
    obtain ⟨f⟩ := hS
    exact ⟨(isoImg e S).symm.trans f⟩
  · intro a _ b _ h
    exact map_injective _ h
  · intro S hS
    simp only [mem_filter, mem_univ, true_and] at hS
    have hm : (S.map e.symm.toEquiv.toEmbedding).map e.toEquiv.toEmbedding = S := by
      ext x
      simp only [mem_map, Equiv.toEmbedding_apply]
      constructor
      · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
        rw [show e.toEquiv (e.symm.toEquiv z) = z from e.apply_symm_apply z]
        exact hz
      · intro hx
        exact ⟨e.symm x, ⟨x, hx, rfl⟩, e.apply_symm_apply x⟩
    refine ⟨S.map e.symm.toEquiv.toEmbedding, ?_, hm⟩
    simp only [mem_filter, mem_univ, true_and]
    obtain ⟨f⟩ := hS
    exact ⟨(isoImg e _).trans ((isoEq L (congrArg (fun T : Finset Y => (T : Set Y)) hm)).trans f)⟩

theorem kelly_sum {k : ℕ} (K : SimpleGraph X) (F : SimpleGraph (Fin k)) :
    ∑ v, sC (K.induce ({v}ᶜ : Set X)) F = (Fintype.card X - k) * sC K F := by
  have h1 : ∀ v, sC (K.induce ({v}ᶜ : Set X)) F = ∑ S : Finset X,
      if v ∉ S ∧ Nonempty (K.induce (S : Set X) ≃g F) then 1 else 0 := by
    intro v
    rw [sC_induce, card_filter]
    refine sum_congr rfl (fun S _ => ?_)
    have hiff : (∀ x ∈ S, x ∈ ({v}ᶜ : Set X)) ↔ v ∉ S :=
      ⟨fun h hv => h v hv rfl, fun h x hx hxv => h (hxv ▸ hx)⟩
    simp only [hiff]
  rw [sum_congr rfl (fun v _ => h1 v), sum_comm]
  unfold sC
  rw [card_filter, mul_sum]
  refine sum_congr rfl (fun S _ => ?_)
  by_cases hP : Nonempty (K.induce (S : Set X) ≃g F)
  · simp only [hP, and_true, if_true, mul_one]
    rw [← card_filter]
    have hc := card_filter_add_card_filter_not (s := (univ : Finset X)) (fun v => v ∈ S)
    have hS : (univ : Finset X).filter (fun v => v ∈ S) = S := by
      ext x
      simp
    rw [hS, card_univ, sC_card hP] at hc
    omega
  · simp [hP]

theorem kelly {V W : Type} [Fintype V] [Fintype W] {G : SimpleGraph V} {H : SimpleGraph W}
    (h : Hypomorphic G H) {k : ℕ} (hk : k < Fintype.card V) (F : SimpleGraph (Fin k)) :
    sC G F = sC H F := by
  obtain ⟨σ, hc⟩ := h
  have e1 := kelly_sum G F
  have e2 := kelly_sum H F
  have hn : Fintype.card W = Fintype.card V := (Fintype.card_congr σ).symm
  have e3 : ∑ v, sC (G.induce ({v}ᶜ : Set V)) F = ∑ w, sC (H.induce ({w}ᶜ : Set W)) F := by
    rw [← Equiv.sum_comp σ (fun w => sC (H.induce ({w}ᶜ : Set W)) F)]
    refine sum_congr rfl (fun v _ => ?_)
    obtain ⟨φ⟩ := hc v
    exact sC_iso φ F
  rw [e1, e2, hn] at e3
  exact Nat.eq_of_mul_eq_mul_left (by omega) e3

noncomputable def sumIso (K : SimpleGraph X) (S : Set X)
    (hS : ∀ x y, x ∈ S → K.Adj x y → y ∈ S) : K.induce S ⊕g K.induce Sᶜ ≃g K where
  toEquiv := Equiv.Set.sumCompl S
  map_rel_iff' := by
    intro a b
    rcases a with a | a <;> rcases b with b | b
    · rw [Equiv.Set.sumCompl_apply_inl, Equiv.Set.sumCompl_apply_inl, sum_adj_inl]
      exact Iff.rfl
    · rw [Equiv.Set.sumCompl_apply_inl, Equiv.Set.sumCompl_apply_inr]
      exact iff_of_false (fun h => b.2 (hS _ _ a.2 h)) (not_adj_sum_inl_inr _ _)
    · rw [Equiv.Set.sumCompl_apply_inr, Equiv.Set.sumCompl_apply_inl]
      exact iff_of_false (fun h => a.2 (hS _ _ b.2 h.symm))
        (fun h => not_adj_sum_inl_inr _ _ h.symm)
    · rw [Equiv.Set.sumCompl_apply_inr, Equiv.Set.sumCompl_apply_inr, sum_adj_inr]
      exact Iff.rfl

theorem glue {K : SimpleGraph X} {L : SimpleGraph Y} {S : Set X} {T : Set Y}
    (hS : ∀ x y, x ∈ S → K.Adj x y → y ∈ S) (hT : ∀ x y, x ∈ T → L.Adj x y → y ∈ T)
    (f : K.induce S ≃g L.induce T) (g : K.induce Sᶜ ≃g L.induce Tᶜ) : Nonempty (K ≃g L) :=
  ⟨((sumIso K S hS).symm.trans (Iso.sumCongr f g)).trans (sumIso L T hT)⟩

theorem compl_closed {K : SimpleGraph X} {S : Set X} (hS : ∀ x y, x ∈ S → K.Adj x y → y ∈ S) :
    ∀ x y, x ∈ Sᶜ → K.Adj x y → y ∈ Sᶜ :=
  fun _ _ hx h hy => hx (hS _ _ hy h.symm)

theorem isComp_induce {K : SimpleGraph X} {U : Set X} (hU : ∀ x y, x ∈ U → K.Adj x y → y ∈ U)
    (T : Finset U) : IsComp (K.induce U) T ↔ IsComp K (T.map (Function.Embedding.subtype _)) := by
  unfold IsComp
  rw [(indMap K U T).connected_iff]
  apply and_congr Iff.rfl
  constructor
  · intro h x y hx hxy
    rw [mem_map] at hx
    obtain ⟨x', hx', rfl⟩ := hx
    have hy : y ∈ U := hU _ _ x'.2 hxy
    have := h x' ⟨y, hy⟩ hx' hxy
    exact mem_map.mpr ⟨⟨y, hy⟩, this, rfl⟩
  · intro h x y hx hxy
    have := h x.1 y.1 (mem_map.mpr ⟨x, hx, rfl⟩) hxy
    rw [mem_map] at this
    obtain ⟨y', hy', e⟩ := this
    have : y' = y := Subtype.ext e
    rw [← this]
    exact hy'

theorem cC_induce {k : ℕ} (K : SimpleGraph X) {U : Set X} [Fintype U]
    (hU : ∀ x y, x ∈ U → K.Adj x y → y ∈ U) (F : SimpleGraph (Fin k)) :
    cC (K.induce U) F = Finset.card (univ.filter fun S : Finset X => (∀ x ∈ S, x ∈ U) ∧
      (IsComp K S ∧ Nonempty (K.induce (S : Set X) ≃g F))) := by
  have h := card_restrict U (fun S => IsComp K S ∧ Nonempty (K.induce (S : Set X) ≃g F))
  unfold cC
  refine Eq.trans ?_ (h.trans ?_)
  · congr 1
    ext T
    simp only [mem_filter, mem_univ, true_and]
    exact and_congr (isComp_induce hU T) (nonempty_iso_congr (indMap K U T))
  · congr 1 <;> ext S <;> simp only [mem_filter, mem_univ, true_and]

theorem eq_of_meet {K : SimpleGraph X} {S T : Finset X} (hS : IsComp K S) (hT : IsComp K T)
    {x : X} (hxS : x ∈ S) (hxT : x ∈ T) : S = T :=
  (R_eq hS hxS).symm.trans (R_eq hT hxT)

theorem remove_comp {k : ℕ} (K : SimpleGraph X) {S : Finset X} (hS : IsComp K S)
    (F : SimpleGraph (Fin k)) :
    cC K F = cC (K.induce ((S : Set X)ᶜ)) F +
      (if Nonempty (K.induce (S : Set X) ≃g F) then 1 else 0) := by
  rw [cC_induce K (compl_closed hS.2) F]
  have hc := card_filter_add_card_filter_not
    (s := univ.filter fun R : Finset X => IsComp K R ∧ Nonempty (K.induce (R : Set X) ≃g F))
    (fun R : Finset X => ∀ x ∈ R, x ∈ ((S : Set X)ᶜ))
  rw [filter_filter, filter_filter] at hc
  unfold cC
  rw [← hc]
  congr 1
  · congr 1
    ext R
    simp only [mem_filter, mem_univ, true_and]
    exact and_comm
  · split_ifs with hP
    · rw [card_eq_one]
      refine ⟨S, ?_⟩
      ext R
      simp only [mem_filter, mem_univ, true_and, mem_singleton]
      constructor
      · rintro ⟨⟨hR, _⟩, hD⟩
        have : ∃ x, x ∈ R ∧ x ∈ S := by
          by_contra hne
          apply hD
          intro x hx hxS
          exact hne ⟨x, hx, hxS⟩
        obtain ⟨x, hxR, hxS⟩ := this
        exact eq_of_meet hR hS hxR hxS
      · rintro rfl
        refine ⟨⟨hS, hP⟩, ?_⟩
        intro hD
        obtain ⟨x, hx⟩ := comp_nonempty hS
        exact hD x hx hx
    · rw [card_eq_zero, filter_eq_empty_iff]
      rintro R - ⟨⟨hR, hRF⟩, hD⟩
      have : ∃ x, x ∈ R ∧ x ∈ S := by
        by_contra hne
        apply hD
        intro x hx hxS
        exact hne ⟨x, hx, hxS⟩
      obtain ⟨x, hxR, hxS⟩ := this
      have := eq_of_meet hR hS hxR hxS
      subst this
      exact hP hRF

theorem exists_fin {A : Type} [Fintype A] (G : SimpleGraph A) :
    ∃ F : SimpleGraph (Fin (Fintype.card A)), Nonempty (G ≃g F) :=
  ⟨_, ⟨Iso.map (Fintype.equivFin A) G⟩⟩

theorem match_comp {K : SimpleGraph X} {L : SimpleGraph Y}
    (hc : ∀ k (F : SimpleGraph (Fin k)), F.Connected → cC K F = cC L F) {S : Finset X}
    (hS : IsComp K S) :
    ∃ T : Finset Y, IsComp L T ∧ Nonempty (K.induce (S : Set X) ≃g L.induce (T : Set Y)) := by
  obtain ⟨F, ⟨e⟩⟩ := exists_fin (K.induce (S : Set X))
  have hF : F.Connected := e.connected_iff.mp hS.1
  have h1 : 0 < cC K F := by
    unfold cC
    apply card_pos.mpr
    exact ⟨S, by simp only [mem_filter, mem_univ, true_and]; exact ⟨hS, ⟨e⟩⟩⟩
  rw [hc _ _ hF] at h1
  unfold cC at h1
  obtain ⟨T, hT⟩ := card_pos.mp h1
  simp only [mem_filter, mem_univ, true_and] at hT
  obtain ⟨hT1, ⟨f⟩⟩ := hT
  exact ⟨T, hT1, ⟨e.trans f.symm⟩⟩

theorem iso_of_cC : ∀ (n : ℕ) {X Y : Type} [Fintype X] [Fintype Y] (K : SimpleGraph X)
    (L : SimpleGraph Y), Fintype.card X = n →
    (∀ k (F : SimpleGraph (Fin k)), F.Connected → cC K F = cC L F) → Nonempty (K ≃g L) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro X Y _ _ K L hn hc
  by_cases hX : Nonempty X
  · obtain ⟨x⟩ := hX
    have hS := R_comp K x
    obtain ⟨T, hT, ⟨φ⟩⟩ := match_comp hc hS
    have hlt : Fintype.card ((R K x : Set X)ᶜ : Set X) < n := by
      rw [← hn]
      apply Fintype.card_subtype_lt (x := x)
      intro h
      exact h (Finset.mem_coe.mpr (mem_R.mpr (Reachable.refl x)))
    have hc' : ∀ k (F : SimpleGraph (Fin k)), F.Connected →
        cC (K.induce ((R K x : Set X)ᶜ)) F = cC (L.induce ((T : Set Y)ᶜ)) F := by
      intro k F hF
      have hK := remove_comp K hS F
      have hL := remove_comp L hT F
      have hiff := nonempty_iso_congr (F := F) φ
      rw [hc k F hF] at hK
      by_cases hP : Nonempty (K.induce (R K x : Set X) ≃g F)
      · have hQ := hiff.mp hP
        simp only [hP, hQ, if_true] at hK hL
        omega
      · have hQ : ¬ Nonempty (L.induce (T : Set Y) ≃g F) := fun h => hP (hiff.mpr h)
        simp only [hP, hQ, if_false] at hK hL
        omega
    obtain ⟨ψ⟩ := ih _ hlt (K.induce ((R K x : Set X)ᶜ)) (L.induce ((T : Set Y)ᶜ)) rfl hc'
    exact glue (S := (R K x : Set X)) (T := (T : Set Y)) hS.2 hT.2 φ ψ
  · by_cases hY : Nonempty Y
    · exfalso
      obtain ⟨y⟩ := hY
      obtain ⟨S, hS, -⟩ := match_comp (fun k F hF => (hc k F hF).symm) (R_comp L y)
      obtain ⟨x, -⟩ := comp_nonempty hS
      exact hX ⟨x⟩
    · have : IsEmpty X := not_nonempty_iff.mp hX
      have : IsEmpty Y := not_nonempty_iff.mp hY
      exact ⟨⟨Equiv.equivOfIsEmpty X Y, fun {a} => isEmptyElim a⟩⟩

/-- Vertices whose component has more than `k` vertices. -/
def Uset (K : SimpleGraph X) (k : ℕ) : Set X := {x | k < (R K x).card}

theorem Uset_closed (K : SimpleGraph X) (k : ℕ) :
    ∀ x y, x ∈ Uset K k → K.Adj x y → y ∈ Uset K k := by
  intro x y hx h
  change k < (R K y).card
  rw [← R_adj h]
  exact hx

theorem s_rec {k : ℕ} (K : SimpleGraph X) (F : SimpleGraph (Fin k)) (hF : F.Connected) :
    sC K F = cC K F + sC (K.induce (Uset K k)) F := by
  rw [sC_induce]
  have hc := card_filter_add_card_filter_not
    (s := univ.filter fun S : Finset X => Nonempty (K.induce (S : Set X) ≃g F))
    (fun S : Finset X => ∀ x ∈ S, x ∈ Uset K k)
  rw [filter_filter, filter_filter] at hc
  unfold sC cC
  rw [← hc, add_comm]
  congr 1
  · congr 1
    ext S
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨hP, hD⟩
      have hcard := sC_card hP
      obtain ⟨f⟩ := hP
      have hconn : (K.induce (S : Set X)).Connected := f.connected_iff.mpr hF
      have : ∃ x, x ∈ S ∧ ¬ k < (R K x).card := by
        by_contra hne
        apply hD
        intro x hx
        by_contra hxU
        exact hne ⟨x, hx, hxU⟩
      obtain ⟨x, hxS, hxk⟩ := this
      have hsub : S ⊆ R K x := by
        intro y hy
        exact mem_R.mpr (reach_of_induce
          (hconn.preconnected ⟨x, Finset.mem_coe.mpr hxS⟩ ⟨y, Finset.mem_coe.mpr hy⟩))
      have heq : S = R K x := eq_of_subset_of_card_le hsub (by omega)
      refine ⟨?_, ⟨f⟩⟩
      rw [heq]
      exact R_comp K x
    · rintro ⟨hC, hP⟩
      refine ⟨hP, ?_⟩
      intro hD
      obtain ⟨x, hx⟩ := comp_nonempty hC
      have h1 := hD x hx
      change k < (R K x).card at h1
      rw [R_eq hC hx, sC_card hP] at h1
      omega
  · congr 1
    ext S
    simp only [mem_filter, mem_univ, true_and]
    exact and_comm

theorem cC_U {k j : ℕ} (K : SimpleGraph X) (F : SimpleGraph (Fin j)) :
    cC (K.induce (Uset K k)) F = if k < j then cC K F else 0 := by
  rw [cC_induce K (Uset_closed K k) F]
  split_ifs with hkj
  · unfold cC
    congr 1
    ext S
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · exact fun h => h.2
    · intro h
      refine ⟨?_, h⟩
      intro x hx
      change k < (R K x).card
      rw [R_eq h.1 hx, sC_card h.2]
      exact hkj
  · rw [card_eq_zero, filter_eq_empty_iff]
    rintro S - ⟨hD, hC, hP⟩
    obtain ⟨x, hx⟩ := comp_nonempty hC
    have h1 := hD x hx
    change k < (R K x).card at h1
    rw [R_eq hC hx, sC_card hP] at h1
    exact hkj h1

theorem cC_big {k : ℕ} (K : SimpleGraph X) (hK : ¬ K.Connected) (hk : Fintype.card X ≤ k)
    (F : SimpleGraph (Fin k)) : cC K F = 0 := by
  unfold cC
  rw [card_eq_zero, filter_eq_empty_iff]
  rintro S - ⟨hC, hP⟩
  have hcard := sC_card hP
  have hle := card_le_univ S
  have hS : S = univ := eq_univ_of_card S (by omega)
  have h := hC.1
  rw [hS, Finset.coe_univ] at h
  exact hK ((induceUnivIso K).connected_iff.mp h)

end general

theorem two_cards {W : Type} [Fintype W] (H : SimpleGraph W) (hc : H.Connected)
    (hn : 2 ≤ Fintype.card W) : ∃ a b, a ≠ b ∧ (H.induce ({a}ᶜ : Set W)).Connected ∧
      (H.induce ({b}ᶜ : Set W)).Connected := by
  obtain ⟨T, hle, hT⟩ := hc.exists_isTree_le
  have : Nontrivial W := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨u, v, huv, hu, hv⟩ := hT.exists_ne_and_degree_eq_one
  exact ⟨u, v, huv, (hT.1.induce_compl_singleton_of_degree_eq_one hu).mono (fun _ _ h => hle h),
    (hT.1.induce_compl_singleton_of_degree_eq_one hv).mono (fun _ _ h => hle h)⟩

theorem disc_cards {V : Type} [Fintype V] (G : SimpleGraph V) (hG : ¬ G.Connected)
    (h3 : 3 ≤ Fintype.card V) {v w : V} (hvw : v ≠ w)
    (hv : (G.induce ({v}ᶜ : Set V)).Connected) (hw : (G.induce ({w}ᶜ : Set V)).Connected) :
    False := by
  have hr : ∀ {u : V}, (G.induce ({u}ᶜ : Set V)).Connected → ∀ a b : V, a ≠ u → b ≠ u →
      G.Reachable a b := fun hu a b ha hb =>
    reach_of_induce (hu.preconnected ⟨a, Set.mem_compl_singleton_iff.mpr ha⟩
      ⟨b, Set.mem_compl_singleton_iff.mpr hb⟩)
  have hlt : ({v, w} : Finset V).card < (univ : Finset V).card := by
    have := card_le_two (a := v) (b := w)
    rw [card_univ]
    omega
  obtain ⟨c, -, hc⟩ := exists_mem_notMem_of_card_lt_card hlt
  have hcv : c ≠ v := fun h => hc (by simp [h])
  have hcw : c ≠ w := fun h => hc (by simp [h])
  apply hG
  have hall : ∀ x, G.Reachable x c := by
    intro x
    by_cases hx : x = v
    · exact hr hw x c (by rw [hx]; exact hvw) hcw
    · exact hr hv x c hx hcv
  exact (connected_iff_exists_forall_reachable G).mpr ⟨c, fun x => (hall x).symm⟩

theorem H_disc {V W : Type} [Fintype V] [Fintype W] {G : SimpleGraph V} {H : SimpleGraph W}
    (hG : ¬ G.Connected) (h3 : 3 ≤ Fintype.card V) (hyp : Hypomorphic G H) : ¬ H.Connected := by
  intro hH
  obtain ⟨σ, hc⟩ := hyp
  have hn : Fintype.card W = Fintype.card V := (Fintype.card_congr σ).symm
  obtain ⟨a, b, hab, ha, hb⟩ := two_cards H hH (by omega)
  have card_conn : ∀ w, (H.induce ({w}ᶜ : Set W)).Connected →
      (G.induce ({σ.symm w}ᶜ : Set V)).Connected := by
    intro w hw
    obtain ⟨φ⟩ := hc (σ.symm w)
    rw [σ.apply_symm_apply] at φ
    exact φ.connected_iff.mpr hw
  exact disc_cards G hG h3 (fun h => hab (σ.symm.injective h)) (card_conn a ha) (card_conn b hb)

theorem H1proof : OMA.R_ReconstructionConjecture_reconstruction_conjecture_R2.H1 := by
  intro V W _ _ h3 G H hG hyp
  have hH := H_disc hG h3 hyp
  have hn : Fintype.card V = Fintype.card W := hyp.card_eq
  have key : ∀ m k (F : SimpleGraph (Fin k)), F.Connected → Fintype.card V ≤ k + m →
      cC G F = cC H F := by
    intro m
    induction m with
    | zero =>
      intro k F _ hk
      rw [cC_big G hG (by omega), cC_big H hH (by omega)]
    | succ m ih =>
      intro k F hF hk
      by_cases hk' : Fintype.card V ≤ k + m
      · exact ih k F hF hk'
      · have hU : ∀ j (F' : SimpleGraph (Fin j)), F'.Connected →
            cC (G.induce (Uset G k)) F' = cC (H.induce (Uset H k)) F' := by
          intro j F' hF'
          rw [cC_U, cC_U]
          split_ifs with hkj
          · exact ih j F' hF' (by omega)
          · rfl
        obtain ⟨ψ⟩ := iso_of_cC _ (G.induce (Uset G k)) (H.induce (Uset H k)) rfl hU
        have e1 := s_rec G F hF
        have e2 := s_rec H F hF
        have e3 := kelly hyp (show k < Fintype.card V by omega) F
        have e4 := sC_iso ψ F
        omega
  exact iso_of_cC _ G H rfl (fun k F hF => key (Fintype.card V) k F hF (by omega))

end OMA.KellyDisc

theorem OMA.solution : OMA.R_ReconstructionConjecture_reconstruction_conjecture_R2.H1 :=
  OMA.KellyDisc.H1proof
