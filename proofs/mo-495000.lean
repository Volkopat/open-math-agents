import OMAStatements.S_mo_495000

/-!
# McKay's finite powerset graph reconstruction conjecture

Credit: @vlad-ds
-/

open SimpleGraph
open OMA.S_mo_495000

namespace McKay


variable {V W A B : Type}

def componentIso {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H)
    (C : G.ConnectedComponent) :
    C.toSimpleGraph ≃g (e.connectedComponentEquiv C).toSimpleGraph :=
  ⟨C.isoEquivSupp e, e.map_rel_iff⟩

def boxCongr {G : SimpleGraph V} {H : SimpleGraph W} {I : SimpleGraph A}
    {J : SimpleGraph B} (e : G ≃g I) (f : H ≃g J) : SimpleGraph.boxProd G H ≃g SimpleGraph.boxProd I J :=
  ⟨e.toEquiv.prodCongr f.toEquiv, by simp [SimpleGraph.boxProd_adj, e.map_rel_iff, f.map_rel_iff]⟩

private theorem full_map_adj {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) {S T : Set V} (h : (fullGraph G).Adj S T) :
    (fullGraph H).Adj (e '' S) (e '' T) := by
  obtain ⟨u, v, huv, hu, hv⟩ := h
  refine ⟨e u, e v, e.map_rel_iff.mpr huv, ?_, ?_⟩
  · rw [← Set.image_sdiff e.injective, hu, Set.image_singleton]
  · rw [← Set.image_sdiff e.injective, hv, Set.image_singleton]

def fullCongr {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) :
    fullGraph G ≃g fullGraph H where
  toEquiv := Equiv.Set.congr e.toEquiv
  map_rel_iff' := by
    intro S T
    constructor
    · intro h
      have hh := full_map_adj e.symm h
      change (fullGraph G).Adj (e.toEquiv.symm '' (e.toEquiv '' S)) (e.toEquiv.symm '' (e.toEquiv '' T)) at hh
      simpa only [Equiv.symm_image_image] using hh
    · exact full_map_adj e

private def merge (p : Set V × Set W) : Set (V ⊕ W) := Sum.elim p.1 p.2

private theorem left_diff {s t : Set V × Set W} (u : V) :
    merge s \ merge t = {Sum.inl u} ↔ s.1 \ t.1 = {u} ∧ s.2 ⊆ t.2 := by
  rw [Set.ext_iff, Sum.forall, Set.ext_iff]
  change ((∀ a, a ∈ s.1 ∧ a ∉ t.1 ↔ Sum.inl a = (Sum.inl u : V ⊕ W)) ∧
    (∀ b, b ∈ s.2 ∧ b ∉ t.2 ↔ Sum.inr b = (Sum.inl u : V ⊕ W))) ↔ _
  simp [Set.subset_def]

private theorem right_diff {s t : Set V × Set W} (u : W) :
    merge s \ merge t = {Sum.inr u} ↔ s.2 \ t.2 = {u} ∧ s.1 ⊆ t.1 := by
  rw [Set.ext_iff, Sum.forall, Set.ext_iff]
  change ((∀ a, a ∈ s.1 ∧ a ∉ t.1 ↔ Sum.inl a = (Sum.inr u : V ⊕ W)) ∧
    (∀ b, b ∈ s.2 ∧ b ∉ t.2 ↔ Sum.inr b = (Sum.inr u : V ⊕ W))) ↔ _
  simp [Set.subset_def, and_comm]

def fullSum (G : SimpleGraph V) (H : SimpleGraph W) :
    SimpleGraph.boxProd (fullGraph G) (fullGraph H) ≃g fullGraph (G ⊕g H) where
  toEquiv := {
    toFun := merge
    invFun := fun t => (Sum.inl ⁻¹' t, Sum.inr ⁻¹' t)
    left_inv := fun _ => rfl
    right_inv := fun _ => Set.ext (by rintro (x | x) <;> rfl) }
  map_rel_iff' := by
    intro s t
    change (∃ u v, (G ⊕g H).Adj u v ∧ merge s \ merge t = {u} ∧
      merge t \ merge s = {v}) ↔ _
    constructor
    · rintro ⟨u | u, v | v, huv, h₁, h₂⟩
      · obtain ⟨ha, hb⟩ := (left_diff _).mp h₁
        obtain ⟨hc, hd⟩ := (left_diff _).mp h₂
        exact Or.inl ⟨⟨u, v, huv, ha, hc⟩, le_antisymm hb hd⟩
      · simp at huv
      · simp at huv
      · obtain ⟨ha, hb⟩ := (right_diff _).mp h₁
        obtain ⟨hc, hd⟩ := (right_diff _).mp h₂
        exact Or.inr ⟨⟨u, v, huv, ha, hc⟩, le_antisymm hb hd⟩
    · rintro (⟨⟨u, v, huv, h₁, h₂⟩, he⟩ | ⟨⟨u, v, huv, h₁, h₂⟩, he⟩)
      · exact ⟨Sum.inl u, Sum.inl v, huv, (left_diff _).mpr ⟨h₁, he.le⟩,
          (left_diff _).mpr ⟨h₂, he.ge⟩⟩
      · exact ⟨Sum.inr u, Sum.inr v, huv, (right_diff _).mpr ⟨h₁, he.le⟩,
          (right_diff _).mpr ⟨h₂, he.ge⟩⟩

noncomputable def splitComponent {G : SimpleGraph V} (C : G.ConnectedComponent) :
    C.toSimpleGraph ⊕g G.induce C.suppᶜ ≃g G := by
  classical
  refine ⟨Equiv.Set.sumCompl C.supp, ?_⟩
  rintro (u | u) (v | v)
  · rfl
  · exact iff_of_false (fun h => v.property ((C.mem_supp_congr_adj h).mp u.property)) (by simp)
  · exact iff_of_false (fun h => u.property ((C.mem_supp_congr_adj h).mpr v.property)) (by simp)
  · rfl

end McKay

open SimpleGraph


namespace McKayCancel

variable {α β γ : Type}

private theorem productComponentEq (X : SimpleGraph α) (Y : SimpleGraph β)
    (u v : α × β) :
    (SimpleGraph.boxProd X Y).connectedComponentMk u = (SimpleGraph.boxProd X Y).connectedComponentMk v ↔
      (X.connectedComponentMk u.1, Y.connectedComponentMk u.2) =
      (X.connectedComponentMk v.1, Y.connectedComponentMk v.2) := by
  simp only [Prod.mk.injEq, ConnectedComponent.eq, reachable_boxProd]

noncomputable def productComponents (X : SimpleGraph α) (Y : SimpleGraph β) :
    (SimpleGraph.boxProd X Y).ConnectedComponent ≃ X.ConnectedComponent × Y.ConnectedComponent :=
  Equiv.ofBijective
    (Quot.lift (fun u : α × β => (X.connectedComponentMk u.1, Y.connectedComponentMk u.2))
      (fun _ _ h => (productComponentEq X Y _ _).mp (ConnectedComponent.sound h))) <| by
    constructor
    · intro a b
      refine a.ind₂ (fun u v h => ?_) b
      exact (productComponentEq X Y u v).mpr h
    · rintro ⟨a, b⟩
      induction a using ConnectedComponent.ind with
      | _ u =>
        induction b using ConnectedComponent.ind with
        | _ v => exact ⟨(SimpleGraph.boxProd X Y).connectedComponentMk (u, v), rfl⟩

@[simp] theorem productComponents_mk (X : SimpleGraph α) (Y : SimpleGraph β) (u : α × β) :
    productComponents X Y ((SimpleGraph.boxProd X Y).connectedComponentMk u) =
      (X.connectedComponentMk u.1, Y.connectedComponentMk u.2) := rfl

noncomputable def productComponentIso (X : SimpleGraph α) (Y : SimpleGraph β)
    (D : (SimpleGraph.boxProd X Y).ConnectedComponent) :
    D.toSimpleGraph ≃g
      SimpleGraph.boxProd (productComponents X Y D).1.toSimpleGraph (productComponents X Y D).2.toSimpleGraph where
  toEquiv := {
    toFun := fun u =>
      let h : (X.connectedComponentMk u.1.1, Y.connectedComponentMk u.1.2) =
          productComponents X Y D :=
        congrArg (productComponents X Y) u.2
      (⟨u.1.1, congrArg Prod.fst h⟩, ⟨u.1.2, congrArg Prod.snd h⟩)
    invFun := fun u => ⟨(u.1.1, u.2.1), (productComponents X Y).injective (Prod.ext u.1.2 u.2.2)⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  map_rel_iff' := by
    intro u v
    change (_ ∧ _ = _ ∨ _ ∧ _ = _) ↔ (_ ∧ _ = _ ∨ _ ∧ _ = _)
    simp only [Subtype.ext_iff]
    rfl

/-- A finite graph up to isomorphism, with its vertex type normalized to `Fin n`. -/
private def FiniteGraph := Σ n : ℕ, SimpleGraph (Fin n)

private def graphSetoid : Setoid FiniteGraph where
  r A B := Nonempty (A.2 ≃g B.2)
  iseqv :=
    ⟨fun _ => ⟨Iso.refl⟩, fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e⟩ ⟨f⟩ => ⟨e.trans f⟩⟩

private abbrev GraphClass := Quotient graphSetoid

private noncomputable def finModel (G : SimpleGraph α) [Finite α] : FiniteGraph :=
  letI := Fintype.ofFinite α
  ⟨Fintype.card α, G.comap (Fintype.equivFin α).symm⟩

private noncomputable def finModelIso (G : SimpleGraph α) [Finite α] : (finModel G).2 ≃g G :=
  letI := Fintype.ofFinite α
  Iso.comap (Fintype.equivFin α).symm G

private noncomputable def graphClass (G : SimpleGraph α) [Finite α] : GraphClass :=
  Quotient.mk graphSetoid (finModel G)

private theorem graphClass_eq_iff (G : SimpleGraph α) (H : SimpleGraph β) [Finite α] [Finite β] :
    graphClass G = graphClass H ↔ Nonempty (G ≃g H) := by
  rw [graphClass, graphClass, Quotient.eq]
  constructor
  · rintro ⟨e⟩
    exact ⟨(finModelIso G).symm.trans (e.trans (finModelIso H))⟩
  · rintro ⟨e⟩
    exact ⟨(finModelIso G).trans (e.trans (finModelIso H).symm)⟩

noncomputable def isoComponent (G : SimpleGraph α) (H : SimpleGraph β) (e : G ≃g H)
    (c : G.ConnectedComponent) :
    c.toSimpleGraph ≃g (e.connectedComponentEquiv c).toSimpleGraph :=
  ⟨ConnectedComponent.isoEquivSupp e c, by intro a b; exact e.map_rel_iff⟩

/-- Assemble a graph isomorphism from a bijection of components and maps on those components. -/
noncomputable def isoOfComponents (G : SimpleGraph α) (H : SimpleGraph β)
    (e : G.ConnectedComponent ≃ H.ConnectedComponent)
    (f : ∀ c, c.toSimpleGraph ≃g (e c).toSimpleGraph) : G ≃g H := by
  let split {δ : Type} (K : SimpleGraph δ) : (Σ c : K.ConnectedComponent, c.supp) ≃ δ :=
    Equiv.sigmaFiberEquiv K.connectedComponentMk
  refine ⟨(split G).symm.trans ((Equiv.sigmaCongr e fun c => (f c).toEquiv).trans (split H)), ?_⟩
  intro a b
  let ca := G.connectedComponentMk a
  let cb := G.connectedComponentMk b
  let va : ca.supp := ⟨a, rfl⟩
  let vb : cb.supp := ⟨b, rfl⟩
  change H.Adj (f ca va).1 (f cb vb).1 ↔ G.Adj a b
  by_cases hab : ca = cb
  · have hfun (c d : G.ConnectedComponent) (h : c = d)
        (hc : G.connectedComponentMk b = c) (hd : G.connectedComponentMk b = d) :
        (f c ⟨b, hc⟩).1 = (f d ⟨b, hd⟩).1 := by subst d; rfl
    have hfv : (f ca ⟨b, hab.symm⟩).1 = (f cb vb).1 := hfun _ _ hab _ _
    rw [← hfv]
    exact (f ca).map_rel_iff
  · have hG : ¬ G.Adj a b := fun h => hab (ConnectedComponent.connectedComponentMk_eq_of_adj h)
    have hH : ¬ H.Adj (f ca va).1 (f cb vb).1 := by
      intro h
      apply hab
      apply e.injective
      exact (f ca va).2.symm.trans ((ConnectedComponent.connectedComponentMk_eq_of_adj h).trans (f cb vb).2)
    exact iff_of_false hH hG

private abbrev witness (G : SimpleGraph α) (A : SimpleGraph β) :=
  { c : G.ConnectedComponent // Nonempty (c.toSimpleGraph ≃g A) }

private theorem cardWitness_components (G : SimpleGraph α) (H : SimpleGraph β) [Finite α] [Finite β]
    (e : G ≃g H) (A : SimpleGraph γ) : Nat.card (witness G A) = Nat.card (witness H A) := by
  refine Nat.card_congr (e.connectedComponentEquiv.subtypeEquiv fun c => ?_)
  exact ⟨fun ⟨f⟩ => ⟨(isoComponent G H e c).symm.trans f⟩,
    fun ⟨f⟩ => ⟨(isoComponent G H e c).trans f⟩⟩

private theorem graphClass_eq_mk_iff (G : SimpleGraph α) [Finite α] (A : FiniteGraph) :
    graphClass G = Quotient.mk graphSetoid A ↔ Nonempty (G ≃g A.2) := by
  rw [graphClass, Quotient.eq]
  constructor
  · rintro ⟨e⟩
    exact ⟨(finModelIso G).symm.trans e⟩
  · rintro ⟨e⟩
    exact ⟨(finModelIso G).trans e⟩

private noncomputable def equivCard {δ ε : Type} [Finite δ] [Finite ε]
    (h : Nat.card δ = Nat.card ε) : δ ≃ ε := by
  letI := Fintype.ofFinite δ
  letI := Fintype.ofFinite ε
  exact Fintype.equivOfCardEq (by simpa only [Fintype.card_eq_nat_card] using h)

private theorem equalOfCounts (G : SimpleGraph α) (H : SimpleGraph β) [Finite α] [Finite β]
    (h : ∀ (n : ℕ) (A : SimpleGraph (Fin n)), Nat.card (witness G A) = Nat.card (witness H A)) :
    Nonempty (G ≃g H) := by
  classical
  let f (c : G.ConnectedComponent) := graphClass c.toSimpleGraph
  let g (c : H.ConnectedComponent) := graphClass c.toSimpleGraph
  have hm (c : GraphClass) : Nonempty ({x // f x = c} ≃ {y // g y = c}) := by
    refine Quotient.inductionOn c ?_
    intro A
    let toWitness (K : SimpleGraph α) (x : K.ConnectedComponent) :=
      graphClass_eq_mk_iff x.toSimpleGraph A
    let eG : {x // f x = Quotient.mk graphSetoid A} ≃ witness G A.2 :=
      (Equiv.refl _).subtypeEquiv (toWitness G)
    let eH : {x // g x = Quotient.mk graphSetoid A} ≃ witness H A.2 :=
      (Equiv.refl _).subtypeEquiv fun x => graphClass_eq_mk_iff x.toSimpleGraph A
    exact ⟨eG.trans ((equivCard (h A.1 A.2)).trans eH.symm)⟩
  let e := Equiv.ofFiberEquiv fun c => (hm c).some
  refine ⟨isoOfComponents G H e fun c => Classical.choice ?_⟩
  exact (graphClass_eq_iff _ _).mp (Equiv.ofFiberEquiv_map (fun x => (hm x).some) c).symm

private abbrev small (G : SimpleGraph α) (n : ℕ) :=
  {c : G.ConnectedComponent // Nat.card (↥c) < n}

private noncomputable def smallIso (G : SimpleGraph α) (H : SimpleGraph β) [Finite α] [Finite β]
    (n : ℕ) (h : ∀ (m : ℕ) (_ : m < n) (A : SimpleGraph (Fin m)),
      Nat.card (witness G A) = Nat.card (witness H A)) :
    {e : small G n ≃ small H n //
      ∀ c, Nonempty (c.1.toSimpleGraph ≃g (e c).1.toSimpleGraph)} := by
  classical
  let f (c : small G n) := graphClass c.1.toSimpleGraph
  let g (c : small H n) := graphClass c.1.toSimpleGraph
  have hm (c : GraphClass) : Nonempty ({x // f x = c} ≃ {y // g y = c}) := by
    refine Quotient.inductionOn c ?_
    intro A
    by_cases ha : A.1 < n
    · have witnessFiber {δ : Type} [Finite δ] (K : SimpleGraph δ) :
          {x : small K n // graphClass x.1.toSimpleGraph = Quotient.mk graphSetoid A} ≃ witness K A.2 := {
        toFun := fun x => ⟨x.1.1, (graphClass_eq_mk_iff _ A).mp x.2⟩
        invFun := fun x =>
          let he : Nat.card (↥x.1) = Nat.card (Fin A.1) := Nat.card_congr x.2.some.toEquiv
          ⟨⟨x.1, he.trans_lt (by simpa using ha)⟩, (graphClass_eq_mk_iff _ A).mpr x.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
      exact ⟨(witnessFiber G).trans ((equivCard (h A.1 ha A.2)).trans (witnessFiber H).symm)⟩
    · have fiberEmpty {δ : Type} [Finite δ] (K : SimpleGraph δ) :
          IsEmpty {x : small K n // graphClass x.1.toSimpleGraph = Quotient.mk graphSetoid A} :=
        ⟨fun x => ha (by
          have he : Nat.card (↥x.1.1) = Nat.card (Fin A.1) :=
            Nat.card_congr ((graphClass_eq_mk_iff _ A).mp x.2).some.toEquiv
          simpa [he] using x.1.2)⟩
      let := fiberEmpty G
      let := fiberEmpty H
      exact ⟨Equiv.equivOfIsEmpty _ _⟩
  let e := Equiv.ofFiberEquiv fun c => (hm c).some
  exact ⟨e, fun c => (graphClass_eq_iff _ _).mp (Equiv.ofFiberEquiv_map (fun x => (hm x).some) c).symm⟩

private abbrev productWitness {δ : Type} (C : SimpleGraph δ) (Y : SimpleGraph β)
    (A : SimpleGraph γ) :=
  {e : Y.ConnectedComponent // Nonempty (SimpleGraph.boxProd C e.toSimpleGraph ≃g A)}

private theorem cardProductWitness (X : SimpleGraph α) (Y : SimpleGraph β) [Finite α] [Finite β]
    [Fintype X.ConnectedComponent] (A : SimpleGraph γ) :
    Nat.card (witness (SimpleGraph.boxProd X Y) A) =
      ∑ c : X.ConnectedComponent, Nat.card (productWitness c.toSimpleGraph Y A) := by
  let e : witness (SimpleGraph.boxProd X Y) A ≃ { x : X.ConnectedComponent × Y.ConnectedComponent //
      Nonempty (SimpleGraph.boxProd x.1.toSimpleGraph x.2.toSimpleGraph ≃g A) } :=
    (productComponents X Y).subtypeEquiv
    (fun c => ⟨fun ⟨f⟩ => ⟨(productComponentIso X Y c).symm.trans f⟩,
      fun ⟨f⟩ => ⟨(productComponentIso X Y c).trans f⟩⟩)
  let split : { x : X.ConnectedComponent × Y.ConnectedComponent //
      Nonempty (SimpleGraph.boxProd x.1.toSimpleGraph x.2.toSimpleGraph ≃g A) } ≃
      (Σ c : X.ConnectedComponent, productWitness c.toSimpleGraph Y A) := {
    toFun := fun x => ⟨x.1.1, ⟨x.1.2, x.2⟩⟩
    invFun := fun x => ⟨(x.1, x.2.1), x.2.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  rw [Nat.card_congr (e.trans split), Nat.card_sigma]

/-- Projection onto the second factor is a graph isomorphism when the first has one vertex. -/
noncomputable def singletonProduct (X : SimpleGraph α) (Y : SimpleGraph β)
    (h : Nat.card α = 1) : SimpleGraph.boxProd X Y ≃g Y := by
  let a := Classical.choose (Nat.card_eq_one_iff_exists.mp h)
  have ha := Classical.choose_spec (Nat.card_eq_one_iff_exists.mp h)
  let e : α × β ≃ β := {
    toFun := Prod.snd
    invFun := fun b => (a, b)
    left_inv := fun b => Prod.ext (ha b.1).symm rfl
    right_inv := fun _ => rfl }
  refine ⟨e, ?_⟩
  intro u v
  change Y.Adj u.2 v.2 ↔ (SimpleGraph.boxProd X Y).Adj u v
  have hEq : u.1 = v.1 := (ha _).trans (ha _).symm
  simp [boxProd_adj, hEq]

private theorem cardProductWitness_singleton {δ : Type} (C : SimpleGraph δ) (Y : SimpleGraph β)
    (A : SimpleGraph γ) (h : Nat.card δ = 1) :
    Nat.card (productWitness C Y A) = Nat.card (witness Y A) := by
  refine Nat.card_congr ((Equiv.refl _).subtypeEquiv fun c => ?_)
  let e := singletonProduct C c.toSimpleGraph h
  exact ⟨fun ⟨f⟩ => ⟨e.symm.trans f⟩, fun ⟨f⟩ => ⟨e.trans f⟩⟩

private theorem productWitness_smaller {δ : Type} [Finite δ] (C : SimpleGraph δ) (Y : SimpleGraph β)
    [Finite β] {n : ℕ} (A : SimpleGraph (Fin n)) (h : 1 < Nat.card δ)
    (c : productWitness C Y A) : Nat.card (↥c.1) < n := by
  have hc : Nat.card δ * Nat.card (↥c.1) = n := by
    simpa [Nat.card_prod] using Nat.card_congr c.2.some.toEquiv
  let : Nonempty (↥c.1) := c.1.nonempty_supp.to_subtype
  exact (lt_mul_of_one_lt_left Nat.card_pos h).trans_eq hc

private theorem cardProductWitness_larger {δ : Type} [Finite δ] (C : SimpleGraph δ)
    (Y : SimpleGraph β) (Z : SimpleGraph γ) [Finite β] [Finite γ]
    {n : ℕ} (A : SimpleGraph (Fin n)) (h : 1 < Nat.card δ)
    (prior : ∀ (m : ℕ) (_ : m < n) (B : SimpleGraph (Fin m)),
      Nat.card (witness Y B) = Nat.card (witness Z B)) :
    Nat.card (productWitness C Y A) = Nat.card (productWitness C Z A) := by
  let restr {ε : Type} [Finite ε] (K : SimpleGraph ε) :
      productWitness C K A ≃
        {x : small K n // Nonempty (SimpleGraph.boxProd C x.1.toSimpleGraph ≃g A)} := {
    toFun := fun c => ⟨⟨c.1, productWitness_smaller C K A h c⟩, c.2⟩
    invFun := fun c => ⟨c.1.1, c.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  let e := smallIso Y Z n prior
  refine Nat.card_congr ((restr Y).trans ((e.1.subtypeEquiv fun c => ?_).trans (restr Z).symm))
  have g := (e.2 c).some
  let f : SimpleGraph.boxProd C c.1.toSimpleGraph ≃g SimpleGraph.boxProd C (e.1 c).1.toSimpleGraph :=
    ⟨(Equiv.refl _).prodCongr g.toEquiv, by
      intro u v
      change (C.Adj u.1 v.1 ∧ g u.2 = g v.2 ∨
        (e.1 c).1.toSimpleGraph.Adj (g u.2) (g v.2) ∧ u.1 = v.1) ↔
        (C.Adj u.1 v.1 ∧ u.2 = v.2 ∨ c.1.toSimpleGraph.Adj u.2 v.2 ∧ u.1 = v.1)
      rw [g.injective.eq_iff, g.map_rel_iff]⟩
  exact ⟨fun ⟨i⟩ => ⟨f.symm.trans i⟩, fun ⟨i⟩ => ⟨f.trans i⟩⟩

private theorem component_card_pos {X : SimpleGraph α} [Finite α] (c : X.ConnectedComponent) :
    0 < Nat.card (↥c) := by
  let : Nonempty (↥c) := c.nonempty_supp.to_subtype
  exact Nat.card_pos

private theorem singleton_component (X : SimpleGraph α) (a : α) (ha : ∀ b, ¬ X.Adj a b) :
    Nat.card (↥(X.connectedComponentMk a)) = 1 := by
  refine Nat.card_eq_one_iff_exists.mpr ⟨⟨a, rfl⟩, ?_⟩
  rintro ⟨b, hb⟩
  apply Subtype.ext
  have hr := ConnectedComponent.exact hb.symm
  obtain ⟨w⟩ := hr
  cases w with
  | nil => rfl
  | cons h _ => exact (ha _ h).elim

/-- A graph with an isolated vertex can be cancelled from a finite Cartesian product. -/
theorem cancel_of_isolated (X : SimpleGraph α) (Y : SimpleGraph β) (Z : SimpleGraph γ)
    [Finite α] [Finite β] [Finite γ] (a : α) (ha : ∀ b, ¬ X.Adj a b)
    (h : Nonempty (SimpleGraph.boxProd X Y ≃g SimpleGraph.boxProd X Z)) : Nonempty (Y ≃g Z) := by
  classical
  let := Fintype.ofFinite X.ConnectedComponent
  apply equalOfCounts
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro A
    let w (c : X.ConnectedComponent) : ℕ := if Nat.card (↥c) = 1 then 1 else 0
    let rest {δ : Type} (K : SimpleGraph δ) (c : X.ConnectedComponent) : ℕ :=
      if Nat.card (↥c) = 1 then 0 else Nat.card (productWitness c.toSimpleGraph K A)
    have split {δ : Type} [Finite δ] (K : SimpleGraph δ) :
        Nat.card (witness (SimpleGraph.boxProd X K) A) =
          (∑ c : X.ConnectedComponent, w c) * Nat.card (witness K A) +
            ∑ c : X.ConnectedComponent, rest K c := by
      rw [cardProductWitness, Finset.sum_mul, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro c _
      by_cases hc : Nat.card (↥c) = 1
      · simp [rest, w, hc, cardProductWitness_singleton _ _ _ hc]
      · simp [rest, w, hc]
    have sameRest : (∑ c : X.ConnectedComponent, rest Y c) =
        ∑ c : X.ConnectedComponent, rest Z c := by
      apply Finset.sum_congr rfl
      intro c _
      by_cases hc : Nat.card (↥c) = 1
      · simp [rest, hc]
      · simpa [rest, hc] using
          cardProductWitness_larger c.toSimpleGraph Y Z A (by
            have := component_card_pos c
            omega) (fun m hm B => ih m hm B)
    have hc := cardWitness_components (SimpleGraph.boxProd X Y) (SimpleGraph.boxProd X Z) h.some A
    rw [split Y, split Z, sameRest] at hc
    have pos : 0 < ∑ c : X.ConnectedComponent, w c := by
      have hs : w (X.connectedComponentMk a) = 1 := by
        simp [w, singleton_component X a ha]
      have hb : w (X.connectedComponentMk a) ≤ ∑ c : X.ConnectedComponent, w c :=
        Finset.single_le_sum (fun c _ => Nat.zero_le (w c)) (Finset.mem_univ _)
      omega
    exact Nat.eq_of_mul_eq_mul_left pos (Nat.add_right_cancel hc)

end McKayCancel

open SimpleGraph OMA.S_mo_495000
namespace McKay
variable {V W A B : Type}

def Occurs (G : SimpleGraph V) (T : SimpleGraph W) : Prop :=
  ∃ d : G.ConnectedComponent, Nonempty (d.toSimpleGraph ≃g T)

theorem occurs_host {G : SimpleGraph V} {H : SimpleGraph W} {T : SimpleGraph A}
    (e : G ≃g H) : Occurs G T → Occurs H T := by
  rintro ⟨d, ⟨f⟩⟩
  exact ⟨_, ⟨(componentIso e d).symm.trans f⟩⟩

theorem occurs_type {G : SimpleGraph V} {T : SimpleGraph W} {T' : SimpleGraph A}
    (e : T ≃g T') : Occurs G T → Occurs G T' := by
  rintro ⟨d, ⟨f⟩⟩
  exact ⟨d, ⟨f.trans e⟩⟩

theorem occurs_component {G : SimpleGraph V} (d : G.ConnectedComponent) :
    Occurs G d.toSimpleGraph := ⟨d, ⟨.refl⟩⟩

theorem occurs_box {G : SimpleGraph V} {H : SimpleGraph W} {P : SimpleGraph A} {Q : SimpleGraph B}
    (hG : Occurs G P) (hH : Occurs H Q) : Occurs (SimpleGraph.boxProd G H) (SimpleGraph.boxProd P Q) := by
  obtain ⟨c, ⟨e⟩⟩ := hG
  obtain ⟨d, ⟨f⟩⟩ := hH
  obtain ⟨k, hk⟩ := (McKayCancel.productComponents G H).surjective (c,d)
  have h := McKayCancel.productComponentIso G H k
  rw [hk] at h
  exact ⟨k, ⟨h.trans (boxCongr e f)⟩⟩

def boxRightOne (G : SimpleGraph V) (H : SimpleGraph W) [Unique W] : SimpleGraph.boxProd G H ≃g G where
  toEquiv := ⟨Prod.fst, fun u => (u, default), fun p => Prod.ext rfl (Subsingleton.elim _ _), fun _ => rfl⟩
  map_rel_iff' := by
    intro p q
    change G.Adj p.1 q.1 ↔ _
    have he : p.2 = q.2 := Subsingleton.elim _ _
    simp [boxProd_adj, he]

theorem full_empty_isolated (G : SimpleGraph V) : (fullGraph G).IsIsolated ∅ := by
  rintro t ⟨u, v, _, h, _⟩
  simp at h

theorem full_one (G : SimpleGraph V) : Occurs (fullGraph G) (⊥ : SimpleGraph Unit) := by
  let d := (fullGraph G).connectedComponentMk ∅
  have he : ∀ a : d, (a : Set V) = ∅ := by
    rintro ⟨s, hs⟩
    obtain ⟨p⟩ := (ConnectedComponent.eq.mp hs).symm
    cases p with
    | nil => rfl
    | cons h _ => exact False.elim (full_empty_isolated G _ h)
  letI : Unique d := { default := ⟨∅, rfl⟩, uniq := fun a => Subtype.ext (he a) }
  refine ⟨d, ⟨⟨Equiv.ofUnique _ _, ?_⟩⟩⟩
  intro a b
  rw [Subsingleton.elim a b]
  simp

theorem liftLeft {G : SimpleGraph V} {H : SimpleGraph W} {T : SimpleGraph A}
    (h : Occurs (fullGraph G) T) : Occurs (SimpleGraph.boxProd (fullGraph G) (fullGraph H)) T :=
  occurs_type (boxRightOne T _) (occurs_box h (full_one H))

theorem liftRight {G : SimpleGraph V} {H : SimpleGraph W} {T : SimpleGraph A}
    (h : Occurs (fullGraph H) T) : Occurs (SimpleGraph.boxProd (fullGraph G) (fullGraph H)) T :=
  occurs_host (SimpleGraph.boxProdComm _ _) (liftLeft h)

def Lower (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ (A : Type) [Finite A] (T : SimpleGraph A), Occurs G T → 1 < Nat.card A → k ≤ Nat.card A

theorem lower_host {G : SimpleGraph V} {H : SimpleGraph W} {k} (e : G ≃g H) (h : Lower H k) :
    Lower G k := fun _ _ _ hT hcard => h _ _ (occurs_host e hT) hcard

theorem lower_left {G : SimpleGraph V} {H : SimpleGraph W} {k}
    (h : Lower (SimpleGraph.boxProd (fullGraph G) (fullGraph H)) k) : Lower (fullGraph G) k :=
  fun _ _ _ hT hcard => h _ _ (liftLeft hT) hcard

theorem lower_right {G : SimpleGraph V} {H : SimpleGraph W} {k}
    (h : Lower (SimpleGraph.boxProd (fullGraph G) (fullGraph H)) k) : Lower (fullGraph H) k :=
  fun _ _ _ hT hcard => h _ _ (liftRight hT) hcard

theorem component_pos {G : SimpleGraph V} [Finite V] (d : G.ConnectedComponent) :
    0 < Nat.card d := by
  haveI := d.nonempty_supp.to_subtype
  exact Nat.card_pos

def Factor (G : SimpleGraph V) (T : SimpleGraph A) : Prop :=
  ∃ (R : Type) (_ : Finite R) (K : SimpleGraph R), Nonempty (T ⊕g K ≃g G)

def sumSwap (G : SimpleGraph V) (H : SimpleGraph W) (K : SimpleGraph A) :
    G ⊕g (H ⊕g K) ≃g H ⊕g (G ⊕g K) :=
  Iso.sumAssoc.symm.trans ((Iso.sumCongr Iso.sumComm Iso.refl).trans Iso.sumAssoc)

end McKay

namespace OMA.S_mo_495000

open Set SimpleGraph

private theorem swap_reachable {V : Type} [DecidableEq V] (C : SimpleGraph V)
    {u v : V} (huv : C.Adj u v) (S : Set V) :
    (fullGraph C).Reachable S (Equiv.swap u v '' S) := by
  have hne := huv.ne
  by_cases hu : u ∈ S <;> by_cases hv : v ∈ S
  · have he : Equiv.swap u v '' S = S := by
      ext x
      simp only [Set.mem_image_equiv, Equiv.symm_swap, Equiv.swap_apply_def]
      split_ifs <;> simp_all
    rw [he]
  · apply Adj.reachable
    refine ⟨u, v, huv, ?_, ?_⟩ <;> ext x <;>
      simp only [Set.mem_sdiff, Set.mem_image_equiv, Equiv.symm_swap,
        Equiv.swap_apply_def, Set.mem_singleton_iff] <;>
      split_ifs <;> simp_all
  · apply Adj.reachable
    refine ⟨v, u, huv.symm, ?_, ?_⟩ <;> ext x <;>
      simp only [Set.mem_sdiff, Set.mem_image_equiv, Equiv.symm_swap,
        Equiv.swap_apply_def, Set.mem_singleton_iff] <;>
      split_ifs <;> simp_all
  · have he : Equiv.swap u v '' S = S := by
      ext x
      simp only [Set.mem_image_equiv, Equiv.symm_swap, Equiv.swap_apply_def]
      split_ifs <;> simp_all
    rw [he]

private theorem reachable_image {V : Type} [Finite V] (C : SimpleGraph V)
    (hc : C.Connected) (p : Equiv.Perm V) (S : Set V) :
    (fullGraph C).Reachable S (p '' S) := by
  classical
  let E : Set (Equiv.Perm V) := {p | ∃ u v, C.Adj u v ∧ p = Equiv.swap u v}
  have edge (u v : V) (h : C.Adj u v) :
      Equiv.swap u v ∈ Submonoid.closure E := Submonoid.subset_closure ⟨u, v, h, rfl⟩
  have walk_mem {u v : V} (w : C.Walk u v) :
      Equiv.swap u v ∈ Submonoid.closure E := by
    induction w with
    | nil =>
      rw [Equiv.swap_self]
      exact one_mem (Submonoid.closure E)
    | cons h _ ih => exact SubmonoidClass.swap_mem_trans _ (edge _ _ h) ih
  have all_swap (u v : V) : Equiv.swap u v ∈ Submonoid.closure E :=
    (hc.preconnected u v).elim walk_mem
  have htop : Submonoid.closure E = ⊤ := by
    apply top_unique
    rw [← Equiv.Perm.mclosure_isSwap]
    refine Submonoid.closure_le.mpr ?_
    rintro _ ⟨u, v, _, rfl⟩
    exact all_swap u v
  have hp : p ∈ Submonoid.closure E := by simp [htop]
  suffices h : ∀ S : Set V, (fullGraph C).Reachable S (p '' S) by exact h S
  induction hp using Submonoid.closure_induction with
  | mem q hq =>
    obtain ⟨u, v, he, rfl⟩ := hq
    exact swap_reachable C he
  | one =>
    intro S
    have he : (1 : Equiv.Perm V) '' S = S := by simp
    rw [he]
  | mul p q _ _ hp hq =>
    intro S
    have he : (p * q) '' S = p '' (q '' S) := by
      rw [← Set.image_comp]
      rfl
    rw [he]
    exact (hq S).trans (hp (q '' S))

private theorem image_of_rank_eq {V : Type} [Finite V] {S T : Set V}
    (h : S.ncard = T.ncard) : ∃ p : Equiv.Perm V, p '' S = T := by
  classical
  let := Fintype.ofFinite S
  let := Fintype.ofFinite T
  let := Fintype.ofFinite (Sᶜ : Set V)
  let := Fintype.ofFinite (Tᶜ : Set V)
  let e : S ≃ T := Fintype.equivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq,
      Nat.card_coe_set_eq]
    exact h)
  let f : (Sᶜ : Set V) ≃ (Tᶜ : Set V) := Fintype.equivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq,
      Nat.card_coe_set_eq, Set.ncard_compl, Set.ncard_compl, h])
  let p := (Equiv.sumCompl (· ∈ S)).symm.trans
     ((Equiv.sumCongr e f).trans (Equiv.sumCompl (· ∈ T)))
  refine ⟨p, ?_⟩
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    change p a ∈ T
    rw [show p a = (e ⟨a, ha⟩).val by simp [p, Equiv.sumCompl_symm_apply_of_pos ha]; rfl]
    exact (e ⟨a, ha⟩).property
  · intro hx
    refine ⟨(e.symm ⟨x,hx⟩).val, (e.symm ⟨x,hx⟩).property, ?_⟩
    simp [p, Equiv.sumCompl_symm_apply_of_pos (e.symm ⟨x,hx⟩).property]
    rfl

private theorem adj_rank_eq {V : Type} [Finite V] (C : SimpleGraph V)
    {S T : Set V} (h : (fullGraph C).Adj S T) : S.ncard = T.ncard := by
  obtain ⟨u,v,_, hS,hT⟩ := h
  have first := Set.ncard_union_eq (s := S \ T) (t := S ∩ T) (Set.disjoint_left.mpr fun _ ha hb => ha.2 hb.2)
  have second := Set.ncard_union_eq (s := T \ S) (t := T ∩ S) (Set.disjoint_left.mpr fun _ ha hb => ha.2 hb.2)
  rw [Set.sdiff_union_inter, hS, Set.ncard_singleton] at first
  rw [Set.sdiff_union_inter, hT, Set.ncard_singleton, inter_comm] at second
  exact first.trans second.symm

/-- Reachability in the full token graph is equality of token counts. -/
theorem fullGraph_reachable_iff {V : Type} [Finite V] (C : SimpleGraph V)
    (hc : C.Connected) (S T : Set V) :
    (fullGraph C).Reachable S T ↔ S.ncard = T.ncard := by
  constructor
  · rintro ⟨w⟩
    induction w with
    | nil => rfl
    | cons h _ ih => exact (adj_rank_eq C h).trans ih
  · intro h
    obtain ⟨p, rfl⟩ := image_of_rank_eq h
    exact reachable_image C hc p S


private theorem mem_layer {V : Type} [Finite V] (C : SimpleGraph V)
    (hc : C.Connected) (S T : Set V) :
    S ∈ ((fullGraph C).connectedComponentMk T).supp ↔ S.ncard = T.ncard := by
  rw [ConnectedComponent.mem_supp_iff, ConnectedComponent.eq, fullGraph_reachable_iff C hc]

private theorem card_layer {V : Type} [Finite V] (C : SimpleGraph V)
    (hc : C.Connected) (T : Set V) :
    Nat.card ((fullGraph C).connectedComponentMk T) = (Nat.card V).choose T.ncard := by
  classical
  let : Fintype V := Fintype.ofFinite V
  let e : ((fullGraph C).connectedComponentMk T) ≃
      (Finset.univ.powersetCard T.ncard : Finset (Finset V)) := {
    toFun := fun S => ⟨S.val.toFinite.toFinset, Finset.mem_powersetCard.mpr
      ⟨Finset.subset_univ _, (Set.ncard_eq_toFinset_card S.val).symm.trans
        ((mem_layer C hc S.val T).mp S.property)⟩⟩
    invFun := fun S => ⟨S.val, (mem_layer C hc _ T).mpr (by
      simpa using (Finset.mem_powersetCard.mp S.property).2)⟩
    left_inv := fun S => Subtype.ext (by simp)
    right_inv := fun S => Subtype.ext (Finset.coe_injective (Set.Finite.coe_toFinset _))
  }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe,
    Finset.card_powersetCard, Finset.card_univ, Nat.card_eq_fintype_card]

private theorem choose_inner {n k : ℕ} (hk : 2 ≤ k) (hk' : k ≤ n / 2) :
    n < n.choose k := by
  have hn : 4 ≤ n := by omega
  have hbase : n < n.choose 2 := by
    rw [Nat.choose_two_right]
    have hmul : n * 3 ≤ n * (n - 1) := Nat.mul_le_mul_left n (by omega)
    omega
  induction k with
  | zero => omega
  | succ k ih =>
    rcases eq_or_lt_of_le hk with eq | lt
    · simpa [← eq] using hbase
    · exact (ih (by omega) (by omega)).trans_le (Nat.choose_le_succ_of_lt_half_left (by omega))

private theorem layer_order_cases {n k : ℕ} (hk : k ≤ n) :
    n.choose k = 1 ∨ (n ≤ n.choose k ∧
      (n.choose k = n → k = 1 ∨ n - k = 1)) := by
  by_cases hz : k = 0
  · exact Or.inl (by simp [hz])
  by_cases hn : k = n
  · exact Or.inl (by simp [hn])
  right
  by_cases ho : k = 1
  · simp [ho]
  by_cases hp : n-k = 1
  · rw [← Nat.choose_symm hk, hp, Nat.choose_one_right]
    omega
  have hs : n < n.choose k := by
    by_cases hm : k ≤ n / 2
    · exact choose_inner (by omega) hm
    · rw [← Nat.choose_symm hk]
      exact choose_inner (by omega) (by omega)
  exact ⟨hs.le, fun he => (hs.ne he.symm).elim⟩

private theorem singleton_adj {V : Type} (C : SimpleGraph V) (u v : V) :
    (fullGraph C).Adj ({u} : Set V) {v} ↔ C.Adj u v := by
  classical
  by_cases h : u = v
  · subst v
    simp
  constructor
  · rintro ⟨a,b,hab,ha,hb⟩
    have h₁ : a = u := by
      have : a ∈ ({u} : Set V) \ {v} := by rw [ha]; simp
      exact Set.mem_singleton_iff.mp this.1
    have h₂ : b = v := by
      have : b ∈ ({v} : Set V) \ {u} := by rw [hb]; simp
      exact Set.mem_singleton_iff.mp this.1
    simpa [h₁,h₂] using hab
  · intro hab
    refine ⟨u,v,hab,?_,?_⟩ <;> ext x <;> simp [h, Ne.symm h]

private theorem fullGraph_compl_adj {V : Type} (C : SimpleGraph V) (S T : Set V) :
    (fullGraph C).Adj Sᶜ Tᶜ ↔ (fullGraph C).Adj S T := by
  have h₁ : Sᶜ \ Tᶜ = T \ S := by ext x; simp [and_comm]
  have h₂ : Tᶜ \ Sᶜ = S \ T := by ext x; simp [and_comm]
  change (∃ u v, C.Adj u v ∧ Sᶜ \ Tᶜ = {u} ∧ Tᶜ \ Sᶜ = {v}) ↔ _
  rw [h₁,h₂]
  constructor <;> rintro ⟨u,v,h,hu,hv⟩ <;> exact ⟨v,u,h.symm,hv,hu⟩

private theorem singleton_layer {V : Type} [Finite V] (C : SimpleGraph V)
    (hc : C.Connected) (T : Set V) (h : T.ncard = 1) :
    Nonempty (((fullGraph C).connectedComponentMk T).toSimpleGraph ≃g C) := by
  classical
  let f (v : V) : ((fullGraph C).connectedComponentMk T) :=
    ⟨{v}, (mem_layer C hc _ T).mpr (by simp [h])⟩
  have hf : Function.Bijective f := by
    constructor
    · intro u v huv
      simpa [f] using congrArg Subtype.val huv
    · intro S
      have hS := ((mem_layer C hc _ T).mp S.property).trans h
      obtain ⟨v,hv⟩ := Set.ncard_eq_one.mp hS
      exact ⟨v, Subtype.ext hv.symm⟩
  let e : C ≃g ((fullGraph C).connectedComponentMk T).toSimpleGraph := {
    toEquiv := Equiv.ofBijective f hf
    map_rel_iff' := by intro u v; exact singleton_adj C u v
  }
  exact ⟨e.symm⟩

private theorem cosingleton_layer {V : Type} [Finite V] (C : SimpleGraph V)
    (hc : C.Connected) (T : Set V) (h : Nat.card V - T.ncard = 1) :
    Nonempty (((fullGraph C).connectedComponentMk T).toSimpleGraph ≃g C) := by
  classical
  have hT : T.ncard ≤ Nat.card V := by
    simpa using (Set.ncard_le_ncard T.subset_univ)
  let f (v : V) : ((fullGraph C).connectedComponentMk T) :=
    ⟨({v} : Set V)ᶜ, (mem_layer C hc _ T).mpr (by rw [Set.ncard_compl, Set.ncard_singleton]; omega)⟩
  have hf : Function.Bijective f := by
    constructor
    · intro u v huv
      simpa [f] using congrArg Subtype.val huv
    · intro S
      have hS := (mem_layer C hc _ T).mp S.property
      have hSc : (S.valᶜ).ncard = 1 := by rw [Set.ncard_compl, hS, h]
      obtain ⟨v,hv⟩ := Set.ncard_eq_one.mp hSc
      exact ⟨v, Subtype.ext (by
        change ({v} : Set V)ᶜ = S.val
        rw [← hv, compl_compl])⟩
  let e : C ≃g ((fullGraph C).connectedComponentMk T).toSimpleGraph := {
    toEquiv := Equiv.ofBijective f hf
    map_rel_iff' := by
      intro u v
      exact (fullGraph_compl_adj C {u} {v}).trans (singleton_adj C u v)
  }
  exact ⟨e.symm⟩

/-- The nontrivial layers have at least the order of the connected original graph.
The smallest order is reached by a layer isomorphic to the original graph. -/
theorem fullGraph_component_layers {V : Type} [Finite V] (C : SimpleGraph V)
    (hc : C.Connected) :
    (∀ D : (fullGraph C).ConnectedComponent,
      (Nat.card D = 1 ∨ Nat.card V ≤ Nat.card D) ∧
      (2 ≤ Nat.card D → Nat.card D = Nat.card V → Nonempty (D.toSimpleGraph ≃g C))) ∧
    (∃ D : (fullGraph C).ConnectedComponent, Nonempty (D.toSimpleGraph ≃g C)) := by
  constructor
  · refine ConnectedComponent.ind ?_
    intro T
    have hT : T.ncard ≤ Nat.card V := by
      simpa using (Set.ncard_le_ncard T.subset_univ)
    have hcard := card_layer C hc T
    rcases layer_order_cases hT with h | ⟨h, he⟩
    · have hD : Nat.card ((fullGraph C).connectedComponentMk T) = 1 := hcard.trans h
      refine ⟨Or.inl hD, fun hn _ => False.elim ?_⟩
      rw [hD] at hn
      omega
    · refine ⟨Or.inr (h.trans hcard.ge), fun _ heq => ?_⟩
      rcases he (hcard.symm.trans heq) with hT | hT
      · exact singleton_layer C hc T hT
      · exact cosingleton_layer C hc T hT
  · obtain ⟨v⟩ := hc.nonempty
    exact ⟨(fullGraph C).connectedComponentMk {v}, singleton_layer C hc _ (by simp)⟩


/-- A nontrivial component requires at least two vertices in the original graph. -/
theorem fullGraph_component_nontriv_source {V : Type} [Finite V] (C : SimpleGraph V)
    (hc : C.Connected) (D : (fullGraph C).ConnectedComponent)
    (h : 1 < Nat.card D) : 1 < Nat.card V := by
  by_contra! hn
  revert h
  refine ConnectedComponent.ind ?_ D
  intro T h
  have hk : T.ncard ≤ Nat.card V := by simpa using (Set.ncard_le_ncard T.subset_univ)
  rw [card_layer C hc T] at h
  have hz : T.ncard = 0 ∨ T.ncard = Nat.card V := by omega
  rcases hz with hz | hz <;> simp [hz] at h

end OMA.S_mo_495000

open SimpleGraph OMA.S_mo_495000
namespace McKay

private noncomputable def removeOne {V W : Type} (G : SimpleGraph V) (H : SimpleGraph W)
    (h : Nat.card W = 1) : SimpleGraph.boxProd G H ≃g G := by
  let w := (Nat.card_eq_one_iff_exists.mp h).choose
  letI : Unique W := ⟨⟨w⟩, (Nat.card_eq_one_iff_exists.mp h).choose_spec⟩
  exact boxRightOne G H

/-- A smallest nontrivial component of the full move graph is an original component. -/
theorem extract {A : Type} [Finite A] (T : SimpleGraph A) (hbig : 1 < Nat.card A) :
    ∀ n (V : Type) [Finite V] (G : SimpleGraph V), Nat.card V = n →
    Occurs (fullGraph G) T → Lower (fullGraph G) (Nat.card A) → Factor G T := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V _ G hn hT hmin
    cases isEmpty_or_nonempty V with
    | inl h =>
      obtain ⟨d, ⟨e⟩⟩ := hT
      have hd : Subsingleton (Set V) := ⟨fun s t => Set.ext (fun v => isEmptyElim v)⟩
      have := d.nonempty_supp.to_subtype
      have ho := Nat.card_congr e.toEquiv
      have h1 : Nat.card d = 1 := Nat.card_unique
      omega
    | inr h =>
      let c := G.connectedComponentMk (Classical.choice h)
      let K := G.induce c.suppᶜ
      let e : c.toSimpleGraph ⊕g K ≃g G := splitComponent c
      let iso := (fullSum c.toSimpleGraph K).trans (fullCongr e)
      have low := lower_host iso hmin
      obtain ⟨d, ⟨f⟩⟩ := occurs_host iso.symm hT
      let L := (McKayCancel.productComponents (fullGraph c.toSimpleGraph) (fullGraph K) d).1
      let R := (McKayCancel.productComponents (fullGraph c.toSimpleGraph) (fullGraph K) d).2
      let g : T ≃g SimpleGraph.boxProd L.toSimpleGraph R.toSimpleGraph :=
        f.symm.trans (McKayCancel.productComponentIso _ _ d)
      have prodSize : Nat.card A = Nat.card L * Nat.card R :=
        (Nat.card_congr g.toEquiv).trans (Nat.card_prod _ _)
      have hL := component_pos L
      have hR := component_pos R
      by_cases lb : 1 < Nat.card L
      · have hlower := lower_left low _ _ (occurs_component L) lb
        have hr1 : Nat.card R = 1 := by
          by_contra! hne
          have : 2 ≤ Nat.card R := by omega
          nlinarith
        let tL := g.trans (removeOne _ _ hr1)
        have cardAL := Nat.card_congr tL.toEquiv
        have lc := fullGraph_component_layers c.toSimpleGraph c.connected_toSimpleGraph
        have cBig := fullGraph_component_nontriv_source c.toSimpleGraph c.connected_toSimpleGraph L lb
        have ca := lower_left low _ _ lc.2 cBig
        have cb := (lc.1 L).1
        have eqCL : Nat.card L = Nat.card c := by omega
        obtain ⟨tC⟩ := (lc.1 L).2 lb eqCL
        exact ⟨_, inferInstance, K, ⟨(Iso.sumCongr (tL.trans tC) Iso.refl).trans e⟩⟩
      · have hl1 : Nat.card L = 1 := by omega
        let tR := g.trans ((boxProdComm _ _).trans (removeOne _ _ hl1))
        have occ := occurs_type tR.symm (occurs_component R)
        have hc : 0 < Nat.card c := component_pos c
        have sizes : Nat.card c + Nat.card ↥(c.suppᶜ) = n :=
          Nat.card_sum.symm.trans ((Nat.card_congr e.toEquiv).trans hn)
        obtain ⟨U, hU, P, ⟨q⟩⟩ := ih (Nat.card ↥(c.suppᶜ)) (by omega) _ K rfl occ (lower_right low)
        exact ⟨_, inferInstance, c.toSimpleGraph ⊕g P,
          ⟨(sumSwap _ _ _).trans ((Iso.sumCongr Iso.refl q).trans e)⟩⟩

end McKay

namespace OMA.S_mo_495000

private theorem empty_has_no_move {V : Type} (G : SimpleGraph V) (S : Set V) :
    ¬ (fullGraph G).Adj ∅ S := by
  rintro ⟨u, v, huv, h, h'⟩
  have hm : u ∈ ((∅ : Set V) \ S) := by rw [h]; simp
  simp at hm

private theorem univ_has_no_move {V : Type} (G : SimpleGraph V) (S : Set V) :
    ¬ (fullGraph G).Adj Set.univ S := by
  rintro ⟨u, v, huv, h, h'⟩
  have hm : v ∈ S \ (Set.univ : Set V) := by rw [h']; simp
  simp at hm

private noncomputable def subsetWithIsolates (V : Type) [Nonempty V] :
    {S : Set V // S ≠ ∅ ∧ S ≠ Set.univ} ⊕ Bool ≃ Set V := by
  classical
  have hne : (∅ : Set V) ≠ Set.univ := Set.empty_ne_univ
  refine {
    toFun := Sum.elim Subtype.val (fun b => if b then Set.univ else ∅)
    invFun := fun S => if he : S = ∅ then Sum.inr false else
      if hu : S = Set.univ then Sum.inr true else Sum.inl ⟨S, he, hu⟩
    left_inv := ?_
    right_inv := ?_ }
  · intro x
    cases x with
    | inl S => simp [S.property.1, S.property.2]
    | inr b => cases b <;> simp [hne.symm]
  · intro S
    by_cases he : S = ∅
    · simp [he]
    · by_cases hu : S = Set.univ
      · simp [hu, hne.symm]
      · simp [he, hu]

private noncomputable def fullGraphIsoSum {V : Type} [Nonempty V] (G : SimpleGraph V) :
    (powersetGraph G).sum (⊥ : SimpleGraph Bool) ≃g fullGraph G := by
  refine ⟨subsetWithIsolates V, ?_⟩
  have empty_right (S : Set V) : ¬ (fullGraph G).Adj S ∅ :=
    fun h => empty_has_no_move G S h.symm
  have univ_right (S : Set V) : ¬ (fullGraph G).Adj S Set.univ :=
    fun h => univ_has_no_move G S h.symm
  intro a b
  rcases a with S | a <;> rcases b with T | b
  · rfl
  · cases b <;> simp [subsetWithIsolates, SimpleGraph.sum, empty_right, univ_right]
  · cases a <;> simp [subsetWithIsolates, SimpleGraph.sum, empty_has_no_move, univ_has_no_move]
  · cases a <;> cases b <;>
      simp [subsetWithIsolates, SimpleGraph.sum, empty_has_no_move, univ_has_no_move]

/-- An isomorphism of proper move graphs extends to all subsets. -/
theorem fullGraph_iso_of_powersetGraph_iso {V W : Type} [Nonempty V] [Nonempty W]
    {G : SimpleGraph V} {H : SimpleGraph W}
    (h : Nonempty (powersetGraph G ≃g powersetGraph H)) :
    Nonempty (fullGraph G ≃g fullGraph H) := by
  obtain ⟨e⟩ := h
  exact ⟨(fullGraphIsoSum G).symm.trans
    ((e.sumCongr (SimpleGraph.Iso.refl : (⊥ : SimpleGraph Bool) ≃g ⊥)).trans
      (fullGraphIsoSum H))⟩

end OMA.S_mo_495000

open SimpleGraph OMA.S_mo_495000

namespace McKay

variable {V W : Type}

/-- The number of vertices of the full move graph determines the original order. -/
theorem full_order [Finite V] [Finite W] {G : SimpleGraph V} {H : SimpleGraph W}
    (e : fullGraph G ≃g fullGraph H) : Nat.card V = Nat.card W := by
  classical
  let := Fintype.ofFinite V
  let := Fintype.ofFinite W
  have h := Fintype.card_congr e.toEquiv
  rw [Fintype.card_set, Fintype.card_set] at h
  simpa only [Nat.card_eq_fintype_card] using Nat.pow_right_injective (a := 2) le_rfl h

/-- Every original edge gives a move between distinct singleton subsets. -/
theorem edgeless_of_small [Finite V] {G : SimpleGraph V}
    (h : ∀ D : (fullGraph G).ConnectedComponent, Nat.card D ≤ 1) : G = ⊥ := by
  classical
  apply SimpleGraph.eq_bot_iff_forall_not_adj.mpr
  intro u v huv
  have ha : (fullGraph G).Adj ({u} : Set V) {v} := by
    refine ⟨u, v, huv, ?_, ?_⟩ <;> ext x <;> simp [huv.ne, huv.ne.symm]
  let D := (fullGraph G).connectedComponentMk ({u} : Set V)
  let := Fintype.ofFinite D
  have hsub : Subsingleton D := Fintype.card_le_one_iff_subsingleton.mp
    (by simpa only [Nat.card_eq_fintype_card] using h D)
  have he : (fullGraph G).connectedComponentMk ({v} : Set V) = D :=
    (ConnectedComponent.connectedComponentMk_eq_of_adj ha).symm
  have hs : (⟨{u}, rfl⟩ : D) = ⟨{v}, he⟩ := hsub.elim _ _
  exact huv.ne (Set.singleton_injective (congrArg Subtype.val hs))

/-- Two terminal graphs are edgeless, and the full move graph gives their common order. -/
theorem iso_of_small [Finite V] [Finite W] {G : SimpleGraph V} {H : SimpleGraph W}
    (e : fullGraph G ≃g fullGraph H)
    (hG : ∀ D : (fullGraph G).ConnectedComponent, Nat.card D ≤ 1)
    (hH : ∀ D : (fullGraph H).ConnectedComponent, Nat.card D ≤ 1) :
    Nonempty (G ≃g H) := by
  have h := full_order e
  rw [edgeless_of_small hG, edgeless_of_small hH]
  let f := (Finite.equivFin V).trans ((finCongr h).trans (Finite.equivFin W).symm)
  exact ⟨⟨f, by simp⟩⟩

end McKay

open SimpleGraph OMA.S_mo_495000
namespace McKay

/-- Recover all components by cancelling the full move graph of a known component. -/
theorem reconstruct : ∀ n (V : Type) [Finite V] (G : SimpleGraph V),
    Nat.card V = n → ∀ (W : Type) [Finite W] (H : SimpleGraph W),
    Nonempty (fullGraph G ≃g fullGraph H) → Nonempty (G ≃g H) := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V _ G hn W _ H ⟨e⟩
    let hasSize := fun k => ∃ d : (fullGraph G).ConnectedComponent, 1 < Nat.card d ∧ Nat.card d = k
    by_cases hex : ∃ k, hasSize k
    · obtain ⟨d, hd, hsize⟩ := Nat.find_spec hex
      have low : Lower (fullGraph G) (Nat.card d) := by
        intro A _ T ⟨c, ⟨f⟩⟩ hcard
        have hcf := Nat.card_congr f.toEquiv
        exact hsize.trans_le (Nat.find_min' hex ⟨c, by omega, hcf⟩)
      obtain ⟨R, _, K, ⟨g⟩⟩ :=
        extract d.toSimpleGraph hd n V G hn (occurs_component d) low
      obtain ⟨S, _, L, ⟨h⟩⟩ :=
        extract d.toSimpleGraph hd _ W H rfl (occurs_host e (occurs_component d)) (lower_host e.symm low)
      let left := (fullSum d.toSimpleGraph K).trans (fullCongr g)
      let right := (fullSum d.toSimpleGraph L).trans (fullCongr h)
      have rest := McKayCancel.cancel_of_isolated (fullGraph d.toSimpleGraph) (fullGraph K) (fullGraph L)
        ∅ (full_empty_isolated d.toSimpleGraph) ⟨left.trans (e.trans right.symm)⟩
      have sizes : Nat.card d + Nat.card R = n :=
        Nat.card_sum.symm.trans ((Nat.card_congr g.toEquiv).trans hn)
      obtain ⟨f⟩ := ih (Nat.card R) (by omega) R K rfl S L rest
      exact ⟨g.symm.trans ((Iso.sumCongr Iso.refl f).trans h)⟩
    · have small : ∀ d : (fullGraph G).ConnectedComponent, Nat.card d ≤ 1 := by
        intro d
        by_contra! hd
        exact hex ⟨_, d, hd, rfl⟩
      have small' : ∀ d : (fullGraph H).ConnectedComponent, Nat.card d ≤ 1 := by
        intro d
        have h := small (e.symm.connectedComponentEquiv d)
        exact (Nat.card_congr (componentIso e.symm d).toEquiv).trans_le h
      exact iso_of_small e small small'


end McKay

/-- The finite nonempty case of McKay's reconstruction question. -/
theorem OMA.solution : type_of% @OMA.S_mo_495000.main := by
  intro V W _ _ _ _ G H h
  exact McKay.reconstruct _ V G rfl W H (fullGraph_iso_of_powersetGraph_iso h)
