import OMAReductions.R_TotalColoringConjecture_total_coloring_conjecture_variants_maxDegree_le_five_R1_H2_R1

import Mathlib

/-! Formalization of the total coloring bounds of A. V. Kostochka, Discrete Mathematics 162 (1996), 199–214. -/


section -- VertexGlue

/-
Kostochka (1996), Section 6, Lemma 6. Two colored pieces sharing a vertex can
be glued by assigning distinct target colors to the shared vertex and its star,
then independently permuting each piece's palette.
-/
namespace TotalFive
open SimpleGraph

private theorem align {J P : Type*} [Finite J] (a b : J → P)
    (ha : Function.Injective a) (hb : Function.Injective b) :
    ∃ p : Equiv.Perm P, ∀ j, p (a j) = b j := by
  classical
  let := Fintype.ofFinite J
  suffices H : ∀ s : Finset J, ∃ p : Equiv.Perm P, ∀ j ∈ s, p (a j) = b j by
    obtain ⟨p, hp⟩ := H .univ
    exact ⟨p, fun j => hp j (Finset.mem_univ _)⟩
  intro s
  induction s using Finset.induction_on with
  | empty => exact ⟨Equiv.refl _, by simp⟩
  | @insert i s hi ih =>
    obtain ⟨p, hp⟩ := ih
    refine ⟨p.trans (Equiv.swap (p (a i)) (b i)), ?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · simp
    · have hji : j ≠ i := fun eq => hi (eq ▸ hj)
      rw [Equiv.trans_apply, Equiv.swap_apply_of_ne_of_ne (p.injective.ne (ha.ne hji))
        ((hp j hj).trans_ne (hb.ne hji)), hp _ hj]

/-- A spanning graph representing one side of an edge partition. Vertices
outside that side are isolated and their colors can be discarded. -/
def wing {V : Type*} (G : SimpleGraph V) (owner : G.edgeSet → Bool) (b : Bool) : SimpleGraph V where
  Adj v w := ∃ h : G.Adj v w, owner ⟨s(v, w), h⟩ = b
  symm := ⟨by
    rintro v w ⟨h, hb⟩
    refine ⟨h.symm, ?_⟩
    simpa only [Sym2.eq_swap] using hb⟩
  loopless := ⟨by rintro v ⟨h, _⟩; exact G.loopless.irrefl _ h⟩

private theorem wing_edge {V : Type*} {G : SimpleGraph V} {own : G.edgeSet → Bool}
    (e : G.edgeSet) : e.val ∈ (wing G own (own e)).edgeSet := by
  obtain ⟨e, he⟩ := e
  induction e using Sym2.ind with
  | _ v w => exact ⟨he, rfl⟩

private def liftEdge {V : Type*} {G : SimpleGraph V} (own : G.edgeSet → Bool) (e : G.edgeSet)
    (b : Bool) (h : own e = b) : (wing G own b).edgeSet :=
  ⟨e.val, by subst b; exact wing_edge e⟩

/-- Glue any two wings along their unique possible common incident vertex.
The same proof allows an arbitrary split of the edges at that vertex. -/
theorem glueAtVertex {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hub : V) (part : V → Bool) (owner : G.edgeSet → Bool)
    (each : ∀ (e : G.edgeSet) (v : V), v ∈ e.val → v ≠ hub → part v = owner e)
    {k : ℕ} (hk : G.degree hub + 1 ≤ k)
    (pieces : ∀ b, (wing G owner b).TotalColorable k) : G.TotalColorable k := by
  classical
  choose c hc using pieces
  let target : Option (G.incidenceSet hub) ↪ Fin k :=
    Classical.choice (Function.Embedding.nonempty_of_card_le (by
      simpa only [Fintype.card_option, Fintype.card_fin, G.card_incidenceSet_eq_degree] using hk))
  let subedge (e : G.edgeSet) : (wing G owner (owner e)).edgeSet := ⟨e.val, wing_edge e⟩
  let index (b : Bool) := Option {e : G.incidenceSet hub // owner ⟨e.val, e.property.1⟩ = b}
  let old (b : Bool) : index b → Fin k := fun i => match i with
    | none => c b (.inl hub)
    | some e => c b (.inr (liftEdge owner ⟨e.val.val, e.val.property.1⟩ b e.property))
  let name (b : Bool) : index b → Option (G.incidenceSet hub) := Option.map Subtype.val
  have hinj (b : Bool) : Function.Injective (old b) := by
    rintro (_ | e) (_ | f) h
    · rfl
    · exact False.elim ((hc b).2.2 hub _ f.val.property.2 h)
    · exact False.elim ((hc b).2.2 hub _ e.val.property.2 h.symm)
    · by_contra hne
      apply (hc b).2.1 _ _ _ ⟨hub, e.val.property.2, f.val.property.2⟩ h
      intro eq
      apply hne
      congr 1
      exact Subtype.ext (Subtype.ext (congrArg (fun z : (wing G owner b).edgeSet => z.val) eq))
  have asgn (b : Bool) := align (old b) (target ∘ name b) (hinj b)
    (target.injective.comp (Option.map_injective Subtype.val_injective))
  choose p hp using asgn
  let vc (v : V) := if v = hub then target none else p (part v) (c (part v) (.inl v))
  let ec (e : G.edgeSet) := p (owner e) (c (owner e) (.inr (subedge e)))
  have atHub (b : Bool) : p b (c b (.inl hub)) = target none := hp b none
  have atSide (e : G.edgeSet) (v : V) (hv : v ∈ e.val) :
      vc v = p (owner e) (c (owner e) (.inl v)) := by
    by_cases h : v = hub
    · subst v; simp [vc, atHub]
    · change (if v = hub then _ else _) = _
      rw [if_neg h]
      exact congrArg (fun b => p b (c b (.inl v))) (each e v hv h)
  have edgeAtHub (e : G.edgeSet) (h : hub ∈ e.val) :
      ec e = target (some ⟨e.val, e.property, h⟩) :=
    hp (owner e) (some ⟨⟨e.val, e.property, h⟩, rfl⟩)
  refine ⟨Sum.elim vc ec, ?_, ?_, ?_⟩
  · intro v w hadj
    let e : G.edgeSet := ⟨s(v,w), hadj⟩
    change vc v ≠ vc w
    rw [atSide e v (Sym2.mem_mk_left _ _), atSide e w (Sym2.mem_mk_right _ _)]
    exact (p _).injective.ne ((hc _).1 v w ⟨hadj, rfl⟩)
  · rintro e f hne ⟨v, hev, hfv⟩
    change ec e ≠ ec f
    by_cases hv : v = hub
    · subst v
      rw [edgeAtHub e hev, edgeAtHub f hfv]
      exact fun eq => hne (Subtype.ext (congrArg (fun x : G.incidenceSet hub => x.val) (Option.some.inj (target.injective eq))))
    · have heq := (each e v hev hv).symm.trans (each f v hfv hv)
      have hf (b : Bool) (h : owner f = b) : ec f = p b (c b (.inr (liftEdge owner f b h))) := by
        subst b; rfl
      rw [hf (owner e) heq.symm]
      exact (p _).injective.ne ((hc _).2.1 _ _ (fun eq => hne (Subtype.ext
        (congrArg (fun x : (wing G owner (owner e)).edgeSet => x.val) eq)))
        ⟨v, hev, hfv⟩)
  · intro v e he
    change vc v ≠ ec e
    rw [atSide e v he]
    exact (p _).injective.ne ((hc _).2.2 _ _ he)

end TotalFive

end


section -- Articulation

/- Gluing induced subgraphs along a separating vertex, including isolated vertices. -/

namespace TotalFive
open SimpleGraph

/-- Restricting to a nonempty vertex set containing every edge loses only isolated vertices. -/
theorem totalColorable_of_support {V : Type*} (G : SimpleGraph V) (S : Set V)
    (hs : S.Nonempty) (ends : ∀ ⦃v w⦄, G.Adj v w → v ∈ S ∧ w ∈ S)
    {k : ℕ} (colored : (G.induce S).TotalColorable k) : G.TotalColorable k := by
  classical
  let r (v : V) : S := if h : v ∈ S then ⟨v,h⟩ else ⟨hs.choose, hs.choose_spec⟩
  have fix (v : V) (h : v ∈ S) : (r v).val = v := by simp [r, h]
  let f : G →g G.induce S := ⟨r, fun {x y} h => by
    change G.Adj (r x).val (r y).val
    rw [fix x (ends h).1, fix y (ends h).2]
    exact h⟩
  have back (e : G.edgeSet) : Sym2.map Subtype.val (f.mapEdgeSet e).val = e.val := by
    obtain ⟨e, he⟩ := e
    induction e using Sym2.ind with
    | _ v w =>
      change s((r v).val, (r w).val) = s(v,w)
      rw [fix v (ends he).1, fix w (ends he).2]
  obtain ⟨c, hv, he, hi⟩ := colored
  refine ⟨Sum.elim (fun v => c (.inl (f v))) (fun e => c (.inr (f.mapEdgeSet e))), ?_, ?_, ?_⟩
  · exact fun v w h => hv _ _ (f.map_rel' h)
  · rintro e g ne ⟨v, h₁, h₂⟩
    apply he _ _ ?_ ⟨f v, Sym2.mem_map.mpr ⟨v, h₁, rfl⟩, Sym2.mem_map.mpr ⟨v, h₂, rfl⟩⟩
    intro h
    exact ne (Subtype.ext ((back e).symm.trans ((congrArg (fun a : (G.induce S).edgeSet =>
      Sym2.map Subtype.val a.val) h).trans (back g))))
  · exact fun v e h => hi _ _ (Sym2.mem_map.mpr ⟨v, h, rfl⟩)

/-- Each piece includes the hub; any two other adjacent vertices must share a side. -/
theorem glueInducedAtVertex {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hub : V) (part : V → Bool)
    (split : ∀ ⦃v w⦄, G.Adj v w → v ≠ hub → w ≠ hub → part v = part w)
    {k : ℕ} (hk : G.degree hub + 1 ≤ k)
    (pieces : ∀ b, (G.induce {v | v = hub ∨ part v = b}).TotalColorable k) :
    G.TotalColorable k := by
  classical
  have endpt (e : G.edgeSet) : ∃ x, x ∈ e.val ∧ x ≠ hub := by
    obtain ⟨e, he⟩ := e
    induction e using Sym2.ind with
    | _ v w =>
      by_cases h : v = hub
      · exact ⟨w, Sym2.mem_mk_right _ _, fun hw => he.ne (h.trans hw.symm)⟩
      · exact ⟨v, Sym2.mem_mk_left _ _, h⟩
  let owner (e : G.edgeSet) := part (endpt e).choose
  have each (e : G.edgeSet) (v : V) (hv : v ∈ e.val) (neq : v ≠ hub) : part v = owner e := by
    obtain ⟨hw, hn⟩ := (endpt e).choose_spec
    by_cases h : v = (endpt e).choose
    · exact congrArg part h
    · apply split _ neq hn
      have hh : s(v, (endpt e).choose) = e.val := ((Sym2.mem_and_mem_iff h).mp ⟨hv,hw⟩).symm
      exact G.mem_edgeSet.mp (hh.symm ▸ e.property)
  apply glueAtVertex G hub part owner each hk
  intro b
  let S : Set V := {v | v = hub ∨ part v = b}
  have ends ⦃v w⦄ (vw : (wing G owner b).Adj v w) : v ∈ S ∧ w ∈ S := by
    obtain ⟨ha, ho⟩ := vw
    let e : G.edgeSet := ⟨s(v,w), ha⟩
    constructor
    · by_cases hv : v = hub
      · exact Or.inl hv
      · exact Or.inr ((each e v (Sym2.mem_mk_left _ _) hv).trans ho)
    · by_cases hw : w = hub
      · exact Or.inl hw
      · exact Or.inr ((each e w (Sym2.mem_mk_right _ _) hw).trans ho)
  apply totalColorable_of_support _ S ⟨hub, Or.inl rfl⟩ ends
  have eq : (wing G owner b).induce S = G.induce S := by
    ext x y
    constructor
    · rintro ⟨h, _⟩; exact h
    · intro h
      let e : G.edgeSet := ⟨s(x.val,y.val), h⟩
      refine ⟨h, ?_⟩
      by_cases hx : x.val = hub
      · have hy : y.val ≠ hub := fun hy => h.ne (Subtype.ext (hx.trans hy.symm))
        exact (each e y.val (Sym2.mem_mk_right _ _) hy).symm.trans (y.property.resolve_left hy)
      · exact (each e x.val (Sym2.mem_mk_left _ _) hx).symm.trans (x.property.resolve_left hx)
  rw [eq]
  exact pieces b

end TotalFive

end


section -- Regularization

/-
Kostochka works with regular graphs in Theorems 1 and 2. For a simple graph of
maximum degree at most `d`, repeatedly join two copies along vertices of degree
less than `d`. The original is an induced subgraph at every stage.
-/

namespace TotalFive
open SimpleGraph

/-- Pull back vertex and edge colors along a graph embedding. -/
theorem totalColorable_of_embedding {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G ↪g H) {k : ℕ} (h : H.TotalColorable k) : G.TotalColorable k := by
  obtain ⟨c, hv, he, hi⟩ := h
  refine ⟨Sum.elim (fun v => c (.inl (f v))) (fun e => c (.inr (f.mapEdgeSet e))), ?_, ?_, ?_⟩
  · intro u v huv
    exact hv _ _ (f.map_rel_iff.mpr huv)
  · rintro e e' hne ⟨v, h₁, h₂⟩
    apply he _ _ (f.mapEdgeSet.injective.ne hne)
    exact ⟨f v, Sym2.mem_map.mpr ⟨v, h₁, rfl⟩, Sym2.mem_map.mpr ⟨v, h₂, rfl⟩⟩
  · intro v e hve
    exact hi _ _ (Sym2.mem_map.mpr ⟨v, hve, rfl⟩)

variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Two copies of `G`, with one cross-edge for each vertex still lacking a neighbor. -/
def doubleDeficient (d : ℕ) : SimpleGraph (Bool × V) where
  Adj x y := (x.1 = y.1 ∧ G.Adj x.2 y.2) ∨ (x.1 ≠ y.1 ∧ x.2 = y.2 ∧ G.degree x.2 < d)
  symm := ⟨by
    rintro x y (⟨hb, ha⟩ | ⟨hb, hv, h⟩)
    · exact Or.inl ⟨hb.symm, ha.symm⟩
    · exact Or.inr ⟨hb.symm, hv.symm, hv ▸ h⟩⟩
  loopless := ⟨by intro x; simp⟩

instance instDecidableDouble [DecidableEq V] (d : ℕ) : DecidableRel (doubleDeficient G d).Adj :=
  fun _ _ => inferInstanceAs (Decidable ((_ ∧ _) ∨ (_ ∧ _ ∧ _)))

def leftEmbedding (d : ℕ) : G ↪g doubleDeficient G d where
  toFun v := (false, v)
  inj' := fun _ _ h => congrArg Prod.snd h
  map_rel_iff' := by
    intro u v
    change (false = false ∧ G.Adj u v ∨ false ≠ false ∧ u = v ∧ G.degree u < d) ↔ G.Adj u v
    simp

private def layer (b : Bool) : V ↪ Bool × V where
  toFun v := (b, v)
  inj' := fun _ _ h => congrArg Prod.snd h

omit [Fintype V] in
private theorem layer_apply (b : Bool) (v : V) : layer b v = (b, v) := rfl

private theorem neighbor_double [DecidableEq V] (d : ℕ) (b : Bool) (v : V) :
    (doubleDeficient G d).neighborFinset (b, v) =
      if G.degree v < d then insert (!b, v) ((G.neighborFinset v).map (layer b))
      else (G.neighborFinset v).map (layer b) := by
  ext ⟨a, u⟩
  rw [SimpleGraph.mem_neighborFinset]
  cases b <;> cases a <;> by_cases h : G.degree v < d <;>
    simp [h, doubleDeficient, Finset.mem_map, layer_apply, eq_comm]

theorem degree_double [DecidableEq V] (d : ℕ) (b : Bool) (v : V) :
    (doubleDeficient G d).degree (b, v) = if G.degree v < d then G.degree v + 1 else G.degree v := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, neighbor_double]
  have hnot : (!b, v) ∉ (G.neighborFinset v).map (layer b) := by
    cases b <;> simp [layer_apply, Finset.mem_map]
  split <;> simp [hnot, SimpleGraph.card_neighborFinset_eq_degree]

/-- It is enough to color the regular case. The induction parameter counts how
many further doublings may be needed to fill the maximum degree deficit. -/
theorem totalColorable_of_regular {d c : ℕ}
    (color : ∀ {W : Type} [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj],
      H.IsRegularOfDegree d → H.TotalColorable c)
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (upper : ∀ v, G.degree v ≤ d) : G.TotalColorable c := by
  have fill (s : ℕ) : ∀ {W : Type} [Fintype W] [DecidableEq W] (H : SimpleGraph W)
      [DecidableRel H.Adj], (∀ v, H.degree v ≤ d) → (∀ v, d ≤ H.degree v + s) →
      H.TotalColorable c := by
    induction s with
    | zero =>
      intro W _ _ H _ hi lo
      exact color H (fun v => Nat.le_antisymm (hi v) (by simpa using lo v))
    | succ s ih =>
      intro W _ _ H _ hi lo
      apply totalColorable_of_embedding (leftEmbedding H d)
      apply ih
      · rintro ⟨b, v⟩
        rw [degree_double]
        split <;> have := hi v <;> omega
      · rintro ⟨b, v⟩
        rw [degree_double]
        split <;> have := lo v <;> omega
  exact fill d G upper (fun v => by omega)

end TotalFive

end


section -- Target

namespace TotalFive
open SimpleGraph

/-- The two regular cases that suffice for the exact board statement. -/
def RegularBound (d k : ℕ) : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    G.IsRegularOfDegree d → G.TotalColorable k

theorem h2_of_regular_bounds (four : RegularBound 4 6) (five : RegularBound 5 7) :
    OMA.R_TotalColoringConjecture_total_coloring_conjecture_variants_maxDegree_le_five_R1.H2 := by
  intro V _ _ G _ hm
  rcases hm with h | h <;> rw [h]
  · exact Nat.sInf_le (totalColorable_of_regular four G (fun v => h ▸ G.degree_le_maxDegree v))
  · exact Nat.sInf_le (totalColorable_of_regular five G (fun v => h ▸ G.degree_le_maxDegree v))

end TotalFive

end


section -- Components

/- Reduction of regular total coloring to connected components. -/

namespace TotalFive
open SimpleGraph

/-- A total coloring may be selected independently on each connected component. -/
theorem totalColorable_of_components {V : Type*} (G : SimpleGraph V) {k : ℕ}
    (colored : ∀ C : G.ConnectedComponent, C.toSimpleGraph.TotalColorable k) : G.TotalColorable k := by
  classical
  have span (C : G.ConnectedComponent) : C.toSimpleGraph.spanningCoe.TotalColorable k := by
    apply totalColorable_of_support _ C.supp C.nonempty_supp
    · intro v w h
      obtain ⟨hv, vw⟩ := C.adj_spanningCoe_toSimpleGraph.mp h
      exact ⟨hv, C.mem_supp_of_adj_mem_supp hv vw⟩
    · simpa only [ConnectedComponent.toSimpleGraph, induce_spanningCoe] using colored C
  choose c hc using span
  let own (e : G.edgeSet) := G.connectedComponentMk e.val.out.1
  have eqOwn (e : G.edgeSet) (v : V) (hv : v ∈ e.val) : G.connectedComponentMk v = own e := by
    by_cases h : v = e.val.out.1
    · exact congrArg G.connectedComponentMk h
    · have he := (Sym2.mem_and_mem_iff h).mp ⟨hv, Sym2.out_fst_mem _⟩
      exact ConnectedComponent.connectedComponentMk_eq_of_adj (G.mem_edgeSet.mp (he ▸ e.property))
  have onComp (e : G.edgeSet) : e.val ∈ (own e).toSimpleGraph.spanningCoe.edgeSet := by
    obtain ⟨e, he⟩ := e
    induction e using Sym2.ind with
    | _ v w =>
      exact ((own ⟨s(v,w),he⟩).adj_spanningCoe_toSimpleGraph).mpr
        ⟨eqOwn ⟨s(v,w),he⟩ v (Sym2.mem_mk_left _ _), he⟩
  let ec (e : G.edgeSet) := c (own e) (.inr ⟨e.val, onComp e⟩)
  let vc (v : V) := c (G.connectedComponentMk v) (.inl v)
  have toComp (e : G.edgeSet) (C : G.ConnectedComponent) (h : own e = C) :
      ec e = c C (.inr ⟨e.val, h ▸ onComp e⟩) := by subst C; rfl
  refine ⟨Sum.elim vc ec, ?_, ?_, ?_⟩
  · intro v w vw
    have h := ConnectedComponent.connectedComponentMk_eq_of_adj vw
    change c (G.connectedComponentMk v) (.inl v) ≠ c (G.connectedComponentMk w) (.inl w)
    rw [← h]
    exact (hc _).1 v w ((G.connectedComponentMk v).adj_spanningCoe_toSimpleGraph.mpr ⟨rfl, vw⟩)
  · rintro e f ne ⟨v, hv, hw⟩
    change ec e ≠ ec f
    rw [toComp e _ (eqOwn e v hv).symm, toComp f _ (eqOwn f v hw).symm]
    apply (hc _).2.1 _ _ ?_ ⟨v,hv,hw⟩
    exact fun h => ne (Subtype.ext (congrArg (fun a : (G.connectedComponentMk v).toSimpleGraph.spanningCoe.edgeSet => a.val) h))
  · intro v e hv
    change vc v ≠ ec e
    rw [toComp e _ (eqOwn e v hv).symm]
    exact (hc _).2.2 v _ hv

/-- Work component by component in the regular form of H2. -/
theorem regularBound_of_connected {d k : ℕ}
    (color : ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
      [DecidableRel G.Adj], G.Connected → G.IsRegularOfDegree d → G.TotalColorable k) :
    RegularBound d k := by
  classical
  intro V _ _ G _ h
  apply totalColorable_of_components G
  intro C
  let : Fintype C := Fintype.ofFinite C
  apply color C.toSimpleGraph C.connected_toSimpleGraph
  intro v
  let H := G.induce C.supp
  have eqn := degree_induce_of_neighborSet_subset (G := G) (s := C.supp) (v := v)
    (fun _ hv => C.mem_supp_of_adj_mem_supp v.property hv)
  have irrel (a b : Fintype (H.neighborSet v)) :
      @SimpleGraph.degree C H v a = @SimpleGraph.degree C H v b := by
    rw [Subsingleton.elim a b]
  exact (irrel _ _).trans (eqn.trans (h v.val))

end TotalFive

end


section -- SmallOrder

/- The complete-graph exception in Kostochka's Theorem 1. Label a vertex by
`a`, give it color `a+a`, and color the edge with labels `a,b` by `a+b`.
The construction also supplies the small-order base cases in degree five. -/
namespace TotalFive
open SimpleGraph

private def sumLabel {V : Type*} {q : ℕ} [NeZero q] (lab : V → Fin q) : Sym2 V → Fin q :=
  Sym2.lift ⟨fun x y => lab x + lab y, fun _ _ => add_comm _ _⟩

private theorem sumLabel_mk {V : Type*} {q : ℕ} [NeZero q] (lab : V → Fin q) (u v : V) :
    sumLabel lab s(u,v) = lab u + lab v := rfl

theorem totalColorable_by_sum {V : Type*} {q : ℕ} [NeZero q] (G : SimpleGraph V) (lab : V ↪ Fin q)
    (two : Function.Injective (fun a : Fin q => a + a)) : G.TotalColorable q := by
  refine ⟨Sum.elim (fun v => lab v + lab v) (fun e => sumLabel lab e.val), ?_, ?_, ?_⟩
  · intro u v huv eq
    exact huv.ne (lab.injective (two eq))
  · rintro ⟨e, he⟩ ⟨f, hf⟩ hne ⟨v, hv, hv'⟩ eq
    obtain ⟨u, rfl⟩ := Sym2.mem_iff_exists.mp hv
    obtain ⟨w, rfl⟩ := Sym2.mem_iff_exists.mp hv'
    change lab v + lab u = lab v + lab w at eq
    have h := lab.injective (add_left_cancel eq)
    subst w
    exact hne rfl
  · rintro v ⟨e, he⟩ hv eq
    obtain ⟨u, rfl⟩ := Sym2.mem_iff_exists.mp hv
    change lab v + lab v = lab v + lab u at eq
    exact (G.mem_edgeSet.mp he).ne (lab.injective (add_left_cancel eq))

theorem five_colors_of_order_le_five {V : Type*} [Fintype V] (G : SimpleGraph V)
    (h : Fintype.card V ≤ 5) : G.TotalColorable 5 := by
  obtain ⟨lab⟩ := Function.Embedding.nonempty_of_card_le (β := Fin 5) (by simpa using h)
  exact totalColorable_by_sum G lab (by decide)

theorem seven_colors_of_order_le_seven {V : Type*} [Fintype V] (G : SimpleGraph V)
    (h : Fintype.card V ≤ 7) : G.TotalColorable 7 := by
  obtain ⟨lab⟩ := Function.Embedding.nonempty_of_card_le (β := Fin 7) (by simpa using h)
  exact totalColorable_by_sum G lab (by decide)

end TotalFive

end


section -- ForestPartition

/-
# Initial forest bipartition for Kostochka (1996) Lemma 1

We prove from first principles that every finite simple graph `G` with maximum degree at most `4`
and no `K₅` clique (`G.CliqueFree 5`) admits a partition of its vertex set into two sets each
inducing an acyclic graph (forest). In particular, every connected finite simple `4`-regular graph
other than `K₅` admits a partition into two induced forests.

## Proof outline
1. **Walk lifting and acyclicity preservation** (`isAcyclic_induce_insert_of_not_reachable`,
   `isAcyclic_induce_insert_of_unique_adj`, `not_reachable_induce_insert_of_unique_adj`):
   Adding a vertex `u` whose distinct neighbors in `A` lie in distinct connected components
   of `G.induce A` preserves acyclicity; in particular, adding a vertex `u ∉ A` with at most one
   neighbor in `A` preserves both acyclicity and non-reachability between any two vertices of `A`.
2. **Greedy coloring along a good ordering** (`greedy_extend_coloring`,
   `exists_forestColoring_of_exists_degree_le_three`):
   If `G` is connected, every vertex has degree `≤ 4`, and some vertex `v` has degree `≤ 3`,
   sorting vertices by decreasing graph distance from `v` ensures every vertex has at most `3`
   earlier neighbors, so greedy coloring produces a forest bipartition.
3. **Cut-vertex decomposition** (`exists_forestColoring_of_cut_vertex`):
   If a connected graph `G` with `Δ ≤ 4` has a cut vertex `x`, splitting `V \ {x}` into a
   component `A` of `G - {x}` and its complement `B` yields two connected induced subgraphs
   `G[A ∪ {x}]` and `G[B ∪ {x}]` in both of which `x` has degree `≤ 3`. Coloring each by step 2,
   flipping colors on the second piece to agree at `x`, and gluing yields a forest bipartition.
4. **Lovász's cherry lemma** (`exists_good_cherry_of_two_connected`):
   Every `2`-connected non-complete finite simple graph with minimum degree `≥ 3` contains a
   vertex `v` and two nonadjacent neighbors `a, b` of `v` such that `G - {a, b}` is connected.
5. **Brooks ordering & main theorems**:
   In a `2`-connected `4`-regular non-`K₅` graph, color `a, b` with `false` (distinct components
   of `G[{a, b}]`), extend greedily in reverse BFS order of `G - {a, b}` toward `v` (preserving
   acyclicity and non-reachability of `a, b` in the `false`-class), and finally color `v`.
   Combining connected components gives the full `Δ ≤ 4`, `CliqueFree 5` theorem and all
   `4`-regular non-`K₅` corollaries, plus sharpness (`K₅` has no forest bipartition).
-/

namespace ForestPartition

open SimpleGraph SimpleGraph.Walk

/- ### Section 1: Walk lifting, separation helpers, and acyclicity preservation -/

section WalkHelpers

variable {V : Type*} {G : SimpleGraph V}

/-- A `Bool`-valued vertex coloring of `G` whose two color classes induce acyclic graphs. -/
def IsForestColoring (G : SimpleGraph V) (c : V → Bool) : Prop :=
  (G.induce {v : V | c v = false}).IsAcyclic ∧ (G.induce {v : V | c v = true}).IsAcyclic

/-- Flipping the two colors of a forest coloring yields a forest coloring. -/
lemma IsForestColoring.not {c : V → Bool} (hc : IsForestColoring G c) :
    IsForestColoring G (fun v => !c v) := by
  constructor
  · have hset : {v : V | (!c v) = false} = {v : V | c v = true} := by
      ext v; cases c v <;> simp
    rw [hset]
    exact hc.2
  · have hset : {v : V | (!c v) = true} = {v : V | c v = false} := by
      ext v; cases c v <;> simp
    rw [hset]
    exact hc.1

/-- Lift a walk in `G.induce S` whose vertex values lie in `T` to a walk in `G.induce T`. -/
def walkInduce {S : Set V} (T : Set V) :
    ∀ {u v : S} (p : (G.induce S).Walk u v) (h : ∀ x ∈ p.support, x.1 ∈ T),
      (G.induce T).Walk ⟨u.1, h u p.start_mem_support⟩ ⟨v.1, h v p.end_mem_support⟩
  | _, _, .nil, _ => .nil
  | _, _, @Walk.cons _ _ _ w _ hadj p, h =>
      let h' : ∀ x ∈ p.support, x.1 ∈ T := fun x hx => h x (List.mem_cons_of_mem _ hx)
      .cons (v := (⟨w.1, h' w p.start_mem_support⟩ : T))
        (induce_adj.mpr (induce_adj.mp hadj)) (walkInduce T p h')

@[simp]
lemma map_val_support_walkInduce {S : Set V} (T : Set V) {u v : S} (p : (G.induce S).Walk u v)
    (h : ∀ x ∈ p.support, x.1 ∈ T) :
    (walkInduce T p h).support.map Subtype.val = p.support.map Subtype.val := by
  induction p with
  | nil => rfl
  | cons hadj p ih =>
      simp only [walkInduce, Walk.support_cons, List.map_cons]
      exact congrArg _ (ih _)

@[simp]
lemma length_walkInduce {S : Set V} (T : Set V) {u v : S} (p : (G.induce S).Walk u v)
    (h : ∀ x ∈ p.support, x.1 ∈ T) :
    (walkInduce T p h).length = p.length := by
  induction p with
  | nil => rfl
  | cons hadj p ih =>
      simp only [walkInduce, Walk.length_cons]
      exact congrArg Nat.succ (ih _)

lemma isCycle_walkInduce {S : Set V} (T : Set V) {u : S} {p : (G.induce S).Walk u u}
    (hp : p.IsCycle) (h : ∀ x ∈ p.support, x.1 ∈ T) :
    (walkInduce T p h).IsCycle := by
  rw [Walk.isCycle_iff_isPath_tail_and_le_length]
  refine ⟨?_, ?_⟩
  · rw [Walk.isPath_def]
    have hnotnil : ¬ (walkInduce T p h).Nil := by
      rw [Walk.not_nil_iff_lt_length, length_walkInduce]
      have := hp.three_le_length
      omega
    rw [Walk.support_tail_of_not_nil _ hnotnil]
    have hmap : ((walkInduce T p h).support.tail).map Subtype.val =
        p.support.tail.map Subtype.val := by
      rw [List.map_tail, List.map_tail, map_val_support_walkInduce]
    have hnodup : (p.support.tail.map Subtype.val).Nodup :=
      hp.support_nodup.map Subtype.val_injective
    rw [← hmap] at hnodup
    exact List.Nodup.of_map Subtype.val hnodup
  · rw [length_walkInduce]
    exact hp.three_le_length

/-- Lift a walk in `G` whose support lies in `T` to a walk in `G.induce T`. -/
def walkToInduce (T : Set V) :
    ∀ {u v : V} (p : G.Walk u v) (h : ∀ x ∈ p.support, x ∈ T),
      (G.induce T).Walk ⟨u, h u p.start_mem_support⟩ ⟨v, h v p.end_mem_support⟩
  | _, _, .nil, _ => .nil
  | _, _, @Walk.cons _ _ _ w _ hadj p, h =>
      let h' : ∀ x ∈ p.support, x ∈ T := fun x hx => h x (List.mem_cons_of_mem _ hx)
      .cons (v := (⟨w, h' w p.start_mem_support⟩ : T)) hadj (walkToInduce T p h')

/-- Project a walk in `G.induce S` back down to a walk in `G`. -/
def walkFromInduce {S : Set V} :
    ∀ {u v : S}, (G.induce S).Walk u v → G.Walk u.1 v.1
  | _, _, .nil => .nil
  | _, _, .cons hadj p => .cons (induce_adj.mp hadj) (walkFromInduce p)

@[simp]
lemma support_walkFromInduce {S : Set V} {u v : S} (p : (G.induce S).Walk u v) :
    (walkFromInduce p).support = p.support.map Subtype.val := by
  induction p with
  | nil => rfl
  | cons hadj p ih =>
      simp only [walkFromInduce, Walk.support_cons, List.map_cons, ih]

lemma isPath_walkFromInduce {S : Set V} {u v : S} {p : (G.induce S).Walk u v}
    (hp : p.IsPath) : (walkFromInduce p).IsPath := by
  rw [Walk.isPath_def, support_walkFromInduce]
  exact hp.support_nodup.map Subtype.val_injective

/-- Any walk starting in `A` and ending outside `A` when `A` has no edges to `V \ (A ∪ {x})`
must pass through `x`. -/
lemma mem_support_of_walk_leaving {H : SimpleGraph V} {x : V} {A : Set V}
    (hno : ∀ a ∈ A, ∀ y, H.Adj a y → y ∈ A ∨ y = x)
    {u v : V} (p : H.Walk u v) (hu : u ∈ A) (hv : v ∉ A) :
    x ∈ p.support := by
  induction p with
  | nil => exact (hv hu).elim
  | @cons u u' v hadj p ih =>
      rcases hno u hu u' hadj with hu'A | rfl
      · exact List.mem_cons_of_mem _ (ih hu'A hv)
      · exact List.mem_cons_of_mem _ p.start_mem_support

/-- A simple path from `u ∈ A` to `x` stays inside `insert x A` whenever `A` has no edges to
`V \ (A ∪ {x})`. -/
lemma support_path_subset_insert_of_no_edge {H : SimpleGraph V} {x : V} {A : Set V}
    (hno : ∀ a ∈ A, ∀ y, H.Adj a y → y ∈ A ∨ y = x) :
    ∀ {u : V} (p : H.Walk u x), p.IsPath → u ∈ A → ∀ z ∈ p.support, z ∈ insert x A
  | _, .nil, _, _, z, hz => by
      rw [Walk.mem_support_nil_iff.mp hz]
      exact Set.mem_insert x A
  | u, @Walk.cons _ _ _ u' _ hadj p, hp, hu, z, hz => by
      have hp' := (Walk.cons_isPath_iff hadj p).mp hp
      rcases List.mem_cons.mp hz with rfl | hz'
      · exact Set.mem_insert_of_mem x hu
      · rcases hno u hu u' hadj with hu'A | hu'x
        · exact support_path_subset_insert_of_no_edge hno p hp'.1 hu'A z hz'
        · subst hu'x
          have hnil : p.Nil := Walk.isPath_iff_nil.mp hp'.1
          rw [hnil.eq_nil, Walk.mem_support_nil_iff] at hz'
          rw [hz']
          exact Set.mem_insert u' A

/-- A simple path with both endpoints outside `A` avoids `A` entirely whenever `A` has no edges
to `V \ (A ∪ {x})`. -/
lemma path_avoids_sep {H : SimpleGraph V} {x : V} {A : Set V}
    (hno : ∀ a ∈ A, ∀ y, H.Adj a y → y ∈ A ∨ y = x) :
    ∀ {u v : V} (p : H.Walk u v), p.IsPath → u ∉ A → v ∉ A → ∀ z ∈ p.support, z ∉ A
  | _, _, .nil, _, hu, _, z, hz => by
      rw [Walk.mem_support_nil_iff.mp hz]
      exact hu
  | u, v, @Walk.cons _ _ _ u' _ hadj p, hp, hu, hv, z, hz => by
      have hp' := (Walk.cons_isPath_iff hadj p).mp hp
      by_cases hu'A : u' ∈ A
      · have hux : u = x := (hno u' hu'A u hadj.symm).resolve_left hu
        have hxmem : x ∈ p.support := mem_support_of_walk_leaving hno p hu'A hv
        exact (hp'.2 (hux ▸ hxmem)).elim
      · rcases List.mem_cons.mp hz with rfl | hz'
        · exact hu
        · exact path_avoids_sep hno p hp'.1 hu'A hv z hz'

/-- Adding a vertex `u` whose distinct neighbors in `A` lie in distinct connected components
of `G.induce A` preserves acyclicity. -/
lemma isAcyclic_induce_insert_of_not_reachable {A : Set V} {u : V}
    (hA : (G.induce A).IsAcyclic)
    (hsep : ∀ x (hx : x ∈ A) y (hy : y ∈ A),
      G.Adj u x → G.Adj u y → x ≠ y → ¬ (G.induce A).Reachable ⟨x, hx⟩ ⟨y, hy⟩) :
    (G.induce (insert u A)).IsAcyclic := by
  let _ := Classical.decEq V
  intro w p hp
  let u' : (insert u A : Set V) := ⟨u, Set.mem_insert u A⟩
  by_cases hmem : u' ∈ p.support
  · let q := p.rotate u' hmem
    have hq : q.IsCycle := hp.rotate hmem
    have hqlen : 3 ≤ q.length := hq.three_le_length
    have hqnn : ¬ q.Nil := hq.not_nil
    let qt := q.tail
    have hqt_add : qt.length + 1 = q.length := q.length_tail_add_one hqnn
    have hqtlen : 2 ≤ qt.length := by omega
    have hqtnn : ¬ qt.Nil := by
      rw [Walk.not_nil_iff_lt_length]
      omega
    let r := qt.dropLast
    have hsupp_qt : qt.support = q.support.tail := q.support_tail_of_not_nil hqnn
    have hnodup_qt : qt.support.Nodup := hsupp_qt ▸ hq.support_nodup
    have hu_not_r : u' ∉ r.support := by
      intro hru
      have hconcat : r.support ++ [u'] = qt.support := qt.support_dropLast_concat hqtnn
      rw [← hconcat, List.nodup_append] at hnodup_qt
      exact hnodup_qt.2.2 u' hru u' (List.mem_singleton.mpr rfl) rfl
    have hrA : ∀ x ∈ r.support, x.1 ∈ A := by
      intro x hx
      rcases x.2 with hxu | hxA
      · have hxeq : x = u' := Subtype.ext hxu
        exact (hu_not_r (hxeq ▸ hx)).elim
      · exact hxA
    let rA := walkInduce A r hrA
    have hadj1 : G.Adj u q.snd.1 := q.adj_snd hqnn
    have hadj2 : G.Adj u q.penultimate.1 := (q.adj_penultimate hqnn).symm
    have hpen : qt.penultimate = q.penultimate := by
      dsimp only [qt, Walk.penultimate]
      rw [q.getVert_tail]
      have hsub : q.tail.length - 1 + 1 = q.length - 1 := by
        have := q.length_tail_add_one hqnn
        omega
      rw [hsub]
    have hne : q.snd.1 ≠ q.penultimate.1 := by
      intro heq
      exact hq.snd_ne_penultimate (Subtype.ext heq)
    have hpenA : q.penultimate.1 ∈ A := hpen ▸ hrA qt.penultimate r.end_mem_support
    have hreach : (G.induce A).Reachable
        ⟨q.snd.1, hrA q.snd r.start_mem_support⟩
        ⟨q.penultimate.1, hpenA⟩ := by
      have hreach0 : (G.induce A).Reachable
          ⟨q.snd.1, hrA q.snd r.start_mem_support⟩
          ⟨qt.penultimate.1, hrA qt.penultimate r.end_mem_support⟩ := ⟨rA⟩
      have hval : qt.penultimate.1 = q.penultimate.1 := congrArg Subtype.val hpen
      have heq_sub : (⟨qt.penultimate.1, hrA qt.penultimate r.end_mem_support⟩ : A) =
          ⟨q.penultimate.1, hpenA⟩ := Subtype.ext hval
      rwa [← heq_sub]
    exact hsep q.snd.1 (hrA q.snd r.start_mem_support)
      q.penultimate.1 hpenA hadj1 hadj2 hne hreach
  · have hpA : ∀ x ∈ p.support, x.1 ∈ A := by
      intro x hx
      rcases x.2 with hxu | hxA
      · have hxeq : x = u' := Subtype.ext hxu
        exact (hmem (hxeq ▸ hx)).elim
      · exact hxA
    exact hA (walkInduce A p hpA) (isCycle_walkInduce A hp hpA)

/-- Adding a vertex `u` with at most one neighbor in `A` preserves acyclicity. -/
lemma isAcyclic_induce_insert_of_unique_adj {A : Set V} {u : V}
    (hA : (G.induce A).IsAcyclic)
    (huniq : ∀ x ∈ A, ∀ y ∈ A, G.Adj u x → G.Adj u y → x = y) :
    (G.induce (insert u A)).IsAcyclic :=
  isAcyclic_induce_insert_of_not_reachable hA fun x hx y hy hux huy hne =>
    (hne (huniq x hx y hy hux huy)).elim

/-- Adding a vertex `u ∉ A` with at most one neighbor in `A` does not merge distinct connected
components of `G.induce A`. -/
lemma not_reachable_induce_insert_of_unique_adj {A : Set V} {u a b : V}
    (ha : a ∈ A) (hb : b ∈ A) (hu : u ∉ A)
    (hnot : ¬ (G.induce A).Reachable ⟨a, ha⟩ ⟨b, hb⟩)
    (huniq : ∀ x ∈ A, ∀ y ∈ A, G.Adj u x → G.Adj u y → x = y) :
    ¬ (G.induce (insert u A)).Reachable ⟨a, Set.mem_insert_of_mem u ha⟩
        ⟨b, Set.mem_insert_of_mem u hb⟩ := by
  let _ := Classical.decEq V
  intro hreach
  obtain ⟨q, hq⟩ := hreach.exists_isPath
  let u' : (insert u A : Set V) := ⟨u, Set.mem_insert u A⟩
  by_cases hmem : u' ∈ q.support
  · let q₁ := q.takeUntil u' hmem
    let q₂ := q.dropUntil u' hmem
    have hq₁_ne : ¬ q₁.Nil := by
      intro hnil
      have heq : a = u := congrArg Subtype.val hnil.eq
      exact hu (heq ▸ ha)
    have hq₂_ne : ¬ q₂.Nil := by
      intro hnil
      have heq : b = u := (congrArg Subtype.val hnil.eq).symm
      exact hu (heq ▸ hb)
    have hspec : q₁.append q₂ = q := q.take_spec hmem
    have hnodup : (q₁.support ++ q₂.support.tail).Nodup := by
      rw [← Walk.support_append, hspec]
      exact hq.support_nodup
    have hdisj := (List.nodup_append.mp hnodup).2.2
    let x₁ := q₁.penultimate
    let x₂ := q₂.snd
    have hadj₁ : G.Adj u x₁.1 := (q₁.adj_penultimate hq₁_ne).symm
    have hadj₂ : G.Adj u x₂.1 := q₂.adj_snd hq₂_ne
    have hx₁_mem : x₁ ∈ q₁.support := q₁.getVert_mem_support (q₁.length - 1)
    have hx₂_mem : x₂ ∈ q₂.support.tail := by
      rw [← q₂.support_tail_of_not_nil hq₂_ne]
      exact q₂.tail.start_mem_support
    have hne : x₁ ≠ x₂ := hdisj x₁ hx₁_mem x₂ hx₂_mem
    have hx₁A : x₁.1 ∈ A := by
      rcases x₁.2 with hx₁u | hx₁A
      · exact (hadj₁.ne hx₁u.symm).elim
      · exact hx₁A
    have hx₂A : x₂.1 ∈ A := by
      rcases x₂.2 with hx₂u | hx₂A
      · exact (hadj₂.ne hx₂u.symm).elim
      · exact hx₂A
    exact hne (Subtype.ext (huniq x₁.1 hx₁A x₂.1 hx₂A hadj₁ hadj₂))
  · have hqA : ∀ x ∈ q.support, x.1 ∈ A := by
      intro x hx
      rcases x.2 with hxu | hxA
      · have hxeq : x = u' := Subtype.ext hxu
        exact (hmem (hxeq ▸ hx)).elim
      · exact hxA
    exact hnot ⟨walkInduce A q hqA⟩

/-- Degree in an induced subgraph is at most the degree in the ambient graph. -/
lemma degree_induce_le [Fintype V] [DecidableRel G.Adj] {s : Set V} [DecidablePred (· ∈ s)]
    (u : s) :
    (G.induce s).degree u ≤ G.degree u.1 := by
  let _ := Classical.decEq V
  rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree]
  refine Finset.card_le_card_of_injOn Subtype.val ?_ ?_
  · intro x hx
    simp only [Finset.mem_coe, mem_neighborFinset, induce_adj] at hx ⊢
    exact hx
  · intro x _ y _ hxy
    exact Subtype.ext hxy

/-- If `u ∈ s` has a neighbor `w ∉ s`, then its degree in `G.induce s` is strictly smaller than
its degree in `G`. -/
lemma degree_induce_add_one_le_of_adj_notMem [Fintype V] [DecidableRel G.Adj]
    {s : Set V} [DecidablePred (· ∈ s)] (u : s) {w : V} (hw : w ∉ s) (hadj : G.Adj u.1 w) :
    (G.induce s).degree u + 1 ≤ G.degree u.1 := by
  let _ := Classical.decEq V
  have hwmem : w ∈ G.neighborFinset u.1 := (mem_neighborFinset G u.1 w).mpr hadj
  have hle : (G.induce s).degree u ≤ ((G.neighborFinset u.1).erase w).card := by
    rw [← card_neighborFinset_eq_degree]
    refine Finset.card_le_card_of_injOn Subtype.val ?_ ?_
    · intro x hx
      simp only [Finset.mem_coe, mem_neighborFinset, induce_adj, Finset.mem_erase] at hx ⊢
      exact ⟨fun hxw => hw (hxw ▸ x.2), hx⟩
    · intro x _ y _ hxy
      exact Subtype.ext hxy
  have hcard : ((G.neighborFinset u.1).erase w).card + 1 = G.degree u.1 := by
    rw [Finset.card_erase_add_one hwmem, card_neighborFinset_eq_degree]
  omega

/-- Every vertex `x ≠ v` in a connected graph has a neighbor strictly closer to `v`. -/
lemma exists_adj_dist_lt_of_connected {H : SimpleGraph V} (hconn : H.Connected)
    {v x : V} (hne : x ≠ v) :
    ∃ w : V, H.Adj x w ∧ H.dist v w < H.dist v x := by
  obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist x v
  have hpos : 0 < p.length := by
    rw [hp]
    exact hconn.pos_dist_of_ne hne
  have hnn : ¬ p.Nil := Walk.not_nil_iff_lt_length.mpr hpos
  refine ⟨p.snd, p.adj_snd hnn, ?_⟩
  have hle : H.dist p.snd v ≤ p.tail.length := dist_le p.tail
  have htail : p.tail.length + 1 = p.length := p.length_tail_add_one hnn
  have h1 : H.dist v p.snd = H.dist p.snd v := dist_comm
  have h2 : H.dist v x = H.dist x v := dist_comm
  omega

/-- Transfer acyclicity from a doubly-induced subgraph `(G.induce S).induce {z | c₁ z = col}` to
`G.induce {v | v ∈ S ∧ c v = col}` when `c` agrees with `c₁` on `S`. -/
lemma isAcyclic_induce_of_subinduce {S : Set V} {c : V → Bool} {c₁ : S → Bool} {col : Bool}
    (hagree : ∀ u (hu : u ∈ S), c u = c₁ ⟨u, hu⟩)
    (hacyc : ((G.induce S).induce {z : S | c₁ z = col}).IsAcyclic) :
    (G.induce {v : V | v ∈ S ∧ c v = col}).IsAcyclic := by
  let f : G.induce {v : V | v ∈ S ∧ c v = col} →g (G.induce S).induce {z : S | c₁ z = col} :=
    { toFun := fun u => ⟨⟨u.1, u.2.1⟩, (hagree u.1 u.2.1).symm.trans u.2.2⟩
      map_rel' := id }
  refine hacyc.comap f ?_
  intro u v huv
  exact Subtype.ext (congrArg (fun z => z.1.1) huv)

/-- Sort a finset `S` in decreasing order of `d : V → ℕ`. -/
noncomputable def sortDesc [DecidableEq V] (d : V → ℕ) (S : Finset V) : List V :=
  S.toList.insertionSort (fun x y => d y ≤ d x)

lemma sortDesc_perm [DecidableEq V] (d : V → ℕ) (S : Finset V) :
    List.Perm (sortDesc d S) S.toList :=
  List.perm_insertionSort _ _

lemma sortDesc_nodup [DecidableEq V] (d : V → ℕ) (S : Finset V) :
    (sortDesc d S).Nodup :=
  (sortDesc_perm d S).nodup_iff.mpr S.nodup_toList

lemma mem_sortDesc [DecidableEq V] (d : V → ℕ) (S : Finset V) {x : V} :
    x ∈ sortDesc d S ↔ x ∈ S := by
  rw [(sortDesc_perm d S).mem_iff, Finset.mem_toList]

lemma sortDesc_pairwise [DecidableEq V] (d : V → ℕ) (S : Finset V) :
    (sortDesc d S).Pairwise (fun x y => d y ≤ d x) := by
  let r : V → V → Prop := fun x y => d y ≤ d x
  have : Std.Total r := ⟨fun x y => le_total (d y) (d x)⟩
  have : IsTrans V r := ⟨fun _ _ _ h₁ h₂ => le_trans h₂ h₁⟩
  exact List.pairwise_insertionSort r S.toList

/-- If `u` appears after `y` in `sortDesc d S`, then `d u ≤ d y`. -/
lemma dist_le_of_split_sortDesc [DecidableEq V] {d : V → ℕ} {S : Finset V}
    {l₁ l₂ : List V} {u y : V} (heq : sortDesc d S = l₁ ++ u :: l₂) (hy : y ∈ l₁) :
    d u ≤ d y := by
  have hp := sortDesc_pairwise d S
  rw [heq, List.pairwise_append] at hp
  exact hp.2.2 y hy u List.mem_cons_self

end WalkHelpers

/- ### Section 2: Greedy forest coloring along a good ordering -/

section GreedyOrdering

variable {V : Type*} (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj]

/-- A list of vertices that can be added to `S` one by one so that each added vertex has at most
`3` neighbors among the previously placed vertices. -/
def GoodOrder [DecidableEq V] (S : Finset V) : List V → Prop
  | [] => True
  | u :: L => u ∉ S ∧ (S.filter (G.Adj u)).card ≤ 3 ∧ GoodOrder (insert u S) L

/-- If every vertex in a duplicate-free list `L` (disjoint from `S`) has degree `≤ 4`, and either
has degree `≤ 3` or has a neighbor outside `S` and not preceding it in `L`, then `L` is a
`GoodOrder` over `S`. -/
lemma goodOrder_of_forall_split [DecidableEq V] {S : Finset V} {L : List V}
    (hdeg : ∀ x ∈ L, G.degree x ≤ 4)
    (hnodup : L.Nodup)
    (hdisj : ∀ x ∈ L, x ∉ S)
    (hstep : ∀ l₁ u l₂, L = l₁ ++ u :: l₂ →
      G.degree u ≤ 3 ∨ ∃ w, G.Adj u w ∧ w ∉ S ∧ w ∉ l₁) :
    GoodOrder G S L := by
  induction L generalizing S with
  | nil => trivial
  | cons u L ih =>
      simp only [List.nodup_cons] at hnodup
      have huS : u ∉ S := hdisj u List.mem_cons_self
      have hcard : (S.filter (G.Adj u)).card ≤ 3 := by
        rcases hstep [] u L rfl with h3 | ⟨w, hadj, hwS, _⟩
        · have hsub : S.filter (G.Adj u) ⊆ G.neighborFinset u := by
            intro x hx
            simp only [Finset.mem_filter, mem_neighborFinset] at hx ⊢
            exact hx.2
          exact (Finset.card_le_card hsub).trans (by simpa [card_neighborFinset_eq_degree] using h3)
        · have hsub : S.filter (G.Adj u) ⊆ (G.neighborFinset u).erase w := by
            intro x hx
            simp only [Finset.mem_filter, Finset.mem_erase, mem_neighborFinset] at hx ⊢
            exact ⟨fun hxw => hwS (hxw ▸ hx.1), hx.2⟩
          have hwmem : w ∈ G.neighborFinset u := (mem_neighborFinset G u w).mpr hadj
          have herase : ((G.neighborFinset u).erase w).card + 1 = G.degree u := by
            rw [Finset.card_erase_add_one hwmem, card_neighborFinset_eq_degree]
          have h4 := hdeg u List.mem_cons_self
          have := Finset.card_le_card hsub
          omega
      refine ⟨huS, hcard, ih (fun x hx => hdeg x (List.mem_cons_of_mem _ hx)) hnodup.2 ?_ ?_⟩
      · intro x hx hxins
        rcases Finset.mem_insert.mp hxins with rfl | hxS
        · exact hnodup.1 hx
        · exact hdisj x (List.mem_cons_of_mem _ hx) hxS
      · intro l₁ x l₂ heq
        rcases hstep (u :: l₁) x l₂ (by simp [heq]) with h3 | ⟨w, hadj, hwS, hwl⟩
        · exact Or.inl h3
        · refine Or.inr ⟨w, hadj, ?_, fun h => hwl (List.mem_cons_of_mem _ h)⟩
          intro hwins
          rcases Finset.mem_insert.mp hwins with rfl | hwS'
          · exact hwl List.mem_cons_self
          · exact hwS hwS'

omit [Fintype V] in
/-- Given a `Bool`-coloring `c` on `S` and `u` with `≤ 3` neighbors in `S`, we can choose a color
`col` for `u` so that `u` has at most one neighbor of color `col` in `S`. -/
lemma exists_color_unique_adj [DecidableEq V] {S : Finset V} {u : V} (c : V → Bool)
    (hcard : (S.filter (G.Adj u)).card ≤ 3) :
    ∃ col : Bool, ∀ x ∈ S, ∀ y ∈ S,
      c x = col → c y = col → G.Adj u x → G.Adj u y → x = y := by
  let N₀ := S.filter (fun x => G.Adj u x ∧ c x = false)
  let N₁ := S.filter (fun x => G.Adj u x ∧ c x = true)
  have hsum : N₀.card + N₁.card = (S.filter (G.Adj u)).card := by
    rw [← Finset.card_union_of_disjoint]
    · congr 1
      ext x
      simp only [N₀, N₁, Finset.mem_union, Finset.mem_filter]
      cases c x <;> simp
    · rw [Finset.disjoint_left]
      intro x hx0 hx1
      simp only [N₀, N₁, Finset.mem_filter] at hx0 hx1
      exact Bool.false_ne_true (hx0.2.2.symm.trans hx1.2.2)
  by_cases h0 : N₀.card ≤ 1
  · refine ⟨false, fun x hx y hy hcx hcy hux huy => ?_⟩
    exact Finset.card_le_one.mp h0 x (Finset.mem_filter.mpr ⟨hx, hux, hcx⟩)
      y (Finset.mem_filter.mpr ⟨hy, huy, hcy⟩)
  · have h1 : N₁.card ≤ 1 := by omega
    refine ⟨true, fun x hx y hy hcx hcy hux huy => ?_⟩
    exact Finset.card_le_one.mp h1 x (Finset.mem_filter.mpr ⟨hx, hux, hcx⟩)
      y (Finset.mem_filter.mpr ⟨hy, huy, hcy⟩)

omit [Fintype V] in
/-- Greedily extend a forest coloring from `S₀` along a `GoodOrder` list `L`, preserving:
1. the coloring on `S₀`,
2. acyclicity of both color classes on `S₀ ∪ L.toFinset`,
3. non-reachability in the `false`-class between any two `false`-colored vertices of `S₀` that
   were already in distinct components of the `false`-class on `S₀`. -/
lemma greedy_extend_coloring [DecidableEq V] {S₀ : Finset V} {L : List V} {c₀ : V → Bool}
    (hgood : GoodOrder G S₀ L)
    (hacyc₀ : (G.induce {x : V | x ∈ S₀ ∧ c₀ x = false}).IsAcyclic)
    (hacyc₁ : (G.induce {x : V | x ∈ S₀ ∧ c₀ x = true}).IsAcyclic) :
    ∃ c : V → Bool,
      (∀ x ∈ S₀, c x = c₀ x) ∧
      (G.induce {x : V | x ∈ S₀ ∪ L.toFinset ∧ c x = false}).IsAcyclic ∧
      (G.induce {x : V | x ∈ S₀ ∪ L.toFinset ∧ c x = true}).IsAcyclic ∧
      (∀ a b (ha : a ∈ S₀) (hb : b ∈ S₀) (hca : c₀ a = false) (hcb : c₀ b = false),
        ¬ (G.induce {x : V | x ∈ S₀ ∧ c₀ x = false}).Reachable ⟨a, ha, hca⟩ ⟨b, hb, hcb⟩ →
        ∀ (ha' : a ∈ S₀ ∪ L.toFinset) (hb' : b ∈ S₀ ∪ L.toFinset)
          (hca' : c a = false) (hcb' : c b = false),
        ¬ (G.induce {x : V | x ∈ S₀ ∪ L.toFinset ∧ c x = false}).Reachable
            ⟨a, ha', hca'⟩ ⟨b, hb', hcb'⟩) := by
  induction L generalizing S₀ c₀ with
  | nil =>
      have hS : S₀ ∪ ([] : List V).toFinset = S₀ := by simp
      refine ⟨c₀, fun _ _ => rfl, ?_, ?_, ?_⟩
      · rw [hS]; exact hacyc₀
      · rw [hS]; exact hacyc₁
      · intro a b ha hb hca hcb hnot ha' hb' hca' hcb' hreach
        obtain ⟨p⟩ := hreach
        exact hnot ⟨walkInduce {x : V | x ∈ S₀ ∧ c₀ x = false} p
          (fun x _ => ⟨by simpa using x.2.1, x.2.2⟩)⟩
  | cons u L ih =>
      rcases hgood with ⟨huS, hcard, hgood'⟩
      obtain ⟨col, huniq⟩ := exists_color_unique_adj G c₀ hcard
      let S₁ : Finset V := insert u S₀
      let c₁ : V → Bool := Function.update c₀ u col
      have hc₁_eq : ∀ x ∈ S₀, c₁ x = c₀ x := fun x hx =>
        Function.update_of_ne (by rintro rfl; exact huS hx) col c₀
      have hset_false :
          {x : V | x ∈ S₁ ∧ c₁ x = false} =
          if col = false then insert u {x : V | x ∈ S₀ ∧ c₀ x = false}
          else {x : V | x ∈ S₀ ∧ c₀ x = false} := by
        ext x
        by_cases hxu : x = u
        · subst hxu
          cases col <;> simp [S₁, c₁, huS]
        · cases col <;> simp [S₁, c₁, hxu]
      have hset_true :
          {x : V | x ∈ S₁ ∧ c₁ x = true} =
          if col = true then insert u {x : V | x ∈ S₀ ∧ c₀ x = true}
          else {x : V | x ∈ S₀ ∧ c₀ x = true} := by
        ext x
        by_cases hxu : x = u
        · subst hxu
          cases col <;> simp [S₁, c₁, huS]
        · cases col <;> simp [S₁, c₁, hxu]
      have hacyc₁_false : (G.induce {x : V | x ∈ S₁ ∧ c₁ x = false}).IsAcyclic := by
        rw [hset_false]
        cases col
        · rw [if_pos rfl]
          exact isAcyclic_induce_insert_of_unique_adj hacyc₀
            (fun x hx y hy hux huy => huniq x hx.1 y hy.1 hx.2 hy.2 hux huy)
        · rw [if_neg Bool.false_ne_true.symm]
          exact hacyc₀
      have hacyc₁_true : (G.induce {x : V | x ∈ S₁ ∧ c₁ x = true}).IsAcyclic := by
        rw [hset_true]
        cases col
        · rw [if_neg Bool.false_ne_true]
          exact hacyc₁
        · rw [if_pos rfl]
          exact isAcyclic_induce_insert_of_unique_adj hacyc₁
            (fun x hx y hy hux huy => huniq x hx.1 y hy.1 hx.2 hy.2 hux huy)
      have hstep_not_reach :
          ∀ a b (ha : a ∈ S₀) (hb : b ∈ S₀) (hca : c₀ a = false) (hcb : c₀ b = false),
            ¬ (G.induce {x : V | x ∈ S₀ ∧ c₀ x = false}).Reachable ⟨a, ha, hca⟩ ⟨b, hb, hcb⟩ →
            ¬ (G.induce {x : V | x ∈ S₁ ∧ c₁ x = false}).Reachable
                ⟨a, Finset.mem_insert_of_mem ha, (hc₁_eq a ha).trans hca⟩
                ⟨b, Finset.mem_insert_of_mem hb, (hc₁_eq b hb).trans hcb⟩ := by
        intro a b ha hb hca hcb hnot hreach
        cases hcol : col
        · have hsub : {x : V | x ∈ S₁ ∧ c₁ x = false} =
              insert u {x : V | x ∈ S₀ ∧ c₀ x = false} := by
            rw [hset_false, hcol, if_pos rfl]
          have hreach' : (G.induce (insert u {x : V | x ∈ S₀ ∧ c₀ x = false})).Reachable
              ⟨a, Set.mem_insert_of_mem u ⟨ha, hca⟩⟩
              ⟨b, Set.mem_insert_of_mem u ⟨hb, hcb⟩⟩ := by
            obtain ⟨p⟩ := hreach
            exact ⟨walkInduce (insert u {x : V | x ∈ S₀ ∧ c₀ x = false}) p (fun x _ => hsub ▸ x.2)⟩
          exact not_reachable_induce_insert_of_unique_adj (A := {x : V | x ∈ S₀ ∧ c₀ x = false})
            ⟨ha, hca⟩ ⟨hb, hcb⟩ (fun h => huS h.1) hnot
            (fun x hx y hy hux huy => huniq x hx.1 y hy.1 (hx.2.trans hcol.symm)
              (hy.2.trans hcol.symm) hux huy) hreach'
        · have hsub : {x : V | x ∈ S₁ ∧ c₁ x = false} = {x : V | x ∈ S₀ ∧ c₀ x = false} := by
            rw [hset_false, hcol, if_neg Bool.false_ne_true.symm]
          obtain ⟨p⟩ := hreach
          exact hnot ⟨walkInduce {x : V | x ∈ S₀ ∧ c₀ x = false} p (fun x _ => hsub ▸ x.2)⟩
      obtain ⟨c, hc_eq, hfin_false, hfin_true, hfin_nr⟩ := ih hgood' hacyc₁_false hacyc₁_true
      have hunion : S₀ ∪ (u :: L).toFinset = S₁ ∪ L.toFinset := by
        ext x
        simp only [S₁, Finset.mem_union, List.toFinset_cons, Finset.mem_insert]
        tauto
      refine ⟨c, ?_, ?_, ?_, ?_⟩
      · intro x hx
        exact (hc_eq x (Finset.mem_insert_of_mem hx)).trans (hc₁_eq x hx)
      · rw [hunion]; exact hfin_false
      · rw [hunion]; exact hfin_true
      · intro a b ha hb hca hcb hnot ha' hb' hca' hcb'
        have hnr1 := hstep_not_reach a b ha hb hca hcb hnot
        have hnr2 := hfin_nr a b (Finset.mem_insert_of_mem ha) (Finset.mem_insert_of_mem hb)
          ((hc₁_eq a ha).trans hca) ((hc₁_eq b hb).trans hcb) hnr1
          (hunion ▸ ha') (hunion ▸ hb') hca' hcb'
        intro hreach
        obtain ⟨p⟩ := hreach
        exact hnr2 ⟨walkInduce {x : V | x ∈ S₁ ∪ L.toFinset ∧ c x = false} p
          (fun x _ => ⟨hunion ▸ x.2.1, x.2.2⟩)⟩

/-- **Case 1 (Degenerate case)**: Every connected finite simple graph with `∀ u, G.degree u ≤ 4`
and at least one vertex of degree `≤ 3` admits a forest bipartition. -/
theorem exists_forestColoring_of_exists_degree_le_three
    (hconn : G.Connected) (hdeg : ∀ u : V, G.degree u ≤ 4)
    (h3 : ∃ v : V, G.degree v ≤ 3) :
    ∃ c : V → Bool, IsForestColoring G c := by
  let _ := Classical.decEq V
  obtain ⟨v, hv3⟩ := h3
  let d : V → ℕ := fun x => G.dist v x
  let L : List V := sortDesc d Finset.univ
  have hgood : GoodOrder G ∅ L := by
    refine goodOrder_of_forall_split G (fun x _ => hdeg x) (sortDesc_nodup d _)
      (fun _ _ => Finset.notMem_empty _) ?_
    intro l₁ u l₂ heq
    by_cases huv : u = v
    · exact Or.inl (huv ▸ hv3)
    · obtain ⟨w, hadj, hlt⟩ := exists_adj_dist_lt_of_connected hconn huv
      refine Or.inr ⟨w, hadj, Finset.notMem_empty _, fun hwl => ?_⟩
      have hle : d u ≤ d w := dist_le_of_split_sortDesc heq hwl
      dsimp only [d] at hle
      omega
  have hacyc_empty : ∀ b : Bool,
      (G.induce {x : V | x ∈ (∅ : Finset V) ∧ (fun _ => false) x = b}).IsAcyclic := by
    intro b
    have : Subsingleton {x : V | x ∈ (∅ : Finset V) ∧ (fun _ => false) x = b} :=
      ⟨fun ⟨_, hx⟩ _ => (Finset.notMem_empty _ hx.1).elim⟩
    exact IsAcyclic.of_subsingleton
  obtain ⟨c, _, hfalse, htrue, _⟩ :=
    greedy_extend_coloring G hgood (hacyc_empty false) (hacyc_empty true)
  have hLuniv : (∅ : Finset V) ∪ L.toFinset = Finset.univ := by
    ext x
    simp [L, mem_sortDesc]
  refine ⟨c, ?_, ?_⟩
  · have hset : {x : V | x ∈ (∅ : Finset V) ∪ L.toFinset ∧ c x = false} =
        {x : V | c x = false} := by
      ext x; simp [hLuniv]
    rwa [hset] at hfalse
  · have hset : {x : V | x ∈ (∅ : Finset V) ∪ L.toFinset ∧ c x = true} =
        {x : V | c x = true} := by
      ext x; simp [hLuniv]
    rwa [hset] at htrue

end GreedyOrdering

/- ### Section 3: Cut-vertex decomposition -/

section CutVertex

variable {V : Type*} (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj]

/-- **Case 2a (Cut-vertex case)**: If `G` is connected, `∀ u, G.degree u ≤ 4`, and `G` has a cut
vertex `x`, then `G` admits a forest bipartition. -/
theorem exists_forestColoring_of_cut_vertex
    (hconn : G.Connected) (hdeg : ∀ u : V, G.degree u ≤ 4)
    {x : V} (hcut : ¬ (G.induce {u : V | u ≠ x}).Connected) :
    ∃ c : V → Bool, IsForestColoring G c := by
  let _ := Classical.decEq V
  by_cases hnt : Nontrivial V
  swap
  · rw [not_nontrivial_iff_subsingleton] at hnt
    refine exists_forestColoring_of_exists_degree_le_three G hconn hdeg ⟨x, ?_⟩
    have : G.degree x = 0 := by
      rw [degree_eq_zero]
      intro y hadj
      exact hadj.ne (Subsingleton.elim x y)
    omega
  have hne_del : Nonempty {u : V | u ≠ x} := by
    obtain ⟨u, hu⟩ := exists_ne x
    exact ⟨⟨u, hu⟩⟩
  let Gx := G.induce {u : V | u ≠ x}
  have hnot_pre : ¬ Gx.Preconnected := fun hpre => hcut ⟨hpre⟩
  unfold Preconnected at hnot_pre
  push Not at hnot_pre
  obtain ⟨u₁, u₂, hu₁₂⟩ := hnot_pre
  let A : Set V := {u : V | ∃ hu : u ≠ x, Gx.Reachable u₁ ⟨u, hu⟩}
  let B : Set V := {u : V | u ≠ x ∧ u ∉ A}
  let SA : Set V := insert x A
  let SB : Set V := insert x B
  have hu₁A : u₁.1 ∈ A := ⟨u₁.2, Reachable.rfl⟩
  have hu₂B : u₂.1 ∈ B := ⟨u₂.2, fun ⟨_, hr⟩ => hu₁₂ hr⟩
  have hxA : x ∉ A := fun ⟨hx, _⟩ => hx rfl
  have hxB : x ∉ B := fun ⟨hx, _⟩ => hx rfl
  have hAB_disj : ∀ u, u ∈ A → u ∈ B → False := fun _ hA hB => hB.2 hA
  have hnoAB : ∀ a ∈ A, ∀ y, G.Adj a y → y ∈ A ∨ y = x := by
    intro a ⟨ha, hra⟩ y hadj
    by_cases hyx : y = x
    · exact Or.inr hyx
    · exact Or.inl ⟨hyx, hra.trans (Adj.reachable (G := Gx) hadj)⟩
  have hnoBA : ∀ b ∈ B, ∀ y, G.Adj b y → y ∈ B ∨ y = x := by
    intro b ⟨hb, hbA⟩ y hadj
    by_cases hyx : y = x
    · exact Or.inr hyx
    · exact Or.inl ⟨hyx, fun ⟨_, hry⟩ => hbA ⟨hb, hry.trans (Adj.reachable (G := Gx) hadj.symm)⟩⟩
  have hconn₁ : (G.induce SA).Connected := by
    rw [connected_iff_exists_forall_reachable]
    refine ⟨⟨x, Set.mem_insert x A⟩, fun w => ?_⟩
    rcases w.2 with hwx | hwA
    · have : w = ⟨x, Set.mem_insert x A⟩ := Subtype.ext hwx
      rw [this]
    · obtain ⟨p, hp⟩ := hconn.exists_isPath w.1 x
      exact ⟨(walkToInduce SA p (support_path_subset_insert_of_no_edge hnoAB p hp hwA)).reverse⟩
  have hconn₂ : (G.induce SB).Connected := by
    rw [connected_iff_exists_forall_reachable]
    refine ⟨⟨x, Set.mem_insert x B⟩, fun w => ?_⟩
    rcases w.2 with hwx | hwB
    · have : w = ⟨x, Set.mem_insert x B⟩ := Subtype.ext hwx
      rw [this]
    · obtain ⟨p, hp⟩ := hconn.exists_isPath w.1 x
      exact ⟨(walkToInduce SB p (support_path_subset_insert_of_no_edge hnoBA p hp hwB)).reverse⟩
  have hx_nbr_A : ∃ a ∈ A, G.Adj x a := by
    obtain ⟨p⟩ := hconn₁ ⟨x, Set.mem_insert x A⟩ ⟨u₁.1, Set.mem_insert_of_mem x hu₁A⟩
    have hnn : ¬ p.Nil := Walk.not_nil_of_ne (fun h => u₁.2 (congrArg Subtype.val h).symm)
    have hadj : G.Adj x p.snd.1 := p.adj_snd hnn
    have hsndA : p.snd.1 ∈ A := by
      rcases p.snd.2 with h | h
      · exact (hadj.ne h.symm).elim
      · exact h
    exact ⟨p.snd.1, hsndA, hadj⟩
  have hx_nbr_B : ∃ b ∈ B, G.Adj x b := by
    obtain ⟨p⟩ := hconn₂ ⟨x, Set.mem_insert x B⟩ ⟨u₂.1, Set.mem_insert_of_mem x hu₂B⟩
    have hnn : ¬ p.Nil := Walk.not_nil_of_ne (fun h => u₂.2 (congrArg Subtype.val h).symm)
    have hadj : G.Adj x p.snd.1 := p.adj_snd hnn
    have hsndB : p.snd.1 ∈ B := by
      rcases p.snd.2 with h | h
      · exact (hadj.ne h.symm).elim
      · exact h
    exact ⟨p.snd.1, hsndB, hadj⟩
  let _ : DecidablePred (· ∈ SA) := Classical.decPred _
  let _ : DecidablePred (· ∈ SB) := Classical.decPred _
  let _ : Fintype SA := Subtype.fintype (· ∈ SA)
  let _ : Fintype SB := Subtype.fintype (· ∈ SB)
  obtain ⟨b₀, hb₀B, hxb₀⟩ := hx_nbr_B
  obtain ⟨a₀, ha₀A, hxa₀⟩ := hx_nbr_A
  have hdeg₁_x : (G.induce SA).degree ⟨x, Set.mem_insert x A⟩ ≤ 3 := by
    have hb₀_not : b₀ ∉ SA := by
      intro h; rcases h with rfl | hA
      · exact hxB hb₀B
      · exact hAB_disj b₀ hA hb₀B
    have hlt := degree_induce_add_one_le_of_adj_notMem (G := G)
      (⟨x, Set.mem_insert x A⟩ : SA) hb₀_not hxb₀
    dsimp only at hlt
    have h4 := hdeg x
    omega
  have hdeg₂_x : (G.induce SB).degree ⟨x, Set.mem_insert x B⟩ ≤ 3 := by
    have ha₀_not : a₀ ∉ SB := by
      intro h; rcases h with rfl | hB
      · exact hxA ha₀A
      · exact hAB_disj a₀ ha₀A hB
    have hlt := degree_induce_add_one_le_of_adj_notMem (G := G)
      (⟨x, Set.mem_insert x B⟩ : SB) ha₀_not hxa₀
    dsimp only at hlt
    have h4 := hdeg x
    omega
  obtain ⟨c₁, hc₁⟩ := exists_forestColoring_of_exists_degree_le_three (G.induce SA)
    hconn₁ (fun u => (degree_induce_le u).trans (hdeg u.1)) ⟨⟨x, Set.mem_insert x A⟩, hdeg₁_x⟩
  obtain ⟨c₂_raw, hc₂_raw⟩ := exists_forestColoring_of_exists_degree_le_three (G.induce SB)
    hconn₂ (fun u => (degree_induce_le u).trans (hdeg u.1)) ⟨⟨x, Set.mem_insert x B⟩, hdeg₂_x⟩
  let c₂ : SB → Bool :=
    if c₂_raw ⟨x, Set.mem_insert x B⟩ = c₁ ⟨x, Set.mem_insert x A⟩ then c₂_raw
    else fun u => !c₂_raw u
  have hc₂ : IsForestColoring (G.induce SB) c₂ := by
    dsimp only [c₂]
    split_ifs
    · exact hc₂_raw
    · exact hc₂_raw.not
  have hc_agree : c₂ ⟨x, Set.mem_insert x B⟩ = c₁ ⟨x, Set.mem_insert x A⟩ := by
    dsimp only [c₂]
    split_ifs with h
    · exact h
    · cases h1 : c₁ ⟨x, Set.mem_insert x A⟩ <;> cases h2 : c₂_raw ⟨x, Set.mem_insert x B⟩ <;>
        simp_all
  let c : V → Bool := fun u =>
    if hu : u ∈ SA then c₁ ⟨u, hu⟩
    else c₂ ⟨u, Set.mem_insert_of_mem x ⟨fun h => hu (h ▸ Set.mem_insert x A),
      fun h => hu (Set.mem_insert_of_mem x h)⟩⟩
  have hc_on_A : ∀ u (hu : u ∈ SA), c u = c₁ ⟨u, hu⟩ := fun u hu => dif_pos hu
  have hc_on_B : ∀ u (hu : u ∈ SB), c u = c₂ ⟨u, hu⟩ := by
    intro u hu
    rcases hu with hux | huB
    · subst hux
      rw [hc_on_A u (Set.mem_insert u A), hc_agree]
    · have hnot : u ∉ SA := by
        intro h; rcases h with rfl | huA
        · exact hxB huB
        · exact hAB_disj u huA huB
      simp [c, hnot]
  have hacyc_col : ∀ col : Bool, (G.induce {v : V | c v = col}).IsAcyclic := by
    intro col w p hp
    have hacycA : (G.induce {v : V | v ∈ SA ∧ c v = col}).IsAcyclic := by
      cases col
      · exact isAcyclic_induce_of_subinduce hc_on_A hc₁.1
      · exact isAcyclic_induce_of_subinduce hc_on_A hc₁.2
    have hacycB : (G.induce {v : V | v ∈ SB ∧ c v = col}).IsAcyclic := by
      cases col
      · exact isAcyclic_induce_of_subinduce hc_on_B hc₂.1
      · exact isAcyclic_induce_of_subinduce hc_on_B hc₂.2
    by_cases hsubA : ∀ z ∈ p.support, z.1 ∈ SA
    · exact hacycA (walkInduce {v : V | v ∈ SA ∧ c v = col} p (fun z hz => ⟨hsubA z hz, z.2⟩))
        (isCycle_walkInduce {v : V | v ∈ SA ∧ c v = col} hp _)
    by_cases hsubB : ∀ z ∈ p.support, z.1 ∈ SB
    · exact hacycB (walkInduce {v : V | v ∈ SB ∧ c v = col} p (fun z hz => ⟨hsubB z hz, z.2⟩))
        (isCycle_walkInduce {v : V | v ∈ SB ∧ c v = col} hp _)
    push Not at hsubA hsubB
    obtain ⟨b', hb'_mem, hb'_notA⟩ := hsubA
    obtain ⟨a', ha'_mem, ha'_notB⟩ := hsubB
    have hb'B : b'.1 ∈ B :=
      ⟨fun h => hb'_notA (h ▸ Set.mem_insert x A), fun h => hb'_notA (Set.mem_insert_of_mem x h)⟩
    have ha'A : a'.1 ∈ A := by
      by_cases hax : a'.1 = x
      · exact (ha'_notB (hax ▸ Set.mem_insert x B)).elim
      · by_contra haA
        exact ha'_notB (Set.mem_insert_of_mem x ⟨hax, haA⟩)
    let q := p.rotate a' ha'_mem
    have hq : q.IsCycle := hp.rotate ha'_mem
    have hb'_q : b' ∈ q.support := (Walk.mem_support_rotate_iff p a' ha'_mem).mpr hb'_mem
    let q₁ := q.takeUntil b' hb'_q
    let q₂ := q.dropUntil b' hb'_q
    have hspec : q₁.append q₂ = q := q.take_spec hb'_q
    have hits_x : ∀ {s t : {v : V | c v = col}} (r : (G.induce {v : V | c v = col}).Walk s t),
        s.1 ∈ A → t.1 ∈ B → ∃ z ∈ r.support, z.1 = x := by
      intro s t r
      induction r with
      | nil =>
          intro hs ht
          exact (hAB_disj _ hs ht).elim
      | @cons s s' t hadj r ih =>
          intro hs ht
          rcases hnoAB s.1 hs s'.1 hadj with hs'A | hs'x
          · obtain ⟨z, hz, hzx⟩ := ih hs'A ht
            exact ⟨z, List.mem_cons_of_mem _ hz, hzx⟩
          · exact ⟨s', List.mem_cons_of_mem _ r.start_mem_support, hs'x⟩
    obtain ⟨z₁, hz₁_mem, hz₁x⟩ := hits_x q₁ ha'A hb'B
    obtain ⟨z₂, hz₂_rev, hz₂x⟩ := hits_x q₂.reverse ha'A hb'B
    have hz₂_mem : z₂ ∈ q₂.support := by
      rw [Walk.support_reverse, List.mem_reverse] at hz₂_rev
      exact hz₂_rev
    have hz_eq : z₁ = z₂ := Subtype.ext (hz₁x.trans hz₂x.symm)
    have hz₁_ne_a' : z₁ ≠ a' := fun h => hxA (hz₁x ▸ h ▸ ha'A)
    have hz₂_ne_b' : z₂ ≠ b' := fun h => hxB (hz₂x ▸ h ▸ hb'B)
    have hz₁_tail : z₁ ∈ q₁.support.tail := by
      have hne : q₁.support ≠ [] := q₁.support_ne_nil
      have hcons := List.cons_head_tail hne
      have hhead : q₁.support.head hne = a' := q₁.head_support
      rw [← hcons, hhead, List.mem_cons] at hz₁_mem
      exact hz₁_mem.resolve_left hz₁_ne_a'
    have hz₂_tail : z₂ ∈ q₂.support.tail := by
      have hne : q₂.support ≠ [] := q₂.support_ne_nil
      have hcons := List.cons_head_tail hne
      have hhead : q₂.support.head hne = b' := q₂.head_support
      rw [← hcons, hhead, List.mem_cons] at hz₂_mem
      exact hz₂_mem.resolve_left hz₂_ne_b'
    have hnodup : (q₁.support.tail ++ q₂.support.tail).Nodup := by
      rw [← Walk.tail_support_append, hspec]
      exact hq.support_nodup
    exact (List.nodup_append.mp hnodup).2.2 z₁ hz₁_tail z₂ hz₂_tail hz_eq
  exact ⟨c, hacyc_col false, hacyc_col true⟩

end CutVertex

/- ### Section 4: Lovász's cherry lemma for 2-connected graphs -/

section CherryLemma

variable {W : Type*}

/-- `(c, S)` is a separating pair in `H` if `S` is a nonempty proper subset of `V(H) \ {c}`
with no edges leaving `S` except to `c`. -/
def IsSepPair (H : SimpleGraph W) (c : W) (S : Finset W) : Prop :=
  S.Nonempty ∧ c ∉ S ∧ (∃ z : W, z ∉ S ∧ z ≠ c) ∧
    ∀ x ∈ S, ∀ y, H.Adj x y → y ∈ S ∨ y = c

/-- A separating pair `(c, S)` witnesses that `H - {c}` is disconnected. -/
lemma not_connected_induce_ne_of_isSepPair {H : SimpleGraph W} {c : W} {S : Finset W}
    (hsep : IsSepPair H c S) :
    ¬ (H.induce {x : W | x ≠ c}).Connected := by
  intro hconn
  obtain ⟨s, hs⟩ := hsep.1
  obtain ⟨z, hzS, hzc⟩ := hsep.2.2.1
  have hsc : s ≠ c := fun h => hsep.2.1 (h ▸ hs)
  obtain ⟨p⟩ := hconn ⟨s, hsc⟩ ⟨z, hzc⟩
  have hc_mem : c ∈ (walkFromInduce p).support := mem_support_of_walk_leaving
    (A := (S : Set W)) (fun a ha y hadj => hsep.2.2.2 a ha y hadj) (walkFromInduce p) hs hzS
  rw [support_walkFromInduce, List.mem_map] at hc_mem
  obtain ⟨u, _, huc⟩ := hc_mem
  exact u.2 huc

/-- In a connected graph `H` with a separating pair `(c, S)`, every vertex outside `S` is
reachable from `c` in `H - S`. -/
lemma reachable_exterior_of_isSepPair {H : SimpleGraph W} (hconn : H.Connected)
    {c : W} {S : Finset W} (hsep : IsSepPair H c S) {z : W} (hz : z ∉ S) :
    (H.induce {x : W | x ∉ S}).Reachable ⟨z, hz⟩ ⟨c, hsep.2.1⟩ := by
  obtain ⟨p, hp⟩ := hconn.exists_isPath z c
  have havoid := path_avoids_sep (A := (S : Set W))
    (fun a ha y hadj => hsep.2.2.2 a ha y hadj) p hp hz hsep.2.1
  exact ⟨walkToInduce {x : W | x ∉ S} p havoid⟩

/-- Inside any separating pair `(c₀, S₀)` of a finite connected graph `H`, there exists a
separating pair `(c, S)` with `S ⊆ S₀` such that no vertex of `S` is a cut vertex of `H`. -/
lemma exists_minimal_sepPair [Fintype W] [DecidableEq W] {H : SimpleGraph W}
    (hconn : H.Connected) {c₀ : W} {S₀ : Finset W} (hsep₀ : IsSepPair H c₀ S₀) :
    ∃ c S, IsSepPair H c S ∧ S ⊆ S₀ ∧ ∀ a ∈ S, (H.induce {x : W | x ≠ a}).Connected := by
  let _ : DecidablePred (fun p : W × Finset W => IsSepPair H p.1 p.2 ∧ p.2 ⊆ S₀) :=
    Classical.decPred _
  let P : Finset (W × Finset W) :=
    Finset.univ.filter (fun p => IsSepPair H p.1 p.2 ∧ p.2 ⊆ S₀)
  have hPne : P.Nonempty := ⟨(c₀, S₀), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsep₀, subset_rfl⟩⟩
  obtain ⟨⟨c, S⟩, hmem, hmin⟩ := Finset.exists_min_image P (fun p => p.2.card) hPne
  obtain ⟨hsep, hsub₀⟩ := (Finset.mem_filter.mp hmem).2
  refine ⟨c, S, hsep, hsub₀, fun a ha => ?_⟩
  by_contra hnotconn
  have hca : c ≠ a := fun h => hsep.2.1 (h ▸ ha)
  have hne_a : Nonempty {x : W | x ≠ a} := ⟨⟨c, hca⟩⟩
  let Ha := H.induce {x : W | x ≠ a}
  have hnot_pre : ¬ Ha.Preconnected := fun hpre => hnotconn ⟨hpre⟩
  unfold Preconnected at hnot_pre
  push Not at hnot_pre
  obtain ⟨u₁, u₂, hu₁₂⟩ := hnot_pre
  let c' : {x : W | x ≠ a} := ⟨c, hca⟩
  have hex : ∃ x₀ : {x : W | x ≠ a}, ¬ Ha.Reachable c' x₀ := by
    by_cases h1 : Ha.Reachable c' u₁
    · exact ⟨u₂, fun h2 => hu₁₂ (h1.symm.trans h2)⟩
    · exact ⟨u₁, h1⟩
  obtain ⟨x₀, hx₀⟩ := hex
  let _ : DecidablePred (fun y : W => ∃ hy : y ≠ a, Ha.Reachable x₀ ⟨y, hy⟩) := Classical.decPred _
  let S' : Finset W := Finset.univ.filter (fun y => ∃ hy : y ≠ a, Ha.Reachable x₀ ⟨y, hy⟩)
  have hS'_ne : S'.Nonempty := ⟨x₀.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, x₀.2, Reachable.rfl⟩⟩
  have ha_not : a ∉ S' := by
    intro h
    obtain ⟨hne, _⟩ := (Finset.mem_filter.mp h).2
    exact hne rfl
  have hc_not : c ∉ S' := by
    intro h
    obtain ⟨_, hr⟩ := (Finset.mem_filter.mp h).2
    exact hx₀ hr.symm
  have hS'_no : ∀ x ∈ S', ∀ y, H.Adj x y → y ∈ S' ∨ y = a := by
    intro x hx y hadj
    by_cases hya : y = a
    · exact Or.inr hya
    · left
      obtain ⟨_, hr⟩ := (Finset.mem_filter.mp hx).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hya, hr.trans (Adj.reachable (G := Ha) hadj)⟩
  have hS'_sub_S : S' ⊆ S := by
    intro y hy
    by_contra hyS
    obtain ⟨hyne, hrx⟩ := (Finset.mem_filter.mp hy).2
    have hrext := reachable_exterior_of_isSepPair hconn hsep hyS
    have hrc : Ha.Reachable ⟨y, hyne⟩ c' := by
      obtain ⟨p⟩ := hrext
      exact ⟨walkInduce {x : W | x ≠ a} p (fun z _ hza => z.2 (hza ▸ ha))⟩
    exact hx₀ (hrx.trans hrc).symm
  have hsep' : IsSepPair H a S' := ⟨hS'_ne, ha_not, ⟨c, hc_not, hca⟩, hS'_no⟩
  have hmem' : (a, S') ∈ P :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsep', hS'_sub_S.trans hsub₀⟩
  have hle : S.card ≤ S'.card := hmin (a, S') hmem'
  have hlt : S'.card < S.card :=
    Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hS'_sub_S, fun heq => ha_not (heq ▸ ha)⟩)
  omega

/-- **Lovász's Cherry Lemma**: Every `2`-connected non-complete finite simple graph with minimum
degree at least `3` has a vertex `v` with two nonadjacent neighbors `a, b` such that
`G - {a, b}` is connected. -/
theorem exists_good_cherry_of_two_connected {V : Type*} (G : SimpleGraph V)
    [Fintype V] [DecidableRel G.Adj]
    (hconn : G.Connected)
    (h2conn : ∀ x : V, (G.induce {u : V | u ≠ x}).Connected)
    (hdeg3 : ∀ u : V, 3 ≤ G.degree u)
    (hnotTop : G ≠ ⊤) :
    ∃ v a b : V, G.Adj v a ∧ G.Adj v b ∧ a ≠ b ∧ ¬ G.Adj a b ∧
      (G.induce {u : V | u ≠ a ∧ u ≠ b}).Connected := by
  let _ := Classical.decEq V
  by_cases h3conn : ∀ u v : V, u ≠ v → (G.induce {w : V | w ≠ u ∧ w ≠ v}).Connected
  · have hex : ∃ x y : V, x ≠ y ∧ ¬ G.Adj x y := by
      by_contra hall
      push Not at hall
      exact hnotTop (G.eq_top_iff_forall_ne_adj.mpr hall)
    obtain ⟨x, y, hxy, hnadj⟩ := hex
    have hlt : 1 < G.dist x y := hconn.one_lt_dist_of_ne_of_not_adj hxy hnadj
    obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist x y
    obtain ⟨a, v, b, hav, hvb, hnab, hne⟩ := Walk.exists_adj_adj_not_adj_ne hp hlt
    exact ⟨v, a, b, hav.symm, hvb, hne, hnab, h3conn a b hne⟩
  · push Not at h3conn
    obtain ⟨v, w, hvw, hcut2⟩ := h3conn
    let H := G.induce {u : V | u ≠ v}
    have hHconn : H.Connected := h2conn v
    let w' : {u : V | u ≠ v} := ⟨w, hvw.symm⟩
    let Hw := H.induce {x : {u : V | u ≠ v} | x ≠ w'}
    have hHw_not_conn : ¬ Hw.Connected := by
      let e : Hw ≃g G.induce {u : V | u ≠ v ∧ u ≠ w} :=
        { toFun := fun z => ⟨z.1.1, z.1.2, fun h => z.2 (Subtype.ext h)⟩
          invFun := fun z => ⟨⟨z.1, z.2.1⟩, fun h => z.2.2 (congrArg Subtype.val h)⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl
          map_rel_iff' := Iff.rfl }
      exact fun h => hcut2 (e.connected_iff.mp h)
    have hHw_ne : Nonempty {x : {u : V | u ≠ v} | x ≠ w'} := by
      have hcard : 3 ≤ (G.neighborFinset v).card := by
        rw [card_neighborFinset_eq_degree]; exact hdeg3 v
      have hsub : ¬ G.neighborFinset v ⊆ {w} := by
        intro h
        have hle := Finset.card_le_card h
        rw [Finset.card_singleton] at hle
        omega
      obtain ⟨z, hzN, hzw⟩ := Finset.not_subset.mp hsub
      have hzv : z ≠ v := ((mem_neighborFinset G v z).mp hzN).ne.symm
      exact ⟨⟨⟨z, hzv⟩, fun h => hzw (Finset.mem_singleton.mpr (congrArg Subtype.val h))⟩⟩
    have hHw_not_pre : ¬ Hw.Preconnected := fun hpre => hHw_not_conn ⟨hpre⟩
    unfold Preconnected at hHw_not_pre
    push Not at hHw_not_pre
    obtain ⟨u₁, u₂, hu₁₂⟩ := hHw_not_pre
    let _ : DecidablePred (fun x : {u : V | u ≠ v} => ∃ hx : x ≠ w', Hw.Reachable u₁ ⟨x, hx⟩) :=
      Classical.decPred _
    let S₀ : Finset {u : V | u ≠ v} :=
      Finset.univ.filter (fun x => ∃ hx : x ≠ w', Hw.Reachable u₁ ⟨x, hx⟩)
    let R₀ : Finset {u : V | u ≠ v} := Finset.univ.filter (fun x => x ≠ w' ∧ x ∉ S₀)
    have hu₁S₀ : u₁.1 ∈ S₀ := Finset.mem_filter.mpr ⟨Finset.mem_univ _, u₁.2, Reachable.rfl⟩
    have hu₂R₀ : u₂.1 ∈ R₀ := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, u₂.2, fun h => ?_⟩
      obtain ⟨_, hr⟩ := (Finset.mem_filter.mp h).2
      exact hu₁₂ hr
    have hsepS₀ : IsSepPair H w' S₀ := by
      refine ⟨⟨u₁.1, hu₁S₀⟩, ?_, ⟨u₂.1, (Finset.mem_filter.mp hu₂R₀).2.2, u₂.2⟩, ?_⟩
      · intro hw; exact (Finset.mem_filter.mp hw).2.1 rfl
      · intro x hx y hadj
        by_cases hyw : y = w'
        · exact Or.inr hyw
        · left
          obtain ⟨_, hr⟩ := (Finset.mem_filter.mp hx).2
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hyw, hr.trans (Adj.reachable (G := Hw) hadj)⟩
    have hsepR₀ : IsSepPair H w' R₀ := by
      refine ⟨⟨u₂.1, hu₂R₀⟩, ?_, ⟨u₁.1, fun h => (Finset.mem_filter.mp h).2.2 hu₁S₀, u₁.2⟩, ?_⟩
      · intro hw; exact (Finset.mem_filter.mp hw).2.1 rfl
      · intro x hx y hadj
        by_cases hyw : y = w'
        · exact Or.inr hyw
        · left
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hyw, fun hyS => ?_⟩
          obtain ⟨_, hry⟩ := (Finset.mem_filter.mp hyS).2
          have hxS : x ∈ S₀ := Finset.mem_filter.mpr
            ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2.1,
              hry.trans (Adj.reachable (G := Hw) hadj.symm)⟩
          exact (Finset.mem_filter.mp hx).2.2 hxS
    have hdisj₀ : Disjoint S₀ R₀ := by
      rw [Finset.disjoint_left]
      intro x hxS hxR
      exact (Finset.mem_filter.mp hxR).2.2 hxS
    obtain ⟨c₁, S₁, hsep₁, hsub₁, hmin₁⟩ := exists_minimal_sepPair hHconn hsepS₀
    obtain ⟨c₂, S₂, hsep₂, hsub₂, hmin₂⟩ := exists_minimal_sepPair hHconn hsepR₀
    have hdisj : Disjoint S₁ S₂ := hdisj₀.mono hsub₁ hsub₂
    have hc₂_not_S₁ : c₂ ∉ S₁ := fun h => not_connected_induce_ne_of_isSepPair hsep₂ (hmin₁ c₂ h)
    have hc₁_not_S₂ : c₁ ∉ S₂ := fun h => not_connected_induce_ne_of_isSepPair hsep₁ (hmin₂ c₁ h)
    have hv_nbr : ∀ c S, IsSepPair H c S → ∃ a ∈ S, G.Adj v a.1 := by
      intro c S hsep
      by_contra hno
      push Not at hno
      obtain ⟨s, hs⟩ := hsep.1
      have hsc : s.1 ≠ c.1 := fun h => hsep.2.1 (Subtype.ext h ▸ hs)
      have hvc : v ≠ c.1 := c.2.symm
      obtain ⟨p⟩ := h2conn c.1 ⟨s.1, hsc⟩ ⟨v, hvc⟩
      let SV : Set V := Subtype.val '' (S : Set {u : V | u ≠ v})
      have hsSV : s.1 ∈ SV := ⟨s, hs, rfl⟩
      have hvSV : v ∉ SV := by
        rintro ⟨x, _, hxv⟩
        exact x.2 hxv
      have hnoSV : ∀ a ∈ SV, ∀ y, G.Adj a y → y ∈ SV ∨ y = c.1 := by
        rintro _ ⟨x, hxS, rfl⟩ y hadj
        by_cases hyv : y = v
        · exact (hno x hxS (hyv ▸ hadj.symm)).elim
        · rcases hsep.2.2.2 x hxS ⟨y, hyv⟩ hadj with hyS | hyc
          · exact Or.inl ⟨⟨y, hyv⟩, hyS, rfl⟩
          · exact Or.inr (congrArg Subtype.val hyc)
      have hc_mem : c.1 ∈ (walkFromInduce p).support :=
        mem_support_of_walk_leaving hnoSV (walkFromInduce p) hsSV hvSV
      rw [support_walkFromInduce, List.mem_map] at hc_mem
      obtain ⟨z, _, hzc⟩ := hc_mem
      exact z.2 hzc
    obtain ⟨a, haS₁, hva⟩ := hv_nbr c₁ S₁ hsep₁
    obtain ⟨b, hbS₂, hvb⟩ := hv_nbr c₂ S₂ hsep₂
    have hab_ne : a.1 ≠ b.1 := fun h =>
      Finset.disjoint_left.mp hdisj haS₁ (Subtype.ext h.symm ▸ hbS₂)
    have hab_nadj : ¬ G.Adj a.1 b.1 := by
      intro hadj
      rcases hsep₁.2.2.2 a haS₁ b hadj with hbS₁ | rfl
      · exact Finset.disjoint_left.mp hdisj hbS₁ hbS₂
      · exact hc₁_not_S₂ hbS₂
    refine ⟨v, a.1, b.1, hva, hvb, hab_ne, hab_nadj, ?_⟩
    let Sab : Set V := {u : V | u ≠ a.1 ∧ u ≠ b.1}
    let Gab := G.induce Sab
    have hc₁_in : c₁.1 ∈ Sab :=
      ⟨fun h => hsep₁.2.1 (Subtype.ext h ▸ haS₁),
       fun h => hc₁_not_S₂ (Subtype.ext h ▸ hbS₂)⟩
    have hc₂_in : c₂.1 ∈ Sab :=
      ⟨fun h => hc₂_not_S₁ (Subtype.ext h ▸ haS₁),
       fun h => hsep₂.2.1 (Subtype.ext h ▸ hbS₂)⟩
    let c₁' : Sab := ⟨c₁.1, hc₁_in⟩
    let c₂' : Sab := ⟨c₂.1, hc₂_in⟩
    have hM_reach : ∀ (z : {u : V | u ≠ v}) (hz₁ : z ∉ S₁) (hz₂ : z ∉ S₂),
        Gab.Reachable ⟨z.1, fun h => hz₁ (Subtype.ext h ▸ haS₁),
          fun h => hz₂ (Subtype.ext h ▸ hbS₂)⟩ c₁' := by
      intro z hz₁ hz₂
      obtain ⟨p, hp⟩ := hHconn.exists_isPath z c₁
      have hav₁ := path_avoids_sep (A := (S₁ : Set {u : V | u ≠ v}))
        (fun x hx y hadj => hsep₁.2.2.2 x hx y hadj) p hp hz₁ hsep₁.2.1
      have hav₂ := path_avoids_sep (A := (S₂ : Set {u : V | u ≠ v}))
        (fun x hx y hadj => hsep₂.2.2.2 x hx y hadj) p hp hz₂ hc₁_not_S₂
      exact ⟨walkInduce Sab p (fun x hx =>
        ⟨fun h => hav₁ x hx (Subtype.ext h ▸ haS₁),
         fun h => hav₂ x hx (Subtype.ext h ▸ hbS₂)⟩)⟩
    have hc₂_reach : Gab.Reachable c₂' c₁' := hM_reach c₂ hc₂_not_S₁ hsep₂.2.1
    have hS₁_reach : ∀ (x : {u : V | u ≠ v}) (hxS : x ∈ S₁) (hxa : x ≠ a),
        Gab.Reachable ⟨x.1, fun h => hxa (Subtype.ext h),
          fun h => Finset.disjoint_left.mp hdisj hxS (Subtype.ext h ▸ hbS₂)⟩ c₁' := by
      intro x hxS hxa
      have hc₁a : c₁ ≠ a := fun h => hsep₁.2.1 (h ▸ haS₁)
      obtain ⟨p, hp⟩ := (hmin₁ a haS₁).exists_isPath ⟨x, hxa⟩ ⟨c₁, hc₁a⟩
      let q : H.Walk x c₁ := walkFromInduce p
      have hq_path : q.IsPath := isPath_walkFromInduce hp
      have hq_sub := support_path_subset_insert_of_no_edge (A := (S₁ : Set {u : V | u ≠ v}))
        (fun s hs y hadj => hsep₁.2.2.2 s hs y hadj) q hq_path hxS
      have hq_good : ∀ y ∈ q.support, y.1 ∈ Sab := by
        intro y hy
        constructor
        · intro hya
          dsimp only [q] at hy
          rw [support_walkFromInduce, List.mem_map] at hy
          obtain ⟨z, _, rfl⟩ := hy
          exact z.2 (Subtype.ext hya)
        · intro hyb
          rcases hq_sub y hy with hyc | hyS₁
          · exact hc₁_not_S₂ (hyc ▸ Subtype.ext hyb ▸ hbS₂)
          · exact Finset.disjoint_left.mp hdisj hyS₁ (Subtype.ext hyb ▸ hbS₂)
      exact ⟨walkInduce Sab q hq_good⟩
    have hS₂_reach : ∀ (x : {u : V | u ≠ v}) (hxS : x ∈ S₂) (hxb : x ≠ b),
        Gab.Reachable ⟨x.1, fun h => Finset.disjoint_left.mp hdisj (Subtype.ext h ▸ haS₁) hxS,
          fun h => hxb (Subtype.ext h)⟩ c₂' := by
      intro x hxS hxb
      have hc₂b : c₂ ≠ b := fun h => hsep₂.2.1 (h ▸ hbS₂)
      obtain ⟨p, hp⟩ := (hmin₂ b hbS₂).exists_isPath ⟨x, hxb⟩ ⟨c₂, hc₂b⟩
      let q : H.Walk x c₂ := walkFromInduce p
      have hq_path : q.IsPath := isPath_walkFromInduce hp
      have hq_sub := support_path_subset_insert_of_no_edge (A := (S₂ : Set {u : V | u ≠ v}))
        (fun s hs y hadj => hsep₂.2.2.2 s hs y hadj) q hq_path hxS
      have hq_good : ∀ y ∈ q.support, y.1 ∈ Sab := by
        intro y hy
        constructor
        · intro hya
          rcases hq_sub y hy with hyc | hyS₂
          · exact hc₂_not_S₁ (hyc ▸ Subtype.ext hya ▸ haS₁)
          · exact Finset.disjoint_left.mp hdisj (Subtype.ext hya ▸ haS₁) hyS₂
        · intro hyb
          dsimp only [q] at hy
          rw [support_walkFromInduce, List.mem_map] at hy
          obtain ⟨z, _, rfl⟩ := hy
          exact z.2 (Subtype.ext hyb)
      exact ⟨walkInduce Sab q hq_good⟩
    have hH_all_reach : ∀ z : Sab, z.1 ≠ v → Gab.Reachable z c₁' := by
      intro z hzv
      let zH : {u : V | u ≠ v} := ⟨z.1, hzv⟩
      by_cases hz₁ : zH ∈ S₁
      · exact hS₁_reach zH hz₁ (fun h => z.2.1 (congrArg Subtype.val h))
      · by_cases hz₂ : zH ∈ S₂
        · exact (hS₂_reach zH hz₂ (fun h => z.2.2 (congrArg Subtype.val h))).trans hc₂_reach
        · exact hM_reach zH hz₁ hz₂
    rw [connected_iff_exists_forall_reachable]
    refine ⟨c₁', fun z => ?_⟩
    by_cases hzv : z.1 = v
    · have hcard : 3 ≤ (G.neighborFinset v).card := by
        rw [card_neighborFinset_eq_degree]; exact hdeg3 v
      have hsub : ¬ G.neighborFinset v ⊆ {a.1, b.1} := by
        intro h
        have h1 := Finset.card_le_card h
        have h2 : ({a.1, b.1} : Finset V).card ≤ 2 := Finset.card_le_two
        omega
      obtain ⟨y, hyN, hyab⟩ := Finset.not_subset.mp hsub
      have hvy : G.Adj v y := (mem_neighborFinset G v y).mp hyN
      have hy_in : y ∈ Sab := by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hyab
        exact hyab
      have hyv : y ≠ v := hvy.ne.symm
      have hzy : Gab.Adj z ⟨y, hy_in⟩ := show G.Adj z.1 y by rw [hzv]; exact hvy
      exact (hH_all_reach ⟨y, hy_in⟩ hyv).symm.trans hzy.symm.reachable
    · exact (hH_all_reach z hzv).symm

end CherryLemma

/- ### Section 5: Brooks ordering for 2-connected graphs and main theorems -/

section MainTheorems

variable {V : Type*} (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj]

/-- **Case 2b (2-connected Brooks ordering)**: Given `G` with `∀ u, G.degree u ≤ 4` and a cherry
`(v, a, b)` with `G.Adj v a`, `G.Adj v b`, `a ≠ b`, `¬ G.Adj a b`, and `G - {a, b}` connected,
`G` admits a forest bipartition. -/
theorem exists_forestColoring_of_good_cherry
    (hdeg : ∀ u : V, G.degree u ≤ 4)
    {v a b : V} (hva : G.Adj v a) (hvb : G.Adj v b) (hab_ne : a ≠ b) (hab_nadj : ¬ G.Adj a b)
    (hconn' : (G.induce {u : V | u ≠ a ∧ u ≠ b}).Connected) :
    ∃ c : V → Bool, IsForestColoring G c := by
  let _ := Classical.decEq V
  let G' := G.induce {u : V | u ≠ a ∧ u ≠ b}
  have hv_in : v ≠ a ∧ v ≠ b := ⟨hva.ne, hvb.ne⟩
  let v' : {u : V | u ≠ a ∧ u ≠ b} := ⟨v, hv_in⟩
  let d : V → ℕ := fun u =>
    if hu : u ≠ a ∧ u ≠ b then G'.dist v' ⟨u, hu⟩ else 0
  let S₀ : Finset V := {a, b}
  let midSet : Finset V := Finset.univ.filter (fun u => u ≠ a ∧ u ≠ b ∧ u ≠ v)
  let L : List V := sortDesc d midSet
  have hgood : GoodOrder G S₀ L := by
    refine goodOrder_of_forall_split G (fun x _ => hdeg x) (sortDesc_nodup d midSet) ?_ ?_
    · intro x hx
      have hxm := (mem_sortDesc d midSet).mp hx
      simp only [midSet, Finset.mem_filter, Finset.mem_univ, true_and] at hxm
      simp [S₀, hxm.1, hxm.2.1]
    · intro l₁ u l₂ heq
      have huL : u ∈ sortDesc d midSet := by
        change u ∈ L
        rw [heq]
        simp
      have hum : u ∈ midSet := (mem_sortDesc d midSet).mp huL
      simp only [midSet, Finset.mem_filter, Finset.mem_univ, true_and] at hum
      have hu_in : u ≠ a ∧ u ≠ b := ⟨hum.1, hum.2.1⟩
      have hu_ne_v' : (⟨u, hu_in⟩ : {x : V | x ≠ a ∧ x ≠ b}) ≠ v' :=
        fun h => hum.2.2 (congrArg Subtype.val h)
      obtain ⟨w', hadj', hlt'⟩ := exists_adj_dist_lt_of_connected hconn' hu_ne_v'
      refine Or.inr ⟨w'.1, hadj', ?_, fun hwl => ?_⟩
      · simp [S₀, w'.2.1, w'.2.2]
      · have hle : d u ≤ d w'.1 := dist_le_of_split_sortDesc heq hwl
        have hdu : d u = (G.induce {u : V | u ≠ a ∧ u ≠ b}).dist v' ⟨u, hu_in⟩ := dif_pos hu_in
        have hdw : d w'.1 = (G.induce {u : V | u ≠ a ∧ u ≠ b}).dist v' w' := dif_pos w'.2
        omega
  let c₀ : V → Bool := fun _ => false
  have hacyc₀_false : (G.induce {x : V | x ∈ S₀ ∧ c₀ x = false}).IsAcyclic := by
    refine IsAcyclic.of_card_le_two ?_
    have hsub : {x : V | x ∈ S₀ ∧ c₀ x = false} ⊆ ({a, b} : Set V) := by
      intro x hx; simpa [S₀] using hx.1
    calc
      ENat.card {x : V | x ∈ S₀ ∧ c₀ x = false}
        ≤ ENat.card ({a, b} : Set V) :=
            ENat.card_le_card_of_injective (Set.inclusion_injective hsub)
      _ ≤ 2 := by
            have : ({a, b} : Set V) = (({a, b} : Finset V) : Set V) := by simp
            rw [this, ENat.card_coe_set_eq]
            exact_mod_cast (Finset.card_le_two : ({a, b} : Finset V).card ≤ 2)
  have hacyc₀_true : (G.induce {x : V | x ∈ S₀ ∧ c₀ x = true}).IsAcyclic := by
    have : Subsingleton {x : V | x ∈ S₀ ∧ c₀ x = true} :=
      ⟨fun ⟨_, hx⟩ _ => (Bool.false_ne_true hx.2).elim⟩
    exact IsAcyclic.of_subsingleton
  have haS₀ : a ∈ S₀ := Finset.mem_insert_self a {b}
  have hbS₀ : b ∈ S₀ := Finset.mem_insert_of_mem (Finset.mem_singleton_self b)
  have hab_not_reach₀ :
      ¬ (G.induce {x : V | x ∈ S₀ ∧ c₀ x = false}).Reachable ⟨a, haS₀, rfl⟩ ⟨b, hbS₀, rfl⟩ := by
    rintro ⟨p⟩
    cases p with
    | nil => exact hab_ne rfl
    | @cons _ y _ hadj _ =>
        have hy : y.1 = a ∨ y.1 = b := by simpa [S₀] using y.2.1
        rcases hy with hya | hyb
        · exact hadj.ne (Subtype.ext hya.symm)
        · exact hab_nadj (hyb ▸ hadj)
  obtain ⟨c, hc_eq, hfalse_S, htrue_S, hnr_S⟩ :=
    greedy_extend_coloring G hgood hacyc₀_false hacyc₀_true
  let S : Finset V := S₀ ∪ L.toFinset
  have hS_eq : S = Finset.univ.erase v := by
    ext x
    simp only [S, S₀, L, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
      List.mem_toFinset, mem_sortDesc, midSet, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_erase]
    by_cases hxa : x = a
    · subst hxa; simp [hv_in.1.symm]
    · by_cases hxb : x = b
      · subst hxb; simp [hv_in.2.symm]
      · simp [hxa, hxb]
  have hv_not_S : v ∉ S := by rw [hS_eq]; exact Finset.notMem_erase v _
  have hca : c a = false := hc_eq a haS₀
  have hcb : c b = false := hc_eq b hbS₀
  have haS : a ∈ S := Finset.mem_union_left _ haS₀
  have hbS : b ∈ S := Finset.mem_union_left _ hbS₀
  have hab_not_reach :
      ¬ (G.induce {x : V | x ∈ S ∧ c x = false}).Reachable ⟨a, haS, hca⟩ ⟨b, hbS, hcb⟩ :=
    hnr_S a b haS₀ hbS₀ rfl rfl hab_not_reach₀ haS hbS hca hcb
  let N₀ := S.filter (fun x => G.Adj v x ∧ c x = false)
  let N₁ := S.filter (fun x => G.Adj v x ∧ c x = true)
  have hN_card : N₀.card + N₁.card ≤ 4 := by
    rw [← Finset.card_union_of_disjoint]
    · have hsub : N₀ ∪ N₁ ⊆ G.neighborFinset v := by
        intro x hx
        simp only [N₀, N₁, Finset.mem_union, Finset.mem_filter, mem_neighborFinset] at hx ⊢
        rcases hx with ⟨_, h, _⟩ | ⟨_, h, _⟩ <;> exact h
      exact (Finset.card_le_card hsub).trans (by simpa [card_neighborFinset_eq_degree] using hdeg v)
    · rw [Finset.disjoint_left]
      intro x hx0 hx1
      simp only [N₀, N₁, Finset.mem_filter] at hx0 hx1
      exact Bool.false_ne_true (hx0.2.2.symm.trans hx1.2.2)
  have haN₀ : a ∈ N₀ := Finset.mem_filter.mpr ⟨haS, hva, hca⟩
  have hbN₀ : b ∈ N₀ := Finset.mem_filter.mpr ⟨hbS, hvb, hcb⟩
  have hN₀_ge : 2 ≤ N₀.card := by
    have hsub : ({a, b} : Finset V) ⊆ N₀ := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    have hpair : ({a, b} : Finset V).card = 2 := Finset.card_pair hab_ne
    exact hpair ▸ Finset.card_le_card hsub
  by_cases h1 : N₁.card ≤ 1
  · let c' := Function.update c v true
    have hfalse_eq : {x : V | c' x = false} = {x : V | x ∈ S ∧ c x = false} := by
      ext x
      by_cases hxv : x = v
      · subst hxv; simp [c', hv_not_S]
      · have hxS : x ∈ S := by rw [hS_eq]; exact Finset.mem_erase.mpr ⟨hxv, Finset.mem_univ _⟩
        simp [c', hxv, hxS]
    have htrue_eq : {x : V | c' x = true} = insert v {x : V | x ∈ S ∧ c x = true} := by
      ext x
      by_cases hxv : x = v
      · subst hxv; simp [c']
      · have hxS : x ∈ S := by rw [hS_eq]; exact Finset.mem_erase.mpr ⟨hxv, Finset.mem_univ _⟩
        simp [c', hxv, hxS]
    refine ⟨c', ?_, ?_⟩
    · rw [hfalse_eq]; exact hfalse_S
    · rw [htrue_eq]
      refine isAcyclic_induce_insert_of_unique_adj htrue_S ?_
      intro x hx y hy hvx hvy
      exact Finset.card_le_one.mp h1 x (Finset.mem_filter.mpr ⟨hx.1, hvx, hx.2⟩)
        y (Finset.mem_filter.mpr ⟨hy.1, hvy, hy.2⟩)
  · have hN₀_eq : N₀ = {a, b} := by
      have hsub : ({a, b} : Finset V) ⊆ N₀ := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl <;> assumption
      have hpair : ({a, b} : Finset V).card = 2 := Finset.card_pair hab_ne
      exact (Finset.eq_of_subset_of_card_le hsub (by omega)).symm
    let c' := Function.update c v false
    have hfalse_eq : {x : V | c' x = false} = insert v {x : V | x ∈ S ∧ c x = false} := by
      ext x
      by_cases hxv : x = v
      · subst hxv; simp [c']
      · have hxS : x ∈ S := by rw [hS_eq]; exact Finset.mem_erase.mpr ⟨hxv, Finset.mem_univ _⟩
        simp [c', hxv, hxS]
    have htrue_eq : {x : V | c' x = true} = {x : V | x ∈ S ∧ c x = true} := by
      ext x
      by_cases hxv : x = v
      · subst hxv; simp [c', hv_not_S]
      · have hxS : x ∈ S := by rw [hS_eq]; exact Finset.mem_erase.mpr ⟨hxv, Finset.mem_univ _⟩
        simp [c', hxv, hxS]
    refine ⟨c', ?_, ?_⟩
    · rw [hfalse_eq]
      refine isAcyclic_induce_insert_of_not_reachable hfalse_S ?_
      intro x hx y hy hvx hvy hxy
      have hxmem : x ∈ ({a, b} : Finset V) := hN₀_eq ▸ Finset.mem_filter.mpr ⟨hx.1, hvx, hx.2⟩
      have hymem : y ∈ ({a, b} : Finset V) := hN₀_eq ▸ Finset.mem_filter.mpr ⟨hy.1, hvy, hy.2⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxmem hymem
      rcases hxmem with rfl | rfl <;> rcases hymem with rfl | rfl
      · exact (hxy rfl).elim
      · exact hab_not_reach
      · exact fun h => hab_not_reach h.symm
      · exact (hxy rfl).elim
    · rw [htrue_eq]; exact htrue_S

/-- Every connected finite simple graph with `∀ v, G.degree v ≤ 4` that is not `K₅` (expressed as
`¬ (Fintype.card V = 5 ∧ G = ⊤)`) admits a forest bipartition. -/
theorem exists_forestColoring_of_connected_degree_le_four
    (hconn : G.Connected) (hdeg : ∀ u : V, G.degree u ≤ 4)
    (hnotK5 : ¬ (Fintype.card V = 5 ∧ G = ⊤)) :
    ∃ c : V → Bool, IsForestColoring G c := by
  by_cases h3 : ∃ v : V, G.degree v ≤ 3
  · exact exists_forestColoring_of_exists_degree_le_three G hconn hdeg h3
  push Not at h3
  have hreg : ∀ u : V, G.degree u = 4 := fun u => le_antisymm (hdeg u) (h3 u)
  have hnotTop : G ≠ ⊤ := by
    intro htop
    apply hnotK5
    refine ⟨?_, htop⟩
    let _ := Classical.decEq V
    obtain ⟨v⟩ := hconn.nonempty
    have hnbr : G.neighborFinset v = Finset.univ.erase v := by
      ext u
      simp [mem_neighborFinset, htop, ne_comm]
    have hcard : (G.neighborFinset v).card + 1 = Fintype.card V := by
      rw [hnbr, Finset.card_erase_add_one (Finset.mem_univ v), Finset.card_univ]
    rw [card_neighborFinset_eq_degree, hreg v] at hcard
    omega
  by_cases h2conn : ∀ x : V, (G.induce {u : V | u ≠ x}).Connected
  · obtain ⟨v, a, b, hva, hvb, hab_ne, hab_nadj, hconn'⟩ :=
      exists_good_cherry_of_two_connected G hconn h2conn (fun u => by have := hreg u; omega) hnotTop
    exact exists_forestColoring_of_good_cherry G hdeg hva hvb hab_ne hab_nadj hconn'
  · push Not at h2conn
    obtain ⟨x, hcut⟩ := h2conn
    exact exists_forestColoring_of_cut_vertex G hconn hdeg hcut

/-- **General Theorem (Kostochka 1996 Lemma 1 / Catlin / Lovász)**: Every finite simple graph `G`
with maximum degree at most `4` and no `K₅` clique (`G.CliqueFree 5`) admits a forest
bipartition. -/
theorem exists_forestColoring_of_degree_le_four_of_cliqueFree_five
    (hdeg : ∀ u : V, G.degree u ≤ 4) (hK5 : G.CliqueFree 5) :
    ∃ c : V → Bool, IsForestColoring G c := by
  let _ := Classical.decEq V
  have hcomp : ∀ C : G.ConnectedComponent, ∃ cC : C → Bool, IsForestColoring C.toSimpleGraph cC := by
    intro C
    let _ : DecidablePred (· ∈ C.supp) := Classical.decPred _
    let _ : DecidableRel C.toSimpleGraph.Adj := fun u w => inferInstanceAs (Decidable (G.Adj u.1 w.1))
    have hconnC : C.toSimpleGraph.Connected := C.connected_toSimpleGraph
    have hdegC : ∀ u : C, C.toSimpleGraph.degree u ≤ 4 := fun u =>
      (degree_induce_le (G := G) (s := C.supp) u).trans (hdeg u.1)
    have hnotK5C : ¬ (Fintype.card C = 5 ∧ C.toSimpleGraph = ⊤) := by
      rintro ⟨hcard, htop⟩
      let s : Finset V := Finset.univ.image (fun u : C => u.1)
      have hscard : s.card = 5 := by
        rw [Finset.card_image_of_injective _ Subtype.val_injective, Finset.card_univ, hcard]
      have hsclique : G.IsClique (s : Set V) := by
        intro x hx y hy hxy
        simp only [s, Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hx hy
        obtain ⟨u, rfl⟩ := hx
        obtain ⟨w, rfl⟩ := hy
        have huw : u ≠ w := fun h => hxy (congrArg Subtype.val h)
        have hadj : C.toSimpleGraph.Adj u w := by rw [htop]; exact huw
        exact hadj
      exact hK5 s ⟨hsclique, hscard⟩
    exact exists_forestColoring_of_connected_degree_le_four C.toSimpleGraph hconnC hdegC hnotK5C
  choose cComp hcComp using hcomp
  let c : V → Bool := fun v => cComp (G.connectedComponentMk v) ⟨v, rfl⟩
  have hagree_aux : ∀ (C₁ C₂ : G.ConnectedComponent) (_ : C₁ = C₂)
      (u : V) (hu₁ : u ∈ C₁.supp) (hu₂ : u ∈ C₂.supp),
      cComp C₁ ⟨u, hu₁⟩ = cComp C₂ ⟨u, hu₂⟩ := by
    rintro C₁ _ rfl u hu₁ hu₂
    rfl
  have hacyc_col : ∀ col : Bool, (G.induce {v : V | c v = col}).IsAcyclic := by
    intro col w p hp
    let C := G.connectedComponentMk w.1
    have hsubC : ∀ z ∈ p.support, z.1 ∈ C.supp := by
      intro z hz
      have hr : (G.induce {v : V | c v = col}).Reachable w z := ⟨p.takeUntil z hz⟩
      have hrG : G.Reachable w.1 z.1 := hr.map (Embedding.induce {v : V | c v = col}).toHom
      exact ConnectedComponent.sound hrG.symm
    have hagree : ∀ u (hu : u ∈ C.supp), c u = cComp C ⟨u, hu⟩ := fun u hu =>
      hagree_aux (G.connectedComponentMk u) C hu u rfl hu
    have hacycC : (G.induce {v : V | v ∈ C.supp ∧ c v = col}).IsAcyclic := by
      cases col
      · exact isAcyclic_induce_of_subinduce hagree (hcComp C).1
      · exact isAcyclic_induce_of_subinduce hagree (hcComp C).2
    exact hacycC (walkInduce {v : V | v ∈ C.supp ∧ c v = col} p (fun z hz => ⟨hsubC z hz, z.2⟩))
      (isCycle_walkInduce {v : V | v ∈ C.supp ∧ c v = col} hp _)
  exact ⟨c, hacyc_col false, hacyc_col true⟩

/-- Set-partition form of the general `Δ ≤ 4`, `CliqueFree 5` forest bipartition theorem. -/
theorem exists_forest_bipartition_of_degree_le_four
    (hdeg : ∀ u : V, G.degree u ≤ 4) (hK5 : G.CliqueFree 5) :
    ∃ A B : Set V, A ∪ B = Set.univ ∧ Disjoint A B ∧
      (G.induce A).IsAcyclic ∧ (G.induce B).IsAcyclic := by
  obtain ⟨c, hfalse, htrue⟩ :=
    exists_forestColoring_of_degree_le_four_of_cliqueFree_five G hdeg hK5
  refine ⟨{v | c v = false}, {v | c v = true}, ?_, ?_, hfalse, htrue⟩
  · ext v; cases c v <;> simp
  · rw [Set.disjoint_left]; intro v h0 h1; exact Bool.false_ne_true (h0.symm.trans h1)

/-- Finset-partition form of the general `Δ ≤ 4`, `CliqueFree 5` forest bipartition theorem. -/
theorem exists_finset_forest_bipartition_of_degree_le_four [DecidableEq V]
    (hdeg : ∀ u : V, G.degree u ≤ 4) (hK5 : G.CliqueFree 5) :
    ∃ A B : Finset V, A ∪ B = Finset.univ ∧ Disjoint A B ∧
      (G.induce (A : Set V)).IsAcyclic ∧ (G.induce (B : Set V)).IsAcyclic := by
  obtain ⟨c, hfalse, htrue⟩ :=
    exists_forestColoring_of_degree_le_four_of_cliqueFree_five G hdeg hK5
  refine ⟨Finset.univ.filter (fun v => c v = false), Finset.univ.filter (fun v => c v = true),
    ?_, ?_, ?_, ?_⟩
  · ext v; cases c v <;> simp
  · rw [Finset.disjoint_left]; intro v h0 h1
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h0 h1
    exact Bool.false_ne_true (h0.symm.trans h1)
  · have hA : ((Finset.univ.filter (fun v => c v = false) : Finset V) : Set V) =
        {v | c v = false} := by ext v; simp
    rw [hA]
    exact hfalse
  · have hB : ((Finset.univ.filter (fun v => c v = true) : Finset V) : Set V) =
        {v | c v = true} := by ext v; simp
    rw [hB]
    exact htrue

omit [DecidableRel G.Adj] in
/-- A finite simple graph `G` is isomorphic to `K₅` if and only if
`Fintype.card V = 5 ∧ G = ⊤`. -/
lemma nonempty_iso_K5_iff_card_five_and_top :
    Nonempty (G ≃g (⊤ : SimpleGraph (Fin 5))) ↔ Fintype.card V = 5 ∧ G = ⊤ := by
  constructor
  · rintro ⟨e⟩
    refine ⟨?_, ?_⟩
    · simpa using Fintype.card_congr e.toEquiv
    · rw [G.eq_top_iff_forall_ne_adj]
      intro u v huv
      rw [← e.map_rel_iff]
      exact e.injective.ne huv
  · rintro ⟨hcard, htop⟩
    let e := Fintype.equivFinOfCardEq hcard
    refine ⟨{ toEquiv := e, map_rel_iff' := ?_ }⟩
    intro u v
    rw [htop, top_adj, top_adj]
    exact e.injective.ne_iff

/-- **Kostochka (1996) Lemma 1 — Initial Forest Bipartition**:
Every connected finite simple `4`-regular graph not isomorphic to `K₅` admits a partition of its
vertex set into two sets each inducing a forest (acyclic graph). -/
theorem exists_forest_bipartition_of_connected_four_regular
    (hconn : G.Connected)
    (hreg : G.IsRegularOfDegree 4)
    (hnotK5 : ¬ Nonempty (G ≃g (⊤ : SimpleGraph (Fin 5)))) :
    ∃ A B : Set V, A ∪ B = Set.univ ∧ Disjoint A B ∧
      (G.induce A).IsAcyclic ∧ (G.induce B).IsAcyclic := by
  have hnot : ¬ (Fintype.card V = 5 ∧ G = ⊤) :=
    (nonempty_iso_K5_iff_card_five_and_top G).not.mp hnotK5
  obtain ⟨c, hfalse, htrue⟩ :=
    exists_forestColoring_of_connected_degree_le_four G hconn (fun u => (hreg u).le) hnot
  refine ⟨{v | c v = false}, {v | c v = true}, ?_, ?_, hfalse, htrue⟩
  · ext v; cases c v <;> simp
  · rw [Set.disjoint_left]; intro v h0 h1; exact Bool.false_ne_true (h0.symm.trans h1)

/-- Corollary with hypothesis `G ≠ ⊤`. -/
theorem exists_forest_bipartition_of_connected_four_regular_ne_top
    (hconn : G.Connected)
    (hreg : G.IsRegularOfDegree 4)
    (hne : G ≠ ⊤) :
    ∃ A B : Set V, A ∪ B = Set.univ ∧ Disjoint A B ∧
      (G.induce A).IsAcyclic ∧ (G.induce B).IsAcyclic := by
  refine exists_forest_bipartition_of_connected_four_regular G hconn hreg ?_
  rw [nonempty_iso_K5_iff_card_five_and_top G]
  exact fun h => hne h.2

/-- Corollary with hypothesis `Fintype.card V ≠ 5`. -/
theorem exists_forest_bipartition_of_connected_four_regular_card_ne_five
    (hconn : G.Connected)
    (hreg : G.IsRegularOfDegree 4)
    (hcard : Fintype.card V ≠ 5) :
    ∃ A B : Set V, A ∪ B = Set.univ ∧ Disjoint A B ∧
      (G.induce A).IsAcyclic ∧ (G.induce B).IsAcyclic := by
  refine exists_forest_bipartition_of_connected_four_regular G hconn hreg ?_
  rw [nonempty_iso_K5_iff_card_five_and_top G]
  exact fun h => hcard h.1

/-- Corollary using `G.maxDegree ≤ 4`. -/
theorem exists_forest_bipartition_of_maxDegree_le_four
    (hmax : G.maxDegree ≤ 4) (hK5 : G.CliqueFree 5) :
    ∃ A B : Set V, A ∪ B = Set.univ ∧ Disjoint A B ∧
      (G.induce A).IsAcyclic ∧ (G.induce B).IsAcyclic :=
  exists_forest_bipartition_of_degree_le_four G
    (fun u => (G.degree_le_maxDegree u).trans hmax) hK5

/-- Finset-partition form for connected finite simple `4`-regular graphs other than `K₅`. -/
theorem exists_finset_forest_bipartition_of_connected_four_regular [DecidableEq V]
    (hconn : G.Connected)
    (hreg : G.IsRegularOfDegree 4)
    (hnotK5 : ¬ Nonempty (G ≃g (⊤ : SimpleGraph (Fin 5)))) :
    ∃ A B : Finset V, A ∪ B = Finset.univ ∧ Disjoint A B ∧
      (G.induce (A : Set V)).IsAcyclic ∧ (G.induce (B : Set V)).IsAcyclic := by
  have hnot : ¬ (Fintype.card V = 5 ∧ G = ⊤) :=
    (nonempty_iso_K5_iff_card_five_and_top G).not.mp hnotK5
  obtain ⟨c, hfalse, htrue⟩ :=
    exists_forestColoring_of_connected_degree_le_four G hconn (fun u => (hreg u).le) hnot
  refine ⟨Finset.univ.filter (fun v => c v = false), Finset.univ.filter (fun v => c v = true),
    ?_, ?_, ?_, ?_⟩
  · ext v; cases c v <;> simp
  · rw [Finset.disjoint_left]; intro v h0 h1
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h0 h1
    exact Bool.false_ne_true (h0.symm.trans h1)
  · have hA : ((Finset.univ.filter (fun v => c v = false) : Finset V) : Set V) =
        {v | c v = false} := by ext v; simp
    rw [hA]
    exact hfalse
  · have hB : ((Finset.univ.filter (fun v => c v = true) : Finset V) : Set V) =
        {v | c v = true} := by ext v; simp
    rw [hB]
    exact htrue

/-- Sharpness: `K₅` does NOT admit a partition into two induced forests. -/
theorem not_exists_forest_bipartition_K5 :
    ¬ ∃ A B : Set (Fin 5), A ∪ B = Set.univ ∧ Disjoint A B ∧
      ((⊤ : SimpleGraph (Fin 5)).induce A).IsAcyclic ∧
      ((⊤ : SimpleGraph (Fin 5)).induce B).IsAcyclic := by
  classical
  rintro ⟨A, B, hunion, hdisj, hA, hB⟩
  have htri : ∀ {S : Set (Fin 5)}, 3 ≤ S.toFinset.card →
      ¬ ((⊤ : SimpleGraph (Fin 5)).induce S).IsAcyclic := by
    intro S hcard hacyc
    obtain ⟨x, y, z, hx, hy, hz, hxy, hxz, hyz⟩ :=
      Finset.two_lt_card_iff.mp (by omega : 2 < S.toFinset.card)
    have hxS : x ∈ S := Set.mem_toFinset.mp hx
    have hyS : y ∈ S := Set.mem_toFinset.mp hy
    have hzS : z ∈ S := Set.mem_toFinset.mp hz
    let K := (⊤ : SimpleGraph (Fin 5)).induce S
    let x' : S := ⟨x, hxS⟩
    let y' : S := ⟨y, hyS⟩
    let z' : S := ⟨z, hzS⟩
    have h1 : K.Adj x' y' := hxy
    have h2 : K.Adj y' z' := hyz
    have h3 : K.Adj z' x' := hxz.symm
    let cyc : K.Walk x' x' := .cons h1 (.cons h2 (.cons h3 .nil))
    refine hacyc cyc ?_
    rw [Walk.isCycle_iff_isPath_tail_and_le_length]
    refine ⟨?_, by simp [cyc]⟩
    rw [Walk.isPath_def]
    simp [cyc, x', y', z', hyz, Ne.symm hxy, Ne.symm hxz]
  have hsum : A.toFinset.card + B.toFinset.card = 5 := by
    rw [← Finset.card_union_of_disjoint]
    · have hun : A.toFinset ∪ B.toFinset = Finset.univ := by
        ext x
        have hx : x ∈ A ∪ B := by rw [hunion]; trivial
        simpa using hx
      rw [hun, Finset.card_univ, Fintype.card_fin]
    · rw [Finset.disjoint_left]
      intro x hxA hxB
      exact Set.disjoint_left.mp hdisj (Set.mem_toFinset.mp hxA) (Set.mem_toFinset.mp hxB)
  by_cases h3 : 3 ≤ A.toFinset.card
  · exact htri h3 hA
  · exact htri (by omega) hB

end MainTheorems

end ForestPartition

end


section -- FiveRegularCut

/- Section 4, Lemma 4 of Kostochka's degree-five total coloring theorem.
We count crossing ordered pairs instead of edges, so the score of a cut is
twice its size. The maximizers are the same.
-/

namespace Kostochka.FiveRegular

open SimpleGraph Finset

variable {V : Type*} [Fintype V]

/-- The spanning subgraph formed by the edges which cross the cut `p`. -/
def crossGraph (G : SimpleGraph V) (p : V → Bool) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ p x ≠ p y
  symm.symm _ _ h := ⟨h.1.symm, h.2.symm⟩
  loopless.irrefl _ h := h.2 rfl

private noncomputable def cutPair (G : SimpleGraph V) (p : V → Bool) (x y : V) : ℤ := by
  classical
  exact if (crossGraph G p).Adj x y then 1 else 0

noncomputable def cutScore (G : SimpleGraph V) (p : V → Bool) : ℤ :=
  ∑ x, ∑ y, cutPair G p x y

omit [Fintype V] in
/-- A maximum cut leaves every original component connected after the
monochromatic edges are removed. This is the component-flip argument of
Kostochka's Lemma 4(2), applied to the complement of the perfect matching. -/
theorem crossing_reachable_of_maximal (G : SimpleGraph V) (p : V → Bool)
    (maximal : ∀ q, crossGraph G p ≤ crossGraph G q → crossGraph G q ≤ crossGraph G p) {u v : V} (huv : G.Adj u v) :
    (crossGraph G p).Reachable u v := by
  classical
  by_contra hdis
  let q := fun x => if (crossGraph G p).Reachable u x then !(p x) else p x
  have keep {x y : V} (h : (crossGraph G p).Adj x y) : (crossGraph G q).Adj x y := by
    have hab : (crossGraph G p).Reachable u x ↔ (crossGraph G p).Reachable u y :=
      ⟨fun hx => hx.trans h.reachable, fun hy => hy.trans h.symm.reachable⟩
    refine ⟨h.1, ?_⟩
    have hxy := h.2
    by_cases hx : (crossGraph G p).Reachable u x
    · simpa [q, hx, hab.mp hx] using hxy
    · have hy := mt hab.mpr hx
      simpa [q, hx, hy] using hxy
  have hsame : p u = p v := by
    by_contra hne
    exact hdis (show (crossGraph G p).Adj u v from ⟨huv, hne⟩).reachable
  have gained : (crossGraph G q).Adj u v := by
    refine ⟨huv, ?_⟩
    simp [q, hdis, hsame]
  exact hdis ((maximal q (fun _ _ h => keep h)) gained).reachable

theorem crossing_reachable_of_maximum (G : SimpleGraph V) (p : V → Bool)
    (maximum : ∀ q, cutScore G q ≤ cutScore G p) {u v : V} (huv : G.Adj u v) :
    (crossGraph G p).Reachable u v := by
  classical
  apply crossing_reachable_of_maximal G p _ huv
  intro q keep u v gained
  by_contra hno
  have mono (x y : V) : cutPair G p x y ≤ cutPair G q x y := by
    simp only [cutPair]
    split_ifs <;> first | decide | solve_by_elim [keep]
  have strict : cutPair G p u v < cutPair G q u v := by
    simp [cutPair, hno, gained]
  have whole : cutScore G p < cutScore G q := by
    unfold cutScore
    apply Finset.sum_lt_sum (fun x _ => Finset.sum_le_sum (fun y _ => mono x y))
    exact ⟨u, mem_univ _, Finset.sum_lt_sum (fun y _ => mono u y) ⟨v, mem_univ _, strict⟩⟩
  exact (maximum q).not_gt whole

/-- A same-side neighbor contributes one, an opposite-side neighbor contributes
minus one. Flipping a vertex gains the sum of these contributions. -/
private noncomputable def gainPair (G : SimpleGraph V) (p : V → Bool) (u v : V) : ℤ := by
  classical
  exact if G.Adj u v then (if p u = p v then 1 else -1) else 0

noncomputable def gain (G : SimpleGraph V) (p : V → Bool) (u : V) : ℤ :=
  ∑ v, gainPair G p u v

private noncomputable def flip (p : V → Bool) (u : V) : V → Bool := by
  classical
  exact fun v => if v = u then !(p v) else p v

omit [Fintype V] in
private theorem delta_pair [DecidableEq V] (G : SimpleGraph V) (p : V → Bool) (u x y : V) :
    cutPair G (flip p u) x y - cutPair G p x y =
      (if x = u then gainPair G p u y else 0) + (if y = u then gainPair G p u x else 0) := by
  classical
  by_cases hx : x = u <;> by_cases hy : y = u
  · subst x; subst y; simp [cutPair, crossGraph, gainPair]
  · subst x
    cases hp : p u <;> cases hp' : p y <;> by_cases ha : G.Adj u y <;>
      simp [cutPair, crossGraph, gainPair, flip, hy, hp, hp', ha]
  · subst y
    cases hp : p u <;> cases hp' : p x <;> by_cases ha : G.Adj u x <;>
      simp [cutPair, crossGraph, gainPair, flip, hx, hp, hp', ha, G.adj_comm x u]
  · by_cases hadj : G.Adj x y <;> by_cases hxy : p x = p y <;>
      simp [cutPair, crossGraph, flip, hx, hy, hadj, hxy]

private theorem cutScore_flip (G : SimpleGraph V) (p : V → Bool) (u : V) :
    cutScore G (flip p u) - cutScore G p = 2 * gain G p u := by
  classical
  unfold gain cutScore
  simp only [← Finset.sum_sub_distrib, delta_pair, Finset.sum_add_distrib]
  simp [Finset.sum_ite_irrel, two_mul]

theorem gain_nonpos_of_maximum (G : SimpleGraph V) (p : V → Bool)
    (maximum : ∀ q, cutScore G q ≤ cutScore G p) (u : V) : gain G p u ≤ 0 := by
  have := maximum (flip p u)
  have := cutScore_flip G p u
  omega

private theorem gain_other_flip (G : SimpleGraph V) (p : V → Bool) {u v : V}
    (hadj : G.Adj u v) (hop : p u ≠ p v) :
    gain G (flip p u) v = gain G p v + 2 := by
  classical
  have hvu := hadj.ne.symm
  have aux (x : V) : gainPair G (flip p u) v x = gainPair G p v x + (if x = u then 2 else 0) := by
    by_cases hxu : x = u
    · subst x
      cases hu : p u <;> cases hv : p v <;> simp_all [gainPair, flip, hadj.symm]
    · simp [gainPair, flip, hvu, hxu]
  simp [gain, aux, Finset.sum_add_distrib]

/-- Endpoints of a crossing edge in a maximum cut cannot both have exactly as
many neighbors inside as outside. This is the two-vertex flip in Lemma 4(3). -/
theorem separated_balanced_nonadjacent (G : SimpleGraph V) (p : V → Bool)
    (maximum : ∀ q, cutScore G q ≤ cutScore G p) {u v : V}
    (hop : p u ≠ p v) (hu : gain G p u = 0) (hv : gain G p v = 0) : ¬ G.Adj u v := by
  intro hadj
  have step := cutScore_flip G p u
  have equ : cutScore G (flip p u) = cutScore G p := by omega
  have second := gain_nonpos_of_maximum G (flip p u) (fun q => equ ▸ maximum q) v
  have inc := gain_other_flip G p hadj hop
  omega

/-- Number of neighbors of a vertex which are on the same side of the cut. -/
noncomputable def insideDegree (G : SimpleGraph V) (p : V → Bool) (u : V) : ℕ := by
  classical
  exact (univ.filter (fun v => G.Adj u v ∧ p u = p v)).card

private theorem gain_eq (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → Bool) (u : V) :
    gain G p u = 2 * (insideDegree G p u : ℤ) - G.degree u := by
  classical
  have terms (v : V) : gainPair G p u v = 2 * (if G.Adj u v ∧ p u = p v then (1 : ℤ) else 0) -
      (if G.Adj u v then 1 else 0) := by
    by_cases ha : G.Adj u v <;> by_cases hp : p u = p v <;> simp [gainPair, ha, hp]
  simp only [gain, terms, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_boole]
  simp only [insideDegree, ← G.card_neighborFinset_eq_degree u, neighborFinset_eq_filter]
  congr 4
  ext v
  simp

private theorem gain_remove_matching (G : SimpleGraph V) (M : G.Subgraph)
    (hM : M.IsPerfectMatching) (p : V → Bool) (u : V) :
    gain G p u ≤ gain (G \ M.spanningCoe) p u + 1 := by
  classical
  obtain ⟨w, hw, huni⟩ := hM.1 (hM.2 u)
  have aux (v : V) : gainPair G p u v = gainPair (G \ M.spanningCoe) p u v +
      (if v = w then gainPair G p u w else 0) := by
    by_cases hv : v = w
    · subst v; simp [gainPair, hw, sdiff_adj, Subgraph.spanningCoe_adj]
    · have hnot : ¬ M.Adj u v := fun hh => hv (huni v hh)
      simp [gainPair, sdiff_adj, Subgraph.spanningCoe_adj, hnot, hv]
  have hsum := Finset.sum_congr (s₁ := univ) rfl (fun v _ => aux v)
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', mem_univ, if_true] at hsum
  change gain G p u = gain (G \ M.spanningCoe) p u + gainPair G p u w at hsum
  have hle : gainPair G p u w ≤ 1 := by
    unfold gainPair
    split_ifs <;> decide
  omega

/-- A maximum cut for the nonmatching edges can be refined by maximizing the
whole cut on the tied cuts. Both maxima are taken over a finite set. -/
private theorem exists_lex_cut (H G : SimpleGraph V) :
    ∃ p : V → Bool, (∀ q, cutScore H q ≤ cutScore H p) ∧
      ∀ q, cutScore H q = cutScore H p → cutScore G q ≤ cutScore G p := by
  classical
  obtain ⟨p, _, hp⟩ := univ.exists_max_image (cutScore H) univ_nonempty
  let tied := univ.filter (fun q => cutScore H q = cutScore H p)
  have ht : tied.Nonempty := ⟨p, by simp [tied]⟩
  obtain ⟨r, hr, hrmax⟩ := tied.exists_max_image (cutScore G) ht
  have he : cutScore H r = cutScore H p := (mem_filter.mp hr).2
  exact ⟨r, fun q => he ▸ hp q (mem_univ _), fun q hq => hrmax q (by simp [tied, hq, he])⟩

/-- Section 4, Lemma 4 for simple graphs. Removing the given perfect matching
gives the residual graph. All internal degrees in the full graph are at most
two, the crossing residual edges preserve reachability, and the residual has
no crossing edge between two vertices of internal residual degree two. -/
theorem exists_matching_cut (G : SimpleGraph V) [DecidableRel G.Adj]
    (regular : G.IsRegularOfDegree 5) (M : G.Subgraph) (hm : M.IsPerfectMatching) :
    let H := G \ M.spanningCoe
    ∃ p : V → Bool, (∀ u, insideDegree G p u ≤ 2) ∧
      (∀ u v, H.Adj u v → (crossGraph H p).Reachable u v) ∧
      (∀ u v, p u ≠ p v → insideDegree H p u = 2 → insideDegree H p v = 2 → ¬ H.Adj u v) := by
  classical
  let H := G \ M.spanningCoe
  obtain ⟨p, hmax, htie⟩ := exists_lex_cut H G
  refine ⟨p, ?_, fun u v huv => crossing_reachable_of_maximum H p hmax huv, ?_⟩
  · intro u
    by_contra! hlarge
    have gpos : 0 < gain G p u := by rw [gain_eq, regular u]; omega
    have hcomp := gain_remove_matching G M hm p u
    change gain G p u ≤ gain H p u + 1 at hcomp
    have hneg := gain_nonpos_of_maximum H p hmax u
    have hflip := cutScore_flip H p u
    have heq : cutScore H (flip p u) = cutScore H p := by omega
    have hle := htie (flip p u) heq
    have := cutScore_flip G p u
    omega
  · intro u v hop hdu hdv
    have hreg (x : V) : H.degree x = 4 := by
      obtain ⟨y, hy, huniq⟩ := hm.1 (hm.2 x)
      have diff : H.neighborFinset x = (G.neighborFinset x).erase y := by
        ext z
        simpa only [H, mem_neighborFinset, sdiff_adj, Subgraph.spanningCoe_adj, mem_erase] using
          (show G.Adj x z ∧ ¬ M.Adj x z ↔ z ≠ y ∧ G.Adj x z from by
            have hmem : M.Adj x z ↔ z = y := ⟨fun h => huniq z h, fun e => e ▸ hy⟩
            tauto)
      rw [← H.card_neighborFinset_eq_degree, diff, Finset.card_erase_of_mem, G.card_neighborFinset_eq_degree,
        regular x]
      exact (G.mem_neighborFinset _ _).mpr (M.adj_sub hy)
    apply separated_balanced_nonadjacent H p hmax hop
    · rw [gain_eq, hreg, hdu]; decide
    · rw [gain_eq, hreg, hdv]; decide

end Kostochka.FiveRegular

end


section -- DegreeFourCut

/- The cut optimization in Lemma 1 of A. V. Kostochka (1996), specialized
to simple graphs. The two induced forests are witnessed by a removal ordering.
-/

namespace Kostochka.Cut

open Finset SimpleGraph

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- An ordering in which every vertex has at most one earlier same-side neighbor.
Ties are included, so a cycle is forbidden independent of the ordering of ties. -/
def ForestCut (c : V → Bool) : Prop :=
  ∃ rank : V → ℕ, ∀ u, ((G.neighborFinset u).filter
    (fun w => c w = c u ∧ rank w ≤ rank u)).card ≤ 1

private def weight (c : V → Bool) (u v : V) : ℕ :=
  if G.Adj u v ∧ c u = c v then 1 else 0

private def energy (c : V → Bool) : ℕ := ∑ u, ∑ v, weight G c u v

omit [Fintype V] [DecidableEq V] in
private theorem weight_symm (c : V → Bool) (u v : V) :
    weight G c u v = weight G c v u := by simp [weight, G.adj_comm, eq_comm]

omit [DecidableEq V] in
private theorem weight_count (c : V → Bool) (u : V) :
    (∑ v, weight G c u v) = ((G.neighborFinset u).filter fun v => c v = c u).card := by
  classical
  simp only [weight, Finset.sum_boole]
  apply congrArg Finset.card
  ext v
  simp [eq_comm]

/-- Splitting the symmetric adjacency sum into the row and column through `x`
counts each monochromatic incident edge twice. -/
private theorem split_energy (c : V → Bool) (x : V) :
    energy G c = (∑ u ∈ univ.erase x, ∑ v ∈ univ.erase x, weight G c u v)
      + 2 * ((G.neighborFinset x).filter fun v => c v = c x).card := by
  classical
  have split (f : V → ℕ) : (∑ u, f u) = (∑ u ∈ univ.erase x, f u) + f x :=
    (Finset.sum_erase_add _ _ (Finset.mem_univ x)).symm
  have diag : weight G c x x = 0 := by simp [weight]
  have row : (∑ v ∈ univ.erase x, weight G c x v) =
      ((G.neighborFinset x).filter fun v => c v = c x).card := by
    rw [← weight_count G, split (weight G c x), diag, Nat.add_zero]
  have col : (∑ v ∈ univ.erase x, weight G c v x) =
      ((G.neighborFinset x).filter fun v => c v = c x).card := by
    convert row using 1
    exact Finset.sum_congr rfl fun v _ => weight_symm G c v x
  unfold energy
  rw [split (fun u => ∑ v, weight G c u v)]
  simp_rw [split (weight G c _)]
  rw [Finset.sum_add_distrib, col, row, diag]
  omega

def flip (c : V → Bool) (v u : V) : Bool := if u = v then !c u else c u

private theorem flip_count (c : V → Bool) (v : V) :
    ((G.neighborFinset v).filter (fun w => flip c v w = flip c v v)).card +
      ((G.neighborFinset v).filter (fun w => c w = c v)).card = G.degree v := by
  classical
  have heq : (G.neighborFinset v).filter (fun w => flip c v w = flip c v v) =
      (G.neighborFinset v).filter (fun w => ¬ c w = c v) := by
    ext w
    by_cases h : w = v
    · subst w; simp
    · cases hv : c v <;> cases hw : c w <;> simp [flip, h, hv, hw]
  rw [heq, Nat.add_comm, Finset.card_filter_add_card_filter_not, G.card_neighborFinset_eq_degree]

private theorem flip_forest {c : V → Bool} (hc : ForestCut G c) (v : V)
    (hv : ((G.neighborFinset v).filter (fun w => flip c v w = flip c v v)).card ≤ 1) :
    ForestCut G (flip c v) := by
  classical
  obtain ⟨rank, hr⟩ := hc
  let fresh := univ.sup rank + 1
  let r (w : V) := if w = v then fresh else rank w
  refine ⟨r, fun u => ?_⟩
  by_cases hu : u = v
  · subst u
    apply Nat.le_trans _ hv
    apply Finset.card_le_card
    intro w hw
    obtain ⟨hw, h, _⟩ := Finset.mem_filter.mp hw
    exact Finset.mem_filter.mpr ⟨hw, h⟩
  · apply Nat.le_trans _ (hr u)
    apply Finset.card_le_card
    intro w hw
    obtain ⟨hwu, hcol, hle⟩ := Finset.mem_filter.mp hw
    have hwv : w ≠ v := by
      rintro rfl
      have hb : rank u ≤ univ.sup rank := Finset.le_sup (f := rank) (mem_univ u)
      simp [r, fresh, hu] at hle
      omega
    exact Finset.mem_filter.mpr ⟨hwu, by simpa [flip, hwv, hu] using hcol,
      by simpa [r, hwv, hu] using hle⟩

private theorem optimized_cut (h : ∃ c, ForestCut G c) :
    ∃ c, ForestCut G c ∧ ∀ d, ForestCut G d → energy G c ≤ energy G d := by
  classical
  let choices := univ.filter (fun c : V → Bool => ForestCut G c)
  obtain ⟨c, hc, hmin⟩ := choices.exists_min_image (energy G)
    (by obtain ⟨c, hc⟩ := h; exact ⟨c, by simpa [choices] using hc⟩)
  exact ⟨c, by simpa [choices] using hc, fun d hd => hmin d (by simpa [choices] using hd)⟩

/-- The optimizing step of Lemma 1: among forest cuts choose one with fewest
monochromatic edges. If any vertex retains three neighbors, switching it preserves
the forest ordering and strictly improves the objective. -/
private theorem bounded_of_min {c : V → Bool} (forest : ForestCut G c)
    (hmin : ∀ d, ForestCut G d → energy G c ≤ energy G d) (hdeg : ∀ u, G.degree u ≤ 4)
    (u : V) : ((G.neighborFinset u).filter fun w => c w = c u).card ≤ 2 := by
  classical
  by_contra! bad
  have count := flip_count G c u
  have small : ((G.neighborFinset u).filter (fun w => flip c u w = flip c u u)).card ≤ 1 := by
    have := hdeg u; omega
  have newForest := flip_forest G forest u small
  have best := hmin (flip c u) newForest
  have off : (∑ x ∈ univ.erase u, ∑ y ∈ univ.erase u, weight G (flip c u) x y) =
      (∑ x ∈ univ.erase u, ∑ y ∈ univ.erase u, weight G c x y) := by
    apply Finset.sum_congr rfl
    intro x hx
    apply Finset.sum_congr rfl
    intro y hy
    simp [weight, flip, (Finset.mem_erase.mp hx).1, (Finset.mem_erase.mp hy).1]
  rw [split_energy G c u, split_energy G (flip c u) u, off] at best
  omega

omit [DecidableEq V] in
/-- A forest cut of minimum energy is maximal under inclusion of crossing edges.
Any strict enlargement preserves the forest ordering and strictly lowers energy. -/
private theorem maximal_of_min {c : V → Bool} (hc : ForestCut G c)
    (hmin : ∀ d, ForestCut G d → energy G c ≤ energy G d) (d : V → Bool)
    (hinc : ∀ x y, G.Adj x y → c x ≠ c y → d x ≠ d y) :
    ∀ x y, G.Adj x y → d x ≠ d y → c x ≠ c y := by
  classical
  have same {x y : V} (hxy : G.Adj x y) (hd : d x = d y) : c x = c y := by
    by_contra h
    exact hinc _ _ hxy h hd
  obtain ⟨rank, hr⟩ := hc
  have hforest : ForestCut G d := by
    refine ⟨rank, fun u => Nat.le_trans (Finset.card_le_card ?_) (hr u)⟩
    intro w hw
    obtain ⟨hwu, hcol, hle⟩ := Finset.mem_filter.mp hw
    exact Finset.mem_filter.mpr ⟨hwu, same ((G.mem_neighborFinset _ _).mp hwu).symm hcol, hle⟩
  have mono (x y : V) : weight G d x y ≤ weight G c x y := by
    unfold weight
    split_ifs with hd hc hc <;> first | omega | exact False.elim (hc ⟨hd.1, same hd.1 hd.2⟩)
  intro x y hxy hd hcol
  have lt : weight G d x y < weight G c x y := by simp [weight, hxy, hd, hcol]
  have strict : energy G d < energy G c := Finset.sum_lt_sum
    (fun v _ => Finset.sum_le_sum (fun w _ => mono v w))
    ⟨x, mem_univ x, Finset.sum_lt_sum (fun w _ => mono x w) ⟨y, mem_univ y, lt⟩⟩
  exact (Nat.not_lt_of_ge (hmin d hforest)) strict

/-- The local-degree bound and inclusion maximality hold for the same cut. -/
theorem bounded_forest_cut (h : ∃ c, ForestCut G c) (hdeg : ∀ u, G.degree u ≤ 4) :
    ∃ c, ForestCut G c ∧
      (∀ u, ((G.neighborFinset u).filter fun w => c w = c u).card ≤ 2) ∧
      ∀ d : V → Bool, (∀ x y, G.Adj x y → c x ≠ c y → d x ≠ d y) →
        ∀ x y, G.Adj x y → d x ≠ d y → c x ≠ c y := by
  obtain ⟨c, hc, hmin⟩ := optimized_cut G h
  exact ⟨c, hc, bounded_of_min G hc hmin hdeg, maximal_of_min G hc hmin⟩

/-- All three cut properties used for Kostochka's constrained Euler tour. -/
theorem forest_cut_with_connected_cross_edges (h : ∃ c, ForestCut G c) (hdeg : ∀ u, G.degree u ≤ 4) :
    ∃ c, ForestCut G c ∧
      (∀ u, ((G.neighborFinset u).filter fun w => c w = c u).card ≤ 2) ∧
      ∀ x y, G.Adj x y → (FiveRegular.crossGraph G c).Reachable x y := by
  obtain ⟨c, hc, hb, hm⟩ := bounded_forest_cut G h hdeg
  refine ⟨c, hc, hb, fun x y hxy => FiveRegular.crossing_reachable_of_maximal G c ?_ hxy⟩
  intro d h a b hd
  exact ⟨hd.1, hm d (fun u v huv hne => (h (show (FiveRegular.crossGraph G c).Adj u v from ⟨huv, hne⟩)).2) a b hd.1 hd.2⟩

end Kostochka.Cut

end


section -- ForestOrder

/- Finite forests admit a leaf deletion order. Conversely, the maximal vertex
of a cycle would have two earlier neighbors in any such order. -/

namespace Kostochka.Cut
open SimpleGraph Finset

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Pointwise version of the leaf deletion order. -/
def LeafOrder (rank : V → ℕ) : Prop :=
  ∀ v x y, G.Adj v x → G.Adj v y → rank x ≤ rank v → rank y ≤ rank v → x = y

omit [DecidableEq V] [DecidableRel G.Adj] in
private theorem exists_leaf [Nonempty V] (forest : G.IsAcyclic) :
    ∃ v, ∀ x y, G.Adj v x → G.Adj v y → x = y := by
  classical
  let C := G.connectedComponentMk (Classical.arbitrary V)
  let : Fintype C := Fintype.ofFinite C
  have tree : C.toSimpleGraph.IsTree := ⟨C.connected_toSimpleGraph, forest.induce C.supp⟩
  have leaf : ∃ v : C, ∀ x y : C, C.toSimpleGraph.Adj v x → C.toSimpleGraph.Adj v y → x = y := by
    rcases subsingleton_or_nontrivial C with hs | hn
    · exact ⟨⟨C.out, C.out_eq⟩, fun x y _ _ => hs.elim x y⟩
    · obtain ⟨v, hv⟩ := tree.exists_vert_degree_one_of_nontrivial
      obtain ⟨_, _, unique⟩ := degree_eq_one_iff_existsUnique_adj.mp hv
      exact ⟨v, fun x y hx hy => (unique x hx).trans (unique y hy).symm⟩
  obtain ⟨v, hv⟩ := leaf
  refine ⟨v.val, fun x y hx hy => ?_⟩
  let x' : C := ⟨x,C.mem_supp_of_adj_mem_supp v.property hx⟩
  let y' : C := ⟨y,C.mem_supp_of_adj_mem_supp v.property hy⟩
  exact congrArg Subtype.val (hv x' y' hx hy)

omit [DecidableRel G.Adj] in
theorem leafOrder_of_isAcyclic (forest : G.IsAcyclic) : ∃ rank, LeafOrder G rank := by
  classical
  have go (s : Finset V) : ∃ r : V → ℕ, ∀ v ∈ s, ∀ x ∈ s, ∀ y ∈ s,
      G.Adj v x → G.Adj v y → r x ≤ r v → r y ≤ r v → x = y := by
    induction s using Finset.strongInductionOn with
    | _ s ih =>
      by_cases hs : s.Nonempty
      · let : Nonempty (s : Set V) := ⟨⟨hs.choose, hs.choose_spec⟩⟩
        obtain ⟨v, hv⟩ := exists_leaf (G.induce (s : Set V)) (forest.induce _)
        obtain ⟨r, hr⟩ := ih (s.erase v.val) (Finset.erase_ssubset v.property)
        let fresh := univ.sup r + 1
        let rr (z : V) := if z = v.val then fresh else r z
        have high (z : V) : r z < fresh := Nat.lt_succ_of_le (Finset.le_sup (f := r) (mem_univ z))
        refine ⟨rr, ?_⟩
        intro w hw x hx y hy wx wy rx ry
        by_cases hwv : w = v.val
        · subst w
          exact congrArg Subtype.val (hv ⟨x,hx⟩ ⟨y,hy⟩ wx wy)
        · have nx : x ≠ v.val := by
            intro hxv
            have : fresh ≤ r w := by simpa [rr, hxv, hwv] using rx
            exact (high w).not_ge this
          have ny : y ≠ v.val := by
            intro hyv
            have : fresh ≤ r w := by simpa [rr, hyv, hwv] using ry
            exact (high w).not_ge this
          exact hr w (mem_erase.mpr ⟨hwv,hw⟩) x (mem_erase.mpr ⟨nx,hx⟩) y (mem_erase.mpr ⟨ny,hy⟩)
            wx wy (by simpa [rr,nx,hwv] using rx) (by simpa [rr,ny,hwv] using ry)
      · exact ⟨fun _ => 0, fun v hv => (hs ⟨v,hv⟩).elim⟩
  obtain ⟨r, hr⟩ := go univ
  exact ⟨r, fun v x y => hr v (mem_univ _) x (mem_univ _) y (mem_univ _)⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem isAcyclic_of_leafOrder {r : V → ℕ} (ord : LeafOrder G r) : G.IsAcyclic := by
  classical
  rw [isAcyclic_iff_free_cycleGraph]
  intro n hn hc
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [Nat.add_comm 3 m] at hc
  obtain ⟨f⟩ := hc
  obtain ⟨v, _, maxv⟩ := Finset.exists_max_image univ (fun i => r (f i)) Finset.univ_nonempty
  let N := (cycleGraph (m + 3)).neighborFinset v
  have two : N.card = 2 := cycleGraph_degree_three_le
  have small : N.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro x hx y hy
    apply f.injective
    exact ord (f v) (f x) (f y) (f.toHom.map_rel' ((mem_neighborFinset _ _ _).mp hx))
      (f.toHom.map_rel' ((mem_neighborFinset _ _ _).mp hy)) (maxv x (mem_univ x)) (maxv y (mem_univ y))
  omega

/-- Translate between the graph theoretic forests and the rank used to optimize the cut. -/
theorem forestCut_iff_induce (c : V → Bool) :
    ForestCut G c ↔ ∀ b, (G.induce {v | c v = b}).IsAcyclic := by
  classical
  constructor
  · rintro ⟨r, hr⟩ b
    apply isAcyclic_of_leafOrder _ (r := fun v => r v.val)
    intro v x y vx vy rx ry
    have h := Finset.card_le_one.mp (hr v.val)
    exact Subtype.ext (h x.val (mem_filter.mpr ⟨(G.mem_neighborFinset _ _).mpr vx,
        x.property.trans v.property.symm, rx⟩) y.val
      (mem_filter.mpr ⟨(G.mem_neighborFinset _ _).mpr vy, y.property.trans v.property.symm, ry⟩))
  · intro h
    choose r hr using fun b => leafOrder_of_isAcyclic _ (h b)
    let rank (v : V) := r (c v) ⟨v,rfl⟩
    refine ⟨rank, fun v => Finset.card_le_one.mpr ?_⟩
    intro x hx y hy
    obtain ⟨hvx, ex, rx⟩ := mem_filter.mp hx
    obtain ⟨hvy, ey, ry⟩ := mem_filter.mp hy
    have atSide (w : V) {b : Bool} (e : c w = b) : rank w = r b ⟨w,e⟩ := by
      subst b; rfl
    exact congrArg Subtype.val (hr (c v) ⟨v,rfl⟩ ⟨x,ex⟩ ⟨y,ey⟩
      ((G.mem_neighborFinset _ _).mp hvx) ((G.mem_neighborFinset _ _).mp hvy)
      (by simpa only [atSide x ex] using rx) (by simpa only [atSide y ey] using ry))

end Kostochka.Cut

end


section -- Factors

/-
# Core of Kostochka (1996) Lemma 2: 2-Factor Partition Separating Internal Edges

Given a finite 4-regular simple graph `G` with a vertex bipartition `V = S ⊔ Sᶜ` (or `c : V → Bool`)
whose induced subgraphs on each part are forests of maximum degree at most 2, and whose spanning
subgraph of crossing edges is connected, we partition `E(G)` into two 2-factors `F₁` and `F₂`
such that at every vertex any two distinct incident internal edges belong to different 2-factors.

## Proof overview

1. **Eulerian circuits (`exists_closed_isEulerian`)**:
   Every finite connected simple graph in which every vertex has even degree admits a closed
   Eulerian trail `p : H.Walk r r`, proved by taking a closed trail of maximum length and
   splicing in a closed trail from the residual even-degree graph via `Walk.rotate`.
2. **Balanced alternating coloring (`exists_half_degree_partition_of_closed_isEulerian`)**:
   Splitting a closed Eulerian trail of even length into its even-indexed edges and odd-indexed
   edges partitions `H` into two edge-disjoint spanning subgraphs `H₁, H₂` satisfying
   `H₁.degree x = H₂.degree x` and `2 * H₁.degree x = H.degree x` at every vertex `x`.
3. **Vertex-splitting construction (`splitGraph`)**:
   Split every vertex `v` with internal degree 2 into `crossVert v` (incident to the 2 crossing
   edges at `v`) and `intVert v` (incident to the 2 internal edges at `v`), while leaving vertices
   of internal degree 0 or 1 unsplit. The resulting graph `H` is still a **simple** graph:
   - Its edges are in bijection with `E(G)`, so `#H.edgeFinset = #G.edgeFinset = 2 * |V|` is even.
   - Every vertex of `H` has degree 2 or 4 (hence even).
   - `H` is connected: all `crossVert v` lie in one component via the connected crossing graph, and
     every `intVert v` lies in a nontrivial tree component of the acyclic internal graph, hence
     reaches a leaf (internal degree 1), where the internal edge attaches to `crossVert`.
   Applying (1) and (2) to `H` and projecting back to `G` yields two 2-factors `F₁, F₂`
   partitioning `E(G)` such that every vertex of internal degree 2 has one internal edge in `F₁`
   and one in `F₂`.
-/

namespace Kostochka

open SimpleGraph Finset

section Eulerian

variable {W : Type*}

/-- For a trail `p` in `H`, the number of edges of `p` incident to `x` equals the cardinality of
`hp.edgesFinset.filter (x ∈ ·)`. -/
private lemma countP_edges_eq_card_filter [DecidableEq W] {H : SimpleGraph W} {u v : W}
    {p : H.Walk u v} (hp : p.IsTrail) (x : W) :
    p.edges.countP (fun e => x ∈ e) = (hp.edgesFinset.filter (fun e => x ∈ e)).card := by
  rw [← Multiset.coe_countP, Multiset.countP_eq_card_filter]
  rfl

/-- Deleting the edges of a trail `p` reduces the degree of `x` by `p.edges.countP (x ∈ ·)`. -/
private lemma degree_deleteEdges_walk_add_countP [Fintype W] [DecidableEq W] {H : SimpleGraph W}
    [DecidableRel H.Adj] {u v : W} {p : H.Walk u v}
    [DecidableRel (H.deleteEdges p.edgeSet).Adj] (hp : p.IsTrail) (x : W) :
    (H.deleteEdges p.edgeSet).degree x + p.edges.countP (fun e => x ∈ e) = H.degree x := by
  rw [countP_edges_eq_card_filter hp x, ← card_incidenceFinset_eq_degree,
    ← card_incidenceFinset_eq_degree]
  have h1 : (H.deleteEdges p.edgeSet).incidenceFinset x =
      (H.incidenceFinset x).filter (fun e => e ∉ hp.edgesFinset) := by
    ext e
    simp only [mem_incidenceFinset, mem_filter, incidenceSet, Set.mem_ofPred_eq,
      edgeSet_deleteEdges, Set.mem_sdiff, Walk.mem_edgeSet]
    tauto
  have h2 : hp.edgesFinset.filter (fun e => x ∈ e) =
      (H.incidenceFinset x).filter (fun e => e ∈ hp.edgesFinset) := by
    ext e
    simp only [mem_filter, mem_incidenceFinset, incidenceSet, Set.mem_ofPred_eq]
    exact ⟨fun ⟨he, hx⟩ => ⟨⟨p.edges_subset_edgeSet he, hx⟩, he⟩,
      fun ⟨⟨_, hx⟩, he⟩ => ⟨he, hx⟩⟩
  rw [h1, h2, add_comm]
  exact Finset.card_filter_add_card_filter_not (fun e => e ∈ hp.edgesFinset)

/-- In a finite graph where every vertex has even degree, every vertex of positive degree lies on
a nonempty closed trail. -/
private lemma exists_nonempty_closed_isTrail_of_even_degree [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj]
    (heven : ∀ x : W, Even (H.degree x)) {w : W} (hw : 0 < H.degree w) :
    ∃ c : H.Walk w w, c.IsTrail ∧ 0 < c.length := by
  classical
  let S : Set ℕ := {n | ∃ (z : W) (t : H.Walk w z), t.IsTrail ∧ t.length = n}
  have hS_fin : S.Finite :=
    (Set.finite_le_nat H.edgeFinset.card).subset fun n ⟨_, _, ht, hn⟩ =>
      hn ▸ ht.length_le_card_edgeFinset
  have hS_ne : S.Nonempty := ⟨0, w, Walk.nil, Walk.IsTrail.nil, rfl⟩
  obtain ⟨m, ⟨z, t, ht, rfl⟩, hmax⟩ := hS_fin.exists_maximal hS_ne
  have ht_pos : 0 < t.length := by
    obtain ⟨w', hww'⟩ := (H.degree_pos_iff_exists_adj w).mp hw
    have h1 : 1 ∈ S := ⟨w', Walk.cons hww' Walk.nil, by simp, rfl⟩
    have hle : 1 ≤ t.length := by
      by_contra hlt
      have ht0 : t.length < 1 := Nat.lt_of_not_ge hlt
      exact absurd (hmax h1 ht0.le) (by omega)
    exact lt_of_lt_of_le Nat.zero_lt_one hle
  have hzw : z = w := by
    by_contra hne
    have hne' : w ≠ z := Ne.symm hne
    have hnotEven : ¬ Even (t.edges.countP (fun e => z ∈ e)) := by
      rw [ht.even_countP_edges_iff z]
      intro h
      exact (h hne').2 rfl
    have hdeg_eq := degree_deleteEdges_walk_add_countP ht z
    have hdel_pos : 0 < (H.deleteEdges t.edgeSet).degree z := by
      by_contra hzero
      have h0 : (H.deleteEdges t.edgeSet).degree z = 0 := Nat.eq_zero_of_not_pos hzero
      rw [h0, zero_add] at hdeg_eq
      exact hnotEven (hdeg_eq ▸ heven z)
    obtain ⟨z', hzz'⟩ := ((H.deleteEdges t.edgeSet).degree_pos_iff_exists_adj z).mp hdel_pos
    rw [deleteEdges_adj] at hzz'
    have hnotmem : s(z, z') ∉ t.edges := hzz'.2
    have hconcat_trail : (t.concat hzz'.1).IsTrail := by
      rw [Walk.concat_eq_append, Walk.isTrail_append]
      refine ⟨ht, by simp, ?_⟩
      intro e he1 he2
      simp only [Walk.edges_cons, Walk.edges_nil, List.mem_singleton] at he2
      exact hnotmem (he2 ▸ he1)
    have hmem : t.length + 1 ∈ S := ⟨z', t.concat hzz'.1, hconcat_trail, t.length_concat hzz'.1⟩
    exact absurd (hmax hmem (Nat.le_succ _)) (by omega)
  subst hzw
  exact ⟨t, ht, ht_pos⟩

/-- **Euler's theorem (closed Eulerian trail)**: every finite connected simple graph in which every
vertex has even degree has a closed Eulerian trail. -/
theorem exists_closed_isEulerian [Fintype W] [DecidableEq W] (H : SimpleGraph W)
    [DecidableRel H.Adj] (hconn : H.Connected) (heven : ∀ x : W, Even (H.degree x)) :
    ∃ (r : W) (p : H.Walk r r), p.IsEulerian := by
  classical
  let S : Set ℕ := {n | ∃ (u : W) (p : H.Walk u u), p.IsTrail ∧ p.length = n}
  have hS_fin : S.Finite :=
    (Set.finite_le_nat H.edgeFinset.card).subset fun n ⟨_, _, hp, hn⟩ =>
      hn ▸ hp.length_le_card_edgeFinset
  obtain ⟨r₀⟩ := hconn.nonempty
  have hS_ne : S.Nonempty := ⟨0, r₀, Walk.nil, Walk.IsTrail.nil, rfl⟩
  obtain ⟨m, ⟨u, p, hp, rfl⟩, hmax⟩ := hS_fin.exists_maximal hS_ne
  refine ⟨u, p, hp.isEulerian_of_forall_mem fun e he => ?_⟩
  by_contra hnotmem
  let H' : SimpleGraph W := H.deleteEdges p.edgeSet
  have heven' : ∀ x : W, Even (H'.degree x) := by
    intro x
    have hsum := degree_deleteEdges_walk_add_countP hp x
    have hp_even : Even (p.edges.countP (fun e => x ∈ e)) :=
      (hp.even_countP_edges_iff x).mpr fun hne => (hne rfl).elim
    have hadd : Even (H'.degree x + p.edges.countP (fun e => x ∈ e)) := hsum ▸ heven x
    exact (Nat.even_add.mp hadd).mpr hp_even
  -- Find a vertex `w ∈ p.support` with positive degree in `H'`.
  have hex_w : ∃ w ∈ p.support, 0 < H'.degree w := by
    induction e using Sym2.ind with
    | _ a b =>
      have hab : H.Adj a b := he
      have hab' : H'.Adj a b := by
        rw [deleteEdges_adj]
        exact ⟨hab, hnotmem⟩
      by_cases ha : a ∈ p.support
      · exact ⟨a, ha, hab'.degree_pos_left⟩
      · obtain ⟨q⟩ := hconn u a
        obtain ⟨d, _, hd_fst, hd_snd⟩ :=
          q.exists_boundary_dart {x | x ∈ p.support} p.start_mem_support ha
        have hd_notmem : s(d.fst, d.snd) ∉ p.edges := fun hmem =>
          hd_snd (p.snd_mem_support_of_mem_edges hmem)
        have hd_adj' : H'.Adj d.fst d.snd := by
          rw [deleteEdges_adj]
          exact ⟨d.adj, hd_notmem⟩
        exact ⟨d.fst, hd_fst, hd_adj'.degree_pos_left⟩
  obtain ⟨w, hw_supp, hw_pos⟩ := hex_w
  obtain ⟨c, hc_trail, hc_pos⟩ := exists_nonempty_closed_isTrail_of_even_degree heven' hw_pos
  let cH : H.Walk w w := c.mapLe (H.deleteEdges_le p.edgeSet)
  let p' : H.Walk w w := p.rotate w hw_supp
  have hcH_edges : cH.edges = c.edges := Walk.edges_mapLe_eq_edges _ _
  have hcH_trail : cH.IsTrail := by
    rw [Walk.isTrail_def, hcH_edges]
    exact hc_trail.edges_nodup
  have hp'_trail : p'.IsTrail := hp.rotate hw_supp
  have hdisj : p'.edges.Disjoint cH.edges := by
    intro e' he1 he2
    have he1' : e' ∈ p.edges := (p.rotate_edges w hw_supp).perm.mem_iff.mp he1
    rw [hcH_edges] at he2
    have he2' : e' ∈ H'.edgeSet := c.edges_subset_edgeSet he2
    rw [edgeSet_deleteEdges] at he2'
    exact he2'.2 he1'
  have hcomb_trail : (p'.append cH).IsTrail :=
    (Walk.isTrail_append p' cH).mpr ⟨hp'_trail, hcH_trail, hdisj⟩
  have hcomb_len : (p'.append cH).length = p.length + c.length := by
    rw [Walk.length_append, Walk.length_rotate, Walk.length_mapLe]
  have hmem : p.length + c.length ∈ S := ⟨w, p'.append cH, hcomb_trail, hcomb_len⟩
  have hle : p.length + c.length ≤ p.length := hmax hmem (Nat.le_add_right _ _)
  omega

/-- The length of an Eulerian trail equals the number of edges of the graph. -/
lemma IsEulerian.length_eq_card_edgeFinset [Fintype W] [DecidableEq W] {H : SimpleGraph W}
    [DecidableRel H.Adj] {u v : W} {p : H.Walk u v} (hp : p.IsEulerian) :
    p.length = H.edgeFinset.card := by
  have h1 : p.edges.toFinset = H.edgeFinset := by
    ext e
    simp [hp.mem_edges_iff]
  rw [← h1, List.toFinset_card_of_nodup hp.isTrail.edges_nodup, p.length_edges]

end Eulerian

section AlternatingPartition

variable {W : Type*}

mutual
/-- Edges at even indices (`0, 2, 4, ...`) of a walk. -/
def evenEdges {H : SimpleGraph W} : ∀ {u v : W}, H.Walk u v → List (Sym2 W)
  | _, _, .nil => []
  | a, _, .cons (v := b) _ q => s(a, b) :: oddEdges q

/-- Edges at odd indices (`1, 3, 5, ...`) of a walk. -/
def oddEdges {H : SimpleGraph W} : ∀ {u v : W}, H.Walk u v → List (Sym2 W)
  | _, _, .nil => []
  | _, _, .cons _ q => evenEdges q
end

private lemma perm_evenEdges_append_oddEdges {H : SimpleGraph W} {u v : W} (w : H.Walk u v) :
    (evenEdges w ++ oddEdges w).Perm w.edges := by
  induction w with
  | nil => simp [evenEdges, oddEdges]
  | cons h q ih =>
    simp only [evenEdges, oddEdges, Walk.edges_cons, List.cons_append]
    exact (List.perm_append_comm.trans ih).cons _

private lemma countP_evenEdges_sub_oddEdges [DecidableEq W] {H : SimpleGraph W} {u v : W}
    (w : H.Walk u v) (x : W) :
    ((evenEdges w).countP (fun e => x ∈ e) : ℤ) - ((oddEdges w).countP (fun e => x ∈ e) : ℤ) =
      (if x = u then 1 else 0) + (-1 : ℤ) ^ w.length * (if x = v then -1 else 0) := by
  induction w with
  | nil =>
    simp only [evenEdges, oddEdges, List.countP_nil, Nat.cast_zero, sub_self, Walk.length_nil,
      pow_zero, one_mul]
    split_ifs <;> ring
  | @cons a b c h q ih =>
    have hab : a ≠ b := h.ne
    have hmem : ((decide (x ∈ s(a, b))).toNat : ℤ) =
        (if x = a then 1 else 0) + (if x = b then 1 else 0) := by
      by_cases hxa : x = a <;> by_cases hxb : x = b
      · exact absurd (hxa.symm.trans hxb) hab
      · simp [Sym2.mem_iff, hxa, hab]
      · simp [Sym2.mem_iff, hxb, hab.symm]
      · simp [Sym2.mem_iff, hxa, hxb]
    simp only [evenEdges, oddEdges, List.countP_cons, Walk.length_cons, pow_succ']
    have hstep :
        (((oddEdges q).countP (fun e => x ∈ e) + (if decide (x ∈ s(a, b)) then 1 else 0) : ℕ) : ℤ) =
        ((oddEdges q).countP (fun e => x ∈ e) : ℤ) + ((decide (x ∈ s(a, b))).toNat : ℤ) := by
      cases decide (x ∈ s(a, b)) <;> simp
    rw [hstep, hmem]
    linarith

private lemma countP_evenEdges_eq_oddEdges [DecidableEq W] {H : SimpleGraph W} {r : W}
    (p : H.Walk r r) (hlen : Even p.length) (x : W) :
    (evenEdges p).countP (fun e => x ∈ e) = (oddEdges p).countP (fun e => x ∈ e) := by
  have h := countP_evenEdges_sub_oddEdges p x
  rw [hlen.neg_one_pow, one_mul] at h
  have hzero : ((evenEdges p).countP (fun e => x ∈ e) : ℤ) -
      ((oddEdges p).countP (fun e => x ∈ e) : ℤ) = 0 := by
    rw [h]
    split_ifs <;> ring
  omega

/-- Subgraph spanned by the edges in a list `L` contained in `H.edgeSet`. -/
private def graphOfEdgeList {H : SimpleGraph W} (L : List (Sym2 W))
    (hL : ∀ e ∈ L, e ∈ H.edgeSet) : SimpleGraph W where
  Adj x y := s(x, y) ∈ L
  symm := ⟨fun _ _ h => by rwa [Sym2.eq_swap]⟩
  loopless := ⟨fun x h => H.loopless.irrefl x (hL s(x, x) h)⟩

private instance decRelGraphOfEdgeList [DecidableEq W] {H : SimpleGraph W} (L : List (Sym2 W))
    (hL : ∀ e ∈ L, e ∈ H.edgeSet) : DecidableRel (graphOfEdgeList L hL).Adj :=
  fun x y => inferInstanceAs (Decidable (s(x, y) ∈ L))

private lemma degree_graphOfEdgeList [Fintype W] [DecidableEq W] {H : SimpleGraph W}
    (L : List (Sym2 W)) (hL : ∀ e ∈ L, e ∈ H.edgeSet) (hnodup : L.Nodup) (x : W) :
    (graphOfEdgeList L hL).degree x = L.countP (fun e => x ∈ e) := by
  rw [← card_incidenceFinset_eq_degree]
  have hinc : (graphOfEdgeList L hL).incidenceFinset x = (L.filter (fun e => x ∈ e)).toFinset := by
    ext e
    rw [mem_incidenceFinset, List.mem_toFinset, List.mem_filter]
    induction e using Sym2.ind with
    | _ a b =>
      simp [incidenceSet, graphOfEdgeList]
  rw [hinc, List.toFinset_card_of_nodup (hnodup.filter _), List.countP_eq_length_filter]

/-- Partition a finite graph with an even-length closed Eulerian trail into two edge-disjoint
spanning subgraphs each having half the degree of `H` at every vertex. -/
theorem exists_half_degree_partition_of_closed_isEulerian [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] {r : W} (p : H.Walk r r)
    (hp : p.IsEulerian) (hlen : Even p.length) :
    ∃ (H₁ H₂ : SimpleGraph W) (_ : DecidableRel H₁.Adj) (_ : DecidableRel H₂.Adj),
      H₁ ⊔ H₂ = H ∧ Disjoint H₁ H₂ ∧
      (∀ x : W, H₁.degree x = H₂.degree x) ∧
      (∀ x : W, 2 * H₁.degree x = H.degree x) ∧
      (∀ x : W, 2 * H₂.degree x = H.degree x) := by
  have hperm : (evenEdges p ++ oddEdges p).Perm p.edges := perm_evenEdges_append_oddEdges p
  have hnodup_all : (evenEdges p ++ oddEdges p).Nodup := hperm.nodup_iff.mpr hp.isTrail.edges_nodup
  rw [List.nodup_append'] at hnodup_all
  obtain ⟨hnodup₁, hnodup₂, hdisj_list⟩ := hnodup_all
  have hsub₁ : ∀ e ∈ evenEdges p, e ∈ H.edgeSet := fun e he =>
    p.edges_subset_edgeSet (hperm.mem_iff.mp (List.mem_append_left _ he))
  have hsub₂ : ∀ e ∈ oddEdges p, e ∈ H.edgeSet := fun e he =>
    p.edges_subset_edgeSet (hperm.mem_iff.mp (List.mem_append_right _ he))
  let H₁ := graphOfEdgeList (evenEdges p) hsub₁
  let H₂ := graphOfEdgeList (oddEdges p) hsub₂
  refine ⟨H₁, H₂, inferInstance, inferInstance, ?_, ?_, ?_, ?_, ?_⟩
  · ext x y
    simp only [sup_adj, H₁, H₂, graphOfEdgeList]
    rw [← List.mem_append, hperm.mem_iff, hp.mem_edges_iff, mem_edgeSet]
  · rw [disjoint_iff]
    ext x y
    simp only [inf_adj, bot_adj, H₁, H₂, graphOfEdgeList, iff_false, not_and]
    exact fun h1 h2 => hdisj_list h1 h2
  · intro x
    rw [degree_graphOfEdgeList _ _ hnodup₁, degree_graphOfEdgeList _ _ hnodup₂]
    exact countP_evenEdges_eq_oddEdges p hlen x
  · intro x
    have hdeg_eq : H₁.degree x = H₂.degree x := by
      rw [degree_graphOfEdgeList _ _ hnodup₁, degree_graphOfEdgeList _ _ hnodup₂]
      exact countP_evenEdges_eq_oddEdges p hlen x
    have hdeg_sum : H₁.degree x + H₂.degree x = H.degree x := by
      rw [degree_graphOfEdgeList _ _ hnodup₁, degree_graphOfEdgeList _ _ hnodup₂,
        ← List.countP_append, hperm.countP_eq, countP_edges_eq_card_filter hp.isTrail x,
        ← card_incidenceFinset_eq_degree, hp.edgesFinset_eq, H.incidenceFinset_eq_filter x]
    omega
  · intro x
    have hdeg_eq : H₁.degree x = H₂.degree x := by
      rw [degree_graphOfEdgeList _ _ hnodup₁, degree_graphOfEdgeList _ _ hnodup₂]
      exact countP_evenEdges_eq_oddEdges p hlen x
    have hdeg_sum : H₁.degree x + H₂.degree x = H.degree x := by
      rw [degree_graphOfEdgeList _ _ hnodup₁, degree_graphOfEdgeList _ _ hnodup₂,
        ← List.countP_append, hperm.countP_eq, countP_edges_eq_card_filter hp.isTrail x,
        ← card_incidenceFinset_eq_degree, hp.edgesFinset_eq, H.incidenceFinset_eq_filter x]
    omega

end AlternatingPartition

section SplitConstruction

variable {V : Type*}

/-- Spanning subgraph of edges with both endpoints in the same part of `c : V → Bool`. -/
def internalGraph (G : SimpleGraph V) (c : V → Bool) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ c u = c v
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => G.loopless.irrefl _ h.1⟩

/-- Spanning subgraph of edges with endpoints in opposite parts of `c : V → Bool`. -/
def crossingGraph (G : SimpleGraph V) (c : V → Bool) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ c u ≠ c v
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => G.loopless.irrefl _ h.1⟩

instance instDecidableRelInternalGraph (G : SimpleGraph V) [DecidableRel G.Adj] (c : V → Bool) :
    DecidableRel (internalGraph G c).Adj :=
  fun u v => inferInstanceAs (Decidable (G.Adj u v ∧ c u = c v))

instance instDecidableRelCrossingGraph (G : SimpleGraph V) [DecidableRel G.Adj] (c : V → Bool) :
    DecidableRel (crossingGraph G c).Adj :=
  fun u v => inferInstanceAs (Decidable (G.Adj u v ∧ c u ≠ c v))

lemma internalGraph_le (G : SimpleGraph V) (c : V → Bool) : internalGraph G c ≤ G :=
  fun _ _ h => h.1

lemma crossingGraph_le (G : SimpleGraph V) (c : V → Bool) : crossingGraph G c ≤ G :=
  fun _ _ h => h.1

lemma degree_internal_add_crossing [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → Bool) (v : V) :
    (internalGraph G c).degree v + (crossingGraph G c).degree v = G.degree v := by
  rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree,
    ← card_neighborFinset_eq_degree]
  have h1 : (internalGraph G c).neighborFinset v =
      (G.neighborFinset v).filter (fun w => c v = c w) := by
    ext w
    rw [mem_neighborFinset, mem_filter, mem_neighborFinset]
    rfl
  have h2 : (crossingGraph G c).neighborFinset v =
      (G.neighborFinset v).filter (fun w => ¬ c v = c w) := by
    ext w
    rw [mem_neighborFinset, mem_filter, mem_neighborFinset]
    rfl
  rw [h1, h2]
  exact Finset.card_filter_add_card_filter_not (fun w => c v = c w)

private lemma bool_beq_comm (a b : Bool) : (a == b) = (b == a) := by
  cases a <;> cases b <;> rfl

/-- Vertex set of the split graph: every vertex has a `false` (crossing/unsplit) copy, and
vertices of internal degree 2 additionally have a `true` (internal) copy. -/
abbrev SplitVert [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (c : V → Bool) :=
  { p : V × Bool // p.2 = false ∨ (internalGraph G c).degree p.1 = 2 }

private def crossVert [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (c : V → Bool)
    (v : V) : SplitVert G c :=
  ⟨(v, false), Or.inl rfl⟩

private def intVert [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (c : V → Bool)
    (v : V) (hv : (internalGraph G c).degree v = 2) : SplitVert G c :=
  ⟨(v, true), Or.inr hv⟩

private def splitEndpt [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (c : V → Bool)
    (isInt : Bool) (v : V) : SplitVert G c :=
  if h : isInt = true ∧ (internalGraph G c).degree v = 2 then
    ⟨(v, true), Or.inr h.2⟩
  else
    ⟨(v, false), Or.inl rfl⟩

@[simp]
private lemma splitEndpt_fst [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (c : V → Bool)
    (isInt : Bool) (v : V) : (splitEndpt G c isInt v).1.1 = v := by
  unfold splitEndpt
  split_ifs <;> rfl

private lemma splitEndpt_false [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → Bool) (v : V) :
    splitEndpt G c false v = crossVert G c v := by
  simp [splitEndpt, crossVert]

private lemma splitEndpt_true_of_eq_two [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → Bool) {v : V} (hv : (internalGraph G c).degree v = 2) :
    splitEndpt G c true v = intVert G c v hv := by
  simp [splitEndpt, intVert, hv]

private lemma splitEndpt_of_ne_two [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → Bool) (isInt : Bool) {v : V} (hv : (internalGraph G c).degree v ≠ 2) :
    splitEndpt G c isInt v = crossVert G c v := by
  simp [splitEndpt, crossVert, hv]

/-- The split simple graph `H`: crossing edges attach to `crossVert`, while internal edges attach
to `intVert` at endpoints of internal degree 2 and to `crossVert` otherwise. -/
private def splitGraph [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (c : V → Bool) :
    SimpleGraph (SplitVert G c) where
  Adj x y := G.Adj x.1.1 y.1.1 ∧
    x = splitEndpt G c (c x.1.1 == c y.1.1) x.1.1 ∧
    y = splitEndpt G c (c x.1.1 == c y.1.1) y.1.1
  symm := ⟨fun x y h => by
    refine ⟨h.1.symm, ?_, ?_⟩
    · simpa [bool_beq_comm] using h.2.2
    · simpa [bool_beq_comm] using h.2.1⟩
  loopless := ⟨fun x h => G.loopless.irrefl x.1.1 h.1⟩

private instance decRelSplitGraph [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (c : V → Bool) :
    DecidableRel (splitGraph G c).Adj :=
  fun x y => inferInstanceAs (Decidable (G.Adj x.1.1 y.1.1 ∧
    x = splitEndpt G c (c x.1.1 == c y.1.1) x.1.1 ∧
    y = splitEndpt G c (c x.1.1 == c y.1.1) y.1.1))

private lemma splitGraph_adj_splitEndpt [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → Bool) {u v : V} (h : G.Adj u v) :
    (splitGraph G c).Adj (splitEndpt G c (c u == c v) u) (splitEndpt G c (c u == c v) v) := by
  simp [splitGraph, h]

/-- Projecting a subgraph `K ≤ splitGraph G c` back down to `V`. -/
private def projectSubgraph [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (c : V → Bool)
    (K : SimpleGraph (SplitVert G c)) : SimpleGraph V where
  Adj u v := K.Adj (splitEndpt G c (c u == c v) u) (splitEndpt G c (c u == c v) v)
  symm := ⟨fun u v h => by
    rw [bool_beq_comm]
    exact h.symm⟩
  loopless := ⟨fun u h => K.loopless.irrefl _ h⟩

private instance decRelProjectSubgraph [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → Bool) (K : SimpleGraph (SplitVert G c)) [DecidableRel K.Adj] :
    DecidableRel (projectSubgraph G c K).Adj :=
  fun u v => inferInstanceAs
    (Decidable (K.Adj (splitEndpt G c (c u == c v) u) (splitEndpt G c (c u == c v) v)))

private lemma projectSubgraph_splitGraph [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → Bool) :
    projectSubgraph G c (splitGraph G c) = G := by
  ext u v
  simp [projectSubgraph, splitGraph]

private lemma projectSubgraph_sup [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → Bool) (K₁ K₂ : SimpleGraph (SplitVert G c)) :
    projectSubgraph G c (K₁ ⊔ K₂) = projectSubgraph G c K₁ ⊔ projectSubgraph G c K₂ := by
  ext u v
  simp [projectSubgraph]

private lemma projectSubgraph_disjoint [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → Bool) {K₁ K₂ : SimpleGraph (SplitVert G c)} (h : Disjoint K₁ K₂) :
    Disjoint (projectSubgraph G c K₁) (projectSubgraph G c K₂) := by
  rw [disjoint_iff] at h ⊢
  ext u v
  simp only [inf_adj, bot_adj, projectSubgraph, iff_false]
  intro h12
  have : (K₁ ⊓ K₂).Adj (splitEndpt G c (c u == c v) u) (splitEndpt G c (c u == c v) v) := h12
  rw [h] at this
  exact this

/-- For `K ≤ splitGraph G c` and `u` with internal degree `≠ 2`, the neighbors of `u` in
`projectSubgraph K` biject with the neighbors of `crossVert u` in `K`. -/
private lemma degree_projectSubgraph_of_ne_two [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (c : V → Bool) {K : SimpleGraph (SplitVert G c)} [DecidableRel K.Adj]
    (hK : K ≤ splitGraph G c) {u : V} (hu : (internalGraph G c).degree u ≠ 2) :
    (projectSubgraph G c K).degree u = K.degree (crossVert G c u) := by
  rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree]
  refine Finset.card_bij (fun v _ => splitEndpt G c (c u == c v) v) ?_ ?_ ?_
  · intro v hv
    rw [mem_neighborFinset] at hv ⊢
    dsimp [projectSubgraph] at hv
    rwa [splitEndpt_of_ne_two G c _ hu] at hv
  · intro v₁ _ v₂ _ h
    have := congrArg (fun x : SplitVert G c => x.1.1) h
    simpa using this
  · intro y hy
    rw [mem_neighborFinset] at hy
    have hH : (splitGraph G c).Adj (crossVert G c u) y := hK hy
    have hy_eq : y = splitEndpt G c (c u == c y.1.1) y.1.1 := hH.2.2
    refine ⟨y.1.1, ?_, hy_eq.symm⟩
    rw [mem_neighborFinset]
    dsimp [projectSubgraph]
    rw [splitEndpt_of_ne_two G c _ hu, ← hy_eq]
    exact hy

/-- For `K ≤ splitGraph G c` and `u` with internal degree `= 2`, the internal neighbors of `u` in
`projectSubgraph K` biject with the neighbors of `intVert u` in `K`. -/
private lemma card_internal_neighbors_projectSubgraph [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (c : V → Bool)
    {K : SimpleGraph (SplitVert G c)} [DecidableRel K.Adj]
    (hK : K ≤ splitGraph G c) {u : V} (hu : (internalGraph G c).degree u = 2) :
    ((projectSubgraph G c K).neighborFinset u |>.filter (fun v => c u = c v)).card =
      K.degree (intVert G c u hu) := by
  rw [← card_neighborFinset_eq_degree]
  refine Finset.card_bij (fun v _ => splitEndpt G c true v) ?_ ?_ ?_
  · intro v hv
    rw [mem_filter, mem_neighborFinset] at hv
    rw [mem_neighborFinset]
    have hbeq : (c u == c v) = true := beq_iff_eq.mpr hv.2
    have h1 : K.Adj (splitEndpt G c (c u == c v) u) (splitEndpt G c (c u == c v) v) := hv.1
    rw [hbeq, splitEndpt_true_of_eq_two G c hu] at h1
    exact h1
  · intro v₁ _ v₂ _ h
    have := congrArg (fun x : SplitVert G c => x.1.1) h
    simpa using this
  · intro y hy
    rw [mem_neighborFinset] at hy
    have hH : (splitGraph G c).Adj (intVert G c u hu) y := hK hy
    have hbeq : (c u == c y.1.1) = true := by
      cases hval : (c u == c y.1.1) with
      | true => rfl
      | false =>
        have hxu := hH.2.1
        simp only [intVert, hval, splitEndpt_false, crossVert, Subtype.mk.injEq,
          Prod.mk.injEq] at hxu
        exact absurd hxu.2 (by decide)
    have hceq : c u = c y.1.1 := beq_iff_eq.mp hbeq
    have hy_eq : y = splitEndpt G c true y.1.1 := by
      simpa [intVert, hbeq] using hH.2.2
    refine ⟨y.1.1, ?_, hy_eq.symm⟩
    rw [mem_filter, mem_neighborFinset]
    refine ⟨?_, hceq⟩
    change K.Adj (splitEndpt G c (c u == c y.1.1) u) (splitEndpt G c (c u == c y.1.1) y.1.1)
    rw [hbeq, splitEndpt_true_of_eq_two G c hu, ← hy_eq]
    exact hy

/-- For `K ≤ splitGraph G c` and `u` with internal degree `= 2`, the crossing neighbors of `u` in
`projectSubgraph K` biject with the neighbors of `crossVert u` in `K`. -/
private lemma card_crossing_neighbors_projectSubgraph [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (c : V → Bool)
    {K : SimpleGraph (SplitVert G c)} [DecidableRel K.Adj]
    (hK : K ≤ splitGraph G c) {u : V} (hu : (internalGraph G c).degree u = 2) :
    ((projectSubgraph G c K).neighborFinset u |>.filter (fun v => c u ≠ c v)).card =
      K.degree (crossVert G c u) := by
  rw [← card_neighborFinset_eq_degree]
  refine Finset.card_bij (fun v _ => splitEndpt G c false v) ?_ ?_ ?_
  · intro v hv
    rw [mem_filter, mem_neighborFinset] at hv
    rw [mem_neighborFinset]
    have hbeq : (c u == c v) = false := beq_eq_false_iff_ne.mpr hv.2
    have h1 : K.Adj (splitEndpt G c (c u == c v) u) (splitEndpt G c (c u == c v) v) := hv.1
    rw [hbeq, splitEndpt_false] at h1
    exact h1
  · intro v₁ _ v₂ _ h
    have := congrArg (fun x : SplitVert G c => x.1.1) h
    simpa using this
  · intro y hy
    rw [mem_neighborFinset] at hy
    have hH : (splitGraph G c).Adj (crossVert G c u) y := hK hy
    have hbeq : (c u == c y.1.1) = false := by
      cases hval : (c u == c y.1.1) with
      | false => rfl
      | true =>
        have hxu := hH.2.1
        simp only [crossVert, hval, splitEndpt_true_of_eq_two G c hu, intVert,
          Subtype.mk.injEq, Prod.mk.injEq] at hxu
        exact absurd hxu.2 (by decide)
    have hcne : c u ≠ c y.1.1 := beq_eq_false_iff_ne.mp hbeq
    have hy_eq : y = splitEndpt G c false y.1.1 := by
      simpa [crossVert, hbeq] using hH.2.2
    refine ⟨y.1.1, ?_, hy_eq.symm⟩
    rw [mem_filter, mem_neighborFinset]
    refine ⟨?_, hcne⟩
    change K.Adj (splitEndpt G c (c u == c y.1.1) u) (splitEndpt G c (c u == c y.1.1) y.1.1)
    rw [hbeq, splitEndpt_false, ← hy_eq]
    exact hy

private lemma degree_projectSubgraph_of_eq_two [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (c : V → Bool) {K : SimpleGraph (SplitVert G c)} [DecidableRel K.Adj]
    (hK : K ≤ splitGraph G c) {u : V} (hu : (internalGraph G c).degree u = 2) :
    (projectSubgraph G c K).degree u =
      K.degree (intVert G c u hu) + K.degree (crossVert G c u) := by
  rw [← card_internal_neighbors_projectSubgraph G c hK hu,
    ← card_crossing_neighbors_projectSubgraph G c hK hu,
    ← card_neighborFinset_eq_degree]
  exact (Finset.card_filter_add_card_filter_not (fun v => c u = c v)).symm

private lemma neighborFinset_projectSubgraph_splitGraph [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (c : V → Bool) (u : V) :
    (projectSubgraph G c (splitGraph G c)).neighborFinset u = G.neighborFinset u := by
  ext v
  rw [mem_neighborFinset, mem_neighborFinset]
  simp [projectSubgraph, splitGraph]

private lemma splitGraph_degree_cross_of_ne_two [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (c : V → Bool) {u : V} (hu : (internalGraph G c).degree u ≠ 2) :
    (splitGraph G c).degree (crossVert G c u) = G.degree u := by
  rw [← degree_projectSubgraph_of_ne_two G c le_rfl hu, ← card_neighborFinset_eq_degree,
    ← card_neighborFinset_eq_degree, neighborFinset_projectSubgraph_splitGraph]

private lemma splitGraph_degree_int [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (c : V → Bool) {u : V} (hu : (internalGraph G c).degree u = 2) :
    (splitGraph G c).degree (intVert G c u hu) = 2 := by
  rw [← card_internal_neighbors_projectSubgraph G c le_rfl hu,
    neighborFinset_projectSubgraph_splitGraph]
  have hfilt : (G.neighborFinset u).filter (fun v => c u = c v) =
      (internalGraph G c).neighborFinset u := by
    ext v
    rw [mem_filter, mem_neighborFinset, mem_neighborFinset]
    rfl
  rw [hfilt, card_neighborFinset_eq_degree, hu]

private lemma splitGraph_degree_cross_of_eq_two [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (c : V → Bool) (hreg : G.IsRegularOfDegree 4)
    {u : V} (hu : (internalGraph G c).degree u = 2) :
    (splitGraph G c).degree (crossVert G c u) = 2 := by
  rw [← card_crossing_neighbors_projectSubgraph G c le_rfl hu,
    neighborFinset_projectSubgraph_splitGraph]
  have hfilt : (G.neighborFinset u).filter (fun v => c u ≠ c v) =
      (crossingGraph G c).neighborFinset u := by
    ext v
    rw [mem_filter, mem_neighborFinset, mem_neighborFinset]
    rfl
  rw [hfilt, card_neighborFinset_eq_degree]
  have hsum := degree_internal_add_crossing G c u
  have h4 := hreg u
  omega

private lemma splitGraph_even_degree [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (c : V → Bool) (hreg : G.IsRegularOfDegree 4) (x : SplitVert G c) :
    Even ((splitGraph G c).degree x) := by
  rcases x with ⟨⟨u, b⟩, hx⟩
  cases b with
  | false =>
    change Even ((splitGraph G c).degree (crossVert G c u))
    by_cases hu : (internalGraph G c).degree u = 2
    · rw [splitGraph_degree_cross_of_eq_two G c hreg hu]
      exact even_two
    · rw [splitGraph_degree_cross_of_ne_two G c hu, hreg u]
      exact ⟨2, rfl⟩
  | true =>
    have hu : (internalGraph G c).degree u = 2 := hx.resolve_left (by simp)
    change Even ((splitGraph G c).degree (intVert G c u hu))
    rw [splitGraph_degree_int G c hu]
    exact even_two

private lemma card_edgeFinset_splitGraph [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (c : V → Bool) :
    (splitGraph G c).edgeFinset.card = G.edgeFinset.card := by
  refine Finset.card_bij (fun e _ => e.map (fun x : SplitVert G c => x.1.1)) ?_ ?_ ?_
  · intro e he
    rw [mem_edgeFinset] at he ⊢
    induction e using Sym2.ind with
    | _ x y =>
      simpa using he.1
  · intro e₁ he₁ e₂ he₂ heq
    rw [mem_edgeFinset] at he₁ he₂
    induction e₁ using Sym2.ind with
    | _ x₁ y₁ =>
      induction e₂ using Sym2.ind with
      | _ x₂ y₂ =>
        rw [mem_edgeSet] at he₁ he₂
        rw [Sym2.map_mk, Sym2.map_mk, Sym2.eq_iff] at heq
        rcases heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · have hx : x₁ = x₂ := by rw [he₁.2.1, he₂.2.1, h1, h2]
          have hy : y₁ = y₂ := by rw [he₁.2.2, he₂.2.2, h1, h2]
          rw [hx, hy]
        · have hx : x₁ = y₂ := by rw [he₁.2.1, he₂.2.2, h1, h2, bool_beq_comm]
          have hy : y₁ = x₂ := by rw [he₁.2.2, he₂.2.1, h1, h2, bool_beq_comm]
          rw [hx, hy, Sym2.eq_swap]
  · intro e he
    rw [mem_edgeFinset] at he
    induction e using Sym2.ind with
    | _ u v =>
      refine ⟨s(splitEndpt G c (c u == c v) u, splitEndpt G c (c u == c v) v), ?_, ?_⟩
      · rw [mem_edgeFinset]
        exact splitGraph_adj_splitEndpt G c he
      · simp

private lemma even_card_edgeFinset_splitGraph [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (c : V → Bool) (hreg : G.IsRegularOfDegree 4) :
    Even (splitGraph G c).edgeFinset.card := by
  rw [card_edgeFinset_splitGraph]
  have hsum := G.sum_degrees_eq_twice_card_edges
  have h4 : ∑ v : V, G.degree v = 4 * Fintype.card V := by
    simp [hreg.degree_eq, mul_comm]
  rw [h4] at hsum
  exact ⟨Fintype.card V, by omega⟩

private lemma splitGraph_connected [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (c : V → Bool)
    (hacyc : (internalGraph G c).IsAcyclic) (hcross : (crossingGraph G c).Connected) :
    (splitGraph G c).Connected := by
  have : Nonempty (SplitVert G c) := ⟨crossVert G c hcross.nonempty.some⟩
  -- `crossVert` maps walks of `crossingGraph G c` into `splitGraph G c`.
  let fCross : crossingGraph G c →g splitGraph G c :=
    { toFun := crossVert G c
      map_rel' := fun {u v} h => by
        have hbeq : (c u == c v) = false := beq_eq_false_iff_ne.mpr h.2
        refine ⟨h.1, ?_, ?_⟩ <;> simp [crossVert, hbeq, splitEndpt_false] }
  -- `splitEndpt true` maps walks of `internalGraph G c` into `splitGraph G c`.
  let fInt : internalGraph G c →g splitGraph G c :=
    { toFun := splitEndpt G c true
      map_rel' := fun {u v} h => by
        have hbeq : (c u == c v) = true := beq_iff_eq.mpr h.2
        simpa [hbeq] using splitGraph_adj_splitEndpt G c h.1 }
  -- Every vertex of `splitGraph G c` is reachable from some `crossVert w`.
  have htoCross : ∀ x : SplitVert G c, ∃ w : V, (splitGraph G c).Reachable x (crossVert G c w) := by
    rintro ⟨⟨u, b⟩, hx⟩
    cases b with
    | false =>
      exact ⟨u, Reachable.refl _⟩
    | true =>
      have hu : (internalGraph G c).degree u = 2 := hx.resolve_left (by simp)
      let C := (internalGraph G c).connectedComponentMk u
      have htree : C.toSimpleGraph.IsTree := hacyc.isTree_connectedComponent C
      have hu_pos : 0 < (internalGraph G c).degree u := by omega
      obtain ⟨v, huv⟩ := ((internalGraph G c).degree_pos_iff_exists_adj u).mp hu_pos
      have : Nontrivial C.supp := by
        refine ⟨⟨u, rfl⟩, ⟨v, ConnectedComponent.sound huv.symm.reachable⟩, ?_⟩
        intro heq
        exact huv.ne (congrArg Subtype.val heq)
      classical
      obtain ⟨w, hw_deg⟩ := htree.exists_vert_degree_one_of_nontrivial
      have hw_deg_int : (internalGraph G c).degree w.1 = 1 := by
        rw [← hw_deg, ← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree]
        refine Finset.card_bij
          (fun z hz => ⟨z, by
            have hadj : (internalGraph G c).Adj w.1 z := (mem_neighborFinset _ _ _).mp hz
            exact (ConnectedComponent.sound hadj.symm.reachable).trans w.2⟩)
          ?_ ?_ ?_
        · intro z hz
          rw [mem_neighborFinset] at hz ⊢
          exact hz
        · intro z₁ _ z₂ _ h
          exact congrArg Subtype.val h
        · intro z hz
          rw [mem_neighborFinset] at hz
          exact ⟨z.1, (mem_neighborFinset _ _ _).mpr hz, Subtype.ext rfl⟩
      have hw_ne2 : (internalGraph G c).degree w.1 ≠ 2 := by omega
      have hreach_int : (internalGraph G c).Reachable u w.1 :=
        ConnectedComponent.exact w.2.symm
      have hreach_H : (splitGraph G c).Reachable (fInt u) (fInt w.1) :=
        hreach_int.map fInt
      refine ⟨w.1, ?_⟩
      have hfu : fInt u = ⟨(u, true), hx⟩ := by
        simp [fInt, splitEndpt, hu]
      have hfw : fInt w.1 = crossVert G c w.1 := splitEndpt_of_ne_two G c true hw_ne2
      rwa [hfu, hfw] at hreach_H
  refine Connected.mk fun x y => ?_
  obtain ⟨u, hxu⟩ := htoCross x
  obtain ⟨v, hyv⟩ := htoCross y
  have huv : (splitGraph G c).Reachable (crossVert G c u) (crossVert G c v) :=
    (hcross u v).map fCross
  exact hxu.trans (huv.trans hyv.symm)

end SplitConstruction

section MainTheorems

variable {V : Type*}

/-- **Core of Kostochka (1996) Lemma 2** (`Bool`-bipartition formulation).

Let `G` be a finite 4-regular simple graph with a vertex bipartition `c : V → Bool` such that:
- `internalGraph G c` is acyclic (the two induced pieces are forests),
- every vertex has internal degree at most 2, and
- `crossingGraph G c` is connected.

Then `E(G)` partitions into two edge-disjoint 2-factors `F₁` and `F₂` such that at every vertex
any two distinct incident internal edges belong to different factors (equivalently, each factor
has internal degree at most 1 at every vertex). -/
theorem exists_two_factor_partition_of_bipartition [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (c : V → Bool)
    (hreg : G.IsRegularOfDegree 4)
    (hacyc : (internalGraph G c).IsAcyclic)
    (hdeg_int : ∀ v : V, (internalGraph G c).degree v ≤ 2)
    (hcross : (crossingGraph G c).Connected) :
    ∃ (F₁ F₂ : SimpleGraph V),
      F₁ ⊔ F₂ = G ∧
      Disjoint F₁ F₂ ∧
      (∀ [F₁.LocallyFinite], F₁.IsRegularOfDegree 2) ∧
      (∀ [F₂.LocallyFinite], F₂.IsRegularOfDegree 2) ∧
      (∀ u v w : V, v ≠ w →
        (internalGraph G c).Adj u v → (internalGraph G c).Adj u w →
        ¬ (F₁.Adj u v ∧ F₁.Adj u w) ∧ ¬ (F₂.Adj u v ∧ F₂.Adj u w)) := by
  let H := splitGraph G c
  have hconn : H.Connected := splitGraph_connected G c hacyc hcross
  have heven : ∀ x, Even (H.degree x) := splitGraph_even_degree G c hreg
  obtain ⟨r, p, hp⟩ := exists_closed_isEulerian H hconn heven
  have hplen : Even p.length := by
    rw [IsEulerian.length_eq_card_edgeFinset hp]
    exact even_card_edgeFinset_splitGraph G c hreg
  obtain ⟨H₁, H₂, _, _, hsup, hdisj, _, hdeg₁, hdeg₂⟩ :=
    exists_half_degree_partition_of_closed_isEulerian H p hp hplen
  have hH₁_le : H₁ ≤ H := hsup ▸ le_sup_left
  have hH₂_le : H₂ ≤ H := hsup ▸ le_sup_right
  let F₁ := projectSubgraph G c H₁
  let F₂ := projectSubgraph G c H₂
  have hF₁_deg : ∀ v : V, F₁.degree v = 2 := by
    intro v
    by_cases hv : (internalGraph G c).degree v = 2
    · rw [degree_projectSubgraph_of_eq_two G c hH₁_le hv]
      have h1 := hdeg₁ (intVert G c v hv)
      have h2 := hdeg₁ (crossVert G c v)
      rw [splitGraph_degree_int G c hv] at h1
      rw [splitGraph_degree_cross_of_eq_two G c hreg hv] at h2
      omega
    · rw [degree_projectSubgraph_of_ne_two G c hH₁_le hv]
      have h1 := hdeg₁ (crossVert G c v)
      rw [splitGraph_degree_cross_of_ne_two G c hv, hreg v] at h1
      omega
  have hF₂_deg : ∀ v : V, F₂.degree v = 2 := by
    intro v
    by_cases hv : (internalGraph G c).degree v = 2
    · rw [degree_projectSubgraph_of_eq_two G c hH₂_le hv]
      have h1 := hdeg₂ (intVert G c v hv)
      have h2 := hdeg₂ (crossVert G c v)
      rw [splitGraph_degree_int G c hv] at h1
      rw [splitGraph_degree_cross_of_eq_two G c hreg hv] at h2
      omega
    · rw [degree_projectSubgraph_of_ne_two G c hH₂_le hv]
      have h1 := hdeg₂ (crossVert G c v)
      rw [splitGraph_degree_cross_of_ne_two G c hv, hreg v] at h1
      omega
  refine ⟨F₁, F₂, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← projectSubgraph_sup, hsup, projectSubgraph_splitGraph]
  · exact projectSubgraph_disjoint G c hdisj
  · intro inst v
    have h := hF₁_deg v
    rw [← card_neighborSet_eq_degree] at h ⊢
    convert h
  · intro inst v
    have h := hF₂_deg v
    rw [← card_neighborSet_eq_degree] at h ⊢
    convert h
  · intro u v w hvw huv huw
    have h2le : 2 ≤ (internalGraph G c).degree u := by
      rw [← card_neighborFinset_eq_degree]
      have hsub : ({v, w} : Finset V) ⊆ (internalGraph G c).neighborFinset u := by
        intro z hz
        simp only [mem_insert, mem_singleton] at hz
        rcases hz with rfl | rfl <;> simpa
      calc 2 = ({v, w} : Finset V).card := (Finset.card_pair hvw).symm
        _ ≤ ((internalGraph G c).neighborFinset u).card := Finset.card_le_card hsub
    have hu2 : (internalGraph G c).degree u = 2 := le_antisymm (hdeg_int u) h2le
    have hcard₁ : ((F₁.neighborFinset u).filter (fun z => c u = c z)).card = 1 := by
      rw [card_internal_neighbors_projectSubgraph G c hH₁_le hu2]
      have h1 := hdeg₁ (intVert G c u hu2)
      rw [splitGraph_degree_int G c hu2] at h1
      omega
    have hcard₂ : ((F₂.neighborFinset u).filter (fun z => c u = c z)).card = 1 := by
      rw [card_internal_neighbors_projectSubgraph G c hH₂_le hu2]
      have h2 := hdeg₂ (intVert G c u hu2)
      rw [splitGraph_degree_int G c hu2] at h2
      omega
    constructor
    · rintro ⟨hv1, hw1⟩
      have hsub : ({v, w} : Finset V) ⊆ (F₁.neighborFinset u).filter (fun z => c u = c z) := by
        intro z hz
        simp only [mem_insert, mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact mem_filter.mpr ⟨(mem_neighborFinset _ _ _).mpr hv1, huv.2⟩
        · exact mem_filter.mpr ⟨(mem_neighborFinset _ _ _).mpr hw1, huw.2⟩
      have hle := Finset.card_le_card hsub
      rw [Finset.card_pair hvw, hcard₁] at hle
      omega
    · rintro ⟨hv2, hw2⟩
      have hsub : ({v, w} : Finset V) ⊆ (F₂.neighborFinset u).filter (fun z => c u = c z) := by
        intro z hz
        simp only [mem_insert, mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact mem_filter.mpr ⟨(mem_neighborFinset _ _ _).mpr hv2, huv.2⟩
        · exact mem_filter.mpr ⟨(mem_neighborFinset _ _ _).mpr hw2, huw.2⟩
      have hle := Finset.card_le_card hsub
      rw [Finset.card_pair hvw, hcard₂] at hle
      omega

private lemma induce_isCycle_of_internal_isCycle {G : SimpleGraph V} {c : V → Bool} {b : Bool}
    {u : V} (hcu : c u = b) {p : (internalGraph G c).Walk u u} (hp : p.IsCycle) :
    ∃ q : (G.induce {v | c v = b}).Walk ⟨u, hcu⟩ ⟨u, hcu⟩, q.IsCycle := by
  have hconst : ∀ x ∈ p.support, c x = b := by
    have hwalk : ∀ {a d : V} (q : (internalGraph G c).Walk a d),
        ∀ x ∈ q.support, c x = c a := by
      intro a d q
      induction q with
      | nil =>
        intro x hx
        rw [Walk.mem_support_nil_iff.mp hx]
      | @cons a d e hadj q ih =>
        intro x hx
        rw [Walk.support_cons, List.mem_cons] at hx
        rcases hx with rfl | hx
        · rfl
        · exact (ih x hx).trans hadj.2.symm
    intro x hx
    exact (hwalk p x hx).trans hcu
  let pG : G.Walk u u := p.mapLe (internalGraph_le G c)
  have hpG_supp : ∀ x ∈ pG.support, x ∈ ({v | c v = b} : Set V) := by
    intro x hx
    rw [Walk.support_mapLe_eq_support] at hx
    exact hconst x hx
  let q : (G.induce {v | c v = b}).Walk ⟨u, hcu⟩ ⟨u, hcu⟩ := pG.induce {v | c v = b} hpG_supp
  have hmap : q.map (Embedding.induce {v | c v = b}).toHom = pG := Walk.map_induce pG hpG_supp
  refine ⟨q, ?_⟩
  rw [Walk.isCycle_def, Walk.isTrail_def]
  refine ⟨?_, ?_, ?_⟩
  · refine List.Nodup.of_map (Sym2.map (Embedding.induce (G := G) {v | c v = b}).toHom) ?_
    rw [← Walk.edges_map, hmap]
    exact (Walk.edges_mapLe_eq_edges (internalGraph_le G c) p).symm ▸ hp.isTrail.edges_nodup
  · intro hnil
    have hlen := congrArg Walk.length hmap
    rw [Walk.length_map, hnil, Walk.length_nil] at hlen
    have hplen : p.length = 0 := by simpa [pG, Walk.length_mapLe] using hlen.symm
    exact hp.not_nil (Walk.length_eq_zero_iff.mp hplen)
  · refine List.Nodup.of_map (Embedding.induce (G := G) {v | c v = b}).toHom ?_
    rw [List.map_tail, ← Walk.support_map, hmap]
    exact congrArg List.tail (Walk.support_mapLe_eq_support (internalGraph_le G c) p) ▸ hp.support_nodup

/-- Equivalence between acyclicity of `internalGraph G c` and acyclicity of both induced pieces. -/
lemma internalGraph_isAcyclic_iff_induce (G : SimpleGraph V) (c : V → Bool) :
    (internalGraph G c).IsAcyclic ↔
      (G.induce {v | c v = true}).IsAcyclic ∧ (G.induce {v | c v = false}).IsAcyclic := by
  constructor
  · intro h
    constructor
    · let fT : G.induce {v | c v = true} →g internalGraph G c :=
        ⟨Subtype.val, fun {u v} huv => ⟨huv, u.2.trans v.2.symm⟩⟩
      exact h.comap fT Subtype.val_injective
    · let fF : G.induce {v | c v = false} →g internalGraph G c :=
        ⟨Subtype.val, fun {u v} huv => ⟨huv, u.2.trans v.2.symm⟩⟩
      exact h.comap fF Subtype.val_injective
  · rintro ⟨ht, hf⟩ u p hp
    cases hcu : c u with
    | true =>
      obtain ⟨q, hq⟩ := induce_isCycle_of_internal_isCycle hcu hp
      exact ht q hq
    | false =>
      obtain ⟨q, hq⟩ := induce_isCycle_of_internal_isCycle hcu hp
      exact hf q hq

/-- The degree of a vertex in `internalGraph G c` equals its degree in its induced piece. -/
lemma degree_internalGraph_eq_degree_induce [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → Bool) (b : Bool) (u : {v : V // c v = b}) :
    (internalGraph G c).degree u.1 = (G.induce {v | c v = b}).degree u := by
  rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree]
  refine Finset.card_bij
    (fun w hw => ⟨w, ((mem_neighborFinset _ _ _).mp hw).2.symm.trans u.2⟩) ?_ ?_ ?_
  · intro w hw
    rw [mem_neighborFinset] at hw ⊢
    exact hw.1
  · intro w₁ _ w₂ _ h
    exact congrArg Subtype.val h
  · intro w hw
    rw [mem_neighborFinset] at hw
    refine ⟨w.1, ?_, Subtype.ext rfl⟩
    rw [mem_neighborFinset]
    exact ⟨hw, u.2.trans w.2.symm⟩

private lemma degree_internalGraph_eq_degree_induce_set [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (S : Set V) [DecidablePred (· ∈ S)] (u : S) :
    (internalGraph G (fun v => decide (v ∈ S))).degree u.1 = (G.induce S).degree u := by
  rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree]
  refine Finset.card_bij
    (fun w hw => ⟨w, by
      have h := ((mem_neighborFinset _ _ _).mp hw).2
      simpa [u.2] using h.symm⟩) ?_ ?_ ?_
  · intro w hw
    rw [mem_neighborFinset] at hw ⊢
    exact hw.1
  · intro w₁ _ w₂ _ h
    exact congrArg Subtype.val h
  · intro w hw
    rw [mem_neighborFinset] at hw
    refine ⟨w.1, ?_, Subtype.ext rfl⟩
    rw [mem_neighborFinset]
    exact ⟨hw, by simp [u.2, w.2]⟩

private lemma degree_internalGraph_eq_degree_induce_compl [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (S : Set V) [DecidablePred (· ∈ S)] (u : (Sᶜ : Set V)) :
    (internalGraph G (fun v => decide (v ∈ S))).degree u.1 = (G.induce Sᶜ).degree u := by
  rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree]
  refine Finset.card_bij
    (fun w hw => ⟨w, by
      have h := ((mem_neighborFinset _ _ _).mp hw).2
      have hu : u.1 ∉ S := u.2
      simpa [hu] using h.symm⟩) ?_ ?_ ?_
  · intro w hw
    rw [mem_neighborFinset] at hw ⊢
    exact hw.1
  · intro w₁ _ w₂ _ h
    exact congrArg Subtype.val h
  · intro w hw
    rw [mem_neighborFinset] at hw
    refine ⟨w.1, ?_, Subtype.ext rfl⟩
    rw [mem_neighborFinset]
    have hu : u.1 ∉ S := u.2
    have hw' : w.1 ∉ S := w.2
    exact ⟨hw, by simp [hu, hw']⟩

/-- **Core of Kostochka (1996) Lemma 2** (induced-pieces & `maxDegree` formulation).

Given a finite 4-regular simple graph `G` and a vertex bipartition `S : Set V` (with `DecidablePred`
membership) such that:
- `G.induce S` and `G.induce Sᶜ` are forests (`IsAcyclic`) of `maxDegree ≤ 2`, and
- the spanning subgraph of crossing edges between `S` and `Sᶜ` is connected,

there exist two edge-disjoint 2-factors `F₁, F₂` with `F₁ ⊔ F₂ = G` such that at every vertex any
two distinct incident internal edges belong to different factors. -/
theorem exists_two_factor_partition_of_induced_forests [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Set V) [DecidablePred (· ∈ S)]
    (hreg : G.IsRegularOfDegree 4)
    (hacycS : (G.induce S).IsAcyclic)
    (hacycSc : (G.induce Sᶜ).IsAcyclic)
    (hmaxS : (G.induce S).maxDegree ≤ 2)
    (hmaxSc : (G.induce Sᶜ).maxDegree ≤ 2)
    (hcross : (crossingGraph G (fun v => decide (v ∈ S))).Connected) :
    ∃ (F₁ F₂ : SimpleGraph V),
      F₁ ⊔ F₂ = G ∧
      Disjoint F₁ F₂ ∧
      (∀ [F₁.LocallyFinite], F₁.IsRegularOfDegree 2) ∧
      (∀ [F₂.LocallyFinite], F₂.IsRegularOfDegree 2) ∧
      (∀ u v w : V, v ≠ w →
        G.Adj u v → G.Adj u w →
        ((u ∈ S ∧ v ∈ S ∧ w ∈ S) ∨ (u ∉ S ∧ v ∉ S ∧ w ∉ S)) →
        ¬ (F₁.Adj u v ∧ F₁.Adj u w) ∧ ¬ (F₂.Adj u v ∧ F₂.Adj u w)) := by
  let c : V → Bool := fun v => decide (v ∈ S)
  have hsetT : {v : V | c v = true} = S := by
    ext v
    simp [c]
  have hsetF : {v : V | c v = false} = Sᶜ := by
    ext v
    simp [c]
  have hacyc : (internalGraph G c).IsAcyclic := by
    rw [internalGraph_isAcyclic_iff_induce]
    exact ⟨hsetT ▸ hacycS, hsetF ▸ hacycSc⟩
  have hdeg_int : ∀ v : V, (internalGraph G c).degree v ≤ 2 := by
    intro v
    by_cases hv : v ∈ S
    · rw [degree_internalGraph_eq_degree_induce_set G S ⟨v, hv⟩]
      exact (degree_le_maxDegree (G.induce S) ⟨v, hv⟩).trans hmaxS
    · rw [degree_internalGraph_eq_degree_induce_compl G S ⟨v, hv⟩]
      exact (degree_le_maxDegree (G.induce Sᶜ) ⟨v, hv⟩).trans hmaxSc
  obtain ⟨F₁, F₂, hsup, hdisj, hreg₁, hreg₂, hsep⟩ :=
    exists_two_factor_partition_of_bipartition G c hreg hacyc hdeg_int hcross
  refine ⟨F₁, F₂, hsup, hdisj, hreg₁, hreg₂, ?_⟩
  intro u v w hvw huv huw hsame
  have hcu_v : c u = c v := by
    rcases hsame with ⟨hu, hv, _⟩ | ⟨hu, hv, _⟩ <;> simp [c, hu, hv]
  have hcu_w : c u = c w := by
    rcases hsame with ⟨hu, _, hw⟩ | ⟨hu, _, hw⟩ <;> simp [c, hu, hw]
  exact hsep u v w hvw ⟨huv, hcu_v⟩ ⟨huw, hcu_w⟩

/-- Characterization of edges in `crossingGraph` for a set-defined bipartition `S`. -/
lemma crossingGraph_decide_adj (G : SimpleGraph V) (S : Set V) [DecidablePred (· ∈ S)] (u v : V) :
    (crossingGraph G (fun x => decide (x ∈ S))).Adj u v ↔ G.Adj u v ∧ (u ∈ S ↔ v ∉ S) := by
  change (G.Adj u v ∧ decide (u ∈ S) ≠ decide (v ∈ S)) ↔ G.Adj u v ∧ (u ∈ S ↔ v ∉ S)
  by_cases hu : u ∈ S <;> by_cases hv : v ∈ S <;> simp [hu, hv]

/-- Given a partition `F₁ ⊔ F₂ = G` such that two edges `u~v` and `u~w` of `G` do not lie in the
same factor, one lies in `F₁` and the other in `F₂`. -/
lemma mem_opposite_factors_of_not_same {G F₁ F₂ : SimpleGraph V}
    (hsup : F₁ ⊔ F₂ = G) {u v w : V} (huv : G.Adj u v) (huw : G.Adj u w)
    (hsep : ¬ (F₁.Adj u v ∧ F₁.Adj u w) ∧ ¬ (F₂.Adj u v ∧ F₂.Adj u w)) :
    (F₁.Adj u v ∧ F₂.Adj u w) ∨ (F₂.Adj u v ∧ F₁.Adj u w) := by
  have hv : F₁.Adj u v ∨ F₂.Adj u v := by
    rw [← hsup] at huv
    exact huv
  have hw : F₁.Adj u w ∨ F₂.Adj u w := by
    rw [← hsup] at huw
    exact huw
  tauto

end MainTheorems

end Kostochka

end


section -- FourFactors

/- From the initial two induced forests to the constrained pair of spanning
2-factors in Kostochka's degree-four construction. -/

namespace Kostochka.Cut
open SimpleGraph Finset

/-- The factor and ordering data needed for the six-color construction. -/
theorem fourFactors {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (conn : G.Connected) (reg : G.IsRegularOfDegree 4)
    (initial : ∃ c : V → Bool, ∀ b, (G.induce {v | c v = b}).IsAcyclic) :
    ∃ (c : V → Bool) (F₁ F₂ : SimpleGraph V), ForestCut G c ∧
      F₁ ⊔ F₂ = G ∧ Disjoint F₁ F₂ ∧
      (∀ [F₁.LocallyFinite], F₁.IsRegularOfDegree 2) ∧
      (∀ [F₂.LocallyFinite], F₂.IsRegularOfDegree 2) ∧
      ∀ u v w, v ≠ w → c u = c v → c u = c w →
        ¬ (F₁.Adj u v ∧ F₁.Adj u w) ∧ ¬ (F₂.Adj u v ∧ F₂.Adj u w) := by
  classical
  obtain ⟨c₀,h₀⟩ := initial
  obtain ⟨c, hr, hb, hc⟩ := forest_cut_with_connected_cross_edges G
    ⟨c₀,(forestCut_iff_induce G c₀).mpr h₀⟩ (fun v => (reg v).le)
  have acyc : (internalGraph G c).IsAcyclic := by
    obtain ⟨r, h⟩ := hr
    apply isAcyclic_of_leafOrder _ (r := r)
    intro v x y vx vy rx ry
    apply Finset.card_le_one.mp (h v)
    · exact mem_filter.mpr ⟨(G.mem_neighborFinset _ _).mpr vx.1,vx.2.symm,rx⟩
    · exact mem_filter.mpr ⟨(G.mem_neighborFinset _ _).mpr vy.1,vy.2.symm,ry⟩
  have internal (v) : (internalGraph G c).degree v ≤ 2 := by
    have eqn : (internalGraph G c).neighborFinset v = (G.neighborFinset v).filter (fun w => c w = c v) := by
      ext w
      simp only [mem_neighborFinset, mem_filter]
      change _ ∧ c v = c w ↔ _ ∧ c w = c v
      exact and_congr_right fun _ => eq_comm
    simpa only [← card_neighborFinset_eq_degree, eqn] using (show _ from hb v)
  have cx : (crossingGraph G c).Connected := by
    have := conn.nonempty
    refine { preconnected := ?_ }
    intro x y
    obtain ⟨p⟩ := conn.preconnected x y
    induction p with
    | nil => exact Reachable.refl _
    | cons h _ ih => exact (hc _ _ h).trans ih
  obtain ⟨F₁,F₂,hs,hd,h₁,h₂,hboth⟩ := exists_two_factor_partition_of_bipartition G c reg acyc internal cx
  have sub₁ : F₁ ≤ G := hs ▸ le_sup_left
  have sub₂ : F₂ ≤ G := hs ▸ le_sup_right
  refine ⟨c,F₁,F₂,hr,hs,hd,@h₁,@h₂,?_⟩
  intro u v w hne hv hw
  constructor
  · rintro ⟨h₃,h₄⟩
    exact (hboth u v w hne ⟨sub₁ h₃,hv⟩ ⟨sub₁ h₄,hw⟩).1 ⟨h₃,h₄⟩
  · rintro ⟨h₃,h₄⟩
    exact (hboth u v w hne ⟨sub₂ h₃,hv⟩ ⟨sub₂ h₄,hw⟩).2 ⟨h₃,h₄⟩

end Kostochka.Cut

end


section -- DegreeFourPaths

/-
# Three-color extension on a path or a cycle factor

This is the path calculation in Section 3 of A. V. Kostochka,
*The total chromatic number of any multigraph with maximum degree five is at most seven*.
Each vertex carries either one prescribed color or none. Its two incident edges must
have distinct colors, both different from a prescribed vertex color.
-/

namespace Kostochka.Path

abbrev Color := Fin 3

/-- `Extension a vs b` colors the edges around the consecutive vertices `vs`, with the
incoming edge fixed to `a` and the outgoing edge fixed to `b`. -/
inductive Extension : Color → List (Option Color) → Color → Prop where
  | nil (a : Color) : Extension a [] a
  | cons {a b t : Color} {v : Option Color} {vs : List (Option Color)}
      (distinct : a ≠ t) (incoming : v ≠ some a) (outgoing : v ≠ some t)
      (rest : Extension t vs b) : Extension a (v :: vs) b

theorem append {a b c : Color} {s t : List (Option Color)}
    (hs : Extension a s b) (ht : Extension b t c) : Extension a (s ++ t) c := by
  induction hs with
  | nil => exact ht
  | cons hne ha hb _ ih => exact .cons hne ha hb (ih ht)

private theorem third (x y : Color) : ∃ z : Color, z ≠ x ∧ z ≠ y := by decide +revert

private theorem forced {a b c d : Color} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) : a = d := by decide +revert

theorem Extension.split {a b : Color} (s t : List (Option Color))
    (h : Extension a (s ++ t) b) : ∃ c, Extension a s c ∧ Extension c t b := by
  induction s generalizing a with
  | nil => exact ⟨a, .nil _, h⟩
  | cons v s ih =>
    cases h with
    | cons ha hb hc ht =>
      obtain ⟨c, h₁, h₂⟩ := ih ht
      exact ⟨c, .cons ha hb hc h₁, h₂⟩

theorem Extension.rotate {a : Color} {vs : List (Option Color)} (h : Extension a vs a)
    {ws : List (Option Color)} (r : List.IsRotated vs ws) : ∃ b, Extension b ws b := by
  obtain ⟨k,rfl⟩ := r
  let n := k % vs.length
  have eq : vs.take n ++ vs.drop n = vs := List.take_append_drop _ _
  obtain ⟨b,h₁,h₂⟩ := Extension.split (vs.take n) (vs.drop n) (eq.symm ▸ h)
  exact ⟨b, List.rotate_eq_drop_append_take_mod.symm ▸ append h₂ h₁⟩

/-- Read a proof of extension as explicit edge colors indexed along the walk. -/
theorem Extension.edgeColors {a b : Color} {vs : List (Option Color)} (h : Extension a vs b) :
    ∃ f : ℕ → Color, f 0 = a ∧ f vs.length = b ∧
      ∀ i (hi : i < vs.length), f i ≠ f (i + 1) ∧
        vs[i] ≠ some (f i) ∧ vs[i] ≠ some (f (i+1)) := by
  induction h with
  | nil a => exact ⟨fun _ => a, rfl, rfl, by simp⟩
  | @cons a b t v vs hne ha ht h ih =>
    obtain ⟨f, hf0, hfl, hf⟩ := ih
    let g : ℕ → Color := fun n => Nat.casesOn n a f
    refine ⟨g, rfl, hfl, fun i hi => ?_⟩
    cases i with
    | zero => simpa [g,hf0] using And.intro hne (And.intro ha ht)
    | succ i => exact hf i (by simpa using hi)

/-- The same construction with explicit wraparound for a nonempty cyclic factor. -/
theorem Extension.cyclicColors {a : Color} {vs : List (Option Color)}
    (h : Extension a vs a) : ∃ f : Fin vs.length → Color,
      ∀ i : Fin vs.length,
        let j : Fin vs.length := ⟨(i.val + 1) % vs.length, Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩
        f i ≠ f j ∧ vs[i.val] ≠ some (f i) ∧ vs[i.val] ≠ some (f j) := by
  obtain ⟨f, hf0, hfl, hf⟩ := h.edgeColors
  refine ⟨fun i => f i.val, fun i => ?_⟩
  have he : f ((i.val + 1) % vs.length) = f (i.val + 1) := by
    by_cases hlast : i.val + 1 = vs.length
    · simp [hlast, hf0, hfl]
    · rw [Nat.mod_eq_of_lt (by omega)]
  simpa only [he] using hf i.val i.isLt

/-- A nonempty gap between two adjacent-vertex pairs. There is an uncolored vertex
at either end, and no two precolored vertices in the gap are adjacent. -/
inductive Gap where
  | one
  | extra (rest : Gap)
  | mark (c : Color) (rest : Gap)

def Gap.vertices : Gap → List (Option Color)
  | .one => [none]
  | .extra s => none :: s.vertices
  | .mark c s => none :: some c :: s.vertices

/-- A double separator or an intermediate vertex of the incoming edge's color
restores the choice between colors, even if the two boundary colors coincide. -/
def Gap.resets (a : Color) : Gap → Prop
  | .one => False
  | .extra _ => True
  | .mark c s => a = c ∨ s.resets a

/-- Exact endpoint criterion, covering all gap lengths. With a single uncolored
separator between successive prescribed vertices, equal end colors are possible
exactly when the intervening list contains that color. -/
theorem gap_iff (cs : Gap) (a b : Color) :
    Extension a cs.vertices b ↔ a ≠ b ∨ cs.resets a := by
  induction cs generalizing a b with
  | one =>
    constructor
    · intro h
      cases h with
      | cons hd _ _ htail => cases htail; exact Or.inl hd
    · intro h
      have hn : a ≠ b := by simpa [Gap.resets] using h
      exact .cons hn (by simp) (by simp) (.nil _)
  | extra cs ih =>
    refine ⟨fun _ => .inr trivial, fun _ => ?_⟩
    obtain ⟨d, hda, hdb⟩ := third a b
    exact .cons hda.symm (by simp) (by simp) ((ih _ _).mpr (.inl hdb))
  | mark c cs ih =>
    constructor
    · intro h
      cases h with
      | @cons _ _ t _ _ hat _ _ h =>
        cases h with
        | @cons _ _ d _ _ htd hct hcd htail =>
          by_cases hac : a = c
          · exact .inr (.inl hac)
          · have had := forced hat hac (by simpa [eq_comm] using hct) htd
                (by simpa using hcd)
            subst d
            rcases (ih _ _).mp htail with h | h
            · exact .inl h
            · exact .inr (.inr h)
    · intro h
      by_cases hac : a = c
      · subst c
        obtain ⟨d, hda, hdb⟩ := third a b
        obtain ⟨t, hta, htd⟩ := third a d
        exact .cons hta.symm (by simp) (by simp)
          (.cons htd (by simpa using hta.symm) (by simpa using hda.symm)
            ((ih _ _).mpr (.inl hdb)))
      · obtain ⟨t, hta, htc⟩ := third a c
        have hnext : a ≠ b ∨ cs.resets a := by simpa [Gap.resets, hac] using h
        exact .cons hta.symm (by simp) (by simp)
          (.cons hta (by simpa using htc.symm) (by simpa using Ne.symm hac)
            ((ih _ _).mpr hnext))

/-- In a precolored adjacent pair, the exterior edges have the opposite endpoint's
color and the internal edge uses the remaining third color. -/
structure Pair where
  left : Color
  right : Color
  ne : left ≠ right

def Pair.vertices (p : Pair) : List (Option Color) := [some p.left, some p.right]

theorem pair_extension (p : Pair) : Extension p.right p.vertices p.left := by
  obtain ⟨z, hzl, hzr⟩ := third p.left p.right
  exact .cons hzr.symm (by simpa using p.ne) (by simpa using hzl.symm)
    (.cons hzl (by simpa using hzr.symm) (by simpa using p.ne.symm) (.nil _))

/-- The part of a cyclic factor following its first adjacent pair, ending immediately
before that same pair. The last gap is the wraparound gap. -/
def between (last : Gap) : List (Gap × Pair) → List (Option Color)
  | [] => last.vertices
  | (g, p) :: ps => g.vertices ++ (p.vertices ++ between last ps)

def canClose (last : Gap) (target : Color) (fromColor : Color) : List (Gap × Pair) → Prop
  | [] => fromColor ≠ target ∨ last.resets fromColor
  | (g, p) :: ps => (fromColor ≠ p.right ∨ g.resets fromColor) ∧
      canClose last target p.left ps

private theorem between_extension (last : Gap) (target a : Color) (ps : List (Gap × Pair))
    (h : canClose last target a ps) : Extension a (between last ps) target := by
  induction ps generalizing a with
  | nil => exact (gap_iff _ _ _).mpr h
  | cons head tail ih =>
    obtain ⟨g, p⟩ := head
    exact append ((gap_iff _ _ _).mpr h.1) (append (pair_extension p) (ih _ h.2))

/-- Edge extension on a cyclic factor containing precolored pairs. Each isolated
vertex of the chosen color class appears in one of the gaps. -/
theorem cycle_paired (p : Pair) (gaps : List (Gap × Pair)) (last : Gap)
    (h : canClose last p.right p.left gaps) :
    Extension p.right (p.vertices ++ between last gaps) p.right :=
  append (pair_extension p) (between_extension _ _ _ _ h)

/-- A cyclic factor without adjacent prescribed vertices can be cut at any one
vertex. The rest is a gap, and the two incident edge colors at the cut are distinct. -/
theorem cycle_isolated (v : Option Color) (g : Gap) :
    ∃ a, Extension a (v :: g.vertices) a := by
  have h : ∃ a b : Color, a ≠ b ∧ v ≠ some a ∧ v ≠ some b := by
    cases v with
    | none => exact ⟨0, 1, by decide, by simp, by simp⟩
    | some c =>
      obtain ⟨a, hac, _⟩ := third c c
      obtain ⟨b, hba, hbc⟩ := third a c
      exact ⟨a, b, hba.symm, by simpa using hac.symm, by simpa using hbc.symm⟩
  obtain ⟨a, b, hab, h1, h2⟩ := h
  exact ⟨a, .cons hab h1 h2 ((gap_iff _ _ _).mpr (.inl hab.symm))⟩

end Kostochka.Path

end


section -- DegreeFourLayout

/- Marked pairs and the auxiliary matching on a factor cycle (Kostochka, §3).
Tags are true on the side assigned to the factor and false on the opposite side.
-/

namespace Kostochka.Four

variable {V : Type}

/-- Consecutive unmarked endpoints enclose isolated marked vertices. -/
inductive VertexGap (V : Type) where
  | one (v : V)
  | extra (v : V) (s : VertexGap V)
  | mark (v w : V) (s : VertexGap V)

def VertexGap.tags : VertexGap V → List (V × Bool)
  | .one v => [(v,false)]
  | .extra v s => (v,false) :: s.tags
  | .mark v w s => (v,false) :: (w,true) :: s.tags

def VertexGap.colors (c : V → Path.Color) : VertexGap V → Path.Gap
  | .one _ => .one
  | .extra _ s => .extra (s.colors c)
  | .mark _ w s => .mark (c w) (s.colors c)

def paint (c : V → Path.Color) (x : V × Bool) : Option Path.Color := if x.2 then some (c x.1) else none

theorem VertexGap.paint_tags (c : V → Path.Color) (s : VertexGap V) :
    s.tags.map (paint c) = (s.colors c).vertices := by
  induction s <;> simp_all [tags, paint, colors, Path.Gap.vertices]

abbrev PairV (V : Type) := V × V
abbrev Block (V : Type) := VertexGap V × PairV V

def pairTags (p : PairV V) : List (V × Bool) := [(p.1,true),(p.2,true)]

def restTags (last : VertexGap V) : List (Block V) → List (V × Bool)
  | [] => last.tags
  | (g,p) :: bs => g.tags ++ (pairTags p ++ restTags last bs)

/-- In the paired case the initial pair is followed by further pairs and a final
wraparound gap. The isolated case cuts the cycle at an arbitrary isolated marked
vertex (or at an unmarked vertex if all tags are false). -/
inductive Layout (V : Type) where
  | isolated (v : V × Bool) (s : VertexGap V)
  | paired (p : PairV V) (bs : List (Block V)) (last : VertexGap V)

def Layout.tags : Layout V → List (V × Bool)
  | .isolated v s => v :: s.tags
  | .paired p bs last => pairTags p ++ restTags last bs

def Layout.pairs : Layout V → List (PairV V)
  | .isolated _ _ => []
  | .paired p bs _ => p :: bs.map Prod.snd

/-- The added matching joins the left endpoint of each marked pair to the right
endpoint of the next marked pair, with the last joined back to the first. -/
def mateList (closing : V) (left : V) : List (Block V) → List (PairV V)
  | [] => [(left,closing)]
  | (_, (a,b)) :: bs => (left,b) :: mateList closing a bs

def Layout.mates : Layout V → List (PairV V)
  | .isolated _ _ => []
  | .paired p bs _ => mateList p.2 p.1 bs

def ends (ps : List (PairV V)) : List V := ps.flatMap fun p => [p.1,p.2]

private theorem mates_perm (r l : V) (bs : List (Block V)) :
    (ends (mateList r l bs)).Perm (l :: r :: ends (bs.map Prod.snd)) := by
  induction bs generalizing l with
  | nil => exact .refl _
  | cons b bs ih =>
    rcases b with ⟨g,u,v⟩
    change (l :: v :: ends (mateList r u bs)).Perm (l :: r :: u :: v :: ends (bs.map Prod.snd))
    apply List.Perm.cons
    refine ((ih u).cons v).trans ?_
    exact ((List.Perm.swap _ _ _).cons _).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons _))

theorem Layout.ends_mates_perm_pairs (L : Layout V) : (ends L.mates).Perm (ends L.pairs) := by
  cases L with
  | isolated => exact .refl _
  | paired p bs last => exact mates_perm p.2 p.1 bs

private theorem pairEnds_sublist (last : VertexGap V) (bs : List (Block V)) :
    (ends (bs.map Prod.snd)).Sublist ((restTags last bs).map Prod.fst) := by
  induction bs with
  | nil => exact List.nil_sublist _
  | cons b bs ih =>
    obtain ⟨g,u,v⟩ := b
    simp only [restTags, pairTags, List.map_append, List.map_cons, List.map_nil]
    change (u :: v :: ends (bs.map Prod.snd)).Sublist (g.tags.map Prod.fst ++ (u :: v :: (restTags last bs).map Prod.fst))
    exact (ih.cons_cons v |>.cons_cons u).trans (List.sublist_append_right _ _)

theorem Layout.mates_nodup (L : Layout V) (hn : (L.tags.map Prod.fst).Nodup) : (ends L.mates).Nodup := by
  cases L with
  | isolated _ _ => exact List.nodup_nil
  | paired p bs last =>
    apply (mates_perm p.2 p.1 bs).nodup_iff.mpr
    exact hn.sublist ((pairEnds_sublist last bs).cons_cons p.2 |>.cons_cons p.1)

theorem Layout.mate_mem (L : Layout V) {x : V} (hx : x ∈ ends L.mates) : x ∈ L.tags.map Prod.fst := by
  cases L with
  | isolated _ _ => simp [Layout.mates, ends] at hx
  | paired p bs last =>
    exact ((pairEnds_sublist last bs).cons_cons p.2 |>.cons_cons p.1).subset ((mates_perm p.2 p.1 bs).mem_iff.mp hx)

private theorem pair_subword_rest {q : PairV V} (bs : List (Block V)) (last : VertexGap V)
    (hq : q ∈ bs.map Prod.snd) : ∃ a b, restTags last bs = a ++ pairTags q ++ b := by
  induction bs with
  | nil => simp at hq
  | cons head bs ih =>
    rcases head with ⟨g,p⟩
    rcases List.mem_cons.mp hq with rfl | h
    · exact ⟨g.tags, restTags last bs, by simp [restTags,List.append_assoc]⟩
    · obtain ⟨a,b,he⟩ := ih h
      exact ⟨g.tags ++ pairTags p ++ a,b,by simp [restTags,he,List.append_assoc]⟩

theorem Layout.pair_subword {q : PairV V} (L : Layout V) (hq : q ∈ L.pairs) :
    ∃ a b, L.tags = a ++ pairTags q ++ b := by
  cases L with
  | isolated _ _ => simp [Layout.pairs] at hq
  | paired p bs last =>
    rcases List.mem_cons.mp hq with rfl | h
    · exact ⟨[],restTags last bs,rfl⟩
    · obtain ⟨a,b,he⟩ := pair_subword_rest bs last h
      exact ⟨pairTags p ++ a,b,by simp [Layout.tags,he,List.append_assoc]⟩

/-- One pair boundary according to Lemma 3. If its endpoint colors agree, either
a doubled unmarked separator or a repeated prescribed color in the gap suffices. -/
def allows (c : V → Path.Color) (g : VertexGap V) (x y : V) : Prop :=
  c x ≠ c y ∨ (g.colors c).resets (c x)

/-- A prescribed vertex of the boundary color permits the exception in Lemma 3(c). -/
theorem allows_of_inner_color (c : V → Path.Color) (g : VertexGap V) (x y z : V)
    (hz : (z,true) ∈ g.tags) (hc : c z = c x) : allows c g x y := by
  apply Or.inr
  induction g with
  | one => simp [VertexGap.tags] at hz
  | extra => trivial
  | mark u v s ih =>
    change c x = c v ∨ (s.colors c).resets (c x)
    rcases (by simpa [VertexGap.tags] using hz : z = v ∨ (z,true) ∈ s.tags) with rfl | hm
    · exact .inl hc.symm
    · exact .inr (ih hm)

/-- Two consecutive unmarked vertices anywhere in the gap permit Lemma 3(b). -/
def VertexGap.hasDouble : VertexGap V → Prop
  | .one _ => False
  | .extra _ _ => True
  | .mark _ _ rest => rest.hasDouble

private def doubleIn (xs : List (V × Bool)) : Prop :=
  ∃ a u v b, xs = a ++ (u,false) :: (v,false) :: b

private theorem doubleIn_cons {z : V × Bool} {xs : List (V × Bool)} :
    doubleIn (z :: xs) ↔ (z.2 = false ∧ ∃ v b, xs = (v,false) :: b) ∨ doubleIn xs := by
  constructor
  · rintro ⟨a,u,v,b,h⟩
    cases a with
    | nil =>
      obtain ⟨hz,hx⟩ := List.cons.inj h
      exact .inl ⟨hz ▸ rfl,v,b,hx⟩
    | cons w a =>
      exact .inr ⟨a,u,v,b,(List.cons.inj h).2⟩
  · rintro (⟨hz,v,b,rfl⟩ | ⟨a,u,v,b,rfl⟩)
    · exact ⟨[], z.1, v, b, by cases z; simp_all⟩
    · exact ⟨z::a,u,v,b,rfl⟩

theorem VertexGap.hasDouble_of_subword (g : VertexGap V) (a : List (V × Bool)) (u v : V)
    (b : List (V × Bool)) (sub : g.tags = a ++ (u,false) :: (v,false) :: b) : g.hasDouble := by
  have h : doubleIn g.tags := ⟨a,u,v,b,sub⟩
  clear sub
  induction g with
  | one w =>
    obtain ⟨p,u,v,s,h⟩ := h
    have hl := congrArg List.length h
    simp [tags] at hl
    omega
  | extra => trivial
  | mark x y g ih =>
    change doubleIn ((x,false) :: (y,true) :: g.tags) at h
    rcases doubleIn_cons.mp h with ⟨_,u,b,hu⟩ | h
    · simp at hu
    · exact ih ((doubleIn_cons.mp h).resolve_left (by simp))

theorem allows_of_double (c : V → Path.Color) (g : VertexGap V) (x y : V)
    (hd : g.hasDouble) : allows c g x y := by
  apply Or.inr
  induction g with
  | one => exact hd.elim
  | extra => trivial
  | mark u v g ih => exact Or.inr (ih hd)

def accepts (c : V → Path.Color) (closing left : V) (last : VertexGap V) : List (Block V) → Prop
  | [] => allows c last left closing
  | (g,p) :: bs => allows c g left p.2 ∧ accepts c closing p.1 last bs

def Layout.accepts (L : Layout V) (c : V → Path.Color) : Prop :=
  match L with
  | .isolated _ _ => True
  | .paired p bs last => Four.accepts c p.2 p.1 last bs

private theorem chain_extension (c : V → Path.Color) (r l : V) (bs : List (Block V)) (last : VertexGap V)
    (internal : ∀ p ∈ bs.map Prod.snd, c p.1 ≠ c p.2)
    (accepted : accepts c r l last bs) :
    Path.Extension (c l) ((restTags last bs).map (paint c)) (c r) := by
  induction bs generalizing l with
  | nil =>
    rw [restTags, VertexGap.paint_tags]
    exact (Path.gap_iff _ _ _).mpr accepted
  | cons h bs ih =>
    rcases h with ⟨g,u,v⟩
    have uv : c u ≠ c v := internal (u,v) (by simp)
    rw [restTags, List.map_append, List.map_append, VertexGap.paint_tags]
    apply Path.append ((Path.gap_iff _ _ _).mpr accepted.1)
    apply Path.append (Path.pair_extension ⟨c u, c v, uv⟩)
    exact ih u (fun p hp => internal p (by simp [hp])) accepted.2

/-- A coloring of the marked vertices, proper on both their original adjacent
pairs and the added matching, extends to every edge of this cyclic layout. -/
theorem Layout.extension_of_accepts (L : Layout V) (c : V → Path.Color)
    (pairs : ∀ p ∈ L.pairs, c p.1 ≠ c p.2) (accepted : L.accepts c) :
    ∃ a, Path.Extension a (L.tags.map (paint c)) a := by
  cases L with
  | isolated v s =>
    change ∃ a, Path.Extension a (paint c v :: s.tags.map (paint c)) a
    rw [VertexGap.paint_tags]
    exact Path.cycle_isolated _ _
  | paired p bs last =>
    have uv := pairs p (by simp [Layout.pairs])
    refine ⟨c p.2, ?_⟩
    change Path.Extension _ ((pairTags p ++ restTags last bs).map _) _
    rw [List.map_append]
    exact Path.append (Path.pair_extension ⟨_, _, uv⟩) (chain_extension c _ _ _ _
      (fun q hq => pairs q (by simp [Layout.pairs,hq])) accepted)

private theorem accepts_of_mates (c : V → Path.Color) (r l : V) (last : VertexGap V) (bs : List (Block V))
    (mates : ∀ p ∈ mateList r l bs, c p.1 ≠ c p.2) : accepts c r l last bs := by
  induction bs generalizing l with
  | nil => exact Or.inl (mates (l,r) (by simp [mateList]))
  | cons h bs ih =>
    obtain ⟨g,u,v⟩ := h
    exact ⟨Or.inl (mates (l,v) (by simp [mateList])), ih u (fun q hq => mates q (by simp [mateList,hq]))⟩

theorem Layout.extension (L : Layout V) (c : V → Path.Color)
    (pairs : ∀ p ∈ L.pairs, c p.1 ≠ c p.2)
    (mates : ∀ p ∈ L.mates, c p.1 ≠ c p.2) :
    ∃ a, Path.Extension a (L.tags.map (paint c)) a := by
  apply L.extension_of_accepts c pairs
  cases L with
  | isolated => trivial
  | paired p bs last => exact accepts_of_mates c _ _ last bs mates

end Kostochka.Four

end


section -- DegreeFourCycles

/- Cyclic coordinates for the two 2-factors in Kostochka's Theorem 1. -/

namespace Kostochka.Four

open SimpleGraph

variable {V : Type} {F : SimpleGraph V}

/-- Cyclic coordinates on all components of a finite simple 2-factor. -/
structure Atlas (F : SimpleGraph V) where
  size : F.ConnectedComponent → ℕ
  three : ∀ j, 3 ≤ size j
  vertices : (Σ j, Fin (size j)) ≃ V
  adj : ∀ j i, F.Adj (vertices ⟨j,i⟩) (vertices ⟨j,finRotate (size j) i⟩)

theorem rotate_val {n : ℕ} (hn : 3 ≤ n) (i : Fin n) :
    (finRotate n i).val = (i.val + 1) % n := by
  have : NeZero n := ⟨by omega⟩
  rw [finRotate_apply]
  change (i.val + 1 % n) % n = _
  rw [Nat.mod_eq_of_lt (show 1 < n by omega)]

/-- Enumerate the vertices of a component by its cycle walk. -/
private theorem coords [Fintype V] [DecidableRel F.Adj] (reg : ∀ v, F.degree v = 2)
    (j : F.ConnectedComponent) : ∃ n : ℕ, 3 ≤ n ∧
      ∃ f : Fin n ≃ {x // F.connectedComponentMk x = j}, ∀ i, F.Adj (f i).val (f (finRotate n i)).val := by
  classical
  have cyc : F.IsCycles := by
    intro v hv
    rw [← reg v, ← F.card_neighborSet_eq_degree]
    exact Nat.card_eq_fintype_card
  obtain ⟨v, hv⟩ := j.nonempty_supp
  have hn : (F.neighborSet v).Nonempty := (F.degree_pos_iff_exists_adj _).mp (by simp [reg])
  obtain ⟨p, hp, hc⟩ := cyc.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp hv hn
  have three := hp.three_le_length
  let fv : Fin p.length → {x // F.connectedComponentMk x = j} := fun i =>
    ⟨p.getVert i.val, (j.mem_supp_iff _).mp (hc ▸ (p.mem_verts_toSubgraph.mpr (p.getVert_mem_support _)))⟩
  have bi : Function.Bijective fv := by
    constructor
    · intro x y h
      apply Fin.ext
      exact hp.getVert_injOn' (show x.val ≤ p.length-1 by omega)
        (show y.val ≤ p.length-1 by omega) (congrArg Subtype.val h)
    · rintro ⟨x,hx⟩
      have mem : x ∈ p.support := p.mem_verts_toSubgraph.mp (hc ▸ (j.mem_supp_iff _).mpr hx)
      obtain ⟨i, hi, hle⟩ := Walk.mem_support_iff_exists_getVert.mp mem
      by_cases hlast : i = p.length
      · subst i
        have he : v = x := by simpa using hi
        refine ⟨⟨0, by omega⟩, Subtype.ext ?_⟩
        exact (p.getVert_zero).trans he
      · exact ⟨⟨i, by omega⟩, Subtype.ext hi⟩
  refine ⟨p.length, three, Equiv.ofBijective fv bi, fun i => ?_⟩
  change F.Adj (p.getVert i.val) (p.getVert (finRotate p.length i).val)
  rw [rotate_val three]
  have ha := p.adj_getVert_succ i.isLt
  by_cases he : i.val + 1 = p.length
  · simpa [he] using ha
  · rwa [Nat.mod_eq_of_lt (by omega)]

noncomputable def atlasOfRegular [Fintype V] [DecidableRel F.Adj] (reg : ∀ v, F.degree v = 2) :
    Atlas F := by
  classical
  choose n hn e ha using coords reg
  refine ⟨n, hn, (Equiv.sigmaCongrRight e).trans (Equiv.sigmaFiberEquiv F.connectedComponentMk), ?_⟩
  exact ha

/-- Successor around the oriented cycles of the factor. -/
noncomputable def Atlas.next (A : Atlas F) : Equiv.Perm V :=
  A.vertices.symm.trans ((Equiv.sigmaCongrRight (fun j => finRotate (A.size j))).trans A.vertices)

theorem Atlas.next_coordinate (A : Atlas F) (j) (i : Fin (A.size j)) :
    A.next (A.vertices ⟨j,i⟩) = A.vertices ⟨j,finRotate _ i⟩ := by simp [Atlas.next]

theorem Atlas.adj_next (A : Atlas F) (v : V) : F.Adj v (A.next v) := by
  obtain ⟨⟨j,i⟩,rfl⟩ := A.vertices.surjective v
  rw [A.next_coordinate]
  exact A.adj j i

theorem Atlas.no_two_cycle (A : Atlas F) (v : V) : A.next (A.next v) ≠ v := by
  obtain ⟨⟨j,i⟩,rfl⟩ := A.vertices.surjective v
  rw [A.next_coordinate, A.next_coordinate]
  intro eq
  have h : finRotate (A.size j) (finRotate (A.size j) i) = i := by
    simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using A.vertices.injective eq
  have he := congrArg Fin.val h
  have hn := A.three j
  simp only [rotate_val hn] at he
  by_cases last : i.val+1=A.size j
  · simp [last, Nat.mod_eq_of_lt (show 1 < A.size j by omega)] at he
    omega
  · rw [Nat.mod_eq_of_lt (show i.val+1 < A.size j by omega)] at he
    by_cases penult : i.val+1+1=A.size j
    · rw [penult, Nat.mod_self] at he; omega
    · rw [Nat.mod_eq_of_lt (by omega)] at he; omega

/-- When all degrees are two, every factor edge leaves exactly one vertex in the
chosen orientation. -/
noncomputable def Atlas.outgoing (A : Atlas F) (v : V) : F.edgeSet :=
  ⟨s(v, A.next v), A.adj_next v⟩

private theorem Atlas.neighbor_cases (A : Atlas F) (hc : F.IsCycles) {v w : V} (h : F.Adj v w) :
    w = A.next v ∨ A.next w = v := by
  by_cases hf : w = A.next v
  · exact .inl hf
  right
  have hprev : F.Adj v (A.next.symm v) := by simpa using (A.adj_next (A.next.symm v)).symm
  have hne : A.next v ≠ A.next.symm v := by
    intro e; exact A.no_two_cycle v ((congrArg A.next e).trans (A.next.apply_symm_apply v))
  obtain ⟨z, _, unique⟩ := hc.existsUnique_ne_adj (A.adj_next v)
  have hw := unique w ⟨Ne.symm hf, h⟩
  have hy := unique (A.next.symm v) ⟨hne, hprev⟩
  exact (congrArg A.next (hw.trans hy.symm)).trans (A.next.apply_symm_apply v)

noncomputable def Atlas.edgeEquiv (A : Atlas F) (hc : F.IsCycles) : V ≃ F.edgeSet := by
  apply Equiv.ofBijective A.outgoing
  constructor
  · intro x y h
    rcases Sym2.eq_iff.mp (congrArg Subtype.val h) with ⟨he, _⟩ | ⟨he, hf⟩
    · exact he
    · exact (A.no_two_cycle y ((congrArg A.next he.symm).trans hf)).elim
  · rintro ⟨e,he⟩
    induction e using Sym2.ind with
    | _ x y =>
      rcases A.neighbor_cases hc he with h | h
      · exact ⟨x, Subtype.ext (Sym2.eq_iff.mpr (.inl ⟨rfl, h.symm⟩))⟩
      · exact ⟨y, Subtype.ext (Sym2.eq_iff.mpr (.inr ⟨rfl, h⟩))⟩

/-- Convert consecutive edge colors around every factor cycle to an edge coloring
of the graph, retaining the avoided colors at precolored vertices. -/
theorem Atlas.edgeColors (A : Atlas F) (hc : F.IsCycles) (label : V → Option (Fin 3))
    (f : V → Fin 3) (hf : ∀ v, f v ≠ f (A.next v) ∧ label v ≠ some (f v) ∧
      label v ≠ some (f (A.next v))) :
    ∃ color : F.edgeSet → Fin 3,
      (∀ e e', e ≠ e' → (∃ v, v ∈ e.val ∧ v ∈ e'.val) → color e ≠ color e') ∧
      ∀ v e, v ∈ e.val → label v ≠ some (color e) := by
  let E := A.edgeEquiv hc
  let color (e : F.edgeSet) := f (A.next (E.symm e))
  have edge (u : V) : (E u).val = s(u, A.next u) := rfl
  have co (u : V) : color (E u) = f (A.next u) := by simp [color]
  refine ⟨color, ?_, ?_⟩
  · intro e e' hne ⟨v,hv,hv'⟩
    obtain ⟨u,rfl⟩ := E.surjective e
    obtain ⟨w,rfl⟩ := E.surjective e'
    rw [co, co]
    rw [edge, Sym2.mem_iff] at hv hv'
    rcases hv with rfl | rfl <;> rcases hv' with he | he
    · exact (hne (congrArg E he)).elim
    · rw [← he]; exact (hf _).1.symm
    · rw [← he]; exact (hf _).1
    · exact (hne (congrArg E (A.next.injective he))).elim
  · intro v e hv
    obtain ⟨u,rfl⟩ := E.surjective e
    rw [co, edge, Sym2.mem_iff] at *
    rcases hv with rfl | rfl
    · exact (hf _).2.2
    · exact (hf _).2.1

end Kostochka.Four

end


section -- DegreeFourMatching

/- Coloring the auxiliary graph in the last step of Kostochka's Theorem 1.
The paths in a factor add a matching to one induced forest. The union admits
three colors by a greedy coloring in the forest removal ordering. -/

namespace Kostochka.Cut

open SimpleGraph Finset

variable {V : Type} [Fintype V] [DecidableEq V]

/-- An ordered greedy coloring. Equal ranks count as predecessors, so the ordering
need not be injective. -/
theorem color_of_rank (H : SimpleGraph V) [DecidableRel H.Adj] (rank : V → ℕ)
    (k : ℕ) (hr : ∀ v, ((H.neighborFinset v).filter fun w => rank w ≤ rank v).card < k)
    (hk : 0 < k) : ∃ c : V → Fin k, ∀ u v, H.Adj u v → c u ≠ c v := by
  classical
  suffices build : ∀ s : Finset V, ∃ c : V → Fin k,
      ∀ u ∈ s, ∀ v ∈ s, H.Adj u v → c u ≠ c v by
    obtain ⟨c, hc⟩ := build univ
    exact ⟨c, fun u v => hc u (mem_univ u) v (mem_univ v)⟩
  intro s
  induction s using Finset.strongInductionOn
  rename_i s ih
  ·
    by_cases hs : s.Nonempty
    · obtain ⟨u, hu, hmax⟩ := s.exists_max_image rank hs
      obtain ⟨c, hc⟩ := ih (s.erase u) (Finset.erase_ssubset hu)
      let earlier := (H.neighborFinset u).filter fun w => rank w ≤ rank u
      have lt : (earlier.image c).card < (univ : Finset (Fin k)).card := by
        simpa using (Finset.card_image_le (f := c) (s := earlier)).trans_lt (hr u)
      obtain ⟨a, _, ha⟩ := exists_mem_notMem_of_card_lt_card lt
      let d (v : V) := if v = u then a else c v
      have avoid (v : V) (hv : v ∈ s) (hadj : H.Adj u v) : a ≠ c v := by
        intro eq
        exact ha (eq ▸ mem_image_of_mem c (mem_filter.mpr
          ⟨(H.mem_neighborFinset _ _).mpr hadj, hmax v hv⟩ : v ∈ earlier))
      refine ⟨d, fun x hx y hy hxy => ?_⟩
      by_cases hxu : x = u
      · subst x
        simpa [d, hxy.ne.symm] using avoid y hy hxy
      · by_cases hyu : y = u
        · subst y; simpa [d, hxu] using (avoid x hx hxy.symm).symm
        · simpa [d, hxu, hyu] using hc x (mem_erase.mpr ⟨hxu, hx⟩) y (mem_erase.mpr ⟨hyu, hy⟩) hxy
    · exact ⟨fun _ => ⟨0, hk⟩, by simp [Finset.not_nonempty_iff_eq_empty.mp hs]⟩

/-- Any graph obtained by adding a matching to same-side edges of an ordered forest
has a proper 3-coloring. The hypothesis on `extra` permits a submatching; the
colors can be used for the vertices of either factor in Kostochka's theorem. -/
theorem forest_add_matching (G extra H : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel extra.Adj] [DecidableRel H.Adj] (p : V → Bool)
    (hforest : ForestCut G p) (hmatch : ∀ u, extra.degree u ≤ 1)
    (cover : ∀ u v, H.Adj u v → (G.Adj u v ∧ p u = p v) ∨ extra.Adj u v) :
    ∃ c : V → Fin 3, ∀ u v, H.Adj u v → c u ≠ c v := by
  obtain ⟨rank, hr⟩ := hforest
  apply color_of_rank H rank 3 _ (by decide)
  intro u
  let tree := (G.neighborFinset u).filter (fun w => p w = p u ∧ rank w ≤ rank u)
  have sub : ((H.neighborFinset u).filter (fun w => rank w ≤ rank u)) ⊆ tree ∪ extra.neighborFinset u := by
    intro v hv
    obtain ⟨hadj, hle⟩ := Finset.mem_filter.mp hv
    rcases cover _ _ ((H.mem_neighborFinset _ _).mp hadj) with ⟨h, col⟩ | h
    · exact mem_union_left _ (mem_filter.mpr ⟨(G.mem_neighborFinset _ _).mpr h, col.symm, hle⟩)
    · exact mem_union_right _ ((extra.mem_neighborFinset _ _).mpr h)
  have card := (card_le_card sub).trans (card_union_le _ _)
  have ht : tree.card ≤ 1 := hr u
  rw [extra.card_neighborFinset_eq_degree] at card
  have hm := hmatch u
  omega

end Kostochka.Cut

end


section -- DegreeFourMates

/- Construct the auxiliary matching from the cyclic words and color all the marked pairs. -/

namespace Kostochka.Four

open SimpleGraph Finset

variable {V : Type}

def Joins (ps : List (PairV V)) (x y : V) : Prop := (x,y) ∈ ps ∨ (y,x) ∈ ps

private theorem joins_mem {ps : List (PairV V)} {x y : V} (h : Joins ps x y) : x ∈ ends ps := by
  rcases h with h | h
  · exact List.mem_flatMap.mpr ⟨(x,y),h,by simp⟩
  · exact List.mem_flatMap.mpr ⟨(y,x),h,by simp⟩

private theorem joins_cons {p : PairV V} {ps} {x y : V} :
    Joins (p :: ps) x y ↔ (p = (x,y) ∨ p = (y,x)) ∨ Joins ps x y := by
  simp only [Joins, List.mem_cons]; tauto

theorem joins_irrefl {ps : List (PairV V)} (h : (ends ps).Nodup) (u : V) : ¬Joins ps u u := by
  induction ps with
  | nil => simp [Joins]
  | cons p ps ih =>
    rcases p with ⟨x,y⟩
    change (x :: y :: ends ps).Nodup at h
    obtain ⟨hx, hy, ht⟩ := List.nodup_cons.mp h |>.imp_right List.nodup_cons.mp
    intro he
    rcases joins_cons.mp he with (hp|hp) | ht'
    · cases hp; exact hx (by simp)
    · cases hp; exact hx (by simp)
    · exact ih ht ht'

theorem joins_unique {ps : List (PairV V)} (h : (ends ps).Nodup) {u x y : V}
    (hx : Joins ps u x) (hy : Joins ps u y) : x = y := by
  induction ps with
  | nil => simp [Joins] at hx
  | cons p ps ih =>
    rcases p with ⟨a,b⟩
    change (a :: b :: ends ps).Nodup at h
    have ha : a ∉ ends ps := fun h' => (List.nodup_cons.mp h).1 (List.mem_cons_of_mem _ h')
    have hb := (List.nodup_cons.mp (List.nodup_cons.mp h).2).1
    have ht := (List.nodup_cons.mp (List.nodup_cons.mp h).2).2
    rcases joins_cons.mp hx with (hx|hx) | hx <;> rcases joins_cons.mp hy with (hy|hy) | hy
    all_goals first | exact ih ht hx hy | cases hx <;> cases hy <;> rfl |
      (have huv := joins_mem hy; cases hx; grind) | (have huv := joins_mem hx; cases hy; grind)

variable {J : Type} (L : J → Layout V)

/-- The disjoint union of the matchings constructed inside the cycle components. -/
def mateGraph (nodup : ∀ j, ((L j).tags.map Prod.fst).Nodup) : SimpleGraph V where
  Adj x y := ∃ j, Joins (L j).mates x y
  symm.symm _ _ := fun ⟨j,h⟩ => ⟨j,Or.symm h⟩
  loopless.irrefl x := fun ⟨j,h⟩ => joins_irrefl ((L j).mates_nodup (nodup j)) x h

theorem mateGraph_degree [Fintype V] [DecidableEq V]
    (nodup : ∀ j, ((L j).tags.map Prod.fst).Nodup)
    (separate : ∀ {j k : J} {u : V}, u ∈ (L j).tags.map Prod.fst → u ∈ (L k).tags.map Prod.fst → j = k)
    [DecidableRel (mateGraph L nodup).Adj] (u : V) : (mateGraph L nodup).degree u ≤ 1 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  refine Finset.card_le_one.mpr (fun x hx y hy => ?_)
  obtain ⟨j,hx⟩ := ((mateGraph L nodup).mem_neighborFinset _ _).mp hx
  obtain ⟨k,hy⟩ := ((mateGraph L nodup).mem_neighborFinset _ _).mp hy
  have eq := separate ((L j).mate_mem (joins_mem hx)) ((L k).mate_mem (joins_mem hy))
  subst k
  exact joins_unique ((L j).mates_nodup (nodup j)) hx hy

/-- Cutting a cycle at a different edge only rotates the vertex list. -/
theorem map_isRotated {α β : Type} (f : α → β) {xs ys : List α} (h : xs.IsRotated ys) :
    (xs.map f).IsRotated (ys.map f) := by
  obtain ⟨k,rfl⟩ := h
  exact ⟨k,by simp⟩

variable {F : SimpleGraph V}

def Atlas.word (A : Atlas F) (side : V → Bool) (b : Bool) (j : F.ConnectedComponent) : List (V × Bool) :=
  List.ofFn fun i => let v := A.vertices ⟨j,i⟩; (v, decide (side v = b))

theorem Atlas.word_nodup (A : Atlas F) (p : V → Bool) (b j) : ((A.word p b j).map Prod.fst).Nodup := by
  simp only [Atlas.word, List.map_ofFn, Function.comp_def]
  apply List.nodup_ofFn_ofInjective
  intro x y h
  exact eq_of_heq ((Sigma.mk.inj_iff.mp (A.vertices.injective h)).2)

theorem Atlas.word_separate (A : Atlas F) (p : V → Bool) (b) {j k : F.ConnectedComponent} {u : V}
    (hj : u ∈ (A.word p b j).map Prod.fst) (hk : u ∈ (A.word p b k).map Prod.fst) : j = k := by
  simp only [Atlas.word, List.map_ofFn, Function.comp_def, List.mem_ofFn] at hj hk
  obtain ⟨i,hi⟩ := hj
  obtain ⟨l,hl⟩ := hk
  exact congrArg Sigma.fst (A.vertices.injective (hi.trans hl.symm))

end Kostochka.Four

end


section -- DegreeFour

/- The disjoint-palette construction at the end of Section 3 of A. V. Kostochka,
*The total chromatic number of any multigraph with maximum degree five is at most seven*.
-/

namespace Kostochka.Four

open SimpleGraph

variable {V : Type} (G : SimpleGraph V)

/-- A palette colors the vertices of its side of the cut and the edges of its
factor. Color values outside that side or factor are ignored. -/
structure Palette (side : V → Bool) (factor : G.edgeSet → Bool) (b : Bool) where
  vertices : V → Fin 3
  edges : G.edgeSet → Fin 3
  properVertices : ∀ u v, side u = b → side v = b → G.Adj u v → vertices u ≠ vertices v
  properEdges : ∀ e f, factor e = b → factor f = b → e ≠ f →
    (∃ x, x ∈ e.val ∧ x ∈ f.val) → edges e ≠ edges f
  properIncidence : ∀ u e, side u = b → factor e = b → u ∈ e.val → vertices u ≠ edges e

private def place (b : Bool) (i : Fin 3) : Fin 6 :=
  if b then ⟨3 + i.val, by omega⟩ else ⟨i.val, by omega⟩

private theorem place_eq {a b : Bool} {i j : Fin 3} (h : place a i = place b j) :
    a = b ∧ i = j := by
  have hv := congrArg Fin.val h
  cases a <;> cases b <;> simp_all [place, Fin.ext_iff] <;> omega

/-- Two independent palettes of three colors give the required six-color bound. -/
theorem six_of_palettes (side : V → Bool) (factor : G.edgeSet → Bool)
    (p : ∀ b, Palette G side factor b) : G.totalChromaticNumber ≤ 6 := by
  apply Nat.sInf_le
  let v (x : V) := place (side x) ((p (side x)).vertices x)
  let e (x : G.edgeSet) := place (factor x) ((p (factor x)).edges x)
  refine ⟨Sum.elim v e, ?_, ?_, ?_⟩
  · intro x y hadj h
    obtain ⟨hs, eq⟩ := place_eq (show v x = v y from h)
    change side x = side y at hs
    exact (p (side y)).properVertices x y hs rfl hadj ((congrArg (fun b => (p b).vertices x) hs).symm.trans eq)
  · intro x y hne hmeet h
    obtain ⟨hs, eq⟩ := place_eq (show e x = e y from h)
    change factor x = factor y at hs
    exact (p (factor y)).properEdges x y hs rfl hne hmeet ((congrArg (fun b => (p b).edges x) hs).symm.trans eq)
  · intro x y hmem h
    obtain ⟨hs, eq⟩ := place_eq (show v x = e y from h)
    change side x = factor y at hs
    exact (p (factor y)).properIncidence x y hs rfl hmem ((congrArg (fun b => (p b).vertices x) hs).symm.trans eq)

end Kostochka.Four

end


section -- DegreeFourPalette

/- The factor palettes in Kostochka's proof of the six-color theorem. -/

namespace Kostochka.Four

open SimpleGraph

variable {V : Type} {F : SimpleGraph V}

private theorem Atlas.rotated_adj (A : Atlas F) (p : V → Bool) (b j k t)
    (ht : t+1 < ((A.word p b j).rotate k).length) :
    F.Adj (((A.word p b j).rotate k)[t]'(by omega)).1 (((A.word p b j).rotate k)[t+1]).1 := by
  simp only [List.getElem_rotate, Atlas.word, List.length_ofFn, List.getElem_ofFn]
  let i : Fin (A.size j) := ⟨(t+k) % A.size j, Nat.mod_lt _ (by have := A.three j; omega)⟩
  have e : (finRotate (A.size j) i).val = (t+1+k) % A.size j := by
    rw [rotate_val (A.three j)]
    simp only [i, Nat.mod_add_mod]
    congr 1
    omega
  have hidx : finRotate (A.size j) i = ⟨(t+1+k) % A.size j, Nat.mod_lt _ (by have := A.three j; omega)⟩ := Fin.ext e
  exact hidx ▸ A.adj j i

private theorem Atlas.marked (A : Atlas F) (p : V → Bool) (b j) {x : V}
    (h : (x,true) ∈ A.word p b j) : p x = b := by
  obtain ⟨i,hi⟩ := List.mem_ofFn.mp h
  change (_, decide (p (A.vertices ⟨j,i⟩) = b)) = (x,true) at hi
  obtain ⟨hv,hb⟩ := Prod.mk.inj hi
  simpa [← hv] using hb

theorem Atlas.original_pair (A : Atlas F) (side : V → Bool) (b j)
    (L : Layout V) (hr : (A.word side b j).IsRotated L.tags) {q : PairV V} (hq : q ∈ L.pairs) :
    F.Adj q.1 q.2 ∧ side q.1 = b ∧ side q.2 = b := by
  obtain ⟨a,d,sub⟩ := L.pair_subword hq
  have m₁ : (q.1,true) ∈ L.tags := by simp [sub,pairTags]
  have m₂ : (q.2,true) ∈ L.tags := by simp [sub,pairTags]
  refine ⟨?_, A.marked side b j (hr.mem_iff.mpr m₁), A.marked side b j (hr.mem_iff.mpr m₂)⟩
  obtain ⟨k,hk⟩ := hr
  have he : (A.word side b j).rotate k = a ++ (q.1,true) :: (q.2,true) :: d := by
    simp [hk,sub,pairTags,List.append_assoc]
  have hadj := A.rotated_adj side b j k a.length (by simp [he])
  have extract (w : List (V × Bool)) (heq : w = a ++ (q.1,true) :: (q.2,true) :: d)
      (h : a.length+1 < w.length)
      (ad : F.Adj (w[a.length]'(by omega)).1 (w[a.length+1]).1) : F.Adj q.1 q.2 := by
    subst w
    have hone : a.length.succ - a.length = 1 := by omega
    simpa only [List.getElem_append_right (Nat.le_refl _), List.getElem_append_right (Nat.le_succ _),
      Nat.sub_self, hone, Nat.add_sub_cancel_left, List.getElem_cons_zero, List.getElem_cons_succ] using ad
  exact extract _ he (by simp [he]) hadj

private theorem coords_colors {n : ℕ} (hn : 3 ≤ n) (c : Fin n → Option Path.Color)
    {a} (h : Path.Extension a (List.ofFn c) a) :
    ∃ f : Fin n → Path.Color, ∀ i, f i ≠ f (finRotate n i) ∧
      c i ≠ some (f i) ∧ c i ≠ some (f (finRotate n i)) := by
  obtain ⟨f,h0,hl,hf⟩ := h.edgeColors
  simp only [List.length_ofFn] at hl
  refine ⟨fun i => f i.val, fun i => ?_⟩
  have he : f (finRotate n i).val = f (i.val+1) := by
    rw [rotate_val hn]
    by_cases hlast : i.val+1 = n
    · simp [hlast,h0,hl]
    · rw [Nat.mod_eq_of_lt (by omega)]
  have value : (List.ofFn c)[i.val]'(by simp) = c i := List.getElem_ofFn _
  simpa only [he,value] using hf i.val (by simp)


/-- Edge-color a 2-regular graph from extensions around each of its component cycles. -/
theorem Atlas.avoiding_of_extensions (A : Atlas F) (hc : F.IsCycles) (label : V → Option Path.Color)
    (extending : ∀ j, ∃ a, Path.Extension a (List.ofFn (fun i => label (A.vertices ⟨j,i⟩))) a) :
    ∃ ec : F.edgeSet → Fin 3,
      (∀ e e', e ≠ e' → (∃ v, v ∈ e.val ∧ v ∈ e'.val) → ec e ≠ ec e') ∧
      ∀ v e, v ∈ e.val → label v ≠ some (ec e) := by
  have colors j := (extending j).elim fun _ ha => coords_colors (A.three j) _ ha
  choose f hf using colors
  let vcolor (v : V) := let t := A.vertices.symm v; f t.1 t.2
  have hv (v : V) : vcolor v ≠ vcolor (A.next v) ∧ label v ≠ some (vcolor v) ∧
      label v ≠ some (vcolor (A.next v)) := by
    obtain ⟨⟨j,i⟩,rfl⟩ := A.vertices.surjective v
    have eval (j) (i : Fin (A.size j)) : vcolor (A.vertices ⟨j,i⟩) = f j i := by
      unfold vcolor
      rw [Equiv.symm_apply_apply]
    simpa only [Atlas.next_coordinate, eval] using hf j i
  exact A.edgeColors hc label vcolor hv

structure FactorPalette (G F : SimpleGraph V) (side : V → Bool) (b : Bool) where
  vertices : V → Fin 3
  edges : F.edgeSet → Fin 3
  properVertices : ∀ u v, side u = b → side v = b → G.Adj u v → vertices u ≠ vertices v
  properEdges : ∀ e f, e ≠ f → (∃ x, x ∈ e.val ∧ x ∈ f.val) → edges e ≠ edges f
  properIncidence : ∀ u e, side u = b → u ∈ e.val → vertices u ≠ edges e

private def sameSide (G : SimpleGraph V) (side : V → Bool) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ side u = side v
  symm.symm _ _ h := ⟨h.1.symm,h.2.symm⟩
  loopless.irrefl _ h := h.1.ne rfl

theorem factorPalette_of_layouts [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (side : V → Bool) (b : Bool)
    (forest : Cut.ForestCut G side) (sub : F ≤ G) (hc : F.IsCycles)
    (A : Atlas F) (L : F.ConnectedComponent → Layout V)
    (hr : ∀ j, (A.word side b j).IsRotated (L j).tags) : Nonempty (FactorPalette G F side b) := by
  classical
  have hd j := (map_isRotated Prod.fst (hr j)).nodup_iff.mp (A.word_nodup side b j)
  let M := mateGraph L hd
  have dm u : M.degree u ≤ 1 := by
    apply mateGraph_degree
    intro j k v hj hk
    exact A.word_separate side b ((map_isRotated Prod.fst (hr j)).mem_iff.mpr hj)
      ((map_isRotated Prod.fst (hr k)).mem_iff.mpr hk)
  let H := sameSide G side ⊔ M
  obtain ⟨vc,hvc⟩ := Cut.forest_add_matching G M H side forest dm (fun _ _ h => h)
  let label (v : V) : Option Path.Color := if side v = b then some (vc v) else none
  have ext j : ∃ a, Path.Extension a (List.ofFn (fun i => label (A.vertices ⟨j,i⟩))) a := by
    obtain ⟨a,ha⟩ := (L j).extension vc (fun q hq => by
      obtain ⟨h₁,h₂,h₃⟩ := A.original_pair side b j _ (hr j) hq
      exact hvc _ _ (.inl ⟨sub h₁,h₂.trans h₃.symm⟩)) (fun q hq =>
        hvc _ _ (.inr ⟨j,.inl hq⟩))
    simpa [Atlas.word, List.map_ofFn, Function.comp_def, paint, label] using
      ha.rotate (map_isRotated (paint vc) (hr j).symm)
  obtain ⟨ec,he,hve⟩ := A.avoiding_of_extensions hc label ext
  refine ⟨⟨vc,ec,fun u v hu hv hadj => hvc _ _ (.inl ⟨hadj,hu.trans hv.symm⟩),he,?_⟩⟩
  intro u e hu hmem
  simpa [label, hu] using hve u e hmem

private noncomputable def FactorPalette.lift {G F : SimpleGraph V} {side : V → Bool} {b : Bool}
    (P : FactorPalette G F side b) (factor : G.edgeSet → Bool)
    (contained : ∀ e, factor e = b → e.val ∈ F.edgeSet) : Palette G side factor b := by
  classical
  let edges (e : G.edgeSet) := if h : e.val ∈ F.edgeSet then P.edges ⟨e.val,h⟩ else 0
  refine ⟨P.vertices,edges,P.properVertices,?_,?_⟩
  · intro e f he hf hne hmeet
    have he' := contained e he
    have hf' := contained f hf
    simp only [edges, dif_pos he', dif_pos hf']
    apply P.properEdges _ _ _ hmeet
    exact fun eq => hne (Subtype.ext (congrArg (fun t : F.edgeSet => t.val) eq))
  · intro u e hu he hm
    have he' := contained e he
    simpa only [edges,dif_pos he'] using P.properIncidence u ⟨e.val,he'⟩ hu hm

/-- The two factor palettes use disjoint triples of colors. -/
theorem six_of_factorPalettes (G F₁ F₂ : SimpleGraph V) (side : V → Bool)
    (union : F₁ ⊔ F₂ = G)
    (P : FactorPalette G F₁ side false) (Q : FactorPalette G F₂ side true) :
    G.totalChromaticNumber ≤ 6 := by
  classical
  let factor (e : G.edgeSet) := decide (e.val ∈ F₂.edgeSet)
  apply six_of_palettes G side factor
  intro b
  cases b with
  | false =>
    apply P.lift factor
    intro e he
    have hu : e.val ∈ (F₁ ⊔ F₂).edgeSet := union ▸ e.property
    rw [edgeSet_sup] at hu
    exact hu.resolve_right (by simpa [factor] using he)
  | true =>
    apply Q.lift factor
    intro e he
    simpa [factor] using he

end Kostochka.Four

end


section -- DegreeFourFactors

/- Use the split property of the two factors to exclude three successive marks. -/

namespace Kostochka.Four

open SimpleGraph

variable {V : Type}

def NoMarkedTriple {n : ℕ} (f : Fin n → V × Bool) :=
  ∀ i, ¬ ((f i).2 = true ∧ (f (finRotate n i)).2 = true ∧
    (f (finRotate n (finRotate n i))).2 = true)

private theorem Atlas.noMarkedTriple {F : SimpleGraph V} (A : Atlas F) (side : V → Bool) (b j)
    (split : ∀ u v w, v ≠ w → side u = side v → side u = side w → ¬(F.Adj u v ∧ F.Adj u w)) :
    NoMarkedTriple (fun i : Fin (A.size j) =>
      let v := A.vertices ⟨j,i⟩; (v,decide (side v = b))) := by
  intro i h
  simp only [decide_eq_true_eq] at h
  let x := A.vertices ⟨j,i⟩
  let y := A.next x
  let z := A.next y
  have labels : side x = b ∧ side y = b ∧ side z = b := by
    simpa only [x,y,z,Atlas.next_coordinate] using h
  exact split y x z (A.no_two_cycle x).symm (labels.2.1.trans labels.1.symm)
    (labels.2.1.trans labels.2.2.symm) ⟨(A.adj_next x).symm, A.adj_next y⟩

/-- The circle parser is the only list-combinatorics dependency in this graph theorem. -/
theorem six_of_ordered_factors_with_parser [Fintype V] [DecidableEq V]
    (parse : ∀ (n : ℕ) (f : Fin n → V × Bool), 3 ≤ n → NoMarkedTriple f →
      ∃ L : Layout V, (List.ofFn f).IsRotated L.tags)
    (G F₁ F₂ : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel F₁.Adj] [DecidableRel F₂.Adj]
    (side : V → Bool) (forest : Cut.ForestCut G side) (union : F₁ ⊔ F₂ = G)
    (reg₁ : ∀ v, F₁.degree v = 2) (reg₂ : ∀ v, F₂.degree v = 2)
    (split : ∀ u v w, v ≠ w → side u = side v → side u = side w →
      ¬ (F₁.Adj u v ∧ F₁.Adj u w) ∧ ¬ (F₂.Adj u v ∧ F₂.Adj u w)) :
    G.totalChromaticNumber ≤ 6 := by
  have each (F : SimpleGraph V) [DecidableRel F.Adj] (reg : ∀ v, F.degree v = 2)
      (sub : F ≤ G) (b : Bool)
      (sp : ∀ u v w, v ≠ w → side u = side v → side u = side w → ¬(F.Adj u v ∧ F.Adj u w)) :
      Nonempty (FactorPalette G F side b) := by
    let A := atlasOfRegular reg
    have hl (j : F.ConnectedComponent) : ∃ L : Layout V, (A.word side b j).IsRotated L.tags :=
      parse (A.size j) _ (A.three j) (A.noMarkedTriple side b j sp)
    choose L hL using hl
    have hc : F.IsCycles := by
      intro v hv
      rw [← reg v, ← F.card_neighborSet_eq_degree]
      exact Nat.card_eq_fintype_card
    exact factorPalette_of_layouts G side b forest sub hc A L hL
  obtain ⟨P⟩ := each F₁ reg₁ (union ▸ le_sup_left) false (fun u v w hn hv hw => (split u v w hn hv hw).1)
  obtain ⟨Q⟩ := each F₂ reg₂ (union ▸ le_sup_right) true (fun u v w hn hv hw => (split u v w hn hv hw).2)
  exact six_of_factorPalettes G F₁ F₂ side union P Q

end Kostochka.Four

end


section -- DegreeFourParser

/- Cyclic word decomposition for Kostochka's Lemma 3. The linear parsers retain the original vertices and their prescribed colors while separating adjacent marked pairs. -/

namespace Kostochka.Four.Parser

variable {α : Type*}

def NoTwoConsecCyclic (mark : α → Bool) (xs : List α) : Prop :=
  ∀ i : Fin xs.length,
    ¬ (mark xs[i.val] = true ∧
       mark (xs[(i.val + 1) % xs.length]'(Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt))) = true)

def NoThreeConsecCyclic (mark : α → Bool) (xs : List α) : Prop :=
  ∀ i : Fin xs.length,
    ¬ (mark xs[i.val] = true ∧
       mark (xs[(i.val + 1) % xs.length]'(Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt))) = true ∧
       mark (xs[(i.val + 2) % xs.length]'(Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt))) = true)

def NoTwoConsec (mark : α → Bool) : List α → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => ¬ (mark a = true ∧ mark b = true) ∧ NoTwoConsec mark (b :: rest)

def NoThreeConsec (mark : α → Bool) : List α → Prop
  | [] => True
  | [_] => True
  | [_, _] => True
  | a :: b :: c :: rest =>
      ¬ (mark a = true ∧ mark b = true ∧ mark c = true) ∧ NoThreeConsec mark (b :: c :: rest)

theorem noTwoConsec_tail {mark : α → Bool} {a : α} {l : List α}
    (h : NoTwoConsec mark (a :: l)) : NoTwoConsec mark l := by
  cases l with
  | nil => trivial
  | cons b rest => exact h.2

theorem noThreeConsec_tail {mark : α → Bool} {a : α} {l : List α}
    (h : NoThreeConsec mark (a :: l)) : NoThreeConsec mark l := by
  cases l with
  | nil => trivial
  | cons b rest =>
    cases rest with
    | nil => trivial
    | cons c tail => exact h.2

theorem noTwoConsec_of_all_false {mark : α → Bool} {l : List α}
    (h : ∀ x ∈ l, mark x = false) : NoTwoConsec mark l := by
  induction l with
  | nil => trivial
  | cons a rest ih =>
    cases rest with
    | nil => trivial
    | cons b tail =>
      refine ⟨?_, ih (fun x hx => h x (List.mem_cons_of_mem a hx))⟩
      intro ⟨ha, _⟩
      have haf := h a (List.mem_cons_self ..)
      rw [haf] at ha
      cases ha

theorem noTwoConsec_iff_getElem {mark : α → Bool} {l : List α} :
    NoTwoConsec mark l ↔
      ∀ i (hi : i + 1 < l.length), ¬ (mark l[i] = true ∧ mark l[i + 1] = true) := by
  induction l with
  | nil => simp [NoTwoConsec]
  | cons a rest ih =>
    cases rest with
    | nil => simp [NoTwoConsec]
    | cons b tail =>
      rw [NoTwoConsec, ih]
      constructor
      · intro ⟨hab, hrest⟩ i hi
        cases i with
        | zero => simpa using hab
        | succ j => exact hrest j (by simpa using hi)
      · intro h
        refine ⟨by simpa using h 0 (by simp), fun j hj => ?_⟩
        exact h (j + 1) (by simpa using hj)

theorem noThreeConsec_iff_getElem {mark : α → Bool} {l : List α} :
    NoThreeConsec mark l ↔
      ∀ i (hi : i + 2 < l.length),
        ¬ (mark l[i] = true ∧ mark l[i + 1] = true ∧ mark l[i + 2] = true) := by
  induction l with
  | nil => simp [NoThreeConsec]
  | cons a rest ih =>
    cases rest with
    | nil => simp [NoThreeConsec]
    | cons b tail =>
      cases tail with
      | nil => simp [NoThreeConsec]
      | cons c tail' =>
        rw [NoThreeConsec, ih]
        constructor
        · intro ⟨habc, hrest⟩ i hi
          cases i with
          | zero => simpa using habc
          | succ j => exact hrest j (by simpa using hi)
        · intro h
          refine ⟨by simpa using h 0 (by simp), fun j hj => ?_⟩
          exact h (j + 1) (by simpa using hj)

theorem noTwoConsecCyclic_imp_linear {mark : α → Bool} {xs : List α}
    (h : NoTwoConsecCyclic mark xs) : NoTwoConsec mark xs := by
  rw [noTwoConsec_iff_getElem]
  intro i hi
  have hlt : i < xs.length := by omega
  have hmod : (i + 1) % xs.length = i + 1 := Nat.mod_eq_of_lt hi
  simpa [hmod] using h ⟨i, hlt⟩

theorem noThreeConsecCyclic_imp_linear {mark : α → Bool} {xs : List α}
    (h : NoThreeConsecCyclic mark xs) : NoThreeConsec mark xs := by
  rw [noThreeConsec_iff_getElem]
  intro i hi
  have hlt : i < xs.length := by omega
  have hmod1 : (i + 1) % xs.length = i + 1 := Nat.mod_eq_of_lt (by omega)
  have hmod2 : (i + 2) % xs.length = i + 2 := Nat.mod_eq_of_lt hi
  simpa [hmod1, hmod2] using h ⟨i, hlt⟩

private theorem getElem_rotate_eq (xs : List α) (k i : ℕ) (hi : i < (xs.rotate k).length) :
    (xs.rotate k)[i] =
      xs[(i + k) % xs.length]'(Nat.mod_lt _ (by rw [List.length_rotate] at hi; omega)) := by
  rw [List.getElem_rotate]

private theorem add_mod_add_right (i k d n : ℕ) :
    ((i + d) % n + k) % n = ((i + k) % n + d) % n := by
  rw [Nat.mod_add_mod, Nat.mod_add_mod, Nat.add_right_comm]

theorem noTwoConsecCyclic_rotate {mark : α → Bool} {xs : List α} (k : ℕ)
    (h : NoTwoConsecCyclic mark xs) : NoTwoConsecCyclic mark (xs.rotate k) := by
  intro i
  have hlen : (xs.rotate k).length = xs.length := List.length_rotate xs k
  have hpos : 0 < xs.length := by have := i.isLt; omega
  have hi0 : (xs.rotate k)[i.val] = xs[(i.val + k) % xs.length]'(Nat.mod_lt _ hpos) :=
    getElem_rotate_eq xs k i.val i.isLt
  have hi1 : (xs.rotate k)[(i.val + 1) % (xs.rotate k).length]'(Nat.mod_lt _ (by omega)) =
      xs[((i.val + k) % xs.length + 1) % xs.length]'(Nat.mod_lt _ hpos) := by
    rw [getElem_rotate_eq]
    congr 1
    rw [congrArg ((i.val + 1) % ·) hlen]
    exact add_mod_add_right i.val k 1 xs.length
  rw [hi0, hi1]
  exact h ⟨(i.val + k) % xs.length, Nat.mod_lt _ hpos⟩

theorem noThreeConsecCyclic_rotate {mark : α → Bool} {xs : List α} (k : ℕ)
    (h : NoThreeConsecCyclic mark xs) : NoThreeConsecCyclic mark (xs.rotate k) := by
  intro i
  have hlen : (xs.rotate k).length = xs.length := List.length_rotate xs k
  have hpos : 0 < xs.length := by have := i.isLt; omega
  have hi0 : (xs.rotate k)[i.val] = xs[(i.val + k) % xs.length]'(Nat.mod_lt _ hpos) :=
    getElem_rotate_eq xs k i.val i.isLt
  have hi1 : (xs.rotate k)[(i.val + 1) % (xs.rotate k).length]'(Nat.mod_lt _ (by omega)) =
      xs[((i.val + k) % xs.length + 1) % xs.length]'(Nat.mod_lt _ hpos) := by
    rw [getElem_rotate_eq]
    congr 1
    rw [congrArg ((i.val + 1) % ·) hlen]
    exact add_mod_add_right i.val k 1 xs.length
  have hi2 : (xs.rotate k)[(i.val + 2) % (xs.rotate k).length]'(Nat.mod_lt _ (by omega)) =
      xs[((i.val + k) % xs.length + 2) % xs.length]'(Nat.mod_lt _ hpos) := by
    rw [getElem_rotate_eq]
    congr 1
    rw [congrArg ((i.val + 2) % ·) hlen]
    exact add_mod_add_right i.val k 2 xs.length
  rw [hi0, hi1, hi2]
  exact h ⟨(i.val + k) % xs.length, Nat.mod_lt _ hpos⟩

inductive LabeledGap (α : Type*) where
  | one (u : α)
  | extra (u : α) (rest : LabeledGap α)
  | mark (u m : α) (rest : LabeledGap α)
  deriving DecidableEq, Repr

def LabeledGap.vertices : LabeledGap α → List α
  | .one u => [u]
  | .extra u rest => u :: rest.vertices
  | .mark u m rest => u :: m :: rest.vertices

def LabeledGap.Valid (mark : α → Bool) : LabeledGap α → Prop
  | .one u => mark u = false
  | .extra u rest => mark u = false ∧ rest.Valid mark
  | .mark u m rest => mark u = false ∧ mark m = true ∧ rest.Valid mark

structure LabeledPair (α : Type*) where
  fst : α
  snd : α
  deriving DecidableEq, Repr

def LabeledPair.vertices (p : LabeledPair α) : List α := [p.fst, p.snd]

def LabeledPair.Valid (mark : α → Bool) (p : LabeledPair α) : Prop :=
  mark p.fst = true ∧ mark p.snd = true

def labeledBetween (last : LabeledGap α) : List (LabeledGap α × LabeledPair α) → List α
  | [] => last.vertices
  | (g, p) :: ps => g.vertices ++ (p.vertices ++ labeledBetween last ps)

def BetweenValid (mark : α → Bool) (ps : List (LabeledGap α × LabeledPair α))
    (last : LabeledGap α) : Prop :=
  (∀ gp ∈ ps, gp.1.Valid mark ∧ gp.2.Valid mark) ∧ last.Valid mark

inductive CycleDecomp (α : Type*) where
  | isolated (head : α) (gap : LabeledGap α)
  | paired (first : LabeledPair α) (rest : List (LabeledGap α × LabeledPair α)) (last : LabeledGap α)
  deriving DecidableEq, Repr

def CycleDecomp.vertices : CycleDecomp α → List α
  | .isolated head gap => head :: gap.vertices
  | .paired first rest last => first.vertices ++ labeledBetween last rest

def CycleDecomp.Valid (mark : α → Bool) : CycleDecomp α → Prop
  | .isolated _ gap => gap.Valid mark
  | .paired first rest last => first.Valid mark ∧ BetweenValid mark rest last

/-- Read a nonempty gap beginning and ending in an unmarked vertex. -/
def parseGap (mark : α → Bool) :
    (l : List α) → (hne : l ≠ []) →
    mark (l.head hne) = false →
    mark (l.getLast hne) = false →
    NoTwoConsec mark l →
    { g : LabeledGap α // g.vertices = l ∧ g.Valid mark }
  | [], hne, _, _, _ => absurd rfl hne
  | [u], _, hhead, _, _ =>
      ⟨.one u, rfl, hhead⟩
  | u :: v :: rest, hne, hhead, hlast, hno2 =>
      match hv : mark v with
      | false =>
        let ⟨g, hgv, hgval⟩ := parseGap mark (v :: rest) (List.cons_ne_nil _ _)
          (by simpa using hv)
          (by simpa using hlast)
          hno2.2
        ⟨.extra u g, by simp [LabeledGap.vertices, hgv], ⟨by simpa using hhead, hgval⟩⟩
      | true =>
        match rest, hne, hlast, hno2 with
        | [], _, hlast, _ => by simp [hv] at hlast
        | w :: tail, _, hlast, hno2 =>
          have hw : mark w = false := by
            have hvw : ¬ (mark v = true ∧ mark w = true) := hno2.2.1
            cases hmw : mark w
            · rfl
            · exact absurd ⟨hv, hmw⟩ hvw
          let ⟨g, hgv, hgval⟩ := parseGap mark (w :: tail) (List.cons_ne_nil _ _)
            (by simpa using hw)
            (by simpa using hlast)
            hno2.2.2
          ⟨.mark u v g, by simp [LabeledGap.vertices, hgv], ⟨by simpa using hhead, hv, hgval⟩⟩
termination_by l => l.length

private def prependExtra (u : α) :
    List (LabeledGap α × LabeledPair α) × LabeledGap α →
    List (LabeledGap α × LabeledPair α) × LabeledGap α
  | ([], last) => ([], .extra u last)
  | ((g, p) :: ps, last) => ((.extra u g, p) :: ps, last)

private def prependMark (u m : α) :
    List (LabeledGap α × LabeledPair α) × LabeledGap α →
    List (LabeledGap α × LabeledPair α) × LabeledGap α
  | ([], last) => ([], .mark u m last)
  | ((g, p) :: ps, last) => ((.mark u m g, p) :: ps, last)

private theorem labeledBetween_prependExtra (u : α)
    (r : List (LabeledGap α × LabeledPair α) × LabeledGap α) :
    labeledBetween (prependExtra u r).2 (prependExtra u r).1 = u :: labeledBetween r.2 r.1 := by
  rcases r with ⟨ps, last⟩
  cases ps with
  | nil => rfl
  | cons gp tail =>
    obtain ⟨g, p⟩ := gp
    rfl

private theorem labeledBetween_prependMark (u m : α)
    (r : List (LabeledGap α × LabeledPair α) × LabeledGap α) :
    labeledBetween (prependMark u m r).2 (prependMark u m r).1 =
      u :: m :: labeledBetween r.2 r.1 := by
  rcases r with ⟨ps, last⟩
  cases ps with
  | nil => rfl
  | cons gp tail =>
    obtain ⟨g, p⟩ := gp
    rfl

private theorem betweenValid_prependExtra {mark : α → Bool} {u : α}
    {r : List (LabeledGap α × LabeledPair α) × LabeledGap α}
    (hu : mark u = false) (hr : BetweenValid mark r.1 r.2) :
    BetweenValid mark (prependExtra u r).1 (prependExtra u r).2 := by
  rcases r with ⟨ps, last⟩
  cases ps with
  | nil =>
    exact ⟨by simp [prependExtra], ⟨hu, hr.2⟩⟩
  | cons gp tail =>
    obtain ⟨g, p⟩ := gp
    refine ⟨?_, hr.2⟩
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · have hgp := hr.1 (g, p) (List.mem_cons_self ..)
      exact ⟨⟨hu, hgp.1⟩, hgp.2⟩
    · exact hr.1 x (List.mem_cons_of_mem _ hx)

private theorem betweenValid_prependMark {mark : α → Bool} {u m : α}
    {r : List (LabeledGap α × LabeledPair α) × LabeledGap α}
    (hu : mark u = false) (hm : mark m = true) (hr : BetweenValid mark r.1 r.2) :
    BetweenValid mark (prependMark u m r).1 (prependMark u m r).2 := by
  rcases r with ⟨ps, last⟩
  cases ps with
  | nil =>
    exact ⟨by simp [prependMark], ⟨hu, hm, hr.2⟩⟩
  | cons gp tail =>
    obtain ⟨g, p⟩ := gp
    refine ⟨?_, hr.2⟩
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · have hgp := hr.1 (g, p) (List.mem_cons_self ..)
      exact ⟨⟨hu, hm, hgp.1⟩, hgp.2⟩
    · exact hr.1 x (List.mem_cons_of_mem _ hx)

/-- Parse a chain of marked pairs and gaps, keeping its final gap separate for wraparound. -/
def parseBetween (mark : α → Bool) :
    (l : List α) → (hne : l ≠ []) →
    mark (l.head hne) = false →
    mark (l.getLast hne) = false →
    NoThreeConsec mark l →
    { r : List (LabeledGap α × LabeledPair α) × LabeledGap α //
        labeledBetween r.2 r.1 = l ∧ BetweenValid mark r.1 r.2 }
  | [], hne, _, _, _ => absurd rfl hne
  | [u], _, hhead, _, _ =>
      ⟨([], .one u), rfl, ⟨by simp, hhead⟩⟩
  | u :: v :: rest, hne, hhead, hlast, hno3 =>
      match hv : mark v with
      | false =>
        let ⟨r, hrv, hrval⟩ := parseBetween mark (v :: rest) (List.cons_ne_nil _ _)
          (by simpa using hv)
          (by simpa using hlast)
          (noThreeConsec_tail hno3)
        ⟨prependExtra u r,
          by rw [labeledBetween_prependExtra, hrv],
          betweenValid_prependExtra (by simpa using hhead) hrval⟩
      | true =>
        match rest, hne, hlast, hno3 with
        | [], _, hlast, _ => by simp [hv] at hlast
        | w :: tail, hne2, hlast, hno3 =>
          match hw : mark w with
          | false =>
            let ⟨r, hrv, hrval⟩ := parseBetween mark (w :: tail) (List.cons_ne_nil _ _)
              (by simpa using hw)
              (by simpa using hlast)
              (noThreeConsec_tail (noThreeConsec_tail hno3))
            ⟨prependMark u v r,
              by rw [labeledBetween_prependMark, hrv],
              betweenValid_prependMark (by simpa using hhead) hv hrval⟩
          | true =>
            match tail, hne2, hlast, hno3 with
            | [], _, hlast, _ => by simp [hw] at hlast
            | x :: tail', _, hlast, hno3 =>
              have hx : mark x = false := by
                have hvwx : ¬ (mark v = true ∧ mark w = true ∧ mark x = true) :=
                  (noThreeConsec_tail hno3).1
                cases hmx : mark x
                · rfl
                · exact absurd ⟨hv, hw, hmx⟩ hvwx
              let ⟨r, hrv, hrval⟩ := parseBetween mark (x :: tail') (List.cons_ne_nil _ _)
                (by simpa using hx)
                (by simpa using hlast)
                (noThreeConsec_tail (noThreeConsec_tail (noThreeConsec_tail hno3)))
              ⟨((.one u, ⟨v, w⟩) :: r.1, r.2),
                by simp [labeledBetween, LabeledGap.vertices, LabeledPair.vertices, hrv],
                ⟨by
                  intro gp hgp
                  rcases List.mem_cons.mp hgp with rfl | hmem
                  · exact ⟨by change mark u = false; simpa using hhead, hv, hw⟩
                  · exact hrval.1 gp hmem,
                 hrval.2⟩⟩
termination_by l => l.length

structure RotatedDecomp (α : Type*) (mark : α → Bool) (xs : List α) where
  shift : ℕ
  shift_lt : shift < xs.length
  decomp : CycleDecomp α
  vertices_eq : decomp.vertices = xs.rotate shift
  valid : decomp.Valid mark

/-- Cut at a marked pair if one exists, otherwise at an isolated marked vertex or at zero. -/
def parseCycle (mark : α → Bool) (xs : List α) (hlen : 2 ≤ xs.length)
    (hno3 : NoThreeConsecCyclic mark xs) : RotatedDecomp α mark xs :=
  match hpair : (List.finRange xs.length).find?
      (fun i => mark xs[i.val] &&
        mark (xs[(i.val + 1) % xs.length]'(Nat.mod_lt _ (by omega)))) with
  | some idx =>
    let ys := xs.rotate idx.val
    have hylen : ys.length = xs.length := List.length_rotate xs idx.val
    have hno3y : NoThreeConsecCyclic mark ys := noThreeConsecCyclic_rotate idx.val hno3
    have hfound : mark xs[idx.val] = true ∧
        mark (xs[(idx.val + 1) % xs.length]'(Nat.mod_lt _ (by omega))) = true := by
      have hp := List.find?_some hpair
      simpa [Bool.and_eq_true] using hp
    have hy0 : mark (ys[0]'(by omega)) = true := by
      have : ys[0]'(by omega) = xs[idx.val] := by
        dsimp only [ys]
        rw [getElem_rotate_eq]
        simp [Nat.mod_eq_of_lt idx.isLt]
      rw [this]; exact hfound.1
    have hy1 : mark (ys[1]'(by omega)) = true := by
      have : ys[1]'(by omega) = xs[(idx.val + 1) % xs.length]'(Nat.mod_lt _ (by omega)) := by
        dsimp only [ys]
        rw [getElem_rotate_eq]
        congr 1
        rw [Nat.add_comm]
      rw [this]; exact hfound.2
    have hlen3 : 3 ≤ ys.length := by
      by_contra hlt3
      have hlen2 : ys.length = 2 := by omega
      have h0 := hno3y ⟨0, by omega⟩
      have hm1 : (0 + 1) % ys.length = 1 := by simp [hlen2]
      have hm2 : (0 + 2) % ys.length = 0 := by simp [hlen2]
      simp only [hm1, hm2] at h0
      exact h0 ⟨hy0, hy1, hy0⟩
    match hys : ys with
    | [] => absurd (by simp [hys] at hlen3) id
    | [_] => absurd (by simp [hys] at hlen3) id
    | [_, _] => absurd (by simp [hys] at hlen3) id
    | a :: b :: c :: tail =>
      have hno3_abc : NoThreeConsecCyclic mark (a :: b :: c :: tail) := hys ▸ hno3y
      have ha : mark a = true := by simpa [hys] using hy0
      have hb : mark b = true := by simpa [hys] using hy1
      have hc : mark c = false := by
        have h0 := hno3_abc ⟨0, by simp⟩
        have hm1 : (0 + 1) % (a :: b :: c :: tail).length = 1 := Nat.mod_eq_of_lt (by simp)
        have hm2 : (0 + 2) % (a :: b :: c :: tail).length = 2 := Nat.mod_eq_of_lt (by simp)
        simp only [hm1, hm2, List.getElem_cons_zero, List.getElem_cons_succ] at h0
        cases hmc : mark c
        · rfl
        · exact absurd ⟨ha, hb, hmc⟩ h0
      have hlast : mark ((c :: tail).getLast (List.cons_ne_nil c tail)) = false := by
        have hn3 : 3 ≤ (a :: b :: c :: tail).length := by simp
        have hlast_idx := hno3_abc ⟨(a :: b :: c :: tail).length - 1, by omega⟩
        have hm1 : ((a :: b :: c :: tail).length - 1 + 1) % (a :: b :: c :: tail).length = 0 := by
          rw [Nat.sub_add_cancel (by omega), Nat.mod_self]
        have hm2 : ((a :: b :: c :: tail).length - 1 + 2) % (a :: b :: c :: tail).length = 1 := by
          have hsum : (a :: b :: c :: tail).length - 1 + 2 = (a :: b :: c :: tail).length + 1 := by
            omega
          rw [hsum, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
        have hgetlast : (a :: b :: c :: tail)[(a :: b :: c :: tail).length - 1]'(by omega) =
            (c :: tail).getLast (List.cons_ne_nil c tail) := by
          rw [← List.getLast_eq_getElem (List.cons_ne_nil a _)]
          simp [List.getLast_cons]
        simp only [hm1, hm2, hgetlast, List.getElem_cons_zero, List.getElem_cons_succ] at hlast_idx
        cases hml : mark ((c :: tail).getLast (List.cons_ne_nil c tail))
        · rfl
        · exact absurd ⟨hml, ha, hb⟩ hlast_idx
      have hno3_rest : NoThreeConsec mark (c :: tail) :=
        noThreeConsec_tail (noThreeConsec_tail (noThreeConsecCyclic_imp_linear hno3_abc))
      let ⟨r, hrv, hrval⟩ := parseBetween mark (c :: tail) (List.cons_ne_nil c tail)
        (by simpa using hc) hlast hno3_rest
      { shift := idx.val
        shift_lt := idx.isLt
        decomp := .paired ⟨a, b⟩ r.1 r.2
        vertices_eq := by
          change [a, b] ++ labeledBetween r.2 r.1 = xs.rotate idx.val
          rw [hrv]
          exact hys.symm
        valid := ⟨⟨ha, hb⟩, hrval⟩ }
  | none =>
    have hno2 : NoTwoConsecCyclic mark xs := by
      intro i
      have hnone := List.find?_eq_none.mp hpair i (List.mem_finRange i)
      intro ⟨h0, h1⟩
      exact hnone (by simp [h0, h1])
    match hmark : (List.finRange xs.length).find? (fun i => mark xs[i.val]) with
    | some idx =>
      let ys := xs.rotate idx.val
      have hylen : ys.length = xs.length := List.length_rotate xs idx.val
      have hno2y : NoTwoConsecCyclic mark ys := noTwoConsecCyclic_rotate idx.val hno2
      have hy0 : mark (ys[0]'(by omega)) = true := by
        have hp := List.find?_some hmark
        have : ys[0]'(by omega) = xs[idx.val] := by
          dsimp only [ys]
          rw [getElem_rotate_eq]
          simp [Nat.mod_eq_of_lt idx.isLt]
        rw [this]; exact hp
      match hys : ys with
      | [] => absurd (by simp [hys] at hylen; omega) id
      | [_] => absurd (by simp [hys] at hylen; omega) id
      | head :: u :: tail =>
        have hno2_hu : NoTwoConsecCyclic mark (head :: u :: tail) := hys ▸ hno2y
        have hhead : mark head = true := by simpa [hys] using hy0
        have hu : mark u = false := by
          have h0 := hno2_hu ⟨0, by simp⟩
          have hm1 : (0 + 1) % (head :: u :: tail).length = 1 := Nat.mod_eq_of_lt (by simp)
          simp only [hm1, List.getElem_cons_zero, List.getElem_cons_succ] at h0
          cases hmu : mark u
          · rfl
          · exact absurd ⟨hhead, hmu⟩ h0
        have hlast : mark ((u :: tail).getLast (List.cons_ne_nil u tail)) = false := by
          have hn2 : 2 ≤ (head :: u :: tail).length := by simp
          have hlast_idx := hno2_hu ⟨(head :: u :: tail).length - 1, by omega⟩
          have hm1 : ((head :: u :: tail).length - 1 + 1) % (head :: u :: tail).length = 0 := by
            rw [Nat.sub_add_cancel (by omega), Nat.mod_self]
          have hgetlast : (head :: u :: tail)[(head :: u :: tail).length - 1]'(by omega) =
              (u :: tail).getLast (List.cons_ne_nil u tail) := by
            rw [← List.getLast_eq_getElem (List.cons_ne_nil head _)]
            simp [List.getLast_cons]
          simp only [hm1, hgetlast, List.getElem_cons_zero] at hlast_idx
          cases hml : mark ((u :: tail).getLast (List.cons_ne_nil u tail))
          · rfl
          · exact absurd ⟨hml, hhead⟩ hlast_idx
        have hno2_rest : NoTwoConsec mark (u :: tail) :=
          noTwoConsec_tail (noTwoConsecCyclic_imp_linear hno2_hu)
        let ⟨gap, hgv, hgval⟩ := parseGap mark (u :: tail) (List.cons_ne_nil u tail)
          (by simpa using hu) hlast hno2_rest
        { shift := idx.val
          shift_lt := idx.isLt
          decomp := .isolated head gap
          vertices_eq := by
            change head :: gap.vertices = xs.rotate idx.val
            rw [hgv, ← hys]
          valid := hgval }
    | none =>
      have hall_false : ∀ x ∈ xs, mark x = false := by
        intro x hx
        obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
        have hnone := List.find?_eq_none.mp hmark ⟨i, hi⟩ (List.mem_finRange ⟨i, hi⟩)
        cases hmx : mark xs[i]
        · rfl
        · exact absurd hmx hnone
      match hxs : xs with
      | [] => absurd (by simp [hxs] at hlen) id
      | [_] => absurd (by simp [hxs] at hlen) id
      | head :: u :: tail =>
        have hall_rest : ∀ x ∈ (u :: tail), mark x = false := fun x hx =>
          hall_false x (by rw [hxs]; exact List.mem_cons_of_mem head hx)
        have hu : mark u = false := hall_rest u (List.mem_cons_self ..)
        have hlast : mark ((u :: tail).getLast (List.cons_ne_nil u tail)) = false :=
          hall_rest _ (List.getLast_mem (List.cons_ne_nil u tail))
        let ⟨gap, hgv, hgval⟩ := parseGap mark (u :: tail) (List.cons_ne_nil u tail)
          (by simpa using hu) hlast (noTwoConsec_of_all_false hall_rest)
        { shift := 0
          shift_lt := by simp
          decomp := .isolated head gap
          vertices_eq := by
            change head :: gap.vertices = (head :: u :: tail).rotate 0
            rw [hgv, List.rotate_zero]
          valid := hgval }

theorem finRotate_val_eq {n : ℕ} (hn : 2 ≤ n) (i : Fin n) :
    (finRotate n i).val = (i.val + 1) % n := by
  have : NeZero n := ⟨by omega⟩
  rw [finRotate_apply]
  change (i.val + 1 % n) % n = _
  rw [Nat.mod_eq_of_lt (show 1 < n by omega)]

theorem finRotate_two_val_eq {n : ℕ} (hn : 2 ≤ n) (i : Fin n) :
    (finRotate n (finRotate n i)).val = (i.val + 2) % n := by
  rw [finRotate_val_eq hn, finRotate_val_eq hn, Nat.mod_add_mod]

theorem noThreeConsecCyclic_ofFn_iff {n : ℕ} (hn : 2 ≤ n) (mark : α → Bool) (v : Fin n → α) :
    NoThreeConsecCyclic mark (List.ofFn v) ↔
      ∀ i : Fin n,
        ¬ (mark (v i) = true ∧
           mark (v (finRotate n i)) = true ∧
           mark (v (finRotate n (finRotate n i))) = true) := by
  constructor
  · intro h i
    have hi := h ⟨i.val, by simp [i.isLt]⟩
    have hrot1 : (⟨(i.val + 1) % n, Nat.mod_lt _ (by omega)⟩ : Fin n) = finRotate n i :=
      Fin.ext (finRotate_val_eq hn i).symm
    have hrot2 : (⟨(i.val + 2) % n, Nat.mod_lt _ (by omega)⟩ : Fin n) =
        finRotate n (finRotate n i) :=
      Fin.ext (finRotate_two_val_eq hn i).symm
    simpa [List.getElem_ofFn, List.length_ofFn, hrot1, hrot2] using hi
  · intro h ⟨i, hi⟩
    have hin : i < n := by simpa [List.length_ofFn] using hi
    have hrot1 : (⟨(i + 1) % n, Nat.mod_lt _ (by omega)⟩ : Fin n) = finRotate n ⟨i, hin⟩ :=
      Fin.ext (finRotate_val_eq hn ⟨i, hin⟩).symm
    have hrot2 : (⟨(i + 2) % n, Nat.mod_lt _ (by omega)⟩ : Fin n) =
        finRotate n (finRotate n ⟨i, hin⟩) :=
      Fin.ext (finRotate_two_val_eq hn ⟨i, hin⟩).symm
    simpa [List.getElem_ofFn, List.length_ofFn, hrot1, hrot2] using h ⟨i, hin⟩

/-- The cycle parser in the cyclic coordinates of a two-regular component. -/
def parseFinCycle {n : ℕ} (hn : 2 ≤ n) (mark : α → Bool) (v : Fin n → α)
    (hno3 : ∀ i : Fin n,
      ¬ (mark (v i) = true ∧
         mark (v (finRotate n i)) = true ∧
         mark (v (finRotate n (finRotate n i))) = true)) :
    RotatedDecomp α mark (List.ofFn v) :=
  parseCycle mark (List.ofFn v) (by simpa [List.length_ofFn] using hn)
    ((noThreeConsecCyclic_ofFn_iff hn mark v).mpr hno3)

end Kostochka.Four.Parser

end


section -- DegreeFourOrdered

/- Transfer the circular parser's tagged lists to the factor palettes. -/

namespace Kostochka.Four

open SimpleGraph _root_.Kostochka.Four.Parser

variable {V : Type}

private def adaptGap : LabeledGap (V × Bool) → VertexGap V
  | .one v => .one v.1
  | .extra v g => .extra v.1 (adaptGap g)
  | .mark v w g => .mark v.1 w.1 (adaptGap g)

private theorem adaptGap_tags (g : LabeledGap (V × Bool)) (valid : g.Valid Prod.snd) :
    (adaptGap g).tags = g.vertices := by
  induction g with
  | one v =>
    obtain ⟨v,b⟩ := v
    change b = false at valid
    subst b
    rfl
  | extra v g ih =>
    obtain ⟨v,b⟩ := v
    obtain ⟨hb,hg⟩ := valid
    change b = false at hb
    subst b
    simp [adaptGap, VertexGap.tags, LabeledGap.vertices, ih hg]
  | mark v w g ih =>
    obtain ⟨v,b⟩ := v
    obtain ⟨w,c⟩ := w
    obtain ⟨hb,hc,hg⟩ := valid
    change b = false at hb
    change c = true at hc
    subst b; subst c
    simp [adaptGap, VertexGap.tags, LabeledGap.vertices, ih hg]

private def adaptPair (p : LabeledPair (V × Bool)) : PairV V := (p.fst.1,p.snd.1)

private theorem adaptPair_tags (p : LabeledPair (V × Bool)) (hp : p.Valid Prod.snd) :
    pairTags (adaptPair p) = p.vertices := by
  obtain ⟨⟨x,b⟩,⟨y,c⟩⟩ := p
  obtain ⟨hb,hc⟩ := hp
  change b = true at hb
  change c = true at hc
  subst b; subst c
  rfl

private theorem adaptRest (last : LabeledGap (V × Bool))
    (ps : List (LabeledGap (V × Bool) × LabeledPair (V × Bool)))
    (hp : BetweenValid Prod.snd ps last) :
    restTags (adaptGap last) (ps.map (fun gp => (adaptGap gp.1,adaptPair gp.2))) = labeledBetween last ps := by
  induction ps with
  | nil => exact adaptGap_tags _ hp.2
  | cons h ps ih =>
    obtain ⟨g,p⟩ := h
    obtain ⟨hg,hp'⟩ := hp.1 (g,p) (by simp)
    have tail : BetweenValid Prod.snd ps last := ⟨fun gp hgp => hp.1 gp (by simp [hgp]),hp.2⟩
    simp [restTags,labeledBetween,adaptGap_tags g hg,adaptPair_tags p hp',ih tail]

theorem layout_of_noMarkedTriple (n : ℕ) (f : Fin n → V × Bool) (hn : 3 ≤ n) (ht : NoMarkedTriple f) :
    ∃ L : Layout V, (List.ofFn f).IsRotated L.tags := by
  let r := parseFinCycle (by omega : 2 ≤ n) Prod.snd f ht
  have valid := r.valid
  have hr : (List.ofFn f).IsRotated r.decomp.vertices := ⟨r.shift,r.vertices_eq.symm⟩
  cases hd : r.decomp with
  | isolated v g =>
    have hg : g.Valid Prod.snd := by simpa only [hd, CycleDecomp.Valid] using valid
    refine ⟨.isolated v (adaptGap g),?_⟩
    simpa [hd, CycleDecomp.vertices, Layout.tags, adaptGap_tags g hg] using hr
  | paired p ps last =>
    have hval : p.Valid Prod.snd ∧ BetweenValid Prod.snd ps last := by simpa only [hd, CycleDecomp.Valid] using valid
    refine ⟨.paired (adaptPair p) (ps.map fun gp => (adaptGap gp.1,adaptPair gp.2)) (adaptGap last),?_⟩
    simpa [hd, CycleDecomp.vertices, Layout.tags, adaptPair_tags p hval.1, adaptRest last ps hval.2] using hr

theorem six_of_ordered_factors [Fintype V] [DecidableEq V]
    (G F₁ F₂ : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel F₁.Adj] [DecidableRel F₂.Adj]
    (side : V → Bool) (forest : Cut.ForestCut G side) (union : F₁ ⊔ F₂ = G)
    (reg₁ : ∀ v, F₁.degree v = 2) (reg₂ : ∀ v, F₂.degree v = 2)
    (split : ∀ u v w, v ≠ w → side u = side v → side u = side w →
      ¬ (F₁.Adj u v ∧ F₁.Adj u w) ∧ ¬ (F₂.Adj u v ∧ F₂.Adj u w)) :
    G.totalChromaticNumber ≤ 6 :=
  six_of_ordered_factors_with_parser layout_of_noMarkedTriple G F₁ F₂ side forest union reg₁ reg₂ split

end Kostochka.Four

end


section -- FourBound

/- Kostochka's six-color theorem for all finite simple graphs of maximum
degree at most four, including the degree-four branch of the board target. -/
namespace TotalFive
open SimpleGraph

theorem more_total_colors {V : Type*} {G : SimpleGraph V} {k n : ℕ} (le : k ≤ n)
    (colored : G.TotalColorable k) : G.TotalColorable n := by
  obtain ⟨c, hv, he, hi⟩ := colored
  let f : Fin k ↪ Fin n := Fin.castLEEmb le
  exact ⟨f ∘ c, fun u v h => f.injective.ne (hv u v h), fun e e' hn adj =>
    f.injective.ne (he e e' hn adj), fun v e h => f.injective.ne (hi v e h)⟩

theorem four_regular_bound : RegularBound 4 6 := by
  apply regularBound_of_connected
  intro V _ _ G _ conn reg
  classical
  by_cases small : Fintype.card V ≤ 5
  · exact more_total_colors (by decide : 5 ≤ 6) (five_colors_of_order_le_five G small)
  have ne : Fintype.card V ≠ 5 := fun e => small e.le
  obtain ⟨A,B,cover,apart,hA,hB⟩ :=
    ForestPartition.exists_forest_bipartition_of_connected_four_regular_card_ne_five G conn reg ne
  let side (v : V) := decide (v ∈ A)
  have h (b : Bool) : (G.induce {v | side v = b}).IsAcyclic := by
    cases b
    · have eqn : {v | side v = false} = B := by
        ext v
        have hc : v ∈ A ∪ B := cover.symm ▸ Set.mem_univ v
        have hd : v ∈ A → v ∉ B := fun ha => Set.disjoint_left.mp apart ha
        by_cases ha : v ∈ A
        · simp [side,ha,hd ha]
        · simp [side,ha,hc.resolve_left ha]
      rwa [eqn]
    · have eqn : {v | side v = true} = A := by ext v; simp [side]
      rwa [eqn]
  obtain ⟨c,F₁,F₂,hc,hs,_,h₁,h₂,hl⟩ := Kostochka.Cut.fourFactors G conn reg ⟨side,h⟩
  apply more_total_colors (Kostochka.Four.six_of_ordered_factors G F₁ F₂ c hc hs h₁ h₂ hl)
  exact Nat.sInf_mem (s := {n | G.TotalColorable n}) ⟨_, G.totalColorable_card_add_card⟩

theorem six_colors_of_degree_le_four {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h : ∀ v, G.degree v ≤ 4) : G.TotalColorable 6 :=
  totalColorable_of_regular four_regular_bound G h

end TotalFive

end

theorem OMA.solution : OMA.R_TotalColoringConjecture_total_coloring_conjecture_variants_maxDegree_le_five_R1_H2_R1.H1 := by
  intro V _ _ G _ h
  exact TotalFive.six_colors_of_degree_le_four G (fun v => h ▸ G.degree_le_maxDegree v)
