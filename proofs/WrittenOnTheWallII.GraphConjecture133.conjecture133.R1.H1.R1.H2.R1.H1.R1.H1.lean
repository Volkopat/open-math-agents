import OMAReductions.R_WrittenOnTheWallII_GraphConjecture133_conjecture133_R1_H1_R1_H2_R1_H1_R1
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Finset.Card
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FinCases
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic.NormNum
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Data.List.FinRange

/-!
General host-graph lemmas for the outer-component argument of WOWII 133.
`SquareFree` is the explicit forbidden square from the LeftToSolve statement.
The component is an arbitrary set of vertices of an arbitrary simple graph.
-/

namespace HeptagonHost

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- This forbids four-cycles as subgraphs, regardless of diagonals. -/
def SquareFree (G : SimpleGraph V) : Prop :=
  ¬ (∃ a b c d : V, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
    G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)

/-- Two distinct vertices of a square-free graph have at most one common neighbor. -/
theorem common_neighbor_unique (hs : SquareFree G) {x y a b : V} (hxy : x ≠ y)
    (hxa : G.Adj x a) (hya : G.Adj y a) (hxb : G.Adj x b) (hyb : G.Adj y b) : a = b := by
  by_contra hab
  exact hs ⟨x, a, y, b, hxa.ne, hxy, hxb.ne, hya.ne.symm, hab, hyb.ne,
    hxa, hya.symm, hyb, hxb.symm⟩

/-- The graph induced on any vertex's neighborhood is a matching with isolated vertices. -/
theorem neighborhood_matching (hs : SquareFree G) {x u a b : V}
    (hxu : G.Adj x u) (hxa : G.Adj x a) (hxb : G.Adj x b)
    (hua : G.Adj u a) (hub : G.Adj u b) : a = b :=
  common_neighbor_unique hs hxu.ne hxa hua hxb hub

/-- For `x ∉ F` this says that there is no induced four-vertex path
beginning at `x` with all three remaining vertices in `F`. Adjacency implies
the required consecutive inequalities and the other inequalities follow from
the two nonadjacencies and `x ∉ F`. -/
def NoOuterP4 (G : SimpleGraph V) (x : V) (F : Set V) : Prop :=
  ∀ ⦃a b c : V⦄, a ∈ F → b ∈ F → c ∈ F →
    G.Adj x a → G.Adj a b → G.Adj b c → ¬G.Adj x b → ¬G.Adj x c → G.Adj a c

/-- `p` is a first neighbor of the root or the unique first neighbor on a
length-two path to a vertex which is not itself adjacent to the root. -/
def Branch (G : SimpleGraph V) (x p v : V) : Prop :=
  G.Adj x p ∧ (v = p ∨ (¬ G.Adj x v ∧ G.Adj p v))

theorem branch_unique (hs : SquareFree G) {x u p q : V} (hxu : x ≠ u)
    (hp : Branch G x p u) (hq : Branch G x q u) : p = q := by
  rcases hp with ⟨hxp, rfl | ⟨hnu, hpu⟩⟩
  · rcases hq with ⟨_, rfl | ⟨hnu,_⟩⟩
    · rfl
    · exact (hnu hxp).elim
  · rcases hq with ⟨hxq, rfl | ⟨_, hqu⟩⟩
    · exact (hnu hxq).elim
    · exact common_neighbor_unique hs hxu hxp hpu.symm hxq hqu.symm

/-- Starting at any chosen neighbor `a` of the root in a connected outer piece,
every vertex has a first neighbor `p` in the same piece, equal or adjacent to `a`. -/
theorem component_branches (hs : SquareFree G) {x a : V} {F : Set V}
    (hx : x ∉ F) (hp4 : NoOuterP4 G x F) (hc : (G.induce F).Preconnected)
    (ha : a ∈ F) (hxa : G.Adj x a) {v : V} (hv : v ∈ F) :
    ∃ p ∈ F, (p = a ∨ G.Adj a p) ∧ Branch G x p v := by
  let base : F := ⟨a,ha⟩
  let dest : F := ⟨v,hv⟩
  have go {w : F} (reach : Relation.ReflTransGen (G.induce F).Adj base w) :
      ∃ p ∈ F, (p = a ∨ G.Adj a p) ∧ Branch G x p (w : V) := by
    induction reach with
    | refl => exact ⟨a, ha, Or.inl rfl, hxa, Or.inl rfl⟩
    | @tail s t _ hst ih =>
      change G.Adj (s : V) (t : V) at hst
      obtain ⟨p, hp, hpa, hxp, hps⟩ := ih
      by_cases hxt : G.Adj x (t : V)
      · refine ⟨t, t.property, ?_, hxt, Or.inl rfl⟩
        rcases hps with he | ⟨_,hps⟩
        · rw [he] at hst
          rcases hpa with rfl | hap
          · exact Or.inr hst
          · exact Or.inl (common_neighbor_unique hs hxp.ne hxt hst hxa hap.symm)
        · have hxs : x ≠ (s : V) := fun h => hx (h ▸ s.property)
          have htp := common_neighbor_unique hs hxs hxt hst hxp hps.symm
          exact htp ▸ hpa
      · refine ⟨p, hp, hpa, hxp, Or.inr ⟨hxt,?_⟩⟩
        rcases hps with he | ⟨hxs,hps⟩
        · simpa [← he] using hst
        · exact hp4 hp s.property t.property hxp hps hst hxs hxt
  exact go (((G.induce F).reachable_iff_reflTransGen base dest).mp (hc base dest))

/-- The neighbors of the root in one connected outer piece form a clique. In a
square-free graph this clique has at most two vertices. -/
theorem attachment_clique (hs : SquareFree G) {x : V} {F : Set V} (hx : x ∉ F)
    (hp4 : NoOuterP4 G x F) (hc : (G.induce F).Preconnected) :
    G.IsClique (F ∩ G.neighborSet x) := by
  intro a ha b hb hab
  obtain ⟨p, _, hpa, _, hpb⟩ := component_branches hs hx hp4 hc ha.1 ha.2 hb.1
  rcases hpb with rfl | ⟨hn,_⟩
  · exact hpa.resolve_left (Ne.symm hab)
  · exact (hn hb.2).elim

/-- Any finite set of attachment vertices in the connected piece has cardinality at most two. -/
theorem attachment_card_le_two (hs : SquareFree G) {x : V} {F : Set V} (hx : x ∉ F)
    (hp4 : NoOuterP4 G x F) (hc : (G.induce F).Preconnected) (s : Finset V)
    (hsub : (s : Set V) ⊆ F ∩ G.neighborSet x) : s.card ≤ 2 := by
  apply Nat.le_of_not_lt
  intro h
  obtain ⟨a,b,c,ha,hb,hc',hab,hac,hbc⟩ := Finset.two_lt_card_iff.mp h
  have hcl := attachment_clique hs hx hp4 hc
  exact hbc (neighborhood_matching hs (hsub ha).2 (hsub hb).2 (hsub hc').2
    (hcl (hsub ha) (hsub hb) hab) (hcl (hsub ha) (hsub hc') hac))

/-- Each non-neighbor in the outer piece has exactly one parent in that piece. -/
theorem unique_parent (hs : SquareFree G) {x a v : V} {F : Set V} (hx : x ∉ F)
    (hp4 : NoOuterP4 G x F) (hc : (G.induce F).Preconnected)
    (ha : a ∈ F) (hxa : G.Adj x a) (hv : v ∈ F) (hxv : ¬G.Adj x v) :
    ∃! p, p ∈ F ∧ G.Adj x p ∧ G.Adj p v := by
  obtain ⟨p,hp,_,hxp,hpv⟩ := component_branches hs hx hp4 hc ha hxa hv
  rcases hpv with rfl | ⟨_,hpv⟩
  · exact (hxv hxp).elim
  · refine ⟨p, ⟨hp,hxp,hpv⟩, ?_⟩
    rintro q ⟨_,hxq,hqv⟩
    exact common_neighbor_unique hs (fun h : x = v => hx (h ▸ hv)) hxq hqv.symm hxp hpv.symm

/-- Adjacent second-layer vertices have the same parent. -/
theorem adjacent_children_same_parent (hs : SquareFree G) {x p q u v : V} {F : Set V}
    (hx : x ∉ F) (hp4 : NoOuterP4 G x F) (hp : p ∈ F) (hu : u ∈ F) (hv : v ∈ F)
    (hxp : G.Adj x p) (hxq : G.Adj x q) (hpu : G.Adj p u) (hqv : G.Adj q v)
    (hnu : ¬G.Adj x u) (hnv : ¬G.Adj x v) (huv : G.Adj u v) : p = q := by
  have hpv := hp4 hp hu hv hxp hpu huv hnu hnv
  exact common_neighbor_unique hs (fun h : x = v => hx (h ▸ hv)) hxp hpv.symm hxq hqv.symm

/-- If all vertices of a connected graph have clique neighborhoods, the whole graph is a clique. -/
private theorem clique_of_no_induced_triple {W : Type*} {H : SimpleGraph W}
    (hc : H.Preconnected)
    (h : ∀ a b c : W, H.Adj a b → H.Adj b c → a ≠ c → H.Adj a c) :
    ∀ a b : W, a ≠ b → H.Adj a b := by
  intro a b hab
  have step {v : W} (r : Relation.ReflTransGen H.Adj a v) : v = a ∨ H.Adj a v := by
    induction r with
    | refl => exact Or.inl rfl
    | @tail u v _ huv ih =>
      rcases ih with rfl | hau
      · exact Or.inr huv
      · by_cases hav : a = v
        · exact Or.inl hav.symm
        · exact Or.inr (h a u v hau huv hav)
  exact (step ((H.reachable_iff_reflTransGen a b).mp (hc a b))).resolve_left hab.symm

/-- In the positive-surplus range, some two attachments share an outer vertex.
Here `t` counts triangles in `F` and `d` counts attachments seeing two vertices.
Only their zero cases are needed, so the formulation works with any counts with
the two stated zero-case properties. `K` is the set of core vertices touching `F`. -/
theorem positive_surplus_forces_shared {K F : Finset V} {t d : ℕ}
    (hk : K.card ≤ 3) (hc : (G.induce (F : Set V)).Preconnected)
    (htouch : ∀ a ∈ K, ∃ v ∈ F, G.Adj a v)
    (hroot : ∀ a ∈ K, NoOuterP4 G a F)
    (htriangle : t = 0 → ∀ u ∈ F, ∀ v ∈ F, ∀ w ∈ F,
      G.Adj u v → G.Adj v w → ¬G.Adj u w)
    (hdouble : d = 0 → ∀ a ∈ K, ∀ u ∈ F, ∀ v ∈ F, G.Adj a u → G.Adj a v → u = v)
    (hpos : F.card + 2 + t + d < 2 * K.card) :
    ∃ a ∈ K, ∃ b ∈ K, a ≠ b ∧ ∃ v ∈ F, G.Adj a v ∧ G.Adj b v := by
  classical
  by_contra hn
  have unique {a b v} (ha : a ∈ K) (hb : b ∈ K) (hv : v ∈ F)
      (hav : G.Adj a v) (hbv : G.Adj b v) : a = b := by
    by_contra h
    exact hn ⟨a,ha,b,hb,h,v,hv,hav,hbv⟩
  have has (a : K) : ∃ v : F, G.Adj (a : V) (v : V) := by
    obtain ⟨v,hv,hav⟩ := htouch a a.property
    exact ⟨⟨v,hv⟩,hav⟩
  let f (a : K) : F := (has a).choose
  have hf (a : K) : G.Adj (a : V) (f a : V) := (has a).choose_spec
  have hfi : Function.Injective f := by
    intro a b he
    exact Subtype.ext (unique a.property b.property (f b).property (he ▸ hf a) (hf b))
  have hsize : K.card ≤ F.card := by simpa using Fintype.card_le_of_injective f hfi
  have hkc : K.card = 3 := by omega
  have hfc : F.card = 3 := by omega
  have ht : t = 0 := by omega
  have hd : d = 0 := by omega
  have hfs : Function.Surjective f := ((Fintype.bijective_iff_injective_and_card f).2
    ⟨hfi, by simpa using hkc.trans hfc.symm⟩).2
  have hcomplete := clique_of_no_induced_triple hc (by
    intro u v w huv hvw huw
    obtain ⟨x,hxu⟩ := hfs u
    have hxu' : G.Adj (x:V) (u:V) := hxu ▸ hf x
    have hnv : ¬G.Adj (x:V) (v:V) := fun hxv =>
      huv.ne (Subtype.ext (hdouble hd x x.property u u.property v v.property hxu' hxv))
    have hnw : ¬G.Adj (x:V) (w:V) := fun hxw =>
      huw (Subtype.ext (hdouble hd x x.property u u.property w w.property hxu' hxw))
    exact hroot x x.property u.property v.property w.property hxu' huv hvw hnv hnw)
  have h3 : 2 < Fintype.card F := by simpa using (show 2 < F.card by omega)
  obtain ⟨u,v,w,huv,huw,hvw⟩ := Fintype.two_lt_card_iff.mp h3
  exact htriangle ht u u.property v v.property w w.property
    (hcomplete u v huv) (hcomplete v w hvw) (hcomplete u w huw)

/-- The finite-core conclusion identifies any two potentially shared pairs up to order.
Combined with square-freeness, it identifies the outer vertex witnessing them as well. -/
theorem shared_vertex_unique (hs : SquareFree G) {a b c d u v : V}
    (hab : a ≠ b) (hu : G.Adj a u ∧ G.Adj b u) (hv : G.Adj c v ∧ G.Adj d v)
    (hp : (a = c ∧ b = d) ∨ (a = d ∧ b = c)) : u = v := by
  rcases hp with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact common_neighbor_unique hs hab hu.1 hu.2 hv.1 hv.2
  · exact common_neighbor_unique hs hab hu.1 hu.2 hv.2 hv.1

/-- If positive components all have a witness in a single vertex, disjointness
of the vertex sets makes the positive component unique. -/
theorem positive_piece_unique {I : Type*} {pieces : I → Set V} {surplus : I → ℤ}
    (hdisj : ∀ i j, i ≠ j → Disjoint (pieces i) (pieces j)) {witness : V → Prop}
    (hunique : ∀ {u v}, witness u → witness v → u = v)
    (hpos : ∀ i, 0 < surplus i → ∃ v ∈ pieces i, witness v)
    {i j : I} (hi : 0 < surplus i) (hj : 0 < surplus j) : i = j := by
  by_contra h
  obtain ⟨u,hu,huw⟩ := hpos i hi
  obtain ⟨v,hv,hvw⟩ := hpos j hj
  have he := hunique huw hvw
  exact Set.disjoint_left.mp (hdisj i j h) hu (he ▸ hv)

/-- Summing outer surpluses loses at most three against a core deficit of four. -/
theorem combine_surpluses {I : Type*} (s : Finset I) (surplus : I → ℤ) {core : ℤ}
    (hcore : core ≤ -4) (hbound : ∀ i ∈ s, surplus i ≤ 3)
    (hunique : ∀ i ∈ s, ∀ j ∈ s, 0 < surplus i → 0 < surplus j → i = j) :
    core + ∑ i ∈ s, surplus i ≤ -1 := by
  classical
  by_cases h : ∃ i ∈ s, 0 < surplus i
  · obtain ⟨i, hi, hpos⟩ := h
    have hrest : ∑ j ∈ s.erase i, surplus j ≤ 0 := by
      apply Finset.sum_nonpos
      intro j hj
      have hj' := Finset.mem_erase.mp hj
      exact le_of_not_gt (fun h => hj'.1 (hunique j hj'.2 i hi h hpos))
    have hsum := Finset.add_sum_erase s surplus hi
    have hb := hbound i hi
    omega
  · have hh : ∑ i ∈ s, surplus i ≤ 0 := by
      apply Finset.sum_nonpos
      intro i hi
      exact le_of_not_gt (fun hpos => h ⟨i,hi,hpos⟩)
    omega

end HeptagonHost

namespace HeptagonNeighborhood

open SimpleGraph

variable {V : Type*}

/-- In a graph of maximum degree one, distinct edges cannot share an endpoint. -/
theorem edges_equal_of_common_vertex (H : SimpleGraph V)
    (uni : ∀ x y z : V, H.Adj x y → H.Adj x z → y = z)
    {e f : H.edgeSet} {x : V} (he : x ∈ e.val) (hf : x ∈ f.val) : e = f := by
  obtain ⟨y, ey⟩ := Sym2.mem_iff_exists.mp he
  obtain ⟨z, fz⟩ := Sym2.mem_iff_exists.mp hf
  have hy : H.Adj x y := H.mem_edgeSet.mp (ey ▸ e.property)
  have hz : H.Adj x z := H.mem_edgeSet.mp (fz ▸ f.property)
  exact Subtype.ext (ey.trans ((uni x y z hy hz) ▸ fz.symm))

/-- One endpoint may be omitted independently for each edge of a matching. -/
theorem independence_of_matching [Fintype V] (H : SimpleGraph V)
    (uni : ∀ x y z : V, H.Adj x y → H.Adj x z → y = z) :
    H.indepNum + Nat.card H.edgeSet = Fintype.card V := by
  classical
  let _ := Fintype.ofFinite H.edgeSet
  rw [Nat.card_eq_fintype_card]
  have selectors (S : Finset V) (hS : H.IsIndepSet S) (e : H.edgeSet) :
      ∃ x : V, x ∈ e.val ∧ x ∉ S := by
    obtain ⟨edge, he⟩ := e
    induction edge using Sym2.inductionOn with
    | _ x y =>
      have hxy : H.Adj x y := H.mem_edgeSet.mp he
      by_cases hx : x ∈ S
      · refine ⟨y, Sym2.mem_mk_right _ _, fun hy => ?_⟩
        exact hS hx hy hxy.ne hxy
      · exact ⟨x, Sym2.mem_mk_left _ _, hx⟩
  obtain ⟨I, hI⟩ := H.exists_isNIndepSet_indepNum
  let f (e : H.edgeSet) : (Iᶜ : Finset V) :=
    ⟨(selectors I hI.isIndepSet e).choose,
      Finset.mem_compl.mpr (selectors I hI.isIndepSet e).choose_spec.2⟩
  have hf : Function.Injective f := by
    intro e₁ e₂ h
    apply edges_equal_of_common_vertex H uni (selectors I hI.isIndepSet e₁).choose_spec.1
    have hx := congrArg Subtype.val h
    change (selectors I hI.isIndepSet e₁).choose = (selectors I hI.isIndepSet e₂).choose at hx
    rw [hx]
    exact (selectors I hI.isIndepSet e₂).choose_spec.1
  have upper := Fintype.card_le_of_injective f hf
  rw [Fintype.card_coe, Finset.card_compl, hI.card_eq] at upper
  have hIcard := I.card_le_univ
  rw [hI.card_eq] at hIcard
  let endpoint (e : H.edgeSet) : V := (selectors ∅ (by simp) e).choose
  have endpoint_mem (e : H.edgeSet) : endpoint e ∈ e.val := (selectors ∅ (by simp) e).choose_spec.1
  have endpoint_inj : Function.Injective endpoint := by
    intro e₁ e₂ heq
    exact edges_equal_of_common_vertex H uni (endpoint_mem e₁) (heq ▸ endpoint_mem e₂)
  let R : Finset V := Finset.univ.image endpoint
  have hRc : R.card = Fintype.card H.edgeSet := by
    simp [R, Finset.card_image_of_injective _ endpoint_inj]
  have hRi : H.IsIndepSet (Rᶜ : Finset V) := by
    intro x hx y hy _ hxy
    let e : H.edgeSet := ⟨s(x,y), H.mem_edgeSet.mpr hxy⟩
    have hR : endpoint e ∈ R := Finset.mem_image.mpr ⟨e, Finset.mem_univ _, rfl⟩
    rcases Sym2.mem_iff.mp (endpoint_mem e) with h | h
    · exact (Finset.mem_compl.mp hx) (h ▸ hR)
    · exact (Finset.mem_compl.mp hy) (h ▸ hR)
  have lower := hRi.card_le_indepNum
  rw [Finset.card_compl, hRc] at lower
  omega

/-- A repeated neighbor inside the neighborhood would complete a four-cycle. -/
theorem neighborhood_matching {G : SimpleGraph V}
    (hC : ¬ ∃ a b c d : V, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
        G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a) (v : V) :
    ∀ x y z : G.neighborSet v, (G.induce (G.neighborSet v)).Adj x y →
      (G.induce (G.neighborSet v)).Adj x z → y = z := by
  intro x y z hxy hxz
  apply Subtype.ext
  by_contra hyz
  have hvx : G.Adj v x.val := x.property
  have hvy : G.Adj v y.val := y.property
  have hvz : G.Adj v z.val := z.property
  have hxy' : G.Adj x.val y.val := hxy
  have hxz' : G.Adj x.val z.val := hxz
  exact hC ⟨v,y,x,z,hvy.ne,hvx.ne,hvz.ne,hxy'.ne.symm,hyz,hxz'.ne,hvy,hxy'.symm,hxz',hvz.symm⟩

theorem neighborhood_identity [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hC : ¬ ∃ a b c d : V, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
        G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a) (v : V) :
    G.indepNeighborsCard v + Nat.card (G.induce (G.neighborSet v)).edgeSet = G.degree v := by
  simpa only [indepNeighborsCard, G.card_neighborSet_eq_degree] using
    independence_of_matching (G.induce (G.neighborSet v)) (neighborhood_matching hC v)

end HeptagonNeighborhood

/-! A host-graph link for the induced-heptagon case of Written on the Wall II 133.
The three cycle vertices continue an induced path from x. A component disjoint
from those vertices and missing all their neighbors cannot extend that path by
three more edges. All conditions below refer to the original graph. -/
namespace HeptagonPathLink

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

lemma no_extension {x p q t a b c : V} (hpath : G.path ≤ 6)
    (rooted : G.isInducedPath [x,p,q,t])
    (sep : ∀ z ∈ [a,b,c], ∀ w ∈ [p,q,t], z ≠ w ∧ ¬ G.Adj z w)
    (outside : ∀ z ∈ [a,b,c], z ≠ x)
    (hxa : G.Adj x a) (hab : G.Adj a b) (hbc : G.Adj b c)
    (hxb : ¬ G.Adj x b) (hxc : ¬ G.Adj x c) : G.Adj a c := by
  by_contra hac
  have distinct : a ≠ c := fun he => hxc (he ▸ hxa)
  have nonmem : ∀ z ∈ [a,b,c], z ∉ [x,p,q,t] := by
    intro z hz h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h|h|h|h
    · exact outside z hz h
    · exact (sep z hz p (by simp)).1 h
    · exact (sep z hz q (by simp)).1 h
    · exact (sep z hz t (by simp)).1 h
  have ha := nonmem a (by simp)
  have hb := nonmem b (by simp)
  have hc := nonmem c (by simp)
  have nd : [c,b,a,x,p,q,t].Nodup := by
    apply List.Nodup.cons _ (List.Nodup.cons _ (List.Nodup.cons ha rooted.1))
    · rw [List.mem_cons, not_or, List.mem_cons, not_or]
      exact ⟨Ne.symm hbc.ne, Ne.symm distinct, hc⟩
    · rw [List.mem_cons, not_or]
      exact ⟨Ne.symm hab.ne, hb⟩
  have path_edges : ∀ i j : Fin 4, G.Adj ([x,p,q,t].get i) ([x,p,q,t].get j) ↔
      i.val + 1 = j.val ∨ j.val + 1 = i.val := rooted.2
  have xp : G.Adj x p := (path_edges 0 1).2 (by decide)
  have pq : G.Adj p q := (path_edges 1 2).2 (by decide)
  have qt : G.Adj q t := (path_edges 2 3).2 (by decide)
  have xq : ¬ G.Adj x q := fun h => (by decide : ¬ ((0 : Fin 4).val + 1 = (2 : Fin 4).val ∨ (2 : Fin 4).val + 1 = (0 : Fin 4).val)) ((path_edges 0 2).1 h)
  have xt : ¬ G.Adj x t := fun h => (by decide : ¬ ((0 : Fin 4).val + 1 = (3 : Fin 4).val ∨ (3 : Fin 4).val + 1 = (0 : Fin 4).val)) ((path_edges 0 3).1 h)
  have pt : ¬ G.Adj p t := fun h => (by decide : ¬ ((1 : Fin 4).val + 1 = (3 : Fin 4).val ∨ (3 : Fin 4).val + 1 = (1 : Fin 4).val)) ((path_edges 1 3).1 h)
  have ap := (sep a (by simp) p (by simp)).2
  have aq := (sep a (by simp) q (by simp)).2
  have atn := (sep a (by simp) t (by simp)).2
  have bp := (sep b (by simp) p (by simp)).2
  have bq := (sep b (by simp) q (by simp)).2
  have bt := (sep b (by simp) t (by simp)).2
  have cp := (sep c (by simp) p (by simp)).2
  have cq := (sep c (by simp) q (by simp)).2
  have ct := (sep c (by simp) t (by simp)).2
  have induced : G.isInducedPath [c,b,a,x,p,q,t] := by
    refine ⟨nd, ?_⟩
    intro i j
    change Fin 7 at i j
    fin_cases i <;> fin_cases j <;> dsimp
    · exact ⟨fun h => False.elim (G.irrefl h), fun h => False.elim ((by decide : ¬ _) h)⟩
    · exact ⟨fun _ => by decide, fun _ => hbc.symm⟩
    · exact ⟨fun h => False.elim (hac h.symm), fun h => False.elim ((by decide : ¬ _) h)⟩
    · exact ⟨fun h => False.elim (hxc h.symm), fun h => False.elim ((by decide : ¬ _) h)⟩
    · exact ⟨fun h => False.elim (cp h), fun h => False.elim ((by decide : ¬ _) h)⟩
    · exact ⟨fun h => False.elim (cq h), fun h => False.elim ((by decide : ¬ _) h)⟩
    · exact ⟨fun h => False.elim (ct h), fun h => False.elim ((by decide : ¬ _) h)⟩
    · exact ⟨fun _ => by decide, fun _ => hbc⟩
    · exact ⟨fun h => False.elim (G.irrefl h), fun h => False.elim ((by decide : ¬ _) h)⟩
    · exact ⟨fun _ => by decide, fun _ => hab.symm⟩
    · exact ⟨fun h => False.elim (hxb h.symm), fun h => False.elim ((by decide : ¬ _) h)⟩
    · exact ⟨fun h => False.elim (bp h), fun h => False.elim ((by decide : ¬ _) h)⟩
    · exact ⟨fun h => False.elim (bq h), fun h => False.elim ((by decide : ¬ _) h)⟩
    · exact ⟨fun h => False.elim (bt h), fun h => False.elim ((by decide : ¬ _) h)⟩
    · exact ⟨fun h => False.elim (hac h), fun h => False.elim ((by decide : ¬ _) h)⟩
    · exact ⟨fun _ => by decide, fun _ => hab⟩
    · exact ⟨fun h => False.elim (G.irrefl h), fun h => False.elim ((by decide : ¬ _) h)⟩
    · exact ⟨fun _ => by decide, fun _ => hxa.symm⟩
    · exact ⟨fun h => False.elim (ap h), fun h => False.elim ((by decide : ¬ _) h)⟩
    · exact ⟨fun h => False.elim (aq h), fun h => False.elim ((by decide : ¬ _) h)⟩
    · exact ⟨fun h => False.elim (atn h), fun h => False.elim ((by decide : ¬ _) h)⟩
    · exact ⟨fun h => False.elim (hxc h), fun h => False.elim ((by decide : ¬ _) h)⟩
    · exact ⟨fun h => False.elim (hxb h), fun h => False.elim ((by decide : ¬ _) h)⟩
    · exact ⟨fun _ => by decide, fun _ => hxa⟩
    · exact ⟨fun h => False.elim (G.irrefl h), fun h => False.elim ((by decide : ¬ _) h)⟩
    · exact ⟨fun _ => by decide, fun _ => xp⟩
    · exact ⟨fun h => False.elim (xq h), fun h => False.elim ((by decide : ¬ _) h)⟩
    · exact ⟨fun h => False.elim (xt h), fun h => False.elim ((by decide : ¬ _) h)⟩
    · exact ⟨fun h => False.elim (cp h.symm), fun h => False.elim ((by decide : ¬ _) h)⟩
    · exact ⟨fun h => False.elim (bp h.symm), fun h => False.elim ((by decide : ¬ _) h)⟩
    · exact ⟨fun h => False.elim (ap h.symm), fun h => False.elim ((by decide : ¬ _) h)⟩
    · exact ⟨fun _ => by decide, fun _ => xp.symm⟩
    · exact ⟨fun h => False.elim (G.irrefl h), fun h => False.elim ((by decide : ¬ _) h)⟩
    · exact ⟨fun _ => by decide, fun _ => pq⟩
    · exact ⟨fun h => False.elim (pt h), fun h => False.elim ((by decide : ¬ _) h)⟩
    · exact ⟨fun h => False.elim (cq h.symm), fun h => False.elim ((by decide : ¬ _) h)⟩
    · exact ⟨fun h => False.elim (bq h.symm), fun h => False.elim ((by decide : ¬ _) h)⟩
    · exact ⟨fun h => False.elim (aq h.symm), fun h => False.elim ((by decide : ¬ _) h)⟩
    · exact ⟨fun h => False.elim (xq h.symm), fun h => False.elim ((by decide : ¬ _) h)⟩
    · exact ⟨fun _ => by decide, fun _ => pq.symm⟩
    · exact ⟨fun h => False.elim (G.irrefl h), fun h => False.elim ((by decide : ¬ _) h)⟩
    · exact ⟨fun _ => by decide, fun _ => qt⟩
    · exact ⟨fun h => False.elim (ct h.symm), fun h => False.elim ((by decide : ¬ _) h)⟩
    · exact ⟨fun h => False.elim (bt h.symm), fun h => False.elim ((by decide : ¬ _) h)⟩
    · exact ⟨fun h => False.elim (atn h.symm), fun h => False.elim ((by decide : ¬ _) h)⟩
    · exact ⟨fun h => False.elim (xt h.symm), fun h => False.elim ((by decide : ¬ _) h)⟩
    · exact ⟨fun h => False.elim (pt h.symm), fun h => False.elim ((by decide : ¬ _) h)⟩
    · exact ⟨fun _ => by decide, fun _ => qt.symm⟩
    · exact ⟨fun h => False.elim (G.irrefl h), fun h => False.elim ((by decide : ¬ _) h)⟩
  have h := G.length_le_path_of_isInducedPath _ induced
  change 7 ≤ G.path at h
  omega

lemma component_root {F C : Set V} {x p q t : V} (hp : p ∈ C) (hq : q ∈ C) (ht : t ∈ C)
    (hx : x ∉ F) (away : ∀ z ∈ F, ∀ w ∈ C, z ≠ w ∧ ¬ G.Adj z w)
    (hp6 : G.path = 6) (rooted : G.isInducedPath [x,p,q,t]) :
    ∀ {a b c}, a ∈ F → b ∈ F → c ∈ F → G.Adj x a → G.Adj a b → G.Adj b c →
      ¬ G.Adj x b → ¬ G.Adj x c → G.Adj a c := by
  intro a b c ha hb hc
  have listF : ∀ z ∈ [a,b,c], z ∈ F := by simpa using And.intro ha (And.intro hb hc)
  have listC : ∀ z ∈ [p,q,t], z ∈ C := by simpa using And.intro hp (And.intro hq ht)
  apply no_extension hp6.le rooted (fun z hz w hw => away z (listF z hz) w (listC w hw))
  intro z hz he
  exact hx (he ▸ listF z hz)

end HeptagonPathLink

namespace HeptagonHost

open SimpleGraph Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The edges induced in the neighborhood of v are in bijection with the triangles containing v. -/
theorem neighborhood_edges_eq_triangle_fiber (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    Nat.card (G.induce (G.neighborSet v)).edgeSet = ((G.cliqueFinset 3).filter (v ∈ ·)).card := by
  classical
  let H := G.induce (G.neighborSet v)
  let _ := Fintype.ofFinite H.edgeSet
  let ends (e : H.edgeSet) : Finset V := e.val.toFinset.image Subtype.val
  let tri (e : H.edgeSet) : Finset V := insert v (ends e)
  have hn (e : H.edgeSet) : v ∉ ends e := by
    rintro hy
    obtain ⟨a, _, he⟩ := Finset.mem_image.mp hy
    exact a.property.ne he.symm
  have hinj : Function.Injective tri := by
    intro e f he
    have he' := congrArg (fun t : Finset V => t.erase v) he
    have he'' : ends e = ends f := by simpa [tri, hn] using he'
    have hg : e.val.toFinset = f.val.toFinset := Finset.image_injective Subtype.val_injective he''
    exact Subtype.ext (Sym2.ext (fun a => by simpa only [← Sym2.mem_toFinset] using Finset.ext_iff.mp hg a))
  have image_eq : Finset.univ.image tri = (G.cliqueFinset 3).filter (v ∈ ·) := by
    ext s
    constructor
    · rintro h
      obtain ⟨⟨e,he⟩,_,rfl⟩ := Finset.mem_image.mp h
      induction e using Sym2.inductionOn with
      | _ a b =>
        have hab : G.Adj (a:V) (b:V) := H.mem_edgeSet.mp he
        have hval : tri ⟨s(a,b),he⟩ = {v, (a:V), (b:V)} := by simp [tri, ends, Sym2.toFinset_mk_eq]
        rw [hval]
        exact Finset.mem_filter.mpr ⟨G.mem_cliqueFinset_iff.mpr
          (G.is3Clique_triple_iff.mpr ⟨a.property,b.property,hab⟩), by simp⟩
    · intro h
      obtain ⟨hs,hv⟩ := Finset.mem_filter.mp h
      have ht := G.mem_cliqueFinset_iff.mp hs
      have htwo : (s.erase v).card = 2 := by rw [card_erase_of_mem hv, ht.card_eq]
      obtain ⟨a,b,hab,he⟩ := Finset.card_eq_two.mp htwo
      have htri : s = {v,a,b} := by rw [←he, Finset.insert_erase hv]
      rw [htri] at ht
      obtain ⟨hva,hvb,hab'⟩ := G.is3Clique_triple_iff.mp ht
      let av : G.neighborSet v := ⟨a,hva⟩
      let bv : G.neighborSet v := ⟨b,hvb⟩
      have hem : s(av,bv) ∈ H.edgeSet := H.mem_edgeSet.mpr hab'
      refine Finset.mem_image.mpr ⟨⟨_,hem⟩, Finset.mem_univ _, ?_⟩
      simp [tri,ends,av,bv,Sym2.toFinset_mk_eq,htri]
  rw [← image_eq, Finset.card_image_of_injective _ hinj, Finset.card_univ]
  exact Nat.card_eq_fintype_card

/-- Counting triangles with a distinguished vertex in the two possible orders. -/
theorem neighborhood_edges_sum (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∑ v, Nat.card (G.induce (G.neighborSet v)).edgeSet) = 3 * (G.cliqueFinset 3).card := by
  classical
  simp_rw [neighborhood_edges_eq_triangle_fiber, Finset.card_filter]
  rw [Finset.sum_comm, Nat.mul_comm]
  apply Finset.sum_const_nat
  intro s hs
  rw [Finset.sum_boole]
  simpa using (G.mem_cliqueFinset_iff.mp hs).card_eq

/-- The precise weighted edge/triangle identity for the upstream local independence invariant. -/
theorem total_local_independence (G : SimpleGraph V) [DecidableRel G.Adj] (hs : SquareFree G) :
    (∑ v, G.indepNeighborsCard v) + 3 * (G.cliqueFinset 3).card = 2 * G.edgeFinset.card := by
  rw [← neighborhood_edges_sum, ← Finset.sum_add_distrib, ← G.sum_degrees_eq_twice_card_edges]
  exact Finset.sum_congr rfl (fun v _ => HeptagonNeighborhood.neighborhood_identity G hs v)

/-- A surplus bound therefore implies the exact average-independence conclusion in the site step. -/
theorem average_bound_of_surplus [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hs : SquareFree G)
    (h : 2 * (G.edgeFinset.card : ℤ) - 3 * ((G.cliqueFinset 3).card : ℤ) ≤ 3 * Fintype.card V) :
    G.l ≤ 3 := by
  have hsum := total_local_independence G hs
  have hle : (∑ v, G.indepNeighborsCard v) ≤ 3 * Fintype.card V := by omega
  unfold SimpleGraph.l SimpleGraph.averageIndepNeighbors SimpleGraph.indepNeighbors
  apply (div_le_iff₀ (by exact_mod_cast Fintype.card_pos (α := V) : (0 : ℝ) < Fintype.card V)).mpr
  exact_mod_cast hle

/-- In the original graph, an attached rooted four-vertex path through the cycle yields
the outer-component partition used above. -/
theorem attachment_bound_from_host {G : SimpleGraph V} {F C : Set V} {x p q t : V}
    (hs : SquareFree G) (hp6 : G.path = 6) (rooted : G.isInducedPath [x,p,q,t])
    (hp : p ∈ C) (hq : q ∈ C) (ht : t ∈ C) (hx : x ∉ F)
    (away : ∀ z ∈ F, ∀ w ∈ C, z ≠ w ∧ ¬ G.Adj z w)
    (hc : (G.induce F).Preconnected) (s : Finset V) (hsub : (s : Set V) ⊆ F ∩ G.neighborSet x) :
    s.card ≤ 2 := by
  apply attachment_card_le_two hs hx _ hc s hsub
  intro a b c
  exact HeptagonPathLink.component_root hp hq ht hx away hp6 rooted

omit [Fintype V] in
/-- A concrete rooted spanning-tree representation of the outer component.
Every non-root vertex has an adjacent parent of lower height, and every edge
outside those parent edges joins siblings. Root and children have height at most two. -/
theorem outer_parent_tree {G : SimpleGraph V} {F : Set V} {x a : V}
    (hs : SquareFree G) (hx : x ∉ F) (hp4 : NoOuterP4 G x F)
    (hc : (G.induce F).Preconnected) (ha : a ∈ F) (hxa : G.Adj x a) :
    ∃ parent : F → F, ∃ height : F → ℕ, parent ⟨a,ha⟩ = ⟨a,ha⟩ ∧
      (∀ v, height v ≤ 2) ∧
      (∀ v, v ≠ ⟨a,ha⟩ → (G.induce F).Adj v (parent v) ∧ height (parent v) < height v) ∧
      (∀ u v, (G.induce F).Adj u v → u = parent v ∨ v = parent u ∨ parent u = parent v) := by
  classical
  let root : F := ⟨a,ha⟩
  have ex (v : F) : ∃ b : F, Branch G x (b:V) (v:V) := by
    obtain ⟨b,hb,_,hv⟩ := component_branches hs hx hp4 hc ha hxa v.property
    exact ⟨⟨b,hb⟩,hv⟩
  let branch (v : F) := (ex v).choose
  have hb (v : F) : Branch G x (branch v : V) (v : V) := (ex v).choose_spec
  let parent (v : F) := if G.Adj x (v:V) then root else branch v
  let height (v : F) : ℕ := if v = root then 0 else if G.Adj x (v:V) then 1 else 2
  have rootAdj : G.Adj x (root : V) := hxa
  have hpa (v : F) (hvn : ¬ G.Adj x (v:V)) : G.Adj (branch v : V) (v:V) := by
    rcases (hb v).2 with he | ⟨_,he⟩
    · exact (hvn (he ▸ (hb v).1)).elim
    · exact he
  have unique (u v : F) (hxu : G.Adj x (u:V)) (huv : G.Adj (u:V) (v:V))
      (hxv : ¬G.Adj x (v:V)) : u = branch v := by
    apply Subtype.ext
    exact common_neighbor_unique hs (fun e : x = (v:V) => hx (e ▸ v.property))
      hxu huv.symm (hb v).1 (hpa v hxv).symm
  have hcl := attachment_clique hs hx hp4 hc
  refine ⟨parent,height,?_,?_,?_,?_⟩
  · simp [parent,rootAdj,root]
  · intro v
    simp [height]; split_ifs <;> omega
  · intro v hvr
    change v ≠ root at hvr
    by_cases hv : G.Adj x (v:V)
    · have hrv : G.Adj (v:V) (root:V) := hcl ⟨v.property,hv⟩ ⟨root.property,rootAdj⟩ (fun e => hvr (Subtype.ext e))
      exact ⟨by simpa [parent,hv] using hrv, by simp [height,parent,hv,hvr]⟩
    · refine ⟨by simpa [parent,hv] using (hpa v hv).symm,?_⟩
      have hbr := (hb v).1
      simp [parent,hv,height,hvr,hbr]; split_ifs <;> omega
  · intro u v huv
    change G.Adj (u:V) (v:V) at huv
    by_cases hxu : G.Adj x (u:V) <;> by_cases hxv : G.Adj x (v:V)
    · exact Or.inr (Or.inr (by simp [parent,hxu,hxv]))
    · exact Or.inl (by simpa [parent,hxv] using unique u v hxu huv hxv)
    · exact Or.inr (Or.inl (by simpa [parent,hxu] using unique v u hxv huv.symm hxu))
    · apply Or.inr; apply Or.inr
      simp only [parent, hxu, hxv, if_false]
      apply Subtype.ext
      exact adjacent_children_same_parent hs hx hp4 (branch u).property u.property v.property
        (hb u).1 (hb v).1 (hpa u hxu) (hpa v hxv) hxu hxv huv

section CountPieces

variable {I : Type*} [Fintype I] {G : SimpleGraph V}

omit [Fintype V] [Fintype I] in
/-- Every clique not contained in the core is contained in exactly one core-plus-piece bag. -/
theorem clique_bag_unique (K : Finset V) (F : I → Finset V)
    (hcover : ∀ v ∉ K, ∃! i, v ∈ F i)
    (hcross : ∀ i j, i ≠ j → ∀ v ∈ F i, ∀ w ∈ F j, ¬ G.Adj v w)
    {S : Finset V} (hs : G.IsClique (S : Set V)) (hout : ¬ S ⊆ K) :
    ∃! i, S ⊆ K ∪ F i := by
  obtain ⟨v,hv,hvk⟩ := Finset.not_subset.mp hout
  obtain ⟨i,hvi,huniq⟩ := hcover v hvk
  refine ⟨i,?_,?_⟩
  · intro w hw
    by_cases hwk : w ∈ K
    · exact Finset.mem_union_left _ hwk
    · obtain ⟨j,hwj,_⟩ := hcover w hwk
      have he : i = j := by
        by_contra h
        by_cases hvw : v = w
        · exact h (huniq j (hvw ▸ hwj)).symm
        · exact hcross i j h v hvi w hwj (hs hv hw hvw)
      exact Finset.mem_union_right _ (he ▸ hwj)
  · intro j hj
    exact huniq j ((Finset.mem_union.mp (hj hv)).resolve_left hvk)

omit [Fintype V] in
/-- Additive decomposition for any finite family of objects with clique support.
Applied to singleton vertices, edges and triangles it yields the same formula for the surplus. -/
theorem clique_object_count {A : Type*} (objects : Finset A) (supp : A → Finset V)
    (K : Finset V) (F : I → Finset V) (hcl : ∀ a ∈ objects, G.IsClique ((supp a : Finset V) : Set V))
    (hcover : ∀ v ∉ K, ∃! i, v ∈ F i)
    (hcross : ∀ i j, i ≠ j → ∀ v ∈ F i, ∀ w ∈ F j, ¬ G.Adj v w) :
    (objects.card : ℤ) = (objects.filter (fun a => supp a ⊆ K)).card +
      ∑ i, (((objects.filter (fun a => supp a ⊆ K ∪ F i)).card : ℤ) -
        (objects.filter (fun a => supp a ⊆ K)).card) := by
  classical
  let inCore := objects.filter (fun a => supp a ⊆ K)
  let bag (i : I) := objects.filter (fun a => supp a ⊆ K ∪ F i)
  let extra (i : I) := bag i \ inCore
  have inc (i : I) : inCore ⊆ bag i := fun a ha => by
    obtain ⟨hao,hak⟩ := Finset.mem_filter.mp ha
    exact Finset.mem_filter.mpr ⟨hao, hak.trans Finset.subset_union_left⟩
  have ext_iff (a : A) (i : I) : a ∈ extra i ↔ a ∈ objects ∧ ¬ supp a ⊆ K ∧ supp a ⊆ K ∪ F i := by
    simp [extra,bag,inCore]; tauto
  have hunion : Finset.univ.biUnion extra = objects \ inCore := by
    ext a
    constructor
    · intro ha
      obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp ha
      obtain ⟨hao,hn,_⟩ := (ext_iff a i).mp hi
      exact Finset.mem_sdiff.mpr ⟨hao, fun h => hn (Finset.mem_filter.mp h).2⟩
    · intro ha
      obtain ⟨hao,hna⟩ := Finset.mem_sdiff.mp ha
      have hn : ¬supp a ⊆ K := fun h => hna (Finset.mem_filter.mpr ⟨hao,h⟩)
      obtain ⟨i,hi,_⟩ := clique_bag_unique K F hcover hcross (hcl a hao) hn
      exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ i,(ext_iff a i).mpr ⟨hao,hn,hi⟩⟩
  have hdisj : (↑(Finset.univ : Finset I) : Set I).PairwiseDisjoint extra := by
    intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro a hai haj
    obtain ⟨hao,hn,hi⟩ := (ext_iff a i).mp hai
    have hj := ((ext_iff a j).mp haj).2.2
    obtain ⟨b,_,hb⟩ := clique_bag_unique K F hcover hcross (hcl a hao) hn
    exact hij ((hb i hi).trans (hb j hj).symm)
  have heq : (objects \ inCore).card = ∑ i, (extra i).card := by
    rw [←hunion,Finset.card_biUnion hdisj]
  have hsz := Finset.card_sdiff_add_card_eq_card (Finset.filter_subset (fun a => supp a ⊆ K) objects)
  have hdiff (i : I) : ((extra i).card : ℤ) = (bag i).card - inCore.card := by
    have h := Finset.card_sdiff_add_card_eq_card (inc i)
    change (((bag i \ inCore).card : ℕ) : ℤ) = _
    omega
  change (objects.card : ℤ) = inCore.card + ∑ i, ((bag i).card - (inCore.card : ℤ))
  simp_rw [← hdiff]
  norm_cast
  change (objects \ inCore).card + inCore.card = objects.card at hsz
  omega

/-- Ambient cliques supported in S are exactly the cliques of its induced graph. -/
theorem clique_filter_card (G : SimpleGraph V) [DecidableRel G.Adj] (n : ℕ) (S : Finset V) :
    ((G.cliqueFinset n).filter (· ⊆ S)).card = ((G.induce (↑S : Set V)).cliqueFinset n).card := by
  classical
  let mapFin := Finset.map (Function.Embedding.subtype (fun v : V => v ∈ (↑S : Set V)))
  let H := G.induce (↑S : Set V)
  have hi : Function.Injective mapFin := Finset.map_injective _
  have eq : (H.cliqueFinset n).image mapFin = (G.cliqueFinset n).filter (· ⊆ S) := by
    ext t
    constructor
    · intro h
      obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp h
      refine Finset.mem_filter.mpr ⟨G.mem_cliqueFinset_iff.mpr ((G.isNClique_induce_iff _ _ _).mp
        (H.mem_cliqueFinset_iff.mp hf)),?_⟩
      intro a ha
      obtain ⟨u,_,rfl⟩ := Finset.mem_map.mp ha
      exact u.property
    · intro h
      obtain ⟨ht,hsub⟩ := Finset.mem_filter.mp h
      let f := t.subtype (· ∈ (↑S : Set V))
      have he : mapFin f = t := Finset.subtype_map_of_mem hsub
      exact Finset.mem_image.mpr ⟨f,H.mem_cliqueFinset_iff.mpr ((G.isNClique_induce_iff _ _ _).mpr
        (by change G.IsNClique n (mapFin f); rw [he]; exact G.mem_cliqueFinset_iff.mp ht)),he⟩
  rw [←eq, Finset.card_image_of_injective _ hi]

/-- The edge, triangle and vertex surplus of an induced subgraph. -/
def surplusOn (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : ℤ :=
  2 * ((G.induce (↑S : Set V)).edgeFinset.card : ℤ) -
    3 * (((G.induce (↑S : Set V)).cliqueFinset 3).card : ℤ) - 3 * (S.card : ℤ)

/-- The global surplus splits as the core surplus plus one increment per outer component. -/
theorem surplus_on_bags (G : SimpleGraph V) [DecidableRel G.Adj] (K : Finset V) (F : I → Finset V)
    (hcover : ∀ v ∉ K, ∃! i, v ∈ F i)
    (hcross : ∀ i j, i ≠ j → ∀ v ∈ F i, ∀ w ∈ F j, ¬ G.Adj v w) :
    2 * (G.edgeFinset.card : ℤ) - 3 * ((G.cliqueFinset 3).card : ℤ) - 3 * (Fintype.card V : ℤ) =
      surplusOn G K + ∑ i, (surplusOn G (K ∪ F i) - surplusOn G K) := by
  classical
  have edgeClique (e : Sym2 V) (he : e ∈ G.edgeFinset) : G.IsClique (e.toFinset : Set V) := by
    induction e using Sym2.inductionOn with
    | _ a b =>
      rw [Sym2.toFinset_mk_eq]
      simp only [coe_insert,coe_singleton]
      exact G.isClique_pair.mpr (fun _ => G.mem_edgeFinset.mp he)
  have hE := clique_object_count G.edgeFinset (fun e : Sym2 V => e.toFinset) K F edgeClique hcover hcross
  have hT := clique_object_count (G.cliqueFinset 3) id K F
    (fun t ht => (G.mem_cliqueFinset_iff.mp ht).isClique) hcover hcross
  have hV := clique_object_count (G := G) (univ : Finset V) (fun v => {v}) K F
    (fun v _ => by simp) hcover hcross
  simp only [SimpleGraph.card_filter_edgeFinset_toFinset_subset] at hE
  simp only [id_eq, clique_filter_card] at hT
  simp only [Finset.card_univ, Finset.singleton_subset_iff, Finset.filter_mem_eq_inter,
    Finset.univ_inter] at hV
  let E (S : Finset V) : ℤ := ((G.induce (↑S : Set V)).edgeFinset.card : ℤ)
  let T (S : Finset V) : ℤ := (((G.induce (↑S : Set V)).cliqueFinset 3).card : ℤ)
  let N (S : Finset V) : ℤ := S.card
  have hsplit (i : I) : surplusOn G (K ∪ F i) - surplusOn G K =
      2 * (E (K ∪ F i) - E K) - 3 * (T (K ∪ F i) - T K) - 3 * (N (K ∪ F i) - N K) := by
    simp only [E,T,N,surplusOn]; ring
  simp_rw [hsplit]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  change 2 * _ - 3 * _ - 3 * _ = (2 * E K - 3 * T K - 3 * N K) + _
  change (G.edgeFinset.card : ℤ) = E K + ∑ i, (E (K ∪ F i) - E K) at hE
  change ((G.cliqueFinset 3).card : ℤ) = T K + ∑ i, (T (K ∪ F i) - T K) at hT
  change (Fintype.card V : ℤ) = N K + ∑ i, (N (K ∪ F i) - N K) at hV
  linarith

end CountPieces

end HeptagonHost

namespace HeptagonEdgeCount

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A finite rooted tree with additional edges between siblings and no four-cycle
has exactly one more edge than its tree for each triangle. -/
theorem edges_of_sibling_graph (r : V) (p : V → V) (lev : V → ℕ)
    (pr : p r = r) (desc : ∀ v, v ≠ r → lev (p v) < lev v)
    (pa : ∀ v, v ≠ r → G.Adj v (p v))
    (sibling : ∀ x y, G.Adj x y → p x ≠ y → p y ≠ x → p x = p y)
    (common : ∀ x y z w, x ≠ y → G.Adj x z → G.Adj y z → G.Adj x w → G.Adj y w → z = w) :
    G.edgeFinset.card + 1 = Fintype.card V + (G.cliqueFinset 3).card := by
  classical
  let D := (Finset.univ : Finset V).erase r
  let tree := D.image fun x => s(x,p x)
  let extra := G.edgeFinset \ tree
  have el (v : V) (hv : v ≠ r) : s(v,p v) ∈ tree :=
    mem_image.mpr ⟨v,mem_erase.mpr ⟨hv,mem_univ _⟩,rfl⟩
  have nt {x y : V} (hxy : G.Adj x y) : s(x,y) ∉ tree ↔ p x ≠ y ∧ p y ≠ x := by
    constructor
    · intro h
      constructor
      · rintro rfl
        apply h; apply el
        rintro rfl; exact hxy.ne pr.symm
      · rintro rfl
        apply h; rw [Sym2.eq_swap]; apply el
        rintro rfl; exact hxy.ne pr
    · rintro ⟨hn,hm⟩ hx
      obtain ⟨v,_,he⟩ := mem_image.mp hx
      rcases Sym2.eq_iff.mp he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> contradiction
  have inc : tree ⊆ G.edgeFinset := by
    rintro _ he
    obtain ⟨v,hv,rfl⟩ := mem_image.mp he
    exact G.mem_edgeFinset.mpr (pa v (mem_erase.mp hv).1)
  have cardTree : tree.card + 1 = Fintype.card V := by
    have hinj : Set.InjOn (fun x => s(x,p x)) (D : Set V) := by
      intro a ha b hb he
      rcases Sym2.eq_iff.mp he with h | ⟨hab,hba⟩
      · exact h.1
      · have h1 := desc a (mem_erase.mp ha).1
        have h2 := desc b (mem_erase.mp hb).1
        rw [hba] at h1
        rw [←hab] at h2
        omega
    change (D.image _).card + 1 = _
    rw [Finset.card_image_of_injOn hinj]
    exact card_erase_add_one (mem_univ r)
  -- For an extra edge, its two parent edges complete the unique containing triangle.
  have edge_triangle {x y : V} (hxy : G.Adj x y) (hne : s(x,y) ∉ tree) :
      p x = p y ∧ G.Adj x (p x) ∧ G.Adj y (p x) ∧ s(x,p x) ∈ tree ∧ s(y,p x) ∈ tree := by
    obtain ⟨nx,ny⟩ := (nt hxy).mp hne
    have he := sibling x y hxy nx ny
    have xr : x ≠ r := by rintro rfl; apply ny; rw [←he,pr]
    have yr : y ≠ r := by rintro rfl; apply nx; rw [he,pr]
    exact ⟨he,pa x xr,he ▸ pa y yr,el x xr,he ▸ el y yr⟩
  -- At least one edge of a triangle is outside the rooted tree.
  have has_extra {a b c : V} (ab : G.Adj a b) (ac : G.Adj a c) (bc : G.Adj b c) :
      s(a,b) ∉ tree ∨ s(a,c) ∉ tree ∨ s(b,c) ∉ tree := by
    by_contra! hh
    have ends {x y : V} (h : s(x,y) ∈ tree) : p x = y ∨ p y = x := by
      obtain ⟨v,hv,he⟩ := mem_image.mp h
      rcases Sym2.eq_iff.mp he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp
    have small {x y : V} (xy : G.Adj x y) (h : p x = y) : lev y < lev x := by
      have xr : x ≠ r := by rintro rfl; rw [pr] at h; exact xy.ne h
      simpa only [h] using desc x xr
    obtain ⟨h1,h2,h3⟩ := hh
    rcases ends h1 with h1 | h1 <;> rcases ends h2 with h2 | h2 <;> rcases ends h3 with h3 | h3
    all_goals first | exact ab.ne (by grind) | exact ac.ne (by grind) | exact bc.ne (by grind) |
      (have l1 := small ab.symm h1; have l2 := small ac h2; have l3 := small bc.symm h3; omega)
  -- Orient each extra edge canonically only to select its shared parent.
  have completion (e : extra) : ∃ T ∈ G.cliqueFinset 3, (e.val.toFinset ⊆ T) ∧
      ∀ f ∈ extra, f.toFinset ⊆ T → f = e.val := by
    obtain ⟨e,mem⟩ := e
    induction e using Sym2.inductionOn with
    | _ x y =>
      obtain ⟨hxy,hout⟩ := mem_sdiff.mp mem
      have adj := G.mem_edgeFinset.mp hxy
      obtain ⟨_,hx,hy,xt,yt⟩ := edge_triangle adj hout
      refine ⟨{x,y,p x},G.mem_cliqueFinset_iff.mpr (G.is3Clique_triple_iff.mpr ⟨adj,hx,hy⟩),?_,?_⟩
      · simp [Sym2.toFinset_mk_eq]
      · intro f
        induction f using Sym2.inductionOn with
        | _ a b =>
          intro hf sub
          obtain ⟨hab,hn't⟩ := mem_sdiff.mp hf
          have ne := (G.mem_edgeFinset.mp hab).ne
          have ha := sub (Sym2.mem_toFinset.mpr (Sym2.mem_mk_left a b))
          have hb := sub (Sym2.mem_toFinset.mpr (Sym2.mem_mk_right a b))
          simp only [mem_insert,mem_singleton] at ha hb
          rcases ha with rfl | rfl | h <;> rcases hb with rfl | rfl | h'
          all_goals first | rfl | exact Sym2.eq_swap | subst_vars; first | contradiction | exact False.elim (hn't ((Sym2.eq_swap) ▸ xt)) | exact False.elim (hn't ((Sym2.eq_swap) ▸ yt))
  let tri (e : extra) := (completion e).choose
  have inj : Function.Injective tri := by
    intro a b hab
    apply Subtype.ext
    apply (completion b).choose_spec.2.2 a.val a.property
    change a.val.toFinset ⊆ tri b
    rw [←hab]
    exact (completion a).choose_spec.2.1
  have image : Finset.univ.image tri = G.cliqueFinset 3 := by
    ext t
    constructor
    · rintro h
      obtain ⟨e,_,rfl⟩ := mem_image.mp h
      exact (completion e).choose_spec.1
    · intro ht
      obtain ⟨a,b,c,hab,hac,hbc,rfl⟩ := G.is3Clique_iff.mp (G.mem_cliqueFinset_iff.mp ht)
      have finish (x y z : V) (hxy : G.Adj x y) (hxz : G.Adj x z) (hyz : G.Adj y z)
          (hne : s(x,y) ∉ tree) : {x,y,z} ∈ Finset.univ.image tri := by
        let e : extra := ⟨s(x,y),mem_sdiff.mpr ⟨G.mem_edgeFinset.mpr hxy,hne⟩⟩
        refine mem_image.mpr ⟨e,mem_univ _,?_⟩
        have hs := (completion e).choose_spec.2.1
        have hh := G.mem_cliqueFinset_iff.mp (completion e).choose_spec.1
        have hx : x ∈ tri e := hs (Sym2.mem_toFinset.mpr (Sym2.mem_mk_left _ _))
        have hy : y ∈ tri e := hs (Sym2.mem_toFinset.mpr (Sym2.mem_mk_right _ _))
        obtain ⟨w, hw, wx, wy⟩ : ∃ w ∈ tri e, w ≠ x ∧ w ≠ y := by
          by_contra! halt
          have hsub : tri e ⊆ {x,y} := by
            intro w hw
            by_cases wx : w = x
            · simp [wx]
            · simp [halt w hw wx]
          have hle := card_le_card hsub
          have h2 : ({x,y} : Finset V).card ≤ 2 := card_le_two
          have h3 : (tri e).card = 3 := hh.card_eq
          omega
        have hxw := hh.isClique hx hw wx.symm
        have hyw := hh.isClique hy hw wy.symm
        have eq := common x y w z hxy.ne hxw hyw hxz hyz
        subst w
        symm
        apply Finset.eq_of_subset_of_card_le
        · intro w h
          simp only [mem_insert,mem_singleton] at h
          rcases h with rfl | rfl | rfl
          · exact hx
          · exact hy
          · exact hw
        · have h3 : (tri e).card = 3 := hh.card_eq
          rw [h3, card_triple_eq_three_iff.mpr ⟨hxy.ne,hxz.ne,hyz.ne⟩]
      rcases has_extra hab hac hbc with h | h | h
      · exact finish a b c hab hac hbc h
      · have order : ({a,c,b} : Finset V) = {a,b,c} := by ext z; simp only [mem_insert,mem_singleton]; tauto
        rw [←order]
        exact finish a c b hac hab hbc.symm h
      · have order : ({b,c,a} : Finset V) = {a,b,c} := by ext z; simp only [mem_insert,mem_singleton]; tauto
        rw [←order]
        exact finish b c a hbc hab.symm hac.symm h
  have hcard := congrArg Finset.card image
  rw [Finset.card_image_of_injective _ inj, Finset.card_univ, Fintype.card_coe] at hcard
  have total := Finset.card_sdiff_add_card_eq_card inc
  change extra.card + tree.card = G.edgeFinset.card at total
  omega

end HeptagonEdgeCount

namespace HeptagonPieces

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev PieceIndex (G : SimpleGraph V) (K : Finset V) :=
  (G.induce ((K : Set V)ᶜ)).ConnectedComponent

/-- The vertices in one exterior component, as a finite set in the ambient graph. -/
noncomputable def piece (G : SimpleGraph V) (K : Finset V) (i : PieceIndex G K) : Finset V := by
  classical
  exact i.supp.toFinset.image Subtype.val

variable {G : SimpleGraph V} {K : Finset V}

lemma mem_piece {i : PieceIndex G K} {v : V} : v ∈ piece G K i ↔
    ∃ h : v ∉ K, (G.induce ((K : Set V)ᶜ)).connectedComponentMk ⟨v,h⟩ = i := by
  classical
  constructor
  · intro h
    obtain ⟨⟨w,hw⟩,ht,rfl⟩ := mem_image.mp h
    have hs : (⟨w,hw⟩ : ((K:Set V)ᶜ : Set V)) ∈ i.supp := Set.mem_toFinset.mp ht
    exact ⟨hw,hs⟩
  · rintro ⟨hv,hi⟩
    exact mem_image.mpr ⟨⟨v,hv⟩,Set.mem_toFinset.mpr hi,rfl⟩

theorem outside_unique {v : V} (hv : v ∉ K) : ∃! i : PieceIndex G K, v ∈ piece G K i := by
  refine ⟨(G.induce ((K:Set V)ᶜ)).connectedComponentMk ⟨v,hv⟩, mem_piece.mpr ⟨hv,rfl⟩, ?_⟩
  rintro i h
  exact (mem_piece.mp h).choose_spec.symm

theorem piece_nonempty (i : PieceIndex G K) : (piece G K i).Nonempty := by
  obtain ⟨v,hv⟩ := i.nonempty_supp
  exact ⟨v.val,mem_piece.mpr ⟨v.property,hv⟩⟩

theorem disjoint_core (i : PieceIndex G K) : Disjoint K (piece G K i) := by
  exact Finset.disjoint_left.mpr (fun _ hK hF => (mem_piece.mp hF).choose hK)

theorem pieces_disjoint {i j : PieceIndex G K} (h : i ≠ j) :
    Disjoint (piece G K i) (piece G K j) := by
  apply Finset.disjoint_left.mpr
  intro v hi hj
  exact h ((outside_unique (G := G) (mem_piece.mp hi).choose).unique hi hj)

theorem preconnected (i : PieceIndex G K) : (G.induce (piece G K i : Set V)).Preconnected := by
  classical
  let f : i.toSimpleGraph →g G.induce (piece G K i : Set V) := {
    toFun := fun v => ⟨v.val.val,mem_piece.mpr ⟨v.val.property,v.property⟩⟩
    map_rel' := fun h => h }
  apply i.connected_toSimpleGraph.preconnected.map f
  rintro ⟨v,hv⟩
  obtain ⟨hvk,hi⟩ := mem_piece.mp hv
  exact ⟨⟨⟨v,hvk⟩,hi⟩,rfl⟩

theorem no_cross_edges {i j : PieceIndex G K} (ij : i ≠ j) {v w : V}
    (hv : v ∈ piece G K i) (hw : w ∈ piece G K j) : ¬ G.Adj v w := by
  intro hadj
  obtain ⟨hvk,hi⟩ := mem_piece.mp hv
  obtain ⟨hwk,hj⟩ := mem_piece.mp hw
  have e : (G.induce ((K:Set V)ᶜ)).Adj ⟨v,hvk⟩ ⟨w,hwk⟩ := hadj
  exact ij (hi.symm.trans ((ConnectedComponent.connectedComponentMk_eq_of_adj e).trans hj))

theorem touches_core (hc : G.Connected) (hk : K.Nonempty) (i : PieceIndex G K) :
    ∃ v ∈ piece G K i, ∃ w ∈ K, G.Adj v w := by
  classical
  by_contra! h
  obtain ⟨a,ha⟩ := piece_nonempty i
  obtain ⟨b,hb⟩ := hk
  have closed {u v : V} (hu : u ∈ piece G K i) (hadj : G.Adj u v) : v ∈ piece G K i := by
    have hvK : v ∉ K := fun hv => h u hu v hv hadj
    obtain ⟨j,hj,_⟩ := outside_unique (G := G) hvK
    by_cases hij : i = j
    · simpa [hij] using hj
    · exact False.elim (no_cross_edges hij hu hj hadj)
  have walk := (G.reachable_iff_reflTransGen a b).mp (hc.preconnected a b)
  have all_mem {w : V} (hw : Relation.ReflTransGen G.Adj a w) : w ∈ piece G K i := by
    induction hw with
    | refl => exact ha
    | tail _ adj ih => exact closed ih adj
  exact (mem_piece.mp (all_mem walk)).choose hb

end HeptagonPieces

namespace HeptagonHost

open SimpleGraph

/-- Every outer piece has one non-tree edge for each of its triangles. -/
theorem outer_edges {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {F : Finset V} {x a : V}
    (hs : SquareFree G) (hx : x ∉ F) (hp4 : NoOuterP4 G x F)
    (hc : (G.induce (F : Set V)).Preconnected) (ha : a ∈ F) (hxa : G.Adj x a) :
    (G.induce (↑F : Set V)).edgeFinset.card + 1 = F.card + ((G.induce (↑F : Set V)).cliqueFinset 3).card := by
  obtain ⟨parent,height,hr,_,hp,he⟩ := outer_parent_tree hs hx hp4 hc ha hxa
  let H := G.induce (↑F : Set V)
  have h := HeptagonEdgeCount.edges_of_sibling_graph H ⟨a,ha⟩ parent height hr
    (fun v hv => (hp v hv).2) (fun v hv => (hp v hv).1) (by
      intro u v huv hn hm
      exact ((he u v huv).resolve_left (Ne.symm hm)).resolve_left (Ne.symm hn)) (by
      intro u v p q huv hup hvp huq hvq
      apply Subtype.ext
      exact common_neighbor_unique hs (fun h => huv (Subtype.ext h)) hup hvp huq hvq)
  simpa [H] using h

end HeptagonHost

namespace HeptagonBoundary

open SimpleGraph Finset
variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

def neighborsIn (F : Finset V) (x : V) := (F.filter (G.Adj x)).card

omit [DecidableEq V] in
theorem induced_handshake (S : Finset V) :
    (∑ x ∈ S, neighborsIn G S x) = 2 * (G.induce (S : Set V)).edgeFinset.card := by
  have hd (v : (S : Set V)) : (G.induce (S : Set V)).degree v = neighborsIn G S v := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    unfold neighborsIn
    apply Finset.card_bij (fun w _ => w.val)
    · intro w hw
      exact Finset.mem_filter.mpr ⟨w.property, (SimpleGraph.mem_neighborFinset (G.induce (S : Set V)) v w).mp hw⟩
    · intro v _ w _ e
      exact Subtype.ext e
    · intro w hw
      obtain ⟨hwS, hwG⟩ := Finset.mem_filter.mp hw
      exact ⟨⟨w, hwS⟩, (SimpleGraph.mem_neighborFinset (G.induce (S : Set V)) v ⟨w, hwS⟩).mpr hwG, rfl⟩
  rw [← (G.induce (S : Set V)).sum_degrees_eq_twice_card_edges]
  simp_rw [hd]
  exact (Finset.sum_attach S (fun x => neighborsIn G S x)).symm

theorem neighbors_union {K F : Finset V} (h : Disjoint K F) (x : V) :
    neighborsIn G (K ∪ F) x = neighborsIn G K x + neighborsIn G F x := by
  unfold neighborsIn
  rw [Finset.filter_union, Finset.card_union_of_disjoint]
  exact h.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)

omit [DecidableEq V] in
theorem cross_symm (K F : Finset V) :
    (∑ x ∈ K, neighborsIn G F x) = ∑ y ∈ F, neighborsIn G K y := by
  simp only [neighborsIn, Finset.card_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : G.Adj x y
  · simp [h, h.symm]
  · have hyx : ¬ G.Adj y x := fun h' => h h'.symm
    simp [h, hyx]

theorem edges_union {K F : Finset V} (h : Disjoint K F) :
    (G.induce ((K ∪ F : Finset V) : Set V)).edgeFinset.card =
      (G.induce (K : Set V)).edgeFinset.card + (G.induce (F : Set V)).edgeFinset.card +
        ∑ x ∈ K, neighborsIn G F x := by
  have hh := induced_handshake G (K ∪ F)
  simp_rw [neighbors_union G h] at hh
  rw [Finset.sum_union h, Finset.sum_add_distrib, Finset.sum_add_distrib,
    induced_handshake, induced_handshake, ← cross_symm G K F] at hh
  omega

omit [DecidableEq V] in
theorem crossing_count (K F : Finset V) (cap : ∀ x ∈ K, neighborsIn G F x ≤ 2) :
    (∑ x ∈ K, neighborsIn G F x) = (K.filter fun x => 0 < neighborsIn G F x).card +
      (K.filter fun x => neighborsIn G F x = 2).card := by
  rw [Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  have := cap x hx
  split_ifs <;> omega

theorem edges_with_attachments {K F : Finset V} (disj : Disjoint K F)
    (cap : ∀ x ∈ K, neighborsIn G F x ≤ 2) :
    (G.induce ((K ∪ F : Finset V) : Set V)).edgeFinset.card =
      (G.induce (K : Set V)).edgeFinset.card + (G.induce (F : Set V)).edgeFinset.card +
      (K.filter fun x => 0 < neighborsIn G F x).card +
      (K.filter fun x => neighborsIn G F x = 2).card := by
  rw [edges_union G disj, crossing_count G K F cap]
  omega

end HeptagonBoundary

namespace HeptagonBoundaryTriangles

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

def trianglesIn (S : Finset V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter fun t => t ⊆ S

lemma card_induced (S : Finset V) :
    ((G.induce (S : Set V)).cliqueFinset 3).card = (trianglesIn G S).card := by
  classical
  let e : (S : Set V) ↪ V := Function.Embedding.subtype _
  let ee : Finset (S : Set V) ↪ Finset V := ⟨fun t => t.map e, Finset.map_injective _⟩
  have h : ((G.induce (S : Set V)).cliqueFinset 3).map ee = trianglesIn G S := by
    ext t
    constructor
    · intro ht
      obtain ⟨u,hu,rfl⟩ := Finset.mem_map.mp ht
      have hcl := (G.isNClique_induce_iff (S : Set V) u 3).mp (mem_cliqueFinset_iff.mp hu)
      exact mem_filter.mpr ⟨mem_cliqueFinset_iff.mpr hcl, fun _ hy => u.property_of_mem_map_subtype hy⟩
    · intro ht
      obtain ⟨hc,hs⟩ := mem_filter.mp ht
      let u := t.subtype (· ∈ S)
      have eqn : u.map e = t := Finset.subtype_map_of_mem hs
      apply Finset.mem_map.mpr
      refine ⟨u, mem_cliqueFinset_iff.mpr ((G.isNClique_induce_iff _ _ _).mpr ?_), eqn⟩
      simpa only [← eqn] using (mem_cliqueFinset_iff.mp hc)
  rw [← h, card_map]

def neighborsIn (F : Finset V) (x : V) : Finset V := F.filter (G.Adj x)

theorem boundary_triangle_count (K F : Finset V) (hdis : Disjoint K F)
    (hind : ∀ x ∈ K, ∀ y ∈ K, ∀ z ∈ F,
      G.Adj x z → G.Adj y z → ¬ G.Adj x y)
    (hmax : ∀ x ∈ K, (neighborsIn G F x).card ≤ 2)
    (hcl : ∀ x ∈ K, G.IsClique (neighborsIn G F x : Set V)) :
    ((G.induce ((K ∪ F : Finset V) : Set V)).cliqueFinset 3).card =
      ((G.induce (K : Set V)).cliqueFinset 3).card +
      ((G.induce (F : Set V)).cliqueFinset 3).card +
      (K.filter (fun x => (neighborsIn G F x).card = 2)).card := by
  classical
  let N := neighborsIn G F
  let D := K.filter fun x => (N x).card = 2
  let tri := fun x => insert x (N x)
  let cross := D.image tri
  have nmem {x y : V} : y ∈ N x ↔ y ∈ F ∧ G.Adj x y := mem_filter
  have separated {x : V} : x ∈ K → x ∈ F → False := fun hx => Finset.disjoint_left.mp hdis hx
  have inj : Set.InjOn tri (D : Set V) := by
    intro x hx y hy he
    have hxK := (mem_filter.mp hx).1
    have hxy : x ∈ insert y (N y) := by
      change x ∈ tri y
      rw [← he]
      exact mem_insert_self _ _
    rcases mem_insert.mp hxy with eqn | h
    · exact eqn
    · exact False.elim (separated hxK (nmem.mp h).1)
  have oneK {x y z : V} (hx : x ∈ K) (hy : y ∈ F) (hz : z ∈ F)
      (xy : G.Adj x y) (xz : G.Adj x z) (yz : G.Adj y z) :
      ({x,y,z} : Finset V) ∈ cross := by
    have inc : {y,z} ⊆ N x := by
      simpa only [insert_subset_iff, singleton_subset_iff] using And.intro (nmem.mpr ⟨hy,xy⟩) (nmem.mpr ⟨hz,xz⟩)
    have size : ({y,z} : Finset V).card = 2 := Finset.card_pair yz.ne
    have eqn : ({y,z} : Finset V) = N x := Finset.eq_of_subset_of_card_le inc (size ▸ hmax x hx)
    apply Finset.mem_image.mpr
    exact ⟨x, mem_filter.mpr ⟨hx,eqn ▸ size⟩, congrArg (insert x) eqn.symm⟩
  have crossValid {t : Finset V} (ht : t ∈ cross) :
      t ∈ trianglesIn G (K ∪ F) ∧ ¬ t ⊆ K ∧ ¬ t ⊆ F := by
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨hxK,hn⟩ := Finset.mem_filter.mp hx
    obtain ⟨y,z,yz,hn⟩ := Finset.card_eq_two.mp hn
    have hy : y ∈ N x := hn ▸ (by simp)
    have hz : z ∈ N x := hn ▸ (by simp)
    have hy' := nmem.mp hy
    have hz' := nmem.mp hz
    have cyz := hcl x hxK hy hz yz
    change (insert x (N x) ∈ _) ∧ ¬ insert x (N x) ⊆ K ∧ ¬ insert x (N x) ⊆ F
    rw [hn]
    refine ⟨mem_filter.mpr ⟨mem_cliqueFinset_iff.mpr
      (is3Clique_triple_iff.mpr ⟨hy'.2,hz'.2,cyz⟩), ?_⟩, ?_, ?_⟩
    · simp [insert_subset_iff, singleton_subset_iff, hxK,hy'.1,hz'.1]
    · intro hs
      exact separated (hs (by simp : y ∈ ({x,y,z} : Finset V))) hy'.1
    · intro hs
      exact separated hxK (hs (by simp))
  have split : trianglesIn G (K ∪ F) = (trianglesIn G K ∪ trianglesIn G F) ∪ cross := by
    ext t
    constructor
    · intro ht
      obtain ⟨hc,hsub⟩ := mem_filter.mp ht
      obtain ⟨x,y,z,xy,xz,yz,rfl⟩ := is3Clique_iff.mp (mem_cliqueFinset_iff.mp hc)
      have hx := Finset.mem_union.mp (hsub (mem_insert_self _ _))
      have hy := Finset.mem_union.mp (hsub (by simp : y ∈ ({x,y,z} : Finset V)))
      have hz := Finset.mem_union.mp (hsub (by simp : z ∈ ({x,y,z} : Finset V)))
      simp only [mem_union]
      rcases hx with xK | xF <;> rcases hy with yK | yF <;> rcases hz with zK | zF
      · exact Or.inl (Or.inl (mem_filter.mpr ⟨hc,by simp [insert_subset_iff, singleton_subset_iff, xK,yK,zK]⟩))
      · exact False.elim (hind _ xK _ yK _ zF xz yz xy)
      · exact False.elim (hind _ xK _ zK _ yF xy yz.symm xz)
      · exact Or.inr (oneK xK yF zF xy xz yz)
      · exact False.elim (hind _ yK _ zK _ xF xy.symm xz.symm yz)
      · exact Or.inr (by simpa only [Finset.insert_comm] using (oneK yK xF zF xy.symm yz xz))
      · apply Or.inr
        have hm := oneK zK xF yF xz.symm yz.symm xy
        convert hm using 1
        ext v
        simp only [mem_insert,mem_singleton]
        tauto
      · exact Or.inl (Or.inr (mem_filter.mpr ⟨hc,by simp [insert_subset_iff, singleton_subset_iff, xF,yF,zF]⟩))
    · intro ht
      rcases mem_union.mp ht with h | h
      · rcases mem_union.mp h with hK | hF
        · obtain ⟨hc,hs⟩ := mem_filter.mp hK
          exact mem_filter.mpr ⟨hc,hs.trans Finset.subset_union_left⟩
        · obtain ⟨hc,hs⟩ := mem_filter.mp hF
          exact mem_filter.mpr ⟨hc,hs.trans Finset.subset_union_right⟩
      · exact (crossValid h).1
  have noKF : Disjoint (trianglesIn G K) (trianglesIn G F) := by
    apply Finset.disjoint_left.mpr
    intro t hk hf
    obtain ⟨hc,hsub⟩ := mem_filter.mp hk
    have htcard := (mem_cliqueFinset_iff.mp hc).card_eq
    obtain ⟨x,hx⟩ := Finset.card_pos.mp (show 0 < t.card by omega)
    exact separated (hsub hx) ((mem_filter.mp hf).2 hx)
  have nocross : Disjoint (trianglesIn G K ∪ trianglesIn G F) cross := by
    apply Finset.disjoint_left.mpr
    intro t ht hC
    rcases mem_union.mp ht with hK | hF
    · exact (crossValid hC).2.1 ((mem_filter.mp hK).2)
    · exact (crossValid hC).2.2 ((mem_filter.mp hF).2)
  rw [card_induced, card_induced, card_induced, split, Finset.card_union_of_disjoint nocross,
    Finset.card_union_of_disjoint noKF]
  change _ + (D.image tri).card = _ + D.card
  rw [Finset.card_image_of_injOn inj]

end HeptagonBoundaryTriangles

namespace HeptagonOuter

open SimpleGraph Finset HeptagonHost

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Each component outside the core increases the surplus by at most three.
A strictly positive increment exhibits two distinct vertices in X with a common
neighbor in this component. -/
theorem piece_surplus {K F X : Finset V} (hs : SquareFree G) (disj : Disjoint K F)
    (touchX : ∀ x ∈ K, ∀ v ∈ F, G.Adj x v → x ∈ X) (hm : X.card ≤ 3)
    (hi : G.IsIndepSet (X : Set V)) (hc : (G.induce (F : Set V)).Preconnected)
    (hex : ∃ x ∈ K, ∃ v ∈ F, G.Adj x v) (hp : ∀ x ∈ X, NoOuterP4 G x F) :
    surplusOn G (K ∪ F) - surplusOn G K ≤ 3 ∧
    (0 < surplusOn G (K ∪ F) - surplusOn G K →
      ∃ a ∈ X, ∃ b ∈ X, a ≠ b ∧ ∃ v ∈ F, G.Adj a v ∧ G.Adj b v) := by
  classical
  let N (x : V) : Finset V := F.filter (G.Adj x)
  let A := K.filter (fun x => 0 < (N x).card)
  let D := K.filter (fun x => (N x).card = 2)
  let t := ((G.induce (F : Set V)).cliqueFinset 3).card
  have memN {x v : V} : v ∈ N x ↔ v ∈ F ∧ G.Adj x v := mem_filter
  have touch (x : V) (hx : x ∈ A) : ∃ v ∈ F, G.Adj x v := by
    obtain ⟨v,hv⟩ := card_pos.mp (mem_filter.mp hx).2
    exact ⟨v, (memN.mp hv).1, (memN.mp hv).2⟩
  have asub : A ⊆ X := by
    intro x hx
    obtain ⟨v,hv,hxv⟩ := touch x hx
    exact touchX x (mem_filter.mp hx).1 v hv hxv
  have cardA := (card_le_card asub).trans hm
  have sep {x : V} (hx : x ∈ K) : x ∉ F := disjoint_left.mp disj hx
  have cap (x : V) (hx : x ∈ K) : (N x).card ≤ 2 := by
    by_cases hn : (N x).Nonempty
    · obtain ⟨v,hv⟩ := hn
      obtain ⟨hf,ha⟩ := memN.mp hv
      exact attachment_card_le_two hs (sep hx) (hp x (touchX x hx v hf ha)) hc _ (fun _ h => memN.mp h)
    · simp [Finset.not_nonempty_iff_eq_empty.mp hn]
  have cl (x : V) (hx : x ∈ K) : G.IsClique (N x : Set V) := by
    intro u hu v hv huv
    obtain ⟨hf,ha⟩ := memN.mp hu
    exact attachment_clique hs (sep hx) (hp x (touchX x hx u hf ha)) hc
      (memN.mp hu) (memN.mp hv) huv
  obtain ⟨r,hr,w,hw,hrw⟩ := hex
  have inside := outer_edges G hs (sep hr) (hp r (touchX r hr w hw hrw)) hc hw hrw
  have edges := HeptagonBoundary.edges_with_attachments G disj cap
  change _ = _ + _ + A.card + D.card at edges
  have tris := HeptagonBoundaryTriangles.boundary_triangle_count G K F disj (by
    intro x hx y hy z hz hxz hyz hxy
    exact hi (touchX x hx z hz hxz) (touchX y hy z hz hyz) hxy.ne hxy) cap cl
  change _ = _ + t + D.card at tris
  change _ + 1 = F.card + t at inside
  have vertices := Finset.card_union_of_disjoint disj
  have count : surplusOn G (K ∪ F) - surplusOn G K =
      2 * (A.card : ℤ) - F.card - 2 - t - D.card := by
    unfold surplusOn
    omega
  have fpos : 0 < F.card := card_pos.mpr ⟨w,hw⟩
  constructor
  · omega
  intro hpos
  have ht : t = 0 → ∀ u ∈ F, ∀ v ∈ F, ∀ w ∈ F, G.Adj u v → G.Adj v w → ¬ G.Adj u w := by
    intro ht u hu v hv z hz huv hvz huz
    let H := G.induce (F : Set V)
    let u' : (F : Set V) := ⟨u,hu⟩
    let v' : (F : Set V) := ⟨v,hv⟩
    let z' : (F : Set V) := ⟨z,hz⟩
    have triangle : ({u',v',z'} : Finset (F : Set V)) ∈ H.cliqueFinset 3 :=
      mem_cliqueFinset_iff.mpr (is3Clique_triple_iff.mpr ⟨huv,huz,hvz⟩)
    have : 0 < t := card_pos.mpr ⟨_,triangle⟩
    omega
  have hd : D.card = 0 → ∀ a ∈ A, ∀ u ∈ F, ∀ v ∈ F, G.Adj a u → G.Adj a v → u = v := by
    intro hD a ha u hu v hv hau hav
    have hK := (mem_filter.mp ha).1
    have hle := cap a hK
    have hne : (N a).card ≠ 2 := by
      intro he
      have ham : a ∈ D := mem_filter.mpr ⟨hK,he⟩
      have : 0 < D.card := card_pos.mpr ⟨a,ham⟩
      omega
    exact card_le_one.mp (show (N a).card ≤ 1 by omega) u (memN.mpr ⟨hu,hau⟩) v
      (memN.mpr ⟨hv,hav⟩)
  obtain ⟨a,ha,b,hb,hab,v,hv,hav,hbv⟩ := positive_surplus_forces_shared cardA hc touch
    (fun a ha => hp a (asub ha)) ht hd (by omega)
  exact ⟨a,asub ha,b,asub hb,hab,v,hv,hav,hbv⟩

end HeptagonOuter

/-! A neighbor classification around any induced heptagon in a simple graph.
A four-cycle here may have chords, whereas the seven-vertex path is induced.
-/

namespace HeptagonEncoding

open SimpleGraph

/-- The two possible nonempty neighborhoods, up to rotation. -/
def allowed (b : Fin 7 → Bool) : Prop :=
  ∃ r : Fin 7, (∀ i, b i = decide (i = r ∨ i = r + 3)) ∨
    (∀ i, b i = decide (i = r ∨ i = r + 1 ∨ i = r + 4))

/-- Given a chosen neighbor, the next five positions cannot all be missed. -/
def hitsForward (b : Fin 7 → Bool) : Prop :=
  ∀ i : Fin 7, b i = true → ∃ j : Fin 5, b (i + j.succ.castSucc) = true

/-- Two neighbors at cyclic distance two would close a four-cycle. -/
def avoidsSkip (b : Fin 7 → Bool) : Prop :=
  ∀ i : Fin 7, b i = true → b (i + 2) = false

private def bitRow (a b c d e f g : Bool) (i : Fin 7) : Bool :=
  match i.val with
  | 0 => a | 1 => b | 2 => c | 3 => d | 4 => e | 5 => f | _ => g

private theorem classify_rows : ∀ a b c d e f g : Bool,
    let t := bitRow a b c d e f g
    (∃ i, t i = true) → avoidsSkip t → hitsForward t → allowed t := by
  unfold avoidsSkip hitsForward allowed
  decide +kernel

private theorem classify (b : Fin 7 → Bool) (hn : ∃ i, b i = true)
    (hs : avoidsSkip b) (hf : hitsForward b) : allowed b := by
  have hb : bitRow (b 0) (b 1) (b 2) (b 3) (b 4) (b 5) (b 6) = b := by
    funext j
    fin_cases j <;> rfl
  have h := classify_rows (b 0) (b 1) (b 2) (b 3) (b 4) (b 5) (b 6)
  dsimp only at h
  rw [hb] at h
  exact h hn hs hf

/-- `p` parametrizes six consecutive cycle vertices starting at `i`. -/
private def position (i : Fin 7) (k : Fin 6) : Fin 7 := i + k.castSucc

private theorem arc : ∀ i : Fin 7, Function.Injective (position i) ∧
    ∀ k l : Fin 6, (cycleGraph 7).Adj (position i k) (position i l) ↔
      k.val + 1 = l.val ∨ l.val + 1 = k.val := by
  unfold Function.Injective
  decide +kernel

private theorem short_arc : ∀ i : Fin 7, (cycleGraph 7).Adj i (i+1) ∧
    (cycleGraph 7).Adj (i+1) (i+2) ∧ i ≠ i+1 ∧ i ≠ i+2 ∧ i+1 ≠ i+2 := by decide +kernel

private theorem rotated_position : ∀ i : Fin 7, ∀ j : Fin 5,
    position i j.succ = i + j.succ.castSucc := by decide +kernel

/-- The exact four-cycle exclusion used in the project reduction. -/
def noC4 {α : Type*} (G : SimpleGraph α) : Prop :=
  ¬ ∃ a b c d : α, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
    G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a

/-- An induced path of order seven is a graph embedding of the standard path. -/
def noP7 {α : Type*} (G : SimpleGraph α) : Prop := ¬(pathGraph 7).IsIndContained G

private theorem no_skip_host {α : Type*} {G : SimpleGraph α} (e : cycleGraph 7 ↪g G)
    (x : α) (hx : ∀ i, x ≠ e i) (hC : noC4 G) (i : Fin 7) (hi : G.Adj x (e i)) :
    ¬G.Adj x (e (i+2)) := by
  intro h2
  obtain ⟨h01,h12,n01,n02,n12⟩ := short_arc i
  exact hC ⟨x, e i, e (i+1), e (i+2), hx _, hx _, hx _, e.injective.ne n01,
    e.injective.ne n02, e.injective.ne n12, hi, e.map_rel_iff.mpr h01,
    e.map_rel_iff.mpr h12, h2.symm⟩

private def rootPath {α : Type*} {G : SimpleGraph α} (e : cycleGraph 7 ↪g G) (x : α) (i : Fin 7) : Fin 7 → α :=
  Fin.cases x (fun k => e (position i k))

private theorem no_five_misses {α : Type*} {G : SimpleGraph α} (e : cycleGraph 7 ↪g G)
    (x : α) (hx : ∀ i, x ≠ e i) (hP : noP7 G) (i : Fin 7) (hi : G.Adj x (e i)) :
    ∃ j : Fin 5, G.Adj x (e (i + j.succ.castSucc)) := by
  classical
  by_contra! hmiss
  have hroot : ∀ k : Fin 6, G.Adj x (e (position i k)) ↔ k = 0 := by
    intro k
    refine Fin.cases ?_ (fun j => ?_) k
    · simp [position, hi]
    · simp only [rotated_position, hmiss, Fin.succ_ne_zero]
  apply hP
  refine ⟨{ toFun := rootPath e x i, inj' := ?_, map_rel_iff' := ?_ }⟩
  · intro a b
    refine Fin.cases ?_ (fun p => ?_) a <;> refine Fin.cases ?_ (fun q => ?_) b
    · simp
    · simp [rootPath, hx]
    · simp [rootPath, Ne.symm (hx _)]
    · simp only [rootPath, Fin.cases_succ, Fin.succ_inj]
      exact fun eq => (arc i).1 (e.injective eq)
  · intro a b
    refine Fin.cases ?_ (fun p => ?_) a <;> refine Fin.cases ?_ (fun q => ?_) b
    · simp
    · change G.Adj x (e (position i q)) ↔ (pathGraph 7).Adj 0 q.succ
      rw [hroot, pathGraph_adj]
      have hel : q = 0 ↔ q.val = 0 := Fin.ext_iff
      simp only [hel, Fin.val_zero, Fin.val_succ]
      omega
    · change G.Adj (e (position i p)) x ↔ (pathGraph 7).Adj p.succ 0
      rw [SimpleGraph.adj_comm, hroot, pathGraph_adj]
      have hel : p = 0 ↔ p.val = 0 := Fin.ext_iff
      simp only [hel, Fin.val_zero, Fin.val_succ]
      omega
    · change G.Adj (e (position i p)) (e (position i q)) ↔ (pathGraph 7).Adj p.succ q.succ
      rw [e.map_rel_iff, (arc i).2, pathGraph_adj]
      simp only [Fin.val_succ]
      omega

/-- A vertex off an induced heptagon which sees it has exactly one of the two
allowable neighborhoods up to rotation. This holds in an arbitrary host. -/
theorem external_neighborhood {α : Type*} {G : SimpleGraph α} [DecidableRel G.Adj]
    (e : cycleGraph 7 ↪g G) (x : α) (hx : ∀ i, x ≠ e i)
    (hits : ∃ i, G.Adj x (e i)) (hC : noC4 G) (hP : noP7 G) :
    allowed (fun i => decide (G.Adj x (e i))) := by
  apply classify
  · simpa using hits
  · intro i hi
    simpa using no_skip_host e x hx hC i (of_decide_eq_true hi)
  · intro i hi
    simpa using no_five_misses e x hx hP i (of_decide_eq_true hi)

/-- The project hypothesis on the longest induced path rules out an induced
copy of Mathlib's seven-vertex path graph. -/
theorem noP7_of_path_le {α : Type*} [Fintype α] [DecidableEq α] {G : SimpleGraph α}
    (h : G.path ≤ 6) : noP7 G := by
  rintro ⟨e⟩
  let f : Fin 7 → α := e
  have hp : G.isInducedPath (List.ofFn f) := by
    refine ⟨List.nodup_ofFn_ofInjective e.injective, ?_⟩
    intro i j
    simp only [List.get_ofFn]
    change G.Adj (e _) (e _) ↔ _
    rw [e.map_rel_iff, pathGraph_adj]
    rfl
  have hle := G.length_le_path_of_isInducedPath (List.ofFn f) hp
  rw [List.length_ofFn] at hle
  omega

end HeptagonEncoding

namespace HeptagonCycle
open SimpleGraph Finset HeptagonEncoding

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

def vertices (e : cycleGraph 7 ↪g G) : Finset V := univ.image (fun i => e i)

/-- Restriction of the given induced embedding to a selected finite set of cycle indices. -/
noncomputable def imageIso (e : cycleGraph 7 ↪g G) (S : Finset (Fin 7)) :
    (cycleGraph 7).induce (S : Set (Fin 7)) ≃g G.induce (S.image (fun i => e i) : Set V) := by
  let f : ↥(S : Set (Fin 7)) → ↥(S.image (fun i => e i) : Set V) :=
    fun v => ⟨e v.val, mem_image.mpr ⟨v.val,v.property,rfl⟩⟩
  have hi : Function.Injective f := fun a b h => Subtype.ext (e.injective (congrArg Subtype.val h))
  have hs : Function.Surjective f := by
    rintro ⟨v,hv⟩
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hv
    exact ⟨⟨i,hi⟩,rfl⟩
  exact { toEquiv := Equiv.ofBijective f ⟨hi,hs⟩, map_rel_iff' := e.map_rel_iff }

theorem cycle_counts (e : cycleGraph 7 ↪g G) :
    (vertices e).card = 7 ∧ (G.induce (vertices e : Set V)).edgeFinset.card = 7 ∧
    ((G.induce (vertices e : Set V)).cliqueFinset 3).card = 0 := by
  let R := (cycleGraph 7).induce (Finset.univ : Finset (Fin 7))
  let E := imageIso e Finset.univ
  have hE : R.edgeFinset.card = 7 := by decide +kernel
  have hT : R.CliqueFree 3 := by
    apply (cliqueFinset_eq_empty_iff).mp
    decide +kernel
  refine ⟨?_,E.card_edgeFinset_eq.symm.trans hE,?_⟩
  · simp [vertices,Finset.card_image_of_injective _ e.injective]
  · apply Finset.card_eq_zero.mpr
    exact (hT.comap E.symm.isContained).cliqueFinset

def two (r : Fin 7) : Finset (Fin 7) := {r,r+3}
def three (r : Fin 7) : Finset (Fin 7) := {r,r+1,r+4}

private theorem index_counts : ∀ r : Fin 7,
    (two r).card = 2 ∧ ((cycleGraph 7).induce (two r : Set (Fin 7))).edgeFinset.card = 0 ∧
    (three r).card = 3 ∧ ((cycleGraph 7).induce (three r : Set (Fin 7))).edgeFinset.card = 1 := by
  decide +kernel

theorem attachment_counts (e : cycleGraph 7 ↪g G) (x : V)
    (ha : allowed (fun i => decide (G.Adj x (e i)))) :
    let N := (vertices e).filter (G.Adj x)
    (N.card = 2 ∧ (G.induce (N : Set V)).edgeFinset.card = 0) ∨
    (N.card = 3 ∧ (G.induce (N : Set V)).edgeFinset.card = 1) := by
  dsimp only
  have img (S : Finset (Fin 7)) (hs : ∀ i, G.Adj x (e i) ↔ i ∈ S) :
      (vertices e).filter (G.Adj x) = S.image (fun i => e i) := by
    ext v
    simp only [vertices, mem_filter, mem_image, mem_univ, true_and]
    constructor
    · rintro ⟨⟨i,rfl⟩,hi⟩
      exact ⟨i,(hs i).mp hi,rfl⟩
    · rintro ⟨i,hi,rfl⟩
      exact ⟨⟨i,rfl⟩,(hs i).mpr hi⟩
  obtain ⟨r,hr | hr⟩ := ha
  · left
    have h := img (two r) (fun i => by simpa [two] using (decide_eq_decide.mp (hr i)))
    rw [h]
    exact ⟨(card_image_of_injective _ e.injective).trans (index_counts r).1,
      (imageIso e (two r)).card_edgeFinset_eq.symm.trans (index_counts r).2.1⟩
  · right
    have h := img (three r) (fun i => by simpa [three] using (decide_eq_decide.mp (hr i)))
    rw [h]
    exact ⟨(card_image_of_injective _ e.injective).trans (index_counts r).2.2.1,
      (imageIso e (three r)).card_edgeFinset_eq.symm.trans (index_counts r).2.2.2⟩

private theorem forward_data (i : Fin 7) :
    (cycleGraph 7).Adj i (i+1) ∧ (cycleGraph 7).Adj (i+1) (i+2) ∧
    ¬ (cycleGraph 7).Adj i (i+2) ∧ i ≠ i+2 := by
  revert i
  decide +kernel

private theorem two_arc (r : Fin 7) :
    ∃ k : Fin 7, k ∈ two r ∧ k+1 ∉ two r ∧ k+2 ∉ two r := by
  revert r
  decide +kernel

private theorem three_arc (r : Fin 7) :
    ∃ k : Fin 7, k ∈ three r ∧ k+1 ∉ three r ∧ k+2 ∉ three r := by
  revert r
  decide +kernel

omit [DecidableEq V] [DecidableRel G.Adj] in
private theorem four_path {x p q t : V} (xp : G.Adj x p) (pq : G.Adj p q) (qt : G.Adj q t)
    (xq : ¬G.Adj x q) (xt : ¬G.Adj x t) (pt : ¬G.Adj p t)
    (xqn : x ≠ q) (xtn : x ≠ t) (ptn : p ≠ t) : G.isInducedPath [x,p,q,t] := by
  have qx : ¬ G.Adj q x := fun h => xq h.symm
  have tx : ¬ G.Adj t x := fun h => xt h.symm
  have tp : ¬ G.Adj t p := fun h => pt h.symm
  refine ⟨by simp [xp.ne,pq.ne,qt.ne,xqn,xtn,ptn], ?_⟩
  intro i j
  change Fin 4 at i j
  fin_cases i <;> fin_cases j <;> dsimp <;> first
    | exact ⟨fun _ => by decide, fun _ => xp⟩
    | exact ⟨fun _ => by decide, fun _ => xp.symm⟩
    | exact ⟨fun _ => by decide, fun _ => pq⟩
    | exact ⟨fun _ => by decide, fun _ => pq.symm⟩
    | exact ⟨fun _ => by decide, fun _ => qt⟩
    | exact ⟨fun _ => by decide, fun _ => qt.symm⟩
    | exact iff_of_false (fun h => G.irrefl h) (by decide)
    | exact iff_of_false xq (by decide)
    | exact iff_of_false xt (by decide)
    | exact iff_of_false pt (by decide)
    | exact iff_of_false tx (by decide)
    | exact iff_of_false qx (by decide)
    | exact iff_of_false tp (by decide)

theorem root_path (e : cycleGraph 7 ↪g G) (x : V) (hx : x ∉ vertices e)
    (ha : allowed (fun i => decide (G.Adj x (e i)))) :
    ∃ p ∈ vertices e, ∃ q ∈ vertices e, ∃ t ∈ vertices e, G.isInducedPath [x,p,q,t] := by
  have hmem (i : Fin 7) : e i ∈ vertices e := mem_image.mpr ⟨i,mem_univ _,rfl⟩
  have hne (i : Fin 7) : x ≠ e i := fun eq => hx (eq ▸ hmem i)
  have extract (S : Finset (Fin 7)) (hs : ∀ i, G.Adj x (e i) ↔ i ∈ S)
      (hw : ∃ k : Fin 7, k ∈ S ∧ k+1 ∉ S ∧ k+2 ∉ S) :
      ∃ p ∈ vertices e, ∃ q ∈ vertices e, ∃ t ∈ vertices e, G.isInducedPath [x,p,q,t] := by
    obtain ⟨k,hk,hk1,hk2⟩ := hw
    obtain ⟨a,b,c,d⟩ := forward_data k
    exact ⟨_,hmem k,_,hmem (k+1),_,hmem (k+2), four_path ((hs k).mpr hk)
      (e.map_rel_iff.mpr a) (e.map_rel_iff.mpr b) (mt (hs _).mp hk1) (mt (hs _).mp hk2)
      (mt e.map_rel_iff.mp c) (hne _) (hne _) (e.injective.ne d)⟩
  obtain ⟨r, hr | hr⟩ := ha
  · exact extract (two r) (fun i => by simpa [two] using (decide_eq_decide.mp (hr i))) (two_arc r)
  · exact extract (three r) (fun i => by simpa [three] using (decide_eq_decide.mp (hr i))) (three_arc r)

end HeptagonCycle

namespace HeptagonCoreCount

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- An attachment with three cycle neighbors and at least one edge between them
supplies its own triangle, uniquely identified by its vertex off the cycle. -/
lemma three_attachments_le_triangles (C X : Finset V) (hdis : Disjoint C X)
    (hlink : ∀ x ∈ X, (C.filter (G.Adj x)).card = 3 →
      0 < (G.induce (↑(C.filter (G.Adj x)) : Set V)).edgeFinset.card) :
    (X.filter (fun x => (C.filter (G.Adj x)).card = 3)).card ≤
      ((G.induce (↑(C ∪ X : Finset V) : Set V)).cliqueFinset 3).card := by
  classical
  rw [HeptagonBoundaryTriangles.card_induced]
  let D := X.filter (fun x => (C.filter (G.Adj x)).card = 3)
  let T := HeptagonBoundaryTriangles.trianglesIn G (C ∪ X)
  have unique_triangle (x : D) : ∃ t ∈ T, (t ∩ X) = {x.val} := by
    obtain ⟨hxX,hxcard⟩ := mem_filter.mp x.property
    let N := C.filter (G.Adj x.val)
    have hedge : 0 < (G.induce (N : Set V)).edgeFinset.card := hlink _ hxX hxcard
    have hne : G.induce (N : Set V) ≠ ⊥ := by
      intro h
      exact (Finset.card_pos.mp hedge).ne_empty (SimpleGraph.edgeFinset_eq_empty.mpr h)
    obtain ⟨y,z,hyz⟩ := SimpleGraph.ne_bot_iff_exists_adj.mp hne
    have hy := Finset.mem_filter.mp (show y.val ∈ C.filter (G.Adj x.val) from y.property)
    have hz := Finset.mem_filter.mp (show z.val ∈ C.filter (G.Adj x.val) from z.property)
    have hyX : y.val ∉ X := Finset.disjoint_left.mp hdis hy.1
    have hzX : z.val ∉ X := Finset.disjoint_left.mp hdis hz.1
    refine ⟨{x.val,y.val,z.val}, ?_, ?_⟩
    · apply mem_filter.mpr
      refine ⟨mem_cliqueFinset_iff.mpr (is3Clique_triple_iff.mpr ⟨hy.2,hz.2,hyz⟩), ?_⟩
      simp [Finset.insert_subset_iff, Finset.singleton_subset_iff, hxX, hy.1,hz.1]
    · ext v
      simp only [mem_inter,mem_insert,mem_singleton]
      constructor
      · rintro ⟨h,hv⟩
        rcases h with h | rfl | rfl
        · exact h
        · contradiction
        · contradiction
      · rintro rfl; exact ⟨Or.inl rfl,hxX⟩
  let f : D → T := fun x => ⟨(unique_triangle x).choose,(unique_triangle x).choose_spec.1⟩
  apply Finset.card_le_card_of_injective (f := f)
  intro x y e
  have hv := congrArg Subtype.val e
  change (unique_triangle x).choose = (unique_triangle y).choose at hv
  have h := congrArg (fun t : Finset V => t ∩ X) hv
  change (unique_triangle x).choose ∩ X = (unique_triangle y).choose ∩ X at h
  rw [(unique_triangle x).choose_spec.2,(unique_triangle y).choose_spec.2] at h
  exact Subtype.ext (Finset.singleton_injective h)

/-- Seven cycle edges and at most three independent attachments give surplus
at most minus four. The inequality only needs one triangle per three-attachment. -/
theorem core_surplus (C X : Finset V) (hdis : Disjoint C X)
    (hC : C.card = 7) (hE : (G.induce (C : Set V)).edgeFinset.card = 7)
    (hX : X.card ≤ 3) (hind : G.IsIndepSet (X : Set V))
    (hattach : ∀ x ∈ X,
      (C.filter (G.Adj x)).card = 2 ∨
      ((C.filter (G.Adj x)).card = 3 ∧
        0 < (G.induce (↑(C.filter (G.Adj x)) : Set V)).edgeFinset.card)) :
    HeptagonHost.surplusOn G (C ∪ X) ≤ -4 := by
  classical
  have htri := three_attachments_le_triangles G C X hdis (by
    intro x hx h3
    rcases hattach x hx with h2 | ⟨_,h⟩
    · omega
    · exact h)
  have empty : G.induce (X : Set V) = ⊥ := by
    by_contra hh
    obtain ⟨x,y,xy⟩ := SimpleGraph.ne_bot_iff_exists_adj.mp hh
    exact hind x.property y.property (fun eq => xy.ne (Subtype.ext eq)) xy
  have hXE : (G.induce (X : Set V)).edgeFinset.card = 0 :=
    Finset.card_eq_zero.mpr (SimpleGraph.edgeFinset_eq_empty.mpr empty)
  have hdeg : (∑ x ∈ X, HeptagonBoundary.neighborsIn G C x) =
      2*X.card + (X.filter fun x => (C.filter (G.Adj x)).card = 3).card := by
    rw [card_filter]
    calc
      _ = ∑ x ∈ X, (2 + if (C.filter (G.Adj x)).card = 3 then 1 else 0) := by
        apply sum_congr rfl
        intro x hx
        unfold HeptagonBoundary.neighborsIn
        rcases hattach x hx with h | ⟨h,_⟩ <;> simp [h]
      _ = _ := by rw [sum_add_distrib]; simp [Nat.mul_comm]
  have hedge := HeptagonBoundary.edges_union G hdis.symm
  rw [Finset.union_comm X C, hXE, hE,hdeg] at hedge
  have hsize := Finset.card_union_of_disjoint hdis
  unfold HeptagonHost.surplusOn
  omega

/-- The cycle embedding supplies the edge counts and each attachment's triangle. -/
theorem cycle_core_surplus (e : cycleGraph 7 ↪g G) (X : Finset V)
    (hdis : Disjoint (HeptagonCycle.vertices e) X)
    (hX : X.card ≤ 3) (hind : G.IsIndepSet (X : Set V))
    (ha : ∀ x ∈ X, HeptagonEncoding.allowed (fun i => decide (G.Adj x (e i)))) :
    HeptagonHost.surplusOn G (HeptagonCycle.vertices e ∪ X) ≤ -4 := by
  obtain ⟨hC,hE,_⟩ := HeptagonCycle.cycle_counts e
  apply core_surplus G _ _ hdis hC hE hX hind
  intro x hx
  rcases HeptagonCycle.attachment_counts e x (ha x hx) with h | h
  · exact Or.inl h.1
  · exact Or.inr ⟨h.1, h.2 ▸ (by decide)⟩

end HeptagonCoreCount

namespace HeptagonCore
def types : List Nat := [9, 17, 18, 19, 25, 34, 36, 38, 50, 68, 72, 73, 76, 100]
def allowedPairs : List (Nat × Nat) :=
  [(9, 17), (9, 18), (9, 19), (9, 38), (9, 68), (9, 72), (9, 76), (17, 18), (17, 34), (17, 50), (17, 72), (17, 73), (17, 100), (18, 25), (18, 34), (18, 36), (18, 38), (18, 76), (19, 34), (19, 68), (19, 76), (19, 100), (25, 36), (25, 38), (25, 72), (25, 100), (34, 36), (34, 68), (34, 73), (34, 100), (36, 50), (36, 68), (36, 72), (36, 76), (38, 68), (38, 73), (50, 72), (50, 73), (50, 76), (68, 72), (68, 73), (72, 100)]
end HeptagonCore

/-! Adjacency data can be extended one vertex at a time in an arbitrary host.
For the 14 possible heptagon neighborhoods, the table supplies one explicit
four-cycle or induced seven-vertex path for each forbidden pair configuration.
Every listed witness is checked against all relevant edges by ordinary kernel
reduction. Its construction is independent of its verification. -/
namespace HeptagonPairEncoding
open SimpleGraph HeptagonEncoding

abbrev Model (n : ℕ) := Fin n → Fin n → Bool

def Realizes {α : Type*} {n : ℕ} (G : SimpleGraph α) (f : Fin n → α) (r : Model n) : Prop :=
  Function.Injective f ∧ ∀ i j, G.Adj (f i) (f j) ↔ r i j = true

def addVertex {n : ℕ} (r : Model n) (b : Fin n → Bool) : Model (n+1) :=
  Fin.lastCases (Fin.lastCases false b) (fun i => Fin.lastCases (b i) (r i))

theorem realize_add {α : Type*} {n : ℕ} {G : SimpleGraph α} {f : Fin n → α} {r : Model n}
    (hr : Realizes G f r) {v : α} (fresh : ∀ i, v ≠ f i) (b : Fin n → Bool)
    (hb : ∀ i, G.Adj v (f i) ↔ b i = true) :
    Realizes G (Fin.lastCases v f) (addVertex r b) := by
  constructor
  · intro a c
    refine Fin.lastCases ?_ (fun i => ?_) a <;> refine Fin.lastCases ?_ (fun j => ?_) c
    · simp
    · simp [fresh]
    · simp [Ne.symm (fresh _)]
    · simp only [Fin.lastCases_castSucc, Fin.castSucc_inj]
      exact fun eq => hr.1 eq
  · intro a c
    refine Fin.lastCases ?_ (fun i => ?_) a <;> refine Fin.lastCases ?_ (fun j => ?_) c
    · simp [addVertex]
    · simpa [addVertex] using hb _
    · simpa [addVertex, G.adj_comm (f i) v] using hb i
    · simpa [addVertex] using hr.2 _ _

private def digit {n m : ℕ} [NeZero n] (w : ℕ) (i : Fin m) : Fin n :=
  ⟨((w >>> (4*i.val)) % 16) % n, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne n))⟩

def certC4 {n : ℕ} [NeZero n] (r : Model n) (w : ℕ) : Prop :=
  let f : Fin 4 → Fin n := digit w
  Function.Injective f ∧ r (f 0) (f 1) = true ∧ r (f 1) (f 2) = true ∧
    r (f 2) (f 3) = true ∧ r (f 3) (f 0) = true

def certP7 {n : ℕ} [NeZero n] (r : Model n) (w : ℕ) : Prop :=
  let f : Fin 7 → Fin n := digit w
  Function.Injective f ∧ ∀ i j : Fin 7, r (f i) (f j) = true ↔
    i.val + 1 = j.val ∨ j.val + 1 = i.val

def cert {n : ℕ} [NeZero n] (r : Model n) (w : ℕ) : Prop :=
  if w.testBit 28 then certP7 r w else certC4 r w

/-- A local forbidden configuration gives a forbidden subgraph of its host. -/
theorem no_certificate {α : Type*} {n : ℕ} [NeZero n] {G : SimpleGraph α}
    {f : Fin n → α} {r : Model n} (hr : Realizes G f r) (hc : noC4 G) (hp : noP7 G)
    (w : ℕ) : ¬ cert r w := by
  unfold cert
  split
  · rintro ⟨hinj,hedges⟩
    apply hp
    refine ⟨{ toFun := f ∘ digit w, inj' := hr.1.comp hinj, map_rel_iff' := ?_ }⟩
    intro i j
    exact (hr.2 _ _).trans ((hedges i j).trans pathGraph_adj.symm)
  · rintro ⟨hi,hab,hbc,hcd,hda⟩
    let e : Fin 4 → α := f ∘ digit w
    have inj : Function.Injective e := hr.1.comp hi
    exact hc ⟨e 0, e 1, e 2, e 3, inj.ne (by decide), inj.ne (by decide),
      inj.ne (by decide), inj.ne (by decide), inj.ne (by decide), inj.ne (by decide),
      (hr.2 _ _).mpr hab, (hr.2 _ _).mpr hbc, (hr.2 _ _).mpr hcd, (hr.2 _ _).mpr hda⟩

def mask (a : Fin 14) := HeptagonCore.types.getD a 0

def cycleAdj : Model 7 := fun i j => decide ((cycleGraph 7).Adj i j)

def pairModel (a b : Fin 14) (joined : Bool) : Model 9 :=
  addVertex (addVertex cycleAdj (fun i => (mask a).testBit i))
    (Fin.lastCases joined (fun i => (mask b).testBit i))

private def pairWitnesses : Array Nat := #[
  33648, 33648, 0, 30787, 0, 30736, 0, 30736, 33648, 33648, 408291122, 30736, 408172289, 34610,
  0, 30736, 408291122, 30736, 0, 30816, 0, 30816, 33648, 33648, 0, 30816, 408172289, 30816,
  0, 34627, 33904, 33904, 0, 30736, 33904, 33904, 33904, 33904, 0, 30736, 386291747, 30804,
  386291747, 30736, 0, 30736, 390424609, 30816, 0, 30816, 0, 30816, 390424609, 30816, 0, 30816,
  0, 34576, 0, 34576, 33905, 33905, 33905, 34576, 0, 34576, 0, 30804, 0, 30753,
  0, 30753, 33905, 33905, 390277216, 30753, 409290514, 34627, 409290514, 34576, 0, 30753, 390277216, 30753,
  0, 34576, 33904, 33904, 33905, 30736, 33136, 33136, 33904, 33904, 0, 30736, 386291747, 30753,
  386291747, 30736, 33905, 30736, 0, 30816, 409290514, 30816, 409290514, 34576, 0, 30816, 0, 30816,
  33648, 33648, 33904, 33904, 0, 30736, 33904, 33904, 33648, 33648, 408291122, 30736, 0, 34610,
  0, 30736, 408291122, 30736, 390424609, 30816, 0, 30816, 33648, 33648, 390424609, 30816, 0, 30816,
  391514162, 34576, 0, 34576, 0, 34644, 0, 34576, 391514162, 34576, 34161, 34161, 0, 30753,
  34161, 34161, 34161, 34161, 0, 30753, 406083344, 30821, 0, 34576, 406083344, 30753, 0, 30753,
  391395329, 30770, 403068707, 34644, 0, 34593, 403068707, 34593, 0, 30770, 0, 34593, 34162, 34162,
  34162, 34593, 0, 34593, 0, 30821, 0, 30770, 391395329, 30770, 0, 30770, 34162, 34162,
  0, 34576, 403068707, 34576, 0, 34593, 403068707, 34576, 0, 34576, 34161, 34161, 34162, 30753,
  33393, 33393, 34161, 34161, 0, 30753, 406083344, 30770, 0, 34576, 406083344, 30753, 34162, 30753,
  391514162, 34576, 0, 34576, 33905, 33905, 33905, 34576, 391514162, 34576, 34161, 34161, 0, 30753,
  34161, 34161, 33905, 33905, 390277216, 30753, 0, 34627, 0, 34576, 0, 30753, 390277216, 30753,
  0, 34656, 407201569, 34656, 407054176, 34593, 0, 34656, 407201569, 34656, 0, 34593, 0, 34661,
  0, 34593, 407054176, 34593, 34418, 34418, 0, 30770, 0, 34656, 34418, 34418, 34418, 34418,
  0, 34656, 0, 34656, 392513554, 30787, 392513554, 34656, 0, 34656, 389306384, 34661, 0, 34610,
  389306384, 34610, 0, 30787, 0, 34610, 34419, 34419, 34419, 34656, 34419, 34610, 0, 34610,
  33648, 33648, 0, 34656, 392513554, 30736, 392513554, 34656, 33648, 33648, 0, 30736, 408172289, 34610,
  0, 30736, 0, 30736, 0, 30816, 34419, 30816, 33648, 33648, 34419, 30816, 408172289, 30816,
  0, 34656, 407201569, 34656, 0, 34593, 0, 34656, 407201569, 34656, 389306384, 34593, 0, 34610,
  389306384, 34593, 0, 34593, 34418, 34418, 34419, 30770, 34419, 34656, 33650, 33650, 34418, 34418,
  391395329, 34656, 0, 34656, 407054176, 34593, 0, 34656, 0, 34656, 0, 34593, 34162, 34162,
  34162, 34593, 407054176, 34593, 34418, 34418, 0, 30770, 391395329, 34656, 34418, 34418, 34162, 34162
]

private def pairWitness (a b : Fin 14) (joined : Bool) : ℕ :=
  pairWitnesses[(a.val*14 + b.val)*2 + joined.toNat]?.getD 0

def compatible (a b : Fin 14) : Prop :=
  (mask a,mask b) ∈ HeptagonCore.allowedPairs ∨ (mask b,mask a) ∈ HeptagonCore.allowedPairs

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 10000 in
private theorem pair_cases : ∀ (a b : Fin 14) (joined : Bool),
    (joined = false ∧ compatible a b) ∨ cert (pairModel a b joined) (pairWitness a b joined) := by
  unfold compatible cert certP7 certC4 Function.Injective
  decide +kernel

/-- In any host realizing the two attachment patterns, the outside vertices are
independent, and their ordered or reversed pair is in the explicit list of 42. -/
theorem pair_constraint {α : Type*} {G : SimpleGraph α} {f : Fin 9 → α}
    {a b : Fin 14} {joined : Bool} (hr : Realizes G f (pairModel a b joined))
    (hc : noC4 G) (hp : noP7 G) : joined = false ∧
    ((mask a, mask b) ∈ HeptagonCore.allowedPairs ∨ (mask b, mask a) ∈ HeptagonCore.allowedPairs) :=
  (pair_cases a b joined).resolve_right (no_certificate hr hc hp _)

private theorem masks_represent_shapes : ∀ r : Fin 7,
    (∃ a : Fin 14, ∀ i : Fin 7, decide (i = r ∨ i = r + 3) = (mask a).testBit i) ∧
    (∃ a : Fin 14, ∀ i : Fin 7, decide (i = r ∨ i = r+1 ∨ i = r+4) = (mask a).testBit i) := by
  decide +kernel

/-- Each nonempty exterior neighborhood is one of the 14 numerical masks, with
its membership bits equal to the host's actual adjacency decisions. -/
theorem mask_exists {α : Type*} {G : SimpleGraph α} [DecidableRel G.Adj]
    (e : cycleGraph 7 ↪g G) {x : α} (hx : ∀ i, x ≠ e i) (hit : ∃ i, G.Adj x (e i))
    (hc : noC4 G) (hp : noP7 G) : ∃ a : Fin 14, ∀ i : Fin 7,
    G.Adj x (e i) ↔ (mask a).testBit i = true := by
  obtain ⟨r, hb | hb⟩ := external_neighborhood e x hx hit hc hp
  · obtain ⟨a,ha⟩ := (masks_represent_shapes r).1
    exact ⟨a,fun i => by rw [← ha i, ← hb i]; simp⟩
  · obtain ⟨a,ha⟩ := (masks_represent_shapes r).2
    exact ⟨a,fun i => by rw [← ha i, ← hb i]; simp⟩

/-- The host itself gives a faithful labeling of the induced subgraph on the
cycle and the two prescribed outside vertices. Consequently there is no
adjacency between them and their distinct masks belong to the 42-pair table. -/
theorem actual_pair {α : Type*} {G : SimpleGraph α} [DecidableRel G.Adj]
    (e : cycleGraph 7 ↪g G) {v w : α} (hv : ∀ i, v ≠ e i) (hw : ∀ i, w ≠ e i)
    (hvw : v ≠ w) (a b : Fin 14)
    (ha : ∀ i : Fin 7, G.Adj v (e i) ↔ (mask a).testBit i = true)
    (hb : ∀ i : Fin 7, G.Adj w (e i) ↔ (mask b).testBit i = true)
    (hc : noC4 G) (hp : noP7 G) : ¬G.Adj v w ∧
    ((mask a, mask b) ∈ HeptagonCore.allowedPairs ∨ (mask b, mask a) ∈ HeptagonCore.allowedPairs) := by
  have hbase : Realizes G (fun i => e i) cycleAdj :=
    ⟨e.injective, fun i j => by simp [cycleAdj, e.map_rel_iff]⟩
  let f := Fin.lastCases (motive := fun _ : Fin 8 => α) v (fun i => e i)
  have h1 := realize_add hbase hv _ ha
  have fresh : ∀ i, w ≠ f i := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [f, Fin.lastCases_last] using Ne.symm hvw
    · simpa only [f, Fin.lastCases_castSucc] using hw j
  let joined := decide (G.Adj w v)
  have hb' : ∀ i : Fin 8, G.Adj w (f i) ↔
      Fin.lastCases joined (fun i : Fin 7 => (mask b).testBit i) i = true := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [f, joined, Fin.lastCases_last, decide_eq_true_eq]
    · simpa [f] using hb j
  have hr := realize_add h1 fresh _ hb'
  have h := pair_constraint (a := a) (b := b) (joined := joined) hr hc hp
  exact ⟨fun he => (by simpa [joined] using h.1 : ¬G.Adj w v) he.symm, h.2⟩

/- The finite compatibility graph has no four-clique. Premises are interleaved
with the vertices so that nonedges discard the whole branch of the check. -/
set_option synthInstance.maxSize 2048 in
set_option maxHeartbeats 9000000 in
set_option maxRecDepth 10000 in
private theorem no_four_masks : ∀ a b : Fin 14, compatible a b →
    ∀ c : Fin 14, compatible a c → compatible b c →
    ∀ d : Fin 14, compatible a d → compatible b d → compatible c d → False := by
  unfold compatible
  decide +kernel

/-- All vertices outside the cycle that have at least one neighbor on it. -/
def Outer {α : Type*} {G : SimpleGraph α} (e : cycleGraph 7 ↪g G) :=
  {v : α // (∀ i, v ≠ e i) ∧ ∃ i, G.Adj v (e i)}

noncomputable def typeOfVertex {α : Type*} {G : SimpleGraph α} [DecidableRel G.Adj]
    (e : cycleGraph 7 ↪g G) (hc : noC4 G) (hp : noP7 G) (v : Outer e) : Fin 14 :=
  Classical.choose (mask_exists e v.property.1 v.property.2 hc hp)

theorem actual_types_compatible {α : Type*} {G : SimpleGraph α} [DecidableRel G.Adj]
    {e : cycleGraph 7 ↪g G} (hc : noC4 G) (hp : noP7 G) {v w : Outer e} (h : v ≠ w) :
    ¬ G.Adj v.val w.val ∧ compatible (typeOfVertex e hc hp v) (typeOfVertex e hc hp w) := by
  apply actual_pair e v.property.1 w.property.1 (fun eq => h (Subtype.ext eq))
  · exact Classical.choose_spec (mask_exists e v.property.1 v.property.2 hc hp)
  · exact Classical.choose_spec (mask_exists e w.property.1 w.property.2 hc hp)
  · exact hc
  · exact hp

/-- The outside neighbors of an induced heptagon form an independent set. -/
theorem outer_independent {α : Type*} {G : SimpleGraph α} [DecidableRel G.Adj]
    {e : cycleGraph 7 ↪g G} (hc : noC4 G) (hp : noP7 G) (v w : Outer e) (h : v ≠ w) :
    ¬ G.Adj v.val w.val := (actual_types_compatible hc hp h).1

/-- At most three vertices outside the heptagon have any neighbor on it. -/
theorem at_most_three_outer {α : Type*} {G : SimpleGraph α} [DecidableRel G.Adj]
    (e : cycleGraph 7 ↪g G) [Fintype (Outer e)] (hc : noC4 G) (hp : noP7 G) :
    Fintype.card (Outer e) ≤ 3 := by
  by_contra! h
  let ⟨f⟩ := Function.Embedding.nonempty_of_card_le
    (by simp only [Fintype.card_fin]; omega : Fintype.card (Fin 4) ≤ Fintype.card (Outer e))
  let t (i : Fin 4) := typeOfVertex e hc hp (f i)
  have edge {i j : Fin 4} (hne : i ≠ j) : compatible (t i) (t j) :=
    (actual_types_compatible hc hp (f.injective.ne hne)).2
  exact no_four_masks (t 0) (t 1) (edge (by decide)) (t 2) (edge (by decide))
    (edge (by decide)) (t 3) (edge (by decide)) (edge (by decide)) (edge (by decide))

private theorem incompatible_self : ∀ a : Fin 14, ¬ compatible a a := by
  unfold compatible
  decide +kernel

theorem typeOfVertex_injective {α : Type*} {G : SimpleGraph α} [DecidableRel G.Adj]
    (e : cycleGraph 7 ↪g G) (hc : noC4 G) (hp : noP7 G) :
    Function.Injective (typeOfVertex e hc hp) := by
  intro a b eq
  by_contra h
  have hh := (actual_types_compatible hc hp h).2
  rw [eq] at hh
  exact incompatible_self _ hh

end HeptagonPairEncoding

namespace HeptagonSharedPair
variable {V T : Type*} [LinearOrder T] {R : V → V → Prop}

/-- A property checked once for each sorted triple of distinct types. The
edges in this relation stand for pairs with a shared remote neighbor. -/
def SortedUnique (t : V → T) (R : V → V → Prop) : Prop :=
  ∀ a b c, t a < t b → t b < t c →
    ¬(R a b ∧ R a c) ∧ ¬(R a b ∧ R b c) ∧ ¬(R a c ∧ R b c)

theorem one_at_vertex {t : V → T} (hinj : Function.Injective t)
    (hs : ∀ {u v : V}, R u v → R v u) (hcert : SortedUnique t R) {a b c : V}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (h1 : R a b) (h2 : R a c) : False := by
  have ab := hinj.ne hab
  have ac := hinj.ne hac
  have bc := hinj.ne hbc
  rcases lt_or_gt_of_ne ab with ab | ba
  · rcases lt_or_gt_of_ne bc with bc | cb
    · exact (hcert a b c ab bc).1 ⟨h1,h2⟩
    · rcases lt_or_gt_of_ne ac with ac | ca
      · exact (hcert a c b ac cb).1 ⟨h2,h1⟩
      · exact (hcert c a b ca ab).2.1 ⟨hs h2,h1⟩
  · rcases lt_or_gt_of_ne ac with ac | ca
    · exact (hcert b a c ba ac).2.1 ⟨hs h1,h2⟩
    · rcases lt_or_gt_of_ne bc with bc | cb
      · exact (hcert b c a bc ca).2.2 ⟨hs h1,hs h2⟩
      · exact (hcert c b a cb ba).2.2 ⟨hs h2,hs h1⟩

/-- On at most three vertices, checking each sorted triple suffices to prove
uniqueness of the entire unordered pair with a shared remote neighbor. -/
theorem unique_pair [Fintype V] {t : V → T} (hinj : Function.Injective t)
    (hs : ∀ {u v : V}, R u v → R v u) (hcert : SortedUnique t R) (hcard : Fintype.card V ≤ 3)
    {a b c d : V} (hab : a ≠ b) (hcd : c ≠ d) (h1 : R a b) (h2 : R c d) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  classical
  by_cases hac : a = c
  · subst c
    by_cases hbd : b = d
    · exact Or.inl ⟨rfl,hbd⟩
    · exact (one_at_vertex hinj hs hcert hab hcd hbd h1 h2).elim
  by_cases had : a = d
  · subst d
    by_cases hbc : b = c
    · exact Or.inr ⟨rfl,hbc⟩
    · exact (one_at_vertex hinj hs hcert hab hac hbc h1 (hs h2)).elim
  by_cases hbc : b = c
  · subst c
    exact (one_at_vertex hinj hs hcert hab.symm hcd had (hs h1) h2).elim
  by_cases hbd : b = d
  · subst d
    exact (one_at_vertex hinj hs hcert hab.symm hbc hac (hs h1) (hs h2)).elim
  have hfour : ({a,b,c,d} : Finset V).card = 4 := by
    simp [hab,hac,had,hbc,hbd,hcd]
  have hle := Finset.card_le_univ ({a,b,c,d} : Finset V)
  omega
end HeptagonSharedPair

/-! A remote vertex in the presence of three immediate attachments to the cycle.
Two remote vertices can never witness two different attachment pairs.
The numerical array records a forbidden C4 or induced P7 for every excluded
configuration. All vertices and all relevant adjacencies are checked in Lean. -/
namespace HeptagonTripleEncoding
open SimpleGraph HeptagonEncoding HeptagonPairEncoding

private def tripleList : Array (Fin 14 × Fin 14 × Fin 14) := #[(0, 1, 2), (0, 1, 10), (0, 2, 7), (0, 2, 12), (0, 3, 9), (0, 3, 12), (0, 7, 9), (0, 9, 10), (1, 2, 5), (1, 5, 11), (1, 5, 13), (1, 8, 10), (1, 8, 11), (1, 10, 13), (2, 4, 6), (2, 4, 7), (2, 5, 6), (2, 6, 12), (3, 5, 9), (3, 5, 13), (4, 6, 10), (4, 10, 13), (5, 6, 9), (5, 9, 11), (6, 8, 10), (6, 8, 12), (6, 9, 10), (7, 9, 11)]

def tripleCode (t : Fin 28) := tripleList[t.val]?.getD (0,0,0)

private def sharedList : Array Nat := #[5, 6, 0, 0, 0, 6, 0, 3, 5, 0, 0, 0, 6, 0, 0, 6, 5, 0, 0, 5, 0, 5, 5, 0, 0, 6, 5, 5]

def sharedCode (t : Fin 28) : Fin 8 := ⟨(sharedList[t.val]?.getD 0) % 8, by omega⟩

private def certificates : Array Nat := #[0, 443554117, 0, 35440, 445921030, 0, 39556, 35440, 0, 0, 444623154, 35440, 445859841, 39539, 0, 35440, 0, 443762065, 444872454, 424970864, 445989744, 407214704, 39553, 39553, 0, 443553861, 444873056, 444873056, 445859856, 39539, 386308740, 39539, 0, 443754853, 444880530, 35440, 445789312, 445789312, 446039860, 35440, 0, 0, 444880530, 35440, 446059649, 39539, 0, 35440, 0, 443762049, 444941168, 426084979, 446039860, 360880752, 39554, 39554, 0, 443754597, 444991284, 0, 0, 39539, 39558, 39539, 0, 443832594, 0, 35444, 445712195, 0, 39553, 39553, 0, 443832338, 444941200, 444941200, 445859201, 39536, 390306433, 39536, 0, 443832609, 444663619, 311790192, 445789296, 443832338, 39557, 39557, 0, 443574578, 444873056, 35444, 445859856, 445859856, 445859585, 35444, 0, 0, 444950834, 35444, 446060562, 39536, 0, 39536, 0, 443832609, 444811009, 421759600, 445789296, 405969520, 39558, 39558, 0, 443623766, 444881185, 35444, 445990672, 396960640, 445990672, 35444, 0, 0, 444622226, 35444, 445997187, 39537, 0, 39537, 0, 443623766, 0, 35441, 445990672, 0, 39557, 35441, 0, 443824480, 444942096, 396896608, 445859600, 408328817, 39554, 39554, 0, 443831954, 444950819, 35441, 445789296, 408189586, 445789296, 35441, 0, 443574563, 0, 35441, 445789296, 0, 39557, 35441, 0, 443832353, 444741984, 444741984, 446060577, 39539, 361403248, 39539, 0, 443832609, 0, 35443, 445990657, 0, 39558, 35443, 0, 443902243, 0, 35445, 445781844, 0, 39554, 39554, 0, 443892624, 444733268, 396895120, 445859185, 443901987, 39558, 39558, 0, 443693408, 444873056, 35445, 445859856, 445859856, 446060321, 35445, 0, 0, 444873056, 35445, 445859856, 39538, 0, 39538, 0, 443693408, 0, 35442, 446060321, 0, 39558, 35442, 0, 443892624, 0, 35442, 445859185, 0, 39558, 35442]

private def bits3 (a b c : Bool) := a.toNat + 2*b.toNat + 4*c.toNat

private def thirdRow (c : Fin 14) : Fin 9 → Bool :=
  Fin.lastCases false (Fin.lastCases false (fun i : Fin 7 => (mask c).testBit i))

private def remoteRow (a b c : Bool) : Fin 10 → Bool :=
  Fin.lastCases c (Fin.lastCases b (Fin.lastCases a (fun _ : Fin 7 => false)))

private def permitted (t : Fin 8) (a b c : Bool) : Prop :=
  let s := bits3 a b c
  s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 4 ∨ (s = t.val ∧ (s = 3 ∨ s = 5 ∨ s = 6))

set_option synthInstance.maxSize 8192 in
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 10000 in
private theorem sorted_triple : ∀ a b c : Fin 14,
    (a < b ∧ b < c ∧ compatible a b ∧ compatible b c ∧ compatible a c) →
    ∃ t : Fin 28, tripleCode t = (a,b,c) := by
  unfold compatible
  decide +kernel

set_option synthInstance.maxSize 4096 in
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 10000 in
private theorem remote_cases : ∀ (t : Fin 28) (a b c : Bool),
    permitted (sharedCode t) a b c ∨
    cert (addVertex (addVertex (pairModel (tripleCode t).1 (tripleCode t).2.1 false)
      (thirdRow (tripleCode t).2.2)) (remoteRow a b c))
      (certificates[t.val*8 + bits3 a b c]?.getD 0) := by
  unfold permitted cert certP7 certC4 Function.Injective
  decide +kernel

private theorem fresh_add {α : Type*} {n : ℕ} {z v : α} {f : Fin n → α}
    (hv : z ≠ v) (hf : ∀ i, z ≠ f i) : ∀ i, z ≠ Fin.lastCases v f i := by
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa only [Fin.lastCases_last] using hv
  · simpa only [Fin.lastCases_castSucc] using hf j

private theorem adj_add {α : Type*} {n : ℕ} {G : SimpleGraph α} {z v : α}
    {f : Fin n → α} {s : Fin n → Bool} {b : Bool}
    (hv : G.Adj z v ↔ b = true) (hf : ∀ i, G.Adj z (f i) ↔ s i = true) :
    ∀ i, G.Adj z (Fin.lastCases v f i) ↔ Fin.lastCases b s i = true := by
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa only [Fin.lastCases_last] using hv
  · simpa only [Fin.lastCases_castSucc] using hf j

private theorem consecutive : ∀ i : Fin 7, (cycleGraph 7).Adj i (i+1) := by decide +kernel

private theorem actual_remote_pair {α : Type*} {G : SimpleGraph α} [DecidableRel G.Adj]
    (e : cycleGraph 7 ↪g G) (hc : noC4 G) (hp : noP7 G) (a b c : Outer e)
    (ab : a ≠ b) (bc : b ≠ c) (ac : a ≠ c) {t : Fin 28}
    (ht : tripleCode t = (typeOfVertex e hc hp a, typeOfVertex e hc hp b, typeOfVertex e hc hp c))
    (z : α) (hz : ∀ i, ¬G.Adj z (e i)) :
    permitted (sharedCode t) (decide (G.Adj z a.val)) (decide (G.Adj z b.val)) (decide (G.Adj z c.val)) := by
  have ht₀ : Realizes G (fun i => e i) cycleAdj :=
    ⟨e.injective,fun i j => by simp [cycleAdj,e.map_rel_iff]⟩
  have hA := Classical.choose_spec (mask_exists e a.property.1 a.property.2 hc hp)
  have hB := Classical.choose_spec (mask_exists e b.property.1 b.property.2 hc hp)
  have hC := Classical.choose_spec (mask_exists e c.property.1 c.property.2 hc hp)
  have ha := realize_add ht₀ a.property.1 _ hA
  have nAB : b.val ≠ a.val := fun he => ab (Subtype.ext he.symm)
  have nAC : c.val ≠ a.val := fun he => ac (Subtype.ext he.symm)
  have nBC : c.val ≠ b.val := fun he => bc (Subtype.ext he.symm)
  have noBA : G.Adj b.val a.val ↔ false = true := by simp [outer_independent hc hp b a ab.symm]
  have noCA : G.Adj c.val a.val ↔ false = true := by simp [outer_independent hc hp c a ac.symm]
  have noCB : G.Adj c.val b.val ↔ false = true := by simp [outer_independent hc hp c b bc.symm]
  have hab := realize_add ha (fresh_add nAB b.property.1) _ (adj_add noBA hB)
  have habc := realize_add hab (fresh_add nBC (fresh_add nAC c.property.1)) _ (adj_add noCB (adj_add noCA hC))
  have nz : ∀ v : Outer e, z ≠ v.val := by
    intro v eq
    obtain ⟨i,hi⟩ := v.property.2
    exact hz i (eq ▸ hi)
  have nzcycle : ∀ i, z ≠ e i := by
    intro i eq
    exact hz (i+1) (eq ▸ e.map_rel_iff.mpr (consecutive i))
  have zbase : ∀ i, G.Adj z (e i) ↔ false = true := fun i => by simp [hz]
  have zsingle (v : Outer e) : G.Adj z v.val ↔ decide (G.Adj z v.val) = true := by simp
  have hzall := realize_add habc (fresh_add (nz c) (fresh_add (nz b) (fresh_add (nz a) nzcycle))) _
    (adj_add (zsingle c) (adj_add (zsingle b) (adj_add (zsingle a) zbase)))
  have choices := remote_cases t (decide (G.Adj z a.val)) (decide (G.Adj z b.val)) (decide (G.Adj z c.val))
  apply choices.resolve_right
  rw [ht]
  exact no_certificate hzall hc hp _

private def distinctPairs (a b c d e f : Prop) : Prop :=
  ((a ∧ b) → ¬((d ∧ f) ∨ (e ∧ f))) ∧
  ((a ∧ c) → ¬((d ∧ e) ∨ (e ∧ f))) ∧
  ((b ∧ c) → ¬((d ∧ e) ∨ (d ∧ f)))

set_option synthInstance.maxSize 2048 in
private theorem resolve_masks : ∀ (s : Fin 8) (a b c d e f : Bool),
    permitted s a b c → permitted s d e f →
    distinctPairs (a=true) (b=true) (c=true) (d=true) (e=true) (f=true) := by
  unfold permitted distinctPairs
  decide +kernel

theorem sorted_no_overlap {α : Type*} {G : SimpleGraph α} [DecidableRel G.Adj]
    (e : cycleGraph 7 ↪g G) (hc : noC4 G) (hp : noP7 G) (a b c : Outer e)
    (hab : typeOfVertex e hc hp a < typeOfVertex e hc hp b)
    (hbc : typeOfVertex e hc hp b < typeOfVertex e hc hp c)
    (z w : α) (hz : ∀ i, ¬ G.Adj z (e i)) (hw : ∀ i, ¬ G.Adj w (e i)) :
    ((G.Adj z a.val ∧ G.Adj z b.val) → ¬((G.Adj w a.val ∧ G.Adj w c.val) ∨ (G.Adj w b.val ∧ G.Adj w c.val))) ∧
    ((G.Adj z a.val ∧ G.Adj z c.val) → ¬((G.Adj w a.val ∧ G.Adj w b.val) ∨ (G.Adj w b.val ∧ G.Adj w c.val))) ∧
    ((G.Adj z b.val ∧ G.Adj z c.val) → ¬((G.Adj w a.val ∧ G.Adj w b.val) ∨ (G.Adj w a.val ∧ G.Adj w c.val))) := by
  have ab : a ≠ b := fun h => ne_of_lt hab (congrArg _ h)
  have bc : b ≠ c := fun h => ne_of_lt hbc (congrArg _ h)
  have ac : a ≠ c := fun h => ne_of_lt (lt_trans hab hbc) (congrArg _ h)
  obtain ⟨t,ht⟩ := sorted_triple _ _ _ ⟨hab,hbc,(actual_types_compatible hc hp ab).2,
    (actual_types_compatible hc hp bc).2,(actual_types_compatible hc hp ac).2⟩
  have h := resolve_masks (sharedCode t) _ _ _ _ _ _
    (actual_remote_pair e hc hp a b c ab bc ac ht z hz)
    (actual_remote_pair e hc hp a b c ab bc ac ht w hw)
  simpa only [distinctPairs,decide_eq_true_eq] using h

end HeptagonTripleEncoding

namespace HeptagonRemotePair
open SimpleGraph HeptagonPairEncoding HeptagonEncoding HeptagonSharedPair

variable {V : Type*} {G : SimpleGraph V} [DecidableRel G.Adj]
def RemotePair (e : cycleGraph 7 ↪g G) (a b : Outer e) : Prop :=
  ∃ z : V, (∀ i, ¬ G.Adj z (e i)) ∧ G.Adj z a.val ∧ G.Adj z b.val

def TripleBound (e : cycleGraph 7 ↪g G) (hc : noC4 G) (hp : noP7 G) : Prop :=
  ∀ (a b c : Outer e), typeOfVertex e hc hp a < typeOfVertex e hc hp b →
    typeOfVertex e hc hp b < typeOfVertex e hc hp c → ∀ z w : V,
    (∀ i, ¬G.Adj z (e i)) → (∀ i, ¬G.Adj w (e i)) →
    ((G.Adj z a.val ∧ G.Adj z b.val → ¬(G.Adj w a.val ∧ G.Adj w c.val) ∧ ¬(G.Adj w b.val ∧ G.Adj w c.val)) ∧
    (G.Adj z a.val ∧ G.Adj z c.val → ¬(G.Adj w a.val ∧ G.Adj w b.val) ∧ ¬(G.Adj w b.val ∧ G.Adj w c.val)) ∧
    (G.Adj z b.val ∧ G.Adj z c.val → ¬(G.Adj w a.val ∧ G.Adj w b.val) ∧ ¬(G.Adj w a.val ∧ G.Adj w c.val)))

theorem verified_triples (e : cycleGraph 7 ↪g G) (hc : noC4 G) (hp : noP7 G) : TripleBound e hc hp := by
  intro a b c hab hbc z w hz hw
  simpa only [not_or] using HeptagonTripleEncoding.sorted_no_overlap e hc hp a b c hab hbc z w hz hw

theorem host_unique (e : cycleGraph 7 ↪g G) [Fintype (Outer e)]
    (hc : noC4 G) (hp : noP7 G) (bh : TripleBound e hc hp)
    (a b c d : Outer e) (hab : a ≠ b) (hcd : c ≠ d) (h1 : RemotePair e a b) (h2 : RemotePair e c d) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  have hs {u v : Outer e} (h : RemotePair e u v) : RemotePair e v u := by
    obtain ⟨z,hz,hu,hv⟩ := h
    exact ⟨z,hz,hv,hu⟩
  have sorted : SortedUnique (typeOfVertex e hc hp) (RemotePair e) := by
    intro a b c hab hbc
    constructor
    · rintro ⟨⟨z,hz,hza,hzb⟩,⟨w,hw,hwa,hwc⟩⟩
      exact ((bh a b c hab hbc z w hz hw).1 ⟨hza,hzb⟩).1 ⟨hwa,hwc⟩
    constructor
    · rintro ⟨⟨z,hz,hza,hzb⟩,⟨w,hw,hwb,hwc⟩⟩
      exact ((bh a b c hab hbc z w hz hw).1 ⟨hza,hzb⟩).2 ⟨hwb,hwc⟩
    · rintro ⟨⟨z,hz,hza,hzc⟩,⟨w,hw,hwb,hwc⟩⟩
      exact ((bh a b c hab hbc z w hz hw).2.1 ⟨hza,hzc⟩).2 ⟨hwb,hwc⟩
  exact unique_pair (typeOfVertex_injective e hc hp) hs sorted (at_most_three_outer e hc hp) hab hcd h1 h2

/-- The core-level API accepts ordinary host vertices. Only the conversion from
membership in the chosen core and attachment sets is exposed to callers. -/
theorem core_pair (e : cycleGraph 7 ↪g G) [Fintype (Outer e)] (hc : noC4 G) (hp : noP7 G)
    (X K : Finset V)
    (ho : ∀ a ∈ X, (∀ i, a ≠ e i) ∧ ∃ i, G.Adj a (e i))
    (hr : ∀ u ∉ K, ∀ i, ¬G.Adj u (e i)) :
    ∀ u ∉ K, ∀ v ∉ K, ∀ a ∈ X, ∀ b ∈ X, ∀ c ∈ X, ∀ d ∈ X,
      a ≠ b → c ≠ d → G.Adj a u → G.Adj b u → G.Adj c v → G.Adj d v →
      (a=c ∧ b=d) ∨ (a=d ∧ b=c) := by
  intro u hu v hv a ha b hb c hc' d hd hab hcd hau hbu hcv hdv
  have he := host_unique e hc hp (verified_triples e hc hp) ⟨a,ho a ha⟩ ⟨b,ho b hb⟩ ⟨c,ho c hc'⟩ ⟨d,ho d hd⟩
    (fun h => hab (congrArg Subtype.val h)) (fun h => hcd (congrArg Subtype.val h))
    ⟨u,hr u hu,hau.symm,hbu.symm⟩ ⟨v,hr v hv,hcv.symm,hdv.symm⟩
  rcases he with ⟨ac,bd⟩ | ⟨ad,bc⟩
  · exact Or.inl ⟨congrArg Subtype.val ac, congrArg Subtype.val bd⟩
  · exact Or.inr ⟨congrArg Subtype.val ad, congrArg Subtype.val bc⟩
end HeptagonRemotePair

/-! Assembly of the host counting inequality for the induced-heptagon reduction. -/
namespace HeptagonAssembly

open SimpleGraph Finset HeptagonHost HeptagonPieces

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

def Shared (G : SimpleGraph V) (X : Finset V) (v : V) : Prop :=
  ∃ a ∈ X, ∃ b ∈ X, a ≠ b ∧ G.Adj a v ∧ G.Adj b v

omit [Fintype V] [DecidableEq V] in
/-- Conversion from a unique possible pair to a unique external vertex witnessing it. -/
theorem shared_vertex_from_pair (hs : SquareFree G) (K X : Finset V)
    (hpair : ∀ u ∉ K, ∀ v ∉ K, ∀ a ∈ X, ∀ b ∈ X, ∀ c ∈ X, ∀ d ∈ X,
      a ≠ b → c ≠ d → G.Adj a u → G.Adj b u → G.Adj c v → G.Adj d v →
      (a = c ∧ b = d) ∨ (a = d ∧ b = c)) :
    ∀ u ∉ K, ∀ v ∉ K, Shared G X u → Shared G X v → u = v := by
  intro u hu v hv
  rintro ⟨a,ha,b,hb,hab,hua,hub⟩ ⟨c,hc,d,hd,hcd,hvc,hvd⟩
  exact shared_vertex_unique hs hab ⟨hua,hub⟩ ⟨hvc,hvd⟩
    (hpair u hu v hv a ha b hb c hc d hd hab hcd hua hub hvc hvd)

/-- The componentwise estimates imply the conclusion for the whole graph. Components here
are the actual connected components of the complement of the proposed core. -/
theorem whole_graph [Nonempty V] [DecidableRel G.Adj] (K X : Finset V) (hs : SquareFree G)
    (hcore : surplusOn G K ≤ -4)
    (hshared : ∀ u ∉ K, ∀ v ∉ K, Shared G X u → Shared G X v → u = v)
    (hp : ∀ i : PieceIndex G K,
      (surplusOn G (K ∪ piece G K i) - surplusOn G K ≤ 3) ∧
      (0 < surplusOn G (K ∪ piece G K i) - surplusOn G K → ∃ v ∈ piece G K i, Shared G X v)) :
    G.l ≤ 3 := by
  classical
  let _ := Fintype.ofFinite (PieceIndex G K)
  let excess (i : PieceIndex G K) := surplusOn G (K ∪ piece G K i) - surplusOn G K
  have hunique (i j : PieceIndex G K) (hi : 0 < excess i) (hj : 0 < excess j) : i = j := by
    obtain ⟨u,hu,hux⟩ := (hp i).2 hi
    obtain ⟨v,hv,hvx⟩ := (hp j).2 hj
    have huv := hshared u (mem_piece.mp hu).choose v (mem_piece.mp hv).choose hux hvx
    exact (outside_unique (G := G) (mem_piece.mp hv).choose).unique (huv ▸ hu) hv
  have bound := combine_surpluses (Finset.univ : Finset (PieceIndex G K)) excess hcore
    (fun i _ => (hp i).1) (fun i _ j _ => hunique i j)
  have allsum := surplus_on_bags G K (piece G K)
    (fun _ h => outside_unique h)
    (fun i j hij _ hv _ hw => no_cross_edges hij hv hw)
  apply average_bound_of_surplus G hs
  change surplusOn G K + ∑ i, (surplusOn G (K ∪ piece G K i) - surplusOn G K) ≤ -1 at bound
  omega

open HeptagonEncoding HeptagonPairEncoding HeptagonCycle

/-- The heptagon case of the local-independence bound, in the actual upstream definitions. -/
theorem heptagon_bound [Nonempty V] [DecidableRel G.Adj] (e : cycleGraph 7 ↪g G)
    (hc : G.Connected) (hs : SquareFree G) (h6 : G.path ≤ 6) : G.l ≤ 3 := by
  classical
  let C := vertices e
  let X := univ.filter (fun x : V => (∀ i, x ≠ e i) ∧ ∃ i, G.Adj x (e i))
  let K := C ∪ X
  let _ : Fintype (Outer e) := by unfold Outer; infer_instance
  have memC {x : V} : x ∈ C ↔ ∃ i, e i = x := by simp [C,vertices]
  have memX {x : V} : x ∈ X ↔ (∀ i, x ≠ e i) ∧ ∃ i, G.Adj x (e i) := by simp [X]
  have off {x : V} (hx : x ∉ K) : (∀ i, x ≠ e i) ∧ ∀ i, ¬ G.Adj x (e i) := by
    have hnc : x ∉ C := fun h => hx (mem_union_left _ h)
    have hnx : x ∉ X := fun h => hx (mem_union_right _ h)
    have ho (i : Fin 7) : x ≠ e i := fun h => hnc (memC.mpr ⟨i,h.symm⟩)
    exact ⟨ho,fun i h => hnx (memX.mpr ⟨ho,i,h⟩)⟩
  have hP := noP7_of_path_le h6
  have hdis : Disjoint C X := by
    apply Finset.disjoint_left.mpr
    intro x hx hxx
    obtain ⟨i,rfl⟩ := memC.mp hx
    exact (memX.mp hxx).1 i rfl
  have hcard : X.card ≤ 3 := by
    let f (x : X) : Outer e := ⟨x.val,memX.mp x.property⟩
    have hf : Function.Injective f := fun a b he => Subtype.ext (congrArg (fun z : Outer e => z.val) he)
    have h := (Fintype.card_le_of_injective f hf).trans (at_most_three_outer e hs hP)
    simpa using h
  have hind : G.IsIndepSet (X : Set V) := by
    intro x hx y hy hxy
    exact outer_independent hs hP (show Outer e from ⟨x,memX.mp hx⟩)
      (show Outer e from ⟨y,memX.mp hy⟩) (fun h => hxy (congrArg Subtype.val h))
  have hallowed (x : V) (hx : x ∈ X) : allowed (fun i => decide (G.Adj x (e i))) :=
    external_neighborhood e x (memX.mp hx).1 (memX.mp hx).2 hs hP
  have hcore := HeptagonCoreCount.cycle_core_surplus G e X hdis hcard hind hallowed
  have hk : K.Nonempty := ⟨e 0, mem_union_left _ (memC.mpr ⟨0,rfl⟩)⟩
  apply whole_graph K X hs hcore
  · apply shared_vertex_from_pair hs
    exact HeptagonRemotePair.core_pair e hs hP X K (fun _ h => memX.mp h) (fun _ h => (off h).2)
  · intro i
    let F := piece G K i
    have hnot {v} (hv : v ∈ F) : v ∉ K := (mem_piece.mp hv).choose
    have htouch (x : V) (hx : x ∈ K) (v : V) (hv : v ∈ F) (hxv : G.Adj x v) : x ∈ X := by
      rcases mem_union.mp hx with hxc | hxx
      · obtain ⟨j,rfl⟩ := memC.mp hxc
        exact ((off (hnot hv)).2 j hxv.symm).elim
      · exact hxx
    have hroot (x : V) (hx : x ∈ X) : NoOuterP4 G x F := by
      obtain ⟨p,hp,q,hq,t,ht,hr⟩ := root_path e x (fun h => Finset.disjoint_left.mp hdis h hx) (hallowed x hx)
      have away (v : V) (hv : v ∈ F) (w : V) (hw : w ∈ C) : v ≠ w ∧ ¬ G.Adj v w := by
        obtain ⟨j,rfl⟩ := memC.mp hw
        exact ⟨(off (hnot hv)).1 j,(off (hnot hv)).2 j⟩
      intro a b c ha hb hcc
      have inF : ∀ z ∈ [a,b,c], z ∈ F := by simpa using And.intro ha (And.intro hb hcc)
      have inC : ∀ z ∈ [p,q,t], z ∈ C := by simpa using And.intro hp (And.intro hq ht)
      apply HeptagonPathLink.no_extension h6 hr
        (fun z hz w hw => away z (inF z hz) w (inC w hw))
      intro z hz eq
      exact hnot (inF z hz) (eq ▸ mem_union_right _ hx)
    obtain ⟨v,hv,x,hx,hvx⟩ := touches_core hc hk i
    have h := HeptagonOuter.piece_surplus G hs (disjoint_core i) htouch hcard hind (preconnected i)
      ⟨x,hx,v,hv,hvx.symm⟩ hroot
    refine ⟨h.1,?_⟩
    intro hp
    obtain ⟨a,ha,b,hb,hab,v,hv,hav,hbv⟩ := h.2 hp
    exact ⟨v,hv,a,ha,b,hb,hab,hav,hbv⟩

end HeptagonAssembly

theorem OMA.solution : OMA.R_WrittenOnTheWallII_GraphConjecture133_conjecture133_R1_H1_R1_H2_R1_H1_R1.H1 := by
  classical
  intro α _ _ _ G hc hs _ h6 _ _ he
  obtain ⟨e⟩ := he
  exact HeptagonAssembly.heptagon_bound e hc hs h6.le
