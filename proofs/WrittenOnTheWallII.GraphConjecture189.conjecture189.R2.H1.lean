import OMAReductions.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R2
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Nodup
import Mathlib.Data.Multiset.Sort
import Mathlib.SetTheory.Cardinal.Finite

section
/-!
The parity estimate in Easwar–Johari, §5, applied directly to arbitrary sides
of a separating vertex. The side need not have been constructed as a block.
-/


namespace Graph189CutCore
open SimpleGraph Finset
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- The defining expression of the upstream even-distance invariant. -/
noncomputable def evenCard (G : SimpleGraph V) (v : V) : ℕ :=
  (Finset.univ.filter fun y => Even (G.dist v y)).card

/-- The defining expression of the upstream degree sequence. -/
noncomputable def sortedDegrees (G : SimpleGraph V) [DecidableRel G.Adj] : List ℕ :=
  (Finset.univ.val.map fun v : V => G.degree v).sort (· ≤ ·)

/-- The defining expression of the upstream second-smallest degree. -/
noncomputable def secondDegree (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (sortedDegrees G).getD 1 0

/-- All edges leaving a nonempty side pass through the gate. -/
structure Side (G : SimpleGraph V) (c : V) (S : Finset V) : Prop where
  nonempty : S.Nonempty
  outside : c ∉ S
  exit_eq : ∀ {u v}, u ∈ S → G.Adj u v → v ∉ S → v = c

omit [Fintype V] [DecidableEq V] in
theorem Side.contact {c : V} {S : Finset V} (h : Side G c S) (hc : G.Connected) :
    ∃ x ∈ S, G.Adj x c := by
  obtain ⟨w,hw⟩ := h.nonempty
  obtain ⟨P⟩ := hc w c
  obtain ⟨d, _, hin, hout⟩ := P.exists_boundary_dart (S : Set V) hw h.outside
  exact ⟨d.fst,hin,h.exit_eq hin d.adj hout ▸ d.adj⟩

omit [Fintype V] in
theorem Side.dist_add {c x y : V} {S : Finset V} (h : Side G c S)
    (hc : G.Connected) (hx : x ∈ S) (hy : y ∉ S) :
    G.dist x y = G.dist x c + G.dist c y := by
  obtain ⟨P,hP⟩ := hc.exists_walk_length_eq_dist x y
  obtain ⟨d, hd, hin, hout⟩ := P.exists_boundary_dart (S : Set V) hx hy
  have hm : c ∈ P.support := h.exit_eq hin d.adj hout ▸ P.dart_snd_mem_support_of_mem_darts hd
  have hsum := congrArg Walk.length (P.take_spec hm)
  rw [Walk.length_append, hP] at hsum
  exact le_antisymm hc.dist_triangle (by
    have := G.dist_le (P.takeUntil c hm)
    have := G.dist_le (P.dropUntil c hm)
    omega)

theorem Side.parity_bound {c : V} {S : Finset V} (h : Side G c S)
    (hc : G.Connected) {k : ℕ} (hσ : ∀ v, evenCard G v ≤ 1 + k) :
    Sᶜ.card + (S.filter (fun y => Even (G.dist c y))).card + 1 ≤ 2*k+2 := by
  classical
  obtain ⟨x,hx,hxc⟩ := h.contact hc
  let E (v : V) := univ.filter (fun y => Even (G.dist v y))
  let A := S.filter (fun y => Even (G.dist c y))
  have hxA : x ∉ A := by simp [A,dist_eq_one_iff_adj.mpr hxc.symm]
  have hdis : Disjoint (insert x A) Sᶜ := by
    apply Finset.disjoint_left.mpr
    intro y hy hys
    have h' : y ∈ S := by
      rcases mem_insert.mp hy with rfl | hh
      · exact hx
      · exact (mem_filter.mp hh).1
    exact (mem_compl.mp hys) h'
  have hin : insert x A ∪ Sᶜ ⊆ E c ∪ E x := by
    intro y hy
    rcases mem_union.mp hy with hm | hm
    · rcases mem_insert.mp hm with rfl | ha
      · exact mem_union_right _ (by simp [E])
      · exact mem_union_left _ (by simpa [E] using (mem_filter.mp ha).2)
    · have hd := h.dist_add hc hx (mem_compl.mp hm)
      rw [dist_eq_one_iff_adj.mpr hxc] at hd
      simp only [E, mem_union, mem_filter, mem_univ, true_and, Nat.even_iff]
      omega
  have hu := (card_le_card hin).trans (card_union_le (E c) (E x))
  rw [card_union_of_disjoint hdis, card_insert_of_notMem hxA] at hu
  have h1 : (E c).card ≤ 1+k := hσ c
  have h2 : (E x).card ≤ 1+k := hσ x
  change Sᶜ.card + A.card + 1 ≤ 2*k+2
  omega

/-- In a graph of order above the small-order threshold, every branch
contains two vertices, and consequently contains a vertex of high degree. -/
theorem Side.card_bounds [DecidableRel G.Adj] {c : V} {S : Finset V} (h : Side G c S)
    (hc : G.Connected) {k : ℕ} (hσ : ∀ v, evenCard G v ≤ 1+k)
    (horder : 2*k+3 ≤ Fintype.card V)
    (hpair : ∀ x y : V, x ≠ y → k ≤ G.degree x ∨ k ≤ G.degree y) :
    2 ≤ S.card ∧ k ≤ S.card ∧ Sᶜ.card ≤ 2*k+1 := by
  classical
  have hb := h.parity_bound hc hσ
  have hcs := card_add_card_compl S
  have h2 : 1 < S.card := by omega
  obtain ⟨x,hx,y,hy,hne⟩ := one_lt_card.mp h2
  have deg (v : V) (hv : v ∈ S) : G.degree v ≤ S.card := by
    have hin : G.neighborFinset v ⊆ insert c (S.erase v) := by
      intro w hw
      have he : G.Adj v w := by simpa using hw
      by_cases h' : w ∈ S
      · exact mem_insert_of_mem (mem_erase.mpr ⟨he.ne.symm,h'⟩)
      · exact mem_insert.mpr (Or.inl (h.exit_eq hv he h'))
    have hh := card_le_card hin
    rw [card_neighborFinset_eq_degree, card_insert_of_notMem (by
      exact fun hm => h.outside (mem_of_mem_erase hm)), card_erase_of_mem hv] at hh
    omega
  exact ⟨by omega, (hpair x y hne).elim (·.trans (deg x hx)) (·.trans (deg y hy)), by omega⟩

omit [Fintype V] [DecidableEq V] in
/-- If a branch contains a nonneighbor of its gate, it contains a vertex
at distance exactly two from the gate. -/
theorem Side.exists_distance_two {c : V} {S : Finset V} (h : Side G c S)
    (hc : G.Connected) {v : V} (hv : v ∈ S) (hn : ¬ G.Adj c v) :
    ∃ u ∈ S, G.dist c u = 2 := by
  classical
  obtain ⟨P⟩ := hc v c
  let far : Set V := {u | u ∈ S ∧ ¬ G.Adj c u}
  have hnot : c ∉ far := fun hm => h.outside hm.1
  obtain ⟨d,_,hin,hout⟩ := P.exists_boundary_dart far ⟨hv, hn⟩ hnot
  have hnear : G.Adj c d.snd := by
    by_contra hh
    have h' : d.snd ∉ S := fun hs => hout ⟨hs,hh⟩
    have heq := h.exit_eq hin.1 d.adj h'
    exact hin.2 (heq ▸ d.adj.symm)
  let Q : G.Walk c d.fst := .cons hnear (.cons d.adj.symm .nil)
  have hle : G.dist c d.fst ≤ 2 := G.dist_le Q
  have hlt := hc.one_lt_dist_of_ne_of_not_adj
    (show c ≠ d.fst from fun he => h.outside (he ▸ hin.1)) hin.2
  exact ⟨d.fst, hin.1, by omega⟩

/-- At a branching cut, two other large branches exhaust both parity budgets.
This forces every vertex in the first branch to touch the gate. -/
theorem Side.full_contact_of_two_other_sides {c : V} {S T U : Finset V}
    (hS : Side G c S) (hT : Side G c T) (hU : Side G c U)
    (hST : Disjoint S T) (hSU : Disjoint S U) (hTU : Disjoint T U)
    (hc : G.Connected) {k : ℕ} (hσ : ∀ v, evenCard G v ≤ 1+k)
    (ht : k ≤ T.card) (hu : k ≤ U.card) :
    ∀ x ∈ S, G.Adj c x := by
  classical
  have hdis : c ∉ T ∪ U := fun hm => (mem_union.mp hm).elim hT.outside hU.outside
  have hin : insert c (T ∪ U) ⊆ Sᶜ := by
    intro v hv
    apply mem_compl.mpr
    rcases mem_insert.mp hv with rfl | hv
    · exact hS.outside
    · rcases mem_union.mp hv with ht | hu
      · exact fun hs => Finset.disjoint_left.mp hST hs ht
      · exact fun hs => Finset.disjoint_left.mp hSU hs hu
  have hcs := card_le_card hin
  rw [card_insert_of_notMem hdis,card_union_of_disjoint hTU] at hcs
  have hb := hS.parity_bound hc hσ
  intro x hx
  by_contra hn
  obtain ⟨y,hy,hy2⟩ := hS.exists_distance_two hc hx hn
  have hp : 0 < (S.filter (fun y => Even (G.dist c y))).card :=
    card_pos.mpr ⟨y,mem_filter.mpr ⟨hy,by simp [hy2]⟩⟩
  omega

/-- Under the large-order Graph 189 hypotheses, a single cut vertex cannot
have three disjoint branches. -/
theorem no_three_sides [DecidableRel G.Adj] {c : V} {S T U : Finset V}
    (hS : Side G c S) (hT : Side G c T) (hU : Side G c U)
    (hST : Disjoint S T) (hSU : Disjoint S U) (hTU : Disjoint T U)
    (hc : G.Connected) {k : ℕ} (hσ : ∀ v, evenCard G v ≤ 1+k)
    (horder : 2*k+3 ≤ Fintype.card V)
    (hpair : ∀ x y : V, x ≠ y → k ≤ G.degree x ∨ k ≤ G.degree y) : False := by
  classical
  obtain ⟨hs,hs',_⟩ := hS.card_bounds hc hσ horder hpair
  obtain ⟨ht,ht',_⟩ := hT.card_bounds hc hσ horder hpair
  obtain ⟨hu,hu',_⟩ := hU.card_bounds hc hσ horder hpair
  obtain ⟨x,hx,hxc⟩ := hS.contact hc
  have hadjT := hT.full_contact_of_two_other_sides hS hU hST.symm hTU hSU hc hσ hs' hu'
  have hadjU := hU.full_contact_of_two_other_sides hS hT hSU.symm hTU.symm hST hc hσ hs' ht'
  have hxa : x ∉ T ∪ U := fun hm => (mem_union.mp hm).elim
    (Finset.disjoint_left.mp hST hx) (Finset.disjoint_left.mp hSU hx)
  have hsub : insert x (T ∪ U) ⊆ univ.filter (fun y => Even (G.dist x y)) := by
    intro y hy
    rcases mem_insert.mp hy with rfl | hy
    · simp
    · rcases mem_union.mp hy with h | h
      · have hd := hS.dist_add hc hx (fun hs => Finset.disjoint_left.mp hST hs h)
        simp [hd,dist_eq_one_iff_adj.mpr hxc,dist_eq_one_iff_adj.mpr (hadjT y h)]
      · have hd := hS.dist_add hc hx (fun hs => Finset.disjoint_left.mp hSU hs h)
        simp [hd,dist_eq_one_iff_adj.mpr hxc,dist_eq_one_iff_adj.mpr (hadjU y h)]
  have hb : (insert x (T ∪ U)).card ≤ 1+k := (card_le_card hsub).trans (hσ x)
  rw [card_insert_of_notMem hxa,card_union_of_disjoint hTU] at hb
  omega


/-- The ambient vertex set of one connected component after deleting the gate. -/
noncomputable def componentVertices (c : V)
    (C : (G.induce {v | v ≠ c}).ConnectedComponent) : Finset V := by
  classical
  exact univ.filter (fun x => ∃ h : x ≠ c, (G.induce {v | v ≠ c}).connectedComponentMk ⟨x,h⟩ = C)

private theorem mem_componentVertices {c x : V}
    {C : (G.induce {v | v ≠ c}).ConnectedComponent} :
    x ∈ componentVertices c C ↔
      ∃ h : x ≠ c, (G.induce {v | v ≠ c}).connectedComponentMk ⟨x,h⟩ = C := by
  classical
  simp [componentVertices]

private theorem componentVertices_side (c : V) (C : (G.induce {v | v ≠ c}).ConnectedComponent) :
    Side G c (componentVertices c C) := by
  classical
  constructor
  · obtain ⟨x,hx⟩ := (Quot.mk_surjective C)
    exact ⟨x.val, mem_componentVertices.mpr ⟨x.property,hx⟩⟩
  · intro h
    obtain ⟨hn,_⟩ := mem_componentVertices.mp h
    exact hn rfl
  · intro u v hu hadj hv
    by_contra hne
    obtain ⟨huc,hC⟩ := mem_componentVertices.mp hu
    have h' : (G.induce {v | v ≠ c}).Adj ⟨u,huc⟩ ⟨v,hne⟩ := hadj
    exact hv (mem_componentVertices.mpr
      ⟨hne,(ConnectedComponent.connectedComponentMk_eq_of_adj h').symm.trans hC⟩)

private theorem componentVertices_disjoint {c : V}
    {A B : (G.induce {v | v ≠ c}).ConnectedComponent} (hne : A ≠ B) :
    Disjoint (componentVertices c A) (componentVertices c B) := by
  refine Finset.disjoint_left.mpr ?_
  intro v hA hB
  obtain ⟨_,ha⟩ := mem_componentVertices.mp hA
  obtain ⟨_,hb⟩ := mem_componentVertices.mp hB
  exact hne (ha.symm.trans hb)

/-- The local block-branching obstruction. Removing any vertex leaves at most
two connected components. The exact Graph 189 degree statistic is used through
its defining order-statistic property. -/
theorem components_after_deleting_le_two [DecidableRel G.Adj]
    (hc : G.Connected) {k : ℕ} (hσ : ∀ v, evenCard G v ≤ 1+k)
    (horder : 2*k+3 ≤ Fintype.card V)
    (hpair : ∀ x y : V, x ≠ y → k ≤ G.degree x ∨ k ≤ G.degree y) (c : V) :
    Nat.card (G.induce {v | v ≠ c}).ConnectedComponent ≤ 2 := by
  classical
  let _ := Fintype.ofFinite (G.induce {v | v ≠ c}).ConnectedComponent
  rw [Nat.card_eq_fintype_card]
  by_contra! h
  obtain ⟨A,B,C,hAB,hAC,hBC⟩ := Fintype.two_lt_card_iff.mp h
  exact no_three_sides (componentVertices_side c A) (componentVertices_side c B)
    (componentVertices_side c C) (componentVertices_disjoint hAB)
    (componentVertices_disjoint hAC) (componentVertices_disjoint hBC) hc hσ horder hpair


omit [DecidableEq V] in
/-- The order-statistic argument from OMA's
`WrittenOnTheWallII.GraphConjecture189.conjecture189.R1` (PR #2971). -/
private lemma degree_pair [DecidableRel G.Adj] [Nontrivial V] (x y : V) (hne : x ≠ y) :
    secondDegree G ≤ G.degree x ∨ secondDegree G ≤ G.degree y := by
  classical
  let ds := sortedDegrees G
  have hlen : 2 ≤ ds.length := by
    simpa [ds, sortedDegrees] using Nat.succ_le_of_lt (Fintype.one_lt_card (α := V))
  obtain ⟨a,b,l,heq⟩ : ∃ a b l, ds = a :: b :: l := by
    cases h : ds with
    | nil => simp [h] at hlen
    | cons a tail =>
      cases hh : tail with
      | nil => simp [h, hh] at hlen
      | cons b l => exact ⟨a,b,l,rfl⟩
  have hs : ds.Pairwise (· ≤ ·) := by simp [ds, sortedDegrees]
  rw [heq] at hs
  have hlow : ∀ t ∈ l, b ≤ t := (List.pairwise_cons.mp (List.pairwise_cons.mp hs).2).1
  have hnil : l.filter (fun t => decide (t < b)) = [] := by
    simpa [List.filter_eq_nil_iff] using hlow
  have hct : (ds.filter (fun t => decide (t < b))).length ≤ 1 := by
    rw [heq]
    by_cases h : a < b <;> simp [h,hnil]
  have hcoeds : (↑ds : Multiset ℕ) = Finset.univ.val.map (fun v : V => G.degree v) := by
    simp [ds, sortedDegrees]
  let low := Finset.univ.filter (fun v : V => G.degree v < b)
  have hl : low.card ≤ 1 := by
    change (Multiset.filter (fun t => G.degree t < b) Finset.univ.val).card ≤ 1
    have hct' : (Multiset.filter (fun t => t < b) (↑ds : Multiset ℕ)).card ≤ 1 := hct
    rw [hcoeds, Multiset.filter_map, Multiset.card_map] at hct'
    exact hct'
  have hb : secondDegree G = b := by
    change ds.getD 1 0 = b
    simp [heq] 
  rw [hb]
  by_contra! h
  exact hne (Finset.card_le_one.mp hl x (by simpa [low] using h.1) y (by simpa [low] using h.2))


/-- The cut-vertex branch of R2 can be restricted to a deletion with exactly
two components. No assumption is made on their sizes, connectivity, or shape. -/
theorem components_after_cut_eq_two [DecidableRel G.Adj] [Nontrivial V]
    (hc : G.Connected) (hσ : ∀ v, evenCard G v ≤ 1 + (secondDegree G))
    (horder : 2 * (secondDegree G) + 3 ≤ Fintype.card V) {c : V}
    (hcut : ¬ (G.induce {v | v ≠ c}).Connected) :
    Nat.card (G.induce {v | v ≠ c}).ConnectedComponent = 2 := by
  classical
  have hub := components_after_deleting_le_two hc hσ horder (degree_pair (G := G)) c
  apply le_antisymm hub
  by_contra! h
  let _ := Fintype.ofFinite (G.induce {v | v ≠ c}).ConnectedComponent
  rw [Nat.card_eq_fintype_card] at h
  have _ : Subsingleton (G.induce {v | v ≠ c}).ConnectedComponent :=
    Fintype.card_le_one_iff_subsingleton.mp (by omega)
  obtain ⟨w,hw⟩ := exists_ne c
  exact hcut { preconnected := fun u v => ConnectedComponent.exact (Subsingleton.elim _ _)
               nonempty := ⟨⟨w,hw⟩⟩ }


end Graph189CutCore
end

section
namespace Graph189CutInterface
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- In the large-order cut-vertex branch of WOWII Graph 189, deleting a cut
vertex separates the graph into exactly two connected components. -/
theorem components_after_cut_eq_two (hc : G.Connected)
    (hσ : ∀ v, G.distEven v ≤ 1 + G.secondSmallestDegree)
    (horder : 2 * G.secondSmallestDegree + 3 ≤ Fintype.card V) {c : V}
    (hcut : ¬ (G.induce {v | v ≠ c}).Connected) :
    Nat.card (G.induce {v | v ≠ c}).ConnectedComponent = 2 :=
  Graph189CutCore.components_after_cut_eq_two hc hσ horder hcut

end Graph189CutInterface
end

section
namespace Graph189CutExtract
open SimpleGraph Graph189CutCore
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- Passing from a component on the deletion subtype to its ambient vertex set
preserves connectedness of the induced graph. -/
theorem componentVertices_connected (c : V)
    (C : (G.induce {v | v ≠ c}).ConnectedComponent) :
    (G.induce (componentVertices c C : Set V)).Connected := by
  classical
  let φ : C.toSimpleGraph →g G.induce (componentVertices c C : Set V) :=
    { toFun := fun z => ⟨z.val.val, mem_componentVertices.mpr ⟨z.val.property,z.property⟩⟩
      map_rel' := fun h => h }
  have hsurj : Function.Surjective φ := by
    intro z
    obtain ⟨hn,hC⟩ := mem_componentVertices.mp z.property
    exact ⟨⟨⟨z.val,hn⟩,hC⟩, Subtype.ext rfl⟩
  exact Connected.map φ hsurj C.connected_toSimpleGraph

/-- Two components after deletion supply the two disjoint connected sides
covering every vertex except the deleted vertex. -/
theorem two_connected_sides (c : V)
    (htwo : Nat.card (G.induce {v | v ≠ c}).ConnectedComponent = 2) :
    ∃ A B : Finset V, Side G c A ∧ Side G c B ∧ Disjoint A B ∧
      (∀ x, x = c ∨ x ∈ A ∨ x ∈ B) ∧
      (G.induce (A : Set V)).Connected ∧ (G.induce (B : Set V)).Connected := by
  classical
  let H := G.induce {v | v ≠ c}
  let _ := Fintype.ofFinite H.ConnectedComponent
  have hcard : Fintype.card H.ConnectedComponent = 2 := by
    rw [← Nat.card_eq_fintype_card]
    exact htwo
  let e : H.ConnectedComponent ≃ Fin 2 := Fintype.equivFinOfCardEq hcard
  let C := e.symm 0
  let D := e.symm 1
  have hne : C ≠ D := fun eq => (by decide : (0 : Fin 2) ≠ 1) (e.symm.injective eq)
  refine ⟨componentVertices c C, componentVertices c D,
    componentVertices_side c C, componentVertices_side c D, componentVertices_disjoint hne,
    ?_, componentVertices_connected c C, componentVertices_connected c D⟩
  intro x
  by_cases hx : x = c
  · exact Or.inl hx
  · let t := H.connectedComponentMk ⟨x,hx⟩
    have alt : e t = 0 ∨ e t = 1 := by
      have lim := (e t).isLt
      rcases (by omega : (e t).val = 0 ∨ (e t).val = 1) with h | h
      · exact Or.inl (Fin.ext h)
      · exact Or.inr (Fin.ext h)
    rcases alt with h | h
    · exact Or.inr (Or.inl (mem_componentVertices.mpr ⟨hx, (e.eq_symm_apply).mpr h⟩))
    · exact Or.inr (Or.inr (mem_componentVertices.mpr ⟨hx, (e.eq_symm_apply).mpr h⟩))

end Graph189CutExtract
end

section
namespace Graph189CutMiddle
open SimpleGraph Finset Graph189CutCore
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- A cut has a nonempty side opposite any specified surviving vertex. -/
theorem side_away_from {c d : V} (hcd : c ≠ d)
    (hcut : ¬ (G.induce {x | x ≠ c}).Connected) :
    ∃ A : Finset V, Side G c A ∧ d ∉ A := by
  classical
  let D := G.induce {x | x ≠ c}
  let t : {x : V // x ≠ c} := ⟨d,hcd.symm⟩
  let A := univ.filter (fun x => ∃ hn : x ≠ c, ¬ D.Reachable ⟨x, hn⟩ t)
  have memA {x : V} : x ∈ A ↔ ∃ hn : x ≠ c, ¬ D.Reachable ⟨x,hn⟩ t := by simp [A]
  have hex : ∃ x, ¬ D.Reachable x t := by
    by_contra! hr
    exact hcut {preconnected := fun x y => (hr x).trans (hr y).symm, nonempty := ⟨t⟩}
  obtain ⟨x,hx⟩ := hex
  refine ⟨A, ⟨⟨x.val,memA.mpr ⟨x.property,hx⟩⟩,?_,?_⟩,?_⟩
  · intro h
    obtain ⟨hh,_⟩ := memA.mp h
    exact hh rfl
  · intro u v hu huv hv
    by_contra hvc
    obtain ⟨huc,hut⟩ := memA.mp hu
    have he : D.Adj ⟨u,huc⟩ ⟨v,hvc⟩ := huv
    exact hv (memA.mpr ⟨hvc, fun hr => hut (he.reachable.trans hr)⟩)
  · intro h
    obtain ⟨_, hh⟩ := memA.mp h
    exact hh (Reachable.refl _)

omit [Fintype V] in
theorem separated_sides_disjoint {c d : V} {A B : Finset V}
    (hc : G.Connected) (hcd : c ≠ d) (hA : Side G c A) (hB : Side G d B)
    (hdA : d ∉ A) (hcB : c ∉ B) : Disjoint A B := by
  apply Finset.disjoint_left.mpr
  intro x hxA hxB
  have h1 := hA.dist_add hc hxA hdA
  have h2 := hB.dist_add hc hxB hcB
  rw [G.dist_comm (u := d) (v := c)] at h2
  have hpos := hc.pos_dist_of_ne hcd
  omega

private theorem complement_count {A B : Finset V} (hab : Disjoint A B) :
    Aᶜ.card = B.card + (A ∪ B)ᶜ.card := by
  have hd : Disjoint B (A ∪ B)ᶜ := by
    apply Finset.disjoint_left.mpr
    exact fun _ hb h => (mem_compl.mp h) (mem_union_right _ hb)
  have heq : Aᶜ = B ∪ (A ∪ B)ᶜ := by
    ext v
    simp only [mem_compl,mem_union]
    have hh : ¬ (v ∈ A ∧ v ∈ B) := fun hp => Finset.disjoint_left.mp hab hp.1 hp.2
    tauto
  rw [heq,card_union_of_disjoint hd]

omit [Fintype V] [DecidableEq V] in
private theorem all_contacts_of_empty_even {c : V} {S : Finset V}
    (h : Side G c S) (hc : G.Connected)
    (ha : (S.filter (fun x => Even (G.dist c x))).card = 0) :
    ∀ x ∈ S, G.Adj c x := by
  intro x hx
  by_contra hn
  obtain ⟨y,hy,hd⟩ := h.exists_distance_two hc hx hn
  have hh : (S.filter (fun x => Even (G.dist c x))).Nonempty :=
    ⟨y,mem_filter.mpr ⟨hy,by simp [hd]⟩⟩
  have := card_pos.mpr hh
  omega

/-- A vertex between the two gates has no edge into either remote side. -/
theorem middle_ball [DecidableRel G.Adj] {c d u : V} {A B : Finset V}
    (hA : Side G c A) (hB : Side G d B) (hu : u ∈ (A ∪ B)ᶜ)
    (huc : u ≠ c) (hud : u ≠ d) :
    insert u (G.neighborFinset u) ⊆ (A ∪ B)ᶜ := by
  intro v hv
  rcases mem_insert.mp hv with rfl | hv
  · exact hu
  · have he : G.Adj u v := by simpa using hv
    apply mem_compl.mpr
    intro hvab
    rcases mem_union.mp hvab with ha | hb
    · exact huc (hA.exit_eq ha he.symm (fun hh => (mem_compl.mp hu) (mem_union_left _ hh)))
    · exact hud (hB.exit_eq hb he.symm (fun hh => (mem_compl.mp hu) (mem_union_right _ hh)))

/-- Every vertex between two remote sides, other than the distinct gates,
has degree strictly below k. -/
theorem middle_vertices_low [DecidableRel G.Adj] {k : ℕ}
    (hc : G.Connected) (hσ : ∀ v, evenCard G v ≤ 1+k)
    (horder : 2*k+3 ≤ Fintype.card V)
    (hpair : ∀ x y : V, x ≠ y → k ≤ G.degree x ∨ k ≤ G.degree y)
    {c d : V} (hcd : c ≠ d) {A B : Finset V} (hA : Side G c A) (hB : Side G d B)
    (hdA : d ∉ A) (hcB : c ∉ B) {u : V} (hu : u ∈ (A ∪ B)ᶜ)
    (huc : u ≠ c) (hud : u ≠ d) : G.degree u < k := by
  classical
  by_contra! high
  have hAB := separated_sides_disjoint hc hcd hA hB hdA hcB
  obtain ⟨ha2,hak,_⟩ := hA.card_bounds hc hσ horder hpair
  obtain ⟨hb2,hbk,_⟩ := hB.card_bounds hc hσ horder hpair
  have pA := hA.parity_bound hc hσ
  have pB := hB.parity_bound hc hσ
  rw [complement_count hAB] at pA
  rw [complement_count hAB.symm,union_comm B A] at pB
  have sub := middle_ball hA hB hu huc hud
  have hcard := card_le_card sub
  have huN : u ∉ G.neighborFinset u := by simp
  have hball : (insert u (G.neighborFinset u)).card = G.degree u + 1 := by
    rw [card_insert_of_notMem huN,card_neighborFinset_eq_degree]
  rw [hball] at hcard
  have hfill := eq_of_subset_of_card_le sub (by rw [hball]; omega)
  have a := all_contacts_of_empty_even hA hc (by omega)
  have b := all_contacts_of_empty_even hB hc (by omega)
  have touch (w : V) (hw : w ∈ (A ∪ B)ᶜ) (hn : w ≠ u) : G.Adj u w := by
    rw [← hfill] at hw
    simpa using (mem_insert.mp hw).resolve_left hn
  have hcg := touch c (by simp [hA.outside,hcB]) huc.symm
  have hdg := touch d (by simp [hdA,hB.outside]) hud.symm
  have unA : u ∉ A := fun hm => (mem_compl.mp hu) (mem_union_left _ hm)
  have unB : u ∉ B := fun hm => (mem_compl.mp hu) (mem_union_right _ hm)
  have hs : insert u (A ∪ B) ⊆ univ.filter (fun x => Even (G.dist u x)) := by
    intro v hv
    rcases mem_insert.mp hv with rfl | hv
    · simp
    · rcases mem_union.mp hv with ha | hb
      · rw [mem_filter]
        rw [G.dist_comm (u := u) (v := v),hA.dist_add hc ha unA,
          dist_eq_one_iff_adj.mpr (a v ha).symm,dist_eq_one_iff_adj.mpr hcg.symm]
        simp
      · rw [mem_filter]
        rw [G.dist_comm (u := u) (v := v),hB.dist_add hc hb unB,
          dist_eq_one_iff_adj.mpr (b v hb).symm,dist_eq_one_iff_adj.mpr hdg.symm]
        simp
  have cap : (insert u (A ∪ B)).card ≤ 1+k :=
    (card_le_card hs).trans (hσ u)
  rw [card_insert_of_notMem (mem_compl.mp hu),card_union_of_disjoint hAB] at cap
  omega

theorem middle_card_le_three [DecidableRel G.Adj] {k : ℕ}
    (hc : G.Connected) (hσ : ∀ v, evenCard G v ≤ 1+k)
    (horder : 2*k+3 ≤ Fintype.card V)
    (hpair : ∀ x y : V, x ≠ y → k ≤ G.degree x ∨ k ≤ G.degree y)
    {c d : V} (hcd : c ≠ d) {A B : Finset V} (hA : Side G c A) (hB : Side G d B)
    (hdA : d ∉ A) (hcB : c ∉ B) : (A ∪ B)ᶜ.card ≤ 3 := by
  classical
  let Z := (A ∪ B)ᶜ
  have hcZ : c ∈ Z := by simp [Z,hA.outside,hcB]
  have hdZ : d ∈ Z := by simp [Z,hdA,hB.outside]
  have hdZ' : d ∈ Z.erase c := mem_erase.mpr ⟨hcd.symm,hdZ⟩
  have hsmall : ((Z.erase c).erase d).card ≤ 1 := by
    refine card_le_one.mpr ?_
    intro x hx y hy
    obtain ⟨hxd,hx⟩ := mem_erase.mp hx
    obtain ⟨hxc,hx⟩ := mem_erase.mp hx
    obtain ⟨hyd,hy⟩ := mem_erase.mp hy
    obtain ⟨hyc,hy⟩ := mem_erase.mp hy
    have lx := middle_vertices_low hc hσ horder hpair hcd hA hB hdA hcB hx hxc hxd
    have ly := middle_vertices_low hc hσ horder hpair hcd hA hB hdA hcB hy hyc hyd
    by_contra hne
    exact (hpair x y hne).elim (fun hh => (Nat.not_le.mpr lx) hh)
      (fun hh => (Nat.not_le.mpr ly) hh)
  rw [card_erase_of_mem hdZ',card_erase_of_mem hcZ] at hsmall
  change Z.card ≤ 3
  omega

end Graph189CutMiddle
end

section
namespace Graph189CutExtreme
open SimpleGraph Finset Graph189CutCore
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

-- Equal-size alternating-chain construction from OMA Graph 189 R1, also
-- used in the earlier bipartite branch of the conjecture.
/-- Alternate between equally sized sets of vertices, starting at an additional
vertex with a neighbor in the first set if that set is nonempty. -/
theorem alternating_chain (left right : Finset V) (z : V)
    (hcard : left.card = right.card)
    (hdisj : ∀ x ∈ left, x ∉ right)
    (hzl : z ∉ left) (hzr : z ∉ right)
    (hcross : ∀ y ∈ right, ∀ x ∈ left, G.Adj y x)
    (hstart : left.Nonempty → ∃ x ∈ left, G.Adj z x) :
    ∃ L : List V, L.head? = some z ∧ L.Nodup ∧ L.IsChain G.Adj ∧
      ∀ b, b ∈ L ↔ b = z ∨ b ∈ left ∨ b ∈ right := by
  by_cases hn : left.Nonempty
  · obtain ⟨x,hxl,hzx⟩ := hstart hn
    have hright : right.Nonempty := Finset.card_pos.mp (hcard ▸ Finset.card_pos.mpr hn)
    obtain ⟨y,hyr⟩ := hright
    have hyl : y ∉ left := fun hy => hdisj y hy hyr
    have hyx : G.Adj y x := hcross y hyr x hxl
    have hc' : (left.erase x).card = (right.erase y).card := by
      rw [Finset.card_erase_of_mem hxl, Finset.card_erase_of_mem hyr, hcard]
    obtain ⟨L,hhead,hnodup,hchain,hcover⟩ :=
      alternating_chain (left.erase x) (right.erase y) y hc'
        (fun b hb hr => hdisj b (Finset.mem_of_mem_erase hb) (Finset.mem_of_mem_erase hr))
        (fun he => hyl (Finset.mem_of_mem_erase he)) (Finset.notMem_erase _ _)
        (fun b hb a ha => hcross b (Finset.mem_of_mem_erase hb) a (Finset.mem_of_mem_erase ha))
        (fun hempty => let ⟨a,ha⟩ := hempty
                       ⟨a,ha,hcross y hyr a (Finset.mem_of_mem_erase ha)⟩)
    have hxy : x ≠ y := fun e => hyl (e ▸ hxl)
    have hxright := hdisj x hxl
    have hxnot : x ∉ L := by
      rw [hcover]
      simp [hxy, hxright]
    have hzxne : z ≠ x := fun e => hzl (e.symm ▸ hxl)
    have hzyne : z ≠ y := fun e => hzr (e.symm ▸ hyr)
    have hznot : z ∉ L := by rw [hcover]; simp [hzyne, hzl, hzr]
    have hchain' : (x :: L).IsChain G.Adj := hchain.cons (by simpa [hhead] using hyx.symm)
    refine ⟨z :: x :: L, rfl, ?_, hchain'.cons (by simpa using hzx), ?_⟩
    · simp [hzxne, hznot, hxnot, hnodup]
    · intro b
      simp only [List.mem_cons, hcover, Finset.mem_erase]
      by_cases qx : b = x <;> by_cases qy : b = y <;> simp_all
  · have el : left = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    have er : right = ∅ := Finset.card_eq_zero.mp (by simpa [el] using hcard.symm)
    subst left
    subst right
    exact ⟨[z],rfl,by simp,by simp,by simp⟩
termination_by left.card
decreasing_by rw [Finset.card_erase_of_mem hxl]; have hpos := Finset.card_pos.mpr hn; omega

omit [DecidableEq V] in
private theorem dist_two_of_two_edges (hc : G.Connected) {a b x : V}
    (hab : G.Adj a b) (hbx : G.Adj b x) (hne : a ≠ x) (hn : ¬ G.Adj a x) :
    G.dist a x = 2 := by
  have hlt := hc.one_lt_dist_of_ne_of_not_adj hne hn
  have hle : G.dist a x ≤ 2 := G.dist_le (.cons hab (.cons hbx .nil))
  omega

omit [DecidableEq V] in
private theorem contact_universal (hc : G.Connected) {A : Finset V}
    (ha : (G.induce (A : Set V)).Connected) {x : V} (hx : x ∈ A)
    (hn : ∀ y ∈ A, G.dist x y ≠ 2) {v : V} (hv : v ∈ A) (hnv : x ≠ v) :
    G.Adj x v := by
  by_contra hvn
  let F : Set (A : Set V) := {w | x ≠ w.val ∧ ¬ G.Adj x w.val}
  obtain ⟨P⟩ := ha (⟨v,hv⟩ : (A : Set V)) ⟨x,hx⟩
  have notx : (⟨x,hx⟩ : (A : Set V)) ∉ F := fun h => h.1 rfl
  obtain ⟨b,_,hi,ho⟩ := P.exists_boundary_dart F ⟨hnv,hvn⟩ notx
  have he : G.Adj b.fst.val b.snd.val := b.adj
  have hnext : G.Adj x b.snd.val := by
    by_contra h
    by_cases hh : x = b.snd.val
    · exact hi.2 (hh ▸ he.symm)
    · exact ho ⟨hh,h⟩
  exact hn b.fst.val b.fst.property (dist_two_of_two_edges hc hnext he.symm hi.1 hi.2)

variable [Fintype V] [DecidableRel G.Adj]

/-- A component of order exactly twice the second-degree threshold has a
spanning path starting at its gate. -/
theorem rooted_at_two_k {k : ℕ} (hc : G.Connected)
    (hσ : ∀ v, evenCard G v ≤ 1+k) {c : V} {A B : Finset V}
    (hA : Side G c A) (hB : Side G c B) (hAB : Disjoint A B)
    (hconn : (G.induce (A : Set V)).Connected) (hsize : A.card = 2*k)
    (hb : k ≤ B.card) :
    ∃ L : List V, L.head? = some c ∧ L.Nodup ∧ L.IsChain G.Adj ∧
      ∀ x, x ∈ L ↔ x = c ∨ x ∈ A := by
  classical
  have pb := hB.parity_bound hc hσ
  have hsub : insert c A ⊆ Bᶜ := by
    intro x hx
    apply mem_compl.mpr
    rcases mem_insert.mp hx with rfl | hx
    · exact hB.outside
    · exact Finset.disjoint_left.mp hAB hx
  have hcount := card_le_card hsub
  rw [card_insert_of_notMem hA.outside] at hcount
  have hBcontact : ∀ x ∈ B, G.Adj c x :=
    Graph189CutMiddle.all_contacts_of_empty_even hB hc (by omega)
  have hfull {x : V} (hx : x ∈ A) (hcx : G.Adj c x) {v : V} (hv : v ∈ A)
      (hne : x ≠ v) : G.Adj x v := by
    apply contact_universal hc hconn hx _ hv hne
    intro y hy hdy
    have hxb := Finset.disjoint_left.mp hAB hx
    have hyb := Finset.disjoint_left.mp hAB hy
    have hxy : x ≠ y := by rintro rfl; simp at hdy
    have hs : insert y (insert x B) ⊆ univ.filter (fun z => Even (G.dist x z)) := by
      intro z hz
      rcases mem_insert.mp hz with rfl | hz
      · simp [hdy]
      rcases mem_insert.mp hz with rfl | hz
      · simp
      · have hd := hA.dist_add hc hx (fun h => Finset.disjoint_left.mp hAB h hz)
        simp [hd,dist_eq_one_iff_adj.mpr hcx.symm,dist_eq_one_iff_adj.mpr (hBcontact z hz)]
    have cap := (card_le_card hs).trans (hσ x)
    rw [card_insert_of_notMem (by simp [hxy.symm,hyb]),card_insert_of_notMem hxb] at cap
    omega
  let P := A.filter (G.Adj c ·)
  let Q := A \ P
  have hPA : P ⊆ A := filter_subset _ _
  obtain ⟨a,ha,hac⟩ := hA.contact hc
  have hQsub : insert c Q ⊆ univ.filter (fun y => Even (G.dist c y)) := by
    intro y hy
    rcases mem_insert.mp hy with rfl | hy
    · simp
    · obtain ⟨hyA,hyP⟩ := mem_sdiff.mp hy
      have hcy : ¬ G.Adj c y := fun he => hyP (mem_filter.mpr ⟨hyA,he⟩)
      have hay : a ≠ y := fun e => hcy (e ▸ hac.symm)
      have hdy := dist_two_of_two_edges hc hac.symm (hfull ha hac.symm hyA hay)
        (fun e => hA.outside (e ▸ hyA)) hcy
      simp [hdy]
  have hq := (card_le_card hQsub).trans (hσ c)
  rw [card_insert_of_notMem (fun h => hA.outside (mem_sdiff.mp h).1)] at hq
  have hsum : Q.card + P.card = A.card := card_sdiff_add_card_eq_card hPA
  change Q.card + 1 ≤ 1+k at hq
  rw [hsize] at hsum
  obtain ⟨T,hTP,hT⟩ := exists_subset_card_eq (s := P) (n := k) (by omega)
  have hTA := hTP.trans hPA
  have hTR := card_sdiff_add_card_eq_card hTA
  rw [hT,hsize] at hTR
  obtain ⟨L,hl,hn,hch,hcov⟩ := alternating_chain (G:=G) T (A \ T) c
    (by omega) (fun x hx hy => (mem_sdiff.mp hy).2 hx)
    (fun h => hA.outside (hTA h)) (fun h => hA.outside (mem_sdiff.mp h).1)
    (fun y hy x hx => (hfull (hTA hx) (mem_filter.mp (hTP hx)).2 (mem_sdiff.mp hy).1
      (fun e => (mem_sdiff.mp hy).2 (e ▸ hx))).symm)
    (fun ⟨x,hx⟩ => ⟨x,hx,(mem_filter.mp (hTP hx)).2⟩)
  refine ⟨L,hl,hn,hch,?_⟩
  intro z
  rw [hcov]
  simp only [mem_sdiff]
  have hz : z ∈ T → z ∈ A := fun h => hTA h
  tauto

end Graph189CutExtreme
end

section
namespace Graph189CutBounds
open SimpleGraph Finset Graph189CutCore
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- The large-order regime excludes all leaves and isolated vertices. -/
theorem two_le_degree [DecidableRel G.Adj] [Nontrivial V] (hc : G.Connected)
    {k : ℕ} (hσ : ∀ v, evenCard G v ≤ 1+k) (horder : 2*k+3 ≤ Fintype.card V)
    (v : V) : 2 ≤ G.degree v := by
  classical
  obtain ⟨a,hva⟩ := hc.preconnected.exists_adj_of_nontrivial v
  have hp : 0 < (G.neighborFinset v).card := card_pos.mpr ⟨a,by simpa using hva⟩
  by_contra! hn
  rw [← card_neighborFinset_eq_degree] at hn
  obtain ⟨c,hN⟩ := card_eq_one.mp (show (G.neighborFinset v).card = 1 by omega)
  have hadj (u : V) : G.Adj v u ↔ u = c := by
    rw [← mem_neighborFinset, hN, mem_singleton]
  have hvc := (hadj c).mpr rfl
  have S : Side G c ({v} : Finset V) := by
    refine ⟨singleton_nonempty _,by simpa using hvc.ne.symm,?_⟩
    intro x y hx he _
    have hx' : x = v := mem_singleton.mp hx
    exact (hadj _).mp (hx' ▸ he)
  have hh := S.parity_bound hc hσ
  have hs := card_add_card_compl ({v} : Finset V)
  rw [card_singleton] at hs
  omega

/-- The other side's gate parity budget bounds the order of a remote side. -/
theorem side_card_le_two_k {k : ℕ} (hc : G.Connected)
    (hσ : ∀ v, evenCard G v ≤ 1+k) {c : V} {A B : Finset V}
    (hA : Side G c A) (hB : Side G c B) (hAB : Disjoint A B) : A.card ≤ 2*k := by
  have hs : insert c A ⊆ Bᶜ := by
    intro y hy
    apply mem_compl.mpr
    rcases mem_insert.mp hy with rfl | hy
    · exact hB.outside
    · exact Finset.disjoint_left.mp hAB hy
  have hh := card_le_card hs
  rw [card_insert_of_notMem hA.outside] at hh
  have := hB.parity_bound hc hσ
  omega

end Graph189CutBounds
end

section
open SimpleGraph

namespace Graph189CutJoin

variable {V : Type*} {G : SimpleGraph V}

private theorem walk_of_chain {a : V} {xs : List V} (h : (a :: xs).IsChain G.Adj) :
    ∃ b, ∃ w : G.Walk a b, w.support = a :: xs := by
  induction xs generalizing a with
  | nil => exact ⟨a, .nil, rfl⟩
  | cons x xs ih =>
    obtain ⟨e, ht⟩ := List.isChain_cons_cons.mp h
    obtain ⟨b, w, hw⟩ := ih ht
    exact ⟨b, .cons e w, by simp [hw]⟩

/-- Splice two ambient vertex lists rooted at the common cut vertex. -/
theorem hamiltonian_of_rooted_sides [DecidableEq V] {c : V} {A B : Finset V}
    (hdis : Disjoint A B) (hcover : ∀ x, x=c ∨ x∈A ∨ x∈B)
    (rootA : ∃ L : List V, L.head? = some c ∧ L.Nodup ∧ L.IsChain G.Adj ∧
      ∀ x, x∈L ↔ x=c ∨ x∈A)
    (rootB : ∃ L : List V, L.head? = some c ∧ L.Nodup ∧ L.IsChain G.Adj ∧
      ∀ x, x∈L ↔ x=c ∨ x∈B) :
    ∃ a b, ∃ p : G.Walk a b, p.IsHamiltonian := by
  obtain ⟨left, hlhead, hln, hlc, hlm⟩ := rootA
  obtain ⟨right, hrhead, hrn, hrc, hrm⟩ := rootB
  cases left with
  | nil => simp at hlhead
  | cons l ls =>
    simp only [List.head?_cons, Option.some.injEq] at hlhead
    subst l
    cases right with
    | nil => simp at hrhead
    | cons r rs =>
      simp only [List.head?_cons, Option.some.injEq] at hrhead
      subst r
      obtain ⟨a, p, hp⟩ := walk_of_chain hlc
      obtain ⟨b, q, hq⟩ := walk_of_chain hrc
      refine ⟨a, b, p.reverse.append q, ?_⟩
      intro x
      simp only [Walk.support_append, Walk.support_reverse, hp, hq, List.tail_cons,
        List.count_append, List.count_reverse]
      by_cases hx : x ∈ c :: ls
      · have hr : x ∉ rs := by
          intro hxr
          have hne : x ≠ c := fun he => (List.nodup_cons.mp hrn).1 (he ▸ hxr)
          have ha := (hlm x).mp hx
          have hb := (hrm x).mp (List.mem_cons_of_mem _ hxr)
          exact Finset.disjoint_left.mp hdis (ha.resolve_left hne) (hb.resolve_left hne)
        simp [List.count_eq_one_of_mem hln hx, List.count_eq_zero_of_not_mem hr]
      · have hne : x ≠ c := fun he => hx (he ▸ List.mem_cons_self)
        have hb : x∈B := ((hcover x).resolve_left hne).resolve_left
          (fun ha => hx ((hlm x).mpr (.inr ha)))
        have hxr : x ∈ rs := (List.mem_cons.mp ((hrm x).mpr (.inr hb))).resolve_left hne
        simp [List.count_eq_zero_of_not_mem hx, List.count_eq_one_of_mem
          (List.nodup_cons.mp hrn).2 hxr]

end Graph189CutJoin
end

section
namespace Graph189CutH1Assembly
open SimpleGraph Finset Graph189CutCore
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- It suffices to construct the rooted path on components of order at most
twice the degree threshold minus one. The saturated size is proved outright. -/
theorem h1_of_small_rooted (hc : G.Connected)
    (hσ : ∀ v, G.distEven v ≤ 1 + G.secondSmallestDegree)
    (horder : 2 * G.secondSmallestDegree + 3 ≤ Fintype.card V)
    (hcut : ∃ c : V, ¬ (G.induce {v | v ≠ c}).Connected)
    (small : ∀ {c : V} {A : Finset V}, Side G c A →
      A.card ≤ 2 * G.secondSmallestDegree - 1 →
      ∃ L : List V, L.head? = some c ∧ L.Nodup ∧ L.IsChain G.Adj ∧
        ∀ x, x ∈ L ↔ x = c ∨ x ∈ A) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  obtain ⟨c,cc⟩ := hcut
  have htwo := Graph189CutInterface.components_after_cut_eq_two hc hσ horder cc
  obtain ⟨A,B,hA,hB,hAB,hcover,hconnA,hconnB⟩ := Graph189CutExtract.two_connected_sides c htwo
  have roots {S T : Finset V} (hs : Side G c S) (ht : Side G c T) (hd : Disjoint S T)
      (hconn : (G.induce (S : Set V)).Connected) :
      ∃ L : List V, L.head? = some c ∧ L.Nodup ∧ L.IsChain G.Adj ∧
        ∀ x, x ∈ L ↔ x = c ∨ x ∈ S := by
    have hu := Graph189CutBounds.side_card_le_two_k hc hσ hs ht hd
    by_cases heq : S.card = 2 * G.secondSmallestDegree
    · have hlo := (ht.card_bounds hc hσ horder (Graph189CutCore.degree_pair (G := G))).2.1
      exact Graph189CutExtreme.rooted_at_two_k hc hσ hs ht hd hconn heq hlo
    · exact small hs (by omega)
  exact Graph189CutJoin.hamiltonian_of_rooted_sides hAB hcover (roots hA hB hAB hconnA)
    (roots hB hA hAB.symm hconnB)

end Graph189CutH1Assembly
end

section
namespace Graph189InducedSide
open SimpleGraph Finset

variable {V : Type*} [DecidableEq V]

abbrev sideVerts (c : V) (A : Finset V) : Set V := ↑(insert c A)
abbrev sideGraph (G : SimpleGraph V) (c : V) (A : Finset V) := G.induce (sideVerts c A)
abbrev sideRoot (c : V) (A : Finset V) : sideVerts c A := ⟨c, Finset.mem_insert_self ..⟩

theorem degree_side [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {c : V} {A : Finset V} (hA : Graph189CutCore.Side G c A)
    (u : sideVerts c A) (hu : u ≠ sideRoot c A) :
    (sideGraph G c A).degree u = G.degree u.val := by
  have hx : u.val ≠ c := fun e => hu (Subtype.ext e)
  have ha : u.val ∈ A := (Finset.mem_insert.mp u.property).resolve_left hx
  have hsub : G.neighborSet u.val ⊆ sideVerts c A := by
    intro v hv
    by_cases hva : v ∈ A
    · exact Finset.mem_insert_of_mem hva
    · exact Finset.mem_insert.mpr (.inl (hA.exit_eq ha hv hva))
  convert SimpleGraph.degree_induce_of_neighborSet_subset (G := G) (s := sideVerts c A)
    (v := u) hsub using 1
  congr 1
  exact Subsingleton.elim _ _


theorem card_side [Fintype V] {G : SimpleGraph V} {c : V} {A : Finset V}
    (hA : Graph189CutCore.Side G c A) : Fintype.card (sideVerts c A) = A.card + 1 := by
  change Fintype.card ↥(insert c A) = _
  exact (Fintype.card_coe (insert c A)).trans (Finset.card_insert_of_notMem hA.outside)

theorem lift_rooted_list {G : SimpleGraph V} {c : V} {A : Finset V}
    (rooted : ∃ L : List (sideVerts c A), L.head? = some (sideRoot c A) ∧
      L.Nodup ∧ L.IsChain (sideGraph G c A).Adj ∧ ∀ u, u ∈ L) :
    ∃ L : List V, L.head? = some c ∧ L.Nodup ∧ L.IsChain G.Adj ∧
      ∀ x, x ∈ L ↔ x = c ∨ x ∈ A := by
  obtain ⟨L, hhead, hn, hchain, hall⟩ := rooted
  refine ⟨L.map Subtype.val, ?_, hn.map Subtype.val_injective, ?_, ?_⟩
  · simp [List.head?_map, hhead]
  · exact (List.isChain_map Subtype.val).mpr hchain
  · intro x
    constructor
    · intro hx
      obtain ⟨u, _, rfl⟩ := List.mem_map.mp hx
      exact Finset.mem_insert.mp u.property
    · intro hx
      let u : sideVerts c A := ⟨x, Finset.mem_insert.mpr hx⟩
      exact List.mem_map.mpr ⟨u, hall u, rfl⟩

/-- Transport the four small-side hypotheses to the induced graph, then
lift the resulting rooted list to the ambient vertex type. -/
theorem small_side_of_induced [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {c : V} {A : Finset V} {k : ℕ} (hA : Graph189CutCore.Side G c A)
    (hconn : G.Connected) (hsize : A.card + 1 ≤ 2*k)
    (hpair : ∀ x y : V, x ≠ y → k ≤ G.degree x ∨ k ≤ G.degree y)
    (htwo : ∀ x : V, 2 ≤ G.degree x)
    (produce :
      Fintype.card (sideVerts c A) ≤ 2*k →
      (∃ u, (sideGraph G c A).Adj (sideRoot c A) u) →
      (∀ u v : sideVerts c A, u ≠ sideRoot c A → v ≠ sideRoot c A → u ≠ v →
        k ≤ (sideGraph G c A).degree u ∨ k ≤ (sideGraph G c A).degree v) →
      (∀ u : sideVerts c A, u ≠ sideRoot c A → 2 ≤ (sideGraph G c A).degree u) →
      ∃ L : List (sideVerts c A), L.head? = some (sideRoot c A) ∧ L.Nodup ∧
        L.IsChain (sideGraph G c A).Adj ∧ ∀ u, u ∈ L) :
    ∃ L : List V, L.head? = some c ∧ L.Nodup ∧ L.IsChain G.Adj ∧
      ∀ x, x ∈ L ↔ x = c ∨ x ∈ A := by
  apply lift_rooted_list
  apply produce
  · rw [card_side hA]
    exact hsize
  · obtain ⟨x, hx, hxc⟩ := hA.contact hconn
    exact ⟨⟨x, Finset.mem_insert_of_mem hx⟩, hxc.symm⟩
  · intro u v hur hvr huv
    rw [degree_side hA u hur, degree_side hA v hvr]
    exact hpair u.val v.val (fun h => huv (Subtype.ext h))
  · intro u hur
    simpa [degree_side hA u hur] using htwo u.val

end Graph189InducedSide
end

section
namespace Graph189
open SimpleGraph Finset

private theorem append_chain {V : Type*} {G : SimpleGraph V} {L R : List V}
    {a b : V} (hl : L.IsChain G.Adj) (hr : R.IsChain G.Adj)
    (ha : L.getLast? = some a) (hb : R.head? = some b) (h : G.Adj a b) :
    (L ++ R).IsChain G.Adj := by
  apply hl.append hr
  intro x hx y hy
  rw [ha] at hx
  rw [hb] at hy
  have hax : a = x := by simpa using hx
  have hby : b = y := by simpa using hy
  exact hax ▸ hby ▸ h

private theorem reverse_chain {V : Type*} {G : SimpleGraph V} {L : List V}
    (h : L.IsChain G.Adj) : L.reverse.IsChain G.Adj :=
  List.isChain_reverse.mpr (h.imp fun _ _ h => h.symm)

private theorem split_at_pair {V : Type*} (l : List V) (i : ℕ) (hi : i + 1 < l.length) :
    ∃ P Q, l = P ++ l[i]'(by omega) :: l[i + 1] :: Q := by
  refine ⟨l.take i, l.drop (i + 2), ?_⟩
  conv_lhs => rw [← List.take_append_drop i l]
  rw [List.drop_eq_getElem_cons (by omega : i < l.length), List.drop_eq_getElem_cons hi]

private theorem trace_of_list {V : Type*} [DecidableEq V] {G : SimpleGraph V} (l : List V)
    (hn : l.Nodup) (hc : l.IsChain G.Adj) (hall : ∀ z : V, z ∈ l) (hne : l ≠ []) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  let p := Walk.ofSupport l hne hc
  have hs : p.support = l := Walk.support_ofSupport hne hc
  exact ⟨_, _, p, (Walk.IsPath.mk' (by rwa [hs])).isHamiltonian_of_mem (fun z => by
    rw [hs]
    exact hall z)⟩

private theorem trace_of_permuted_chain {V : Type*} [DecidableEq V] {G : SimpleGraph V} {l W : List V}
    (hn : l.Nodup) (hall : ∀ z : V, z ∈ l) (h : W.Perm l) (hc : W.IsChain G.Adj)
    (x : V) : ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  have hm (z : V) : z ∈ W := h.mem_iff.mpr (hall z)
  exact trace_of_list W (h.nodup_iff.mpr hn) hc hm (List.ne_nil_of_mem (hm x))

private theorem augmented_chain_excluding {V : Type*} {G : SimpleGraph V} {l : List V}
    {x y : V} (hc : l.IsChain (G ⊔ edge x y).Adj) (h : x ∉ l ∨ y ∉ l) :
    l.IsChain G.Adj := by
  apply List.isChain_iff_forall_rel_of_append_cons_cons.mpr
  intro a b P Q he
  have ha : a ∈ l := by rw [he]; simp
  have hb : b ∈ l := by rw [he]; simp
  have hab := List.isChain_iff_forall_rel_of_append_cons_cons.mp hc he
  rcases hab with hab | hab
  · exact hab
  · have hr := (edge_adj x y a b).mp hab
    rcases hr.1 with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact (h.elim (fun hn => hn ha) (fun hn => hn hb)).elim
    · exact (h.elim (fun hn => hn hb) (fun hn => hn ha)).elim

/-- Repair at an edge within the left path by reversing its trailing piece. -/
private theorem repair_left {V : Type*} {G : SimpleGraph V} {L R : List V}
    {x y u v : V} (hl : L.IsChain G.Adj) (hr : R.IsChain G.Adj)
    (hx : L.getLast? = some x) (hy : R.head? = some y)
    (hxu : G.Adj x u) (hyv : G.Adj y v)
    {P Q : List V} (hcut : L = P ++ u :: v :: Q) :
    ∃ W : List V, W.Perm (L ++ R) ∧ W.IsChain G.Adj := by
  let L₁ := P ++ [u]
  let L₂ := v :: Q
  have hl12 : L = L₁ ++ L₂ := by simpa [L₁,L₂,List.append_assoc] using hcut
  have hl₁ : L₁.IsChain G.Adj := (hl12 ▸ hl).left_of_append
  have hl₂ : L₂.IsChain G.Adj := (hl12 ▸ hl).right_of_append
  have hx₂ : L₂.getLast? = some x := by
    rw [hl12, List.getLast?_append_of_ne_nil _ (by simp [L₂])] at hx
    exact hx
  have hv₂ : L₂.head? = some v := by simp [L₂]
  have hrevH : L₂.reverse.head? = some x := by rwa [List.head?_reverse]
  have hrevL : L₂.reverse.getLast? = some v := by rwa [List.getLast?_reverse]
  have hlast : L₁.getLast? = some u := by simp [L₁]
  refine ⟨L₁ ++ (L₂.reverse ++ R), ?_, ?_⟩
  · apply (((List.reverse_perm L₂).append_right R).append_left L₁).trans
    exact List.Perm.of_eq ((List.append_assoc L₁ L₂ R).symm.trans
      (congrArg (· ++ R) hl12.symm))
  · have hjoin := append_chain (reverse_chain hl₂) hr hrevL hy hyv.symm
    apply append_chain hl₁ hjoin hlast _ hxu.symm
    simp [hrevH]

/-- Repair at an edge within the right path by reflecting both paths. -/
private theorem repair_right {V : Type*} {G : SimpleGraph V} {L R : List V}
    {x y u v : V} (hl : L.IsChain G.Adj) (hr : R.IsChain G.Adj)
    (hx : L.getLast? = some x) (hy : R.head? = some y)
    (hxu : G.Adj x u) (hyv : G.Adj y v)
    {P Q : List V} (hcut : R = P ++ u :: v :: Q) :
    ∃ W : List V, W.Perm (L ++ R) ∧ W.IsChain G.Adj := by
  have hy' : R.reverse.getLast? = some y := by rwa [List.getLast?_reverse]
  have hx' : L.reverse.head? = some x := by rwa [List.head?_reverse]
  have hcut' : R.reverse = Q.reverse ++ v :: u :: P.reverse := by
    rw [hcut]
    simp [List.reverse_append, List.reverse_cons, List.append_assoc]
  obtain ⟨W, hW, hc⟩ :=
    repair_left (reverse_chain hr) (reverse_chain hl) hy' hx' hyv hxu hcut'
  refine ⟨W, hW.trans ?_, hc⟩
  rw [← List.reverse_append]
  exact List.reverse_perm _

private theorem split_closure {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {x y : V}
    (hd : Fintype.card V ≤ G.degree x + G.degree y + 1)
    (P Q : List V) (hn : (P ++ x :: y :: Q).Nodup)
    (hc : (P ++ x :: y :: Q).IsChain (G ⊔ edge x y).Adj)
    (hall : ∀ z : V, z ∈ P ++ x :: y :: Q) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  let L := P ++ [x]
  let R := y :: Q
  let l := L ++ R
  have hLRe : l = P ++ x :: y :: Q := by simp [l,L,R,List.append_assoc]
  rw [← hLRe] at hn hc hall
  have hno_x : x ∉ R := by
    intro h
    exact (List.nodup_append.mp hn).2.2 x (by simp [L]) x h rfl
  have hno_y : y ∉ L := by
    intro h
    exact (List.nodup_append.mp hn).2.2 y h y (by simp [R]) rfl
  have hl := augmented_chain_excluding (x := x) (y := y) hc.left_of_append (Or.inr hno_y)
  have hr := augmented_chain_excluding (x := x) (y := y) hc.right_of_append (Or.inl hno_x)
  have hx : L.getLast? = some x := by simp [L]
  have hy : R.head? = some y := by simp [R]
  have hLe : L ≠ [] := by simp [L]
  have hRe : R ≠ [] := by simp [R]
  let s := L.head hLe
  let t := R.getLast hRe
  have hs : L.head? = some s := List.head?_eq_some_head hLe
  have ht : R.getLast? = some t := List.getLast?_eq_some_getLast hRe
  have hst : l.head? = some s := by simp [l,hs]
  have htt : l.getLast? = some t := by simp [l,ht]
  by_cases hxt : G.Adj x t
  · apply trace_of_permuted_chain hn hall ((List.reverse_perm R).append_left L) _ x
    apply append_chain hl (reverse_chain hr) hx _ hxt
    rwa [List.head?_reverse]
  by_cases hys : G.Adj y s
  · apply trace_of_permuted_chain hn hall ((List.reverse_perm L).append_right R) _ x
    apply append_chain (reverse_chain hl) hr _ hy hys.symm
    rwa [List.getLast?_reverse]
  have hlen : l.length = Fintype.card V := by
    rw [← List.toFinset_card_of_nodup hn]
    have he : l.toFinset = univ := by ext z; simp [hall]
    simp [he]
  let I := Fin (l.length - 1)
  let u (i : I) : V := l[i.val]'(by have := i.isLt; omega)
  let v (i : I) : V := l[i.val+1]'(by have := i.isLt; omega)
  let S : Finset I := univ.filter fun i => G.Adj x (u i)
  let T : Finset I := univ.filter fun i => G.Adj y (v i)
  have hS : G.degree x ≤ S.card := by
    have hsub : G.neighborFinset x ⊆ S.image u := by
      intro z hz
      have hzx := (mem_neighborFinset G x z).mp hz
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem (hall z)
      have hjlt : j < l.length - 1 := by
        by_contra! hh
        have hj' : j + 1 = l.length := by omega
        have hz : l[j] = t := by
          have hlne : l ≠ [] := List.ne_nil_of_mem (hall x)
          have hget : l.getLast hlne = t := List.getLast_of_getLast?_eq_some htt
          rw [List.getLast_eq_getElem] at hget
          have he : j = l.length - 1 := by omega
          exact he ▸ hget
        exact hxt (hz ▸ hzx)
      refine mem_image.mpr ⟨⟨j,hjlt⟩, mem_filter.mpr ⟨mem_univ _, ?_⟩, rfl⟩
      exact hzx
    exact (card_le_card hsub).trans card_image_le
  have hT : G.degree y ≤ T.card := by
    have hsub : G.neighborFinset y ⊆ T.image v := by
      intro z hz
      have hzy := (mem_neighborFinset G y z).mp hz
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem (hall z)
      have hj0 : 0 < j := by
        by_contra! hh
        have he : j = 0 := by omega
        have hlne : l ≠ [] := List.ne_nil_of_mem (hall x)
        have hget : l.head hlne = s := List.head_of_head?_eq_some hst
        rw [List.head_eq_getElem] at hget
        subst j
        exact hys (hget ▸ hzy)
      have hjlt : j - 1 < l.length - 1 := by omega
      let i : I := ⟨j - 1, hjlt⟩
      have hi : v i = l[j] := by
        change l[j - 1 + 1]'(by omega) = l[j]
        congr 1
        omega
      exact mem_image.mpr ⟨i, mem_filter.mpr ⟨mem_univ _, hi.symm ▸ hzy⟩, hi⟩
    exact (card_le_card hsub).trans card_image_le
  have hpidx : P.length < l.length - 1 := by rw [hLRe]; simp
  let i₀ : I := ⟨P.length, hpidx⟩
  have hu₀ : u i₀ = x := by
    change (L ++ R)[P.length]'(by simp [L, R]) = x
    rw [List.getElem_append_left (by simp [L]), List.getElem_append_right le_rfl]
    simp
  have hv₀ : v i₀ = y := by
    change (L ++ R)[P.length + 1]'(by simp [L, R]) = y
    rw [List.getElem_append_right (by simp [L])]
    simp [L, R]
  have hout : i₀ ∉ S ∪ T := by
    simp [S,T,hu₀,hv₀]
  have hcap : (S ∪ T).card < l.length - 1 := by
    have hne : S ∪ T ≠ (univ : Finset I) := fun h => hout (h ▸ mem_univ _)
    have hh := card_lt_card (ssubset_univ_iff.mpr hne)
    simpa [I] using hh
  obtain ⟨i, hiS, hiT⟩ : ∃ i, i ∈ S ∧ i ∈ T := by
    by_contra! h
    have hdis : Disjoint S T := disjoint_left.mpr h
    have hcard := card_union_of_disjoint hdis
    omega
  have hxu : G.Adj x (u i) := (mem_filter.mp hiS).2
  have hyv : G.Adj y (v i) := (mem_filter.mp hiT).2
  have hin : i.val ≠ P.length := by
    intro h
    have hi0 : i = i₀ := Fin.ext h
    exact hout (mem_union_left _ (hi0 ▸ hiS))
  have hit := i.isLt
  have hLv : L.length = P.length + 1 := by simp [L]
  rcases lt_or_gt_of_ne hin with hbefore | hafter
  · have hixy : i.val + 1 < L.length := by omega
    obtain ⟨A,B,hAB⟩ := split_at_pair L i.val hixy
    have hu : u i = L[i.val]'(by omega) := List.getElem_append_left (by omega)
    have hv : v i = L[i.val+1] := List.getElem_append_left hixy
    rw [← hu, ← hv] at hAB
    obtain ⟨W, hw, hWc⟩ := repair_left hl hr hx hy hxu hyv hAB
    exact trace_of_permuted_chain hn hall hw hWc x
  · let j := i.val - L.length
    have hlen' : l.length = L.length + R.length := List.length_append
    have hj : j + 1 < R.length := by dsimp [j]; omega
    obtain ⟨A,B,hAB⟩ := split_at_pair R j hj
    have hu : u i = R[j]'(by omega) := List.getElem_append_right (by omega)
    have hv : v i = R[j+1] := by
      unfold v
      change (L ++ R)[i.val+1] = R[j+1]
      rw [List.getElem_append_right (by omega)]
      congr 1
      dsimp [j]
      omega
    rw [← hu, ← hv] at hAB
    obtain ⟨W, hw, hWc⟩ := repair_right hl hr hx hy hxu hyv hAB
    exact trace_of_permuted_chain hn hall hw hWc x

/-- Hamiltonian-path closure at a nonedge whose end degrees sum to at least n−1. -/
theorem traceable_of_sup_edge {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {x y : V}
    (_hne : x ≠ y) (_hxy : ¬ G.Adj x y)
    (hd : Fintype.card V ≤ G.degree x + G.degree y + 1)
    (hpath : ∃ a b : V, ∃ p : (G ⊔ edge x y).Walk a b, p.IsHamiltonian) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  obtain ⟨a,b,p,hp⟩ := hpath
  let l := p.support
  have hn := hp.isPath.support_nodup
  have hall := hp.mem_support
  have hc := p.isChain_adj_support
  by_cases hG : l.IsChain G.Adj
  · exact trace_of_list l hn hG hall p.support_ne_nil
  obtain ⟨i, hi, hbad⟩ := List.exists_not_getElem_of_not_isChain hG
  obtain ⟨P,Q,he⟩ := split_at_pair l i hi
  have hu : (G ⊔ edge x y).Adj l[i] l[i+1] :=
    List.isChain_iff_forall_rel_of_append_cons_cons.mp hc he
  rcases hu with h | h
  · exact (hbad h).elim
  have hh := (edge_adj x y _ _).mp h
  rcases hh.1 with ⟨hx,hy⟩ | ⟨hx,hy⟩
  · rw [hx,hy] at he
    exact split_closure hd P Q (he ▸ hn) (he ▸ hc) (he ▸ hall)
  · rw [hx,hy] at he
    have hc' : l.IsChain (G ⊔ edge y x).Adj := by simpa only [edge_comm y x] using hc
    exact split_closure (by omega) P Q (he ▸ hn) (he ▸ hc') (he ▸ hall)

end Graph189
end

section
namespace Graph189SmallRoot
open SimpleGraph
variable {V : Type*}
/-- Adjoin a marker of degree one next to c. -/
def marked (G : SimpleGraph V) (c : V) : SimpleGraph (Option V) where
  Adj
    | none, none => False
    | none, some y => y = c
    | some x, none => x = c
    | some x, some y => G.Adj x y
  symm := by
    constructor
    intro x y h
    cases x <;> cases y
    · exact h
    · exact h
    · exact h
    · exact h.symm
  loopless := by
    constructor
    intro x
    cases x
    · exact id
    · exact G.loopless.irrefl _

end Graph189SmallRoot
end

section
namespace Graph189SmallRoot
open SimpleGraph Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Traceability can be tested after completing any high-degree set. -/
theorem trace_of_clique_extension {G : SimpleGraph V} [DecidableRel G.Adj]
    (high : V → Prop) (k : ℕ) (horder : Fintype.card V ≤ 2 * k + 1)
    (hdegree : ∀ x, high x → k ≤ G.degree x)
    (finish : ∀ K : SimpleGraph V, G ≤ K →
      (∀ x y, high x → high y → x ≠ y → K.Adj x y) →
      ∃ a b, ∃ p : K.Walk a b, p.IsHamiltonian) :
    ∃ a b, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  let T (K : SimpleGraph V) := ∃ a b, ∃ p : K.Walk a b, p.IsHamiltonian
  change T G
  by_contra hn
  obtain ⟨K, hGK, hm⟩ := Finite.exists_le_maximal (p := fun K => ¬ T K) hn
  apply hm.prop
  apply finish K hGK
  intro x y hx hy hne
  have mono (v : V) : G.degree v ≤ K.degree v := by
    apply Finset.card_le_card
    intro u hu
    exact (K.mem_neighborFinset _ _).mpr (hGK ((G.mem_neighborFinset _ _).mp hu))
  have hsum : Fintype.card V ≤ K.degree x + K.degree y + 1 := by
    have := (hdegree x hx).trans (mono x)
    have := (hdegree y hy).trans (mono y)
    omega
  by_contra hxy
  have hnot : ¬ T (K ⊔ edge x y) := fun hp =>
    hm.prop (Graph189.traceable_of_sup_edge hne hxy hsum hp)
  exact hxy (hm.le_of_ge hnot le_sup_left
    (Or.inr ((edge_adj _ _ _ _).mpr ⟨Or.inl ⟨rfl,rfl⟩,hne⟩)))

omit [Fintype V] in
/-- A gate-rooted clique traversal lifts to a Hamilton path in a marked supergraph. -/
private theorem prefix_marker {G : SimpleGraph V} {c : V} {K : SimpleGraph (Option V)}
    (hGK : marked G c ≤ K) (L : List V) (hhead : L.head? = some c)
    (hnodup : L.Nodup) (hchain : L.IsChain (K.comap some).Adj)
    (hcover : ∀ v : V, v ∈ L) : ∃ a b, ∃ p : K.Walk a b, p.IsHamiltonian := by
  let W : List (Option V) := none :: L.map some
  have hWn : W.Nodup := List.nodup_cons.mpr ⟨by simp, hnodup.map (Option.some_injective V)⟩
  have hc : W.IsChain K.Adj := by
    apply List.isChain_cons.mpr
    refine ⟨?_, (List.isChain_map _).mpr hchain⟩
    intro y hy
    have he : some c = y := by simpa [List.head?_map,hhead] using hy
    subst y
    exact hGK (show (marked G c).Adj none (some c) from rfl)
  have hw (v : Option V) : v ∈ W := by
    cases v with
    | none => simp [W]
    | some x => simp [W,hcover x]
  let path := SimpleGraph.Walk.ofSupport W (by simp [W]) hc
  have hs : path.support = W := Walk.support_ofSupport _ hc
  exact ⟨_, _, path, (Walk.IsPath.mk' (hs.symm ▸ hWn)).isHamiltonian_of_mem
    (fun v => hs.symm ▸ hw v)⟩

/-- The clique completion argument on a finite side with prescribed gate. -/
theorem marked_trace_at_small_root_of_finish
    (finishClique : ∀ {Q : SimpleGraph V} (A : Finset V) {c : V}, c ∉ A →
      (∃ u ∈ A, Q.Adj c u) →
      ((∀ {u v}, u ∈ A → v ∈ A → u ≠ v → Q.Adj u v) ∨
        ∃ z ∈ A, ∀ {u v}, u ∈ A.erase z → v ∈ A.erase z → u ≠ v → Q.Adj u v) →
      (∀ u ∈ A, ∃ x ∈ insert c A, ∃ y ∈ insert c A, x ≠ y ∧ Q.Adj u x ∧ Q.Adj u y) →
      ∃ L : List V, L.head? = some c ∧ L.Nodup ∧ L.IsChain Q.Adj ∧
        ∀ x, x ∈ L ↔ x = c ∨ x ∈ A)
    (G : SimpleGraph V) [DecidableRel G.Adj] (c : V) (k : ℕ)
    (hsize : Fintype.card V ≤ 2*k) (hc : ∃ u, G.Adj c u)
    (hpair : ∀ u v, u ≠ c → v ≠ c → u ≠ v → k ≤ G.degree u ∨ k ≤ G.degree v)
    (htwo : ∀ u, u ≠ c → 2 ≤ G.degree u) :
    ∃ a b, ∃ p : (marked G c).Walk a b, p.IsHamiltonian := by
  classical
  let H (u : Option V) := ∃ v : V, u = some v ∧ k ≤ G.degree v
  apply trace_of_clique_extension H k
  · rw [Fintype.card_option]
    omega
  · intro u hu
    obtain ⟨v,rfl,hv⟩ := hu
    apply hv.trans
    rw [← G.card_neighborSet_eq_degree v, ← (marked G c).card_neighborSet_eq_degree _]
    let f (y : G.neighborSet v) : (marked G c).neighborSet (some v) :=
      ⟨some y.val, y.property⟩
    apply Fintype.card_le_of_injective f
    intro s t eq
    exact Subtype.ext (Option.some.inj (congrArg Subtype.val eq))
  · intro K hGK hK
    let Q := K.comap (some : V → Option V)
    have hGQ : G ≤ Q := by
      intro x y h
      exact hGK (show (marked G c).Adj (some x) (some y) from h)
    let A : Finset V := univ.erase c
    have hA (u : V) : u ∈ A ↔ u ≠ c := by simp [A]
    have hi (u : V) : u ∈ insert c A := by by_cases h : u = c <;> simp [A,h]
    have hhigh {u v : V} (hu : k ≤ G.degree u) (hv : k ≤ G.degree v) (hne : u ≠ v) :
        Q.Adj u v :=
      hK (some u) (some v) ⟨u,rfl,hu⟩ ⟨v,rfl,hv⟩ (fun e => hne (Option.some.inj e))
    apply Exists.elim (finishClique (Q := Q) A (c := c) (by simp [A]) _ _ _)
    · intro L hL
      exact prefix_marker hGK L hL.1 hL.2.1 hL.2.2.1 (fun x => (hL.2.2.2 x).mpr
        (by by_cases e : x = c; exact Or.inl e; exact Or.inr ((hA x).mpr e)))
    · obtain ⟨u,hu⟩ := hc
      exact ⟨u,(hA u).mpr hu.ne.symm,hGQ hu⟩
    · by_cases hall : ∀ u ∈ A, k ≤ G.degree u
      · exact Or.inl (fun hx hy hxy => hhigh (hall _ hx) (hall _ hy) hxy)
      · push Not at hall
        obtain ⟨z,hz,hlow⟩ := hall
        have high {u : V} (hu : u ∈ A.erase z) : k ≤ G.degree u := by
          obtain ⟨hne,hin⟩ := mem_erase.mp hu
          exact (hpair u z ((hA u).mp hin) ((hA z).mp hz) hne).resolve_right
            (by omega)
        exact Or.inr ⟨z,hz,(fun hu hv hne => hhigh (high hu) (high hv) hne)⟩
    · intro u hu
      have hd : 1 < (G.neighborFinset u).card := by
        rw [G.card_neighborFinset_eq_degree]
        exact htwo u ((hA u).mp hu)
      obtain ⟨x,hx,y,hy,ne⟩ := Finset.one_lt_card.mp hd
      exact ⟨x,hi x,y,hi y,ne,hGQ ((G.mem_neighborFinset u x).mp hx),
        hGQ ((G.mem_neighborFinset u y).mp hy)⟩


end Graph189SmallRoot
end

section
namespace Graph189

open SimpleGraph Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

omit [DecidableEq V] in
private theorem chain_of_clique_list {s : V → Prop} {L : List V}
    (hn : L.Nodup) (hm : ∀ x ∈ L, s x)
    (hclique : ∀ {u v}, s u → s v → u ≠ v → G.Adj u v) :
    L.IsChain G.Adj :=
  List.Pairwise.isChain (hn.imp_of_mem (fun {_ _} ha hb hne =>
    hclique (hm _ ha) (hm _ hb) hne))

/-- A finite clique has a spanning path starting at any prescribed member. -/
theorem rootedCliqueList (s : Finset V) {r : V} (hr : r ∈ s)
    (hclique : ∀ {u v}, u ∈ s → v ∈ s → u ≠ v → G.Adj u v) :
    ∃ L : List V, L.head? = some r ∧ L.Nodup ∧ L.IsChain G.Adj ∧
      ∀ x, x ∈ L ↔ x ∈ s := by
  let L := r :: (s.erase r).toList
  have hm (x : V) : x ∈ L ↔ x ∈ s := by
    by_cases hx : x = r <;> simp [L, hx, hr]
  have hn : L.Nodup := List.nodup_cons.mpr ⟨by simp, Finset.nodup_toList _⟩
  exact ⟨L, rfl, hn, chain_of_clique_list hn (fun x hx => (hm x).mp hx) hclique, hm⟩

/-- A finite clique has a spanning path between distinct prescribed members. -/
theorem rootedCliqueBetweenList (s : Finset V) {r t : V}
    (hr : r ∈ s) (ht : t ∈ s) (hrt : r ≠ t)
    (hclique : ∀ {u v}, u ∈ s → v ∈ s → u ≠ v → G.Adj u v) :
    ∃ L : List V, L.head? = some r ∧ L.getLast? = some t ∧
      L.Nodup ∧ L.IsChain G.Adj ∧ ∀ x, x ∈ L ↔ x ∈ s := by
  let L := r :: (((s.erase r).erase t).toList ++ [t])
  have hm (x : V) : x ∈ L ↔ x ∈ s := by
    by_cases hxr : x = r
    · simp [L, hxr, hr]
    by_cases hxt : x = t
    · simp [L, hxt, ht]
    · simp [L, hxr, hxt]
  have hn : L.Nodup := by
    apply List.nodup_cons.mpr
    refine ⟨by simp [hrt], List.nodup_append.mpr ⟨Finset.nodup_toList _, by simp, ?_⟩⟩
    intro x hx y hy hxy
    have hyt : y = t := by simpa using hy
    exact (Finset.mem_erase.mp (Finset.mem_toList.mp hx)).1 (hxy.trans hyt)
  have hlast : L.getLast? = some t := by simp [L, List.getLast?_cons, List.getLast?_append]
  exact ⟨L, rfl, hlast, hn, chain_of_clique_list hn (fun x hx => (hm x).mp hx) hclique, hm⟩

/-- A graph that is a clique except at z has a rooted spanning path if z has a
clique neighbor different from the root, or if the root is z itself. -/
theorem rootedCliqueExceptList (s : Finset V) {r z : V}
    (hr : r ∈ s) (hz : z ∈ s)
    (hclique : ∀ {u v}, u ∈ s.erase z → v ∈ s.erase z → u ≠ v → G.Adj u v)
    (hcontact : ∃ u ∈ s.erase z, G.Adj z u ∧ (r = z ∨ r ≠ u)) :
    ∃ L : List V, L.head? = some r ∧ L.Nodup ∧ L.IsChain G.Adj ∧
      ∀ x, x ∈ L ↔ x ∈ s := by
  obtain ⟨u, hu, hzu, hroot⟩ := hcontact
  by_cases hrz : r = z
  · subst r
    obtain ⟨L, hhead, hn, hc, hm⟩ := rootedCliqueList (G := G) (s.erase z) hu hclique
    refine ⟨z :: L, rfl, ?_, ?_, ?_⟩
    · exact List.nodup_cons.mpr ⟨fun hmz => (Finset.mem_erase.mp ((hm z).mp hmz)).1 rfl, hn⟩
    · exact hc.cons (by simpa [hhead] using hzu)
    · intro x
      by_cases hx : x = z <;> simp [hx, hz, hm]
  · have hru : r ≠ u := hroot.resolve_left hrz
    obtain ⟨L, hhead, hlast, hn, hc, hm⟩ :=
      rootedCliqueBetweenList (G := G) (s.erase z) (Finset.mem_erase.mpr ⟨hrz,hr⟩) hu hru hclique
    refine ⟨L ++ [z], ?_, ?_, ?_, ?_⟩
    · have hne : L ≠ [] := by intro he; simp [he] at hhead
      rwa [List.head?_append_of_ne_nil _ hne]
    · apply List.nodup_append.mpr
      refine ⟨hn, by simp, ?_⟩
      intro x hx y hy hxy
      have hyz : y = z := by simpa using hy
      exact (Finset.mem_erase.mp ((hm x).mp hx)).1 (hxy.trans hyz)
    · apply hc.append (List.IsChain.singleton z)
      intro x hx y hy
      have hux : u = x := by simpa [hlast] using hx
      have hzy : z = y := by simpa using hy
      exact hux ▸ hzy ▸ hzu.symm
    · intro x
      by_cases hx : x = z <;> simp [hx, hz, hm]

/-- Span a core from its gate after closure has made all but at most one core
vertex a clique. Two internal neighbors suffice for the exceptional vertex. -/
theorem rootedGateCliqueList (A : Finset V) {c : V} (hc : c ∉ A)
    (hcontact : ∃ u ∈ A, G.Adj c u)
    (hshape : (∀ {u v}, u ∈ A → v ∈ A → u ≠ v → G.Adj u v) ∨
      ∃ z ∈ A, ∀ {u v}, u ∈ A.erase z → v ∈ A.erase z → u ≠ v → G.Adj u v)
    (htwo : ∀ u ∈ A, ∃ x ∈ insert c A, ∃ y ∈ insert c A,
      x ≠ y ∧ G.Adj u x ∧ G.Adj u y) :
    ∃ L : List V, L.head? = some c ∧ L.Nodup ∧ L.IsChain G.Adj ∧
      ∀ x, x ∈ L ↔ x = c ∨ x ∈ A := by
  suffices h : ∃ u, G.Adj c u ∧ ∃ L : List V, L.head? = some u ∧
      L.Nodup ∧ L.IsChain G.Adj ∧ ∀ x, x ∈ L ↔ x ∈ A by
    obtain ⟨u, hcu, L, hhead, hn, hchain, hm⟩ := h
    refine ⟨c :: L, rfl, List.nodup_cons.mpr ⟨fun h => hc ((hm c).mp h), hn⟩, ?_, ?_⟩
    · exact hchain.cons (by simpa [hhead] using hcu)
    · intro x
      simp [hm, eq_comm]
  obtain ⟨u, hu, hcu⟩ := hcontact
  rcases hshape with hclique | ⟨z, hz, hclique⟩
  · exact ⟨u, hcu, rootedCliqueList (G := G) A hu hclique⟩
  obtain ⟨x, hx, y, hy, hxy, hzx, hzy⟩ := htwo z hz
  by_cases hcz : G.Adj c z
  · refine ⟨z, hcz, rootedCliqueExceptList (G := G) A hz hz hclique ?_⟩
    by_cases hxc : x = c
    · have hyc : y ≠ c := fun he => hxy (hxc.trans he.symm)
      exact ⟨y, Finset.mem_erase.mpr ⟨hzy.ne.symm, (Finset.mem_insert.mp hy).resolve_left hyc⟩,
        hzy, Or.inl rfl⟩
    · exact ⟨x, Finset.mem_erase.mpr ⟨hzx.ne.symm, (Finset.mem_insert.mp hx).resolve_left hxc⟩,
        hzx, Or.inl rfl⟩
  · refine ⟨u, hcu, rootedCliqueExceptList (G := G) A hu hz hclique ?_⟩
    have hxc : x ≠ c := fun he => hcz (he ▸ hzx).symm
    have hyc : y ≠ c := fun he => hcz (he ▸ hzy).symm
    by_cases hxu : x = u
    · have huy : u ≠ y := fun he => hxy (hxu.trans he)
      exact ⟨y, Finset.mem_erase.mpr ⟨hzy.ne.symm, (Finset.mem_insert.mp hy).resolve_left hyc⟩,
        hzy, Or.inr huy⟩
    · exact ⟨x, Finset.mem_erase.mpr ⟨hzx.ne.symm, (Finset.mem_insert.mp hx).resolve_left hxc⟩,
        hzx, Or.inr (fun he => hxu he.symm)⟩


end Graph189
end

section
namespace Graph189SmallRoot
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A finite side of order at most 2k has a marked Hamilton path if
every pair off the gate contains a high vertex and all such vertices
have at least two neighbors. -/
theorem marked_trace_at_small_root
    (G : SimpleGraph V) [DecidableRel G.Adj] (c : V) (k : ℕ)
    (hsize : Fintype.card V ≤ 2*k) (hc : ∃ u, G.Adj c u)
    (hpair : ∀ u v, u ≠ c → v ≠ c → u ≠ v → k ≤ G.degree u ∨ k ≤ G.degree v)
    (htwo : ∀ u, u ≠ c → 2 ≤ G.degree u) :
    ∃ a b, ∃ p : (marked G c).Walk a b, p.IsHamiltonian := by
  apply marked_trace_at_small_root_of_finish _ G c k hsize hc hpair htwo
  intro Q A root out contact shape two
  exact Graph189.rootedGateCliqueList A out contact shape two

end Graph189SmallRoot
end

section
namespace Graph189SmallRoot
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V} {c : V}

private theorem contact_eq {a : Option V} (h : (marked G c).Adj a none) :
    a = some c := by
  cases a with
  | none => exact False.elim h
  | some a => exact congrArg some h

private theorem endpoint : ∀ (l : List (Option V)), l.Nodup →
    l.IsChain (marked G c).Adj → none ∈ l →
    l.head? = some none ∨ l.getLast? = some none
  | [], _, _, hm => by simp at hm
  | [a], _, _, hm => by
    have h : none = a := by simpa using hm
    exact Or.inl (by simp [← h])
  | a :: b :: l, hn, hc, hm => by
    by_cases ha : a = none
    · exact Or.inl (by simp [ha])
    have mem : none ∈ b :: l := (List.mem_cons.mp hm).resolve_left (Ne.symm ha)
    rcases endpoint (b :: l) (List.nodup_cons.mp hn).2
        (List.isChain_cons_cons.mp hc).2 mem with first | last
    · have hb : b = none := by simpa using first
      subst b
      cases l with
      | nil => exact Or.inr (by simp)
      | cons d t =>
        have links := List.isChain_cons_cons.mp hc
        have ad : a = d := (contact_eq links.1).trans
          (contact_eq (List.isChain_cons_cons.mp links.2).1.symm).symm
        exact False.elim ((List.nodup_cons.mp hn).1 (by simp [ad]))
    · exact Or.inr (by simpa using last)

private theorem all_some : ∀ (l : List (Option V)), none ∉ l →
    ∃ s : List V, l = s.map some
  | [], _ => ⟨[], rfl⟩
  | none :: _, hn => False.elim (hn (by simp))
  | some x :: xs, hn => by
    obtain ⟨ys, hy⟩ := all_some xs (fun h => hn (List.mem_cons_of_mem _ h))
    exact ⟨x :: ys, by simp [hy]⟩

theorem rooted_of_marked_traceable [DecidableEq V]
    (h : ∃ a b, ∃ p : (marked G c).Walk a b, p.IsHamiltonian) :
    ∃ L : List V, L.head? = some c ∧ L.Nodup ∧ L.IsChain G.Adj ∧ ∀ v, v ∈ L := by
  obtain ⟨_, _, p, hp⟩ := h
  have orient : ∃ l : List (Option V), l.head? = some none ∧ l.Nodup ∧
      l.IsChain (marked G c).Adj ∧ ∀ w, w ∈ l := by
    rcases endpoint p.support hp.isPath.support_nodup p.isChain_adj_support
      (hp.mem_support none) with left | right
    · exact ⟨_, left, hp.isPath.support_nodup, p.isChain_adj_support, hp.mem_support⟩
    · refine ⟨p.support.reverse, by simpa using right, by simpa using hp.isPath.support_nodup,
        List.isChain_reverse.mpr (p.isChain_adj_support.imp fun _ _ e => e.symm), ?_⟩
      simpa using hp.mem_support
  obtain ⟨l, first, nodup, chain, full⟩ := orient
  cases l with
  | nil => simp at first
  | cons m r =>
    have hm : m = none := by simpa using first
    subst m
    obtain ⟨s, rfl⟩ := all_some r (List.nodup_cons.mp nodup).1
    have all (v : V) : v ∈ s := by simpa using full (some v)
    have sc : s.IsChain G.Adj :=
      (List.isChain_map some).mp chain.tail
    refine ⟨s, ?_, List.Nodup.of_map some (List.nodup_cons.mp nodup).2, sc, all⟩
    cases s with
    | nil => exact False.elim (by simpa using all c)
    | cons x xs =>
      have hxc : x = c := (List.isChain_cons_cons.mp chain).1
      simp [hxc]
end Graph189SmallRoot
end

section
namespace Graph189CutH1
open SimpleGraph Graph189CutCore Graph189InducedSide Graph189SmallRoot
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]

/-- Every large-order graph in the cut-vertex branch of WOWII Graph 189
has a Hamiltonian path. This is the complete mathematical statement of R2.H1. -/
theorem cut_vertex_case (G : SimpleGraph V) [DecidableRel G.Adj] (hc : G.Connected)
    (hσ : ∀ v, G.distEven v ≤ 1 + G.secondSmallestDegree)
    (horder : 2 * G.secondSmallestDegree + 3 ≤ Fintype.card V)
    (hcut : ∃ c : V, ¬ (G.induce {v | v ≠ c}).Connected) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  apply Graph189CutH1Assembly.h1_of_small_rooted hc hσ horder hcut
  intro c A hA hsize
  have hp := Finset.card_pos.mpr hA.nonempty
  apply small_side_of_induced (k := G.secondSmallestDegree) hA hc (by omega)
    (Graph189CutCore.degree_pair (G := G)) (Graph189CutBounds.two_le_degree hc hσ horder)
  intro hsz hcontact hpair htwo
  apply rooted_of_marked_traceable
  exact marked_trace_at_small_root (sideGraph G c A) (sideRoot c A)
    G.secondSmallestDegree hsz hcontact hpair htwo

end Graph189CutH1
end

theorem OMA.solution : OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R2.H1 := by
  intro V _ _ _ G _ hc hσ horder hcut
  exact Graph189CutH1.cut_vertex_case G hc hσ horder hcut
