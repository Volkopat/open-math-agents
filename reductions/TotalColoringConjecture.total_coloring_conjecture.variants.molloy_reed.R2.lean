import FormalConjectures.Wikipedia.TotalColoringConjecture
import Mathlib

/-! # The bounded reject-graph step in the Molloy–Reed total-coloring theorem

Following Molloy and Reed, Graph Colouring and the Probabilistic Method, chapters 17–18,
use a fixed proper edge coloring of a regular completion and find a vertex coloring
whose conflicting edges form a bounded-degree graph. A separate palette for those
edges finishes the coloring. Bounded-degree input graphs are handled directly by
greedy vertex coloring and the same separate-palette construction. -/

namespace OMA.MolloyReedCompletion

open SimpleGraph

/-- Duplicate the graph, adding a cross-edge for each vertex of degree below `d`. -/
private theorem duplicateStep {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) :
    ∃ H : SimpleGraph (V × Bool), ∃ _ : DecidableRel H.Adj,
      Nonempty (G ↪g H) ∧ ∀ (v : V) (b : Bool),
        H.degree (v,b) = G.degree v + if G.degree v < d then 1 else 0 := by
  let H : SimpleGraph (V × Bool) :=
    { Adj := fun x y =>
        (x.2 = y.2 ∧ G.Adj x.1 y.1) ∨ (x.1 = y.1 ∧ x.2 ≠ y.2 ∧ G.degree x.1 < d)
      symm := by
        constructor
        rintro x y (⟨h,h'⟩ | ⟨h,h',hz⟩)
        · exact Or.inl ⟨h.symm, h'.symm⟩
        · exact Or.inr ⟨h.symm, Ne.symm h', h ▸ hz⟩
      loopless := by
        constructor
        intro x
        simp }
  let hAdj : DecidableRel H.Adj := Classical.decRel _
  let e : G ↪g H :=
    { toEmbedding := ⟨fun v => (v, false), fun _ _ h => congrArg Prod.fst h⟩
      map_rel_iff' := by
        intro u v
        change (false = false ∧ G.Adj u v) ∨
          (u = v ∧ false ≠ false ∧ G.degree u < d) ↔ G.Adj u v
        simp }
  refine ⟨H, hAdj, ⟨e⟩, ?_⟩
  intro v b
  let same : V ↪ V × Bool :=
    ⟨fun w => (w,b), fun _ _ h => congrArg Prod.fst h⟩
  let old := (G.neighborFinset v).map same
  let cross : Finset (V × Bool) := if G.degree v < d then {(v,!b)} else ∅
  have hOld (w : V) (c : Bool) : (w,c) ∈ old ↔ b = c ∧ G.Adj v w := by
    change (w,c) ∈ (G.neighborFinset v).map same ↔ _
    rw [Finset.mem_map]
    constructor
    · rintro ⟨z,hz,h⟩
      change (z,b) = (w,c) at h
      obtain ⟨hw,hc⟩ := Prod.mk.inj h
      exact ⟨hc,(G.mem_neighborFinset v w).mp (hw ▸ hz)⟩
    · rintro ⟨hc, hw⟩
      refine ⟨w,(G.mem_neighborFinset v w).mpr hw,?_⟩
      change (w,b) = (w,c)
      rw [hc]
  have hNeighbors : H.neighborFinset (v,b) = old ∪ cross := by
    ext z
    rcases z with ⟨w,c⟩
    rw [SimpleGraph.mem_neighborFinset, Finset.mem_union, hOld]
    have hb : b ≠ c ↔ c = !b := by cases b <;> cases c <;> decide
    by_cases hd : G.degree v < d
    · simp [H, cross, hd, hb, eq_comm]
    · simp [H, cross, hd]
  have hdisjoint : Disjoint old cross := by
    by_cases hd : G.degree v < d
    · have hn : (v,!b) ∉ old := by rw [hOld]; simp
      simpa [cross, hd] using (Finset.disjoint_singleton_right.mpr hn)
    · simp [cross, hd]
  rw [← H.card_neighborFinset_eq_degree (v,b), hNeighbors,
    Finset.card_union_of_disjoint hdisjoint]
  by_cases hd : G.degree v < d <;> simp [old, cross, hd]

/-- The deficit to the target degree falls by one at each doubling. -/
private theorem completionByDeficit (d t : ℕ) :
    ∀ {V : Type} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj],
      (∀ v, G.degree v ≤ d) → (∀ v, d ≤ G.degree v + t) →
      ∃ W : Type, ∃ _ : Fintype W, ∃ _ : DecidableEq W, ∃ K : SimpleGraph W,
        ∃ _ : DecidableRel K.Adj, Nonempty (G ↪g K) ∧ K.IsRegularOfDegree d := by
  classical
  induction t with
  | zero =>
    intro V hV heq G hdec hlo hhi
    refine ⟨V, hV, heq, G, hdec, ⟨SimpleGraph.Embedding.refl⟩, ?_⟩
    intro v
    exact (hlo v).antisymm (by simpa using hhi v)
  | succ t ih =>
    intro V _ _ G _ hlo hhi
    obtain ⟨H,hHdec,⟨e⟩,hdegree⟩ := duplicateStep G d
    let _ : DecidableRel H.Adj := hHdec
    have hb (x : V × Bool) : H.degree x ≤ d ∧ d ≤ H.degree x + t := by
      rcases x with ⟨v,b⟩
      rw [hdegree]
      by_cases h : G.degree v < d
      · simp only [if_pos h]
        have h' := hhi v
        omega
      · simp only [if_neg h, add_zero]
        have h' := hlo v
        omega
    obtain ⟨W,hW,hWeq,K,hK,⟨f⟩,hKreg⟩ := ih H (fun v => (hb v).1) (fun v => (hb v).2)
    exact ⟨W,hW,hWeq,K,hK,⟨f.comp e⟩,hKreg⟩

private theorem regular_completion {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ W : Type, ∃ _ : Fintype W, ∃ _ : DecidableEq W, ∃ K : SimpleGraph W,
      ∃ _ : DecidableRel K.Adj, Nonempty (G ↪g K) ∧ K.IsRegularOfDegree G.maxDegree :=
  completionByDeficit G.maxDegree G.maxDegree G G.degree_le_maxDegree
    (fun _ => Nat.le_add_left _ _)

end OMA.MolloyReedCompletion

namespace MolloyReedTransfer

open SimpleGraph

/-- Pull back a total coloring along a graph embedding. -/
theorem pullback_isTotalColoring {V W ι : Type*} {G : SimpleGraph V} {K : SimpleGraph W}
    (f : G ↪g K) {c : W ⊕ K.edgeSet → ι} (hc : K.IsTotalColoring c) :
    G.IsTotalColoring (fun x => c (x.map f f.mapEdgeSet)) := by
  have transfer_mem {v : V} {e : G.edgeSet} (h : v ∈ (e : Sym2 V)) :
      f v ∈ (f.mapEdgeSet e : Sym2 W) :=
    Sym2.mem_map.mpr ⟨v, h, rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · intro u v huv
    exact hc.1 (f u) (f v) (f.map_adj_iff.mpr huv)
  · intro e e' hne ⟨v, hv, hv'⟩
    exact hc.2.1 (f.mapEdgeSet e) (f.mapEdgeSet e')
      (f.mapEdgeSet.injective.ne hne) ⟨f v, transfer_mem hv, transfer_mem hv'⟩
  · intro v e hve
    exact hc.2.2 (f v) (f.mapEdgeSet e) (transfer_mem hve)

/-- A regular graph has maximum degree at most its common degree. -/
theorem maxDegree_le_of_regular {W : Type*} [Fintype W] {K : SimpleGraph W}
    [DecidableRel K.Adj] {d : ℕ} (hK : K.IsRegularOfDegree d) : K.maxDegree ≤ d :=
  K.maxDegree_le_of_forall_degree_le d (fun v => (hK.degree_eq v).le)

end MolloyReedTransfer

namespace MolloyReedTransfer

open Finset SimpleGraph

/-- A palette larger than the maximum degree gives a proper vertex
coloring by extending the colored vertex set one vertex at a time. -/
theorem exists_vertex_coloring_of_maxDegree_lt {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} (hk : G.maxDegree < k) :
    ∃ c : V → Fin k, ∀ u v, G.Adj u v → c u ≠ c v := by
  classical
  have hkpos : 0 < k := (Nat.zero_le G.maxDegree).trans_lt hk
  have color_on (S : Finset V) :
      ∃ c : V → Fin k, ∀ u ∈ S, ∀ v ∈ S, G.Adj u v → c u ≠ c v := by
    induction S using Finset.induction_on with
    | empty =>
        exact ⟨fun _ => ⟨0,hkpos⟩, by simp⟩
    | @insert a S _ ih =>
        obtain ⟨c,hc⟩ := ih
        let bad : Finset (Fin k) := (S.filter (G.Adj a)).image c
        have hfilter : S.filter (G.Adj a) ⊆ G.neighborFinset a := by
          intro v hv
          exact (G.mem_neighborFinset a v).mpr (mem_filter.mp hv).2
        have hbad : bad.card < (univ : Finset (Fin k)).card := by
          rw [card_univ, Fintype.card_fin]
          calc
            bad.card ≤ (S.filter (G.Adj a)).card := card_image_le
            _ ≤ (G.neighborFinset a).card := card_le_card hfilter
            _ ≤ G.maxDegree := by rw [G.card_neighborFinset_eq_degree]; exact G.degree_le_maxDegree a
            _ < k := hk
        obtain ⟨color,_,hcolor⟩ := exists_mem_notMem_of_card_lt_card hbad
        have hfresh (v : V) (hv : v ∈ S) (hav : G.Adj a v) : color ≠ c v := by
          intro he
          exact hcolor (mem_image.mpr ⟨v,mem_filter.mpr ⟨hv,hav⟩,he.symm⟩)
        let c' : V → Fin k := fun v => if v = a then color else c v
        refine ⟨c',?_⟩
        intro u hu v hv huv
        by_cases hea : u = a
        · subst u
          have hne : v ≠ a := (G.ne_of_adj huv).symm
          have hvS := (mem_insert.mp hv).resolve_left hne
          simpa [c',hne] using hfresh v hvS huv
        · have huS := (mem_insert.mp hu).resolve_left hea
          by_cases hve : v = a
          · subst v
            simpa [c',hea] using (hfresh u huS huv.symm).symm
          · have hvS := (mem_insert.mp hv).resolve_left hve
            simpa [c',hea,hve] using hc u huS v hvS huv
  obtain ⟨c,hc⟩ := color_on univ
  exact ⟨c,fun u v huv => hc u (mem_univ u) v (mem_univ v) huv⟩

end MolloyReedTransfer

namespace OMA.R_TotalColoringConjecture_total_coloring_conjecture_variants_molloy_reed_R2

open SimpleGraph

/-- Vizing's edge-colouring bound, stated as an explicit witness. -/
def H1 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    ∃ e : G.edgeSet → Fin (G.maxDegree + 1),
      ∀ a b : G.edgeSet, a ≠ b → (∃ v, v ∈ (a : Sym2 V) ∧ v ∈ (b : Sym2 V)) →
        e a ≠ e b

/-- Compatibility with a given proper edge colouring of a regular graph. The reject edges are
those whose colour equals that of an endpoint. Their incidence counts are uniformly bounded. -/
def H2 : Prop :=
  ∃ D B : ℕ, ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ), D ≤ d → G.IsRegularOfDegree d → ∀ e : G.edgeSet → Fin (d + 1),
    (∀ a b : G.edgeSet, a ≠ b → (∃ v, v ∈ (a : Sym2 V) ∧ v ∈ (b : Sym2 V)) →
      e a ≠ e b) →
    ∃ c : V → Fin (d + 1), (∀ u v, G.Adj u v → c u ≠ c v) ∧
      ∀ u, {a : Sym2 V | u ∈ a ∧ ∃ ha : a ∈ G.edgeSet, ∃ v ∈ a, c v = e ⟨a, ha⟩}.ncard ≤ B

theorem finishColoring (hVizing : H1) {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {d B : ℕ}
    (e : G.edgeSet → Fin (d + 1))
    (he : ∀ a b : G.edgeSet, a ≠ b → (∃ v, v ∈ (a : Sym2 V) ∧ v ∈ (b : Sym2 V)) →
      e a ≠ e b)
    (c : V → Fin (d + 1)) (hc : ∀ u v, G.Adj u v → c u ≠ c v)
    (hB : ∀ u, {a : Sym2 V | u ∈ a ∧ ∃ ha : a ∈ G.edgeSet, ∃ v ∈ a,
      c v = e ⟨a, ha⟩}.ncard ≤ B) :
    G.TotalColorable (d + 1 + (B + 1)) := by
  classical
  let bad : Set (Sym2 V) := {a | ∃ ha : a ∈ G.edgeSet, ∃ v ∈ a, c v = e ⟨a, ha⟩}
  let R := SimpleGraph.fromEdgeSet bad
  let : DecidableRel R.Adj := Classical.decRel _
  have hR : R.edgeSet = bad := by
    refine (SimpleGraph.edgeSet_eq_iff R bad).2 ⟨rfl, ?_⟩
    refine Set.disjoint_left.mpr ?_
    intro a ha hdiag
    exact G.not_isDiag_of_mem_edgeSet ha.choose (Sym2.mem_diagSet.mp hdiag)
  have hRB : R.maxDegree ≤ B := R.maxDegree_le_of_forall_degree_le B fun u => by
    have hset : R.incidenceSet u = {a | u ∈ a ∧ a ∈ bad} := by
      ext a
      simp only [SimpleGraph.incidenceSet, Set.mem_ofPred_eq, hR, and_comm]
    rw [← R.card_incidenceSet_eq_degree u, Set.fintypeCard_eq_ncard, hset]
    exact hB u
  obtain ⟨r, hr⟩ := hVizing R
  let oldImbed : Fin (d + 1) → Fin (d + 1 + (B + 1)) := Fin.castAdd (B + 1)
  let newImbed : Fin (R.maxDegree + 1) → Fin (d + 1 + (B + 1)) :=
    fun k => Fin.natAdd (d + 1) (Fin.castLE (Nat.succ_le_succ hRB) k)
  have oldInj : Function.Injective oldImbed := by
    intro x y h
    have hv := congrArg Fin.val h
    exact Fin.eq_of_val_eq hv
  have newInj : Function.Injective newImbed := by
    intro x y h
    apply Fin.eq_of_val_eq
    have hv := congrArg Fin.val h
    change d + 1 + x.val = d + 1 + y.val at hv
    omega
  have disjointPalettes (x : Fin (d + 1)) (y : Fin (R.maxDegree + 1)) :
      oldImbed x ≠ newImbed y := by
    intro h
    have hv := congrArg Fin.val h
    change x.val = d + 1 + y.val at hv
    exact (Nat.not_lt_of_ge (by omega)) x.isLt
  let paintEdge (a : G.edgeSet) : Fin (d + 1 + (B + 1)) :=
    if ha : (a : Sym2 V) ∈ R.edgeSet then newImbed (r ⟨a, ha⟩) else oldImbed (e a)
  refine ⟨Sum.elim (fun v => oldImbed (c v)) paintEdge, ?_, ?_, ?_⟩
  · intro u v huv eq
    exact hc u v huv (oldInj eq)
  · intro a b hab hmeet
    change paintEdge a ≠ paintEdge b
    by_cases ha : (a : Sym2 V) ∈ R.edgeSet <;> by_cases hb : (b : Sym2 V) ∈ R.edgeSet
    · intro eq
      simp only [paintEdge, dif_pos ha, dif_pos hb] at eq
      have hne : (⟨a.val, ha⟩ : R.edgeSet) ≠ ⟨b.val, hb⟩ :=
        fun h => by
          have hv := congrArg Subtype.val h
          exact hab (Subtype.ext hv)
      exact hr _ _ hne hmeet (newInj eq)
    · simp only [paintEdge, dif_pos ha, dif_neg hb]
      exact (disjointPalettes _ _).symm
    · simp only [paintEdge, dif_neg ha, dif_pos hb]
      exact disjointPalettes _ _
    · intro eq
      simp only [paintEdge, dif_neg ha, dif_neg hb] at eq
      exact he a b hab hmeet (oldInj eq)
  · intro v a hva
    change oldImbed (c v) ≠ paintEdge a
    by_cases ha : (a : Sym2 V) ∈ R.edgeSet
    · simp only [paintEdge, dif_pos ha]
      exact disjointPalettes _ _
    · intro eq
      simp only [paintEdge, dif_neg ha] at eq
      exact ha (hR.symm ▸ ⟨a.property, v, hva, oldInj eq⟩)

/-- Complete the graph to a regular graph, construct its total coloring, and pull it back. -/
theorem main : H1 → H2 →
    type_of% @TotalColoringConjecture.total_coloring_conjecture.variants.molloy_reed := by
  classical
  intro hVizing hReject
  obtain ⟨D, B, hReject⟩ := hReject
  refine ⟨max B D + 2, ?_⟩
  intro V _ _ G _
  let d := G.maxDegree
  obtain ⟨W, hW, hWeq, K, hKdec, ⟨f⟩, hKreg⟩ :=
    OMA.MolloyReedCompletion.regular_completion G
  let : Fintype W := hW
  let : DecidableEq W := hWeq
  let : DecidableRel K.Adj := hKdec
  have hKMax : K.maxDegree ≤ d := MolloyReedTransfer.maxDegree_le_of_regular hKreg
  obtain ⟨e', he'⟩ := hVizing K
  let e : K.edgeSet → Fin (d + 1) := fun a => Fin.castLE (Nat.succ_le_succ hKMax) (e' a)
  have he (a b : K.edgeSet) (hab : a ≠ b)
      (hmeet : ∃ v, v ∈ (a : Sym2 W) ∧ v ∈ (b : Sym2 W)) : e a ≠ e b := by
    intro h
    have hv := congrArg Fin.val h
    exact he' a b hab hmeet (Fin.eq_of_val_eq hv)
  have compatible :
      ∃ c : W → Fin (d + 1), (∀ u v, K.Adj u v → c u ≠ c v) ∧
        ∀ u, {a : Sym2 W | u ∈ a ∧ ∃ ha : a ∈ K.edgeSet, ∃ v ∈ a,
          c v = e ⟨a, ha⟩}.ncard ≤ max B D := by
    by_cases high : D ≤ d
    · obtain ⟨c, hproper, hbound⟩ := hReject K d high hKreg e he
      exact ⟨c, hproper, fun u => (hbound u).trans (le_max_left B D)⟩
    · obtain ⟨c, hproper⟩ :=
        MolloyReedTransfer.exists_vertex_coloring_of_maxDegree_lt K (Nat.lt_succ_of_le hKMax)
      refine ⟨c, hproper, fun u => ?_⟩
      have hsubset : {a : Sym2 W | u ∈ a ∧ ∃ ha : a ∈ K.edgeSet, ∃ v ∈ a,
          c v = e ⟨a, ha⟩} ⊆ K.incidenceSet u := by
        intro a ha
        exact ⟨ha.2.choose, ha.1⟩
      apply (Set.ncard_le_ncard hsubset).trans
      rw [← Set.fintypeCard_eq_ncard, K.card_incidenceSet_eq_degree, hKreg.degree_eq]
      exact (Nat.le_of_lt (Nat.lt_of_not_ge high)).trans (le_max_right B D)
  obtain ⟨c, hc, hlocal⟩ := compatible
  obtain ⟨paint, hpaint⟩ := finishColoring hVizing K e he c hc hlocal
  have hG : G.TotalColorable (d + 1 + (max B D + 1)) :=
    ⟨_, MolloyReedTransfer.pullback_isTotalColoring f hpaint⟩
  have upper : G.totalChromaticNumber ≤ d + 1 + (max B D + 1) :=
    Nat.sInf_le (show d + 1 + (max B D + 1) ∈ {k | G.TotalColorable k} from hG)
  omega

end OMA.R_TotalColoringConjecture_total_coloring_conjecture_variants_molloy_reed_R2
