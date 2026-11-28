import OMAReductions.R_TotalColoringConjecture_total_coloring_conjecture_variants_maxDegree_le_five_R1_H2_R1_H3_R1
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Sym.Sym2
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Dedup
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.FinCases
import Mathlib

/-! A finite loopless multigraph of maximum degree two splits into disjoint paths and cycles. A doubled edge is represented by a two-vertex cycle. -/

namespace OMA.DegreeTwoRows
open scoped Classical

noncomputable def rowCount {W : Type*} (l : List W) (c : Bool) (x y : W) : ℕ :=
  if ∃ i : Fin l.length, (c = true ∨ i.val + 1 < l.length) ∧
    s(x,y) = s(l[i.val],l[(i.val+1)%l.length]'(Nat.mod_lt _ (Fin.pos i)))
  then (if c = true ∧ l.length = 2 then 2 else 1) else 0

end OMA.DegreeTwoRows

open SimpleGraph

namespace OMA.PathRows

theorem exists_path_row {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj] (hconn : G.Connected)
    (hforest : G.IsAcyclic) (hd : ∀ w, G.degree w ≤ 2) :
    ∃ l : List W, l.Nodup ∧ l ≠ [] ∧ (∀ x, x ∈ l) ∧
      ∀ x y, G.Adj x y ↔ ∃ i : Fin l.length, i.val + 1 < l.length ∧
        s(x,y) = s(l[i.val], l[(i.val+1)%l.length]'(Nat.mod_lt _ (Fin.pos i))) := by
  classical
  let : Nonempty W := hconn.nonempty
  obtain ⟨u, v, p, hp, longest⟩ := Walk.exists_isPath_forall_isPath_length_le_length G
  have closed : ∀ x y, x ∈ p.support → G.Adj x y → y ∈ p.support := by
    intro x y hx hxy
    by_contra hy
    obtain ⟨i, rfl, hi⟩ := Walk.mem_support_iff_exists_getVert.mp hx
    by_cases hz : i = 0
    · subst i
      rw [Walk.getVert_zero] at hxy
      have h := longest y v (.cons hxy.symm p) (hp.cons hy)
      simp at h
    by_cases hlast : i = p.length
    · subst i
      rw [Walk.getVert_length] at hxy
      have hy' : y ∉ p.reverse.support := by simpa using hy
      have h := longest y u (.cons hxy.symm p.reverse) (hp.reverse.cons hy')
      simp at h
    have cardInternal := hp.ncard_neighborSet_toSubgraph_internal_eq_two hz (by omega : i < p.length)
    have sub : p.toSubgraph.neighborSet (p.getVert i) ⊆ G.neighborSet (p.getVert i) :=
      fun _ hz => p.toSubgraph.adj_sub hz
    have card : (G.neighborSet (p.getVert i)).ncard ≤ 2 := by
      simpa [Set.ncard_eq_toFinset_card', SimpleGraph.degree, SimpleGraph.neighborFinset] using hd (p.getVert i)
    have hsets := Set.eq_of_subset_of_ncard_le sub (card.trans_eq cardInternal.symm)
    have hin : y ∈ p.toSubgraph.neighborSet (p.getVert i) := hsets.symm ▸ (show y ∈ G.neighborSet (p.getVert i) from hxy)
    exact hy (Walk.mem_support_of_adj_toSubgraph hin.symm)
  have transport : ∀ {a b : W} (q : G.Walk a b), a ∈ p.support → b ∈ p.support := by
    intro a b q
    induction q with
    | nil => exact id
    | cons hab q ih => exact fun ha => ih (closed _ _ ha hab)
  have allMem (x : W) : x ∈ p.support :=
    transport (hconn.preconnected u x).some p.start_mem_support
  let inc : p.toSubgraph.coe →g p.toSubgraph.spanningCoe := ⟨Subtype.val, fun h => h⟩
  have onto : Function.Surjective inc :=
    fun x => ⟨⟨x, p.mem_verts_toSubgraph.mpr (allMem x)⟩, rfl⟩
  have hc : p.toSubgraph.spanningCoe.Connected :=
    SimpleGraph.Connected.map inc onto p.toSubgraph_connected
  have tree : G.IsTree := ⟨hconn, hforest⟩
  have subgraph : G ≤ p.toSubgraph.spanningCoe :=
    (SimpleGraph.isTree_iff_minimal_connected.mp tree).2 hc p.toSubgraph.spanningCoe_le
  refine ⟨p.support, hp.support_nodup, p.support_ne_nil, allMem, ?_⟩
  intro x y
  constructor
  · intro h
    obtain ⟨j, hpair, hj⟩ := (p.toSubgraph_adj_iff).mp (subgraph h)
    have hlen := p.length_support
    have hj' : j + 1 < p.support.length := by omega
    refine ⟨⟨j, by omega⟩, hj', ?_⟩
    simpa only [Nat.mod_eq_of_lt hj', Walk.support_getElem_eq_getVert] using hpair.symm
  · rintro ⟨i, hi, hpair⟩
    have hlen := p.length_support
    have hi' : i.val < p.length := by omega
    apply p.toSubgraph.adj_sub
    apply (p.toSubgraph_adj_iff).mpr
    refine ⟨i.val, ?_, hi'⟩
    simpa only [Nat.mod_eq_of_lt hi, Walk.support_getElem_eq_getVert] using hpair.symm

end OMA.PathRows

/- The cyclic-component case of the path/cycle row problem. Prior related
work on simple 2-factors is in lefttosolve2/open-math-agents PR 22956.
Here a single spanning walk gives the row, with its repeated endpoint removed. -/

namespace OMA.CycleRows

open SimpleGraph

variable {V : Type} {F : SimpleGraph V}

theorem cycle_row_of_not_acyclic [Fintype V] [DecidableRel F.Adj]
    (hconn : F.Connected) (upper : ∀ x, F.degree x ≤ 2) (hcyc : ¬ F.IsAcyclic) :
    ∃ l : List V, l.Nodup ∧ l ≠ [] ∧ (∀ x, x ∈ l) ∧ 3 ≤ l.length ∧
      ∀ x y, F.Adj x y ↔ ∃ i : Fin l.length,
        s(x, y) = s(l[i.val], l[(i.val + 1) % l.length]'(Nat.mod_lt _ (Fin.pos i))) := by
  classical
  obtain ⟨v, p, hp⟩ : ∃ (v : V) (p : F.Walk v v), p.IsCycle := by
    by_contra! ha
    exact hcyc (fun _ w => ha _ w)
  -- A cycle already uses both available neighbors at each of its vertices.
  have closed : ∀ x ∈ p.toSubgraph.verts, ∀ y, F.Adj x y → p.toSubgraph.Adj x y := by
    intro x hx y hxy
    have eq : p.toSubgraph.neighborSet x = F.neighborSet x := by
      apply Set.eq_of_subset_of_ncard_le (p.toSubgraph.neighborSet_subset x)
      rw [hp.ncard_neighborSet_toSubgraph_eq_two (p.mem_verts_toSubgraph.mp hx)]
      exact (Nat.card_eq_fintype_card.trans (F.card_neighborSet_eq_degree x)).le.trans (upper x)
    change y ∈ p.toSubgraph.neighborSet x
    rw [eq]
    exact hxy
  have spans (x : V) : x ∈ p.toSubgraph.verts :=
    (hconn v x).mem_subgraphVerts closed (p.mem_verts_toSubgraph.mpr p.start_mem_support)
  let l := p.support.dropLast
  have length_eq : l.length = p.length := by simp [l]
  have three : 3 ≤ l.length := length_eq.symm ▸ hp.three_le_length
  have entry (n : ℕ) (h : n < l.length) : l[n] = p.getVert n := by
    simp [l, List.getElem_dropLast, p.support_getElem_eq_getVert]
  have wrap (n : ℕ) (hn : n ≤ l.length) :
      l[n % l.length]'(Nat.mod_lt _ (by omega)) = p.getVert n := by
    rw [entry]
    by_cases he : n = l.length
    · simp [he, length_eq]
    · rw [Nat.mod_eq_of_lt (by omega)]
  refine ⟨l, hp.nodup_dropLast_support, ?_, ?_, three, ?_⟩
  · intro he
    simp [he] at three
  · intro x
    obtain ⟨n, hn, hnlen⟩ := Walk.mem_support_iff_exists_getVert.mp
      (p.mem_verts_toSubgraph.mp (spans x))
    have h := wrap n (length_eq.symm ▸ hnlen)
    exact (h.trans hn) ▸ List.getElem_mem (Nat.mod_lt n (show 0 < l.length by omega))
  · intro x y
    constructor
    · intro hxy
      obtain ⟨n, h, hn⟩ := p.toSubgraph_adj_iff.mp (closed x (spans x) y hxy)
      have hi : n < l.length := length_eq.symm ▸ hn
      refine ⟨⟨n, hi⟩, ?_⟩
      change s(x, y) = s(l[n], l[(n + 1) % l.length]'(Nat.mod_lt _ (by omega)))
      rw [entry, wrap (n + 1) (by omega)]
      exact h.symm
    · rintro ⟨i, h⟩
      have hi := i.isLt
      rw [entry, wrap (i.val + 1) (by omega)] at h
      exact (p.toSubgraph_adj_iff.mpr ⟨i.val, h.symm, length_eq ▸ hi⟩).adj_sub

end OMA.CycleRows

namespace OMA.DegreeTwoRows

open SimpleGraph
open scoped Classical

variable {W : Type*}

theorem other_multiplicity_zero [Fintype W] [DecidableEq W] (k : W → W → ℕ)
    (hdeg : ∀ x, ∑ y, k x y ≤ 2) {x y z : W}
    (hxy : 2 ≤ k x y) (hyz : y ≠ z) : k x z = 0 := by
  have hpair : k x y + k x z ≤ ∑ u, k x u := by
    calc
      k x y + k x z = ∑ u ∈ ({y, z} : Finset W), k x u := by simp [hyz]
      _ ≤ ∑ u, k x u := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ _) (by intros; exact Nat.zero_le _)
  have := hdeg x
  omega

theorem rowCount_pair [DecidableEq W] (x y a b : W) :
    rowCount [x,y] true a b = if s(a,b) = s(x,y) then 2 else 0 := by
  have iffPair :
      (∃ i : Fin ([x,y] : List W).length, (true = true ∨ i.val + 1 < ([x,y] : List W).length) ∧
        s(a,b) = s(([x,y] : List W)[i.val],
          ([x,y] : List W)[(i.val+1)%([x,y] : List W).length]'(Nat.mod_lt _ (Fin.pos i)))) ↔
        s(a,b) = s(x,y) := by
    constructor
    · rintro ⟨i, _, hi⟩
      change Fin 2 at i
      fin_cases i
      · exact hi
      · norm_num [Sym2.eq, Sym2.rel_iff', Prod.swap_prod_mk] at hi ⊢
        tauto
    · intro h
      exact ⟨0, Or.inl rfl, h⟩
  unfold rowCount
  split
  next yes =>
    have h := iffPair.mp yes
    rw [if_pos h]
    simp
  next no =>
    have h := mt iffPair.mpr no
    rw [if_neg h]

theorem double_edge_row [Fintype W] [DecidableEq W] (G : SimpleGraph W) (k : W → W → ℕ)
    (hsym : ∀ x y, k x y = k y x) (hloop : ∀ x, k x x = 0)
    (hdeg : ∀ x, ∑ y, k x y ≤ 2)
    (hadj : ∀ x y, G.Adj x y ↔ 0 < k x y) (hconn : G.Connected)
    {x y : W} (hdouble : 2 ≤ k x y) :
    ([x,y] : List W).Nodup ∧ (∀ a, a ∈ [x,y]) ∧
      ∀ a b, k a b = rowCount [x,y] true a b := by
  classical
  have hne : x ≠ y := by
    rintro rfl
    simp [hloop] at hdouble
  have hvalue : k x y = 2 := by
    have le : k x y ≤ ∑ z, k x z :=
      Finset.single_le_sum (fun z _ => Nat.zero_le (k x z)) (Finset.mem_univ y)
    exact Nat.le_antisymm (le.trans (hdeg x)) hdouble
  have hrev : k y x = 2 := (hsym y x).trans hvalue
  have closed (a b : W) (ha : a = x ∨ a = y) (hab : G.Adj a b) : b = x ∨ b = y := by
    rcases ha with ha | ha <;> subst a
    · right
      by_contra h
      have hzero := other_multiplicity_zero k hdeg hdouble (Ne.symm h)
      have hpos := (hadj x b).1 hab
      omega
    · left
      by_contra h
      have hzero := other_multiplicity_zero k hdeg (le_of_eq hrev.symm) (Ne.symm h)
      have hpos := (hadj y b).1 hab
      omega
  have transport : ∀ {a b : W} (w : G.Walk a b), a = x ∨ a = y → b = x ∨ b = y := by
    intro a b w
    induction w with
    | nil => exact id
    | cons hab w ih => exact fun ha => ih (closed _ _ ha hab)
  have allPairs (a : W) : a = x ∨ a = y :=
    transport (hconn.preconnected x a).some (Or.inl rfl)
  refine ⟨by simp [hne], fun a => by simpa using allPairs a, ?_⟩
  intro a b
  rw [rowCount_pair]
  rcases allPairs a with ha | ha <;> rcases allPairs b with hb | hb <;> subst a <;> subst b <;>
    simp [hloop, hne, Ne.symm hne, hvalue, hrev, Sym2.eq, Sym2.rel_iff', Prod.swap_prod_mk]

end OMA.DegreeTwoRows

open SimpleGraph

namespace OMA.DegreeTwoRows

theorem connected_row {W : Type} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) (k : W → W → ℕ)
    (hsym : ∀ x y, k x y = k y x) (hloop : ∀ x, k x x = 0)
    (hdeg : ∀ x, ∑ y, k x y ≤ 2)
    (hadj : ∀ x y, G.Adj x y ↔ 0 < k x y) (hconn : G.Connected) :
    ∃ (l : List W) (c : Bool), l.Nodup ∧ l ≠ [] ∧ (∀ x, x ∈ l) ∧
      ∀ x y, k x y = rowCount l c x y := by
  classical
  by_cases hdbl : ∃ x y, 2 ≤ k x y
  · obtain ⟨x, y, hxy⟩ := hdbl
    obtain ⟨hn, hall, hk⟩ := double_edge_row G k hsym hloop hdeg hadj hconn hxy
    exact ⟨[x,y], true, hn, by simp, hall, hk⟩
  have simple (x y : W) : k x y = if G.Adj x y then 1 else 0 := by
    have hlt : ¬ 2 ≤ k x y := fun h => hdbl ⟨x,y,h⟩
    split_ifs with h
    · have := (hadj x y).1 h
      omega
    · have := mt (hadj x y).2 h
      omega
  have upper (x : W) : G.degree x ≤ 2 := by
    calc
      G.degree x = ∑ _ ∈ G.neighborFinset x, 1 := by simp
      _ ≤ ∑ y ∈ G.neighborFinset x, k x y :=
        Finset.sum_le_sum fun y hy => (hadj x y).1 ((G.mem_neighborFinset x y).mp hy)
      _ ≤ ∑ y, k x y := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ _) (by intros; exact Nat.zero_le _)
      _ ≤ 2 := hdeg x
  by_cases hforest : G.IsAcyclic
  · obtain ⟨l, hn, hne, hall, edges⟩ := OMA.PathRows.exists_path_row G hconn hforest upper
    refine ⟨l, false, hn, hne, hall, ?_⟩
    intro x y
    rw [simple x y]
    simp only [rowCount, Bool.false_eq_true, false_or, false_and, if_false, ← edges x y]
  · obtain ⟨l, hn, hne, hall, hlen, edges⟩ := OMA.CycleRows.cycle_row_of_not_acyclic hconn upper hforest
    refine ⟨l, true, hn, hne, hall, ?_⟩
    intro x y
    rw [simple x y]
    have hlen' : l.length ≠ 2 := by omega
    simp only [rowCount, eq_self, true_or, true_and, ← edges x y, if_neg hlen']

end OMA.DegreeTwoRows

namespace OMA.DegreeTwoRows

open SimpleGraph
open scoped Classical BigOperators

theorem rowCount_map {U W : Type*} (f : U → W) (hf : Function.Injective f)
    (l : List U) (b : Bool) (x y : U) :
    rowCount (l.map f) b (f x) (f y) = rowCount l b x y := by
  simp [rowCount, hf.eq_iff]
  congr 1
  apply propext
  constructor <;> rintro ⟨i, hi⟩ <;> exact ⟨⟨i.val, by simpa only [List.length_map] using i.isLt⟩, hi⟩

theorem rowCount_zero_of_notMem {W : Type*} (l : List W) (b : Bool) {x y : W}
    (hy : y ∉ l) : rowCount l b x y = 0 := by
  unfold rowCount
  apply if_neg
  rintro ⟨i, _, hi⟩
  rcases Sym2.eq_iff.mp hi with ⟨_,hy'⟩ | ⟨_,hy'⟩ <;>
    exact hy (hy' ▸ List.getElem_mem _)

theorem rows_of_components
    (localRows : ∀ {U : Type} [Fintype U] [DecidableEq U] (G : SimpleGraph U) (k : U → U → ℕ),
      (∀ x y, k x y = k y x) → (∀ x, k x x = 0) → (∀ x, ∑ y, k x y ≤ 2) →
      (∀ x y, G.Adj x y ↔ 0 < k x y) → G.Connected →
      ∃ (l : List U) (b : Bool), l.Nodup ∧ l ≠ [] ∧ (∀ x, x ∈ l) ∧
        ∀ x y, k x y = rowCount l b x y)
    {W : Type} [Fintype W] [DecidableEq W] (k : W → W → ℕ)
    (hsym : ∀ x y, k x y = k y x) (hloop : ∀ x, k x x = 0)
    (hdeg : ∀ x, ∑ y, k x y ≤ 2) :
    ∃ P : List (List W × Bool), (P.map (fun p => p.1.toFinset)).Pairwise Disjoint ∧
      (∀ x, ∃ p ∈ P, x ∈ p.1) ∧ ∀ p ∈ P, p.1.Nodup ∧ p.1 ≠ [] ∧
        ∀ x ∈ p.1, ∀ y, k x y = rowCount p.1 p.2 x y := by
  classical
  let G : SimpleGraph W :=
    { Adj := fun x y => 0 < k x y
      symm := ⟨fun x y h => (hsym x y) ▸ h⟩
      loopless := ⟨fun x => by simp [hloop]⟩ }
  have each (C : G.ConnectedComponent) :
      ∃ (l : List W) (b : Bool), l.Nodup ∧ l ≠ [] ∧ (∀ x, x ∈ l ↔ x ∈ C.supp) ∧
        ∀ x ∈ l, ∀ y, k x y = rowCount l b x y := by
    let kC (x y : C.supp) := k x.val y.val
    have upper (x : C.supp) : ∑ y, kC x y ≤ 2 := by
      have splitSum := Fintype.sum_subtype_add_sum_subtype (fun v => v ∈ C.supp) (k x.val)
      have total := hdeg x.val
      change ∑ y : C.supp, k x.val y.val ≤ 2
      have hfirst := (Nat.le_add_right _ _).trans (Nat.le_of_eq splitSum)
      convert hfirst.trans total using 2
    obtain ⟨l, b, hnd, hne, hcover, hval⟩ :=
      localRows (G.induce C.supp) kC (fun x y => hsym x y) (fun x => hloop x) upper
        (fun _ _ => Iff.rfl) C.connected_toSimpleGraph
    let L := l.map (Subtype.val : C.supp → W)
    have memL (x : W) : x ∈ L ↔ x ∈ C.supp := by
      constructor
      · intro h
        obtain ⟨v, _, rfl⟩ := List.mem_map.mp h
        exact v.property
      · intro h
        exact List.mem_map.mpr ⟨⟨x,h⟩, hcover _, rfl⟩
    refine ⟨L, b, hnd.map Subtype.val_injective, ?_, memL, ?_⟩
    · exact fun h => hne (List.map_eq_nil_iff.mp h)
    · intro x hx y
      let vx : C.supp := ⟨x, (memL x).mp hx⟩
      by_cases hy : y ∈ C.supp
      · let vy : C.supp := ⟨y, hy⟩
        exact (hval vx vy).trans
          (rowCount_map Subtype.val Subtype.val_injective l b vx vy).symm
      · rw [rowCount_zero_of_notMem L b (fun h => hy ((memL y).mp h))]
        by_contra hn
        have ha : G.Adj x y := Nat.pos_of_ne_zero hn
        exact hy (C.mem_supp_of_adj_mem_supp ((memL x).mp hx) ha)
  choose l b hnd hne hmem hval using each
  let row (C : G.ConnectedComponent) : List W × Bool := (l C, b C)
  let : Fintype G.ConnectedComponent := Fintype.ofFinite _
  let cs := (Finset.univ : Finset G.ConnectedComponent).toList
  refine ⟨cs.map row, ?_, ?_, ?_⟩
  · rw [List.map_map, List.pairwise_map]
    refine (Finset.univ.nodup_toList : cs.Nodup).imp ?_
    intro C D hCD
    refine Finset.disjoint_left.mpr ?_
    intro x hx hy
    apply hCD
    exact ConnectedComponent.eq_of_common_vertex ((hmem C x).mp (List.mem_toFinset.mp hx))
      ((hmem D x).mp (List.mem_toFinset.mp hy))
  · intro x
    let C := G.connectedComponentMk x
    exact ⟨row C, List.mem_map.mpr ⟨C, by simp [cs], rfl⟩, (hmem C x).mpr rfl⟩
  · intro p hp
    obtain ⟨C, _, rfl⟩ := List.mem_map.mp hp
    exact ⟨hnd C, hne C, hval C⟩

end OMA.DegreeTwoRows

theorem OMA.solution : OMA.R_TotalColoringConjecture_total_coloring_conjecture_variants_maxDegree_le_five_R1_H2_R1_H3_R1.H1 := by
  intro W _ _ k hsym hloop hdeg
  obtain ⟨P, hdisj, hcover, hrows⟩ :=
    OMA.DegreeTwoRows.rows_of_components OMA.DegreeTwoRows.connected_row k hsym hloop hdeg
  refine ⟨P, hdisj, hcover, ?_⟩
  intro p hp
  obtain ⟨hnd, hne, hm⟩ := hrows p hp
  refine ⟨hnd, hne, ?_⟩
  intro x hx y
  rw [hm x hx y]
  dsimp only [OMA.DegreeTwoRows.rowCount]
  split_ifs <;> rfl
