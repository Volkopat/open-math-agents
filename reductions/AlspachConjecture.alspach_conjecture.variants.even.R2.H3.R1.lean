import OMAReductions.R_AlspachConjecture_alspach_conjecture_variants_even_R2
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
import Mathlib.Algebra.Order.Group.Multiset
import Mathlib.Data.Multiset.Filter
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Finset.Option
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fin.Embedding
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Logic.Equiv.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.BigOperators

import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Abel

/-!
Bryant, Horsley and Pettersson, *Cycle decompositions V*, Lemmas 4 and 5
(arXiv:1204.3709), separate ancestor lists with at most one Hamilton cycle
from those with at least two. Lemma 5 uses the conclusions for the three preceding
orders in the paper's induction. The proof of Lemma 4 handles lists supported on
triangles and Hamilton cycles by the theorem of Bryant and Maenhaut [26].
The even-order Walecki construction below gives every all-Hamilton list.
Its walk and edge-count arguments adapt Salofe's odd-order proof in PR #6728.
For triangle-only lists, the Skolem and Bose constructions below cover orders
zero and two modulo six. The edge budget excludes orders four modulo six.
For square-only lists, each pair of matching edges spans one four-cycle.
For lists supported on four and the full order, doubling Walecki cycles supplies
pairs of Hamilton cycles, while every unused base edge supplies one square.
When the order is twice an odd number, the edge budget forces an even Hamilton count.
For the remaining odd Hamilton counts, a ladder cycle uses the two rails and end rungs,
and the other Hamilton cycles avoid the reserved path.
For orders two and six modulo twelve, a Steiner triple system on the matched pairs
allows any admissible mixture of triangles and squares. Each chosen triple of pairs
replaces three squares with four triangles. At other even orders the same
construction works when the requested squares cover the edges outside a triple packing.
Deleting points from a Steiner system or embedding a smaller system supplies the packing.
For the remaining lists, constructions around groups of two or four points and complete
tripartite graphs supply the required square counts. Recursive triple systems with one
four-point group cover the smaller square counts in the remaining residue classes.
Over a master triple, the two decompositions of the complete tripartite graph on three
groups of three vertices exchange four triangles for three squares. Together these
constructions realize every triangle/square list for every prescribed perfect matching.
For orders six modulo twelve, affine triples on three layers split into
paired cyclic listings and disjoint triples. Doubling their vertices realizes lists
supported on three, four and the full order for every even Hamilton count from four
through one third of the order. At orders thirty modulo thirty-six,
three squares suffice to complete the three inner groups. Signed cyclic differences and Langford pairings supply a single pair of
Hamilton cycles with every admissible number of triangles and squares.
Further doublings of a three-group decomposition give new orders and Hamilton counts.
Each base matching pair contributes one square in the first doubling, and the iteration
keeps track of those squares and their later lifts. Omitting a Hamilton cycle at the
last doubling yields one square for each of its base edges. A starting pair of
Hamilton cycles needs no squares, including when each of the three groups has two vertices. At every even
order, a base triangle packing can supply triangles away from the selected Hamilton
cycles. A cyclic suborder also supplies one pair of Hamilton cycles when enough
squares remain to cover the other base edges. At orders thirty and sixty-six, certified base partitions cover every even Hamilton count
from four to a third of the order without a square cutoff. On a base of even order, a ladder also contributes one
Hamilton cycle while triangle trades and paired Hamilton lifts use edges outside the ladder.
-/

namespace AlspachEvenHamilton
open SimpleGraph AlspachConjecture
open scoped Classical

/-- The finite edge-union counting argument follows @Salofe's odd-order
Walecki proof in LeftToSolve PR #6728. The count here applies to any graph. -/
theorem colored_cycles {n k l : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (c : Fin k → Cycle G) (color : Sym2 (Fin n) → Nat)
    (len : ∀ i, (c i).length = l)
    (shade : ∀ i e, e ∈ (c i).edges → color e = i.val)
    (edgeCount : G.edgeFinset.card = k*l) :
    ∃ C : Multiset (Cycle G), IsCycleDecomposition G C ∧
      lengths C = Multiset.replicate k l := by
  classical
  let edges (i : Fin k) := (c i).edges.toFinset
  have unique {i j : Fin k} {e} (hi : e ∈ (c i).edges) (hj : e ∈ (c j).edges) : i = j :=
    Fin.ext ((shade i e hi).symm.trans (shade j e hj))
  have disj : ((Finset.univ : Finset (Fin k)) : Set (Fin k)).PairwiseDisjoint edges := by
    intro i _ j _ ne
    rw [Function.onFun, Finset.disjoint_left]
    exact fun e hi hj => ne (unique (List.mem_toFinset.mp hi) (List.mem_toFinset.mp hj))
  have included : Finset.univ.biUnion edges ⊆ G.edgeFinset := by
    intro e he
    obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp he
    exact mem_edgeFinset.mpr (Walk.edges_subset_edgeSet _ (List.mem_toFinset.mp hi))
  have size (i : Fin k) : (edges i).card = l := by
    dsimp only [edges]
    have nodup : (c i).edges.Nodup := (c i).isCycle.edges_nodup
    rw [List.toFinset_card_of_nodup nodup,
      SimpleGraph.Cycle.edges, Walk.length_edges]
    exact len i
  have unionSize : (Finset.univ.biUnion edges).card = k*l := by
    rw [Finset.card_biUnion disj]
    simp [size]
  have allEdges := Finset.eq_of_subset_of_card_le included (by rw [unionSize,edgeCount])
  refine ⟨(Finset.univ : Finset (Fin k)).val.map c, ?_, ?_⟩
  · intro e he
    obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp (allEdges.symm ▸ he : e ∈ Finset.univ.biUnion edges)
    have hit := List.mem_toFinset.mp hi
    rw [Multiset.filter_map,Multiset.card_map,Multiset.card_eq_one]
    refine ⟨i,?_⟩
    rw [Multiset.Nodup.ext (Multiset.Nodup.filter _ Finset.univ.nodup) (Multiset.nodup_singleton _)]
    intro j
    simp only [Multiset.mem_filter,Finset.mem_val,Finset.mem_univ,true_and,
      Multiset.mem_singleton,Function.comp]
    exact ⟨fun hj => unique hj hit, fun hj => hj ▸ hit⟩
  · rw [lengths,Multiset.map_map]
    have eq : (SimpleGraph.Cycle.length ∘ c) = fun _ => l := funext len
    rw [eq,Multiset.map_const']
    simp

theorem complement_card (k : Nat) (I : (completeGraph (Fin (2*k+2))).Subgraph)
    (hI : I.IsPerfectMatching) :
    (completeGraph (Fin (2*k+2)) \ I.spanningCoe).edgeFinset.card = k*(2*k+2) := by
  classical
  let D := completeGraph (Fin (2*k+2)) \ I.spanningCoe
  have graph : D = I.spanningCoeᶜ := top_sdiff
  have eqE : D.edgeFinset = I.spanningCoeᶜ.edgeFinset := by
    ext e
    simp only [mem_edgeFinset]
    rw [graph]
  change D.edgeFinset.card = _
  rw [eqE]
  have deg (v : Fin (2*k+2)) : I.spanningCoeᶜ.degree v = 2*k := by
    rw [degree_compl,Subgraph.degree_spanningCoe,Subgraph.isPerfectMatching_iff_forall_degree.mp hI v,
      Fintype.card_fin]
    omega
  have sum := I.spanningCoeᶜ.sum_degrees_eq_twice_card_edges
  simp only [deg,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at sum
  change (2*k+2)*(2*k) = 2*I.spanningCoeᶜ.edgeFinset.card at sum
  rw [show (2*k+2)*(2*k) = 2*(k*(2*k+2)) by ac_rfl] at sum
  omega

theorem even_budget (k : Nat) : (2*k+2).choose 2 - (2*k+2)/2 = k*(2*k+2) := by
  have h : (2*k+2)*(2*k+2-1) = 2*((k+1)*(2*k+1)) := by
    rw [show 2*k+2-1 = 2*k+1 by omega]
    ring
  rw [Nat.choose_two_right,h,Nat.mul_div_cancel_left _ (by decide : 0<2),
    show (k+1)*(2*k+1) = k*(2*k+2)+(k+1) by ring]
  omega

theorem on_matching (k : Nat) (I : (completeGraph (Fin (2*k+2))).Subgraph)
    (hI : I.IsPerfectMatching)
    (c : Fin k → Cycle (completeGraph (Fin (2*k+2)) \ I.spanningCoe))
    (color : Sym2 (Fin (2*k+2)) → Nat) (len : ∀ i, (c i).length = 2*k+2)
    (shade : ∀ i e, e ∈ (c i).edges → color e = i.val)
    (m : Multiset Nat) (hm : ∀ x ∈ m, x = 2*k+2)
    (hs : m.sum = (2*k+2).choose 2 - (2*k+2)/2) :
    ∃ C : Multiset (Cycle (completeGraph (Fin (2*k+2)) \ I.spanningCoe)),
      IsCycleDecomposition _ C ∧ lengths C = m := by
  classical
  have equal : m = Multiset.replicate m.card (2*k+2) := Multiset.eq_replicate.mpr ⟨rfl,hm⟩
  have count : m.card = k := by
    rw [equal,Multiset.sum_replicate,smul_eq_mul,even_budget] at hs
    exact Nat.eq_of_mul_eq_mul_right (by omega) hs
  obtain ⟨C,dec,lens⟩ := colored_cycles _ c color len shade (by
    convert complement_card k I hI using 1
    congr 1
    ext e
    simp only [mem_edgeFinset])
  rw [count] at equal
  exact ⟨C,dec,lens.trans equal.symm⟩

end AlspachEvenHamilton

namespace EvenWalecki
open SimpleGraph AlspachConjecture
open scoped Classical

set_option maxHeartbeats 1800000 in
/-- Walecki's alternating list and the edge-colour and partner functions, together
with the arithmetic facts used to construct the cycles. -/
theorem zigzag_data (k : Nat) :
    ∃ wal : Nat → Nat → Nat, ∃ colour : Nat → Nat → Nat, ∃ mate : Nat → Nat,
      (∀ i t, i < k → wal i t < 2*k+2) ∧
      (∀ i t u, i < k → t ≤ 2*k+1 → u ≤ 2*k+1 → wal i t = wal i u → t = u) ∧
      (∀ a b, colour a b = colour b a) ∧
      (∀ i t, i < k → t < 2*k+1 → colour (wal i t) (wal i (t+1)) = i) ∧
      (∀ i, i < k → colour (wal i (2*k+1)) (wal i 0) = i) ∧
      (∀ a, a < 2*k+2 → mate a < 2*k+2) ∧
      (∀ a, a < 2*k+2 → mate (mate a) = a) ∧
      (∀ a, a < 2*k+2 → mate a ≠ a) ∧
      (∀ a, a < 2*k+2 → colour a (mate a) = k) := by
  let wal (k i t : Nat) : Nat :=
    if 2*k+1 ≤ t then 2*k+1
    else if t%2=0 then i+t/2
    else if (t+1)/2 ≤ i then i-(t+1)/2
    else i+(2*k+1)-(t+1)/2

  have wal_lt (k i t : Nat) (hi : i < k) : wal k i t < 2*k+2 := by
    simp only [wal]
    split_ifs <;> omega

  have wal_inj (k i t u : Nat) (hi : i < k) (ht : t ≤ 2*k+1)
      (hu : u ≤ 2*k+1) (eq : wal k i t = wal k i u) : t = u := by
    simp only [wal] at eq
    split_ifs at eq <;> omega

  let colour (k a b : Nat) : Nat :=
    if a = 2*k+1 then (if b < k then b else b-k)
    else if b = 2*k+1 then (if a < k then a else a-k)
    else if a+b+1 < 2*k+1 then (a+b+1)/2
    else (a+b+1-(2*k+1))/2

  have colour_comm (k a b : Nat) : colour k a b = colour k b a := by
    simp only [colour]
    split_ifs <;> omega

  have colour_step (k i t : Nat) (hi : i < k) (ht : t < 2*k+1) :
      colour k (wal k i t) (wal k i (t+1)) = i := by
    simp only [colour, wal]
    split_ifs <;> omega

  have colour_close (k i : Nat) (hi : i < k) :
      colour k (wal k i (2*k+1)) (wal k i 0) = i := by
    simp only [colour, wal]
    split_ifs <;> omega

  let mate (k a : Nat) : Nat :=
    if a < 2*k then 2*k-1-a else if a = 2*k then 2*k+1 else 2*k

  have mate_lt {k a : Nat} (ha : a < 2*k+2) : mate k a < 2*k+2 := by
    simp only [mate]
    split_ifs <;> omega

  have mate_inv {k a : Nat} (ha : a < 2*k+2) : mate k (mate k a) = a := by
    simp only [mate]
    split_ifs <;> omega

  have mate_ne {k a : Nat} (ha : a < 2*k+2) : mate k a ≠ a := by
    simp only [mate]
    split_ifs <;> omega

  have colour_mate {k a : Nat} (ha : a < 2*k+2) : colour k a (mate k a) = k := by
    simp only [colour, mate]
    split_ifs <;> omega
  exact ⟨wal k, colour k, mate k, wal_lt k, wal_inj k, colour_comm k, colour_step k,
    colour_close k, fun _ h => mate_lt h, fun _ h => mate_inv h, fun _ h => mate_ne h,
    fun _ h => colour_mate h⟩

/-- Assemble the walk through a prescribed vertex list. Its support and edge
description adapt @Salofe's odd-order Walecki proof in PR #6728. -/
theorem path_through {V : Type} {G : SimpleGraph V} (v : Nat → V) (N : Nat)
    (adj : ∀ t, t < N → G.Adj (v t) (v (t+1))) :
    ∃ w : G.Walk (v 0) (v N),
      w.support = (List.range (N+1)).map v ∧
      w.edges = (List.range N).map (fun t => s(v t, v (t+1))) ∧ w.length = N := by
  induction N with
  | zero => exact ⟨Walk.nil, by simp, by simp, rfl⟩
  | succ n ih =>
    obtain ⟨p, vs, es, len⟩ := ih (fun t ht => adj t (by omega))
    refine ⟨p.concat (adj n (by omega)), ?_, ?_, ?_⟩
    · rw [Walk.support_concat, vs, List.range_succ (n := n+1), List.map_append]
      simp
    · rw [Walk.edges_concat, es, List.range_succ (n := n), List.map_append]
      simp
    · rw [Walk.length_concat, len]

/-- Even-order Walecki construction. The row formula is evaluated in the cyclic
group of size `2*k+1`; the remaining colour defines a perfect matching. -/
theorem all_hamilton (n : Nat) (even : Even n) (large : 4 ≤ n)
    (m : Multiset Nat) (only : ∀ x ∈ m, x = n) (budget : m.sum = n.choose 2 - n/2) :
    ∃ J : (completeGraph (Fin n)).Subgraph, J.IsPerfectMatching ∧
      ∃ C : Multiset (Cycle (completeGraph (Fin n) \ J.spanningCoe)),
        IsCycleDecomposition _ C ∧ lengths C = m := by
  classical
  obtain ⟨j,hj⟩ := even
  have form : ∃ k, 1 ≤ k ∧ n = 2*k+2 := ⟨j-1, by omega, by omega⟩
  obtain ⟨k,hk,rfl⟩ := form
  obtain ⟨wal, colour, mate, bound, injective, comm, step, close, mateBound,
    mateInv, noFix, shadeMate⟩ := zigzag_data k
  let J : (completeGraph (Fin (2*k+2))).Subgraph := {
    verts := Set.univ
    Adj := fun a b => mate a.val = b.val
    adj_sub := by
      intro a b h
      change a ≠ b
      intro e
      subst b
      exact noFix a a.isLt h
    edge_vert := fun _ => Set.mem_univ _
    symm := ⟨by
      intro a b h
      rw [← h]
      exact mateInv a a.isLt⟩ }
  have perf : J.IsPerfectMatching := by
    apply Subgraph.isPerfectMatching_iff.mpr
    intro a
    exact ⟨⟨mate a.val, mateBound a a.isLt⟩, rfl,
      fun b hb => Fin.ext (Eq.symm (show mate a.val = b.val from hb))⟩
  let G := completeGraph (Fin (2*k+2)) \ J.spanningCoe
  let col : Sym2 (Fin (2*k+2)) → Nat :=
    Sym2.lift ⟨fun a b => colour a b, fun a b => comm a b⟩
  have pairAdj (a b : Fin (2*k+2)) (ne : a ≠ b) (hc : colour a.val b.val < k) : G.Adj a b := by
    refine ⟨ne, ?_⟩
    intro h
    change mate a.val = b.val at h
    rw [← h, shadeMate a a.isLt] at hc
    omega
  have one (i : Fin k) : ∃ c : Cycle G, c.length = 2*k+2 ∧ ∀ e ∈ c.edges, col e = i := by
    let v (t : Nat) : Fin (2*k+2) := ⟨wal i t, bound i t i.isLt⟩
    have vinj (t u : Nat) (ht : t ≤ 2*k+1) (hu : u ≤ 2*k+1) (h : v t = v u) : t = u :=
      injective i t u i.isLt ht hu (congrArg Fin.val h)
    have adjacent (t : Nat) (ht : t < 2*k+1) : G.Adj (v t) (v (t+1)) := by
      apply pairAdj
      · intro h
        have e := vinj t (t+1) (by omega) (by omega) h
        omega
      · exact (step i t i.isLt ht).trans_lt i.isLt
    have closing : G.Adj (v (2*k+1)) (v 0) := by
      apply pairAdj
      · intro h
        have e := vinj (2*k+1) 0 (by omega) (by omega) h
        omega
      · exact (close i i.isLt).trans_lt i.isLt
    obtain ⟨p, vs, es, plen⟩ := path_through v (2*k+1) adjacent
    let c : Cycle G := {
      base := v (2*k+1)
      walk := Walk.cons closing p
      isCycle := by
        rw [Walk.cons_isCycle_iff]
        constructor
        · rw [Walk.isPath_def, vs]
          apply List.Nodup.map_on
          · intro x hx y hy hxy
            rw [List.mem_range] at hx hy
            exact vinj x y (by omega) (by omega) hxy
          · exact List.nodup_range
        · rw [es, List.mem_map]
          rintro ⟨t, ht, he⟩
          rw [List.mem_range] at ht
          rcases Sym2.eq_iff.mp he with ⟨h1,h2⟩ | ⟨h1,h2⟩
          · have q := vinj t (2*k+1) (by omega) le_rfl h1
            omega
          · have q := vinj t 0 (by omega) (by omega) h1
            have r := vinj (t+1) (2*k+1) (by omega) le_rfl h2
            omega }
    refine ⟨c, ?_, ?_⟩
    · change (Walk.cons closing p).length = _
      rw [Walk.length_cons, plen]
    · intro edge he
      change edge ∈ (Walk.cons closing p).edges at he
      rw [Walk.edges_cons, es, List.mem_cons, List.mem_map] at he
      rcases he with rfl | ⟨t, ht, rfl⟩
      · exact close i i.isLt
      · exact step i t i.isLt (List.mem_range.mp ht)
  choose cs hlen hcol using one
  exact ⟨J, perf, AlspachEvenHamilton.on_matching k J perf cs col hlen hcol m only budget⟩

end EvenWalecki

namespace AlspachFamilies
open SimpleGraph AlspachConjecture
open scoped Classical

/-- A finite family of equal-length cycles covering every edge once gives a
cycle decomposition. Counting the disjoint edge sets fixes its size. -/
theorem edge_partition {V B : Type*} [Fintype V] [DecidableEq V] [Fintype B]
    (G : SimpleGraph V) [DecidableRel G.Adj] {l : Nat} (c : B → Cycle G)
    (len : ∀ i, (c i).length=l) (unique : ∀ e∈G.edgeFinset, ∃! i, e∈(c i).edges) :
    ∃ C : Multiset (Cycle G), IsCycleDecomposition G C ∧
      lengths C=Multiset.replicate (Fintype.card B) l ∧ G.edgeFinset.card=Fintype.card B*l := by
  classical
  let D (i : B) := (c i).edges.toFinset
  have union : Finset.univ.biUnion D = G.edgeFinset := by
    ext e
    constructor
    · intro h
      obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp h
      exact G.mem_edgeFinset.mpr (Walk.edges_subset_edgeSet _ (List.mem_toFinset.mp hi))
    · intro h
      obtain ⟨i,hi,_⟩ := unique e h
      exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,List.mem_toFinset.mpr hi⟩
  have disj : ((Finset.univ : Finset B) : Set B).PairwiseDisjoint D := by
    intro i _ j _ ne
    rw [Function.onFun,Finset.disjoint_left]
    intro e hi hj
    have he := G.mem_edgeFinset.mpr (Walk.edges_subset_edgeSet _ (List.mem_toFinset.mp hi))
    exact ne ((unique e he).unique (List.mem_toFinset.mp hi) (List.mem_toFinset.mp hj))
  have cardD (i : B) : (D i).card=l := by
    have h : (c i).edges.Nodup := (c i).isCycle.edges_nodup
    dsimp only [D]
    rw [List.toFinset_card_of_nodup h,SimpleGraph.Cycle.edges,Walk.length_edges]
    exact len i
  refine ⟨(Finset.univ : Finset B).val.map c, ?_, ?_, ?_⟩
  · intro e he
    obtain ⟨i,hi,hu⟩ := unique e he
    rw [Multiset.filter_map,Multiset.card_map,Multiset.card_eq_one]
    refine ⟨i,?_⟩
    rw [Multiset.Nodup.ext (Multiset.Nodup.filter _ Finset.univ.nodup) (Multiset.nodup_singleton _)]
    intro j
    simp only [Multiset.mem_filter,Finset.mem_val,Finset.mem_univ,true_and,
      Multiset.mem_singleton,Function.comp]
    exact ⟨hu j, fun eq => eq ▸ hi⟩
  · rw [lengths,Multiset.map_map]
    have eq : (SimpleGraph.Cycle.length ∘ c) = fun _ => l := funext len
    rw [eq,Multiset.map_const']
    simp
  · rw [←union,Finset.card_biUnion disj]
    simp [cardD]

end AlspachFamilies

namespace TriangleBridge
open SimpleGraph AlspachConjecture
open scoped Classical

private theorem cycle_on_triple {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    (s : Finset V) (three : s.card=3)
    (clique : ∀ x∈s, ∀ y∈s, x≠y → G.Adj x y) :
    ∃ c : Cycle G, c.length=3 ∧ ∀ x y, x≠y → (s(x,y) ∈ c.edges ↔ x∈s ∧ y∈s) := by
  classical
  obtain ⟨a,b,d,hab,had,hbd,rfl⟩ := Finset.card_eq_three.mp three
  have ab := clique a (by simp) b (by simp) hab
  have bd := clique b (by simp) d (by simp) hbd
  have da := clique d (by simp) a (by simp) had.symm
  let w : G.Walk a a := .cons ab (.cons bd (.cons da .nil))
  have cycle : w.IsCycle := by simp [w,Walk.isCycle_def]; aesop
  refine ⟨⟨a,w,cycle⟩,rfl,?_⟩
  intro x y hxy
  change s(x,y) ∈ [s(a,b),s(b,d),s(d,a)] ↔ _
  simp only [List.mem_cons,List.not_mem_nil,or_false,Sym2.eq_iff,Finset.mem_insert,
    Finset.mem_singleton]
  grind

/-- Every graph edge is in exactly one three-point block. This also counts the
blocks, so no auxiliary cardinality axiom for the block construction is needed. -/
theorem blocks_in_graph {V B : Type*} [Fintype V] [DecidableEq V] [Fintype B]
    (G : SimpleGraph V) [DecidableRel G.Adj] (tri : B → Finset V)
    (three : ∀ i, (tri i).card=3)
    (clique : ∀ i x, x∈tri i → ∀ y, y∈tri i → x≠y → G.Adj x y)
    (covers : ∀ x y, G.Adj x y → ∃! i, x∈tri i ∧ y∈tri i) :
    ∃ C : Multiset (Cycle G), IsCycleDecomposition G C ∧
      lengths C=Multiset.replicate (Fintype.card B) 3 ∧ G.edgeFinset.card=Fintype.card B*3 := by
  classical
  choose c len mem using fun i => cycle_on_triple (tri i) (three i) (clique i)
  have unique (e : Sym2 V) (he : e∈G.edgeFinset) : ∃! i, e∈(c i).edges := by
    induction e using Sym2.ind with
    | h x y =>
      have adj : G.Adj x y := G.mem_edgeFinset.mp he
      obtain ⟨i,hi,hu⟩ := covers x y adj
      exact ⟨i, (mem i x y adj.ne).mpr hi, fun j hj => hu j ((mem j x y adj.ne).mp hj)⟩
  exact AlspachFamilies.edge_partition G c len unique

private theorem card_congr {V : Type*} (G : SimpleGraph V) (a b : Fintype G.edgeSet) :
    (@edgeFinset V G a).card = (@edgeFinset V G b).card := by
  rw [Subsingleton.elim a b]

theorem matching_budget {V : Type*} [Fintype V] [DecidableEq V]
    (J : (completeGraph V).Subgraph) (hJ : J.IsPerfectMatching) :
    (completeGraph V \ J.spanningCoe).edgeFinset.card=
      (Fintype.card V).choose 2-(Fintype.card V)/2 := by
  classical
  have degree (v : V) : J.spanningCoe.degree v=1 := by
    rw [Subgraph.degree_spanningCoe]
    exact Subgraph.isPerfectMatching_iff_forall_degree.mp hJ v
  have sum := J.spanningCoe.sum_degrees_eq_twice_card_edges
  simp only [degree, Finset.sum_const,Finset.card_univ,nsmul_one] at sum
  have sum' : Fintype.card V=2*J.spanningCoe.edgeFinset.card := by
    calc _ = _ := sum
         _ = _ := congrArg (2*·) (card_congr J.spanningCoe _ _)
  have size : J.spanningCoe.edgeFinset.card=Fintype.card V/2 := by omega
  change ((⊤ : SimpleGraph V) \ J.spanningCoe).edgeFinset.card=_
  rw [edgeFinset_sdiff,Finset.card_sdiff_of_subset (edgeFinset_mono le_top),size,
    card_edgeFinset_top_eq_card_choose_two]

private theorem on_fin {n : Nat} {B : Type*} [Fintype B]
    (mate : Fin n → Fin n) (inv : Function.Involutive mate) (fixed : ∀ x, mate x ≠ x)
    (tri : B → Finset (Fin n)) (three : ∀ i, (tri i).card=3)
    (valid : ∀ i x, x∈tri i → ∀ y, y∈tri i → x≠y → mate x ≠ y)
    (covers : ∀ x y, x ≠ y → mate x ≠ y → ∃! i, x∈tri i ∧ y∈tri i)
    (m : Multiset Nat) (hm : ∀ x∈m, x=3) (budget : m.sum = n.choose 2 - n/2) :
    ∃ J : (completeGraph (Fin n)).Subgraph, J.IsPerfectMatching ∧
      ∃ C : Multiset (Cycle (completeGraph (Fin n) \ J.spanningCoe)),
        IsCycleDecomposition _ C ∧ lengths C=m := by
  classical
  let J : (completeGraph (Fin n)).Subgraph :=
    { verts := Set.univ
      Adj := fun x y => mate x=y
      adj_sub := fun h eq => fixed _ (h.trans eq.symm)
      edge_vert := fun _ => Set.mem_univ _
      symm := ⟨fun x y h => by rw [←h,inv x]⟩ }
  have perfect : J.IsPerfectMatching := by
    apply Subgraph.isPerfectMatching_iff.mpr
    exact fun x => ⟨mate x,rfl,fun y hy => Eq.symm hy⟩
  let G := completeGraph (Fin n) \ J.spanningCoe
  have adj (x y : Fin n) : G.Adj x y ↔ x≠y ∧ mate x≠y := Iff.rfl
  obtain ⟨C,dec,lens,sz⟩ := blocks_in_graph G tri three
    (fun i x hx y hy ne => (adj x y).mpr ⟨ne,valid i x hx y hy ne⟩)
    (fun x y h => covers x y ((adj x y).mp h).1 ((adj x y).mp h).2)
  have gb := matching_budget J perfect
  simp only [Fintype.card_fin] at gb
  have count : n.choose 2-n/2=Fintype.card B*3 :=
    gb.symm.trans ((card_congr G _ _).trans sz)
  have eq := Multiset.eq_replicate_of_mem hm
  have ct : m.card=Fintype.card B := by
    rw [eq,Multiset.sum_replicate,smul_eq_mul,count] at budget
    omega
  rw [ct] at eq
  exact ⟨J,perfect,C,dec,lens.trans eq.symm⟩

theorem from_blocks {V B : Type*} [Fintype V] [DecidableEq V] [Fintype B]
    (n : Nat) (card : Fintype.card V=n)
    (mate : V → V) (inv : Function.Involutive mate) (fixed : ∀ x, mate x ≠ x)
    (tri : B → Finset V) (three : ∀ i, (tri i).card=3)
    (valid : ∀ i x, x∈tri i → ∀ y, y∈tri i → x≠y → mate x ≠ y)
    (covers : ∀ x y, x ≠ y → mate x ≠ y → ∃! i, x∈tri i ∧ y∈tri i)
    (m : Multiset Nat) (hm : ∀ x∈m, x=3) (budget : m.sum = n.choose 2 - n/2) :
    ∃ J : (completeGraph (Fin n)).Subgraph, J.IsPerfectMatching ∧
      ∃ C : Multiset (Cycle (completeGraph (Fin n) \ J.spanningCoe)),
        IsCycleDecomposition _ C ∧ lengths C=m := by
  classical
  let f : V ≃ Fin n := Fintype.equivOfCardEq (by simpa only [Fintype.card_fin] using card)
  let paired (x : Fin n) := f (mate (f.symm x))
  let block (i : B) := (tri i).map f.toEmbedding
  have mem (i : B) (x : Fin n) : x∈block i ↔ f.symm x∈tri i := by simp [block]
  apply on_fin paired (fun x => by simp only [paired,Equiv.symm_apply_apply,inv (f.symm x),Equiv.apply_symm_apply]) (fun x h => fixed (f.symm x)
      (by simpa [paired] using congrArg f.symm h)) block (fun i => by simp [block,three])
  · intro i x hx y hy ne h
    have eq : mate (f.symm x)=f.symm y := by simpa [paired] using congrArg f.symm h
    exact valid i _ ((mem i x).mp hx) _ ((mem i y).mp hy) (fun e => ne (f.symm.injective e)) eq
  · intro x y ne nmate
    have pair := covers (f.symm x) (f.symm y) (fun e => ne (f.symm.injective e))
      (fun e => nmate (by simp [paired,e]))
    obtain ⟨i,hi,hu⟩ := pair
    exact ⟨i,⟨(mem i x).mpr hi.1,(mem i y).mpr hi.2⟩,fun j hj => hu j
      ⟨(mem j x).mp hj.1,(mem j y).mp hj.2⟩⟩
  · exact hm
  · exact budget

private theorem third_vertex {W : Type*} [DecidableEq W] {s : Finset W} (sz : s.card=3)
    {p x : W} (hp : p∈s) (hx : x∈s) (ne : x≠p) :
    ∃! y, y∈s ∧ y≠p ∧ y≠x := by
  let t := (s.erase p).erase x
  have h : t.card=1 := by
    rw [show t=(s.erase p).erase x by rfl,
      Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨ne,hx⟩),Finset.card_erase_of_mem hp,sz]
  obtain ⟨a,ha⟩ := Finset.card_eq_one.mp h
  have iff_mem (y : W) : (y∈s ∧ y≠p ∧ y≠x) ↔ y=a := by
    rw [←Finset.mem_singleton,←ha]
    simp only [t,Finset.mem_erase]
    tauto
  exact ⟨a,(iff_mem _).mpr rfl,fun y hy => (iff_mem y).mp hy⟩

/-- Deleting one vertex from a Steiner triple system leaves a perfect matching
as the uncovered pairs. All surviving blocks decompose its complement. -/
theorem from_steiner_delete {W B : Type*} [Fintype W] [DecidableEq W] [Fintype B]
    (n : Nat) (card : Fintype.card W=n+1) (p : W)
    (tri : B → Finset W) (three : ∀ i, (tri i).card=3)
    (pairs : ∀ x y : W, x≠y → ∃! i, x∈tri i ∧ y∈tri i)
    (m : Multiset Nat) (hm : ∀ x∈m, x=3) (budget : m.sum=n.choose 2-n/2) :
    ∃ J : (completeGraph (Fin n)).Subgraph, J.IsPerfectMatching ∧
      ∃ C : Multiset (Cycle (completeGraph (Fin n) \ J.spanningCoe)),
        IsCycleDecomposition _ C ∧ lengths C=m := by
  classical
  let V := {x : W // x≠p}
  let T := {i : B // p∉tri i}
  let rel (x y : V) := x≠y ∧ ∃ i, p∈tri i ∧ x.val∈tri i ∧ y.val∈tri i
  have symm {x y} (h : rel x y) : rel y x := by
    obtain ⟨ne,i,hp,hx,hy⟩ := h
    exact ⟨ne.symm,i,hp,hy,hx⟩
  have one (x : V) : ∃! y, rel x y := by
    obtain ⟨i,⟨hp,hx⟩,hu⟩ := pairs p x.val x.property.symm
    obtain ⟨z,⟨hz,zp,zx⟩,uz⟩ := third_vertex (three i) hp hx x.property
    refine ⟨⟨z,zp⟩,⟨fun eq => zx (congrArg Subtype.val eq.symm),i,hp,hx,hz⟩,?_⟩
    rintro y ⟨ne,j,jp,jx,jy⟩
    obtain rfl : j=i := hu j ⟨jp,jx⟩
    exact Subtype.ext (uz y.val ⟨jy,y.property,fun eq => ne (Subtype.ext eq.symm)⟩)
  let mate (x : V) := (one x).exists.choose
  have hit (x : V) : rel x (mate x) := (one x).exists.choose_spec
  have pair {x y} (h : rel x y) : mate x=y := (one x).unique (hit x) h
  have inv : Function.Involutive mate := fun x => pair (symm (hit x))
  have fixed (x : V) : mate x≠x := (hit x).1.symm
  let block (i : T) := (tri i.val).subtype (fun x => x≠p)
  have mem (x : V) (i : T) : x∈block i ↔ x.val∈tri i.val := Finset.mem_subtype
  have size (i : T) : (block i).card=3 := by
    dsimp only [block]
    rw [Finset.card_subtype,Finset.filter_eq_self.mpr,three]
    intro x hx eq
    exact i.property (eq ▸ hx)
  have remain : Fintype.card V=n := by
    change Fintype.card {x : W // ¬x=p} = n
    rw [Fintype.card_subtype_compl,Fintype.card_subtype_eq,card]
    omega
  apply from_blocks n remain mate inv fixed block size
  · intro i x hx y hy ne eq
    obtain ⟨_,j,hp,jx,jy⟩ : rel x y := eq ▸ hit x
    have uniq := pairs x.val y.val (fun h => ne (Subtype.ext h))
    have ji := uniq.unique (show x.val∈tri j ∧ y.val∈tri j from ⟨jx,jy⟩)
      (show x.val∈tri i.val ∧ y.val∈tri i.val from ⟨(mem x i).mp hx,(mem y i).mp hy⟩)
    exact i.property (ji ▸ hp)
  · intro x y ne notMate
    obtain ⟨i,hi,uni⟩ := pairs x.val y.val (fun eq => ne (Subtype.ext eq))
    have hp : p∉tri i := fun hp => notMate (pair ⟨ne,i,hp,hi⟩)
    let j : T := ⟨i,hp⟩
    exact ⟨j,⟨(mem x j).mpr hi.1,(mem y j).mpr hi.2⟩,fun b hb =>
      Subtype.ext (uni b.val ⟨(mem x b).mp hb.1,(mem y b).mp hb.2⟩)⟩
  · exact hm
  · exact budget

end TriangleBridge

namespace AlspachTriple

/-- The residue classes modulo n give a commutative Latin operation. -/
theorem addition_data (n : Nat) :
    ∃ plus : Fin n → Fin n → Fin n, (∀ x y, plus x y=plus y x) ∧
      (∀ x, Function.Bijective (plus x)) ∧
      (∀ x : Fin n, (plus x x).val=if x.val+x.val<n then x.val+x.val else x.val+x.val-n) := by
  let plus (x y : Fin n) : Fin n :=
    ⟨if x.val+y.val<n then x.val+y.val else x.val+y.val-n,
      by have := x.isLt; have := y.isLt; split <;> omega⟩
  refine ⟨plus, ?_, ?_, fun _ => rfl⟩
  · intro x y
    simp only [plus, Nat.add_comm x.val y.val]
  · intro x
    apply Finite.injective_iff_bijective.mp
    intro y z eq
    have hx := x.isLt
    have hy := y.isLt
    have hz := z.isLt
    have h := congrArg Fin.val eq
    apply Fin.ext
    simp only [plus] at h
    split_ifs at h <;> omega

/-- For the Skolem construction, the lower half consists of fixed points of
the diagonal. The upper half maps diagonally onto the lower half. -/
theorem half_latin (k : Nat) :
    ∃ op : Fin (2*k) → Fin (2*k) → Fin (2*k), ∃ other : Fin (2*k) → Fin (2*k),
       (∀ x y, op x y = op y x) ∧ (∀ x, Function.Bijective (op x)) ∧
       (∀ x, (other x).val<k ↔ ¬x.val<k) ∧ Function.Involutive other ∧
       (∀ x, other x ≠ x) ∧ (∀ x, op x x = if x.val<k then x else other x) := by
  obtain ⟨plus,comm,latin,diag⟩ := addition_data (2*k)
  let perm (z : Fin (2*k)) : Fin (2*k) :=
    ⟨if z.val%2=0 then z.val/2 else k+z.val/2,
     by have := z.isLt; split <;> omega⟩
  have bij : Function.Bijective perm := by
    apply Finite.injective_iff_bijective.mp
    intro a b eq
    have ha := a.isLt
    have hb := b.isLt
    have h := congrArg Fin.val eq
    apply Fin.ext
    simp only [perm] at h
    split_ifs at h <;> omega
  let other (x : Fin (2*k)) : Fin (2*k) :=
    ⟨if x.val<k then x.val+k else x.val-k,
     by have := x.isLt; split <;> omega⟩
  refine ⟨fun x y => perm (plus x y), other, fun a b => congrArg perm (comm a b),
    fun a => bij.comp (latin a), ?_, ?_, ?_, ?_⟩
  · intro x
    have h := x.isLt
    simp only [other]; split_ifs <;> omega
  · intro x
    have h := x.isLt
    apply Fin.ext
    simp only [other]; split_ifs <;> omega
  · intro x e
    have h := x.isLt
    have v := congrArg Fin.val e
    simp only [other] at v; split_ifs at v <;> omega
  · intro x
    have h := x.isLt
    apply Fin.ext
    simp only [perm,diag,other]
    split_ifs <;> (try dsimp) <;> omega

/-- Modular averaging over an odd cyclic group gives an idempotent
commutative Latin operation for the Bose construction. -/
theorem odd_latin (k : Nat) :
    ∃ op : Fin (2*k+1) → Fin (2*k+1) → Fin (2*k+1),
      (∀ x y, op x y = op y x) ∧ (∀ x, Function.Bijective (op x)) ∧
      (∀ x, op x x = x) := by
  obtain ⟨plus,comm,latin,diag⟩ := addition_data (2*k+1)
  let perm (z : Fin (2*k+1)) : Fin (2*k+1) :=
    ⟨if z.val%2=0 then z.val/2 else k+1+z.val/2,
     by have := z.isLt; split <;> omega⟩
  have bij : Function.Bijective perm := by
    apply Finite.injective_iff_bijective.mp
    intro a b eq
    have ha := a.isLt
    have hb := b.isLt
    have h := congrArg Fin.val eq
    apply Fin.ext
    simp only [perm] at h
    split_ifs at h <;> omega
  refine ⟨fun x y => perm (plus x y), fun a b => congrArg perm (comm a b),
    fun a => bij.comp (latin a), ?_⟩
  intro x
  have h := x.isLt
  apply Fin.ext
  simp only [perm,diag]
  split_ifs <;> omega

/-- The mixed triples of a commutative Latin square use each same-layer
pair once. Among consecutive-layer pairs, only the omitted diagonal
transitions are missing. Low fixed points carry a vertical triple instead. -/
theorem latin_blocks {Q : Type} [Fintype Q] [DecidableEq Q]
    (op : Q → Q → Q) (comm : ∀ x y, op x y = op y x)
    (latin : ∀ x, Function.Bijective (op x))
    (low : Q → Prop) (fixed : ∀ x, low x → op x x = x) :
    let hole (p q : Q × Fin 3) :=
      (¬low p.1 ∧ q.2=p.2+1 ∧ q.1=op p.1 p.1) ∨
      (¬low q.1 ∧ p.2=q.2+1 ∧ p.1=op q.1 q.1)
    ∃ family : Finset (Q × Fin 3) → Prop,
      (∀ b, family b → b.card=3) ∧
      (∀ b, family b → ∀ p∈b, ∀ q∈b, ¬hole p q) ∧
      (∀ p q : Q × Fin 3, p ≠ q → ¬hole p q →
        ∃! b : {b // family b}, p ∈ b.val ∧ q ∈ b.val) := by
  classical
  let N (i : Fin 3) := i+1
  have n_ne : ∀ i, N i ≠ i := by decide
  have n2_ne : ∀ i, N (N i) ≠ i := by decide
  have orient : ∀ i j, i=j ∨ N i=j ∨ N j=i := by decide
  let mix (x y : Q) (i : Fin 3) : Finset (Q × Fin 3) :=
    {(x,i),(y,i),(op x y,N i)}
  let vert (x : Q) : Finset (Q × Fin 3) := {x} ×ˢ Finset.univ
  let F (b : Finset (Q × Fin 3)) :=
    (∃ x, low x ∧ b=vert x) ∨ (∃ x y i, x≠y ∧ b=mix x y i)
  have mcomm (x y : Q) (i : Fin 3) : mix x y i = mix y x i := by
    ext z
    simp only [mix, Finset.mem_insert, Finset.mem_singleton, comm x y]
    tauto
  have mv {a x : Q} {i : Fin 3} : (a,i) ∈ vert x ↔ a=x := by
    simp [vert,eq_comm]
  have mm {a x y : Q} {i j : Fin 3} :
      (a,i) ∈ mix x y j ↔ ((a=x ∨ a=y) ∧ i=j) ∨ (a=op x y ∧ i=N j) := by
    simp only [mix, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
    tauto
  have three (b : Finset (Q × Fin 3)) (h : F b) : b.card=3 := by
    rcases h with ⟨x,_,rfl⟩ | ⟨x,y,i,hxy,rfl⟩
    · simp [vert]
    · simp [mix,hxy,Ne.symm (n_ne i)]
  have same {b : Finset (Q × Fin 3)} {x y : Q} {i : Fin 3} (h : F b) (ne : x≠y)
      (hx : (x,i) ∈ b) (hy : (y,i) ∈ b) : b = mix x y i := by
    rcases h with ⟨a,_,rfl⟩ | ⟨a,d,j,had,rfl⟩
    · exact False.elim (ne ((mv.mp hx).trans (mv.mp hy).symm))
    · have nh := n_ne j
      rcases mm.mp hx with ⟨hx|hx,hi⟩|⟨hx,hi⟩ <;>
        rcases mm.mp hy with ⟨hy|hy,hj⟩|⟨hy,hj⟩ <;> grind
  have cross {b : Finset (Q × Fin 3)} {x z : Q} {i : Fin 3}
      (h : F b) (hx : (x,i) ∈ b) (hz : (z,N i) ∈ b) :
      (low x ∧ z=x ∧ b=vert x) ∨ ∃ y, y≠x ∧ z=op x y ∧ b=mix x y i := by
    rcases h with ⟨a,ha,rfl⟩ | ⟨a,d,j,had,rfl⟩
    · exact Or.inl (by have := mv.mp hx; have := mv.mp hz; grind)
    · have nh := n_ne i
      have nj := n_ne j
      have n2 := n2_ne j
      rcases mm.mp hx with ⟨hx|hx,hi⟩|⟨hx,hi⟩ <;>
        rcases mm.mp hz with ⟨hz|hz,hj⟩|⟨hz,hj⟩ <;> grind
  have notHole {b : Finset (Q × Fin 3)} (hf : F b) {x : Q} {i : Fin 3}
      (hi : ¬low x) (hx : (x,i) ∈ b) : (op x x,N i) ∉ b := by
    intro hy
    rcases cross hf hx hy with ⟨hl,_⟩ | ⟨y,ne,eq,_⟩
    · exact hi hl
    · exact ne ((latin x).1 eq.symm)
  have uc (x z : Q) (i : Fin 3) (h : ¬(¬low x ∧ z=op x x)) :
      ∃! b : {b // F b}, (x,i) ∈ b.val ∧ (z,N i) ∈ b.val := by
    by_cases diag : z = op x x
    · have hl : low x := by by_contra no; exact h ⟨no,diag⟩
      have zx := diag.trans (fixed x hl)
      refine ⟨⟨vert x, Or.inl ⟨x,hl,rfl⟩⟩, ⟨mv.mpr rfl,mv.mpr zx⟩, ?_⟩
      rintro b ⟨hx,hz⟩
      rcases cross b.property hx hz with ⟨_,_,e⟩ | ⟨y,ne,hy,_⟩
      · exact Subtype.ext e
      · exact False.elim (ne ((latin x).1 (hy.symm.trans diag)))
    · obtain ⟨y,ey⟩ := (latin x).2 z
      have ne : x≠y := by rintro rfl; exact diag ey.symm
      refine ⟨⟨mix x y i, Or.inr ⟨x,y,i,ne,rfl⟩⟩,
        ⟨mm.mpr (Or.inl ⟨Or.inl rfl,rfl⟩),mm.mpr (Or.inr ⟨ey.symm,rfl⟩)⟩,?_⟩
      rintro b ⟨hx,hz⟩
      rcases cross b.property hx hz with ⟨hl,zx,_⟩ | ⟨y',_,e',eq⟩
      · exact False.elim (diag (zx.trans (fixed x hl).symm))
      · have yy := (latin x).1 (e'.symm.trans ey.symm)
        exact Subtype.ext (by simpa [yy] using eq)
  refine ⟨F, three, ?_, ?_⟩
  · rintro b h ⟨x,i⟩ hx ⟨z,j⟩ hz (⟨hn,hi,he⟩|⟨hn,hi,he⟩)
    · change j=i+1 at hi
      change z=op x x at he
      subst j
      subst z
      exact notHole h hn hx hz
    · change i=j+1 at hi
      change x=op z z at he
      subst i
      subst x
      exact notHole h hn hz hx
  · rintro ⟨x,i⟩ ⟨z,j⟩ neq nh
    rcases orient i j with eq|eq|eq
    · subst j
      have ne : x≠z := fun e => neq (congrArg (fun u => (u,i)) e)
      refine ⟨⟨mix x z i, Or.inr ⟨x,z,i,ne,rfl⟩⟩,
        ⟨mm.mpr (Or.inl ⟨Or.inl rfl,rfl⟩),mm.mpr (Or.inl ⟨Or.inr rfl,rfl⟩)⟩,?_⟩
      exact fun b hh => Subtype.ext (same b.property ne hh.1 hh.2)
    · subst j
      exact uc x z i (fun h => nh (Or.inl ⟨h.1,rfl,h.2⟩))
    · subst i
      simpa only [and_comm] using uc z x j (fun h => nh (Or.inr ⟨h.1,rfl,h.2⟩))

end AlspachTriple

namespace AlspachTriple
open SimpleGraph AlspachConjecture
open scoped Classical

/-- Skolem's construction at orders divisible by six. The omitted diagonal
pairs between the upper and lower halves form the required perfect matching. -/
theorem six_triangles (k : Nat) (m : Multiset Nat)
    (hm : ∀ x∈m, x=3) (budget : m.sum=(6*k).choose 2-(6*k)/2) :
    ∃ J : (completeGraph (Fin (6*k))).Subgraph, J.IsPerfectMatching ∧
      ∃ C : Multiset (Cycle (completeGraph (Fin (6*k)) \ J.spanningCoe)),
        IsCycleDecomposition _ C ∧ lengths C=m := by
  classical
  obtain ⟨op,other,comm,latin,swap,inv,ne,diag⟩ := half_latin k
  obtain ⟨F,three,avoids,covers⟩ := latin_blocks op comm latin (fun x => x.val<k)
    (fun x hx => by simpa [hx] using diag x)
  let mate (p : Fin (2*k) × Fin 3) : Fin (2*k) × Fin 3 :=
    (other p.1,if p.1.val<k then p.2+2 else p.2+1)
  have n1 : ∀ i : Fin 3, i+1+2=i := by decide
  have n2 : ∀ i : Fin 3, i+2+1=i := by decide
  have mi : Function.Involutive mate := by
    rintro ⟨x,i⟩
    by_cases h : x.val<k
    · have hh : ¬(other x).val<k := fun eq => (swap x).mp eq h
      simp [mate,h,hh,inv x,n2]
    · have hh := (swap x).mpr h
      simp [mate,h,hh,inv x,n1]
  have mf (p) : mate p ≠ p := fun e => ne p.1 (congrArg Prod.fst e)
  have holes (p q : Fin (2*k) × Fin 3) : mate p=q ↔
      (¬p.1.val<k ∧ q.2=p.2+1 ∧ q.1=op p.1 p.1) ∨
      (¬q.1.val<k ∧ p.2=q.2+1 ∧ p.1=op q.1 q.1) := by
    rcases p with ⟨x,i⟩
    constructor
    · rintro rfl
      by_cases h : x.val<k
      · have hh : ¬(other x).val<k := fun eq => (swap x).mp eq h
        right
        simp [mate,h,diag,hh,inv x,n2]
      · left
        simp [mate,h,diag]
    · rcases q with ⟨y,j⟩
      change ((¬x.val<k ∧ j=i+1 ∧ y=op x x) ∨
        (¬y.val<k ∧ i=j+1 ∧ x=op y y)) → _
      rintro (⟨h,rfl,rfl⟩ | ⟨h,rfl,hx⟩)
      · simp [mate,h,diag]
      · have eq : x=other y := by simpa [diag,h] using hx
        rw [eq]
        simp [mate,(swap y).mpr h,inv y,n1]
  let : Fintype {b // F b} := Fintype.ofFinite _
  have size : Fintype.card (Fin (2*k) × Fin 3)=6*k := by
    simp only [Fintype.card_prod,Fintype.card_fin]
    ring
  apply TriangleBridge.from_blocks (6*k) size mate mi mf
    (fun b : {b // F b} => b.val) (fun b => three _ b.property)
  · intro b p hp q hq _ eq
    exact avoids _ b.property _ hp _ hq ((holes _ _).mp eq)
  · exact fun p q pq nq => covers p q pq (fun h => nq ((holes p q).mpr h))
  · exact hm
  · exact budget

/-- Bose's Steiner system has three layers over a commutative idempotent
Latin square of order 2k+1. Delete one point to obtain the required matching. -/
theorem six_add_two_triangles (k : Nat) (m : Multiset Nat)
    (hm : ∀ x∈m, x=3) (budget : m.sum=(6*k+2).choose 2-(6*k+2)/2) :
    ∃ J : (completeGraph (Fin (6*k+2))).Subgraph, J.IsPerfectMatching ∧
      ∃ C : Multiset (Cycle (completeGraph (Fin (6*k+2)) \ J.spanningCoe)),
        IsCycleDecomposition _ C ∧ lengths C=m := by
  classical
  obtain ⟨op,comm,latin,fixed⟩ := odd_latin k
  obtain ⟨F,three,_,covers⟩ := latin_blocks op comm latin (fun _ => True) (fun x _ => fixed x)
  let : Fintype {b // F b} := Fintype.ofFinite _
  have size : Fintype.card (Fin (2*k+1) × Fin 3)=(6*k+2)+1 := by
    simp only [Fintype.card_prod,Fintype.card_fin]
    ring
  apply TriangleBridge.from_steiner_delete (6*k+2) size (0,0)
    (fun b : {b // F b} => b.val) (fun b => three _ b.property)
  · exact fun p q pq => covers p q pq (by simp)
  · exact hm
  · exact budget

end AlspachTriple

namespace AlspachTriple

/-- The edge budget of a triangle-only list rules out orders four modulo six. -/
theorem triangle_residues (n : Nat) (he : Even n) (m : Multiset Nat)
    (hm : ∀ x∈m, x=3) (hs : m.sum=n.choose 2-n/2) : n=6*(n/6) ∨ n=6*(n/6)+2 := by
  obtain ⟨j,hj⟩ := he
  let k := n/6
  change n=6*k ∨ n=6*k+2
  by_contra! h
  have bad : n=6*k+4 := by dsimp [k] at *; omega
  have twice : (6*k+4)*(6*k+4-1)=2*((3*k+2)*(6*k+3)) := by
    rw [show 6*k+4-1 = 6*k+3 by omega]
    ring
  have edges : (6*k+4).choose 2-(6*k+4)/2=3*(6*k*k+6*k+1)+1 := by
    rw [Nat.choose_two_right,twice,Nat.mul_div_cancel_left _ (by decide : 0<2),
      show (3*k+2)*(6*k+3) = (3*(6*k*k+6*k+1)+1)+(3*k+2) by ring]
    omega
  have same : m=Multiset.replicate m.card 3 := Multiset.eq_replicate.mpr ⟨rfl,hm⟩
  rw [same,Multiset.sum_replicate,smul_eq_mul,bad,edges] at hs
  omega

end AlspachTriple

namespace AlspachTriple
open SimpleGraph AlspachConjecture
open scoped Classical

/-- For every even order that admits a list consisting entirely of threes,
the complete graph minus a perfect matching has the required triangle decomposition. -/
theorem all_triangles (n : Nat) (even : Even n) (m : Multiset Nat)
    (only : ∀ x∈m, x=3) (budget : m.sum=n.choose 2-n/2) :
    ∃ J : (completeGraph (Fin n)).Subgraph, J.IsPerfectMatching ∧
      ∃ C : Multiset (Cycle (completeGraph (Fin n) \ J.spanningCoe)),
        IsCycleDecomposition _ C ∧ lengths C=m := by
  generalize hk : n/6 = k
  have hr := triangle_residues n even m only budget
  rw [hk] at hr
  rcases hr with h|h <;> subst n
  · exact six_triangles k m only budget
  · exact six_add_two_triangles k m only budget

end AlspachTriple

namespace AlspachSquares
open SimpleGraph AlspachConjecture
open scoped Classical

/-- Removing the edges that join the two vertices in each labeled pair
leaves exactly the pairs of vertices having different first coordinates. -/
theorem pair_matching {k n : Nat} (f : (Fin k × Bool) ≃ Fin n) :
    ∃ J : (completeGraph (Fin n)).Subgraph, J.IsPerfectMatching ∧
      ∀ x y, (completeGraph (Fin n) \ J.spanningCoe).Adj x y ↔ (f.symm x).1 ≠ (f.symm y).1 := by
  classical
  let flip (x : Fin k × Bool) := (x.1,!x.2)
  have invol : Function.Involutive flip := by
    rintro ⟨i,b⟩; cases b <;> rfl
  have fix (x : Fin k × Bool) : flip x ≠ x := by
    rcases x with ⟨i,b⟩; cases b <;> simp [flip]
  let mate (x : Fin n) := f (flip (f.symm x))
  have inv : Function.Involutive mate := fun x => by simp [mate,invol _]
  have fixed (x : Fin n) : mate x ≠ x := fun e => fix (f.symm x) (by simpa [mate] using congrArg f.symm e)
  let J : (completeGraph (Fin n)).Subgraph :=
    { verts := Set.univ
      Adj := fun x y => mate x=y
      adj_sub := fun h eq => fixed _ (h.trans eq.symm)
      edge_vert := fun _ => Set.mem_univ _
      symm := ⟨fun x y h => by rw [←h,inv x]⟩ }
  refine ⟨J,Subgraph.isPerfectMatching_iff.mpr (fun x => ⟨mate x,rfl,fun y hy => Eq.symm hy⟩),?_⟩
  intro x y
  change x≠y ∧ mate x≠y ↔ (f.symm x).1 ≠ (f.symm y).1
  obtain ⟨⟨i,b⟩,rfl⟩ := f.surjective x
  obtain ⟨⟨j,d⟩,rfl⟩ := f.surjective y
  cases b <;> cases d <;> simp [mate,flip]

end AlspachSquares

namespace AlspachSquares
open SimpleGraph

/-- Alternating between two paired vertices on each side traverses every cross edge once. -/
theorem square {k n : ℕ} (f : (Fin k × Bool) ≃ Fin n) (G : SimpleGraph (Fin n))
    (adj : ∀ x y, G.Adj x y ↔ (f.symm x).1 ≠ (f.symm y).1)
    {i j : Fin k} (diff : i ≠ j) :
    ∃ c : Cycle G, c.length = 4 ∧ ∀ x y, s(x,y) ∈ c.edges ↔
      ((f.symm x).1 = i ∧ (f.symm y).1 = j) ∨
      ((f.symm x).1 = j ∧ (f.symm y).1 = i) := by
  have across (a b : Bool) : G.Adj (f (i,a)) (f (j,b)) :=
    (adj _ _).mpr (by simpa only [Equiv.symm_apply_apply] using diff)
  let w : G.Walk (f (i,false)) (f (i,false)) :=
    .cons (across false false) (.cons (across true false).symm
      (.cons (across true true) (.cons (across false true).symm .nil)))
  have cycle : w.IsCycle := by
    simp [w, Walk.isCycle_def, diff, diff.symm]
  refine ⟨⟨_,w,cycle⟩,rfl,?_⟩
  intro x y
  obtain ⟨⟨r,a⟩,rfl⟩ := f.surjective x
  obtain ⟨⟨s,b⟩,rfl⟩ := f.surjective y
  change s(f (r,a), f (s,b)) ∈ [s(f (i,false), f (j,false)), s(f (j,false), f (i,true)),
    s(f (i,true), f (j,true)), s(f (j,true), f (i,false))] ↔ _
  cases a <;> cases b <;> simp
  grind

end AlspachSquares

namespace AlspachSquares
open SimpleGraph AlspachConjecture
open scoped Classical

private theorem ordered_pair {k : Nat} (a b : Fin k) (ne : a ≠ b) :
    ∃! q : {p : Fin k × Fin k // p.1 < p.2},
      (a=q.1.1 ∧ b=q.1.2) ∨ (a=q.1.2 ∧ b=q.1.1) := by
  rcases lt_or_gt_of_ne ne with h | h
  · refine ⟨⟨(a,b),h⟩,Or.inl ⟨rfl,rfl⟩,?_⟩
    rintro ⟨⟨i,j⟩,ij⟩ (⟨rfl,rfl⟩|⟨rfl,rfl⟩)
    · rfl
    · exact False.elim (lt_asymm h ij)
  · refine ⟨⟨(b,a),h⟩,Or.inr ⟨rfl,rfl⟩,?_⟩
    rintro ⟨⟨i,j⟩,ij⟩ (⟨rfl,rfl⟩|⟨rfl,rfl⟩)
    · exact False.elim (lt_asymm h ij)
    · rfl

/-- The four-cycle attached to each ordered representative of an unordered
pair of labels gives an exact edge partition of the graph. -/
theorem square_partition {k n : Nat} (f : (Fin k × Bool) ≃ Fin n)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (adj : ∀ x y, G.Adj x y ↔ (f.symm x).1 ≠ (f.symm y).1) :
    ∃ cs : Multiset (Cycle G), IsCycleDecomposition G cs ∧
      lengths cs = Multiset.replicate (Fintype.card {p : Fin k × Fin k // p.1<p.2}) 4 ∧
        G.edgeFinset.card=Fintype.card {p : Fin k × Fin k // p.1<p.2}*4 := by
  classical
  let B := {ij : Fin k × Fin k // ij.1 < ij.2}
  choose c len mem using fun q : B => square f G adj q.property.ne
  have unique (e : Sym2 (Fin n)) (he : e∈G.edgeFinset) : ∃! i, e∈(c i).edges := by
    induction e using Sym2.ind with
    | h x y =>
      have diff := (adj x y).mp (G.mem_edgeFinset.mp he)
      obtain ⟨i,hi,only⟩ := ordered_pair (f.symm x).1 (f.symm y).1 diff
      exact ⟨i,(mem i x y).mpr hi,fun j hj => only j ((mem j x y).mp hj)⟩
  exact AlspachFamilies.edge_partition G c len unique

/-- Each unordered pair of matching edges gives one square. Every remaining
edge connects exactly one such pair, so these squares partition the complement. -/
theorem all_fours (n : Nat) (even : Even n) (m : Multiset Nat)
    (hm : ∀ v ∈ m, v=4) (budget : m.sum=n.choose 2-n/2) :
    ∃ J : (completeGraph (Fin n)).Subgraph, J.IsPerfectMatching ∧
      ∃ C : Multiset (Cycle (completeGraph (Fin n) \ J.spanningCoe)),
        IsCycleDecomposition _ C ∧ lengths C=m := by
  classical
  obtain ⟨k,hk⟩ := even
  let f : (Fin k × Bool) ≃ Fin n := Fintype.equivOfCardEq (by
    simp only [Fintype.card_prod,Fintype.card_bool,Fintype.card_fin]; omega)
  obtain ⟨J,perfect,adj⟩ := pair_matching f
  let G := completeGraph (Fin n) \ J.spanningCoe
  let B := {ij : Fin k × Fin k // ij.1 < ij.2}
  obtain ⟨cs,decomp,lengthsEq,count⟩ := square_partition f G adj
  have total := TriangleBridge.matching_budget J perfect
  simp only [Fintype.card_fin] at total
  have eqEdges (a b : Fintype G.edgeSet) : (@edgeFinset _ G a).card=(@edgeFinset _ G b).card := by
    rw [Subsingleton.elim a b]
  have number : n.choose 2-n/2=Fintype.card B*4 := total.symm.trans ((eqEdges _ _).trans count)
  have eq := Multiset.eq_replicate_of_mem hm
  have card : m.card=Fintype.card B := by
    rw [eq,Multiset.sum_replicate,smul_eq_mul,number] at budget
    omega
  rw [card] at eq
  exact ⟨J,perfect,cs,decomp,lengthsEq.trans eq.symm⟩

end AlspachSquares


namespace AlspachPaired
open Finset SimpleGraph
open scoped Classical

/-- A cyclic listing of at least three vertices has one edge per vertex.
Color uniqueness across distinct listings makes their edge sets disjoint. -/
private theorem supports_of_listings {m r : ℕ} (hm : 3 ≤ m) :
    let next (a : Fin m) : Fin m := ⟨(a.val+1)%m, Nat.mod_lt _ (Nat.zero_lt_of_lt a.isLt)⟩
    let support (p : Fin m ≃ Fin m) := univ.image (fun a => s(p a,p (next a)))
    (∃ p : Fin r → (Fin m ≃ Fin m), ∀ (i j : Fin r) (a b : Fin m),
      s(p i a,p i (next a)) = s(p j b,p j (next b)) → i=j) →
    ∃ p : Fin r → (Fin m ≃ Fin m),
      (∀ i, support (p i) ⊆ (⊤ : SimpleGraph (Fin m)).edgeFinset) ∧
      (∀ i, (support (p i)).card=m) ∧ Pairwise (fun i j => Disjoint (support (p i)) (support (p j))) := by
  classical
  intro next support ⟨p,unique⟩
  have nofix (a : Fin m) : next a ≠ a := by
    intro h
    have eq := congrArg Fin.val h
    change (a.val+1)%m = a.val at eq
    have ha := a.isLt
    by_cases last : a.val+1=m
    · rw [last,Nat.mod_self] at eq
      omega
    · rw [Nat.mod_eq_of_lt (by omega)] at eq
      omega
  have notTwo (a : Fin m) : next (next a) ≠ a := by
    intro h
    have eq := congrArg Fin.val h
    change ((a.val+1)%m+1)%m = a.val at eq
    have ha := a.isLt
    by_cases last : a.val+1=m
    · rw [last,Nat.mod_self,Nat.zero_add,Nat.mod_eq_of_lt (by omega)] at eq
      omega
    · rw [Nat.mod_eq_of_lt (by omega : a.val+1< m)] at eq
      by_cases penult : a.val+1+1=m
      · rw [penult,Nat.mod_self] at eq
        omega
      · rw [Nat.mod_eq_of_lt (by omega)] at eq
        omega
  refine ⟨p,?_,?_,?_⟩
  · intro i e he
    obtain ⟨a,_,rfl⟩ := mem_image.mp he
    exact SimpleGraph.mem_edgeFinset.mpr (fun h => nofix a ((p i).injective h).symm)
  · intro i
    change (univ.image (fun a => s(p i a,p i (next a)))).card=m
    rw [card_image_of_injective]
    · simp
    · intro a b eq
      rcases Sym2.eq_iff.mp eq with ⟨h,_⟩ | ⟨h,q⟩
      · exact (p i).injective h
      · exact (notTwo b ((congrArg next ((p i).injective h).symm).trans ((p i).injective q))).elim
  · intro i j hij
    apply Finset.disjoint_left.mpr
    intro e hi hj
    obtain ⟨a,_,ha⟩ := mem_image.mp hi
    obtain ⟨b,_,hb⟩ := mem_image.mp hj
    exact hij (unique i j a b (ha.trans hb.symm))

/-- Choose as many labeled Walecki cycles as needed from an even base. -/
private theorem even_listings {m r : ℕ} (even : Even m) (large : 4 ≤ m) (limit : r ≤ m/2-1) :
    let next (a : Fin m) : Fin m := ⟨(a.val+1)%m, Nat.mod_lt _ (Nat.zero_lt_of_lt a.isLt)⟩
    ∃ p : Fin r → (Fin m ≃ Fin m), ∀ (i j : Fin r) (a b : Fin m),
      s(p i a,p i (next a)) = s(p j b,p j (next b)) → i=j := by
  classical
  have shape : ∃ k, m = 2*k+2 ∧ r ≤ k := by
    obtain ⟨v,hv⟩ := even
    exact ⟨v-1,by omega,by omega⟩
  obtain ⟨k,rfl,hr⟩ := shape
  let m := 2*k+2
  intro next
  obtain ⟨wal,colour,_,bound,injective,comm,step,close,_⟩ := EvenWalecki.zigzag_data k
  let idx (i : Fin r) : Fin k := ⟨i.val,i.isLt.trans_le hr⟩
  let g (i : Fin r) (a : Fin m) : Fin m := ⟨wal i.val a.val,bound i.val a.val (idx i).isLt⟩
  have inj (i : Fin r) : Function.Injective (g i) := by
    intro t u eq
    exact Fin.ext (injective i.val t u (idx i).isLt (by have := t.isLt; dsimp [m] at *; omega)
      (by have := u.isLt; dsimp [m] at *; omega) (congrArg Fin.val eq))
  let p (i : Fin r) := Equiv.ofBijective (g i) ⟨inj i,Finite.surjective_of_injective (inj i)⟩
  let col : Sym2 (Fin m) → Nat := Sym2.lift ⟨fun a b => colour a.val b.val,fun a b => comm a b⟩
  have shade (i : Fin r) (t : Fin m) : col s(p i t,p i (next t)) = i.val := by
    change colour (wal i.val t.val) (wal i.val ((t.val+1)%(2*k+2))) = i.val
    by_cases last : t.val = 2*k+1
    · simp only [last, show 2*k+1+1 = 2*k+2 by omega, Nat.mod_self]
      exact close i.val (idx i).isLt
    · have hn : t.val+1 < 2*k+2 := by have := t.isLt; dsimp [m] at *; omega
      rw [Nat.mod_eq_of_lt hn]
      exact step i.val t.val (idx i).isLt (by omega)
  refine ⟨p,fun i j a b eq => Fin.ext ?_⟩
  exact ((shade i a).symm.trans (congrArg col eq)).trans (shade j b)

set_option maxHeartbeats 1800000 in
/-- Walecki's alternating construction on the residues modulo `2*k` together
with one point at infinity. The vertex order and edge coloring follow
@Salofe's odd-order Hamilton decomposition in LeftToSolve PR #6728. -/
private theorem odd_listings {m r : ℕ} (odd : Odd m) (limit : r ≤ (m-1)/2) :
    let next (a : Fin m) : Fin m := ⟨(a.val+1)%m, Nat.mod_lt _ (Nat.zero_lt_of_lt a.isLt)⟩
    ∃ p : Fin r → (Fin m ≃ Fin m), ∀ (i j : Fin r) (a b : Fin m),
      s(p i a,p i (next a)) = s(p j b,p j (next b)) → i=j := by
  classical
  obtain ⟨k,rfl⟩ := odd
  intro next
  have lim : r ≤ k := by omega
  let vertex (i t : ℕ) :=
    if 2*k ≤ t then 2*k else if t%2=1 then i+(t+1)/2
    else if t/2 ≤ i then i-t/2 else i+2*k-t/2
  have bound (i t : ℕ) (hi : i<k) : vertex i t < 2*k+1 := by
    simp only [vertex]; split_ifs <;> omega
  have inject (i t v : ℕ) (hi : i<k) (ht : t ≤ 2*k) (hv : v ≤ 2*k)
      (eq : vertex i t = vertex i v) : t=v := by
    simp only [vertex] at eq; split_ifs at eq <;> omega
  let color (a b : ℕ) :=
    if a=2*k then (if b<k then b else b-k)
    else if b=2*k then (if a<k then a else a-k)
    else if a+b<2*k then (a+b)/2 else (a+b-2*k)/2
  have comm (a b : ℕ) : color a b = color b a := by
    simp only [color]; split_ifs <;> omega
  have along (i t : ℕ) (hi : i<k) (ht : t<2*k) : color (vertex i t) (vertex i (t+1))=i := by
    simp only [color,vertex]; split_ifs <;> omega
  have close (i : ℕ) (hi : i<k) : color (vertex i (2*k)) (vertex i 0)=i := by
    simp only [color,vertex]; split_ifs <;> omega
  let g (i : Fin r) (t : Fin (2*k+1)) : Fin (2*k+1) :=
    ⟨vertex i.val t.val,bound i.val t.val (i.isLt.trans_le lim)⟩
  have inj (i : Fin r) : Function.Injective (g i) := by
    intro t v eq
    exact Fin.ext (inject i.val t.val v.val (i.isLt.trans_le lim) (by have := t.isLt; omega)
      (by have := v.isLt; omega) (congrArg Fin.val eq))
  let f (i : Fin r) := Equiv.ofBijective (g i) ⟨inj i,Finite.surjective_of_injective (inj i)⟩
  let paint : Sym2 (Fin (2*k+1)) → ℕ := Sym2.lift ⟨fun a b => color a.val b.val,fun a b => comm a.val b.val⟩
  have edge (i : Fin r) (a : Fin (2*k+1)) : paint s(f i a,f i (next a))=i.val := by
    change color (vertex i.val a.val) (vertex i.val ((a.val+1)%(2*k+1)))=i.val
    by_cases last : a.val=2*k
    · rw [last,Nat.mod_self]
      exact close i.val (i.isLt.trans_le lim)
    · have lt : a.val+1 < 2*k+1 := by have := a.isLt; omega
      rw [Nat.mod_eq_of_lt lt]
      exact along i.val a.val (i.isLt.trans_le lim) (by omega)
  refine ⟨f,fun i j a b eq => Fin.ext ?_⟩
  exact ((edge i a).symm.trans (congrArg paint eq)).trans (edge j b)

/-- Select edge-disjoint cyclic listings from the even-order Walecki construction. -/
theorem packed_base_family {m r : ℕ} (even : Even m) (large : 4 ≤ m) (limit : r ≤ m/2-1) :
    let next (a : Fin m) : Fin m := ⟨(a.val+1)%m, Nat.mod_lt _ (Nat.zero_lt_of_lt a.isLt)⟩
    let support (p : Fin m ≃ Fin m) := univ.image (fun a => s(p a,p (next a)))
    ∃ p : Fin r → (Fin m ≃ Fin m),
      (∀ i, support (p i) ⊆ (⊤ : SimpleGraph (Fin m)).edgeFinset) ∧
      (∀ i, (support (p i)).card=m) ∧ Pairwise (fun i j => Disjoint (support (p i)) (support (p j))) := supports_of_listings (by omega) (even_listings even large limit)

/-- Select edge-disjoint cyclic listings from the odd-order Walecki construction. -/
theorem packed_odd_base_family {m r : ℕ} (odd : Odd m) (large : 3 ≤ m) (limit : r ≤ (m-1)/2) :
    let next (a : Fin m) : Fin m := ⟨(a.val+1)%m, Nat.mod_lt _ (Nat.zero_lt_of_lt a.isLt)⟩
    let support (p : Fin m ≃ Fin m) := univ.image (fun a => s(p a,p (next a)))
    ∃ p : Fin r → (Fin m ≃ Fin m),
      (∀ i, support (p i) ⊆ (⊤ : SimpleGraph (Fin m)).edgeFinset) ∧
      (∀ i, (support (p i)).card=m) ∧ Pairwise (fun i j => Disjoint (support (p i)) (support (p j))) := supports_of_listings large (odd_listings odd limit)

/-- Every base with at least three vertices admits up to `⌊(m−1)/2⌋`
pairwise edge-disjoint Hamiltonian cyclic listings. -/
theorem packed_base_family_of_limit {m r : ℕ} (large : 3 ≤ m) (limit : r ≤ (m-1)/2) :
    let next (a : Fin m) : Fin m := ⟨(a.val+1)%m, Nat.mod_lt _ (Nat.zero_lt_of_lt a.isLt)⟩
    let support (p : Fin m ≃ Fin m) := univ.image (fun a => s(p a,p (next a)))
    ∃ p : Fin r → (Fin m ≃ Fin m),
      (∀ i, support (p i) ⊆ (⊤ : SimpleGraph (Fin m)).edgeFinset) ∧
      (∀ i, (support (p i)).card=m) ∧ Pairwise (fun i j => Disjoint (support (p i)) (support (p j))) := by
  rcases Nat.even_or_odd m with even|odd
  · have hl : 4 ≤ m ∧ r ≤ m/2-1 := by obtain ⟨k,hk⟩ := even; omega
    exact packed_base_family even hl.1 hl.2
  · exact packed_odd_base_family odd large limit

end AlspachPaired

namespace AlspachLift
open SimpleGraph

/-- An injective cyclic ordering of at least three vertices gives a cycle with
exactly its successive edges. The first edge wraps from the last listed vertex. -/
theorem cycleFromListing {V : Type} {G : SimpleGraph V} {L : ℕ} (hL : 3 ≤ L)
    (f : Fin L ↪ V) (step : Fin L → Fin L) (hstep : ∀ i, (step i).val = (i.val+1)%L)
    (adj : ∀ i, G.Adj (f i) (f (step i))) :
    ∃ c : Cycle G, c.length = L ∧ ∀ e : Sym2 V, e ∈ c.edges ↔ ∃ i, e = s(f i,f (step i)) := by
  let v (n : ℕ) : V := f ⟨n % L, Nat.mod_lt _ (by omega)⟩
  have atIndex (i : Fin L) : v i.val = f i := congrArg f (Fin.ext (Nat.mod_eq_of_lt i.isLt))
  have successor (i : Fin L) : f (step i) = v (i.val+1) := congrArg f (Fin.ext (hstep i))
  have inj {i j : ℕ} (hi : i < L) (hj : j < L) (h : v i = v j) : i = j := by
    have eq := congrArg Fin.val (f.injective h)
    change i%L=j%L at eq
    simpa [Nat.mod_eq_of_lt hi,Nat.mod_eq_of_lt hj] using eq
  have wrap : v (L-1+1) = v 0 := by simp [v,Nat.sub_add_cancel (show 1 ≤ L by omega)]
  have following (i : ℕ) (hi : i < L) : G.Adj (v i) (v (i+1)) := by
    let j : Fin L := ⟨i,hi⟩
    change G.Adj (v j.val) (v (j.val+1))
    rw [atIndex,← successor]
    exact adj j
  obtain ⟨w,vs,es,wl⟩ := EvenWalecki.path_through v (L-1) (fun t ht => following t (by omega))
  have close : G.Adj (v (L-1)) (v 0) := wrap ▸ following (L-1) (by omega)
  let c : Cycle G := {
    base := v (L-1)
    walk := Walk.cons close w
    isCycle := by
      rw [Walk.cons_isCycle_iff]
      constructor
      · rw [Walk.isPath_def, vs]
        apply List.Nodup.map_on _ List.nodup_range
        intro i hi j hj h
        rw [List.mem_range] at hi hj
        exact inj (by omega) (by omega) h
      · rw [es,List.mem_map]
        rintro ⟨i,hi,h⟩
        rw [List.mem_range] at hi
        rcases Sym2.eq_iff.mp h with ⟨h,_⟩ | ⟨h1,h2⟩
        · have hh := inj (by omega) (by omega) h
          omega
        · have hh1 := inj (by omega) (by omega) h1
          have hh2 := inj (by omega) (by omega) h2
          omega }
  refine ⟨c,?_,?_⟩
  · change (Walk.cons close w).length = L
    rw [Walk.length_cons,wl]
    omega
  · intro e
    change e ∈ (Walk.cons close w).edges ↔ _
    simp only [Walk.edges_cons,es,List.mem_cons,List.mem_map,List.mem_range]
    constructor
    · rintro (h | ⟨t,ht,h⟩)
      · let j : Fin L := ⟨L-1,by omega⟩
        refine ⟨j,?_⟩
        rw [successor, ← atIndex j]
        change e = s(v (L-1),v (L-1+1))
        rwa [wrap]
      · let j : Fin L := ⟨t,by omega⟩
        exact ⟨j,by rw [successor,← atIndex j]; exact h.symm⟩
    · rintro ⟨i,rfl⟩
      rw [successor, ← atIndex i]
      by_cases h : i.val = L-1
      · left; rw [h,wrap]
      · exact Or.inr ⟨i.val,by omega,rfl⟩

set_option maxHeartbeats 1800000 in
/-- Expand every edge of a base cycle to a complete bipartite graph on its
    two pairs. Two Hamilton cycles partition all resulting edges. The order
    has a turn at layer zero, so there is no parity restriction on the base. -/
theorem liftPair_any {m : ℕ} {V : Type} (large : 3 ≤ m)
    (f : (Fin m × Bool) ≃ V) (G : SimpleGraph V)
    (step : Fin m → Fin m) (stepEq : ∀ i, (step i).val=(i.val+1)%m)
    (adj : ∀ i a b, G.Adj (f (i,a)) (f (step i,b))) :
    ∃ c : Bool → Cycle G, (∀ t, (c t).length = 2*m) ∧
      (∀ t x y, s(x,y) ∈ (c t).edges →
        step (f.symm x).1 = (f.symm y).1 ∨ step (f.symm y).1 = (f.symm x).1) ∧
      ∀ x y, (step (f.symm x).1 = (f.symm y).1 ∨ step (f.symm y).1 = (f.symm x).1) →
        ∃! t, s(x,y) ∈ (c t).edges := by
  let next {n : ℕ} (i : Fin n) : Fin n := ⟨(i.val+1)%n,Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩
  have hstep : step = @next m := funext fun i => Fin.ext (stepEq i)
  subst step
  let double {m : ℕ} (t : Fin (2*m)) : Fin m × Bool :=
    if h : t.val < m then (⟨t.val,h⟩,false) else (⟨t.val-m,by have := t.isLt; omega⟩,true)
  let index {m : ℕ} (v : Fin m × Bool) : Fin (2*m) :=
    ⟨if v.2 then m+v.1.val else v.1.val, by have := v.1.isLt; split <;> omega⟩
  have double_index {m : ℕ} (v : Fin m × Bool) : double (index v) = v := by
    obtain ⟨i,a⟩ := v
    cases a
    · simp [double,index,i.isLt]
    · simp [double,index]
  have index_double {m : ℕ} (t : Fin (2*m)) : index (double t) = t := by
    apply Fin.ext
    unfold double
    split <;> simp [index]
    omega
  let halves (m : ℕ) : Fin (2*m) ≃ Fin m × Bool := {
    toFun := double
    invFun := index
    left_inv := index_double
    right_inv := double_index }
  let parity {m : ℕ} (i : Fin m) : Bool := decide (i.val % 2 = 1)
  let turn {m : ℕ} (i : Fin m) : Bool := decide (i.val + 1 = m)
  have next_next_ne {m : ℕ} (large : 3 ≤ m) (i : Fin m) : next (next i) ≠ i := by
    intro h
    have eq := congrArg Fin.val h
    change (((i.val+1)%m)+1)%m=i.val at eq
    have hi := i.isLt
    by_cases small : i.val+1< m
    · rw [Nat.mod_eq_of_lt small] at eq
      by_cases small' : i.val+1+1< m
      · rw [Nat.mod_eq_of_lt small'] at eq; omega
      · rw [show i.val+1+1=m by omega,Nat.mod_self] at eq; omega
    · rw [show i.val+1=m by omega,Nat.mod_self] at eq
      simp only [Nat.zero_add] at eq
      rw [Nat.mod_eq_of_lt (by omega)] at eq; omega
  have next_index {m : ℕ} (i : Fin m) (b : Bool) :
      next (index (i,b)) = index (next i, xor b (turn i)) := by
    have hi := i.isLt
    by_cases w : i.val+1=m
    · have a : (next i).val=0 := by simp [next,w]
      have h : turn i=true := by simp [turn,w]
      cases b <;> apply Fin.ext
      · change (i.val+1)%(2*m) = _
        simp [h,index,a,w,Nat.mod_eq_of_lt (show m<2*m by omega)]
      · change (m+i.val+1)%(2*m) = _
        rw [show m+i.val+1=2*m by omega,Nat.mod_self]
        simp [h,index,a]
    · have a : (next i).val=i.val+1 := Nat.mod_eq_of_lt (by omega)
      have h : turn i=false := by simp [turn,w]
      cases b <;> apply Fin.ext
      · change (i.val+1)%(2*m) = _
        simp [h,index,a,Nat.mod_eq_of_lt (show i.val+1<2*m by omega)]
      · change (m+i.val+1)%(2*m) = _
        rw [Nat.mod_eq_of_lt (show m+i.val+1<2*m by omega)]
        simp [h,index,a,Nat.add_assoc]
  let reverseLayer {m : ℕ} (i : Fin m) : Fin m :=
    ⟨if i.val = 0 then 0 else m-i.val, by have := i.isLt; split <;> omega⟩

  have reverseLayer_involutive {m : ℕ} (i : Fin m) : reverseLayer (reverseLayer i) = i := by
    apply Fin.ext
    have hi := i.isLt
    by_cases hz : i.val = 0
    · simp [reverseLayer,hz]
    · simp [reverseLayer,hz,show m-i.val ≠ 0 by omega,show m-(m-i.val) = i.val by omega]

  have reverseLayer_zero_iff {m : ℕ} (i : Fin m) : (reverseLayer i).val = 0 ↔ i.val = 0 := by
    have hi := i.isLt
    by_cases hz : i.val = 0 <;> simp [reverseLayer,hz,show m-i.val ≠ 0 by omega]


  have next_reverseLayer_next {m : ℕ} (i : Fin m) : next (reverseLayer (next i)) = reverseLayer i := by
    apply Fin.ext
    have hi := i.isLt
    by_cases hl : i.val+1 = m
    · have h : (next i).val = 0 := by simp [next,hl]
      change ((reverseLayer (next i)).val + 1) % m = (reverseLayer i).val
      simp only [reverseLayer,h,if_true,Nat.zero_add]
      by_cases hz : i.val = 0
      · have hm : m = 1 := by omega
        subst m; simp
      · rw [if_neg hz,Nat.mod_eq_of_lt (by omega)]; omega
    · have h : (next i).val = i.val+1 := Nat.mod_eq_of_lt (by omega)
      change ((reverseLayer (next i)).val + 1) % m = (reverseLayer i).val
      simp only [reverseLayer,h,Nat.add_one_ne_zero,if_false]
      by_cases hz : i.val = 0
      · rw [if_pos hz, hz, show m-(0+1)+1=m by omega,Nat.mod_self]
      · rw [if_neg hz,Nat.mod_eq_of_lt (by omega)]; omega

  let turningPair {m : ℕ} (i : Fin m) (b : Bool) : Fin m × Bool :=
    (if b then reverseLayer i else i,b)

  let turningListing (m : ℕ) : Fin (2*m) ≃ Fin m × Bool :=
    (halves m).trans {
      toFun := fun v => turningPair v.1 v.2
      invFun := fun v => turningPair v.1 v.2
      left_inv := by rintro ⟨i,b⟩; cases b <;> simp [turningPair,reverseLayer_involutive]
      right_inv := by rintro ⟨i,b⟩; cases b <;> simp [turningPair,reverseLayer_involutive] }

  have turningListing_index {m : ℕ} (i : Fin m) (b : Bool) :
      turningListing m (index (i,b)) = turningPair i b := by
    change turningPair (double (index (i,b))).1 (double (index (i,b))).2 = _
    rw [double_index]

  have turningListing_next_index {m : ℕ} (i : Fin m) (b : Bool) :
      turningListing m (next (index (i,b))) = turningPair (next i) (xor b (turn i)) := by
    rw [next_index,turningListing_index]
  let change {m : ℕ} (t : Bool) (i : Fin m) (v : Bool) : Bool :=
    xor v (t && (decide (i.val=0) || parity i))

  let coordinate (t : Bool) (m : ℕ) : Fin m × Bool ≃ Fin m × Bool := {
    toFun v := (v.1, change t v.1 v.2)
    invFun v := (v.1, change t v.1 v.2)
    left_inv := by rintro ⟨i,a⟩; change (_,change t i (change t i a)) = _; simp [change]
    right_inv := by rintro ⟨i,a⟩; change (_,change t i (change t i a)) = _; simp [change] }

  let leftBase {m : ℕ} (i : Fin m) (z : Bool) := if i.val=0 then false else z
  let rightBase {m : ℕ} (i : Fin m) (z : Bool) := if i.val=0 then true else z

  let fits {m : ℕ} (t : Bool) (i : Fin m) (a b : Bool) : Prop :=
    ∃ z : Bool, change t i (leftBase i z) = a ∧ change t (next i) (rightBase (next i) z) = b

  have next_zero_iff {m : ℕ} (i : Fin m) : (next i).val=0 ↔ i.val+1=m := by
    have hi := i.isLt
    change (i.val+1)%m=0 ↔ _
    by_cases h : i.val+1=m
    · simp [h]
    · rw [Nat.mod_eq_of_lt (show i.val+1< m by omega)]
      omega

  have interParity {m : ℕ} (i : Fin m) (h : (next i).val ≠ 0) : parity (next i) = !(parity i) := by
    have hi := i.isLt
    have hn : i.val+1 ≠ m := fun w => h ((next_zero_iff i).mpr w)
    unfold parity
    change decide (((i.val+1)%m)%2=1) = _
    rw [Nat.mod_eq_of_lt (show i.val+1< m by omega)]
    by_cases bit : i.val%2=1
    · simp [bit,show (i.val+1)%2≠1 by omega]
    · simp [bit,show (i.val+1)%2=1 by omega]


  have unique_fit {m : ℕ} (large : 3 ≤ m) (i : Fin m) (a b : Bool) :
      ∃! t : Bool, fits t i a b := by
    by_cases hi : i.val=0
    · have hj : (next i).val≠0 := fun h => by have := (next_zero_iff i).mp h; omega
      simp only [fits,change,leftBase,rightBase,hi,hj,if_pos,if_false,decide_true,decide_false,
        Bool.true_or,Bool.false_or,Bool.and_true,Bool.false_xor]
      refine ⟨a,⟨xor b (a && parity (next i)), rfl, by simp⟩,?_⟩
      rintro t ⟨z,h,_⟩
      exact h
    · by_cases hj : (next i).val=0
      · simp only [fits,change,leftBase,rightBase,hi,hj,if_pos,if_false,decide_true,decide_false,
          Bool.true_or,Bool.false_or,Bool.and_true,Bool.true_xor]
        refine ⟨!b,⟨xor a ((!b) && parity i), by simp, by simp⟩,?_⟩
        rintro t ⟨z,_,h⟩
        cases t <;> cases b <;> first | rfl | contradiction
      · simp only [fits,change,leftBase,rightBase,hi,hj,if_false,decide_false,Bool.false_or,interParity i hj]
        refine ⟨xor a b, ?_, ?_⟩
        · refine ⟨xor a (xor a b && parity i),by simp,?_⟩
          cases a <;> cases b <;> cases parity i <;> rfl
        · rintro t ⟨z,h,k⟩
          have cancel : ∀ t z a b v : Bool, xor z (t && v) = a → xor z (t && !v) = b → t = xor a b := by decide
          exact cancel t z a b (parity i) h k
  let arc {m : ℕ} (i : Fin m) (z : Bool) : Sym2 (Fin m × Bool) :=
    s((i,leftBase i z),(next i,rightBase (next i) z))

  let stepEdge {m : ℕ} (j : Fin (2*m)) : Sym2 (Fin m × Bool) :=
    s(turningListing m j,turningListing m (next j))

  have reverse_zero {m : ℕ} {i : Fin m} (h : i.val=0) : reverseLayer i=i := by
    apply Fin.ext
    simp [reverseLayer,h]

  have front {m : ℕ} (i : Fin m) : stepEdge (index (i,false)) = arc i false := by
    simp only [stepEdge,turningListing_index,turningListing_next_index]
    by_cases h : i.val+1=m
    · have hz := (next_zero_iff i).mpr h
      simp [arc,turningPair,turn,leftBase,rightBase,h,hz,reverse_zero hz]
    · have hz : (next i).val ≠ 0 := fun w => h ((next_zero_iff i).mp w)
      simp [arc,turningPair,turn,leftBase,rightBase,h,hz]

  have back {m : ℕ} (i : Fin m) : stepEdge (index (i,true)) = arc (reverseLayer (next i)) true := by
    simp only [stepEdge,turningListing_index,turningListing_next_index]
    unfold arc
    rw [next_reverseLayer_next]
    by_cases h : i.val+1=m
    · have hz := (next_zero_iff i).mpr h
      apply Sym2.eq_iff.mpr; right
      simp [turningPair,turn,leftBase,rightBase,h,hz,reverse_zero hz]
    · have hz : (next i).val ≠ 0 := fun w => h ((next_zero_iff i).mp w)
      apply Sym2.eq_iff.mpr; right
      simp [turningPair,turn,leftBase,rightBase,h,hz,reverseLayer_zero_iff]

  have edge_arcs {m : ℕ} (e : Sym2 (Fin m × Bool)) :
      (∃ j : Fin (2*m), e = stepEdge j) ↔ ∃ i z, e = arc i z := by
    constructor
    · rintro ⟨j,rfl⟩
      obtain ⟨⟨i,z⟩,hj⟩ := (halves m).symm.surjective j
      change index (i,z)=j at hj
      subst j
      cases z
      · exact ⟨i,false,front i⟩
      · exact ⟨reverseLayer (next i),true,back i⟩
    · rintro ⟨i,z,rfl⟩
      cases z
      · exact ⟨index (i,false),(front i).symm⟩
      · refine ⟨index (reverseLayer (next i),true),?_⟩
        rw [back,next_reverseLayer_next,reverseLayer_involutive]
  let g (t : Bool) := (coordinate t m).trans f
  let order (t : Bool) := (turningListing m).trans (g t)
  have map_step (t : Bool) (j : Fin (2*m)) (i : Fin m) (z : Bool)
      (eq : stepEdge j = arc i z) :
      s(order t j,order t (next j)) =
        s(f (i,change t i (leftBase i z)),f (next i,change t (next i) (rightBase (next i) z))) :=
    congrArg (Sym2.map (g t)) eq
  have follow (t : Bool) (j : Fin (2*m)) : G.Adj (order t j) (order t (next j)) := by
    obtain ⟨i,z,eq⟩ := (edge_arcs (stepEdge j)).mp ⟨j,rfl⟩
    have h := map_step t j i z eq
    rcases Sym2.eq_iff.mp h with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩ <;> rw [h₁,h₂]
    · exact adj _ _ _
    · exact (adj _ _ _).symm
  have len : 3 ≤ 2*m := by omega
  have existsCycle (t : Bool) := cycleFromListing len (order t).toEmbedding next (fun _ => rfl) (follow t)
  choose c cycleLength cycleEdges using existsCycle
  have form (t : Bool) (e : Sym2 V) : e ∈ (c t).edges ↔
      ∃ i z, e = s(f (i,change t i (leftBase i z)),f (next i,change t (next i) (rightBase (next i) z))) := by
    rw [cycleEdges]
    constructor
    · rintro ⟨j,h⟩
      obtain ⟨i,z,eq⟩ := (edge_arcs (stepEdge j)).mp ⟨j,rfl⟩
      exact ⟨i,z,h.trans (map_step t j i z eq)⟩
    · rintro ⟨i,z,rfl⟩
      obtain ⟨j,eq⟩ := (edge_arcs (arc i z)).mpr ⟨i,z,rfl⟩
      exact ⟨j,(map_step t j i z eq.symm).symm⟩
  have forward (t : Bool) (i : Fin m) (a b : Bool) :
      s(f (i,a),f (next i,b)) ∈ (c t).edges ↔ fits t i a b := by
    rw [form]
    constructor
    · rintro ⟨j,z,eq⟩
      rcases Sym2.eq_iff.mp eq with ⟨hx,hy⟩ | ⟨hx,hy⟩
      · have ij : i = j := congrArg Prod.fst (f.injective hx)
        subst j
        exact ⟨z,(congrArg Prod.snd (f.injective hx)).symm,(congrArg Prod.snd (f.injective hy)).symm⟩
      · have hij : i = next j := congrArg Prod.fst (f.injective hx)
        have hji : next i = j := congrArg Prod.fst (f.injective hy)
        exact False.elim (next_next_ne large i (hji ▸ hij.symm))
    · rintro ⟨z,h₁,h₂⟩
      exact ⟨i,z,by rw [h₁,h₂]⟩
  have one (i : Fin m) (a b : Bool) : ∃! t, s(f (i,a),f (next i,b)) ∈ (c t).edges := by
    obtain ⟨t,ht,only⟩ := unique_fit large i a b
    exact ⟨t,(forward t i a b).mpr ht, fun u hu => only u ((forward u i a b).mp hu)⟩
  refine ⟨c,cycleLength,?_,?_⟩
  · intro t x y mem
    obtain ⟨i,z,h⟩ := (form t _).mp mem
    rcases Sym2.eq_iff.mp h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp
  · intro x y
    obtain ⟨⟨i,a⟩,rfl⟩ := f.surjective x
    obtain ⟨⟨j,b⟩,rfl⟩ := f.surjective y
    simp only [Equiv.symm_apply_apply]
    rintro (rfl | rfl)
    · exact one i a b
    · rw [Sym2.eq_swap (a := f (next j,a)) (b := f (j,b))]
      exact one j b a


end AlspachLift

namespace AlspachLift
open Finset SimpleGraph AlspachConjecture
open scoped Classical

/-- Union of the two-cycle regions over the chosen base Hamilton cycles
and the one-square regions over every remaining base edge. -/
theorem glue_paired_regions {n m r : ℕ} (f : (Fin m × Bool) ≃ Fin n)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (adj : ∀ x y, G.Adj x y ↔ (f.symm x).1 ≠ (f.symm y).1)
    (S : Fin r → Finset (Sym2 (Fin m)))
    (contained : ∀ i, S i ⊆ (⊤ : SimpleGraph (Fin m)).edgeFinset)
    (hsize : ∀ i, (S i).card = m) (disj : Pairwise fun i j => Disjoint (S i) (S j))
    (lift : ∀ i, ∃ c : Bool → Cycle G, (∀ t, (c t).length = 2*m) ∧
      (∀ t x y, s(x,y) ∈ (c t).edges → s((f.symm x).1,(f.symm y).1) ∈ S i) ∧
      ∀ x y, s((f.symm x).1,(f.symm y).1) ∈ S i → ∃! t, s(x,y) ∈ (c t).edges) :
    ∃ C : Multiset (Cycle G), IsCycleDecomposition G C ∧
      lengths C = Multiset.replicate (2*r) (2*m) + Multiset.replicate (m.choose 2-r*m) 4 := by
  classical
  let π := fun x : Fin n => (f.symm x).1
  let E := (⊤ : SimpleGraph (Fin m)).edgeFinset
  let Covers (G : SimpleGraph (Fin n)) (π : (Fin n) → Fin m) (S : Finset (Sym2 (Fin m)))
      (L : Multiset ℕ) : Prop :=
    ∃ C : Multiset (Cycle G), lengths C = L ∧ ∀ x y : (Fin n),
      (C.filter fun c => s(x,y) ∈ c.edges).card = if s(π x,π y) ∈ S then 1 else 0

  have covers_empty (G : SimpleGraph (Fin n)) (π : (Fin n) → Fin m) : Covers G π ∅ 0 := by
    refine ⟨0, rfl, ?_⟩
    simp

  have covers_union {G : SimpleGraph (Fin n)} {π : (Fin n) → Fin m} {S T : Finset (Sym2 (Fin m))}
      {L M : Multiset ℕ} (hS : Covers G π S L) (hT : Covers G π T M) (hd : Disjoint S T) :
      Covers G π (S ∪ T) (L+M) := by
    obtain ⟨C,hC,hSc⟩ := hS
    obtain ⟨D,hD,hTc⟩ := hT
    refine ⟨C+D, ?_, ?_⟩
    · simpa only [lengths, Multiset.map_add] using congrArg₂ (· + ·) hC hD
    · intro x y
      rw [Multiset.filter_add, Multiset.card_add,hSc,hTc]
      by_cases hs : s(π x,π y) ∈ S
      · simp [hs, Finset.disjoint_left.mp hd hs]
      · simp [hs]


  have covers_many {ι : Type} [DecidableEq ι] {G : SimpleGraph (Fin n)} {π : (Fin n) → Fin m}
      (I : Finset ι) (S : ι → Finset (Sym2 (Fin m))) (L : ι → Multiset ℕ)
      (family : ∀ i ∈ I, Covers G π (S i) (L i))
      (disj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (S i) (S j)) :
      Covers G π (I.biUnion S) (∑ i ∈ I, L i) := by
    induction I using Finset.induction_on with
    | empty => simpa using covers_empty G π
    | @insert i I hi ih =>
      rw [biUnion_insert,sum_insert hi]
      apply covers_union (family i (mem_insert_self ..))
      · exact ih (fun j hj => family j (mem_insert_of_mem hj))
          (fun j hj k hk => disj j (mem_insert_of_mem hj) k (mem_insert_of_mem hk))
      · apply Finset.disjoint_left.mpr
        intro e he he'
        obtain ⟨j,hj,hej⟩ := mem_biUnion.mp he'
        exact Finset.disjoint_left.mp (disj i (mem_insert_self ..) j (mem_insert_of_mem hj)
          (fun h => hi (h ▸ hj))) he hej


  have covers_two {G : SimpleGraph (Fin n)} {π : (Fin n) → Fin m} {S : Finset (Sym2 (Fin m))} {l : ℕ}
      (c : Bool → Cycle G) (length : ∀ t, (c t).length = l)
      (only : ∀ t x y, s(x,y) ∈ (c t).edges → s(π x,π y) ∈ S)
      (one : ∀ x y, s(π x,π y) ∈ S → ∃! t, s(x,y) ∈ (c t).edges) :
      Covers G π S (Multiset.replicate 2 l) := by
    refine ⟨c false ::ₘ c true ::ₘ 0, ?_, ?_⟩
    · simp [lengths, length, Multiset.replicate_succ]
    · intro x y
      by_cases h : s(π x,π y) ∈ S
      · obtain ⟨t, ht, h_unique⟩ := one x y h
        cases t with
        | false =>
          have no : s(x,y) ∉ (c true).edges := fun h' => by simpa using h_unique true h'
          simp only [if_pos h, Multiset.filter_cons, if_pos ht, if_neg no, Multiset.filter_zero]
          simp
        | true =>
          have no : s(x,y) ∉ (c false).edges := fun h' => by simpa using h_unique false h'
          simp only [if_pos h, Multiset.filter_cons, if_pos ht, if_neg no, Multiset.filter_zero]
          simp
      · have no (t) : s(x,y) ∉ (c t).edges := fun e => h (only t _ _ e)
        simp [h,no]


  have covers_square {G : SimpleGraph (Fin n)} {π : (Fin n) → Fin m} {i j : Fin m}
      (square : ∃ c : Cycle G, c.length=4 ∧ ∀ x y, s(x,y) ∈ c.edges ↔
        (π x = i ∧ π y = j) ∨ (π x = j ∧ π y = i)) :
      Covers G π {s(i,j)} {4} := by
    obtain ⟨c,hl,he⟩ := square
    refine ⟨{c}, by simpa [lengths] using hl, ?_⟩
    intro x y
    by_cases h : s(π x,π y) = s(i,j)
    · change (Multiset.filter _ (c ::ₘ 0)).card = _
      simp only [Multiset.filter_cons, if_pos ((he x y).mpr (Sym2.eq_iff.mp h)), Multiset.filter_zero, mem_singleton, if_pos h]
      simp
    · have hn : s(x,y) ∉ c.edges := fun hs => h (Sym2.eq_iff.mpr ((he x y).mp hs))
      simp [hn,h]

  have lifted (i) : Covers G π (S i) (Multiset.replicate 2 (2*m)) := by
    obtain ⟨c,hl,only,one⟩ := lift i
    exact covers_two c hl only one
  have squares (e) (he : e ∈ E) : Covers G π {e} {4} := by
    induction e using Sym2.ind with
    | _ i j =>
      exact covers_square (AlspachSquares.square f G adj (SimpleGraph.mem_edgeFinset.mp he))
  let used := univ.biUnion S
  let unused := E \ used
  have hsub : used ⊆ E := by
    intro e he
    obtain ⟨i,_,hi⟩ := mem_biUnion.mp he
    exact contained i hi
  have hleft : Covers G π used (Multiset.replicate (2*r) (2*m)) := by
    have h := covers_many (univ : Finset (Fin r)) S (fun _ => Multiset.replicate 2 (2*m))
      (fun i _ => lifted i) (fun _ _ _ _ hij => disj hij)
    simpa only [used, sum_const, card_univ, Fintype.card_fin, Multiset.nsmul_replicate, Nat.mul_comm r 2] using h
  have hright : Covers G π unused (Multiset.replicate (m.choose 2-r*m) 4) := by
    have h := covers_many unused (fun e => {e}) (fun _ => ({4} : Multiset ℕ))
      (fun i hi => squares i (mem_sdiff.mp hi).1) (fun i _ j _ hij => by simpa using hij)
    have card : unused.card = m.choose 2-r*m := by
      change (E \ univ.biUnion S).card = _
      have hcard : E.card = m.choose 2 := by
        simpa [E] using SimpleGraph.card_edgeFinset_top_eq_card_choose_two (V := Fin m)
      rw [card_sdiff_of_subset hsub, hcard, card_biUnion (fun i _ j _ hij => disj hij)]
      simp [hsize]
    simpa [sum_const, card, Multiset.nsmul_singleton] using h
  have hdisj : Disjoint used unused := by
    exact Finset.disjoint_left.mpr (fun _ h h' => (mem_sdiff.mp h').2 h)
  obtain ⟨C,hL,hC⟩ := covers_union hleft hright hdisj
  refine ⟨C, ?_, hL⟩
  intro e
  induction e using Sym2.ind with
  | _ a b =>
    intro he
    have hadj : G.Adj a b := SimpleGraph.mem_edgeFinset.mp he
    have hbase : s(π a,π b) ∈ E := SimpleGraph.mem_edgeFinset.mpr ((adj a b).mp hadj)
    have hmem : s(π a,π b) ∈ used ∪ unused := by
      rw [mem_union]
      by_cases h : s(π a,π b) ∈ used
      · exact Or.inl h
      · exact Or.inr (mem_sdiff.mpr ⟨hbase,h⟩)
    simpa only [if_pos hmem] using hC a b


end AlspachLift

namespace AlspachPaired

/-- The blow-up has four edges per unordered base pair. -/
lemma paired_budget (m : ℕ) (hm : 0 < m) :
    (2*m).choose 2 - (2*m)/2 = 4 * m.choose 2 := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  have hbase := Nat.add_one_mul_choose_eq k 1
  simp only [Nat.choose_one_right, Nat.reduceAdd] at hbase
  have hlarge := Nat.add_one_mul_choose_eq (2*k+1) 1
  simp only [Nat.choose_one_right,Nat.reduceAdd] at hlarge
  have heq : 2*(k+1) = (2*k+1)+1 := by omega
  have hd : 2*(k+1)/2 = k+1 := Nat.mul_div_cancel_left _ (by decide)
  change (2*(k+1)).choose 2 - (2*(k+1))/2 = 4*(k+1).choose 2
  rw [hd,heq]
  have hrel : (2*k+1+1).choose 2 = 4*(k+1).choose 2 + (k+1) := by nlinarith
  omega

/-- For an admissible list using only squares and Hamilton cycles of a paired graph,
the number of pairs of Hamilton cycles determines the entire list. -/
theorem classify_paired_lengths_any {m : ℕ} (hm : 3 ≤ m) (L : Multiset ℕ)
    (shape : ∀ a ∈ L, a=4 ∨ a=2*m) (hc : Even (L.count (2*m)))
    (budget : L.sum = (2*m).choose 2 - (2*m)/2) :
    ∃ r, r ≤ (m-1)/2 ∧
      L = Multiset.replicate (2*r) (2*m) + Multiset.replicate (m.choose 2-r*m) 4 := by
  obtain ⟨r,hr⟩ := hc
  have hcount : L.count (2*m)=2*r := by omega
  have neq : 4 ≠ 2*m := by omega
  have filt : L.filter (fun a => ¬a=2*m) = Multiset.replicate (L.count 4) 4 := by
    rw [← Multiset.filter_eq']
    apply Multiset.filter_congr
    intro a ha
    rcases shape a ha with ha4 | haN
    · subst a; simp [neq]
    · subst a; simp [Ne.symm neq]
  have split : L = Multiset.replicate (2*r) (2*m) + Multiset.replicate (L.count 4) 4 := by
    have h := Multiset.filter_add_not (fun a => a=2*m) L
    rw [filt,Multiset.filter_eq',hcount] at h
    exact h.symm
  have total := congrArg Multiset.sum split
  rw [Multiset.sum_add,Multiset.sum_replicate,Multiset.sum_replicate,smul_eq_mul,smul_eq_mul,
    budget,paired_budget m (by omega)] at total
  have sum : m.choose 2 = r*m + L.count 4 := by nlinarith
  have base : 2*(m.choose 2) = m*(m-1) := by
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show m≠0 by omega)
    simpa [Nat.mul_comm] using (Nat.add_one_mul_choose_eq k 1).symm
  have mul : m*(2*r) ≤ m*(m-1) := by rw [← base,sum]; nlinarith
  have le := Nat.le_of_mul_le_mul_left mul (show 0< m by omega)
  refine ⟨r,by omega,?_⟩
  rw [sum, Nat.add_sub_cancel_left, ←split]

/-- At odd base order, the edge budget forces an even number of Hamilton cycles. -/
theorem even_hamilton_of_odd_base {m : ℕ} (hm : 3 ≤ m) (odd : Odd m) (L : Multiset ℕ)
    (shape : ∀ a ∈ L, a=4 ∨ a=2*m)
    (budget : L.sum = (2*m).choose 2 - (2*m)/2) : Even (L.count (2*m)) := by
  have neq : 4 ≠ 2*m := by omega
  have filt : L.filter (fun a => ¬a=2*m) = Multiset.replicate (L.count 4) 4 := by
    rw [← Multiset.filter_eq']
    apply Multiset.filter_congr
    intro a ha
    rcases shape a ha with ha4 | haN
    · subst a; simp [neq]
    · subst a; simp [Ne.symm neq]
  have split := Multiset.filter_add_not (fun a => a=2*m) L
  rw [filt,Multiset.filter_eq'] at split
  have total := congrArg Multiset.sum split
  rw [Multiset.sum_add,Multiset.sum_replicate,Multiset.sum_replicate,smul_eq_mul,smul_eq_mul,
    budget,paired_budget m (by omega)] at total
  obtain ⟨k,hk⟩ := odd
  have normal : L.count (2*m) * (2*m) = 4*(L.count (2*m)*k) + 2*L.count (2*m) := by
    conv_lhs => arg 2; rw [hk]
    ring
  rw [normal] at total
  exact ⟨L.count (2*m)/2,by omega⟩

end AlspachPaired

namespace AlspachPaired
open Finset SimpleGraph AlspachConjecture
open scoped Classical

/-- When the Hamilton count is even or the half-order is odd, every admissible list
supported on four and the full order is realized by the paired construction. -/
theorem paired_square_hamilton (n : ℕ) (even : Even n) (large : 6 ≤ n) (L : Multiset ℕ)
    (parity : Even (L.count n) ∨ Odd (n/2))
    (shape : ∀ a ∈ L, a=4 ∨ a=n) (budget : L.sum=n.choose 2-n/2) :
    ∃ J : (completeGraph (Fin n)).Subgraph, J.IsPerfectMatching ∧
      ∃ C : Multiset (Cycle (completeGraph (Fin n) \ J.spanningCoe)),
        IsCycleDecomposition _ C ∧ lengths C=L := by
  classical
  obtain ⟨m,hn⟩ : ∃ m, n=2*m := by obtain ⟨m,hm⟩ := even; exact ⟨m,by omega⟩
  subst n
  have hm : 3 ≤ m := by omega
  have countEven : Even (L.count (2*m)) := by
    rcases parity with h | h
    · exact h
    · apply even_hamilton_of_odd_base hm _ L shape budget
      simpa only [Nat.mul_div_cancel_left _ (by decide : 0 < 2)] using h
  obtain ⟨r,lim,lists⟩ := classify_paired_lengths_any hm L shape countEven budget
  let f : (Fin m × Bool) ≃ Fin (2*m) := Fintype.equivOfCardEq (by simp; omega)
  obtain ⟨J,hJ,adj⟩ := AlspachSquares.pair_matching f
  let G := completeGraph (Fin (2*m)) \ J.spanningCoe
  let next (a : Fin m) : Fin m := ⟨(a.val+1)%m, Nat.mod_lt _ (Nat.zero_lt_of_lt a.isLt)⟩
  let support (p : Fin m ≃ Fin m) := univ.image (fun a => s(p a,p (next a)))
  obtain ⟨p,hsub,hsize,hdisj⟩ := packed_base_family_of_limit hm lim
  have hnext (i : Fin m) : i ≠ next i := by
    intro h
    have hv := congrArg Fin.val h
    change i.val = (i.val+1)%m at hv
    have hi := i.isLt
    by_cases last : i.val+1=m
    · rw [last,Nat.mod_self] at hv
      omega
    · rw [Nat.mod_eq_of_lt (by omega)] at hv
      omega
  have support_iff (σ : Fin m ≃ Fin m) (i j : Fin m) :
      s(i,j) ∈ support σ ↔ next (σ.symm i) = σ.symm j ∨ next (σ.symm j) = σ.symm i := by
    constructor
    · intro h
      obtain ⟨a,_,eq⟩ := mem_image.mp h
      rcases Sym2.eq_iff.mp eq with ⟨hi,hj⟩ | ⟨hj,hi⟩
      · exact Or.inl (by simp [← hi,← hj])
      · exact Or.inr (by simp [← hi,← hj])
    · rintro (h|h)
      · refine mem_image.mpr ⟨σ.symm i,mem_univ _,?_⟩
        simp [h]
      · refine mem_image.mpr ⟨σ.symm j,mem_univ _,?_⟩
        simp [h,Sym2.eq_swap]
  have family (i : Fin r) : ∃ c : Bool → Cycle G, (∀ t, (c t).length=2*m) ∧
      (∀ t x y, s(x,y) ∈ (c t).edges → s((f.symm x).1,(f.symm y).1) ∈ support (p i)) ∧
      ∀ x y, s((f.symm x).1,(f.symm y).1) ∈ support (p i) → ∃! t, s(x,y) ∈ (c t).edges := by
    let g := (Equiv.prodCongr (p i) (Equiv.refl Bool)).trans f
    have hg (j : Fin m) (a b : Bool) : G.Adj (g (j,a)) (g (next j,b)) := by
      apply (adj _ _).mpr
      change (f.symm (f (p i j,a))).1 ≠ (f.symm (f (p i (next j),b))).1
      simpa only [Equiv.symm_apply_apply, ne_eq, EmbeddingLike.apply_eq_iff_eq] using hnext j
    obtain ⟨c,hlen,only,one⟩ := AlspachLift.liftPair_any hm g G next (fun _ => rfl) hg
    exact ⟨c,hlen,fun t x y he => (support_iff _ _ _).mpr (only t x y he),
      fun x y he => one x y ((support_iff _ _ _).mp he)⟩
  obtain ⟨C,hC,hlen⟩ := AlspachLift.glue_paired_regions f G adj (fun i => support (p i)) hsub hsize hdisj family
  exact ⟨J,hJ,C,hC,hlen.trans lists.symm⟩

end AlspachPaired


namespace AlspachRegions
open Finset SimpleGraph AlspachConjecture
open scoped Classical

/-- Disjoint row regions combine by adding cycle lengths. The indexed form
adds all cycle families over a finite set of pairwise disjoint regions. -/
theorem collect {V R : Type} [DecidableEq V] [DecidableEq R] (G : SimpleGraph V) (π : V → R) :
  let Covers (S : Finset (Sym2 R)) (L : Multiset ℕ) : Prop :=
    ∃ C : Multiset (Cycle G), lengths C = L ∧ ∀ x y : V,
      (C.filter fun c => s(x,y) ∈ c.edges).card = if s(π x,π y) ∈ S then 1 else 0
  (∀ {S T : Finset (Sym2 R)} {L M : Multiset ℕ}
      (_ : Covers S L) (_ : Covers T M) (_ : Disjoint S T), Covers (S ∪ T) (L+M)) ∧
  (∀ {ι : Type} [DecidableEq ι]
      (I : Finset ι) (S : ι → Finset (Sym2 R)) (L : ι → Multiset ℕ)
      (_ : ∀ i ∈ I, Covers (S i) (L i))
      (_ : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (S i) (S j)), Covers (I.biUnion S) (∑ i ∈ I, L i)) := by
  intro Covers
  have covers_union {S T : Finset (Sym2 R)} {L M : Multiset ℕ}
      (hS : Covers S L) (hT : Covers T M) (hd : Disjoint S T) : Covers (S ∪ T) (L+M) := by
    obtain ⟨C,hC,hSc⟩ := hS
    obtain ⟨D,hD,hTc⟩ := hT
    refine ⟨C+D, ?_, ?_⟩
    · simpa only [lengths,Multiset.map_add] using congrArg₂ (· + ·) hC hD
    · intro x y
      rw [Multiset.filter_add,Multiset.card_add,hSc,hTc]
      by_cases hs : s(π x,π y) ∈ S
      · simp [hs,Finset.disjoint_left.mp hd hs]
      · simp [hs]
  have covers_many {ι : Type} [DecidableEq ι]
      (I : Finset ι) (S : ι → Finset (Sym2 R)) (L : ι → Multiset ℕ)
      (family : ∀ i ∈ I, Covers (S i) (L i))
      (sep : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (S i) (S j)) :
      Covers (I.biUnion S) (∑ i ∈ I, L i) := by
    induction I using Finset.induction_on with
    | empty =>
      refine ⟨0,by simp [lengths],?_⟩
      simp
    | @insert i I hi ih =>
      rw [biUnion_insert,sum_insert hi]
      apply covers_union (family i (mem_insert_self ..))
      · exact ih (fun j hj => family j (mem_insert_of_mem hj))
          (fun j hj k hk => sep j (mem_insert_of_mem hj) k (mem_insert_of_mem hk))
      · apply Finset.disjoint_left.mpr
        intro e he he'
        obtain ⟨j,hj,hej⟩ := mem_biUnion.mp he'
        exact Finset.disjoint_left.mp (sep i (mem_insert_self ..) j (mem_insert_of_mem hj)
          (fun h => hi (h ▸ hj))) he hej
  exact ⟨fun hS hT hd => covers_union hS hT hd,fun I S L => covers_many I S L⟩

end AlspachRegions

namespace AlspachLadder
open SimpleGraph

/-- Running up the first rail, across the last rung, down the second rail and
across the first rung gives a `2*m`-cycle using exactly these edges. -/
theorem ladder_cycle {m : ℕ} {V : Type} (hm : 2 ≤ m) (f : (Fin m × Bool) ≃ V) (G : SimpleGraph V) :
    let E (u v : Fin m × Bool) : Prop :=
      (u.2 = v.2 ∧ (u.1.val+1 = v.1.val ∨ v.1.val+1 = u.1.val)) ∨
      (u.1 = v.1 ∧ u.2 ≠ v.2 ∧ (u.1.val = 0 ∨ u.1.val+1 = m))
    (∀ u v, E u v → G.Adj (f u) (f v)) → ∃ c : Cycle G, c.length = 2*m ∧
      ∀ u v, s(f u,f v) ∈ c.edges ↔ E u v := by
  intro E allowed
  let code (u : Fin m × Bool) : Fin (2*m) :=
    ⟨if u.2 then 2*m-1-u.1.val else u.1.val,by have := u.1.isLt; split <;> omega⟩
  let coord (t : Fin (2*m)) : Fin m × Bool := if h : t.val < m then (⟨t.val,h⟩,false)
    else (⟨2*m-1-t.val,by have := t.isLt; omega⟩,true)
  have ci (u : Fin m × Bool) : coord (code u) = u := by
    obtain ⟨i,b⟩ := u
    have hi := i.isLt
    cases b
    · simp [coord,code,hi]
    · have h : ¬2*m-1-i.val < m := by omega
      simp [coord,code,h,Fin.ext_iff]
      omega
  have ic (t : Fin (2*m)) : code (coord t) = t := by
    have ht := t.isLt
    apply Fin.ext
    dsimp [coord]
    split <;> simp [code]
    omega
  let eqv : Fin (2*m) ≃ Fin m × Bool := ⟨coord,code,ic,ci⟩
  let step (t : Fin (2*m)) : Fin (2*m) := ⟨(t.val+1)%(2*m),Nat.mod_lt _ (by omega)⟩
  let forward (u : Fin m × Bool) : Fin m × Bool :=
    if u.2 then
      if u.1.val = 0 then (u.1,false) else (⟨u.1.val-1,by have := u.1.isLt; omega⟩,true)
    else if h : u.1.val+1 < m then (⟨u.1.val+1,h⟩,false) else (u.1,true)
  have code_step (u : Fin m × Bool) : code (forward u) = step (code u) := by
    obtain ⟨i,b⟩ := u
    have hi := i.isLt
    cases b
    · by_cases h : i.val+1 < m
      · apply Fin.ext
        simp [code,forward,step,h,Nat.mod_eq_of_lt (show i.val+1<2*m by omega)]
      · apply Fin.ext
        simp [code,forward,step,h,Nat.mod_eq_of_lt (show i.val+1<2*m by omega)]
        omega
    · by_cases h : i.val=0
      · apply Fin.ext
        simp [code,forward,step,h,show 2*m-1+1=2*m by omega]
      · apply Fin.ext
        simp [code,forward,step,h,Nat.mod_eq_of_lt (show 2*m-1-i.val+1<2*m by omega)]
        omega
  have step_pair (t : Fin (2*m)) : eqv (step t) = forward (eqv t) := by
    change coord (step t) = forward (coord t)
    calc coord (step t) = coord (step (code (coord t))) := congrArg (fun z => coord (step z)) (ic t).symm
         _ = _ := by rw [← code_step,ci]
  have edges (u v : Fin m × Bool) : E u v ↔ forward u = v ∨ forward v = u := by
    obtain ⟨i,b⟩ := u
    obtain ⟨j,c⟩ := v
    have hi := i.isLt
    have hj := j.isLt
    cases b <;> cases c
    · by_cases a : i.val+1< m <;> by_cases b : j.val+1< m <;>
        simp [E,forward,a,b,Fin.ext_iff] <;> omega
    · by_cases a : i.val+1< m <;> by_cases b : j.val=0 <;>
        simp [E,forward,a,b,Fin.ext_iff] <;> omega
    · by_cases a : i.val=0 <;> by_cases b : j.val+1< m <;>
        simp [E,forward,a,b,Fin.ext_iff] <;> omega
    · by_cases a : i.val=0 <;> by_cases b : j.val=0 <;>
        simp [E,forward,a,b,Fin.ext_iff] <;> omega
  let listing := eqv.trans f
  have consecutive (t : Fin (2*m)) : G.Adj (listing t) (listing (step t)) := by
    apply allowed
    exact (edges _ _).mpr (Or.inl (step_pair t).symm)
  obtain ⟨cycle,hlen,precise⟩ := AlspachLift.cycleFromListing (by omega : 3 ≤ 2*m)
    listing.toEmbedding step (fun _ => rfl) consecutive
  refine ⟨cycle,hlen,fun u v => ?_⟩
  rw [precise,edges]
  constructor
  · rintro ⟨i,h⟩
    change s(f u,f v) = s(f (eqv i),f (eqv (step i))) at h
    rw [step_pair] at h
    rcases Sym2.eq_iff.mp h with ⟨a,b⟩ | ⟨a,b⟩
    · exact Or.inl ((congrArg forward (f.injective a)).trans (f.injective b).symm)
    · exact Or.inr ((congrArg forward (f.injective b)).trans (f.injective a).symm)
  · rintro (h | h)
    · refine ⟨eqv.symm u,?_⟩
      change _ = s(f (eqv (eqv.symm u)),f (eqv (step (eqv.symm u))))
      rw [step_pair,Equiv.apply_symm_apply,h]
    · refine ⟨eqv.symm v,?_⟩
      change _ = s(f (eqv (eqv.symm v)),f (eqv (step (eqv.symm v))))
      rw [step_pair,Equiv.apply_symm_apply,h]
      exact Sym2.eq_swap

end AlspachLadder

namespace AlspachLadder
open Finset SimpleGraph AlspachConjecture
open scoped Classical

/-- The spanning ladder and its inter-block squares partition the edges lying in one row or between consecutive rows. -/
theorem seed_family {m n : ℕ} (hm : 4≤ m) (even : Even m) (f : (Fin m × Bool) ≃ Fin n)
    (G : SimpleGraph (Fin n)) (adj : ∀ i a j b, G.Adj (f (i,a)) (f (j,b)) ↔
    (i≠j ∨ a≠b) ∧ ¬(((i.val%2=0 ∧ i.val+1=j.val) ∨ (j.val%2=0 ∧ j.val+1=i.val)) ∧ a≠b)) :
    ∃ (q : ℕ) (C : Multiset (Cycle G)), lengths C = {2*m}+Multiset.replicate q 4 ∧
      ∀ i a j b, G.Adj (f (i,a)) (f (j,b)) →
        (C.filter fun c => s(f (i,a),f (j,b)) ∈ c.edges).card =
          if i=j ∨ i.val+1=j.val ∨ j.val+1=i.val then 1 else 0 := by
  classical
  have band_square {m n : ℕ} (f : (Fin m × Bool) ≃ Fin n) (G : SimpleGraph (Fin n))
      (i j : Fin m) (different : i ≠ j)
      (available : ∀ x y : Fin m, (x=i ∨ x=j) → (y=i ∨ y=j) →
        G.Adj (f (x,false)) (f (y,true))) :
      ∃ c : Cycle G, c.length=4 ∧ ∀ x a y b,
        s(f (x,a),f (y,b)) ∈ c.edges ↔ (x=i ∨ x=j) ∧ (y=i ∨ y=j) ∧ a≠b := by
    let w : G.Walk (f (i,false)) (f (i,false)) :=
      .cons (available i i (Or.inl rfl) (Or.inl rfl))
      (.cons (available j i (Or.inr rfl) (Or.inl rfl)).symm
      (.cons (available j j (Or.inr rfl) (Or.inr rfl))
      (.cons (available i j (Or.inl rfl) (Or.inr rfl)).symm .nil)))
    have hc : w.IsCycle := by simp [w,Walk.isCycle_def,different,different.symm]
    refine ⟨⟨_,w,hc⟩,rfl,?_⟩
    intro x a y b
    change s(f (x,a),f (y,b)) ∈ [s(f (i,false),f (i,true)),s(f (i,true),f (j,false)),
      s(f (j,false),f (j,true)),s(f (j,true),f (i,false))] ↔ _
    cases a <;> cases b <;> simp <;> grind
  let Band (m : ℕ) := {t : Fin m // t.val%2=1 ∧ t.val+1< m}
  let bandNext {m : ℕ} (t : Band m) : Fin m := ⟨t.val.val+1,t.property.2⟩
  let InBand {m : ℕ} (t : Band m) (x : Fin m) : Prop := x=t.val ∨ x=bandNext t
  have inBand_iff {m} (t : Band m) (x : Fin m) :
      InBand t x ↔ x.val=t.val.val ∨ x.val=t.val.val+1 := by
    simp only [InBand,Fin.ext_iff,bandNext]
  have band_unique {m} (x : Fin m) (t u : Band m) (hx : InBand t x) (hy : InBand u x) :
      t=u := by
    have ht := t.property.1
    have hu := u.property.1
    rw [inBand_iff] at hx hy
    apply Subtype.ext
    apply Fin.ext
    omega
  have interior_band {m} (even : Even m) (x : Fin m) (interior : 0<x.val ∧ x.val+1< m) :
      ∃ t : Band m, InBand t x := by
    obtain ⟨k,hk⟩ := even
    by_cases odd : x.val%2=1
    · exact ⟨⟨x,odd,interior.2⟩,Or.inl rfl⟩
    · let p : Fin m := ⟨x.val-1, by have := x.isLt; omega⟩
      have hp : p.val%2=1 ∧ p.val+1< m := by dsimp [p]; omega
      exact ⟨⟨p,hp⟩,Or.inr (Fin.ext (by dsimp [bandNext,p]; omega))⟩
  let RowAdj {m} (i : Fin m) (a : Bool) (j : Fin m) (b : Bool) : Prop :=
    (i≠j ∨ a≠b) ∧ ¬(((i.val%2=0 ∧ i.val+1=j.val) ∨ (j.val%2=0 ∧ j.val+1=i.val)) ∧ a≠b)
  let Rail {m} (i : Fin m) (a : Bool) (j : Fin m) (b : Bool) : Prop :=
    (a=b ∧ (i.val+1=j.val ∨ j.val+1=i.val)) ∨ (a≠b ∧ i=j ∧ (i.val=0 ∨ i.val+1=m))
  let Strip {m} (t : Band m) (i : Fin m) (a : Bool) (j : Fin m) (b : Bool) : Prop :=
    InBand t i ∧ InBand t j ∧ a≠b
  have on_strip {m} (t : Band m) (x y : Fin m) (hx : InBand t x) (hy : InBand t y) :
      RowAdj x false y true := by
    have ht := t.property.1
    rw [inBand_iff] at hx hy
    refine ⟨Or.inr (by decide),?_⟩
    rintro ⟨(h | h),_⟩ <;> omega
  have interior_of_band {m} (even : Even m) (t : Band m) (x : Fin m) (hx : InBand t x) :
      0<x.val ∧ x.val+1< m := by
    obtain ⟨k,hk⟩ := even
    have ht := t.property
    rw [inBand_iff] at hx
    omega
  have rail_disjoint {m} (even : Even m) {i j : Fin m} {a b} (t : Band m)
      (rail : Rail i a j b) (strip : Strip t i a j b) : False := by
    have hi := interior_of_band even t i strip.1
    rcases rail with ⟨hab,_⟩ | ⟨_,_,cap⟩
    · exact strip.2.2 hab
    · omega
  have seed_on {m} (even : Even m) {i j : Fin m} {a b}
      (he : RowAdj i a j b) (localRow : i=j ∨ i.val+1=j.val ∨ j.val+1=i.val) :
      Rail i a j b ∨ ∃ t : Band m, Strip t i a j b := by
    rcases localRow with same | consecutive
    · subst j
      have hab : a≠b := he.1.resolve_left (by simp)
      by_cases cap : i.val=0 ∨ i.val+1=m
      · exact Or.inl (Or.inr ⟨hab,rfl,cap⟩)
      · obtain ⟨t,ht⟩ := interior_band even i (by have := i.isLt; omega)
        exact Or.inr ⟨t,ht,ht,hab⟩
    · by_cases hab : a=b
      · exact Or.inl (Or.inl ⟨hab,consecutive⟩)
      · apply Or.inr
        have bad := he.2
        rcases consecutive with h | h
        · have hi : i.val%2=1 := by
            by_contra hn
            exact bad ⟨Or.inl ⟨by omega,h⟩,hab⟩
          let t : Band m := ⟨i,hi,h ▸ j.isLt⟩
          exact ⟨t,Or.inl rfl,Or.inr (Fin.ext h.symm),hab⟩
        · have hj : j.val%2=1 := by
            by_contra hn
            exact bad ⟨Or.inr ⟨by omega,h⟩,hab⟩
          let t : Band m := ⟨j,hj,h ▸ i.isLt⟩
          exact ⟨t,Or.inr (Fin.ext h.symm),Or.inl rfl,hab⟩
  have local_of_seed {m} {i j : Fin m} {a b} :
      Rail i a j b ∨ (∃ t : Band m, Strip t i a j b) → i=j ∨ i.val+1=j.val ∨ j.val+1=i.val := by
    rintro ((⟨_,h⟩ | ⟨_,h,_⟩) | ⟨t,hi,hj,_⟩)
    · exact Or.inr h
    · exact Or.inl h
    · rw [inBand_iff] at hi hj
      rw [Fin.ext_iff]
      omega
  have count_family {α β : Type} [Fintype α] (f : α → β) (P : β → Prop) [DecidablePred P]
      (unique : ∀ i j, P (f i) → P (f j) → i=j) :
      ((univ.val.map f).filter P).card = if ∃ i, P (f i) then 1 else 0 := by
    classical
    rw [Multiset.filter_map, Multiset.card_map]
    by_cases h : ∃ i, P (f i)
    · obtain ⟨i,hi⟩ := h
      rw [if_pos ⟨i,hi⟩,Multiset.card_eq_one]
      refine ⟨i,?_⟩
      rw [Multiset.Nodup.ext (Multiset.Nodup.filter _ univ.nodup) (Multiset.nodup_singleton _)]
      intro j
      simp only [Multiset.mem_filter,Finset.mem_val,mem_univ,true_and,Multiset.mem_singleton,Function.comp]
      exact ⟨fun hj => unique j i hj hi,fun eq => eq ▸ hi⟩
    · rw [if_neg h,Multiset.card_eq_zero]
      apply Multiset.filter_eq_nil.mpr
      intro i _
      exact fun hi => h ⟨i,hi⟩
  have seed_family_of_cycle {m n : ℕ} (even : Even m) (f : (Fin m × Bool) ≃ Fin n)
      (G : SimpleGraph (Fin n)) (adj : ∀ i a j b, G.Adj (f (i,a)) (f (j,b)) ↔ RowAdj i a j b)
      (ladder : Cycle G) (size : ladder.length=2*m)
      (edges : ∀ i a j b, s(f (i,a),f (j,b)) ∈ ladder.edges ↔ Rail i a j b) :
      ∃ (q : ℕ) (C : Multiset (Cycle G)), lengths C = {2*m}+Multiset.replicate q 4 ∧
        ∀ i a j b, G.Adj (f (i,a)) (f (j,b)) →
          (C.filter fun c => s(f (i,a),f (j,b)) ∈ c.edges).card =
            if i=j ∨ i.val+1=j.val ∨ j.val+1=i.val then 1 else 0 := by
    classical
    have square (t : Band m) : ∃ c : Cycle G, c.length=4 ∧
        ∀ i a j b, s(f (i,a),f (j,b)) ∈ c.edges ↔ Strip t i a j b := by
      apply band_square f G t.val (bandNext t)
      · intro h
        have eq := congrArg Fin.val h
        change t.val.val=t.val.val+1 at eq
        omega
      · intro i j hi hj
        exact (adj _ _ _ _).mpr (on_strip t i j hi hj)
    choose c hlen hmem using square
    let squares := (univ : Finset (Band m)).val.map c
    have sizes : lengths squares = Multiset.replicate (Fintype.card (Band m)) 4 := by
      change ((univ.val.map c).map SimpleGraph.Cycle.length) = _
      rw [Multiset.map_map,show (SimpleGraph.Cycle.length ∘ c) = fun _ => 4 from funext hlen,Multiset.map_const']
      simp
    refine ⟨Fintype.card (Band m),ladder ::ₘ squares,?_,?_⟩
    · simpa only [lengths,Multiset.map_cons,size,Multiset.singleton_add] using congrArg (Multiset.cons (2*m)) sizes
    · intro i a j b he
      let e := s(f (i,a),f (j,b))
      have counted := count_family c (fun d : Cycle G => e∈d.edges) (by
        intro t u ht hu
        exact band_unique i t u ((hmem t i a j b).mp ht).1 ((hmem u i a j b).mp hu).1)
      have count : (squares.filter (fun d : Cycle G => e∈d.edges)).card =
          if ∃ t, Strip t i a j b then 1 else 0 := by
        rw [counted]
        apply if_congr _ rfl rfl
        exact exists_congr (fun t => hmem t i a j b)
      change (Multiset.filter (fun d : Cycle G => e∈d.edges) (ladder ::ₘ squares)).card=_
      rw [Multiset.filter_cons]
      by_cases rail : Rail i a j b
      · have yes : e∈ladder.edges := (edges i a j b).mpr rail
        have no : ¬∃ t, Strip t i a j b := fun ⟨t,ht⟩ => rail_disjoint even t rail ht
        rw [if_pos yes,Multiset.card_add,Multiset.card_singleton,count,if_neg no,if_pos (local_of_seed (Or.inl rail))]
      · have no : e∉ladder.edges := fun h => rail ((edges i a j b).mp h)
        rw [if_neg no,zero_add,count]
        apply if_congr _ rfl rfl
        exact ⟨fun h => local_of_seed (Or.inr h),
          fun h => (seed_on even ((adj i a j b).mp he) h).resolve_left rail⟩
  obtain ⟨c,length,edges⟩ := ladder_cycle (by omega : 2≤ m) f G (by
    rintro ⟨i,a⟩ ⟨j,b⟩ (⟨ab,h⟩ | ⟨ij,ab,_⟩)
    · apply (adj i a j b).mpr
      change a=b at ab
      refine ⟨Or.inl ?_,fun bad => bad.2 ab⟩
      intro heq
      subst j
      change i.val+1=i.val ∨ i.val+1=i.val at h
      omega
    · apply (adj i a j b).mpr
      change i=j at ij
      subst j
      refine ⟨Or.inr ab,?_⟩
      rintro ⟨(bad|bad),_⟩ <;> omega)
  apply seed_family_of_cycle even f G adj c length
  intro i a j b
  simpa only [Rail,and_left_comm,and_assoc] using edges (i,a) (j,b)

end AlspachLadder

namespace AlspachLadder
open SimpleGraph

/-- The 2m vertices are grouped into adjacent pairs of rows. Each vertex is
matched diagonally to the opposite Boolean label in the other row of its pair. -/
theorem matched_row_graph {m n : ℕ} (hm : Even m) (f : (Fin m × Bool) ≃ Fin n) :
    ∃ J : (completeGraph (Fin n)).Subgraph, J.IsPerfectMatching ∧
      ∀ (i : Fin m) (a : Bool) (j : Fin m) (b : Bool),
        (completeGraph (Fin n) \ J.spanningCoe).Adj (f (i,a)) (f (j,b)) ↔
          (i ≠ j ∨ a ≠ b) ∧ ¬(((i.val%2=0 ∧ i.val+1=j.val) ∨
            (j.val%2=0 ∧ j.val+1=i.val)) ∧ a ≠ b) := by
  obtain ⟨k,hk⟩ := hm
  let row (i : Fin m) : Fin m := ⟨if i.val%2=0 then i.val+1 else i.val-1,
    by have hi := i.isLt; split <;> omega⟩
  have row_inv (i : Fin m) : row (row i)=i := by
    apply Fin.ext
    simp only [row]
    split_ifs <;> omega
  have row_eq (i j : Fin m) : row i=j ↔
      (i.val%2=0 ∧ i.val+1=j.val) ∨ (j.val%2=0 ∧ j.val+1=i.val) := by
    rw [Fin.ext_iff]
    simp only [row]
    split_ifs <;> omega
  let mate (v : Fin m × Bool) := (row v.1, !v.2)
  have minv : Function.Involutive mate := by
    rintro ⟨i,b⟩
    simp [mate,row_inv]
  have mne (v : Fin m × Bool) : mate v≠v := by
    rintro h
    have hb : (!v.2)=v.2 := congrArg Prod.snd h
    cases v.2 <;> simp_all
  let paired (v : Fin n) := f (mate (f.symm v))
  have pinv (v : Fin n) : paired (paired v)=v := by
    simp only [paired,Equiv.symm_apply_apply,minv (f.symm v),Equiv.apply_symm_apply]
  have pne (v : Fin n) : paired v≠v := fun h => mne (f.symm v) (by simpa [paired] using congrArg f.symm h)
  let J : (completeGraph (Fin n)).Subgraph :=
    { verts := Set.univ
      Adj := fun x y => paired x=y
      adj_sub := fun h eq => pne _ (h.trans eq.symm)
      edge_vert := fun _ => Set.mem_univ _
      symm := ⟨fun x y h => by rw [←h,pinv]⟩ }
  have perfect : J.IsPerfectMatching := Subgraph.isPerfectMatching_iff.mpr
    (fun x => ⟨paired x,rfl,fun _ h => Eq.symm h⟩)
  refine ⟨J,perfect,?_⟩
  intro i a j b
  change f (i,a)≠f (j,b) ∧ ¬paired (f (i,a))=f (j,b) ↔ _
  have flip : (!a)=b ↔ a≠b := by cases a <;> cases b <;> decide
  simp only [ne_eq,paired,Equiv.symm_apply_apply,Equiv.apply_eq_iff_eq,mate,Prod.mk.injEq,
    row_eq,flip,not_and_or]


/-- A surjective labelling of precisely 2m vertices is automatically bijective. -/
theorem matched_row_graph_of_surjective {m n : ℕ} (hm : Even m) (hn : n=2*m) (f : Fin m × Bool → Fin n)
    (onto : Function.Surjective f) :
    ∃ J : (completeGraph (Fin n)).Subgraph, J.IsPerfectMatching ∧
      ∀ (i : Fin m) (a : Bool) (j : Fin m) (b : Bool),
        (completeGraph (Fin n) \ J.spanningCoe).Adj (f (i,a)) (f (j,b)) ↔
          (i ≠ j ∨ a ≠ b) ∧ ¬(((i.val%2=0 ∧ i.val+1=j.val) ∨
            (j.val%2=0 ∧ j.val+1=i.val)) ∧ a ≠ b) := by
  have size : Fintype.card (Fin m × Bool)=Fintype.card (Fin n) := by
    simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool]
    omega
  let e := Equiv.ofBijective f ((Fintype.bijective_iff_surjective_and_card f).mpr ⟨onto,size⟩)
  exact matched_row_graph hm e

end AlspachLadder

namespace AlspachPaired
open SimpleGraph Finset
open scoped Classical

/-- Reserve one Hamilton ordering and use its inverse to put the reserved cycle
in the standard order. The selected cycles then avoid every straight rail. -/
theorem path_avoiding_family {m r : ℕ} (even : Even m) (large : 4 ≤ m) (limit : r ≤ m/2-2) :
    let next (a : Fin m) : Fin m := ⟨(a.val+1)%m, Nat.mod_lt _ (Nat.zero_lt_of_lt a.isLt)⟩
    let support (p : Fin m ≃ Fin m) := univ.image (fun a => s(p a,p (next a)))
    ∃ p : Fin r → (Fin m ≃ Fin m),
      (∀ i, support (p i) ⊆ (⊤ : SimpleGraph (Fin m)).edgeFinset) ∧
      (∀ i, (support (p i)).card=m) ∧
      (Pairwise fun i j => Disjoint (support (p i)) (support (p j))) ∧
      ∀ i, Disjoint (support (p i)) (support (Equiv.refl (Fin m))) := by
  classical
  intro next support
  obtain ⟨p,contained,size,hdis⟩ := packed_base_family (r := r+1) even large (by omega)
  let z := p (Fin.last r)
  let move : Sym2 (Fin m) ↪ Sym2 (Fin m) := ⟨Sym2.map z.symm,Sym2.map.injective z.symm.injective⟩
  let g (i : Fin r) := (p i.castSucc).trans z.symm
  have mapped (q : Fin m ≃ Fin m) : support (q.trans z.symm) = (support q).map move := by
    simp [support, map_eq_image, image_image, Function.comp_def, move]
  have hm (i : Fin r) : support (g i) = (support (p i.castSucc)).map move := mapped _
  have hz : support (Equiv.refl (Fin m)) = (support z).map move := by simpa using mapped z
  refine ⟨g,?_,?_,?_,?_⟩
  · intro i e he
    obtain ⟨a,_,rfl⟩ := mem_image.mp he
    apply SimpleGraph.mem_edgeFinset.mpr
    change g i a ≠ g i (next a)
    intro eq
    have orig := SimpleGraph.mem_edgeFinset.mp (contained i.castSucc
      (mem_image.mpr ⟨a,mem_univ _,rfl⟩))
    apply orig
    exact congrArg (p i.castSucc) ((g i).injective eq)
  · intro i
    rw [hm,card_map]
    exact size _
  · intro i j hij
    rw [hm,hm]
    exact (disjoint_map move).2 (hdis (fun e => hij (Fin.ext (congrArg (fun a : Fin (r+1) => a.val) e))))
  · intro i
    rw [hm,hz]
    exact (disjoint_map move).2 (hdis (Fin.castSucc_ne_last i))

end AlspachPaired

namespace AlspachLadder
open SimpleGraph Finset AlspachConjecture
open scoped Classical

/-- Two Hamilton cycles use all four lifted edges above each edge in the base listing. -/
theorem hamilton_region {n m : ℕ} (hm : 3 ≤ m) (f : (Fin m × Bool) ≃ Fin n)
    (G : SimpleGraph (Fin n)) (σ : Fin m ≃ Fin m) :
    let next (i : Fin m) : Fin m := ⟨(i.val+1)%m, Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩
    let baseSupport := univ.image (fun i => s(σ i,σ (next i)))
    (∀ i a b, G.Adj (f (σ i,a)) (f (σ (next i),b))) →
    ∃ C : Multiset (Cycle G), lengths C = Multiset.replicate 2 (2*m) ∧ ∀ x y : Fin n,
      (C.filter fun c => s(x,y) ∈ c.edges).card =
        if s((f.symm x).1,(f.symm y).1) ∈ baseSupport then 1 else 0 := by
  intro next baseSupport adj
  let g := (Equiv.prodCongr σ (Equiv.refl Bool)).trans f
  obtain ⟨c,len,only,one⟩ := AlspachLift.liftPair_any hm g G next (fun _ => rfl) adj
  have support (i j : Fin m) : s(i,j) ∈ baseSupport ↔
      next (σ.symm i) = σ.symm j ∨ next (σ.symm j) = σ.symm i := by
    constructor
    · intro h
      obtain ⟨a,_,eq⟩ := mem_image.mp h
      rcases Sym2.eq_iff.mp eq with ⟨hi,hj⟩ | ⟨hj,hi⟩
      · exact Or.inl (by simp [← hi,← hj])
      · exact Or.inr (by simp [← hi,← hj])
    · rintro (h|h)
      · refine mem_image.mpr ⟨σ.symm i,mem_univ _,?_⟩
        simp [h]
      · refine mem_image.mpr ⟨σ.symm j,mem_univ _,?_⟩
        simp [h,Sym2.eq_swap]
  refine ⟨c false ::ₘ c true ::ₘ 0, by simp [lengths,len,Multiset.replicate_succ],?_⟩
  intro x y
  by_cases h : s((f.symm x).1,(f.symm y).1) ∈ baseSupport
  · obtain ⟨t,ht,unique⟩ := one x y ((support _ _).mp h)
    cases t with
    | false =>
      have hn : s(x,y) ∉ (c true).edges := fun ht' => by simpa using unique true ht'
      simp only [if_pos h,Multiset.filter_cons,if_pos ht,if_neg hn,Multiset.filter_zero]
      simp
    | true =>
      have hn : s(x,y) ∉ (c false).edges := fun ht' => by simpa using unique false ht'
      simp only [if_pos h,Multiset.filter_cons,if_pos ht,if_neg hn,Multiset.filter_zero]
      simp
  · have hn (t : Bool) : s(x,y) ∉ (c t).edges := fun ht => h ((support _ _).mpr (only t x y ht))
    simp [h,hn]

/-- The four edges between two doubled labels form a square. -/
theorem square_region {n m : ℕ} (f : (Fin m × Bool) ≃ Fin n) (G : SimpleGraph (Fin n))
    {i j : Fin m} (diff : i ≠ j) (adj : ∀ a b, G.Adj (f (i,a)) (f (j,b))) :
    ∃ C : Multiset (Cycle G), lengths C = {4} ∧ ∀ x y : Fin n,
      (C.filter fun c => s(x,y) ∈ c.edges).card =
        if s((f.symm x).1,(f.symm y).1) ∈ ({s(i,j)} : Finset _) then 1 else 0 := by
  let w : G.Walk (f (i,false)) (f (i,false)) :=
    .cons (adj false false) (.cons (adj true false).symm
      (.cons (adj true true) (.cons (adj false true).symm .nil)))
  have cycle : w.IsCycle := by simp [w,Walk.isCycle_def,diff,diff.symm]
  let c : Cycle G := ⟨_,w,cycle⟩
  have mem (x y : Fin n) : s(x,y) ∈ c.edges ↔ s((f.symm x).1,(f.symm y).1) = s(i,j) := by
    obtain ⟨⟨r,a⟩,rfl⟩ := f.surjective x
    obtain ⟨⟨s,b⟩,rfl⟩ := f.surjective y
    change s(f (r,a), f (s,b)) ∈ [s(f (i,false), f (j,false)), s(f (j,false), f (i,true)),
      s(f (i,true), f (j,true)), s(f (j,true), f (i,false))] ↔ _
    rw [Sym2.eq_iff]
    cases a <;> cases b <;> simp
    grind
  refine ⟨{c},rfl,?_⟩
  intro x y
  change (Multiset.filter _ (c ::ₘ 0)).card = _
  simp only [Multiset.filter_cons,Multiset.filter_zero,Finset.mem_singleton,mem]
  split <;> simp_all
end AlspachLadder

namespace AlspachLadder
open Finset SimpleGraph AlspachConjecture
open scoped Classical

/-- The selected Hamilton lifts and the remaining squares cover precisely the edges
between distinct, nonconsecutive rows in the linear order. -/
theorem off_path_region {m n r : ℕ} (large : 3 ≤ m) (f : (Fin m × Bool) ≃ Fin n)
    (G : SimpleGraph (Fin n)) (σ : Fin r → (Fin m ≃ Fin m)) :
    let next (a : Fin m) : Fin m := ⟨(a.val+1)%m, Nat.mod_lt _ (Nat.zero_lt_of_lt a.isLt)⟩
    let support (p : Fin m ≃ Fin m) := univ.image (fun a => s(p a,p (next a)))
    (Pairwise fun i j => Disjoint (support (σ i)) (support (σ j))) →
    (∀ i, Disjoint (support (σ i)) (support (Equiv.refl _))) →
    (∀ (i j : Fin m), i≠j → i.val+1≠j.val → j.val+1≠i.val →
      ∀ a b, G.Adj (f (i,a)) (f (j,b))) →
    ∃ (q : ℕ) (cs : Multiset (Cycle G)),
      lengths cs = Multiset.replicate (2*r) (2*m) + Multiset.replicate q 4 ∧
      ∀ (i : Fin m) (a : Bool) (j : Fin m) (b : Bool),
        (cs.filter fun c => s(f (i,a),f (j,b)) ∈ c.edges).card =
        if i=j ∨ i.val+1=j.val ∨ j.val+1=i.val then 0 else 1 := by
  intro next support disj avoid across
  let π := fun x : Fin n => (f.symm x).1
  let Covers (S : Finset (Sym2 (Fin m))) (L : Multiset ℕ) : Prop :=
    ∃ C : Multiset (Cycle G), lengths C = L ∧ ∀ x y : Fin n,
      (C.filter fun c => s(x,y) ∈ c.edges).card = if s(π x,π y) ∈ S then 1 else 0
  obtain ⟨covers_union,covers_many⟩ := AlspachRegions.collect G π
  let A := (⊤ : SimpleGraph (Fin m)).edgeFinset.filter (fun e =>
    ¬∃ i j : Fin m, i.val+1=j.val ∧ e=s(i,j))
  have mem (i j : Fin m) : s(i,j) ∈ A ↔ i≠j ∧ i.val+1≠j.val ∧ j.val+1≠i.val := by
    rw [show A=(⊤ : SimpleGraph (Fin m)).edgeFinset.filter _ by rfl,mem_filter]
    have inBase : s(i,j) ∈ (⊤ : SimpleGraph (Fin m)).edgeFinset ↔ i≠j := SimpleGraph.mem_edgeFinset
    rw [inBase]
    constructor
    · rintro ⟨ne,none⟩
      exact ⟨ne,fun h => none ⟨i,j,h,rfl⟩,fun h => none ⟨j,i,h,Sym2.eq_swap⟩⟩
    · rintro ⟨ne,fwd,bwd⟩
      refine ⟨ne,?_⟩
      rintro ⟨u,v,step,eq⟩
      rcases Sym2.eq_iff.mp eq with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
      · exact fwd step
      · exact bwd step
  have sub (t : Fin r) : support (σ t) ⊆ A := by
    intro e he
    apply mem_filter.mpr
    constructor
    · obtain ⟨v,_,rfl⟩ := mem_image.mp he
      apply SimpleGraph.mem_edgeFinset.mpr
      intro eq
      have val := congrArg Fin.val ((σ t).injective eq)
      change v.val=(v.val+1)%m at val
      have hv := v.isLt
      by_cases last : v.val+1=m
      · rw [last,Nat.mod_self] at val
        omega
      · rw [Nat.mod_eq_of_lt (by omega)] at val
        omega
    · rintro ⟨i,j,h,rfl⟩
      apply Finset.disjoint_left.mp (avoid t) he
      have nx : next i = j := Fin.ext (show (i.val+1)%m=j.val by rw [h,Nat.mod_eq_of_lt j.isLt])
      exact mem_image.mpr ⟨i,mem_univ i,by change s(i,next i)=s(i,j); rw [nx]⟩
  let S := fun t => support (σ t)
  let used := univ.biUnion S
  let unused := A \ used
  have contained : used ⊆ A := biUnion_subset.mpr (fun t _ => sub t)
  have paired (t : Fin r) : Covers (S t) (Multiset.replicate 2 (2*m)) := by
    apply hamilton_region large f G (σ t)
    intro i a b
    have h := (mem _ _).mp (sub t (mem_image.mpr ⟨i,mem_univ i,rfl⟩))
    exact across _ _ h.1 h.2.1 h.2.2 a b
  have square (e : Sym2 (Fin m)) (he : e ∈ unused) : Covers {e} {4} := by
    induction e using Sym2.ind with
    | _ i j =>
      obtain ⟨ne,fwd,bwd⟩ := (mem i j).mp (mem_sdiff.mp he).1
      exact square_region f G ne (across i j ne fwd bwd)
  have left : Covers used (Multiset.replicate (2*r) (2*m)) := by
    have h := covers_many univ S (fun _ => Multiset.replicate 2 (2*m))
      (fun i _ => paired i) (fun _ _ _ _ hij => disj hij)
    simpa only [used,sum_const,card_univ,Fintype.card_fin,Multiset.nsmul_replicate,Nat.mul_comm r 2] using h
  have right : Covers unused (Multiset.replicate unused.card 4) := by
    have h := covers_many unused (fun e => {e}) (fun _ => ({4} : Multiset ℕ))
      square (fun i _ j _ ne => by simpa using ne)
    simpa [sum_const,Multiset.nsmul_singleton] using h
  have dj : Disjoint used unused := Finset.disjoint_left.mpr fun _ h h' => (mem_sdiff.mp h').2 h
  have union : used ∪ unused = A := Finset.union_sdiff_of_subset contained
  obtain ⟨cs,len,coverage⟩ := covers_union left right dj
  refine ⟨unused.card,cs,len,?_⟩
  intro i a j b
  have h := coverage (f (i,a)) (f (j,b))
  simp only [π,Equiv.symm_apply_apply,union,mem] at h
  rw [h]
  by_cases onPath : i=j ∨ i.val+1=j.val ∨ j.val+1=i.val
  · simp [onPath,show ¬(i≠j ∧ i.val+1≠j.val ∧ j.val+1≠i.val) by tauto]
  · simp [show i≠j ∧ i.val+1≠j.val ∧ j.val+1≠i.val by tauto]
/-- One ladder cycle covers the rails and caps. Its accompanying band squares
and the two-cycle lifts cover disjoint complementary parts of the row graph. -/
theorem odd_row_decomposition {m n r : ℕ} (large : 4≤ m) (even : Even m) (limit : r≤ m/2-2)
    (f : (Fin m × Bool) ≃ Fin n) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (adj : ∀ i a j b, G.Adj (f (i,a)) (f (j,b)) ↔
      (i≠j ∨ a≠b) ∧ ¬(((i.val%2=0 ∧ i.val+1=j.val) ∨ (j.val%2=0 ∧ j.val+1=i.val)) ∧ a≠b)) :
    ∃ (q : ℕ) (C : Multiset (Cycle G)), IsCycleDecomposition G C ∧
      lengths C=Multiset.replicate (2*r+1) (2*m) + Multiset.replicate q 4 := by
  classical
  obtain ⟨σ,_,_,disj,avoid⟩ := AlspachPaired.path_avoiding_family (r:=r) even large limit
  obtain ⟨q₁,S,ls,seed⟩ := seed_family large even f G adj
  obtain ⟨q₂,T,lt,away⟩ := off_path_region (by omega : 3≤ m) f G σ disj avoid
    (fun i j ne fwd bwd a b => (adj i a j b).mpr ⟨Or.inl ne,fun ⟨band,_⟩ =>
      band.elim (fun h => fwd h.2) (fun h => bwd h.2)⟩)
  refine ⟨q₁+q₂,S+T,?_,?_⟩
  · intro e
    induction e using Sym2.ind with
    | _ x y =>
      obtain ⟨⟨i,a⟩,rfl⟩ := f.surjective x
      obtain ⟨⟨j,b⟩,rfl⟩ := f.surjective y
      intro he
      have hs := seed i a j b (G.mem_edgeFinset.mp he)
      have ht := away i a j b
      rw [Multiset.filter_add,Multiset.card_add,hs,ht]
      split <;> rfl
  · change (S+T).map SimpleGraph.Cycle.length=_
    rw [Multiset.map_add]
    change lengths S + lengths T = _
    rw [ls,lt,Multiset.replicate_add (2*r) 1,Multiset.replicate_add q₁ q₂,Multiset.replicate_one]
    ac_rfl

/-- Choose the diagonal matching and decompose its complement into an odd
number of Hamilton cycles and squares. -/
theorem odd_hamilton_and_squares {m n r : ℕ} (large : 4≤ m) (even : Even m) (limit : r≤ m/2-2)
    (f : (Fin m × Bool) ≃ Fin n) :
    ∃ J : (completeGraph (Fin n)).Subgraph, J.IsPerfectMatching ∧
      ∃ (q : ℕ) (C : Multiset (Cycle (completeGraph (Fin n) \ J.spanningCoe))),
        IsCycleDecomposition _ C ∧ lengths C=Multiset.replicate (2*r+1) (2*m) + Multiset.replicate q 4 := by
  classical
  obtain ⟨J,hJ,adj⟩ := matched_row_graph even f
  exact ⟨J,hJ,odd_row_decomposition large even limit f _ adj⟩

end AlspachLadder

namespace AlspachLadder
open SimpleGraph Finset AlspachConjecture
open scoped Classical

/-- Summing the length of each cycle counts the same incidences as summing the
number of covering cycles at each edge. A decomposition counts every edge once. -/
theorem decomposition_budget {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (C : Multiset (Cycle G))
    (h : IsCycleDecomposition G C) : (lengths C).sum=G.edgeFinset.card := by
  classical
  have per_cycle (c : Cycle G) :
      (∑ e ∈ G.edgeFinset, if e∈c.edges then 1 else 0) = c.length := by
    have eq : G.edgeFinset.filter (fun e => e∈c.edges) = c.edges.toFinset := by
      ext e
      simp only [mem_filter,List.mem_toFinset,and_iff_right_iff_imp]
      exact fun he => G.mem_edgeFinset.mpr (Walk.edges_subset_edgeSet c.walk he)
    rw [← sum_filter,eq]
    simp only [sum_const,smul_eq_mul,mul_one,List.toFinset_card_of_nodup c.isCycle.edges_nodup,
      Cycle.edges,Walk.length_edges]
    rfl
  have count (D : Multiset (Cycle G)) : (lengths D).sum =
      ∑ e ∈ G.edgeFinset, (D.filter (fun c => e∈c.edges)).card := by
    induction D using Multiset.induction with
    | empty => simp [lengths]
    | cons c D ih =>
      have cons (e : Sym2 V) : ((c ::ₘ D).filter (fun v => e∈v.edges)).card =
          (if e∈c.edges then 1 else 0) + (D.filter (fun v => e∈v.edges)).card := by
        by_cases he : e∈c.edges <;> simp [he,add_comm]
      simp only [lengths,Multiset.map_cons,Multiset.sum_cons] at ih ⊢
      rw [ih]
      simp only [cons,sum_add_distrib,per_cycle]
  rw [count]
  calc
    _ = ∑ _e ∈ G.edgeFinset, 1 := sum_congr rfl h
    _ = _ := by simp

end AlspachLadder

namespace AlspachLadder
open SimpleGraph AlspachConjecture
open scoped Classical

/-- The two allowed lengths partition the list into copies of each value. -/
theorem square_hamilton_counts {m : ℕ} (hm : 3 ≤ m) (L : Multiset ℕ)
    (shape : ∀ a ∈ L, a=4 ∨ a=2*m) :
    L = Multiset.replicate (L.count (2*m)) (2*m) + Multiset.replicate (L.count 4) 4 := by
  have neq : 4 ≠ 2*m := by omega
  have filt : L.filter (fun a => ¬a=2*m) = Multiset.replicate (L.count 4) 4 := by
    rw [← Multiset.filter_eq']
    apply Multiset.filter_congr
    intro a ha
    rcases shape a ha with h4 | hN
    · subst a; simp [neq]
    · subst a; simp [Ne.symm neq]
  have h := Multiset.filter_add_not (fun a => a=2*m) L
  rw [filt,Multiset.filter_eq'] at h
  exact h.symm

/-- A square leaves room for strictly fewer than m−1 Hamilton cycles. When
m is even and their count is odd, at most m/2−2 additional pairs remain. -/
theorem classify_odd_lengths {m : ℕ} (hm : 4 ≤ m) (even : Even m) (L : Multiset ℕ)
    (shape : ∀ a ∈ L, a=4 ∨ a=2*m) (odd : Odd (L.count (2*m))) (four : 4 ∈ L)
    (budget : L.sum = (2*m).choose 2 - (2*m)/2) :
    ∃ r, r ≤ m/2-2 ∧ L.count (2*m) = 2*r+1 := by
  have total := congrArg Multiset.sum (square_hamilton_counts (by omega) L shape)
  have edgeBudget := AlspachEvenHamilton.even_budget (m-1)
  rw [show 2*(m-1)+2=2*m by omega] at edgeBudget
  rw [budget,edgeBudget,Multiset.sum_add,Multiset.sum_replicate,Multiset.sum_replicate,
    smul_eq_mul,smul_eq_mul] at total
  have sq : 0 < L.count 4 := Multiset.count_pos.mpr four
  have strict : L.count (2*m) * (2*m) < (m-1) * (2*m) := by omega
  have hlt : L.count (2*m) < m-1 := Nat.lt_of_mul_lt_mul_right strict
  obtain ⟨r,hr⟩ := odd
  obtain ⟨k,hk⟩ := even
  exact ⟨r,by omega,by omega⟩

/-- Once the Hamilton count is prescribed, equality of total lengths forces
all remaining square multiplicities as well. -/
theorem ladder_lengths_eq {m r q : ℕ} (hm : 3 ≤ m) (L : Multiset ℕ)
    (shape : ∀ a ∈ L, a=4 ∨ a=2*m) (hc : L.count (2*m) = 2*r+1)
    (hs : (Multiset.replicate (2*r+1) (2*m) + Multiset.replicate q 4).sum = L.sum) :
    Multiset.replicate (2*r+1) (2*m) + Multiset.replicate q 4 = L := by
  have split := square_hamilton_counts hm L shape
  rw [hc] at split
  rw [split] at hs
  simp only [Multiset.sum_add,Multiset.sum_replicate,smul_eq_mul] at hs
  exact (congrArg (fun k => Multiset.replicate (2*r+1) (2*m) + Multiset.replicate k 4)
    (show q=L.count 4 by omega)).trans split.symm

/-- The mixed odd-count construction and Walecki's uniform construction together
realize every admissible square/Hamilton list with an odd Hamilton count. -/
theorem realize_odd_lengths {m : ℕ} (hm : 4 ≤ m) (even : Even m) (L : Multiset ℕ)
    (shape : ∀ a ∈ L, a=4 ∨ a=2*m) (odd : Odd (L.count (2*m)))
    (budget : L.sum = (2*m).choose 2 - (2*m)/2)
    (build : ∀ r ≤ m/2-2, ∃ J : (completeGraph (Fin (2*m))).Subgraph, J.IsPerfectMatching ∧
      ∃ (q : ℕ) (C : Multiset (Cycle (completeGraph (Fin (2*m)) \ J.spanningCoe))),
        IsCycleDecomposition _ C ∧ lengths C = Multiset.replicate (2*r+1) (2*m) + Multiset.replicate q 4) :
    ∃ J : (completeGraph (Fin (2*m))).Subgraph, J.IsPerfectMatching ∧
      ∃ C : Multiset (Cycle (completeGraph (Fin (2*m)) \ J.spanningCoe)),
        IsCycleDecomposition _ C ∧ lengths C=L := by
  classical
  by_cases square : 4 ∈ L
  · obtain ⟨r,lim,hc⟩ := classify_odd_lengths hm even L shape odd square budget
    obtain ⟨J,hJ,q,C,hC,hsize⟩ := build r lim
    refine ⟨J,hJ,C,hC,hsize.trans (ladder_lengths_eq (by omega) L shape hc ?_)⟩
    rw [← hsize,decomposition_budget C hC,budget]
    have cnt := TriangleBridge.matching_budget J hJ
    rw [Fintype.card_fin] at cnt
    convert cnt using 1
    congr 1
    ext e
    simp only [mem_edgeFinset]
  · apply EvenWalecki.all_hamilton (2*m) ⟨m,by omega⟩ (by omega) L _ budget
    intro a ha
    exact (shape a ha).resolve_left (fun eq => square (eq ▸ ha))

end AlspachLadder

namespace AlspachPaired
open Finset SimpleGraph AlspachConjecture
open scoped Classical

/-- On an even number of pairs, one ladder Hamilton cycle and paired Hamilton
lifts realize the remaining odd Hamilton counts. -/
theorem remaining_odd_hamilton (n : ℕ) (even : Even n) (large : 6 ≤ n) (L : Multiset ℕ)
    (baseEven : Even (n/2)) (countOdd : Odd (L.count n)) (shape : ∀ a ∈ L, a=4 ∨ a=n)
    (budget : L.sum=n.choose 2-n/2) :
    ∃ J : (completeGraph (Fin n)).Subgraph, J.IsPerfectMatching ∧
      ∃ C : Multiset (Cycle (completeGraph (Fin n) \ J.spanningCoe)),
        IsCycleDecomposition _ C ∧ lengths C=L := by
  classical
  obtain ⟨m,hn⟩ : ∃ m, n=2*m := by obtain ⟨m,hm⟩ := even; exact ⟨m,by omega⟩
  subst n
  have hmEven : Even m := by simpa only [Nat.mul_div_cancel_left _ (by decide : 0 < 2)] using baseEven
  have hm : 4 ≤ m := by obtain ⟨k,hk⟩ := hmEven; omega
  let f : (Fin m × Bool) ≃ Fin (2*m) := Fintype.equivOfCardEq (by simp; omega)
  apply AlspachLadder.realize_odd_lengths hm hmEven L shape countOdd budget
  exact fun _ lim => AlspachLadder.odd_hamilton_and_squares hm hmEven lim f

/-- The two-length case can choose its perfect matching; this also covers small even orders. -/
theorem realize_square_hamilton (n : ℕ) (even : Even n) (L : Multiset ℕ)
    (lower : ∀ a ∈ L, 3 ≤ a) (shape : ∀ a ∈ L, a=4 ∨ a=n)
    (budget : L.sum=n.choose 2-n/2) :
    ∃ J : (completeGraph (Fin n)).Subgraph, J.IsPerfectMatching ∧
      ∃ C : Multiset (Cycle (completeGraph (Fin n) \ J.spanningCoe)),
        IsCycleDecomposition _ C ∧ lengths C=L := by
  by_cases large : 6 ≤ n
  · by_cases parity : Even (L.count n) ∨ Odd (n/2)
    · exact paired_square_hamilton n even large L parity shape budget
    · exact remaining_odd_hamilton n even large L
        (Nat.not_odd_iff_even.mp (fun h => parity (Or.inr h)))
        (Nat.not_even_iff_odd.mp (fun h => parity (Or.inl h))) shape budget
  · apply AlspachSquares.all_fours n even L _ budget
    intro a ha
    rcases shape a ha with h | rfl
    · exact h
    · have h := lower a ha
      obtain ⟨k,hk⟩ := even
      omega

/-- In every even complete graph with a prescribed perfect matching removed,
every admissible list supported on squares and Hamilton cycles is realized. -/
theorem all_square_hamilton (n : ℕ) (even : Even n) (I : (completeGraph (Fin n)).Subgraph)
    (hI : I.IsPerfectMatching) (L : Multiset ℕ) (lower : ∀ a ∈ L, 3 ≤ a)
    (shape : ∀ a ∈ L, a=4 ∨ a=n) (budget : L.sum=n.choose 2-n/2) :
    ∃ C : Multiset (Cycle (completeGraph (Fin n) \ I.spanningCoe)),
      IsCycleDecomposition _ C ∧ lengths C=L := by
  obtain ⟨J,hJ,C,dec,length⟩ := realize_square_hamilton n even L lower shape budget
  obtain ⟨f⟩ := OMA.R_AlspachConjecture_alspach_conjecture_variants_even_R2.matchings_complements_iso J I hJ hI
  exact OMA.R_AlspachConjecture_alspach_conjecture_variants_even_R2.iso_decomposition f dec length

end AlspachPaired

namespace AlspachLift
open SimpleGraph Finset AlspachConjecture
open scoped Classical

/-- The four choices of two bits yield four triangles in a doubled triple of
rows. Each pair of row labels determines the two freely chosen bits. -/
theorem triangle_pair_region {V : Type*} [DecidableEq V] {m : ℕ} (f : (Fin m × Bool) ≃ V)
    (G : SimpleGraph V) (adj : ∀ i a j b, i ≠ j → G.Adj (f (i,a)) (f (j,b)))
    (i j k : Fin m) (hij : i≠j) (hik : i≠k) (hjk : j≠k) :
    ∃ C : Multiset (Cycle G), lengths C=Multiset.replicate 4 3 ∧ ∀ x y : V,
      (C.filter fun c => s(x,y) ∈ c.edges).card =
        if s((f.symm x).1,(f.symm y).1) ∈ ({s(i,j),s(i,k),s(j,k)} : Finset (Sym2 (Fin m))) then 1 else 0 := by
  classical
  let w (a b : Bool) : G.Walk (f (i,a)) (f (i,a)) :=
    .cons (adj i a j b hij) (.cons (adj j b k (a ^^ b) hjk) (.cons (adj k (a ^^ b) i a hik.symm) .nil))
  have simple (a b : Bool) : (w a b).IsCycle := by
    simp [w,Walk.isCycle_def,hij,hik,hjk,Ne.symm hij,Ne.symm hik]
  let c (a b : Bool) : Cycle G := ⟨f (i,a), w a b, simple a b⟩
  have length (a b : Bool) : (c a b).length=3 := rfl
  have edges (a b : Bool) (x y : Fin m × Bool) :
      s(f x,f y) ∈ (c a b).edges ↔
      s(x,y)=s((i,a),(j,b)) ∨ s(x,y)=s((j,b),(k,a ^^ b)) ∨ s(x,y)=s((k,a ^^ b),(i,a)) := by
    change s(f x,f y) ∈ [s(f (i,a),f (j,b)),s(f (j,b),f (k,a ^^ b)),s(f (k,a ^^ b),f (i,a))] ↔ _
    simp only [List.mem_cons,List.not_mem_nil,or_false,Sym2.eq_iff,Equiv.apply_eq_iff_eq]
  let C := c false false ::ₘ c false true ::ₘ c true false ::ₘ c true true ::ₘ 0
  refine ⟨C,by simp [C,lengths,length,Multiset.replicate_succ],?_⟩
  intro X Y
  obtain ⟨⟨x,u⟩,rfl⟩ := f.surjective X
  obtain ⟨⟨y,v⟩,rfl⟩ := f.surjective Y
  simp only [Equiv.symm_apply_apply]
  by_cases h : s(x,y) ∈ ({s(i,j),s(i,k),s(j,k)} : Finset (Sym2 (Fin m)))
  · rw [if_pos h]
    simp only [Finset.mem_insert,Finset.mem_singleton,Sym2.eq_iff] at h
    rcases h with (⟨rfl,rfl⟩|⟨rfl,rfl⟩) | (⟨rfl,rfl⟩|⟨rfl,rfl⟩) | (⟨rfl,rfl⟩|⟨rfl,rfl⟩)
    all_goals cases u <;> cases v <;>
      simp [C,Multiset.filter_singleton,edges,hij,hik,hjk,Ne.symm hij,Ne.symm hik,Ne.symm hjk]
  · rw [if_neg h]
    have none (a b : Bool) : s(f (x,u),f (y,v)) ∉ (c a b).edges := by
      intro he
      apply h
      rw [edges] at he
      simp only [Finset.mem_insert,Finset.mem_singleton,Sym2.eq_iff] at he ⊢
      simp only [Prod.mk.injEq] at he
      grind
    simp [C,Multiset.filter_singleton,none]

/-- A three-element subset supports four triangles above all its internal base
pairs. -/
theorem region_of_three {V : Type*} [DecidableEq V] {m : ℕ} (f : (Fin m × Bool) ≃ V)
    (G : SimpleGraph V) (adj : ∀ i a j b, i ≠ j → G.Adj (f (i,a)) (f (j,b)))
    (B : Finset (Fin m)) (three : B.card=3) :
    ∃ C : Multiset (Cycle G), lengths C=Multiset.replicate 4 3 ∧ ∀ x y : V,
      (C.filter fun c => s(x,y) ∈ c.edges).card =
        if s((f.symm x).1,(f.symm y).1) ∈ ((⊤ : SimpleGraph (Fin m)).edgeFinset.filter (fun e => e.toFinset ⊆ B)) then 1 else 0 := by
  classical
  obtain ⟨i,j,k,hij,hik,hjk,rfl⟩ := Finset.card_eq_three.mp three
  have support : ((⊤ : SimpleGraph (Fin m)).edgeFinset.filter (fun e => e.toFinset ⊆ {i,j,k})) =
      {s(i,j),s(i,k),s(j,k)} := by
    ext e
    induction e using Sym2.ind with
    | _ x y =>
      simp only [Finset.mem_filter,SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet,SimpleGraph.top_adj,Sym2.toFinset_mk_eq,
        Finset.insert_subset_iff,Finset.singleton_subset_iff,Finset.mem_insert,Finset.mem_singleton,Sym2.eq_iff]
      grind
  rw [support]
  exact triangle_pair_region f G adj i j k hij hik hjk

end AlspachLift

namespace AlspachTrades
open Finset

/-- Adjoin one point to a triple system whose leave is a perfect matching.
Each matched pair forms a new triple with the new point. -/
theorem fill_matched_pairs {V : Type} [DecidableEq V] (mate : V → V)
    (inv : Function.Involutive mate) (ne : ∀ x,mate x≠x)
    (F : Finset V → Prop) (three : ∀ b,F b → b.card=3)
    (valid : ∀ b,F b → ∀ x∈b,∀ y∈b, x≠y → mate x≠y)
    (cover : ∀ x y,x≠y → mate x≠y → ∃! b : {b // F b}, x∈b.val ∧ y∈b.val) :
    ∃ H : Finset (Option V) → Prop,
      (∀ b,H b → b.card=3) ∧
      (∀ p q : Option V,p≠q → ∃! b : {b // H b}, p∈b.val ∧ q∈b.val) := by
  classical
  let embed : V ↪ Option V := ⟨some,Option.some_injective _⟩
  let old (b : Finset V) := b.map embed
  let link (x : V) : Finset (Option V) := {none,some x,some (mate x)}
  let H (b : Finset (Option V)) := (∃ b', F b' ∧ b=old b') ∨ ∃ x, b=link x
  have old_hit (b : Finset V) (x : V) : some x∈old b ↔ x∈b := by
    simp [old,embed]
  have old_non (b : Finset V) : none∉old b := by simp [old,embed]
  have link_inf (x : V) : none∈link x := by simp [link]
  have link_hit (x y : V) : some y∈link x ↔ y=x ∨ y=mate x := by simp [link]
  have flip (x : V) : link (mate x)=link x := by
    ext p
    simp only [link,mem_insert,mem_singleton,inv x]
    tauto
  have pair (x y w : V) (xy : x≠y) (hx : some x∈link w) (hy : some y∈link w) : mate x=y := by
    rcases (link_hit _ _).mp hx with eq|eq <;> rcases (link_hit _ _).mp hy with eq'|eq' <;>
      grind [inv w]
  have uniq_inf (x : V) : ∃! b : {b // H b}, none∈b.val ∧ some x∈b.val := by
    refine ⟨⟨link x,Or.inr ⟨x,rfl⟩⟩,⟨link_inf x,(link_hit x x).mpr (Or.inl rfl)⟩,?_⟩
    rintro ⟨b,hb⟩ ⟨hn,hx⟩
    rcases hb with ⟨s,_,rfl⟩|⟨y,rfl⟩
    · exact False.elim (old_non s hn)
    · apply Subtype.ext
      rcases (link_hit y x).mp hx with rfl|rfl
      · rfl
      · exact (flip y).symm
  have uniq_finite (x y : V) (xy : x≠y) :
      ∃! b : {b // H b}, some x∈b.val ∧ some y∈b.val := by
    by_cases eq : mate x=y
    · refine ⟨⟨link x,Or.inr ⟨x,rfl⟩⟩,⟨(link_hit x x).mpr (Or.inl rfl),
        (link_hit x y).mpr (Or.inr eq.symm)⟩,?_⟩
      rintro ⟨b,hb⟩ ⟨hx,hy⟩
      rcases hb with ⟨s,hs,rfl⟩|⟨z,rfl⟩
      · exact False.elim (valid s hs x ((old_hit _ _).mp hx) y ((old_hit _ _).mp hy) xy eq)
      · apply Subtype.ext
        rcases (link_hit z x).mp hx with rfl|rfl
        · rfl
        · exact (flip z).symm
    · obtain ⟨b,⟨hx,hy⟩,uniq⟩ := cover x y xy eq
      refine ⟨⟨old b.val,Or.inl ⟨b.val,b.property,rfl⟩⟩,⟨(old_hit _ _).mpr hx,(old_hit _ _).mpr hy⟩,?_⟩
      rintro ⟨s,hs⟩ ⟨hsx,hsy⟩
      rcases hs with ⟨w,hw,rfl⟩|⟨z,rfl⟩
      · have ew := uniq (⟨w,hw⟩ : {s // F s}) ⟨(old_hit _ _).mp hsx,(old_hit _ _).mp hsy⟩
        exact Subtype.ext (congrArg (fun a : {s // F s} => old a.val) ew)
      · exact False.elim (eq (pair x y z xy hsx hsy))
  refine ⟨H,?_,?_⟩
  · rintro b (⟨s,hs,rfl⟩ | ⟨x,rfl⟩)
    · simpa [old] using three _ hs
    · simp [link,(ne x).symm]
  · rintro (_|x) (_|y) pq
    · exact False.elim (pq rfl)
    · exact uniq_inf y
    · simpa only [and_comm] using uniq_inf x
    · exact uniq_finite x y (fun h => pq (congrArg some h))

end AlspachTrades

namespace AlspachTrades
open AlspachTriple Finset SimpleGraph

/-- Label a finite triple system with the points 0,...,m−1. Counting each pair
once gives exactly m.choose 2 / 3 blocks; every block is a three-point set. -/
theorem label_full_design {V : Type} [Fintype V] [DecidableEq V] (m : ℕ)
    (size : Fintype.card V=m) (F : Finset V → Prop) (three : ∀ b,F b → b.card=3)
    (pairs : ∀ x y : V,x≠y → ∃! b : {b // F b}, x∈b.val ∧ y∈b.val) :
    ∃ B : Fin (m.choose 2/3) → Finset (Fin m), (∀ i,(B i).card=3) ∧
      ∀ x y : Fin m,x≠y → ∃! i, x∈B i ∧ y∈B i := by
  classical
  let I := {b // F b}
  let : Fintype I := Fintype.ofFinite _
  let tr (b : I) := b.val
  obtain ⟨_,_,_,edgecount⟩ := TriangleBridge.blocks_in_graph (⊤ : SimpleGraph V) tr
    (fun b => three _ b.property) (fun _ _ _ _ _ h => h) (fun x y h => pairs x y h)
  rw [card_edgeFinset_top_eq_card_choose_two,size] at edgecount
  let index : I ≃ Fin (m.choose 2 / 3) := Fintype.equivFinOfCardEq (by omega)
  let label : V ≃ Fin m := Fintype.equivFinOfCardEq size
  let B (i : Fin (m.choose 2/3)) := (tr (index.symm i)).map label.toEmbedding
  have mem (x : Fin m) (i) : x∈B i ↔ label.symm x∈tr (index.symm i) := by
    rw [show x=label (label.symm x) from (label.apply_symm_apply x).symm]
    simp [B]
  refine ⟨B,fun i => by simpa [B,tr] using three _ (index.symm i).property,?_⟩
  intro x y xy
  obtain ⟨v,hit,uniq⟩ := pairs (label.symm x) (label.symm y) (fun h => xy (label.symm.injective h))
  refine ⟨index v,⟨(mem _ _).mpr (by simpa [tr] using hit.1),
    (mem _ _).mpr (by simpa [tr] using hit.2)⟩,?_⟩
  rintro j ⟨hx,hy⟩
  exact index.symm.injective (by simpa using uniq (index.symm j) ⟨(mem _ _).mp hx,(mem _ _).mp hy⟩)

/-- Bose's three-layer model is already a full design at orders 6k+3. -/
theorem bose_full_design (k : ℕ) :
    ∃ B : Fin ((6*k+3).choose 2/3) → Finset (Fin (6*k+3)), (∀ i,(B i).card=3) ∧
      ∀ x y : Fin (6*k+3),x≠y → ∃! i, x∈B i ∧ y∈B i := by
  classical
  obtain ⟨op,comm,latin,fixed⟩ := odd_latin k
  obtain ⟨F,three,_,covers⟩ := latin_blocks op comm latin (fun _ => True) (fun x _ => fixed x)
  have size : Fintype.card (Fin (2*k+1) × Fin 3)=6*k+3 := by
    simp only [Fintype.card_prod,Fintype.card_fin]; ring
  exact label_full_design _ size F three (fun x y xy => covers x y xy (by simp))

/-- Skolem's 6k-point model fills its matching by adding a point at infinity. -/
theorem skolem_full_design (k : ℕ) :
    ∃ B : Fin ((6*k+1).choose 2/3) → Finset (Fin (6*k+1)), (∀ i,(B i).card=3) ∧
      ∀ x y : Fin (6*k+1),x≠y → ∃! i, x∈B i ∧ y∈B i := by
  classical
  obtain ⟨op,other,comm,latin,swap,inv,ne,diag⟩ := half_latin k
  obtain ⟨F,three,avoids,covers⟩ := latin_blocks op comm latin (fun x => x.val<k)
    (fun x hx => by simpa [hx] using diag x)
  let mate (p : Fin (2*k) × Fin 3) : Fin (2*k) × Fin 3 :=
    (other p.1,if p.1.val<k then p.2+2 else p.2+1)
  have n1 : ∀ i : Fin 3, i+1+2=i := by decide
  have n2 : ∀ i : Fin 3, i+2+1=i := by decide
  have mi : Function.Involutive mate := by
    rintro ⟨x,i⟩
    by_cases h : x.val<k
    · have hh : ¬(other x).val<k := fun eq => (swap x).mp eq h
      simp [mate,h,hh,inv x,n2]
    · have hh := (swap x).mpr h
      simp [mate,h,hh,inv x,n1]
  have mf (p) : mate p ≠ p := fun e => ne p.1 (congrArg Prod.fst e)
  have holes (p q : Fin (2*k) × Fin 3) : mate p=q ↔
      (¬p.1.val<k ∧ q.2=p.2+1 ∧ q.1=op p.1 p.1) ∨
      (¬q.1.val<k ∧ p.2=q.2+1 ∧ p.1=op q.1 q.1) := by
    rcases p with ⟨x,i⟩
    constructor
    · rintro rfl
      by_cases h : x.val<k
      · have hh : ¬(other x).val<k := fun eq => (swap x).mp eq h
        right
        simp [mate,h,diag,hh,inv x,n2]
      · left
        simp [mate,h,diag]
    · rcases q with ⟨y,j⟩
      change ((¬x.val<k ∧ j=i+1 ∧ y=op x x) ∨
        (¬y.val<k ∧ i=j+1 ∧ x=op y y)) → _
      rintro (⟨h,rfl,rfl⟩ | ⟨h,rfl,hx⟩)
      · simp [mate,h,diag]
      · have eq : x=other y := by simpa [diag,h] using hx
        rw [eq]
        simp [mate,(swap y).mpr h,inv y,n1]
  obtain ⟨H,card,pairs⟩ := fill_matched_pairs mate mi mf F three
    (fun b hb x hx y hy _ eq => avoids b hb x hx y hy ((holes _ _).mp eq))
    (fun x y xy ne => covers x y xy (fun h => ne ((holes _ _).mpr h)))
  have size : Fintype.card (Option (Fin (2*k) × Fin 3))=6*k+1 := by
    simp only [Fintype.card_option,Fintype.card_prod,Fintype.card_fin]
    ring
  exact label_full_design _ size H card pairs

theorem full_design (m : ℕ) (residue : m%6=1 ∨ m%6=3) :
    ∃ B : Fin (m.choose 2/3) → Finset (Fin m), (∀ i,(B i).card=3) ∧
      ∀ x y : Fin m,x≠y → ∃! i, x∈B i ∧ y∈B i := by
  generalize hk : m/6=k
  rcases residue with h|h
  · have e : m=6*k+1 := by omega
    subst m
    exact skolem_full_design k
  · have e : m=6*k+3 := by omega
    subst m
    exact bose_full_design k

end AlspachTrades

namespace AlspachTrades
open Finset SimpleGraph
open scoped Classical

/-- A Steiner triple system supplies any prescribed number of triple supports,
up to its full block count. Distinct selected blocks have disjoint edge sets. -/
theorem triangle_packing (m t : ℕ) (residue : m%6=1 ∨ m%6=3) (ht : t≤ m.choose 2/3) :
    ∃ B : Fin t → Finset (Fin m), (∀ i,(B i).card=3) ∧
      Pairwise (fun i j => Disjoint
        ((⊤ : SimpleGraph (Fin m)).edgeFinset.filter (fun e => e.toFinset ⊆ B i))
        ((⊤ : SimpleGraph (Fin m)).edgeFinset.filter (fun e => e.toFinset ⊆ B j))) := by
  classical
  obtain ⟨all,three,pair⟩ := full_design m residue
  let inc (i : Fin t) : Fin (m.choose 2/3) := i.castLE ht
  refine ⟨fun i => all (inc i), fun i => three _,?_⟩
  intro i j neq
  apply Finset.disjoint_left.mpr
  intro e
  induction e using Sym2.ind with
  | h x y =>
    intro hi hj
    obtain ⟨edge,bi⟩ := mem_filter.mp hi
    obtain ⟨_,bj⟩ := mem_filter.mp hj
    have distinct : x≠y := SimpleGraph.mem_edgeFinset.mp edge
    have hx := Sym2.mem_toFinset.mpr (Sym2.mem_mk_left x y)
    have hy := Sym2.mem_toFinset.mpr (Sym2.mem_mk_right x y)
    have same : inc i = inc j := (pair x y distinct).unique ⟨bi hx,bi hy⟩ ⟨bj hx,bj hy⟩
    exact neq (Fin.ext (congrArg (fun v : Fin (m.choose 2/3) => v.val) same))

end AlspachTrades

namespace AlspachTrades

/-- In a square/triangle list for order 2m, triangles occur in multiples of four. -/
theorem classify_trades (m : ℕ) (hm : 0< m) (L : Multiset ℕ)
    (shape : ∀a∈L,a=3 ∨ a=4) (budget : L.sum=(2*m).choose 2-(2*m)/2) :
    ∃ t, t ≤ m.choose 2/3 ∧ L = Multiset.replicate (4*t) 3+Multiset.replicate (m.choose 2-3*t) 4 := by
  have filt : L.filter (fun a => ¬a=3) = Multiset.replicate (L.count 4) 4 := by
    rw [←Multiset.filter_eq']
    apply Multiset.filter_congr
    intro a ha
    rcases shape a ha with rfl|rfl <;> decide
  have split := Multiset.filter_add_not (fun a => a=3) L
  rw [filt,Multiset.filter_eq'] at split
  have eq := congrArg Multiset.sum split
  rw [Multiset.sum_add,Multiset.sum_replicate,Multiset.sum_replicate,smul_eq_mul,smul_eq_mul,
    budget,AlspachPaired.paired_budget m hm] at eq
  refine ⟨L.count 3/4,by omega,?_⟩
  have h3 : L.count 3 = 4*(L.count 3/4) := by omega
  have h4 : L.count 4 = m.choose 2-3*(L.count 3/4) := by omega
  simpa only [←h3,←h4] using split.symm

end AlspachTrades

namespace AlspachTrades
open Finset SimpleGraph AlspachConjecture AlspachLift
open scoped Classical

/-- Each selected region replaces three squares by four triangles. The leftover
base edges are represented by single squares. -/
theorem glue_triangles {n m t : ℕ} (f : (Fin m × Bool) ≃ Fin n)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (adj : ∀ x y, G.Adj x y ↔ (f.symm x).1 ≠ (f.symm y).1)
    (S : Fin t → Finset (Sym2 (Fin m)))
    (disj : Pairwise fun i j => Disjoint (S i) (S j))
    (triangles : ∀ i, ∃ C : Multiset (Cycle G), lengths C = Multiset.replicate 4 3 ∧ ∀ x y : Fin n,
      (C.filter fun c => s(x,y) ∈ c.edges).card = if s((f.symm x).1,(f.symm y).1) ∈ S i then 1 else 0) :
    ∃ (q : ℕ) (C : Multiset (Cycle G)), IsCycleDecomposition G C ∧
      lengths C=Multiset.replicate (4*t) 3+Multiset.replicate q 4 := by
  let π := fun x : Fin n => (f.symm x).1
  let Covers (S : Finset (Sym2 (Fin m))) (L : Multiset ℕ) : Prop :=
    ∃ C : Multiset (Cycle G), lengths C = L ∧ ∀ x y : Fin n,
      (C.filter fun c => s(x,y) ∈ c.edges).card = if s(π x,π y) ∈ S then 1 else 0
  obtain ⟨covers_union,covers_many⟩ := AlspachRegions.collect G π
  let used := univ.biUnion S
  let unused := (⊤ : SimpleGraph (Fin m)).edgeFinset \ used
  have left : Covers used (Multiset.replicate (4*t) 3) := by
    have h := covers_many (univ : Finset (Fin t)) S (fun _ => Multiset.replicate 4 3)
      (fun i _ => triangles i) (fun _ _ _ _ hij => disj hij)
    simpa only [used,sum_const,card_univ,Fintype.card_fin,Multiset.nsmul_replicate,Nat.mul_comm t 4] using h
  have squares (e : Sym2 (Fin m)) (he : e∈unused) : Covers {e} {4} := by
    induction e using Sym2.ind with
    | _ i j =>
      have ne : i≠j := SimpleGraph.mem_edgeFinset.mp (mem_sdiff.mp he).1
      apply AlspachLadder.square_region f G ne
      intro a b
      exact (adj _ _).mpr (by simpa using ne)
  have right : Covers unused (Multiset.replicate unused.card 4) := by
    have h := covers_many unused (fun e => {e}) (fun _ => ({4} : Multiset ℕ))
      squares (fun i _ j _ hij => by simpa using hij)
    simpa [sum_const,Multiset.nsmul_singleton] using h
  have separate : Disjoint used unused := disjoint_left.mpr (fun _ hu hx => (mem_sdiff.mp hx).2 hu)
  obtain ⟨C,hC,hcount⟩ := covers_union left right separate
  refine ⟨unused.card,C,?_,hC⟩
  intro edge
  induction edge using Sym2.ind with
  | _ a b =>
    intro he
    have hbase : s(π a,π b)∈(⊤ : SimpleGraph (Fin m)).edgeFinset := SimpleGraph.mem_edgeFinset.mpr ((adj a b).mp (G.mem_edgeFinset.mp he))
    have hmem : s(π a,π b)∈used∪unused := by
      rw [mem_union]
      by_cases hu : s(π a,π b)∈used
      · exact Or.inl hu
      · exact Or.inr (mem_sdiff.mpr ⟨hbase,hu⟩)
    simpa only [if_pos hmem] using hcount a b

/-- A packing of t base triples prescribes four triangles per chosen triple;
every edge outside the packing is covered by a four-cycle. -/
theorem realize_from_packing {m : ℕ} (hm : 0< m) (L : Multiset ℕ)
    (shape : ∀a∈L,a=3 ∨ a=4) (budget : L.sum=(2*m).choose 2-(2*m)/2)
    (packing : ∀ t ≤ m.choose 2/3, ∃ B : Fin t → Finset (Fin m),
      (∀ i, (B i).card=3) ∧ Pairwise (fun i j => Disjoint
        ((⊤ : SimpleGraph (Fin m)).edgeFinset.filter fun e => e.toFinset ⊆ B i)
        ((⊤ : SimpleGraph (Fin m)).edgeFinset.filter fun e => e.toFinset ⊆ B j))) :
    ∃ J : (completeGraph (Fin (2*m))).Subgraph, J.IsPerfectMatching ∧
      ∃ C : Multiset (Cycle (completeGraph (Fin (2*m)) \ J.spanningCoe)),
        IsCycleDecomposition _ C ∧ lengths C=L := by
  classical
  obtain ⟨t,lim,hL⟩ := classify_trades m hm L shape budget
  obtain ⟨B,hB,disj⟩ := packing t lim
  let f : (Fin m × Bool) ≃ Fin (2*m) := Fintype.equivOfCardEq (by simp; omega)
  obtain ⟨J,hJ,adj⟩ := AlspachSquares.pair_matching f
  let G := completeGraph (Fin (2*m)) \ J.spanningCoe
  let S (i : Fin t) := (⊤ : SimpleGraph (Fin m)).edgeFinset.filter fun e => e.toFinset ⊆ B i
  have across (i : Fin m) (a : Bool) (j : Fin m) (b : Bool) (ne : i≠j) :
      G.Adj (f (i,a)) (f (j,b)) := (adj _ _).mpr (by simpa using ne)
  have regions (i : Fin t) : ∃ C : Multiset (Cycle G), lengths C = Multiset.replicate 4 3 ∧ ∀ x y : Fin (2*m),
      (C.filter fun c => s(x,y) ∈ c.edges).card = if s((f.symm x).1,(f.symm y).1) ∈ S i then 1 else 0 :=
    region_of_three f G across (B i) (hB i)
  obtain ⟨q,C,hC,sizes⟩ := glue_triangles f G adj S disj regions
  refine ⟨J,hJ,C,hC,?_⟩
  have edgeCount := TriangleBridge.matching_budget J hJ
  rw [Fintype.card_fin] at edgeCount
  have sum : (lengths C).sum=L.sum := by
    rw [AlspachLadder.decomposition_budget C hC,budget]
    convert edgeCount using 1
    congr 1
    ext e
    simp only [mem_edgeFinset, G]
  rw [sizes,hL,Multiset.sum_add,Multiset.sum_add] at sum
  simp only [Multiset.sum_replicate,smul_eq_mul] at sum
  have hq : q=m.choose 2-3*t := by omega
  rw [sizes,hq,hL]

end AlspachTrades

namespace AlspachTrades
open Finset SimpleGraph AlspachConjecture
open scoped Classical

/-- When n is 2 or 6 modulo 12, every admissible mixture of triangles and squares
partitions the complement of any prescribed perfect matching. -/
theorem triangle_square_lists (n : ℕ) (residue : n%12=2 ∨ n%12=6)
    (I : (completeGraph (Fin n)).Subgraph) (hI : I.IsPerfectMatching) (L : Multiset ℕ)
    (shape : ∀a∈L,a=3 ∨ a=4) (budget : L.sum=n.choose 2-n/2) :
    ∃ C : Multiset (Cycle (completeGraph (Fin n) \ I.spanningCoe)),
      IsCycleDecomposition _ C ∧ lengths C=L := by
  obtain ⟨m,hm,rfl,hr⟩ : ∃ m, 0< m ∧ n=2*m ∧ (m%6=1 ∨ m%6=3) :=
    ⟨n/2,by omega,by omega,by omega⟩
  obtain ⟨J,hJ,C,hC,hL⟩ := realize_from_packing hm L shape budget (triangle_packing m · hr ·)
  obtain ⟨f⟩ := OMA.R_AlspachConjecture_alspach_conjecture_variants_even_R2.matchings_complements_iso J I hJ hI
  exact OMA.R_AlspachConjecture_alspach_conjecture_variants_even_R2.iso_decomposition f hC hL

end AlspachTrades

namespace AlspachTrades
open Finset SimpleGraph
open scoped Classical

/-- Embed a Steiner system on d≤ m points in the first d ambient rows.
Deleting unused blocks allows any prescribed count up to the design size. -/
theorem triangle_packing_suborder {d m t : ℕ} (hd : d≤ m) (hr : d%6=1 ∨ d%6=3)
    (lim : t≤d.choose 2/3) :
    ∃ B : Fin t → Finset (Fin m), (∀ i,(B i).card=3) ∧
      Pairwise (fun i j => Disjoint
        ((⊤ : SimpleGraph (Fin m)).edgeFinset.filter (fun e => e.toFinset ⊆ B i))
        ((⊤ : SimpleGraph (Fin m)).edgeFinset.filter (fun e => e.toFinset ⊆ B j))) := by
  classical
  obtain ⟨all,three,pair⟩ := full_design d hr
  let pick := Fin.castLEEmb lim
  let f := Fin.castLEEmb hd
  refine ⟨fun i => (all (pick i)).map f, fun i => by simp [three],?_⟩
  intro i j ne
  apply Finset.disjoint_left.mpr
  intro e
  induction e using Sym2.ind with
  | h x y =>
    intro hi hj
    obtain ⟨edge,bi⟩ := mem_filter.mp hi
    obtain ⟨_,bj⟩ := mem_filter.mp hj
    have distinct : x≠y := SimpleGraph.mem_edgeFinset.mp edge
    have hx := Sym2.mem_toFinset.mpr (Sym2.mem_mk_left x y)
    have hy := Sym2.mem_toFinset.mpr (Sym2.mem_mk_right x y)
    obtain ⟨x',hi₁,ex⟩ := mem_map.mp (bi hx)
    obtain ⟨y',hi₂,ey⟩ := mem_map.mp (bi hy)
    have hj₁ : x'∈all (pick j) := (mem_map' f).mp (ex.symm ▸ bj hx)
    have hj₂ : y'∈all (pick j) := (mem_map' f).mp (ey.symm ▸ bj hy)
    have xy : x'≠y' := fun eq => distinct (ex.symm.trans ((congrArg f eq).trans ey))
    exact ne (pick.injective ((pair x' y' xy).unique ⟨hi₁,hi₂⟩ ⟨hj₁,hj₂⟩))

/-- Puncturing a Steiner triple system deletes one triple for every two
remaining points. The surviving triples give packings of all smaller sizes. -/
theorem triangle_packing_even (m t : ℕ) (residue : m%6=0 ∨ m%6=2)
    (ht : t ≤ (m.choose 2-m/2)/3) :
    ∃ B : Fin t → Finset (Fin m), (∀ i,(B i).card=3) ∧
      Pairwise (fun i j => Disjoint
        ((⊤ : SimpleGraph (Fin m)).edgeFinset.filter (fun e => e.toFinset ⊆ B i))
        ((⊤ : SimpleGraph (Fin m)).edgeFinset.filter (fun e => e.toFinset ⊆ B j))) := by
  classical
  obtain ⟨all,three,pairs⟩ := full_design (m+1) (by omega)
  let p := Fin.last m
  let through := univ.filter (fun i => p∈all i)
  let leaves (i : Fin ((m+1).choose 2/3)) := (all i).erase p
  have union : through.biUnion leaves = univ.erase p := by
    ext x
    simp only [mem_biUnion,through,mem_filter,mem_univ,true_and,leaves,mem_erase,and_true]
    constructor
    · rintro ⟨_,_,hx,_⟩
      exact hx
    · intro hx
      obtain ⟨i,⟨hp,hi⟩,_⟩ := pairs p x hx.symm
      exact ⟨i,hp,hx,hi⟩
  have disjoint : (through : Set _).PairwiseDisjoint leaves := by
    intro i hi j hj ne
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨xp,xi⟩ := mem_erase.mp hx
    have same := (pairs p x xp.symm).unique
      (show p∈all i ∧ x∈all i from ⟨(mem_filter.mp hi).2,xi⟩)
      (show p∈all j ∧ x∈all j from ⟨(mem_filter.mp hj).2,(mem_erase.mp hy).2⟩)
    exact ne same
  have two (i) (hi : i∈through) : (leaves i).card=2 := by
    dsimp only [leaves]
    rw [card_erase_of_mem (mem_filter.mp hi).2,three]
  have removed := congrArg Finset.card union
  rw [card_biUnion disjoint,sum_congr rfl two,sum_const,smul_eq_mul,card_erase_of_mem (mem_univ p),card_univ,Fintype.card_fin] at removed
  let T := {i : Fin ((m+1).choose 2/3) // p ∉ all i}
  have cardT : t ≤ Fintype.card T := by
    change t ≤ Fintype.card {i : Fin ((m+1).choose 2/3) // ¬p ∈ all i}
    rw [Fintype.card_subtype_compl,Fintype.card_fin,Fintype.card_subtype]
    change t ≤ (m+1).choose 2 / 3 - through.card
    have step : (m+1).choose 2 = m + m.choose 2 := by simpa only [Nat.choose_one_right] using Nat.choose_succ_succ m 1
    omega
  let V := {x : Fin (m+1) // x≠p}
  have cardV : Fintype.card V=m := by
    change Fintype.card {x : Fin (m+1) // ¬x=p} = m
    rw [Fintype.card_subtype_compl,Fintype.card_subtype_eq,Fintype.card_fin]
    omega
  let f : V ≃ Fin m := Fintype.equivFinOfCardEq cardV
  let take (i : Fin t) : T := (Fintype.equivFin T).symm (i.castLE cardT)
  have inj : Function.Injective take := by
    intro i j h
    have e := (Fintype.equivFin T).symm.injective h
    exact Fin.ext (congrArg (fun v : Fin (Fintype.card T) => v.val) e)
  let B (i : Fin t) := ((all (take i).val).subtype (fun x => x≠p)).map f.toEmbedding
  have hit (i : Fin t) (x : Fin m) : x∈B i ↔ (f.symm x).val∈all (take i).val := by
    rw [show x=f (f.symm x) from (f.apply_symm_apply x).symm]
    simp [B]
    exact Finset.mem_subtype
  refine ⟨B,?_,?_⟩
  · intro i
    dsimp only [B]
    rw [Finset.card_map,Finset.card_subtype,Finset.filter_eq_self.mpr,three]
    intro x hx eq
    exact (take i).property (eq ▸ hx)
  · intro i j ne
    apply Finset.disjoint_left.mpr
    intro e
    induction e using Sym2.ind with
    | _ x y =>
      intro ei ej
      obtain ⟨edge,bi⟩ := mem_filter.mp ei
      have bj := (mem_filter.mp ej).2
      have distinct : x≠y := SimpleGraph.mem_edgeFinset.mp edge
      have px := Sym2.mem_toFinset.mpr (Sym2.mem_mk_left x y)
      have py := Sym2.mem_toFinset.mpr (Sym2.mem_mk_right x y)
      have xy : (f.symm x).val≠(f.symm y).val := fun h => distinct (f.symm.injective (Subtype.ext h))
      have same := (pairs _ _ xy).unique
        ⟨(hit i x).mp (bi px),(hit i y).mp (bi py)⟩
        ⟨(hit j x).mp (bj px),(hit j y).mp (bj py)⟩
      exact ne (inj (Subtype.ext same))

/-- Each triple through a specified point pairs two of the other points. -/
theorem design_valency {n : ℕ} {I : Type*} [Fintype I] (all : I → Finset (Fin n))
    (three : ∀ i,(all i).card=3)
    (pairs : ∀ x y : Fin n,x≠y → ∃! i, x∈all i ∧ y∈all i) (p : Fin n) :
    (univ.filter (fun i => p∈all i)).card*2=n-1 := by
  classical
  let through := univ.filter (fun i => p∈all i)
  let leaves (i : I) := (all i).erase p
  have union : through.biUnion leaves = univ.erase p := by
    ext x
    simp only [mem_biUnion,through,mem_filter,mem_univ,true_and,leaves,mem_erase,and_true]
    constructor
    · rintro ⟨_,_,hx,_⟩
      exact hx
    · intro hx
      obtain ⟨i,⟨hp,hi⟩,_⟩ := pairs p x hx.symm
      exact ⟨i,hp,hx,hi⟩
  have disjoint : (through : Set _).PairwiseDisjoint leaves := by
    intro i hi j hj ne
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨xp,xi⟩ := mem_erase.mp hx
    have same := (pairs p x xp.symm).unique
      (show p∈all i ∧ x∈all i from ⟨(mem_filter.mp hi).2,xi⟩)
      (show p∈all j ∧ x∈all j from ⟨(mem_filter.mp hj).2,(mem_erase.mp hy).2⟩)
    exact ne same
  have two (i) (hi : i∈through) : (leaves i).card=2 := by
    dsimp only [leaves]
    rw [card_erase_of_mem (mem_filter.mp hi).2,three]
  have removed := congrArg Finset.card union
  rw [card_biUnion disjoint,sum_congr rfl two,sum_const,smul_eq_mul,card_erase_of_mem (mem_univ p),card_univ,Fintype.card_fin] at removed
  exact removed

/-- Discard those blocks that meet a prescribed set of points, then label
arbitrarily many surviving triples on the remaining points. -/
theorem triangle_packing_after_deletion {n m t : ℕ} {I : Type*} [Fintype I]
    (all : I → Finset (Fin n)) (three : ∀ i,(all i).card=3)
    (pairs : ∀ x y : Fin n,x≠y → ∃! i, x∈all i ∧ y∈all i)
    (removed : Finset (Fin n)) (order : n-removed.card=m)
    (room : t ≤ Fintype.card {i : I // Disjoint (all i) removed}) :
    ∃ B : Fin t → Finset (Fin m), (∀ i,(B i).card=3) ∧
      Pairwise (fun i j => Disjoint
        ((⊤ : SimpleGraph (Fin m)).edgeFinset.filter (fun e => e.toFinset ⊆ B i))
        ((⊤ : SimpleGraph (Fin m)).edgeFinset.filter (fun e => e.toFinset ⊆ B j))) := by
  classical
  let T := {i : I // Disjoint (all i) removed}
  let V := {x : Fin n // x∉removed}
  have cardV : Fintype.card V=m := by
    change Fintype.card {x : Fin n // ¬x∈removed}=m
    rw [Fintype.card_subtype_compl,Fintype.card_coe,Fintype.card_fin,order]
  let f : V ≃ Fin m := Fintype.equivFinOfCardEq cardV
  let take (i : Fin t) : T := (Fintype.equivFin T).symm (i.castLE room)
  have inj : Function.Injective take := by
    intro i j h
    have e := (Fintype.equivFin T).symm.injective h
    exact Fin.ext (congrArg (fun v : Fin (Fintype.card T) => v.val) e)
  let B (i : Fin t) := ((all (take i).val).subtype (fun x => x∉removed)).map f.toEmbedding
  have hit (i : Fin t) (x : Fin m) : x∈B i ↔ (f.symm x).val∈all (take i).val := by
    rw [show x=f (f.symm x) from (f.apply_symm_apply x).symm]
    simp [B]
    exact Finset.mem_subtype
  refine ⟨B,?_,?_⟩
  · intro i
    dsimp only [B]
    rw [Finset.card_map,Finset.card_subtype,Finset.filter_eq_self.mpr,three]
    intro x hx eq
    exact Finset.disjoint_left.mp (take i).property hx eq
  · intro i j ne
    apply Finset.disjoint_left.mpr
    intro e
    induction e using Sym2.ind with
    | _ x y =>
      intro ei ej
      obtain ⟨edge,bi⟩ := mem_filter.mp ei
      have bj := (mem_filter.mp ej).2
      have distinct : x≠y := SimpleGraph.mem_edgeFinset.mp edge
      have px := Sym2.mem_toFinset.mpr (Sym2.mem_mk_left x y)
      have py := Sym2.mem_toFinset.mpr (Sym2.mem_mk_right x y)
      have xy : (f.symm x).val≠(f.symm y).val := fun h => distinct (f.symm.injective (Subtype.ext h))
      have same := (pairs _ _ xy).unique
        ⟨(hit i x).mp (bi px),(hit i y).mp (bi py)⟩
        ⟨(hit j x).mp (bj px),(hit j y).mp (bj py)⟩
      exact ne (inj (Subtype.ext same))

/-- Two points of a Steiner system share exactly one block. Removing them
from order m+2 deletes m triples and leaves m−1 uncovered pairs. -/
theorem triangle_packing_five (m t : ℕ) (residue : m%6=5)
    (ht : t ≤ (m.choose 2-(m-1))/3) :
    ∃ B : Fin t → Finset (Fin m), (∀ i,(B i).card=3) ∧
      Pairwise (fun i j => Disjoint
        ((⊤ : SimpleGraph (Fin m)).edgeFinset.filter (fun e => e.toFinset ⊆ B i))
        ((⊤ : SimpleGraph (Fin m)).edgeFinset.filter (fun e => e.toFinset ⊆ B j))) := by
  classical
  obtain ⟨all,three,pairs⟩ := full_design (m+2) (by omega)
  let p := Fin.last (m+1)
  let q := (Fin.last m).castSucc
  have pq : p≠q := fun h => by have v := congrArg Fin.val h; change m+1=m at v; omega
  let through (x : Fin (m+2)) := univ.filter (fun i => x∈all i)
  have overlap : (through p ∩ through q).card=1 := by
    obtain ⟨i,hi,uniq⟩ := pairs p q pq
    apply Finset.card_eq_one.mpr
    refine ⟨i,?_⟩
    ext j
    simp only [through,Finset.mem_inter,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_singleton]
    exact ⟨uniq j,fun eq => eq ▸ hi⟩
  have pcount := design_valency all three pairs p
  have qcount := design_valency all three pairs q
  change (through p).card*2=m+2-1 at pcount
  change (through q).card*2=m+2-1 at qcount
  have sum := card_union_add_card_inter (through p) (through q)
  have lost : (through p ∪ through q).card=m := by omega
  let removed : Finset (Fin (m+2)) := {p,q}
  have two : removed.card=2 := by simp [removed,pq]
  apply triangle_packing_after_deletion all three pairs removed (by omega)
  rw [Fintype.card_subtype]
  let U := through p ∪ through q
  have excision : (univ.filter (fun i => Disjoint (all i) removed)) = univ \ U := by
    ext i
    simp [removed,U,through,Finset.disjoint_left]
    constructor
    · intro h
      exact ⟨fun hp => (h hp).1 rfl,fun hq => (h hq).2 rfl⟩
    · rintro ⟨hp,hq⟩ x hx
      exact ⟨fun e => hp (e ▸ hx),fun e => hq (e ▸ hx)⟩
  rw [excision,card_sdiff_of_subset (subset_univ _),card_univ,Fintype.card_fin]
  change t ≤ (m+2).choose 2 / 3 - (through p ∪ through q).card
  have step : (m+1).choose 2 = m+m.choose 2 := by simpa only [Nat.choose_one_right] using Nat.choose_succ_succ m 1
  have next : (m+2).choose 2 = (m+1)+(m+1).choose 2 := by simpa only [Nat.choose_one_right] using Nat.choose_succ_succ (m+1) 1
  omega

end AlspachTrades

namespace AlspachTrades
open Finset SimpleGraph AlspachConjecture
open scoped Classical

/-- A bound on uncovered base edges translates into a bound on the number
of squares in the requested list. -/
theorem enough_squares {m leave : ℕ} (hm : 0< m) (L : Multiset ℕ)
    (shape : ∀ a∈L,a=3 ∨ a=4) (budget : L.sum=(2*m).choose 2-(2*m)/2)
    (enough : leave ≤ L.count 4) : L.count 3/4 ≤ (m.choose 2-leave)/3 := by
  obtain ⟨t,lim,eq⟩ := classify_trades m hm L shape budget
  have num3 : L.count 3=4*t := by simp [eq,Multiset.count_replicate]
  have num4 : L.count 4=m.choose 2-3*t := by simp [eq,Multiset.count_replicate]
  omega

/-- For base order four modulo six, use a Steiner design on all but one point. -/
theorem triangle_packing_four {m t : ℕ} (four : m%6=4) (lim : t ≤ (m.choose 2-(m-1))/3) :
    ∃ B : Fin t → Finset (Fin m), (∀i,(B i).card=3) ∧ Pairwise (fun i j => Disjoint
      ((⊤ : SimpleGraph (Fin m)).edgeFinset.filter fun e => e.toFinset ⊆ B i)
      ((⊤ : SimpleGraph (Fin m)).edgeFinset.filter fun e => e.toFinset ⊆ B j)) := by
  have h : m.choose 2-(m-1) = (m-1).choose 2 := by
    obtain ⟨k,hk⟩ : ∃ k, m=k+1 := ⟨m-1,by omega⟩
    subst m
    have step : (k+1).choose 2=k+k.choose 2 := by
      simpa only [Nat.choose_one_right] using Nat.choose_succ_succ k 1
    rw [step,Nat.add_sub_cancel,Nat.add_sub_cancel_left]
  rw [h] at lim
  exact triangle_packing_suborder (show m-1≤ m by omega) (Or.inr (by omega)) lim

end AlspachTrades

namespace AlspachTrades
open Finset SimpleGraph AlspachConjecture AlspachLift
open scoped Classical

/-- A packing of t base triples prescribes four triangles per chosen triple;
every edge outside the packing is covered by a four-cycle. -/
theorem realize_from_packing_count {m : ℕ} (hm : 0< m) (L : Multiset ℕ)
    (shape : ∀a∈L,a=3 ∨ a=4) (budget : L.sum=(2*m).choose 2-(2*m)/2)
    (packing : ∃ B : Fin (L.count 3/4) → Finset (Fin m),
      (∀ i, (B i).card=3) ∧ Pairwise (fun i j => Disjoint
        ((⊤ : SimpleGraph (Fin m)).edgeFinset.filter fun e => e.toFinset ⊆ B i)
        ((⊤ : SimpleGraph (Fin m)).edgeFinset.filter fun e => e.toFinset ⊆ B j))) :
    ∃ J : (completeGraph (Fin (2*m))).Subgraph, J.IsPerfectMatching ∧
      ∃ C : Multiset (Cycle (completeGraph (Fin (2*m)) \ J.spanningCoe)),
        IsCycleDecomposition _ C ∧ lengths C=L := by
  classical
  obtain ⟨t,lim,hL⟩ := classify_trades m hm L shape budget
  have ht : L.count 3/4=t := by
    rw [hL,Multiset.count_add]
    simp [Multiset.count_replicate,Nat.mul_comm 4 t]
  rw [ht] at packing
  obtain ⟨B,hB,disj⟩ := packing
  let f : (Fin m × Bool) ≃ Fin (2*m) := Fintype.equivOfCardEq (by simp; omega)
  obtain ⟨J,hJ,adj⟩ := AlspachSquares.pair_matching f
  let G := completeGraph (Fin (2*m)) \ J.spanningCoe
  let S (i : Fin t) := (⊤ : SimpleGraph (Fin m)).edgeFinset.filter fun e => e.toFinset ⊆ B i
  have across (i : Fin m) (a : Bool) (j : Fin m) (b : Bool) (ne : i≠j) :
      G.Adj (f (i,a)) (f (j,b)) := (adj _ _).mpr (by simpa using ne)
  have regions (i : Fin t) : ∃ C : Multiset (Cycle G), lengths C=Multiset.replicate 4 3 ∧ ∀ x y : Fin (2*m),
      (C.filter fun c => s(x,y) ∈ c.edges).card=if s((f.symm x).1,(f.symm y).1) ∈ S i then 1 else 0 :=
    region_of_three f G across (B i) (hB i)
  obtain ⟨q,C,hC,sizes⟩ := glue_triangles f G adj S disj regions
  refine ⟨J,hJ,C,hC,?_⟩
  have edgeCount := TriangleBridge.matching_budget J hJ
  rw [Fintype.card_fin] at edgeCount
  have sum : (lengths C).sum=L.sum := by
    rw [AlspachLadder.decomposition_budget C hC,budget]
    convert edgeCount using 1
    congr 1
    ext e
    simp only [mem_edgeFinset, G]
  rw [sizes,hL,Multiset.sum_add,Multiset.sum_add] at sum
  simp only [Multiset.sum_replicate,smul_eq_mul] at sum
  have hq : q=m.choose 2-3*t := by omega
  rw [sizes,hq,hL]

end AlspachTrades

namespace AlspachTrades
open Finset SimpleGraph AlspachConjecture
open scoped Classical

/-- A Steiner design or its puncturing gives a triangle/square decomposition
once the requested squares cover its leave. -/
theorem triangle_square_leave_lists {m : ℕ} (hm : 0< m)
    (I : (completeGraph (Fin (2*m))).Subgraph) (hI : I.IsPerfectMatching) (L : Multiset ℕ)
    (shape : ∀a∈L,a=3 ∨ a=4) (budget : L.sum=(2*m).choose 2-(2*m)/2)
    (enough : (if m%6=1 ∨ m%6=3 then 0 else if m%6=0 ∨ m%6=2 then m/2 else m-1) ≤ L.count 4) :
    ∃ C : Multiset (Cycle (completeGraph (Fin (2*m)) \ I.spanningCoe)),
      IsCycleDecomposition _ C ∧ lengths C=L := by
  have pack : ∃ B : Fin (L.count 3/4) → Finset (Fin m), (∀ i, (B i).card=3) ∧
      Pairwise (fun i j => Disjoint
        ((⊤ : SimpleGraph (Fin m)).edgeFinset.filter fun e => e.toFinset ⊆ B i)
        ((⊤ : SimpleGraph (Fin m)).edgeFinset.filter fun e => e.toFinset ⊆ B j)) := by
    by_cases h : m%6=1 ∨ m%6=3
    · exact triangle_packing m _ h (by simpa using enough_squares (leave:=0) hm L shape budget (Nat.zero_le _))
    rw [if_neg h] at enough
    by_cases he : m%6=0 ∨ m%6=2
    · rw [if_pos he] at enough
      exact triangle_packing_even m _ he (enough_squares hm L shape budget enough)
    rw [if_neg he] at enough
    have bound := enough_squares hm L shape budget enough
    by_cases hf : m%6=4
    · exact triangle_packing_four hf bound
    · exact triangle_packing_five m _ (by omega) bound
  obtain ⟨J,hJ,C,dec,len⟩ := realize_from_packing_count hm L shape budget pack
  obtain ⟨f⟩ := OMA.R_AlspachConjecture_alspach_conjecture_variants_even_R2.matchings_complements_iso J I hJ hI
  exact OMA.R_AlspachConjecture_alspach_conjecture_variants_even_R2.iso_decomposition f dec len

/-- At every even order 2m, m−1 squares suffice for every triangle/square list. -/
theorem triangle_square_with_squares {m : ℕ} (hm : 0< m)
    (I : (completeGraph (Fin (2*m))).Subgraph) (hI : I.IsPerfectMatching) (L : Multiset ℕ)
    (shape : ∀a∈L,a=3 ∨ a=4) (budget : L.sum=(2*m).choose 2-(2*m)/2) (enough : m-1≤L.count 4) :
    ∃ C : Multiset (Cycle (completeGraph (Fin (2*m)) \ I.spanningCoe)),
      IsCycleDecomposition _ C ∧ lengths C=L :=
  triangle_square_leave_lists hm I hI L shape budget (by split_ifs <;> omega)

end AlspachTrades

namespace AlspachTripartite
open Finset SimpleGraph AlspachConjecture
open scoped Classical

/-- Decompose precisely the edges crossing between three equally sized groups.
There are s² disjoint doubled triples. Each of the t selected triples yields
four triangles, and each unselected triple yields three squares. -/
theorem tripartite_trades {s : ℕ} {V : Type*} [DecidableEq V]
    (f : ((Fin 3 × Fin s) × Bool) ≃ V) (G : SimpleGraph V)
    (across : ∀ (i j : Fin 3 × Fin s) (a b : Bool), i.1≠j.1 → G.Adj (f (i,a)) (f (j,b)))
    (t : ℕ) (ht : t≤ s*s) :
    ∃ C : Multiset (Cycle G), lengths C = Multiset.replicate (4*t) 3 + Multiset.replicate (3*(s*s-t)) 4 ∧
      ∀ x y : V, (C.filter fun c => s(x,y)∈c.edges).card =
        if (f.symm x).1.1≠(f.symm y).1.1 then 1 else 0 := by
  classical
  let R := Fin 3 × Fin s
  let CoversRows (G : SimpleGraph V) (π : V → R) (S : Finset (Sym2 R))
      (L : Multiset ℕ) : Prop :=
    ∃ C : Multiset (Cycle G), lengths C = L ∧ ∀ x y : V,
      (C.filter fun c => s(x,y) ∈ c.edges).card = if s(π x,π y) ∈ S then 1 else 0
  have covers_empty (G : SimpleGraph V) (π : V → R) : CoversRows G π ∅ 0 := by
    refine ⟨0, rfl, ?_⟩
    simp
  have covers_union {G : SimpleGraph V} {π : V → R} {S T : Finset (Sym2 R)}
      {L M : Multiset ℕ} (hS : CoversRows G π S L) (hT : CoversRows G π T M) (hd : Disjoint S T) :
      CoversRows G π (S ∪ T) (L+M) := by
    obtain ⟨C,hC,hSc⟩ := hS
    obtain ⟨D,hD,hTc⟩ := hT
    refine ⟨C+D, ?_, ?_⟩
    · simpa only [lengths, Multiset.map_add] using congrArg₂ (· + ·) hC hD
    · intro x y
      rw [Multiset.filter_add, Multiset.card_add,hSc,hTc]
      by_cases hs : s(π x,π y) ∈ S
      · simp [hs, Finset.disjoint_left.mp hd hs]
      · simp [hs]
  have covers_many {ι : Type} [DecidableEq ι] {G : SimpleGraph V} {π : V → R}
      (I : Finset ι) (S : ι → Finset (Sym2 R)) (L : ι → Multiset ℕ)
      (family : ∀ i ∈ I, CoversRows G π (S i) (L i))
      (disj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (S i) (S j)) :
      CoversRows G π (I.biUnion S) (∑ i ∈ I, L i) := by
    induction I using Finset.induction_on with
    | empty => simpa using covers_empty G π
    | @insert i I hi ih =>
      rw [biUnion_insert,sum_insert hi]
      apply covers_union (family i (mem_insert_self ..))
      · exact ih (fun j hj => family j (mem_insert_of_mem hj))
          (fun j hj k hk => disj j (mem_insert_of_mem hj) k (mem_insert_of_mem hk))
      · apply Finset.disjoint_left.mpr
        intro e he he'
        obtain ⟨j,hj,hej⟩ := mem_biUnion.mp he'
        exact Finset.disjoint_left.mp (disj i (mem_insert_self ..) j (mem_insert_of_mem hj)
          (fun h => hi (h ▸ hj))) he hej
  have triangle_fibre (f : (R × Bool) ≃ V) (G : SimpleGraph V)
      (i j k : R) (hij : i≠j) (hik : i≠k) (hjk : j≠k)
      (ab : ∀ a b, G.Adj (f (i,a)) (f (j,b))) (bc : ∀ b d, G.Adj (f (j,b)) (f (k,d)))
      (ca : ∀ d a, G.Adj (f (k,d)) (f (i,a))) :
      CoversRows G (fun x => (f.symm x).1) {s(i,j),s(i,k),s(j,k)} (Multiset.replicate 4 3) := by
    classical
    let w (a b : Bool) : G.Walk (f (i,a)) (f (i,a)) :=
      .cons (ab a b) (.cons (bc b (a ^^ b)) (.cons (ca (a ^^ b) a) .nil))
    have simple (a b : Bool) : (w a b).IsCycle := by
      simp [w,Walk.isCycle_def,hij,hik,hjk,Ne.symm hij,Ne.symm hik]
    let c (a b : Bool) : Cycle G := ⟨f (i,a), w a b, simple a b⟩
    have length (a b : Bool) : (c a b).length=3 := rfl
    have edges (a b : Bool) (x y : R × Bool) :
        s(f x,f y) ∈ (c a b).edges ↔
        s(x,y)=s((i,a),(j,b)) ∨ s(x,y)=s((j,b),(k,a ^^ b)) ∨ s(x,y)=s((k,a ^^ b),(i,a)) := by
      change s(f x,f y) ∈ [s(f (i,a),f (j,b)),s(f (j,b),f (k,a ^^ b)),s(f (k,a ^^ b),f (i,a))] ↔ _
      simp only [List.mem_cons,List.not_mem_nil,or_false,Sym2.eq_iff,Equiv.apply_eq_iff_eq]
    let C := c false false ::ₘ c false true ::ₘ c true false ::ₘ c true true ::ₘ 0
    refine ⟨C,by simp [C,lengths,length,Multiset.replicate_succ],?_⟩
    intro X Y
    obtain ⟨⟨x,u⟩,rfl⟩ := f.surjective X
    obtain ⟨⟨y,v⟩,rfl⟩ := f.surjective Y
    simp only [Equiv.symm_apply_apply]
    by_cases h : s(x,y) ∈ ({s(i,j),s(i,k),s(j,k)} : Finset (Sym2 R))
    · rw [if_pos h]
      simp only [Finset.mem_insert,Finset.mem_singleton,Sym2.eq_iff] at h
      rcases h with (⟨rfl,rfl⟩|⟨rfl,rfl⟩) | (⟨rfl,rfl⟩|⟨rfl,rfl⟩) | (⟨rfl,rfl⟩|⟨rfl,rfl⟩)
      all_goals cases u <;> cases v <;>
        simp [C,Multiset.filter_singleton,edges,hij,hik,hjk,Ne.symm hij,Ne.symm hik,Ne.symm hjk]
    · rw [if_neg h]
      have none (a b : Bool) : s(f (x,u),f (y,v)) ∉ (c a b).edges := by
        intro he
        apply h
        rw [edges] at he
        simp only [Finset.mem_insert,Finset.mem_singleton,Sym2.eq_iff] at he ⊢
        simp only [Prod.mk.injEq] at he
        grind
      simp [C,Multiset.filter_singleton,none]
  have square_fibre
      (f : (R × Bool) ≃ V) (G : SimpleGraph V) (i j : R) (ne : i ≠ j)
      (adj : ∀ a b : Bool, G.Adj (f (i,a)) (f (j,b))) :
      ∃ C : Multiset (Cycle G), lengths C = {4} ∧ ∀ x y : V,
        (C.filter fun c => s(x,y) ∈ c.edges).card =
          if s((f.symm x).1,(f.symm y).1) = s(i,j) then 1 else 0 := by
    classical
    let w : G.Walk (f (i,false)) (f (i,false)) :=
      .cons (adj false false) (.cons (adj true false).symm
        (.cons (adj true true) (.cons (adj false true).symm .nil)))
    have cycle : w.IsCycle := by simp [w, Walk.isCycle_def, ne, ne.symm]
    let c : Cycle G := ⟨_,w,cycle⟩
    have exact_edges (x y : V) : s(x,y) ∈ c.edges ↔ s((f.symm x).1,(f.symm y).1) = s(i,j) := by
      obtain ⟨⟨r,a⟩,rfl⟩ := f.surjective x
      obtain ⟨⟨t,b⟩,rfl⟩ := f.surjective y
      change s(f (r,a), f (t,b)) ∈ [s(f (i,false), f (j,false)), s(f (j,false), f (i,true)),
        s(f (i,true),f (j,true)),s(f (j,true),f (i,false))] ↔ _
      simp only [Equiv.symm_apply_apply,Sym2.eq_iff]
      cases a <;> cases b <;> simp
      grind
    refine ⟨{c},?_,?_⟩
    · change {c.length} = ({4} : Multiset ℕ)
      rfl
    · intro x y
      change (Multiset.filter _ (c ::ₘ 0)).card = _
      rw [Multiset.filter_cons]
      by_cases h : s((f.symm x).1,(f.symm y).1) = s(i,j)
      · simp [h,(exact_edges x y).mpr h]
      · have no : s(x,y) ∉ c.edges := fun he => h ((exact_edges x y).mp he)
        simp [no,h]
  have three_square_fibre
      (f : (R × Bool) ≃ V) (G : SimpleGraph V) (i j k : R) (hij : i≠j) (hik : i≠k) (hjk : j≠k)
      (ab : ∀ a b, G.Adj (f (i,a)) (f (j,b))) (ac : ∀ a d, G.Adj (f (i,a)) (f (k,d)))
      (bc : ∀ b d, G.Adj (f (j,b)) (f (k,d))) :
      CoversRows G (fun x => (f.symm x).1) {s(i,j),s(i,k),s(j,k)} (Multiset.replicate 3 4) := by
    classical
    let π (x : V) := (f.symm x).1
    have single (r z : R) (ne : r≠z) (adj : ∀ a b, G.Adj (f (r,a)) (f (z,b))) :
        CoversRows G π {s(r,z)} {4} := by
      obtain ⟨C,len,count⟩ := square_fibre f G r z ne adj
      refine ⟨C,len,?_⟩
      intro x y
      simpa only [π,Finset.mem_singleton] using count x y
    have ij := single i j hij ab
    have ik := single i k hik ac
    have jk := single j k hjk bc
    have disj : Disjoint ({s(i,k)} : Finset (Sym2 R)) {s(j,k)} := by
      simp [hij,hik]
    have middle := covers_union ik jk disj
    have rest : Disjoint ({s(i,j)} : Finset (Sym2 R)) ({s(i,k)} ∪ {s(j,k)}) := by
      simp [hij,hik,hjk]
    have full := covers_union ij middle rest
    simpa only [Finset.singleton_union,Multiset.replicate_succ,Multiset.replicate_zero,
      Multiset.singleton_add,Multiset.cons_zero] using full
  have choose_block_trades {I : Type} [Fintype I]
      (G : SimpleGraph V) (π : V → R) (S : I → Finset (Sym2 R))
      (separate : Pairwise (fun i j => Disjoint (S i) (S j)))
      (triangles : ∀ i, CoversRows G π (S i) (Multiset.replicate 4 3))
      (squares : ∀ i, CoversRows G π (S i) (Multiset.replicate 3 4))
      (t : ℕ) (ht : t ≤ Fintype.card I) :
      CoversRows G π (univ.biUnion S)
        (Multiset.replicate (4*t) 3 + Multiset.replicate (3*(Fintype.card I-t)) 4) := by
    classical
    obtain ⟨T,_,size⟩ := exists_subset_card_eq (s:=univ) (by simpa using ht)
    let Q : Finset I := univ \ T
    have other : Q.card = Fintype.card I-t := by
      rw [show Q=univ \ T from rfl,card_sdiff_of_subset (subset_univ _),card_univ,size]
    have a := covers_many T S (fun _ => Multiset.replicate 4 3) (fun i _ => triangles i)
      (fun _ _ _ _ h => separate h)
    have b := covers_many Q S (fun _ => Multiset.replicate 3 4) (fun i _ => squares i)
      (fun _ _ _ _ h => separate h)
    simp only [sum_const,Multiset.nsmul_replicate,size,Nat.mul_comm t 4] at a
    simp only [sum_const,Multiset.nsmul_replicate,other,Nat.mul_comm (Fintype.card I-t) 3] at b
    have disj : Disjoint (T.biUnion S) (Q.biUnion S) := by
      apply Finset.disjoint_left.mpr
      intro e he hq
      obtain ⟨i,hi,ei⟩ := mem_biUnion.mp he
      obtain ⟨j,hj,ej⟩ := mem_biUnion.mp hq
      have ne : i≠j := fun eq => (mem_sdiff.mp hj).2 (eq ▸ hi)
      exact Finset.disjoint_left.mp (separate ne) ei ej
    have cover := covers_union a b disj
    have total : T ∪ Q=univ := by ext i; simp [Q]
    rwa [← union_biUnion,total] at cover
  let support (u : Fin s × Fin s) : Finset (Sym2 (Fin 3 × Fin s)) :=
    {s((0,u.1),(1,u.2)),s((0,u.1),(2,u.1+u.2)),s((1,u.2),(2,u.1+u.2))}
  have support_disjoint : Pairwise fun u v : Fin s × Fin s =>
      Disjoint (support u) (support v) := by
    rintro ⟨a,b⟩ ⟨c,d⟩ diff
    let : NeZero s := ⟨Nat.ne_of_gt (Nat.zero_lt_of_lt a.isLt)⟩
    apply Finset.disjoint_left.mpr
    intro e he₁ he₂
    apply diff
    rcases (show e = _ ∨ e = _ ∨ e = _ by simpa only [support,mem_insert,mem_singleton] using he₁)
      with rfl|rfl|rfl <;>
      simp only [support,mem_insert,mem_singleton,Sym2.eq_iff,Prod.mk.injEq] at he₂ <;>
      simp at he₂ <;> obtain ⟨h,k⟩ := he₂
    · exact Prod.ext h k
    · subst c; exact Prod.ext rfl (add_left_cancel k)
    · subst d; exact Prod.ext (add_right_cancel k) rfl
  have mem_union_iff (x y : Fin 3 × Fin s) :
      s(x,y) ∈ univ.biUnion support ↔ x.1 ≠ y.1 := by
    obtain ⟨i,a⟩ := x
    obtain ⟨j,b⟩ := y
    let : NeZero s := ⟨Nat.ne_of_gt (Nat.zero_lt_of_lt a.isLt)⟩
    constructor
    · intro he
      obtain ⟨⟨u,v⟩,_,hu⟩ := mem_biUnion.mp he
      simp only [support,mem_insert,mem_singleton,Sym2.eq_iff,Prod.mk.injEq] at hu
      grind
    · have first (x y : Fin s) :
          s(((0 : Fin 3),x),(1,y)) ∈ univ.biUnion support :=
        mem_biUnion.mpr ⟨(x,y),mem_univ _,by simp [support]⟩
      have second (x y : Fin s) :
          s(((0 : Fin 3),x),(2,y)) ∈ univ.biUnion support :=
        mem_biUnion.mpr ⟨(x,y-x),mem_univ _,by simp [support]⟩
      have third (x y : Fin s) :
          s(((1 : Fin 3),x),(2,y)) ∈ univ.biUnion support :=
        mem_biUnion.mpr ⟨(y-x,x),mem_univ _,by simp [support]⟩
      intro ne
      fin_cases i <;> fin_cases j <;>
        first | exact (ne rfl).elim | exact first _ _ | exact second _ _ | exact third _ _
              | exact Sym2.eq_swap ▸ first _ _ | exact Sym2.eq_swap ▸ second _ _
              | exact Sym2.eq_swap ▸ third _ _
  let S := support
  have rows (u : Fin s × Fin s) : S u = {s(((0 : Fin 3),u.1),((1 : Fin 3),u.2)),
      s(((0 : Fin 3),u.1),((2 : Fin 3),u.1+u.2)),s(((1 : Fin 3),u.2),((2 : Fin 3),u.1+u.2))} := rfl
  let π (x : V) := (f.symm x).1
  have options (u : Fin s × Fin s) :
      CoversRows G π (S u) (Multiset.replicate 4 3) ∧ CoversRows G π (S u) (Multiset.replicate 3 4) := by
    let i : Fin 3 × Fin s := (0,u.1)
    let j : Fin 3 × Fin s := (1,u.2)
    let k : Fin 3 × Fin s := (2,u.1+u.2)
    have hij : i.1 ≠ j.1 := (by decide : (0 : Fin 3) ≠ 1)
    have hik : i.1 ≠ k.1 := (by decide : (0 : Fin 3) ≠ 2)
    have hjk : j.1 ≠ k.1 := (by decide : (1 : Fin 3) ≠ 2)
    have ij : i≠j := fun h => hij (congrArg Prod.fst h)
    have ik : i≠k := fun h => hik (congrArg Prod.fst h)
    have jk : j≠k := fun h => hjk (congrArg Prod.fst h)
    rw [rows]
    exact ⟨triangle_fibre f G i j k ij ik jk (fun a b => across i j a b hij)
        (fun b d => across j k b d hjk) (fun d a => across k i d a hik.symm),
      three_square_fibre f G i j k ij ik jk (fun a b => across i j a b hij)
        (fun a d => across i k a d hik) (fun b d => across j k b d hjk)⟩
  have card : Fintype.card (Fin s × Fin s)=s*s := by simp
  obtain ⟨C,len,count⟩ := choose_block_trades G π S support_disjoint (fun u => (options u).1)
    (fun u => (options u).2) t (card ▸ ht)
  refine ⟨C,by simpa only [card] using len,fun x y => ?_⟩
  simpa only [S,mem_union_iff,π] using count x y

/-- On the complete tripartite graph the crossing family is a cycle decomposition. -/
theorem complete_tripartite_trades {s : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    (f : ((Fin 3 × Fin s) × Bool) ≃ V) (G : SimpleGraph V) [DecidableRel G.Adj]
    (adj : ∀ x y : V, G.Adj x y ↔ (f.symm x).1.1≠(f.symm y).1.1)
    (t : ℕ) (ht : t≤ s*s) :
    ∃ C : Multiset (Cycle G), IsCycleDecomposition G C ∧
      lengths C = Multiset.replicate (4*t) 3 + Multiset.replicate (3*(s*s-t)) 4 := by
  classical
  obtain ⟨C,len,count⟩ := tripartite_trades f G (fun i j a b ne => (adj _ _).mpr (by simpa using ne)) t ht
  refine ⟨C,?_,len⟩
  intro e
  induction e using Sym2.ind with
  | _ x y =>
    intro he
    have diff := (adj x y).mp (G.mem_edgeFinset.mp he)
    simpa only [if_pos diff] using count x y

end AlspachTripartite

namespace AlspachTripartite
open SimpleGraph AlspachConjecture Finset
open scoped Classical

/-- Three disjoint copies of one matched graph on W share the ambient vertex
set. The matching is replicated in each group, and so is the cycle decomposition. -/
theorem inner_copies {V W : Type*} [DecidableEq V] [Fintype W] [DecidableEq W]
    (e : (Fin 3 × W) ≃ V) (I : (completeGraph W).Subgraph) (perfect : I.IsPerfectMatching)
    (C : Multiset (Cycle (completeGraph W \ I.spanningCoe)))
    (DC : IsCycleDecomposition _ C) (u : ℕ) (sizes : lengths C=Multiset.replicate u 3) :
    ∃ J : (completeGraph V).Subgraph, J.IsPerfectMatching ∧
      (∀ x y : V,(e.symm x).1≠(e.symm y).1 → (completeGraph V \ J.spanningCoe).Adj x y) ∧
      ∃ (q : ℕ) (D : Multiset (Cycle (completeGraph V \ J.spanningCoe))),
        lengths D=Multiset.replicate q 3 ∧ ∀ x y : V,(completeGraph V \ J.spanningCoe).Adj x y →
          (D.filter (fun v => s(x,y)∈v.edges)).card = if (e.symm x).1=(e.symm y).1 then 1 else 0 := by
  classical
  let J : (completeGraph V).Subgraph :=
    { verts := Set.univ
      Adj := fun x y => (e.symm x).1=(e.symm y).1 ∧ I.Adj (e.symm x).2 (e.symm y).2
      adj_sub := fun h xy => I.adj_sub h.2 (congrArg (fun z => (e.symm z).2) xy)
      edge_vert := fun _ => Set.mem_univ _
      symm := ⟨fun _ _ h => ⟨h.1.symm,h.2.symm⟩⟩ }
  have jp : J.IsPerfectMatching := by
    apply Subgraph.isPerfectMatching_iff.mpr
    intro x
    obtain ⟨b,adj,unique⟩ := Subgraph.isPerfectMatching_iff.mp perfect (e.symm x).2
    refine ⟨e ((e.symm x).1,b), ?_, ?_⟩
    · change _=(e.symm (e _)).1 ∧ I.Adj _ (e.symm (e _)).2
      rw [e.symm_apply_apply]
      exact ⟨rfl,adj⟩
    · rintro z ⟨hz,hb⟩
      apply e.symm.injective
      rw [e.symm_apply_apply]
      exact Prod.ext hz.symm (unique _ hb)
  let G := completeGraph V \ J.spanningCoe
  let F := completeGraph W \ I.spanningCoe
  have adj (x y : V) : G.Adj x y ↔ x≠y ∧
      ¬((e.symm x).1=(e.symm y).1 ∧ I.Adj (e.symm x).2 (e.symm y).2) := Iff.rfl
  have same (g : Fin 3) (a b : W) : G.Adj (e (g,a)) (e (g,b)) ↔ F.Adj a b := by
    change _ ↔ a≠b ∧ ¬I.Adj a b
    simp [adj,ne_eq]
  have cross (x y : V) (nn : (e.symm x).1≠(e.symm y).1) : G.Adj x y :=
    (adj _ _).mpr ⟨fun h => nn (congrArg (fun z => (e.symm z).1) h),fun k => nn k.1⟩
  let inc (g : Fin 3) : F →g G := ⟨fun x => e (g,x),fun h => (same g _ _).mpr h⟩
  have inj (g) : Function.Injective (inc g) := fun a b h => congrArg Prod.snd (e.injective h)
  let move (g : Fin 3) (c : Cycle F) : Cycle G := ⟨_,c.walk.map (inc g),c.isCycle.map (inj g)⟩
  have mem (k i j : Fin 3) (a b : W) (c : Cycle F) :
      s(e (i,a),e (j,b)) ∈ (move k c).edges ↔ i=k ∧ j=k ∧ s(a,b)∈c.edges := by
    change _ ∈ (c.walk.map (inc k)).edges ↔ _
    rw [Walk.edges_map,List.mem_map]
    constructor
    · rintro ⟨edge,hit,eq⟩
      induction edge using Sym2.ind with
      | h x y =>
        change s(e (k,x), e (k,y))=s(e (i,a),e (j,b)) at eq
        rcases Sym2.eq_iff.mp eq with ⟨hx,hy⟩|⟨hx,hy⟩
        · obtain ⟨rfl,rfl⟩ := Prod.mk.inj (e.injective hx)
          obtain ⟨_,rfl⟩ := Prod.mk.inj (e.injective hy)
          exact ⟨rfl,(congrArg Prod.fst (e.injective hy)).symm,hit⟩
        · obtain ⟨rfl,rfl⟩ := Prod.mk.inj (e.injective hx)
          obtain ⟨_,rfl⟩ := Prod.mk.inj (e.injective hy)
          refine ⟨(congrArg Prod.fst (e.injective hy)).symm,rfl,?_⟩
          rw [Sym2.eq_swap]; exact hit
    · rintro ⟨rfl,rfl,h⟩
      exact ⟨s(a,b),h,rfl⟩
  let part (g : Fin 3) := C.map (move g)
  have part_len (g) : lengths (part g)=Multiset.replicate u 3 := by
    have len (c : Cycle F) : (move g c).length = c.length := Walk.length_map _ _
    simpa [part,lengths,Multiset.map_map,Function.comp_def,len] using sizes
  have part_count (k i j : Fin 3) (a b : W) (d : DecidablePred
      (fun c : Cycle G => s(e (i,a),e (j,b))∈c.edges)) :
      (@Multiset.filter _ (fun c => s(e (i,a),e (j,b))∈c.edges) d (part k)).card =
        if i=k ∧ j=k then (C.filter (fun c => s(a,b)∈c.edges)).card else 0 := by
    simp only [part,Multiset.filter_map,Multiset.card_map,Function.comp_def]
    by_cases h : i=k ∧ j=k
    · rw [if_pos h]
      exact congrArg Multiset.card (Multiset.filter_congr (fun c _ =>
        by simpa [h.1,h.2] using mem k i j a b c))
    · have no (c : Cycle F) : s(e (i,a),e (j,b))∉(move k c).edges :=
        fun h' => h ⟨((mem _ _ _ _ _ _).mp h').1,((mem _ _ _ _ _ _).mp h').2.1⟩
      simp [h,no]
  let D := part 0 + part 1 + part 2
  refine ⟨J,jp,cross,u+u+u,D,?_,?_⟩
  · change lengths (part 0+part 1+part 2)=_
    simp only [lengths,Multiset.map_add] at part_len ⊢
    rw [part_len,part_len,part_len,Multiset.replicate_add,Multiset.replicate_add]
  · intro x y hxy
    obtain ⟨⟨i,a⟩,rfl⟩ := e.surjective x
    obtain ⟨⟨j,b⟩,rfl⟩ := e.surjective y
    simp only [D,Multiset.filter_add,Multiset.card_add,e.symm_apply_apply]
    have one (eq : i=j) : (C.filter (fun c => s(a,b)∈c.edges)).card=1 := by
      subst j
      apply Eq.trans _ (DC s(a,b) ?_)
      · exact congrArg Multiset.card (Multiset.filter_congr (fun c _ => Iff.rfl))
      · refine (@SimpleGraph.mem_edgeFinset W F s(a,b) ?_).mpr ?_
        exact (same i a b).mp hxy
    have eval (i j : Fin 3) (N : ℕ) :
        (if i=0 ∧ j=0 then N else 0) + (if i=1 ∧ j=1 then N else 0) +
          (if i=2 ∧ j=2 then N else 0) = if i=j then N else 0 := by
      fin_cases i <;> fin_cases j <;> simp
    refine Eq.trans (congrArg₂ Nat.add (congrArg₂ Nat.add
      (part_count 0 i j a b _) (part_count 1 i j a b _)) (part_count 2 i j a b _)) ?_
    refine Eq.trans (eval i j _) ?_
    split_ifs with h
    · exact one h
    · rfl

end AlspachTripartite

namespace AlspachTripartite
open SimpleGraph AlspachConjecture
open scoped Classical

/-- Use triangle-only local designs in the three groups of size 2s. The union
covers every edge within a group and leaves all cross-group edges available. -/
theorem inner_triangles (s : ℕ) (hs : 0<s) (residue : (2*s)%6=0 ∨ (2*s)%6=2)
    (f : ((Fin 3 × Fin s) × Bool) ≃ Fin (6*s)) :
    ∃ J : (completeGraph (Fin (6*s))).Subgraph, J.IsPerfectMatching ∧
      (∀ x y : Fin (6*s),(f.symm x).1.1≠(f.symm y).1.1 →
        (completeGraph (Fin (6*s)) \ J.spanningCoe).Adj x y) ∧
      ∃ (q : ℕ) (D : Multiset (Cycle (completeGraph (Fin (6*s)) \ J.spanningCoe))),
        lengths D=Multiset.replicate q 3 ∧
        ∀ x y : Fin (6*s),(completeGraph (Fin (6*s)) \ J.spanningCoe).Adj x y →
          (D.filter (fun v => s(x,y)∈v.edges)).card = if (f.symm x).1.1=(f.symm y).1.1 then 1 else 0 := by
  classical
  let n := 2*s
  let budget := n.choose 2-n/2
  have hn : 2*(s-1)+2=n := by dsimp [n]; omega
  have eq : budget = (s-1)*(2*s) := by
    have z := AlspachEvenHamilton.even_budget (s-1)
    rw [hn] at z
    exact z
  have dvd : 3∣budget := by
    rw [eq]
    rcases residue with h|h
    · exact dvd_mul_of_dvd_right (show 3∣2*s by omega) _
    · exact dvd_mul_of_dvd_left (show 3∣s-1 by omega) _
  obtain ⟨u,hu⟩ := dvd
  let m := Multiset.replicate u 3
  have length_budget : m.sum=n.choose 2-n/2 := by
    change (Multiset.replicate u 3).sum=budget
    rw [Multiset.sum_replicate,smul_eq_mul,hu,Nat.mul_comm]
  obtain ⟨I,perfect,C,dc,sizes⟩ := AlspachTriple.all_triangles n
    (show Even (2*s) from ⟨s,by omega⟩) m (fun _ hx => Multiset.eq_of_mem_replicate hx) length_budget
  let labels : (Fin s × Bool) ≃ Fin n := Fintype.equivFinOfCardEq (by
    simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool]; dsimp [n]; omega)
  let e := (((Equiv.refl (Fin 3)).prodCongr labels.symm).trans
    (Equiv.prodAssoc (Fin 3) (Fin s) Bool).symm).trans f
  exact inner_copies e I perfect C dc u sizes

end AlspachTripartite

namespace AlspachTripartite

/-- Splitting off one factor of three from the order leaves an edge budget
divisible by three, so the square multiplicity is a multiple of three. -/
theorem square_count_multiple (s : ℕ) (hs : 0<s) (L : Multiset ℕ)
    (shape : ∀ a∈L,a=3 ∨ a=4) (budget : L.sum=(6*s).choose 2-(6*s)/2) :
    3 ∣ L.count 4 := by
  have formula : 2*((3*s).choose 2)=(3*s)*(3*s-1) := by
    obtain ⟨k,hk⟩ : ∃ k,3*s=k+1 := ⟨3*s-1,by omega⟩
    rw [hk,Nat.add_sub_cancel]
    simpa [Nat.mul_comm] using (Nat.add_one_mul_choose_eq k 1).symm
  have div3 : 3 ∣ (3*s).choose 2 := by
    have h : 2*((3*s).choose 2)=3*(s*(3*s-1)) := by rw [formula,Nat.mul_assoc]
    exact ⟨(3*s).choose 2/3, by omega⟩
  have order : 6*s=2*(3*s) := by omega
  rw [order] at budget
  obtain ⟨t,lim,eq⟩ := AlspachTrades.classify_trades (3*s) (by omega) L shape budget
  have num : L.count 4=(3*s).choose 2-3*t := by simp [eq,Multiset.count_replicate]
  obtain ⟨k,hk⟩ := div3
  exact ⟨L.count 4/3,by omega⟩

/-- For an admissible triangle/square list, its square count and total length
determine the multiplicity of triangles. -/
theorem match_list {L : Multiset ℕ} (shape : ∀ a∈L,a=3 ∨ a=4) {a q : ℕ}
    (hq : q=L.count 4) (sum : (Multiset.replicate a 3+Multiset.replicate q 4).sum=L.sum) :
    Multiset.replicate a 3+Multiset.replicate q 4=L := by
  have filt : L.filter (fun x => ¬ x=3) = Multiset.replicate (L.count 4) 4 := by
    rw [←Multiset.filter_eq']
    apply Multiset.filter_congr
    intro x hx
    rcases shape x hx with rfl|rfl <;> decide
  have split := Multiset.filter_add_not (fun x => x=3) L
  rw [filt,Multiset.filter_eq'] at split
  have sum' := congrArg Multiset.sum split
  simp only [Multiset.sum_add,Multiset.sum_replicate,smul_eq_mul] at sum sum'
  simpa only [hq,show a=L.count 3 by omega] using split

/-- Up to the leave threshold, the cross-group octahedra supply every eligible
square count. -/
theorem small_cross_square {s q : ℕ} (hs : 0<s) (small : q < (3*s)/2)
    (three : 3∣q) : ∃ t, t≤ s*s ∧ 3*(s*s-t)=q := by
  obtain ⟨k,rfl⟩ := three
  have h1 : s≤ s*s := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left s hs
  exact ⟨s*s-k,by omega,by omega⟩

end AlspachTripartite

namespace AlspachTripartite
open Finset SimpleGraph AlspachConjecture
open scoped Classical

/-- Fill the three parts with triangles, then use Latin-square octahedra between
the parts for the prescribed number of four-cycles. -/
theorem join_three {s n : ℕ} (f : ((Fin 3 × Fin s) × Bool) ≃ Fin n)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (across : ∀ x y, (f.symm x).1.1 ≠ (f.symm y).1.1 → G.Adj x y)
    {h : ℕ} (inner : Multiset (Cycle G)) (insideLengths : lengths inner=Multiset.replicate h 3)
    (inside : ∀ x y, G.Adj x y → (inner.filter fun c => s(x,y)∈c.edges).card =
      if (f.symm x).1.1=(f.symm y).1.1 then 1 else 0)
    (L : Multiset ℕ) (shape : ∀ a∈L,a=3 ∨ a=4) (budget : L.sum=G.edgeFinset.card)
    {t : ℕ} (ht : t≤ s*s) (target : 3*(s*s-t)=L.count 4) :
    ∃ C : Multiset (Cycle G), IsCycleDecomposition G C ∧ lengths C=L := by
  obtain ⟨outer,outLengths,outside⟩ := tripartite_trades f G (fun i j a b ne =>
    across _ _ (by simpa using ne)) t ht
  have dec : IsCycleDecomposition G (inner+outer) := by
    intro edge
    induction edge using Sym2.ind with
    | _ x y =>
      intro he
      have adj := G.mem_edgeFinset.mp he
      rw [Multiset.filter_add,Multiset.card_add,inside x y adj,outside x y]
      by_cases same : (f.symm x).1.1=(f.symm y).1.1 <;> simp [same]
  have lengthsAll : lengths (inner+outer) =
      Multiset.replicate (h+4*t) 3+Multiset.replicate (3*(s*s-t)) 4 := by
    rw [show lengths (inner+outer)=lengths inner+lengths outer by exact Multiset.map_add ..,
      insideLengths,outLengths,←add_assoc,←Multiset.replicate_add]
  refine ⟨inner+outer,dec,lengthsAll.trans (match_list shape target ?_)⟩
  rw [←lengthsAll,AlspachLadder.decomposition_budget _ dec,budget]

/-- Three equally sized triangle-filled parts handle the triangle-rich end;
the single-puncture construction covers the square-rich end. -/
theorem all_lists_of_inner {s : ℕ} (hs : 0<s) (even : Even s)
    (I : (completeGraph (Fin (6*s))).Subgraph) (hI : I.IsPerfectMatching) (L : Multiset ℕ)
    (shape : ∀a∈L,a=3 ∨ a=4) (budget : L.sum=(6*s).choose 2-(6*s)/2)
    (fill : ∀ f : ((Fin 3 × Fin s) × Bool) ≃ Fin (6*s),
      ∃ J : (completeGraph (Fin (6*s))).Subgraph, J.IsPerfectMatching ∧
        (∀ x y, (f.symm x).1.1≠(f.symm y).1.1 → (completeGraph (Fin (6*s)) \ J.spanningCoe).Adj x y) ∧
        ∃ (u : ℕ) (D : Multiset (Cycle (completeGraph (Fin (6*s)) \ J.spanningCoe))),
          lengths D=Multiset.replicate u 3 ∧ ∀ x y, (completeGraph (Fin (6*s)) \ J.spanningCoe).Adj x y →
            (D.filter fun c => s(x,y)∈c.edges).card=if (f.symm x).1.1=(f.symm y).1.1 then 1 else 0) :
    ∃ C : Multiset (Cycle (completeGraph (Fin (6*s)) \ I.spanningCoe)), IsCycleDecomposition _ C ∧ lengths C=L := by
  classical
  by_cases high : (3*s)/2 ≤ L.count 4
  · have aux (n : ℕ) (hn : n=2*(3*s)) (J : (completeGraph (Fin n)).Subgraph)
        (hJ : J.IsPerfectMatching) (bud : L.sum=n.choose 2-n/2) :
        ∃ C : Multiset (Cycle (completeGraph (Fin n) \ J.spanningCoe)), IsCycleDecomposition _ C ∧ lengths C=L := by
      subst n
      obtain ⟨k,hk⟩ := even
      have d : (3*s)%6=0 := by omega
      exact AlspachTrades.triangle_square_leave_lists (by omega) J hJ L shape bud (by simpa [d] using high)
    exact aux (6*s) (by omega) I hI budget
  · obtain ⟨t,lim,sq⟩ := small_cross_square hs (Nat.lt_of_not_ge high) (square_count_multiple s hs L shape budget)
    let f : ((Fin 3 × Fin s) × Bool) ≃ Fin (6*s) := Fintype.equivOfCardEq (by simp; omega)
    obtain ⟨J,hJ,across,u,D,lenD,inside⟩ := fill f
    let G := completeGraph (Fin (6*s)) \ J.spanningCoe
    have ecount := TriangleBridge.matching_budget J hJ
    rw [Fintype.card_fin] at ecount
    obtain ⟨C,dec,sz⟩ := join_three f G across D lenD inside L shape (by
      rw [budget]
      convert ecount.symm using 1
      congr 1
      ext e
      simp only [mem_edgeFinset,G]) lim sq
    obtain ⟨iso⟩ := OMA.R_AlspachConjecture_alspach_conjecture_variants_even_R2.matchings_complements_iso J I hJ hI
    exact OMA.R_AlspachConjecture_alspach_conjecture_variants_even_R2.iso_decomposition iso dec sz

end AlspachTripartite

namespace AlspachTripartite
open SimpleGraph AlspachConjecture
open scoped Classical

/-- In these two residue classes the complete tripartite construction fills the
entire gap below the punctured design's square threshold. -/
theorem triangle_square_0_24_mod36 (n : ℕ) (residue : n%36=0 ∨ n%36=24) (positive : 0<n)
    (I : (completeGraph (Fin n)).Subgraph) (hI : I.IsPerfectMatching) (L : Multiset ℕ)
    (shape : ∀a∈L,a=3 ∨ a=4) (budget : L.sum=n.choose 2-n/2) :
    ∃ C : Multiset (Cycle (completeGraph (Fin n) \ I.spanningCoe)), IsCycleDecomposition _ C ∧ lengths C=L := by
  obtain ⟨s,hs,rfl⟩ : ∃ s, 0<s ∧ n=6*s := ⟨n/6,by omega,by omega⟩
  have even : Even s := ⟨s/2,by omega⟩
  have localOrder : (2*s)%6=0 ∨ (2*s)%6=2 := by omega
  exact all_lists_of_inner hs even I hI L shape budget (inner_triangles s hs localOrder)

end AlspachTripartite

namespace AlspachShared
open Finset SimpleGraph

/-- Bose's nonvertical triples on an odd number of groups of size three.
Two distinct group labels determine a unique block through any two points. -/
theorem bose_cross {u : ℕ} (odd : Odd u) :
    ∃ B : Fin (3 * u.choose 2) → Finset (Fin u × Fin 3),
      (∀ i, (B i).card = 3) ∧
      (∀ i x y, x ∈ B i → y ∈ B i → x ≠ y → x.1 ≠ y.1) ∧
      ∀ x y : Fin u × Fin 3, x.1 ≠ y.1 → ∃! i, x ∈ B i ∧ y ∈ B i := by
  classical
  obtain ⟨k,rfl⟩ := odd
  let u := 2*k+1
  obtain ⟨op,comm,latin,diag⟩ := AlspachTriple.odd_latin k
  obtain ⟨F,three,avoids,covers⟩ := AlspachTriple.latin_blocks op comm latin (fun _ => False) (by simp)
  let V := Fin u × Fin 3
  let I := {b // F b}
  let : Fintype I := Fintype.ofFinite _
  let block (i : I) := i.val
  have orient : ∀ a b : Fin 3, a ≠ b → b=a+1 ∨ a=b+1 := by decide
  have separate (i : I) (x y : V) (hx : x∈block i) (hy : y∈block i) (hne : x≠y) : x.1≠y.1 := by
    intro same
    have dist : x.2 ≠ y.2 := fun h => hne (Prod.ext same h)
    have skip := avoids i.val i.property x hx y hy
    rcases orient _ _ dist with a|a
    · exact skip (Or.inl ⟨not_false, a, (diag _).symm ▸ same.symm⟩)
    · exact skip (Or.inr ⟨not_false, a, (diag _).symm ▸ same⟩)
  have cover (x y : V) (hd : x.1≠y.1) : ∃! i : I, x∈block i ∧ y∈block i := by
    apply covers x y (fun eq => hd (congrArg Prod.fst eq))
    rintro (⟨_,_,h⟩|⟨_,_,h⟩) <;> rw [diag] at h
    · exact hd h.symm
    · exact hd h
  let H : SimpleGraph V := (⊤ : SimpleGraph (Fin u)).comap Prod.fst
  let : DecidableRel H.Adj := Classical.decRel _
  obtain ⟨_,_,_,edgeCount⟩ := TriangleBridge.blocks_in_graph H block (fun i => three i.val i.property)
    (fun i x hx y hy hd => separate i x y hx hy hd) cover
  have degrees (v : V) : H.degree v = (u-1)*3 := by
    have eq : H.neighborFinset v = (univ.erase v.1) ×ˢ (univ : Finset (Fin 3)) := by
      ext w
      rw [mem_neighborFinset, mem_product, mem_erase]
      change v.1 ≠ w.1 ↔ _
      simp [ne_comm]
    rw [← card_neighborFinset_eq_degree,eq,card_product,card_erase_of_mem (mem_univ _)]
    simp
  have size := H.sum_degrees_eq_twice_card_edges
  simp_rw [degrees] at size
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at size
  have allCard : Fintype.card V = u*3 := by simp [V]
  rw [allCard,edgeCount] at size
  have hchoose : (2*k+1).choose 2 = (2*k+1)*k := by
    rw [Nat.choose_two_right,show 2*k+1-1=2*k by omega]
    rw [show (2*k+1)*(2*k)=2*((2*k+1)*k) by ring]
    exact Nat.mul_div_cancel_left _ (by decide)
  have card : Fintype.card I = 3 * (2*k+1).choose 2 := by
    rw [hchoose]
    change (2*k+1)*3*((2*k+1-1)*3)=2*(Fintype.card I*3) at size
    rw [show 2*k+1-1=2*k by omega] at size
    have eq : (3*((2*k+1)*k))*6 = Fintype.card I*6 := by
      calc _ = (2*k+1)*3*(2*k*3) := by ring
           _ = 2*(Fintype.card I*3) := size
           _ = _ := by ring
    omega
  let number : I ≃ Fin (3*((2*k+1).choose 2)) := Fintype.equivFinOfCardEq card
  refine ⟨fun i => block (number.symm i),fun i => three _ (number.symm i).property,
    fun i x y hx hy hne => separate _ _ _ hx hy hne,?_⟩
  intro x y hxy
  obtain ⟨i,hit,uniq⟩ := cover x y hxy
  refine ⟨number i,by simpa using hit,fun j hj => number.symm.injective ?_⟩
  simpa using uniq (number.symm j) hj

end AlspachShared

namespace AlspachShared

/-- The shared hole and each outer group split into pairs. Outside the seed,
both endpoints belong to outer positions in distinct groups. -/
theorem pair_chart_data (u : ℕ) :
    let V := Fin 4 ⊕ (Fin u × Fin 6)
    let R := Fin 2 ⊕ (Fin u × Fin 3)
    let pairRow : V → R
      | .inl x => .inl ⟨x.val/2,by have := x.isLt; omega⟩
      | .inr (g,x) => .inr (g,⟨x.val/2,by have := x.isLt; omega⟩)
    let seedRegion : V → V → Prop
      | .inr (g,_), .inr (h,_) => g=h
      | _, _ => True
    (∃ k : V ≃ R × Bool, ∀ x, (k x).1=pairRow x) ∧
    (∀ x y : V, ¬seedRegion x y ↔
       ∃ a b : Fin u × Fin 3, pairRow x=Sum.inr a ∧ pairRow y=Sum.inr b ∧ a.1≠b.1) := by
  intro V R pairRow seedRegion
  constructor
  ·
    let f (j : Fin 4) : Fin 2 × Bool :=
      (⟨j.val/2, by have := j.isLt; omega⟩,decide (j.val%2=1))
    let g (j : Fin 6) : Fin 3 × Bool :=
      (⟨j.val/2, by have := j.isLt; omega⟩,decide (j.val%2=1))
    have bf : Function.Bijective f := by
      show (∀ x y, f x=f y → x=y) ∧ ∀ y, ∃ x, f x=y
      decide +kernel
    have bg : Function.Bijective g := by
      show (∀ x y, g x=g y → x=y) ∧ ∀ y, ∃ x, g x=y
      decide +kernel
    let h := (Equiv.prodCongr (Equiv.refl (Fin u)) (Equiv.ofBijective g bg)).trans
      (Equiv.prodAssoc (Fin u) (Fin 3) Bool).symm
    let k := (Equiv.sumCongr (Equiv.ofBijective f bf) h).trans
      (Equiv.sumProdDistrib (Fin 2) (Fin u × Fin 3) Bool).symm
    refine ⟨k, ?_⟩
    rintro (h | ⟨g,j⟩) <;> rfl
  · intro x y
    rcases x with x | ⟨g,x⟩ <;> rcases y with y | ⟨h,y⟩ <;> simp [seedRegion,pairRow,R]

end AlspachShared

namespace AlspachShared
open SimpleGraph Finset AlspachConjecture
open scoped Classical

/-- The hole square and twelve triangles per group cover all allowed edges internal to a group or incident to the hole. -/
theorem seed_family {u n : ℕ} (f : (Fin 4 ⊕ (Fin u × Fin 6)) ≃ Fin n) (G : SimpleGraph (Fin n)) :
    let pairRow : (Fin 4 ⊕ (Fin u × Fin 6)) → (Fin 2 ⊕ (Fin u × Fin 3))
      | .inl x => .inl ⟨x.val/2,by have := x.isLt; omega⟩
      | .inr (g,x) => .inr (g,⟨x.val/2,by have := x.isLt; omega⟩)

    let seedRegion : (Fin 4 ⊕ (Fin u × Fin 6)) → (Fin 4 ⊕ (Fin u × Fin 6)) → Prop
      | .inr (g,_), .inr (h,_) => g=h
      | _, _ => True
    (∀ x y, G.Adj (f x) (f y) ↔ pairRow x ≠ pairRow y) →
    ∃ C : Multiset (Cycle G), lengths C = {4} + Multiset.replicate (12*u) 3 ∧
      ∀ x y, (C.filter fun c => s(f x,f y) ∈ c.edges).card =
        if pairRow x ≠ pairRow y ∧ seedRegion x y then 1 else 0 := by
  classical
  intro pairRow seedRegion adj
  let triangleTable (t : Fin 12) : Fin 4 × Fin 6 × Fin 6 :=
    match t.val with
    | 0 => (0,0,2) | 1 => (0,1,4) | 2 => (0,3,5)
    | 3 => (1,0,4) | 4 => (1,2,5) | 5 => (1,1,3)
    | 6 => (2,0,5) | 7 => (2,4,3) | 8 => (2,2,1)
    | 9 => (3,0,3) | 10 => (3,5,1) | _ => (3,4,2)
  let acrossHit (t : Fin 12) (h : Fin 4) (x : Fin 6) : Bool :=
    h == (triangleTable t).1 && (x == (triangleTable t).2.1 || x == (triangleTable t).2.2)
  let withinHit (t : Fin 12) (x y : Fin 6) : Bool :=
    ((x == (triangleTable t).2.1) && (y == (triangleTable t).2.2)) ||
    ((y == (triangleTable t).2.1) && (x == (triangleTable t).2.2))
  have table_certified :
      (∀ t, (triangleTable t).2.1.val/2 ≠ (triangleTable t).2.2.val/2) ∧
      (∀ h x, (univ.filter (fun t => acrossHit t h x)).card = 1) ∧
      (∀ x y, (univ.filter (fun t => withinHit t x y)).card =
        if x.val/2 ≠ y.val/2 then 1 else 0) := by
    dsimp only [acrossHit,withinHit,triangleTable]
    decide +kernel
  let hits (g : Fin u) (t : Fin 12) : (Fin 4 ⊕ (Fin u × Fin 6)) → (Fin 4 ⊕ (Fin u × Fin 6)) → Bool
    | .inl _, .inl _ => false
    | .inl h, .inr (k,x) | .inr (k,x), .inl h => (k == g) && acrossHit t h x
    | .inr (k,x), .inr (j,y) => (k == g) && (j == g) && withinHit t x y
  let groupCount (g : Fin u) : (Fin 4 ⊕ (Fin u × Fin 6)) → (Fin 4 ⊕ (Fin u × Fin 6)) → ℕ
    | .inl _, .inl _ => 0
    | .inl _, .inr (k,_) | .inr (k,_), .inl _ => if k=g then 1 else 0
    | .inr (k,x), .inr (j,y) => if k=g ∧ j=g ∧ x.val/2 ≠ y.val/2 then 1 else 0
  have group_family (g : Fin u) :
      ∃ C : Multiset (Cycle G), lengths C = Multiset.replicate 12 3 ∧ ∀ x y : (Fin 4 ⊕ (Fin u × Fin 6)),
        (C.filter fun c => s(f x,f y) ∈ c.edges).card = groupCount g x y := by
    classical
    let a (t : Fin 12) : (Fin 4 ⊕ (Fin u × Fin 6)) := .inl (triangleTable t).1
    let b (t : Fin 12) : (Fin 4 ⊕ (Fin u × Fin 6)) := .inr (g,(triangleTable t).2.1)
    let d (t : Fin 12) : (Fin 4 ⊕ (Fin u × Fin 6)) := .inr (g,(triangleTable t).2.2)
    have bd (t : Fin 12) : G.Adj (f (b t)) (f (d t)) := (adj _ _).mpr (by
      simp [b,d,pairRow, Fin.ext_iff, table_certified.1 t])
    let w (t : Fin 12) : G.Walk (f (a t)) (f (a t)) :=
      .cons ((adj _ _).mpr (by simp [a,b,pairRow])) (.cons (bd t)
        (.cons ((adj _ _).mpr (by simp [d,a,pairRow])) .nil))
    have simple (t : Fin 12) : (w t).IsCycle := by
      have diff := (bd t).ne
      simp [w,Walk.isCycle_def,a,b,d] at diff ⊢
      aesop
    let c (t : Fin 12) : Cycle G := ⟨_,w t,simple t⟩
    have mem (t : Fin 12) (x y : (Fin 4 ⊕ (Fin u × Fin 6))) : s(f x,f y) ∈ (c t).edges ↔ hits g t x y := by
      change s(f x,f y) ∈ [s(f (a t),f (b t)),s(f (b t),f (d t)),s(f (d t),f (a t))] ↔ _
      cases x with
      | inl i => cases y with
        | inl j => simp [a,b,d,hits]
        | inr p => rcases p with ⟨j,k⟩; simp [a,b,d,hits,acrossHit]; tauto
      | inr p =>
        obtain ⟨i,h⟩ := p
        cases y with
        | inl j => simp [a,b,d,hits,acrossHit]; tauto
        | inr p => rcases p with ⟨j,k⟩; simp [a,b,d,hits,withinHit]; tauto
    refine ⟨(univ : Finset (Fin 12)).val.map c,?_,?_⟩
    · rw [lengths,Multiset.map_map,show SimpleGraph.Cycle.length ∘ c = fun _ => 3 from rfl,Multiset.map_const']
      simp
    · intro x y
      rw [Multiset.filter_map,Multiset.card_map]
      change (univ.filter (fun t => s(f x,f y) ∈ (c t).edges)).card = _
      simp only [mem]
      cases x with
      | inl h => cases y with
        | inl h' => simp [hits,groupCount]
        | inr p => rcases p with ⟨j,k⟩; by_cases eq : j=g <;> simp [hits,groupCount,eq,table_certified.2.1]
      | inr p =>
        obtain ⟨i,j⟩ := p
        cases y with
        | inl h => by_cases eq : i=g <;> simp [hits,groupCount,eq,table_certified.2.1]
        | inr p =>
          obtain ⟨k,l⟩ := p
          by_cases eq : i=g <;> by_cases eq' : k=g <;> simp [hits,groupCount,eq,eq',table_certified.2.2]
  let holeCount : (Fin 4 ⊕ (Fin u × Fin 6)) → (Fin 4 ⊕ (Fin u × Fin 6)) → ℕ
    | .inl h, .inl k => if h.val/2≠k.val/2 then 1 else 0
    | _,_ => 0
  have hole_square :
      ∃ C : Multiset (Cycle G), lengths C = {4} ∧ ∀ x y : (Fin 4 ⊕ (Fin u × Fin 6)),
        (C.filter fun c => s(f x,f y) ∈ c.edges).card = holeCount x y := by
    classical
    let v (i : Fin 4) := f (.inl i)
    let w : G.Walk (v 0) (v 0) :=
      .cons ((adj (.inl 0) (.inl 2)).mpr (by simp [pairRow] : pairRow (.inl 0 : (Fin 4 ⊕ (Fin u × Fin 6))) ≠ pairRow (.inl 2)))
      (.cons ((adj (.inl 2) (.inl 1)).mpr (by simp [pairRow] : pairRow (.inl 2 : (Fin 4 ⊕ (Fin u × Fin 6))) ≠ pairRow (.inl 1)))
      (.cons ((adj (.inl 1) (.inl 3)).mpr (by simp [pairRow] : pairRow (.inl 1 : (Fin 4 ⊕ (Fin u × Fin 6))) ≠ pairRow (.inl 3)))
      (.cons ((adj (.inl 3) (.inl 0)).mpr (by simp [pairRow] : pairRow (.inl 3 : (Fin 4 ⊕ (Fin u × Fin 6))) ≠ pairRow (.inl 0))) .nil)))
    have simple : w.IsCycle := by simp [w,v,Walk.isCycle_def]
    let c : Cycle G := ⟨_,w,simple⟩
    refine ⟨{c},rfl,?_⟩
    intro x y
    change (Multiset.filter _ (c ::ₘ 0)).card = _
    simp only [Multiset.filter_cons, Multiset.filter_zero, add_zero]
    change (if s(f x,f y) ∈ [s(v 0,v 2),s(v 2,v 1),s(v 1,v 3),s(v 3,v 0)]
      then ({c} : Multiset (Cycle G)) else 0).card = _
    cases x with
    | inl i => cases y with
      | inl j => fin_cases i <;> fin_cases j <;> simp [v,holeCount]
      | inr p => simp [v,holeCount]
    | inr p => cases y <;> simp [v,holeCount]
  choose T len cnt using group_family
  obtain ⟨Q,hQ,cQ⟩ := hole_square
  have length_sum (I : Finset (Fin u)) :
      lengths (∑ g ∈ I, T g) = Multiset.replicate (12*I.card) 3 := by
    induction I using Finset.induction_on with
    | empty => simp [lengths]
    | insert g I hg ih =>
      rw [sum_insert hg, lengths, Multiset.map_add]
      change lengths (T g) + lengths (∑ k ∈ I,T k) = _
      rw [len,ih,← Multiset.replicate_add,card_insert_of_notMem hg]
      congr 1
      omega
  have count_sum (x y : (Fin 4 ⊕ (Fin u × Fin 6))) (I : Finset (Fin u)) :
      ((∑ g ∈ I, T g).filter fun c => s(f x,f y) ∈ c.edges).card = ∑ g ∈ I,groupCount g x y := by
    induction I using Finset.induction_on with
    | empty => simp
    | insert g I hg ih => rw [sum_insert hg,sum_insert hg,Multiset.filter_add,Multiset.card_add,cnt,ih]
  refine ⟨Q + ∑ g, T g,?_,?_⟩
  · rw [lengths,Multiset.map_add]
    change lengths Q + lengths (∑ g, T g) = _
    simp [hQ,length_sum]
  · intro x y
    rw [Multiset.filter_add,Multiset.card_add,cQ,count_sum]
    cases x with
    | inl h => cases y with
      | inl k => simp [pairRow,seedRegion,groupCount,holeCount,Fin.ext_iff]
      | inr p => rcases p with ⟨i,k⟩; simp [pairRow,seedRegion,groupCount,holeCount]
    | inr p =>
      obtain ⟨i,h⟩ := p
      cases y with
      | inl k => simp [pairRow,seedRegion,groupCount,holeCount]
      | inr p =>
        obtain ⟨j,k⟩ := p
        by_cases eq : j=i
        · subst j
          by_cases row : h.val/2=k.val/2 <;> simp [pairRow,seedRegion,groupCount,holeCount,Fin.ext_iff,row]
          simp only [← Fin.ext_iff]
          have eq : (univ.filter fun x => i=x) = {i} := by ext x; simp [eq_comm]
          rw [eq,Finset.card_singleton]
        · have sep (g : Fin u) : ¬(i=g ∧ j=g ∧ h.val/2≠k.val/2) := fun h => eq (h.2.1.trans h.1.symm)
          simp [pairRow,seedRegion,groupCount,holeCount,sep,Ne.symm eq]
end AlspachShared

namespace AlspachShared
open Finset SimpleGraph AlspachConjecture AlspachLift
open scoped Classical

/-- Take any t cross-group triple supports. Every remaining cross-group pair supplies
a square, including pairs belonging to unused blocks. -/
theorem cross_family {u holes m n t h : ℕ} (lim : t≤h)
    (row : (Fin holes ⊕ (Fin u × Fin 3)) ≃ Fin m)
    (f : (Fin m × Bool) ≃ Fin n) (G : SimpleGraph (Fin n))
    (adj : ∀ x y, G.Adj x y ↔ (f.symm x).1 ≠ (f.symm y).1)
    (B : Fin h → Finset (Fin u × Fin 3)) (three : ∀ i,(B i).card=3)
    (distinct : ∀ i x y, x ∈ B i → y ∈ B i → x ≠ y → x.1 ≠ y.1)
    (unique : ∀ x y : Fin u × Fin 3, x.1 ≠ y.1 → ∃! i, x ∈ B i ∧ y ∈ B i) :
    ∃ (q : ℕ) (C : Multiset (Cycle G)),
      lengths C=Multiset.replicate (4*t) 3 + Multiset.replicate q 4 ∧ ∀ x y,
      (C.filter fun c => s(x,y) ∈ c.edges).card =
        if ∃ a b : Fin u × Fin 3, (f.symm x).1=row (.inr a) ∧
          (f.symm y).1=row (.inr b) ∧ a.1≠b.1 then 1 else 0 := by
  classical
  let π := fun x : Fin n => (f.symm x).1
  let Covers (S : Finset (Sym2 (Fin m))) (L : Multiset ℕ) : Prop :=
    ∃ C : Multiset (Cycle G), lengths C = L ∧ ∀ x y : Fin n,
      (C.filter fun c => s(x,y) ∈ c.edges).card = if s(π x,π y) ∈ S then 1 else 0
  obtain ⟨covers_union,covers_many⟩ := AlspachRegions.collect G π
  let emb : (Fin u × Fin 3) ↪ Fin m := ⟨fun z => row (.inr z), fun x y e => Sum.inr.inj (row.injective e)⟩
  let A := (⊤ : SimpleGraph (Fin m)).edgeFinset.filter fun e =>
    ∃ a b : Fin u × Fin 3, a.1≠b.1 ∧ e=s(emb a,emb b)
  have membership (i j : Fin m) : s(i,j)∈A ↔ ∃ a b : Fin u × Fin 3,
      i=emb a ∧ j=emb b ∧ a.1≠b.1 := by
    rw [show A=_ by rfl, mem_filter]
    constructor
    · rintro ⟨_,a,b,ne,eq⟩
      rcases Sym2.eq_iff.mp eq with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
      · exact ⟨a,b,rfl,rfl,ne⟩
      · exact ⟨b,a,rfl,rfl,ne.symm⟩
    · rintro ⟨a,b,rfl,rfl,ne⟩
      exact ⟨SimpleGraph.mem_edgeFinset.mpr (emb.injective.ne fun e => ne (congrArg Prod.fst e)),a,b,ne,rfl⟩
  let eidx : Fin t ↪ Fin h := ⟨Fin.castLE lim,fun _ _ e => Fin.ext (congrArg (Fin.val : Fin h → ℕ) e)⟩
  let S (i : Fin t) := (⊤ : SimpleGraph (Fin m)).edgeFinset.filter fun e => e.toFinset ⊆ (B (eidx i)).map emb
  have inside (i : Fin t) (x y : Fin m) : s(x,y)∈S i ↔ x≠y ∧
      (∃ a ∈ B (eidx i), emb a=x) ∧ ∃ b ∈ B (eidx i), emb b=y := by
    simp only [S,mem_filter,SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet,SimpleGraph.top_adj,
      Sym2.toFinset_mk_eq,insert_subset_iff,singleton_subset_iff,mem_map]
  have subset (i : Fin t) : S i ⊆ A := by
    intro e
    induction e using Sym2.ind with
    | _ x y =>
      intro hit
      obtain ⟨ne,⟨a,ha,rfl⟩,b,hb,rfl⟩ := (inside i x y).mp hit
      exact (membership _ _).mpr ⟨a,b,rfl,rfl,distinct _ _ _ ha hb (fun e => ne (congrArg emb e))⟩
  have disj : Pairwise fun i j => Disjoint (S i) (S j) := by
    intro i j ij
    apply Finset.disjoint_left.mpr
    intro e
    induction e using Sym2.ind with
    | _ x y =>
      intro hi hj
      obtain ⟨ne,⟨a,ha,rfl⟩,b,hb,rfl⟩ := (inside i x y).mp hi
      obtain ⟨_,⟨a',ha',h1⟩,b',hb',h2⟩ := (inside j _ _).mp hj
      obtain rfl := emb.injective h1
      obtain rfl := emb.injective h2
      obtain ⟨k,_,only⟩ := unique _ _ (distinct _ _ _ ha hb (fun e => ne (congrArg emb e)))
      exact ij (eidx.injective ((only _ ⟨ha,hb⟩).trans (only _ ⟨ha',hb'⟩).symm))
  have across (i : Fin m) (a : Bool) (j : Fin m) (b : Bool) (ne : i≠j) : G.Adj (f (i,a)) (f (j,b)) :=
    (adj _ _).mpr (by simpa using ne)
  have tris (i : Fin t) : Covers (S i) (Multiset.replicate 4 3) :=
    region_of_three f G across _ (by simpa using three (eidx i))
  have sq (e : Sym2 (Fin m)) (he : e∈A) : Covers {e} {4} := by
    induction e using Sym2.ind with
    | _ i j =>
      have ne : i ≠ j := SimpleGraph.mem_edgeFinset.mp (mem_filter.mp he).1
      exact AlspachLadder.square_region f G ne (fun a b => across i a j b ne)
  let used := univ.biUnion S
  let unused := A \ used
  have contained : used ⊆ A := by
    intro e he
    obtain ⟨i,_,hi⟩ := mem_biUnion.mp he
    exact subset i hi
  have left : Covers used (Multiset.replicate (4*t) 3) := by
    have h := covers_many (univ : Finset (Fin t)) S (fun _ => Multiset.replicate 4 3)
      (fun i _ => tris i) (fun _ _ _ _ hij => disj hij)
    simpa only [used,sum_const,card_univ,Fintype.card_fin,Multiset.nsmul_replicate,Nat.mul_comm t 4] using h
  have right : Covers unused (Multiset.replicate unused.card 4) := by
    have h := covers_many unused (fun e => {e}) (fun _ => ({4} : Multiset ℕ))
      (fun e he => sq e (mem_sdiff.mp he).1) (fun i _ j _ ne => by simpa using ne)
    simpa [sum_const,Multiset.nsmul_singleton] using h
  have dj : Disjoint used unused := Finset.disjoint_left.mpr fun _ h h' => (mem_sdiff.mp h').2 h
  have union : used ∪ unused = A := Finset.union_sdiff_of_subset contained
  obtain ⟨C,sz,coverage⟩ := covers_union left right dj
  refine ⟨unused.card,C,sz,?_⟩
  intro x y
  have classify : s(π x,π y) ∈ used ∪ unused ↔
      ∃ a b : Fin u × Fin 3, (f.symm x).1=row (.inr a) ∧
        (f.symm y).1=row (.inr b) ∧ a.1≠b.1 := by rw [union]; exact membership _ _
  simpa only [classify] using coverage x y
end AlspachShared

namespace AlspachShared
open SimpleGraph AlspachConjecture
open scoped Classical

/-- A single four-point hole is shared by the six-point groups. Cross-only Bose
blocks supply the selected triangles, and every other pair of cross-group rows
supplies a square. -/
theorem shared_build (u t : ℕ) (odd : Odd u) (lim : t≤3*u.choose 2) :
    ∃ J : (completeGraph (Fin (6*u+4))).Subgraph, J.IsPerfectMatching ∧
      ∃ (q : ℕ) (C : Multiset (Cycle (completeGraph (Fin (6*u+4)) \ J.spanningCoe))),
        IsCycleDecomposition _ C ∧ lengths C=Multiset.replicate (12*u+4*t) 3 + Multiset.replicate q 4 := by
  classical
  let V := Fin 4 ⊕ (Fin u × Fin 6)
  let R := Fin 2 ⊕ (Fin u × Fin 3)
  let pairRow : V → R
    | .inl x => .inl ⟨x.val/2,by have := x.isLt; omega⟩
    | .inr (g,x) => .inr (g,⟨x.val/2,by have := x.isLt; omega⟩)
  let seedRegion : V → V → Prop
    | .inr (g,_), .inr (h,_) => g=h
    | _, _ => True
  let m := 3*u+2
  let row : R ≃ Fin m := Fintype.equivOfCardEq (by simp [R,m]; omega)
  let f : (Fin m × Bool) ≃ Fin (6*u+4) := Fintype.equivOfCardEq (by simp [m]; omega)
  obtain ⟨⟨k,hk⟩,outside⟩ := pair_chart_data u
  change ∀ x : V, (k x).1=pairRow x at hk
  change ∀ x y : V, ¬seedRegion x y ↔ ∃ a b : Fin u × Fin 3,
    pairRow x=Sum.inr a ∧ pairRow y=Sum.inr b ∧ a.1≠b.1 at outside
  let chart : V ≃ Fin (6*u+4) := (k.trans (row.prodCongr (Equiv.refl Bool))).trans f
  have proj (x : V) : (f.symm (chart x)).1=row (pairRow x) := by simp [chart,hk]
  have build (G : SimpleGraph (Fin (6*u+4))) [DecidableRel G.Adj]
      (adj : ∀ x y, G.Adj x y ↔ (f.symm x).1≠(f.symm y).1) :
      ∃ (q : ℕ) (C : Multiset (Cycle G)), IsCycleDecomposition G C ∧
        lengths C=Multiset.replicate (12*u+4*t) 3 + Multiset.replicate q 4 := by
    have adjSeed (x y : V) : G.Adj (chart x) (chart y) ↔ pairRow x ≠ pairRow y := by
      rw [adj,proj,proj,row.injective.ne_iff]
    obtain ⟨D,dLen,dCount⟩ := seed_family chart G adjSeed
    change ∀ x y : V, (D.filter fun c => s(chart x,chart y)∈c.edges).card =
      if pairRow x ≠ pairRow y ∧ seedRegion x y then 1 else 0 at dCount
    obtain ⟨B,three,separate,uniq⟩ := bose_cross odd
    obtain ⟨q,C,cLen,cCount⟩ := cross_family lim row f G adj B three separate uniq
    refine ⟨q+1,D+C,?_,?_⟩
    · intro e
      induction e using Sym2.ind with
      | _ a b =>
        obtain ⟨x,rfl⟩ := chart.surjective a
        obtain ⟨y,rfl⟩ := chart.surjective b
        intro he
        have edge : G.Adj (chart x) (chart y) := (show s(chart x,chart y) ∈ G.edgeSet from SimpleGraph.mem_edgeFinset.mp he)
        have ne := (adjSeed x y).mp edge
        have out := outside x y
        rw [Multiset.filter_add,Multiset.card_add,dCount,cCount,proj,proj]
        simp only [Equiv.apply_eq_iff_eq,←out]
        by_cases hs : seedRegion x y <;> simp [hs,ne]
    · change (D+C).map SimpleGraph.Cycle.length=_
      rw [Multiset.map_add]
      change lengths D+lengths C=_
      rw [dLen,cLen,Multiset.replicate_add (12*u) (4*t),Multiset.replicate_add q 1,Multiset.replicate_one]
      ac_rfl
  obtain ⟨J,hJ,adj⟩ := AlspachSquares.pair_matching f
  exact ⟨J,hJ,build _ adj⟩

end AlspachShared

namespace AlspachTrades
open SimpleGraph AlspachConjecture
open scoped Classical

/-- The base graph on three labels per group plus two shared labels has this many edges. -/
theorem shared_pair_count (u : ℕ) :
    (3*u+2).choose 2 = 9*u.choose 2 + 9*u+1 := by
  have step (a : ℕ) : (a+1).choose 2 = a.choose 2+a := by
    simpa only [Nat.choose_one_right,Nat.add_comm] using Nat.choose_succ_succ a 1
  induction u with
  | zero => decide
  | succ u ih =>
    have size : 3*(u+1)+2=3*u+2+1+1+1 := by omega
    rw [size,step (3*u+2+1+1),step (3*u+2+1),step (3*u+2),step u,ih]
    omega

/-- A shared-hole construction covers triangle-rich lists at orders ten modulo twelve.
The previously constructed square-rich lists cover all remaining admissible counts. -/
theorem shared_hole_lists
    (build : ∀ (u t : ℕ), Odd u → t ≤ 3*u.choose 2 →
      ∃ J : (completeGraph (Fin (6*u+4))).Subgraph, J.IsPerfectMatching ∧
        ∃ (q : ℕ) (C : Multiset (Cycle (completeGraph (Fin (6*u+4)) \ J.spanningCoe))),
          IsCycleDecomposition _ C ∧
          lengths C = Multiset.replicate (12*u+4*t) 3 + Multiset.replicate q 4)
    (n : ℕ) (residue : n%12=10)
    (I : (completeGraph (Fin n)).Subgraph) (hI : I.IsPerfectMatching)
    (L : Multiset ℕ) (shape : ∀ a∈L, a=3 ∨ a=4) (budget : L.sum=n.choose 2-n/2) :
    ∃ C : Multiset (Cycle (completeGraph (Fin n) \ I.spanningCoe)),
      IsCycleDecomposition _ C ∧ lengths C=L := by
  classical
  obtain ⟨u,odd,rfl⟩ : ∃ u, Odd u ∧ n=6*u+4 :=
    ⟨2*(n/12)+1,⟨n/12,rfl⟩,by omega⟩
  have evenOrder : 6*u+4=2*(3*u+2) := by omega
  have hm : 0<3*u+2 := by omega
  obtain ⟨j,upper,hL⟩ := classify_trades (3*u+2) hm L shape (by rwa [←evenOrder])
  have count := shared_pair_count u
  by_cases high : 3*u≤j
  · let t := j-3*u
    have num : 12*u+4*t=4*j := by dsimp [t]; omega
    have bound : t ≤ 3*u.choose 2 := by dsimp [t]; omega
    obtain ⟨J,hJ,q,C,dec,sizes⟩ := build u t odd bound
    rw [num] at sizes
    have edgeCount := TriangleBridge.matching_budget J hJ
    rw [Fintype.card_fin] at edgeCount
    have sums : (lengths C).sum=L.sum := by
      rw [AlspachLadder.decomposition_budget C dec,budget]
      convert edgeCount using 1
      congr 1
      ext e
      simp only [mem_edgeFinset]
    rw [sizes,hL,Multiset.sum_add,Multiset.sum_add] at sums
    simp only [Multiset.sum_replicate,smul_eq_mul] at sums
    have qval : q=(3*u+2).choose 2-3*j := by omega
    obtain ⟨iso⟩ := OMA.R_AlspachConjecture_alspach_conjecture_variants_even_R2.matchings_complements_iso J I hJ hI
    apply OMA.R_AlspachConjecture_alspach_conjecture_variants_even_R2.iso_decomposition iso dec
    rw [sizes,qval,hL]
  · have dominate : u ≤ 3*u.choose 2+1 := by
      cases u with
      | zero => omega
      | succ a =>
        have step : (a+1).choose 2 = a + a.choose 2 := by
          simpa only [Nat.choose_one_right] using Nat.choose_succ_succ a 1
        omega
    have qs : L.count 4=(3*u+2).choose 2-3*j := by simp [hL,Multiset.count_replicate]
    have enough : 3*u+2-1 ≤ L.count 4 := by omega
    have realize (N : ℕ) (order : N=2*(3*u+2)) (K : (completeGraph (Fin N)).Subgraph)
        (perfect : K.IsPerfectMatching) (size : L.sum=N.choose 2-N/2) :
        ∃ C : Multiset (Cycle (completeGraph (Fin N) \ K.spanningCoe)),
          IsCycleDecomposition _ C ∧ lengths C=L := by
      subst N
      exact triangle_square_with_squares hm K perfect L shape size enough
    exact realize _ evenOrder I hI budget

/-- At orders congruent to ten modulo twelve, every admissible mixture of
triangles and squares decomposes the complement of any prescribed perfect matching. -/
theorem triangle_square_ten_mod_twelve (n : ℕ) (residue : n%12=10)
    (I : (completeGraph (Fin n)).Subgraph) (hI : I.IsPerfectMatching)
    (L : Multiset ℕ) (shape : ∀ a∈L, a=3 ∨ a=4) (budget : L.sum=n.choose 2-n/2) :
    ∃ C : Multiset (Cycle (completeGraph (Fin n) \ I.spanningCoe)),
      IsCycleDecomposition _ C ∧ lengths C=L :=
  shared_hole_lists AlspachShared.shared_build n residue I hI L shape budget

end AlspachTrades

namespace AlspachSharedTwo

/-- The shared hole and each outer group split into pairs. Outside the seed,
both endpoints belong to outer positions in distinct groups. -/
theorem pair_chart_data (u : ℕ) :
    let V := Fin 2 ⊕ (Fin u × Fin 6)
    let R := Fin 1 ⊕ (Fin u × Fin 3)
    let pairRow : V → R
      | .inl _ => .inl 0
      | .inr (g,x) => .inr (g,⟨x.val/2,by have := x.isLt; omega⟩)
    let seedRegion : V → V → Prop
      | .inr (g,_), .inr (h,_) => g=h
      | _, _ => True
    (∃ k : V ≃ R × Bool, ∀ x, (k x).1=pairRow x) ∧
    (∀ x y : V, ¬seedRegion x y ↔
       ∃ a b : Fin u × Fin 3, pairRow x=Sum.inr a ∧ pairRow y=Sum.inr b ∧ a.1≠b.1) := by
  intro V R pairRow seedRegion
  constructor
  ·
    let f (j : Fin 2) : Fin 1 × Bool :=
      (0,decide (j.val%2=1))
    let g (j : Fin 6) : Fin 3 × Bool :=
      (⟨j.val/2, by have := j.isLt; omega⟩,decide (j.val%2=1))
    have bf : Function.Bijective f := by
      show (∀ x y, f x=f y → x=y) ∧ ∀ y, ∃ x, f x=y
      decide +kernel
    have bg : Function.Bijective g := by
      show (∀ x y, g x=g y → x=y) ∧ ∀ y, ∃ x, g x=y
      decide +kernel
    let h := (Equiv.prodCongr (Equiv.refl (Fin u)) (Equiv.ofBijective g bg)).trans
      (Equiv.prodAssoc (Fin u) (Fin 3) Bool).symm
    let k := (Equiv.sumCongr (Equiv.ofBijective f bf) h).trans
      (Equiv.sumProdDistrib (Fin 1) (Fin u × Fin 3) Bool).symm
    refine ⟨k, ?_⟩
    rintro (h | ⟨g,j⟩) <;> rfl
  · intro x y
    rcases x with x | ⟨g,x⟩ <;> rcases y with y | ⟨h,y⟩ <;> simp [seedRegion,pairRow,R]

end AlspachSharedTwo

namespace AlspachSharedTwo
open SimpleGraph Finset AlspachConjecture
open scoped Classical

set_option maxHeartbeats 1000000 in
/-- Each six-point group and the shared matched pair form a cocktail graph of order eight.
Its eight triangles cover all allowed seed edges, even when there are no groups. -/
theorem seed_family {u n : ℕ} (f : (Fin 2 ⊕ (Fin u × Fin 6)) ≃ Fin n) (G : SimpleGraph (Fin n)) :
    let pairRow : (Fin 2 ⊕ (Fin u × Fin 6)) → (Fin 1 ⊕ (Fin u × Fin 3))
      | .inl _ => .inl 0
      | .inr (g,x) => .inr (g,⟨x.val/2,by have := x.isLt; omega⟩)
    let seedRegion : (Fin 2 ⊕ (Fin u × Fin 6)) → (Fin 2 ⊕ (Fin u × Fin 6)) → Prop
      | .inr (g,_), .inr (h,_) => g=h
      | _, _ => True
    (∀ x y, G.Adj (f x) (f y) ↔ pairRow x ≠ pairRow y) →
    ∃ C : Multiset (Cycle G), lengths C = Multiset.replicate (8*u) 3 ∧ ∀ x y,
      (C.filter fun c => s(f x,f y) ∈ c.edges).card =
        if pairRow x ≠ pairRow y ∧ seedRegion x y then 1 else 0 := by
  classical
  intro pairRow seedRegion adj
  let X := Fin 2 ⊕ (Fin u × Fin 6)
  let L := Fin 2 ⊕ Fin 6
  let tri (t : Fin 8) : L × L × L := match t.val with
    | 0 => (.inl 0,.inr 0,.inr 3) | 1 => (.inl 0,.inr 4,.inr 1)
    | 2 => (.inl 0,.inr 2,.inr 5) | 3 => (.inl 1,.inr 3,.inr 4)
    | 4 => (.inl 1,.inr 1,.inr 2) | 5 => (.inl 1,.inr 5,.inr 0)
    | 6 => (.inr 0,.inr 2,.inr 4) | _ => (.inr 1,.inr 3,.inr 5)
  let edge (x y a b : L) : Bool := ((x==a) && (y==b)) || ((x==b) && (y==a))
  let hit (t : Fin 8) (x y : L) : Bool :=
    let v := tri t
    edge x y v.1 v.2.1 || edge x y v.2.1 v.2.2 || edge x y v.2.2 v.1
  let allowed : L → L → Bool
    | .inl _,.inl _ => false
    | .inr a,.inr b => a.val/2 != b.val/2
    | _,_ => true
  have cert :
      (∀ t, allowed (tri t).1 (tri t).2.1 ∧ allowed (tri t).2.1 (tri t).2.2 ∧
        allowed (tri t).2.2 (tri t).1) ∧
      (∀ x y : L, (univ.filter fun t => hit t x y).card = if allowed x y then 1 else 0) := by
    dsimp only [L,allowed,tri,hit,edge]
    decide +kernel
  let embed (g : Fin u) : L → X
    | .inl h => .inl h | .inr a => .inr (g,a)
  let project (g : Fin u) : X → Option L
    | .inl h => some (.inl h)
    | .inr (i,a) => if i=g then some (.inr a) else none
  let groupCount (g : Fin u) (x y : X) := match project g x,project g y with
    | some a,some b => if allowed a b then 1 else 0
    | _,_ => 0
  have lift_adj (g : Fin u) (x y : L) (h : allowed x y) :
      G.Adj (f (embed g x)) (f (embed g y)) := by
    apply (adj _ _).mpr
    cases x <;> cases y <;> simp [allowed,pairRow,embed,Fin.ext_iff] at h ⊢
    assumption
  have group (g : Fin u) : ∃ C : Multiset (Cycle G), lengths C = Multiset.replicate 8 3 ∧
      ∀ x y : X, (C.filter fun c => s(f x,f y) ∈ c.edges).card = groupCount g x y := by
    let v (a : L) := f (embed g a)
    let w (t : Fin 8) : G.Walk (v (tri t).1) (v (tri t).1) :=
      .cons (lift_adj g _ _ (cert.1 t).1) (.cons (lift_adj g _ _ (cert.1 t).2.1)
        (.cons (lift_adj g _ _ (cert.1 t).2.2) .nil))
    have triangle {x y z : Fin n} (xy : G.Adj x y) (yz : G.Adj y z) (zx : G.Adj z x) :
        (Walk.cons xy (.cons yz (.cons zx .nil))).IsCycle := by
      simp [Walk.isCycle_def,xy.ne,yz.ne,zx.ne,Ne.symm xy.ne,Ne.symm zx.ne]
    have simple (t : Fin 8) : (w t).IsCycle :=
      triangle (lift_adj g _ _ (cert.1 t).1) (lift_adj g _ _ (cert.1 t).2.1)
        (lift_adj g _ _ (cert.1 t).2.2)
    let c (t : Fin 8) : Cycle G := ⟨_,w t,simple t⟩
    have test (x : X) (a : L) : f x = v a ↔ project g x = some a := by
      cases x with
      | inl h => cases a <;> simp [L,X,v,embed,project,Sum.inl.injEq]
      | inr p => obtain ⟨i,b⟩ := p; cases a <;> by_cases eq : i=g <;> simp [L,X,v,embed,project,eq,Sum.inr.injEq]
    have decode (x y : X) (a b d : L) :
        s(f x,f y) ∈ [s(v a,v b),s(v b,v d),s(v d,v a)] ↔
        (match project g x,project g y with
          | some k,some l => edge k l a b || edge k l b d || edge k l d a | _,_ => false) := by
      simp only [List.mem_cons,List.not_mem_nil,or_false,Sym2.eq_iff,test]
      generalize project g x = p
      generalize project g y = q
      have eqb : ∀ k l : L, ((k==l)=true) ↔ k=l := by
        dsimp only [L]
        decide +kernel
      cases p <;> cases q <;> simp [edge,eqb,or_assoc]
    have mem (t : Fin 8) (x y : X) :
        s(f x,f y) ∈ (c t).edges ↔ (match project g x,project g y with
          | some a,some b => hit t a b | _,_ => false) :=
      decode x y (tri t).1 (tri t).2.1 (tri t).2.2
    refine ⟨(univ : Finset (Fin 8)).val.map c,?_,?_⟩
    · rw [lengths,Multiset.map_map,show SimpleGraph.Cycle.length ∘ c = fun _ => 3 from rfl,Multiset.map_const']
      simp
    · intro x y
      rw [Multiset.filter_map,Multiset.card_map]
      change (univ.filter (fun t => s(f x,f y) ∈ (c t).edges)).card = _
      simp only [mem,groupCount]
      cases project g x <;> cases project g y <;> simp [cert.2]
  choose T len cnt using group
  have length_sum (I : Finset (Fin u)) : lengths (∑ g ∈ I,T g) = Multiset.replicate (8*I.card) 3 := by
    induction I using Finset.induction_on with
    | empty => simp [lengths]
    | insert g I hg ih =>
      rw [sum_insert hg,lengths,Multiset.map_add]
      change lengths (T g) + lengths (∑ j ∈ I,T j) = _
      rw [len,ih,← Multiset.replicate_add,card_insert_of_notMem hg]
      congr 1
      omega
  have count_sum (x y : X) (I : Finset (Fin u)) :
      ((∑ g ∈ I,T g).filter fun c => s(f x,f y) ∈ c.edges).card = ∑ g ∈ I,groupCount g x y := by
    induction I using Finset.induction_on with
    | empty => simp
    | insert g I hg ih => rw [sum_insert hg,sum_insert hg,Multiset.filter_add,Multiset.card_add,cnt,ih]
  refine ⟨∑ g,T g,by simpa using length_sum univ,?_⟩
  intro x y
  rw [count_sum]
  cases x with
  | inl h => cases y with
    | inl k => simp [groupCount,project,allowed,pairRow]
    | inr p =>
      obtain ⟨i,k⟩ := p
      have each (g : Fin u) : groupCount g (.inl h) (.inr (i,k)) = if i=g then 1 else 0 := by
        by_cases eq : i=g <;> simp [groupCount,project,allowed,eq]
      simp [each,pairRow,seedRegion]
  | inr p =>
    obtain ⟨i,h⟩ := p
    cases y with
    | inl k =>
      have each (g : Fin u) : groupCount g (.inr (i,h)) (.inl k) = if i=g then 1 else 0 := by
        by_cases eq : i=g <;> simp [groupCount,project,allowed,eq]
      simp [each,pairRow,seedRegion]
    | inr p =>
      obtain ⟨j,k⟩ := p
      have each (g : Fin u) : groupCount g (.inr (i,h)) (.inr (j,k)) =
          if i=g ∧ j=g ∧ h.val/2 ≠ k.val/2 then 1 else 0 := by
        by_cases eq : i=g <;> by_cases eq' : j=g <;> simp [groupCount,project,allowed,eq,eq']
      by_cases same : j=i
      · subst j
        by_cases eq : h.val/2=k.val/2 <;> simp [each,pairRow,seedRegion,Fin.ext_iff,eq]
        simp only [← Fin.ext_iff]
        have one : (univ.filter fun g => i=g) = {i} := by ext g; simp [eq_comm]
        rw [one,card_singleton]
      · have sep (g : Fin u) : ¬(i=g ∧ j=g ∧ h.val/2≠k.val/2) := fun h => same (h.2.1.trans h.1.symm)
        simp [each,pairRow,seedRegion,sep,Ne.symm same]
end AlspachSharedTwo

namespace AlspachShared
open SimpleGraph AlspachConjecture
open scoped Classical

/-- A matched two-point hole is shared by the six-point groups. Cross-only Bose
blocks supply the selected triangles, and every other pair of cross-group rows
supplies a square. -/
theorem shared_two_build (u t : ℕ) (odd : Odd u) (lim : t≤3*u.choose 2) :
    ∃ J : (completeGraph (Fin (6*u+2))).Subgraph, J.IsPerfectMatching ∧
      ∃ (q : ℕ) (C : Multiset (Cycle (completeGraph (Fin (6*u+2)) \ J.spanningCoe))),
        IsCycleDecomposition _ C ∧ lengths C=Multiset.replicate (8*u+4*t) 3 + Multiset.replicate q 4 := by
  classical
  let V := Fin 2 ⊕ (Fin u × Fin 6)
  let R := Fin 1 ⊕ (Fin u × Fin 3)
  let pairRow : V → R
    | .inl _ => .inl 0
    | .inr (g,x) => .inr (g,⟨x.val/2,by have := x.isLt; omega⟩)
  let seedRegion : V → V → Prop
    | .inr (g,_), .inr (h,_) => g=h
    | _, _ => True
  let m := 3*u+1
  let row : R ≃ Fin m := Fintype.equivOfCardEq (by simp [R,m]; omega)
  let f : (Fin m × Bool) ≃ Fin (6*u+2) := Fintype.equivOfCardEq (by simp [m]; omega)
  obtain ⟨⟨k,hk⟩,outside⟩ := AlspachSharedTwo.pair_chart_data u
  change ∀ x : V, (k x).1=pairRow x at hk
  change ∀ x y : V, ¬seedRegion x y ↔ ∃ a b : Fin u × Fin 3,
    pairRow x=Sum.inr a ∧ pairRow y=Sum.inr b ∧ a.1≠b.1 at outside
  let chart : V ≃ Fin (6*u+2) := (k.trans (row.prodCongr (Equiv.refl Bool))).trans f
  have proj (x : V) : (f.symm (chart x)).1=row (pairRow x) := by simp [chart,hk]
  have build (G : SimpleGraph (Fin (6*u+2))) [DecidableRel G.Adj]
      (adj : ∀ x y, G.Adj x y ↔ (f.symm x).1≠(f.symm y).1) :
      ∃ (q : ℕ) (C : Multiset (Cycle G)), IsCycleDecomposition G C ∧
        lengths C=Multiset.replicate (8*u+4*t) 3 + Multiset.replicate q 4 := by
    have adjSeed (x y : V) : G.Adj (chart x) (chart y) ↔ pairRow x ≠ pairRow y := by
      rw [adj,proj,proj,row.injective.ne_iff]
    obtain ⟨D,dLen,dCount⟩ := AlspachSharedTwo.seed_family chart G adjSeed
    change ∀ x y : V, (D.filter fun c => s(chart x,chart y)∈c.edges).card =
      if pairRow x ≠ pairRow y ∧ seedRegion x y then 1 else 0 at dCount
    obtain ⟨B,three,separate,uniq⟩ := bose_cross odd
    obtain ⟨q,C,cLen,cCount⟩ := cross_family lim row f G adj B three separate uniq
    refine ⟨q,D+C,?_,?_⟩
    · intro e
      induction e using Sym2.ind with
      | _ a b =>
        obtain ⟨x,rfl⟩ := chart.surjective a
        obtain ⟨y,rfl⟩ := chart.surjective b
        intro he
        have edge : G.Adj (chart x) (chart y) := (show s(chart x,chart y) ∈ G.edgeSet from SimpleGraph.mem_edgeFinset.mp he)
        have ne := (adjSeed x y).mp edge
        have out := outside x y
        rw [Multiset.filter_add,Multiset.card_add,dCount,cCount,proj,proj]
        simp only [Equiv.apply_eq_iff_eq,←out]
        by_cases hs : seedRegion x y <;> simp [hs,ne]
    · change (D+C).map SimpleGraph.Cycle.length=_
      rw [Multiset.map_add]
      change lengths D+lengths C=_
      rw [dLen,cLen,Multiset.replicate_add (8*u) (4*t)]
      ac_rfl
  obtain ⟨J,hJ,adj⟩ := AlspachSquares.pair_matching f
  exact ⟨J,hJ,build _ adj⟩

end AlspachShared

namespace AlspachTrades
open SimpleGraph AlspachConjecture
open scoped Classical

/-- The base graph on three labels per group plus one shared label has this many edges. -/
theorem two_hole_pair_count (u : ℕ) :
    (3*u+1).choose 2 = 9*u.choose 2 + 6*u := by
  have step (a : ℕ) : (a+1).choose 2 = a.choose 2+a := by
    simpa only [Nat.choose_one_right,Nat.add_comm] using Nat.choose_succ_succ a 1
  induction u with
  | zero => decide
  | succ u ih =>
    have size : 3*(u+1)+1=3*u+1+1+1+1 := by omega
    rw [size,step (3*u+1+1+1),step (3*u+1+1),step (3*u+1),step u,ih]
    omega

/-- A shared-hole construction covers triangle-rich lists at orders eight modulo twelve.
The previously constructed square-rich lists cover all remaining admissible counts. -/
theorem two_hole_lists
    (build : ∀ (u t : ℕ), Odd u → t ≤ 3*u.choose 2 →
      ∃ J : (completeGraph (Fin (6*u+2))).Subgraph, J.IsPerfectMatching ∧
        ∃ (q : ℕ) (C : Multiset (Cycle (completeGraph (Fin (6*u+2)) \ J.spanningCoe))),
          IsCycleDecomposition _ C ∧
          lengths C = Multiset.replicate (8*u+4*t) 3 + Multiset.replicate q 4)
    (n : ℕ) (residue : n%12=8)
    (I : (completeGraph (Fin n)).Subgraph) (hI : I.IsPerfectMatching)
    (L : Multiset ℕ) (shape : ∀ a∈L, a=3 ∨ a=4) (budget : L.sum=n.choose 2-n/2) :
    ∃ C : Multiset (Cycle (completeGraph (Fin n) \ I.spanningCoe)),
      IsCycleDecomposition _ C ∧ lengths C=L := by
  classical
  obtain ⟨u,odd,rfl⟩ : ∃ u, Odd u ∧ n=6*u+2 :=
    ⟨2*(n/12)+1,⟨n/12,rfl⟩,by omega⟩
  have evenOrder : 6*u+2=2*(3*u+1) := by omega
  have hm : 0<3*u+1 := by omega
  obtain ⟨j,upper,hL⟩ := classify_trades (3*u+1) hm L shape (by rwa [←evenOrder])
  have count := two_hole_pair_count u
  by_cases high : 2*u≤j
  · let t := j-2*u
    have num : 8*u+4*t=4*j := by dsimp [t]; omega
    have bound : t ≤ 3*u.choose 2 := by dsimp [t]; omega
    obtain ⟨J,hJ,q,C,dec,sizes⟩ := build u t odd bound
    rw [num] at sizes
    have edgeCount := TriangleBridge.matching_budget J hJ
    rw [Fintype.card_fin] at edgeCount
    have sums : (lengths C).sum=L.sum := by
      rw [AlspachLadder.decomposition_budget C dec,budget]
      convert edgeCount using 1
      congr 1
      ext e
      simp only [mem_edgeFinset]
    rw [sizes,hL,Multiset.sum_add,Multiset.sum_add] at sums
    simp only [Multiset.sum_replicate,smul_eq_mul] at sums
    have qval : q=(3*u+1).choose 2-3*j := by omega
    obtain ⟨iso⟩ := OMA.R_AlspachConjecture_alspach_conjecture_variants_even_R2.matchings_complements_iso J I hJ hI
    apply OMA.R_AlspachConjecture_alspach_conjecture_variants_even_R2.iso_decomposition iso dec
    rw [sizes,qval,hL]
  · have dominate : u ≤ 3*u.choose 2+1 := by
      cases u with
      | zero => omega
      | succ a =>
        have step : (a+1).choose 2 = a + a.choose 2 := by
          simpa only [Nat.choose_one_right] using Nat.choose_succ_succ a 1
        omega
    have qs : L.count 4=(3*u+1).choose 2-3*j := by simp [hL,Multiset.count_replicate]
    have enough : 3*u+1-1 ≤ L.count 4 := by omega
    have realize (N : ℕ) (order : N=2*(3*u+1)) (K : (completeGraph (Fin N)).Subgraph)
        (perfect : K.IsPerfectMatching) (size : L.sum=N.choose 2-N/2) :
        ∃ C : Multiset (Cycle (completeGraph (Fin N) \ K.spanningCoe)),
          IsCycleDecomposition _ C ∧ lengths C=L := by
      subst N
      exact triangle_square_with_squares hm K perfect L shape size enough
    exact realize _ evenOrder I hI budget

/-- At orders congruent to eight modulo twelve, every admissible mixture of
triangles and squares decomposes the complement of any prescribed perfect matching. -/
theorem triangle_square_eight_mod_twelve (n : ℕ) (residue : n%12=8)
    (I : (completeGraph (Fin n)).Subgraph) (hI : I.IsPerfectMatching)
    (L : Multiset ℕ) (shape : ∀ a∈L, a=3 ∨ a=4) (budget : L.sum=n.choose 2-n/2) :
    ∃ C : Multiset (Cycle (completeGraph (Fin n) \ I.spanningCoe)),
      IsCycleDecomposition _ C ∧ lengths C=L :=
  two_hole_lists AlspachShared.shared_two_build n residue I hI L shape budget

end AlspachTrades

namespace AlspachTripleBlowup
open Finset AlspachTrades
open scoped Classical

/-- Deleting one point of a Steiner triple system pairs all remaining points.
The surviving blocks cover each unordered nonmatching pair exactly once. -/
theorem matched_base (m : ℕ) (residue : m%6=0 ∨ m%6=2) :
    ∃ mate : Fin m → Fin m, Function.Involutive mate ∧ (∀ x,mate x≠x) ∧
      ∃ B : Fin ((m.choose 2-m/2)/3) → Finset (Fin m),
        (∀ i,(B i).card=3) ∧
        (∀ i x, x∈B i → ∀ y, y∈B i → x≠y → mate x≠y) ∧
        ∀ x y, x≠y → mate x≠y → ∃! i, x∈B i ∧ y∈B i := by
  classical
  obtain ⟨tri,three,pairs⟩ := full_design (m+1) (by omega)
  let p := Fin.last m
  let V := {x : Fin (m+1) // x≠p}
  let T := {i : Fin ((m+1).choose 2/3) // p∉tri i}
  have third_vertex {s : Finset (Fin (m+1))} (sz : s.card=3)
      {p x : Fin (m+1)} (hp : p∈s) (hx : x∈s) (ne : x≠p) :
      ∃! y, y∈s ∧ y≠p ∧ y≠x := by
    let t := (s.erase p).erase x
    have h : t.card=1 := by
      rw [show t=(s.erase p).erase x by rfl,
        Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨ne,hx⟩),Finset.card_erase_of_mem hp,sz]
    obtain ⟨a,ha⟩ := Finset.card_eq_one.mp h
    have iff_mem (y : Fin (m+1)) : (y∈s ∧ y≠p ∧ y≠x) ↔ y=a := by
      rw [←Finset.mem_singleton,←ha]
      simp only [t,Finset.mem_erase]
      tauto
    exact ⟨a,(iff_mem _).mpr rfl,fun y hy => (iff_mem y).mp hy⟩
  let rel (x y : V) := x≠y ∧ ∃ i, p∈tri i ∧ x.val∈tri i ∧ y.val∈tri i
  have symm {x y} (h : rel x y) : rel y x := by
    obtain ⟨ne,i,hp,hx,hy⟩ := h
    exact ⟨ne.symm,i,hp,hy,hx⟩
  have one (x : V) : ∃! y, rel x y := by
    obtain ⟨i,⟨hp,hx⟩,hu⟩ := pairs p x.val x.property.symm
    obtain ⟨z,⟨hz,zp,zx⟩,uz⟩ := third_vertex (three i) hp hx x.property
    refine ⟨⟨z,zp⟩,⟨fun eq => zx (congrArg Subtype.val eq.symm),i,hp,hx,hz⟩,?_⟩
    rintro y ⟨ne,j,jp,jx,jy⟩
    obtain rfl : j=i := hu j ⟨jp,jx⟩
    exact Subtype.ext (uz y.val ⟨jy,y.property,fun eq => ne (Subtype.ext eq.symm)⟩)
  let mate (x : V) := (one x).exists.choose
  have hit (x : V) : rel x (mate x) := (one x).exists.choose_spec
  have pair {x y} (h : rel x y) : mate x=y := (one x).unique (hit x) h
  have inv : Function.Involutive mate := fun x => pair (symm (hit x))
  have fixed (x : V) : mate x≠x := (hit x).1.symm
  let block (i : T) := (tri i.val).subtype (fun x => x≠p)
  have mem (x : V) (i : T) : x∈block i ↔ x.val∈tri i.val := Finset.mem_subtype
  have size (i : T) : (block i).card=3 := by
    dsimp only [block]
    rw [Finset.card_subtype,Finset.filter_eq_self.mpr,three]
    intro x hx eq
    exact i.property (eq ▸ hx)
  have comp (i : T) (x y : V) (hx : x∈block i) (hy : y∈block i)
      (ne : x≠y) : mate x≠y := by
    intro eq
    obtain ⟨_,j,hp,jx,jy⟩ : rel x y := eq ▸ hit x
    have uniq := pairs x.val y.val (fun h => ne (Subtype.ext h))
    have ji := uniq.unique (show x.val∈tri j ∧ y.val∈tri j from ⟨jx,jy⟩)
      (show x.val∈tri i.val ∧ y.val∈tri i.val from ⟨(mem x i).mp hx,(mem y i).mp hy⟩)
    exact i.property (ji ▸ hp)
  have unique (x y : V) (ne : x≠y) (notMate : mate x≠y) :
      ∃! i, x∈block i ∧ y∈block i := by
    obtain ⟨i,hi,uni⟩ := pairs x.val y.val (fun eq => ne (Subtype.ext eq))
    have hp : p∉tri i := fun hp => notMate (pair ⟨ne,i,hp,hi⟩)
    let j : T := ⟨i,hp⟩
    exact ⟨j,⟨(mem x j).mpr hi.1,(mem y j).mpr hi.2⟩,fun b hb =>
      Subtype.ext (uni b.val ⟨(mem x b).mp hb.1,(mem y b).mp hb.2⟩)⟩
  have cardV : Fintype.card V=m := by
    change Fintype.card {x : Fin (m+1) // ¬x=p}=m
    rw [Fintype.card_subtype_compl,Fintype.card_subtype_eq,Fintype.card_fin]
    omega
  have cardT : Fintype.card T=(m.choose 2-m/2)/3 := by
    change Fintype.card {i : Fin ((m+1).choose 2/3) // ¬p∈tri i}=_
    rw [Fintype.card_subtype_compl,Fintype.card_fin,Fintype.card_subtype]
    have lost := design_valency tri three pairs p
    have step : (m+1).choose 2 = m + m.choose 2 :=
      by simpa only [Nat.choose_one_right] using Nat.choose_succ_succ m 1
    omega
  let f := Fintype.equivFinOfCardEq cardV
  let idx := (Fintype.equivFinOfCardEq cardT).symm
  let M (x : Fin m) := f (mate (f.symm x))
  let B (i) := (block (idx i)).map f.toEmbedding
  have bm (i) (x : Fin m) : x∈B i ↔ f.symm x∈block (idx i) := by simp [B]
  refine ⟨M,fun x => ?_,fun x eq => ?_,B,?_,?_,?_⟩
  · simp only [M,Equiv.symm_apply_apply,inv (f.symm x),Equiv.apply_symm_apply]
  · exact fixed (f.symm x) (by simpa only [M,Equiv.symm_apply_apply] using congrArg f.symm eq)
  · intro i
    simpa only [B,card_map] using size (idx i)
  · intro i x hx y hy ne eq
    apply comp (idx i) (f.symm x) (f.symm y) ((bm i x).mp hx) ((bm i y).mp hy)
      (fun e => ne (f.symm.injective e))
    simpa only [M,Equiv.symm_apply_apply] using congrArg f.symm eq
  · intro x y ne nmate
    obtain ⟨b,hb,hu⟩ := unique (f.symm x) (f.symm y) (fun e => ne (f.symm.injective e))
      (fun e => nmate (by simp only [M,e,Equiv.apply_symm_apply]))
    refine ⟨idx.symm b,⟨(bm _ _).mpr (by simpa using hb.1),(bm _ _).mpr (by simpa using hb.2)⟩,?_⟩
    intro j hj
    apply idx.injective
    simpa only [Equiv.apply_symm_apply] using hu (idx j) ⟨(bm j x).mp hj.1,(bm j y).mp hj.2⟩

end AlspachTripleBlowup

namespace AlspachGdd
open Finset

theorem four_hole_seeds :
    let Design {V K : Type} (group : V → K) : Prop :=
      ∃ blocks : Finset (Finset V),
        (∀ B∈blocks, B.card=3) ∧
        (∀ B∈blocks, ∀ x∈B, ∀ y∈B, x≠y → group x≠group y) ∧
        ∀ x y, group x≠group y → ∃! B : {B // B∈blocks}, x∈B.val ∧ y∈B.val
    let holeGroup {H R : Type} : H ⊕ (R × Bool) → Option R := Sum.elim (fun _ => none) (fun x => some x.1)
    Design (holeGroup (H:=Fin 4) (R:=Fin 3)) ∧ Design (holeGroup (H:=Fin 4) (R:=Fin 6)) := by
  let Design {V K : Type} (group : V → K) : Prop :=
    ∃ blocks : Finset (Finset V),
      (∀ B∈blocks, B.card=3) ∧
      (∀ B∈blocks, ∀ x∈B, ∀ y∈B, x≠y → group x≠group y) ∧
      ∀ x y, group x≠group y → ∃! B : {B // B∈blocks}, x∈B.val ∧ y∈B.val
  let holeGroup {H R : Type} : H ⊕ (R × Bool) → Option R := Sum.elim (fun _ => none) (fun x => some x.1)
  have from_index {V K I : Type} [Fintype I] (g : V → K) (b : I → Finset V)
      (three : ∀ i, (b i).card=3)
      (apart : ∀ i, ∀ x∈b i, ∀ y∈b i, x≠y → g x≠g y)
      (pair : ∀ x y, g x≠g y → ∃! i, x∈b i ∧ y∈b i) : Design g := by
    classical
    refine ⟨univ.image b,?_,?_,?_⟩
    · rintro _ h
      obtain ⟨i,_,rfl⟩ := mem_image.mp h
      exact three i
    · rintro _ h
      obtain ⟨i,_,rfl⟩ := mem_image.mp h
      exact apart i
    · intro x y h
      obtain ⟨i,hi,uniq⟩ := pair x y h
      refine ⟨⟨b i,mem_image.mpr ⟨i,mem_univ _,rfl⟩⟩,hi,?_⟩
      rintro ⟨B,hB⟩ hits
      obtain ⟨j,_,rfl⟩ := mem_image.mp hB
      exact Subtype.ext (congrArg b (uniq j hits))
  have seed_3 : Design (holeGroup (H:=Fin 4) (R:=Fin 3)) := by
    let b : Fin 12 → Finset (Fin 4 ⊕ (Fin 3 × Bool)) := fun i => ([
      {Sum.inl 0, Sum.inr (0,false), Sum.inr (1,false)},
      {Sum.inl 0, Sum.inr (0,true), Sum.inr (2,false)},
      {Sum.inl 0, Sum.inr (1,true), Sum.inr (2,true)},
      {Sum.inl 1, Sum.inr (0,false), Sum.inr (1,true)},
      {Sum.inl 1, Sum.inr (0,true), Sum.inr (2,true)},
      {Sum.inl 1, Sum.inr (1,false), Sum.inr (2,false)},
      {Sum.inl 2, Sum.inr (0,false), Sum.inr (2,false)},
      {Sum.inl 2, Sum.inr (0,true), Sum.inr (1,true)},
      {Sum.inl 2, Sum.inr (1,false), Sum.inr (2,true)},
      {Sum.inl 3, Sum.inr (0,false), Sum.inr (2,true)},
      {Sum.inl 3, Sum.inr (0,true), Sum.inr (1,false)},
      {Sum.inl 3, Sum.inr (1,true), Sum.inr (2,false)}] : List (Finset (Fin 4 ⊕ (Fin 3 × Bool))))[i.val]'(by simp)
    apply from_index holeGroup b <;> clear from_index
    · decide +kernel +revert
    · decide +kernel +revert
    · have counts : ∀ x y : Fin 4 ⊕ (Fin 3 × Bool), holeGroup x ≠ holeGroup y → (univ.filter (fun i => x∈b i ∧ y∈b i)).card=1 := by decide +kernel +revert
      intro x y ne
      obtain ⟨i,hi⟩ := Finset.card_eq_one.mp (counts x y ne)
      have iffmem (j) : (x∈b j ∧ y∈b j) ↔ j=i := by
        rw [←Finset.mem_singleton,←hi,Finset.mem_filter]; simp
      exact ⟨i,(iffmem i).mpr rfl,fun j jh => (iffmem j).mp jh⟩
  have seed_6 : Design (holeGroup (H:=Fin 4) (R:=Fin 6)) := by
    let b : Fin 36 → Finset (Fin 4 ⊕ (Fin 6 × Bool)) := fun i => ([
      {Sum.inl 0, Sum.inr (0,false), Sum.inr (1,false)},
      {Sum.inl 0, Sum.inr (0,true), Sum.inr (2,false)},
      {Sum.inl 0, Sum.inr (1,true), Sum.inr (3,false)},
      {Sum.inl 0, Sum.inr (2,true), Sum.inr (4,false)},
      {Sum.inl 0, Sum.inr (3,true), Sum.inr (5,false)},
      {Sum.inl 0, Sum.inr (4,true), Sum.inr (5,true)},
      {Sum.inl 1, Sum.inr (0,false), Sum.inr (1,true)},
      {Sum.inl 1, Sum.inr (0,true), Sum.inr (3,true)},
      {Sum.inl 1, Sum.inr (1,false), Sum.inr (2,false)},
      {Sum.inl 1, Sum.inr (2,true), Sum.inr (5,true)},
      {Sum.inl 1, Sum.inr (3,false), Sum.inr (4,false)},
      {Sum.inl 1, Sum.inr (4,true), Sum.inr (5,false)},
      {Sum.inl 2, Sum.inr (0,false), Sum.inr (2,true)},
      {Sum.inl 2, Sum.inr (0,true), Sum.inr (5,true)},
      {Sum.inl 2, Sum.inr (1,false), Sum.inr (3,true)},
      {Sum.inl 2, Sum.inr (1,true), Sum.inr (4,false)},
      {Sum.inl 2, Sum.inr (2,false), Sum.inr (4,true)},
      {Sum.inl 2, Sum.inr (3,false), Sum.inr (5,false)},
      {Sum.inl 3, Sum.inr (0,false), Sum.inr (4,true)},
      {Sum.inl 3, Sum.inr (0,true), Sum.inr (4,false)},
      {Sum.inl 3, Sum.inr (1,false), Sum.inr (2,true)},
      {Sum.inl 3, Sum.inr (1,true), Sum.inr (3,true)},
      {Sum.inl 3, Sum.inr (2,false), Sum.inr (5,false)},
      {Sum.inl 3, Sum.inr (3,false), Sum.inr (5,true)},
      {Sum.inr (0,false), Sum.inr (2,false), Sum.inr (3,false)},
      {Sum.inr (0,false), Sum.inr (3,true), Sum.inr (5,true)},
      {Sum.inr (0,false), Sum.inr (4,false), Sum.inr (5,false)},
      {Sum.inr (0,true), Sum.inr (1,false), Sum.inr (5,false)},
      {Sum.inr (0,true), Sum.inr (1,true), Sum.inr (4,true)},
      {Sum.inr (0,true), Sum.inr (2,true), Sum.inr (3,false)},
      {Sum.inr (1,false), Sum.inr (3,false), Sum.inr (4,true)},
      {Sum.inr (1,false), Sum.inr (4,false), Sum.inr (5,true)},
      {Sum.inr (1,true), Sum.inr (2,false), Sum.inr (5,true)},
      {Sum.inr (1,true), Sum.inr (2,true), Sum.inr (5,false)},
      {Sum.inr (2,false), Sum.inr (3,true), Sum.inr (4,false)},
      {Sum.inr (2,true), Sum.inr (3,true), Sum.inr (4,true)}] : List (Finset (Fin 4 ⊕ (Fin 6 × Bool))))[i.val]'(by simp)
    apply from_index holeGroup b <;> clear from_index <;> clear seed_3
    · decide +kernel +revert
    · decide +kernel +revert
    · have counts : ∀ x y : Fin 4 ⊕ (Fin 6 × Bool), holeGroup x ≠ holeGroup y → (univ.filter (fun i => x∈b i ∧ y∈b i)).card=1 := by decide +kernel +revert
      intro x y ne
      obtain ⟨i,hi⟩ := Finset.card_eq_one.mp (counts x y ne)
      have iffmem (j) : (x∈b j ∧ y∈b j) ↔ j=i := by
        rw [←Finset.mem_singleton,←hi,Finset.mem_filter]; simp
      exact ⟨i,(iffmem i).mpr rfl,fun j jh => (iffmem j).mp jh⟩
  exact ⟨seed_3,seed_6⟩

open scoped Classical

/-- Four-hole triple designs of every admissible size, and their original
master before replacing each point by three clones. -/
theorem recursive_designs :
    let Design {V K : Type} (group : V → K) : Prop :=
      ∃ blocks : Finset (Finset V),
        (∀ B∈blocks, B.card=3) ∧
        (∀ B∈blocks, ∀ x∈B, ∀ y∈B, x≠y → group x≠group y) ∧
        ∀ x y, group x≠group y → ∃! B : {B // B∈blocks}, x∈B.val ∧ y∈B.val
    let holeGroup {H R : Type} : H ⊕ (R × Bool) → Option R := Sum.elim (fun _ => none) (fun x => some x.1)
    (∀ u : ℕ, Design (holeGroup (H:=Fin 4) (R:=Fin (3*u)))) ∧
    (∀ u : ℕ, ∃ (V K : Type) (fv : Fintype V) (_fk : Fintype K) (g : V → K),
      letI := fv
      Design g ∧ Fintype.card V=2*u ∧
        ∀ i, Fintype.card {x // g x=i}=2 ∨ Fintype.card {x // g x=i}=4) := by
  let Design {V K : Type} (group : V → K) : Prop :=
    ∃ blocks : Finset (Finset V),
      (∀ B∈blocks, B.card=3) ∧
      (∀ B∈blocks, ∀ x∈B, ∀ y∈B, x≠y → group x≠group y) ∧
      ∀ x y, group x≠group y → ∃! B : {B // B∈blocks}, x∈B.val ∧ y∈B.val
  let holeGroup {H R : Type} : H ⊕ (R × Bool) → Option R := Sum.elim (fun _ => none) (fun x => some x.1)
  have from_index {V K I : Type} [Fintype I] (g : V → K) (b : I → Finset V)
      (three : ∀ i, (b i).card=3)
      (apart : ∀ i, ∀ x∈b i, ∀ y∈b i, x≠y → g x≠g y)
      (pair : ∀ x y, g x≠g y → ∃! i, x∈b i ∧ y∈b i) : Design g := by
    classical
    refine ⟨univ.image b,?_,?_,?_⟩
    · rintro _ h
      obtain ⟨i,_,rfl⟩ := mem_image.mp h
      exact three i
    · rintro _ h
      obtain ⟨i,_,rfl⟩ := mem_image.mp h
      exact apart i
    · intro x y h
      obtain ⟨i,hi,uniq⟩ := pair x y h
      refine ⟨⟨b i,mem_image.mpr ⟨i,mem_univ _,rfl⟩⟩,hi,?_⟩
      rintro ⟨B,hB⟩ hits
      obtain ⟨j,_,rfl⟩ := mem_image.mp hB
      exact Subtype.ext (congrArg b (uniq j hits))
  have transport {V K W L : Type} (e : V ≃ W) (g : V → K) (f : W → L)
      (group : ∀ x y, g x=g y ↔ f (e x)=f (e y)) (source : Design g) : Design f := by
    classical
    obtain ⟨B,three,apart,cover⟩ := source
    let b (i : {b // b∈B}) := i.val.map e.toEmbedding
    have mem (i) (x : V) : e x ∈ b i ↔ x ∈ i.val := by simp [b]
    apply from_index f b (fun i => by simpa [b] using three i.val i.property)
    · intro i x hx y hy ne
      obtain ⟨a,rfl⟩ := e.surjective x
      obtain ⟨d,rfl⟩ := e.surjective y
      exact fun eq => apart _ i.property _ ((mem i a).mp hx) _ ((mem i d).mp hy)
        (fun ae => ne (congrArg e ae)) ((group a d).mpr eq)
    · intro x y ne
      obtain ⟨a,rfl⟩ := e.surjective x
      obtain ⟨d,rfl⟩ := e.surjective y
      obtain ⟨i,⟨ha,hd⟩,unique⟩ := cover a d (fun eq => ne ((group a d).mp eq))
      exact ⟨i,⟨(mem i a).mpr ha,(mem i d).mpr hd⟩,fun j h =>
        unique j ⟨(mem j a).mp h.1,(mem j d).mp h.2⟩⟩
  have inflate {V K : Type} [Fintype V] (g : V → K) (master : Design g) :
      Design (fun x : V × Fin 3 => g x.1) := by
    classical
    obtain ⟨blocks,three,separate,unique⟩ := master
    let good (T : Finset (V × Fin 3)) := T.card=3 ∧ T.image Prod.fst ∈ blocks ∧ (∑ a∈T,a.2)=0
    let lifted := univ.filter good
    have membership (T : Finset (V × Fin 3)) : T∈lifted ↔ good T := by simp [lifted]
    have triple {A : Type} [DecidableEq A] (x y z : A) (xy : x≠y) (xz : x≠z) (yz : y≠z) :
        ({x,y,z} : Finset A).card=3 := by simp [xy,xz,yz]
    refine ⟨lifted,fun T h => ((membership T).mp h).1,?_,?_⟩
    · intro T h x hx y hy ne
      obtain ⟨card,base,_⟩ := (membership T).mp h
      have inj : Set.InjOn Prod.fst (T : Set (V × Fin 3)) := card_image_iff.mp ((three _ base).trans card.symm)
      exact separate _ base _ (mem_image_of_mem _ hx) _ (mem_image_of_mem _ hy) (fun e => ne (inj hx hy e))
    · rintro ⟨x,a⟩ ⟨y,b⟩ hgroup
      have hxy : x≠y := fun h => hgroup (congrArg g h)
      obtain ⟨B,⟨hx,hy⟩,only⟩ := unique x y hgroup
      let last := (B.val.erase x).erase y
      have hLast : last.card=1 := by
        dsimp [last]
        rw [card_erase_of_mem (mem_erase.mpr ⟨hxy.symm,hy⟩),card_erase_of_mem hx,three _ B.property]
      obtain ⟨z,hz⟩ := Finset.card_eq_one.mp hLast
      have zmem : z∈last := hz ▸ mem_singleton_self _
      have xz : x≠z := (mem_erase.mp (mem_erase.mp zmem).2).1.symm
      have yz : y≠z := (mem_erase.mp zmem).1.symm
      have hzB : z∈B.val := (mem_erase.mp (mem_erase.mp zmem).2).2
      have baseEq : ({x,y,z} : Finset V)=B.val := by
        apply eq_of_subset_of_card_le
        · intro p hp
          rcases (show p=x ∨ p=y ∨ p=z by simpa using hp) with rfl|rfl|rfl <;> assumption
        · rw [three _ B.property,triple _ _ _ hxy xz yz]
      let T (c : Fin 3) : Finset (V × Fin 3) := {(x,a),(y,b),(z,c)}
      have xy' : (x,a) ≠ (y,b) := fun h => hxy (congrArg Prod.fst h)
      have xz' (c : Fin 3) : (x,a) ≠ (z,c) := fun h => xz (congrArg Prod.fst h)
      have yz' (c : Fin 3) : (y,b) ≠ (z,c) := fun h => yz (congrArg Prod.fst h)
      have sz (c) : (T c).card=3 := triple _ _ _ xy' (xz' c) (yz' c)
      have pts (c) : (T c).image Prod.fst=B.val := by simpa [T] using baseEq
      have labels (c) : (∑ v∈T c,v.2)=a+(b+c) := by simp [T,xy',xz' c,yz' c]
      let c : Fin 3 := -(a+b)
      have balance : a+(b+c)=0 := by simp [c,←add_assoc]
      have yes : T c∈lifted := (membership _).mpr ⟨sz _,pts c ▸ B.property,(labels c).trans balance⟩
      refine ⟨⟨T c,yes⟩,⟨by simp [T],by simp [T]⟩,?_⟩
      rintro ⟨U,hU⟩ ⟨xa,yb⟩
      obtain ⟨uCard,uBase,uSum⟩ := (membership _).mp hU
      let A : {p // p∈blocks} := ⟨U.image Prod.fst,uBase⟩
      have proj : U.image Prod.fst=B.val := congrArg Subtype.val (only A ⟨mem_image_of_mem _ xa,mem_image_of_mem _ yb⟩)
      obtain ⟨⟨z',d⟩,zu,hz'⟩ := mem_image.mp (proj ▸ hzB : z∈U.image Prod.fst)
      obtain rfl : z'=z := hz'
      have exactU : T d=U := by
        apply eq_of_subset_of_card_le
        · intro p hp
          rcases (show p=(x,a) ∨ p=(y,b) ∨ p=(z',d) by simpa [T] using hp) with rfl|rfl|rfl <;> assumption
        · rw [sz,uCard]
      rw [←exactU,labels] at uSum
      have dc : d=c := add_left_cancel (add_left_cancel (uSum.trans balance.symm))
      exact Subtype.ext (exactU.symm.trans (congrArg T dc))
  have seed_3 : Design (holeGroup (H:=Fin 4) (R:=Fin 3)) := four_hole_seeds.1
  have seed_6 : Design (holeGroup (H:=Fin 4) (R:=Fin 6)) := four_hole_seeds.2
  have glue_designs {V K I : Type} {W : I → Type} {A : I → Type}
      [Fintype I] (group : V → K) (localGroup : (i : I) → W i → A i)
      (embed : (i : I) → W i ↪ V) (localDesign : ∀ i, Design (localGroup i))
      (sound : ∀ i x y, localGroup i x ≠ localGroup i y → group (embed i x) ≠ group (embed i y))
      (cover : ∀ x y, group x ≠ group y → ∃! i, ∃ a b : W i,
        embed i a=x ∧ embed i b=y ∧ localGroup i a≠localGroup i b) : Design group := by
    classical
    choose blocks card avoid complete using localDesign
    let family := univ.biUnion fun i => (blocks i).image (Finset.map (embed i))
    have origin {c : Finset V} : c∈family ↔ ∃ i b, b∈blocks i ∧ b.map (embed i)=c := by
      simp [family]
    refine ⟨family,?_,?_,?_⟩
    · intro c hc
      obtain ⟨i,b,hb,rfl⟩ := origin.mp hc
      simpa using card i b hb
    · intro c hc x hx y hy ne
      obtain ⟨i,b,hb,rfl⟩ := origin.mp hc
      obtain ⟨a,ha,rfl⟩ := mem_map.mp hx
      obtain ⟨d,hd,rfl⟩ := mem_map.mp hy
      exact sound _ _ _ (avoid i b hb a ha d hd (fun e => ne (congrArg (embed i) e)))
    · intro x y h
      obtain ⟨i,⟨a,b,rfl,rfl,ab⟩,only⟩ := cover x y h
      obtain ⟨s,⟨ha,hb⟩,unique⟩ := complete i a b ab
      let c : {s // s∈family} := ⟨s.val.map (embed i), origin.mpr ⟨i,s.val,s.property,rfl⟩⟩
      refine ⟨c,⟨mem_map.mpr ⟨a,ha,rfl⟩,mem_map.mpr ⟨b,hb,rfl⟩⟩,?_⟩
      rintro ⟨d,hd⟩ ⟨xa,xb⟩
      obtain ⟨j,r,hr,rfl⟩ := origin.mp hd
      obtain ⟨v,hv,hva⟩ := mem_map.mp xa
      obtain ⟨w,hw,hwc⟩ := mem_map.mp xb
      have vw : v≠w := by
        intro eq
        exact h (congrArg group (hva.symm.trans ((congrArg (embed j) eq).trans hwc)))
      have ji := only j ⟨v,w,hva,hwc,avoid j r hr v hv w hw vw⟩
      subst j
      obtain rfl := (embed i).injective hva
      obtain rfl := (embed i).injective hwc
      have eq := unique ⟨r,hr⟩ ⟨hv,hw⟩
      exact Subtype.ext (congrArg (Finset.map (embed i)) (congrArg Subtype.val eq))
  have fill_shared {I : Type} {R : I → Type} [Fintype I] [∀ i,Fintype (R i)]
      (outer : Design (fun x : Σ i, R i × Bool => x.1))
      (inner : ∀ i, Design (holeGroup (H:=Fin 4) (R:=R i))) :
      Design (holeGroup (H:=Fin 4) (R:=Σ i,R i)) := by
    classical
    let W : Option I → Type
      | none => Σ i, R i × Bool
      | some i => Fin 4 ⊕ (R i × Bool)
    let K : Option I → Type
      | none => I
      | some i => Option (R i)
    let group : ∀ j, W j → K j
      | none => fun x => x.1
      | some _ => holeGroup
    let V := Fin 4 ⊕ ((Σ i,R i) × Bool)
    let g := holeGroup (H:=Fin 4) (R:=Σ i,R i)
    let into (i : I) : R i ↪ (Σ j,R j) := ⟨Sigma.mk i,fun _ _ h => by simpa using h⟩
    let emb : ∀ j, W j ↪ V
      | none => ⟨fun x => Sum.inr (⟨x.1,x.2.1⟩,x.2.2), by
          rintro ⟨i,a,b⟩ ⟨j,c,d⟩ h
          obtain ⟨h,rfl⟩ := Prod.mk.inj (Sum.inr.inj h)
          cases h
          rfl⟩
      | some i => (Function.Embedding.refl (Fin 4)).sumMap
          ((into i).prodMap (Function.Embedding.refl Bool))
    let owner : V → V → Option I
      | .inl _,.inl _ => none
      | .inl _,.inr (r,_) => some r.1
      | .inr (r,_),.inl _ => some r.1
      | .inr (r,_),.inr (s,_) => if r.1=s.1 then some r.1 else none
    have design (j) : Design (group j) := by cases j with
      | none => exact outer
      | some i => exact inner i
    have tag (j) (x y : W j) (h : group j x≠group j y) :
        owner (emb j x) (emb j y)=j ∧ g (emb j x) ≠ g (emb j y) := by
      cases j with
      | none =>
        obtain ⟨i,a,b⟩ := x
        obtain ⟨k,c,d⟩ := y
        change i≠k at h
        change (if i=k then some i else none)=none ∧ some (Sigma.mk i a)≠some (Sigma.mk k c)
        exact ⟨if_neg h, fun e => h (congrArg Sigma.fst (Option.some.inj e))⟩
      | some i =>
        cases x with
        | inl a =>
          cases y with
          | inl b => exact False.elim (h rfl)
          | inr p => exact ⟨rfl,by intro e; cases e⟩
        | inr a =>
          cases y with
          | inl b => exact ⟨rfl,by intro e; cases e⟩
          | inr b =>
            change some a.1≠some b.1 at h
            exact ⟨if_pos rfl,fun e => h (congrArg some ((into i).injective (Option.some.inj e)))⟩
    apply glue_designs g group emb design (fun j x y h => (tag j x y h).2)
    intro x y ne
    have found : ∃ j,∃ a b : W j, emb j a=x ∧ emb j b=y ∧ group j a≠group j b := by
      cases x with
      | inl x =>
        cases y with
        | inl y => exact False.elim (ne rfl)
        | inr p =>
          obtain ⟨⟨i,a⟩,b⟩ := p
          exact ⟨some i,Sum.inl x,Sum.inr (a,b),rfl,rfl,by intro e; cases e⟩
      | inr p =>
        obtain ⟨⟨i,a⟩,b⟩ := p
        cases y with
        | inl y => exact ⟨some i,Sum.inr (a,b),Sum.inl y,rfl,rfl,by intro e; cases e⟩
        | inr q =>
          obtain ⟨⟨j,c⟩,d⟩ := q
          by_cases eq : i=j
          · subst j
            exact ⟨some i,Sum.inr (a,b),Sum.inr (c,d),rfl,rfl,fun e =>
              ne (congrArg some (congrArg (Sigma.mk i) (Option.some.inj e)))⟩
          · exact ⟨none,⟨i,a,b⟩,⟨j,c,d⟩,rfl,rfl,eq⟩
    obtain ⟨j,a,b,rfl,rfl,h⟩ := found
    refine ⟨j,⟨a,b,rfl,rfl,h⟩,?_⟩
    rintro k ⟨c,d,ec,ed,ne⟩
    have h1 := (tag k c d ne).1
    rw [ec,ed] at h1
    exact h1.symm.trans (tag j a b h).1
  have label_pairs (u : ℕ) (mate : Fin (2*u) → Fin (2*u))
      (inv : Function.Involutive mate) (free : ∀ x,mate x≠x) :
      ∃ e : Fin (2*u) ≃ (Fin u × Bool), ∀ x y, (e x).1=(e y).1 ↔ x=y ∨ mate x=y := by
    classical
    have twice (x) : mate (mate x)=x := inv x
    let R := {x : Fin (2*u) // x< mate x}
    let make (z : R × Bool) := if z.2 then mate z.1.val else z.1.val
    have hi (x) (h : ¬x< mate x) : mate x< mate (mate x) := by rw [inv]; exact lt_of_le_of_ne (not_lt.mp h) (free x)
    let split (x : Fin (2*u)) : R × Bool := if h : x< mate x then (⟨x,h⟩,false) else (⟨mate x,hi x h⟩,true)
    have left (x) : make (split x)=x := by
      by_cases h : x< mate x <;> simp [make,split,h,twice]
    have right (v : R × Bool) : split (make v)=v := by
      obtain ⟨⟨x,hx⟩,b⟩ := v
      cases b <;> simp [make,split,hx,twice,not_lt.mpr hx.le]
    let e : Fin (2*u) ≃ R × Bool := ⟨split,make,left,right⟩
    have c := Fintype.card_congr e
    simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool] at c
    let rows : R ≃ Fin u := Fintype.equivFinOfCardEq (by omega)
    refine ⟨e.trans (Equiv.prodCongr rows (Equiv.refl Bool)),?_⟩
    intro x y
    obtain ⟨⟨⟨a,ha⟩,i⟩,rfl⟩ := e.symm.surjective x
    obtain ⟨⟨⟨b,hb⟩,j⟩,rfl⟩ := e.symm.surjective y
    simp only [Equiv.trans_apply,Equiv.apply_symm_apply,Equiv.prodCongr_apply,Equiv.apply_eq_iff_eq ]
    have ab : a ≠ mate b := by intro h; rw [h,inv] at ha; exact (not_lt.mpr hb.le) ha
    have ba : mate a ≠ b := by intro h; rw [←h,inv] at hb; exact (not_lt.mpr ha.le) hb
    have reps : (⟨a,ha⟩ : R) = ⟨b,hb⟩ ↔ a=b := ⟨congrArg Subtype.val,fun h => by cases h; rfl⟩
    cases i <;> cases j <;> simp [e,make,twice,ab,ba,inv.injective.eq_iff,reps]
  have paired_design (u : ℕ) (hu : u%3=0 ∨ u%3=1) : Design (fun x : Fin u × Bool => x.1) := by
    classical
    obtain ⟨mate,inv,free,B,three,apart,pairs⟩ := AlspachTripleBlowup.matched_base (2*u) (by omega)
    obtain ⟨e,rel⟩ := label_pairs u mate inv free
    let g (x : Fin (2*u)) := (e x).1
    apply transport e g Prod.fst (fun _ _ => Iff.rfl)
    apply from_index g B three
    · intro i x hx y hy ne h
      exact (rel x y).mp h |>.elim ne (apart i x hx y hy ne)
    · intro x y h
      exact pairs x y (fun eq => h ((rel _ _).mpr (Or.inl eq))) (fun eq => h ((rel _ _).mpr (Or.inr eq)))
  have row_card {R : Type} [Fintype R] (i : R) :
      Fintype.card {x : R × Bool // x.1=i}=2 := by
    classical
    let e : Bool ≃ {x : R × Bool // x.1=i} :=
      { toFun := fun b => ⟨(i,b),rfl⟩
        invFun := fun x => x.val.2
        left_inv := fun b => rfl
        right_inv := by rintro ⟨⟨r,b⟩,hr⟩; exact Subtype.ext (Prod.ext hr.symm rfl) }
    simpa using (Fintype.card_congr e).symm
  have hole_card {R : Type} [Fintype R] (i : Option R) :
      Fintype.card {x : Fin 4 ⊕ (R × Bool) // holeGroup x=i}=2 ∨
      Fintype.card {x : Fin 4 ⊕ (R × Bool) // holeGroup x=i}=4 := by
    classical
    cases i with
    | none =>
      right
      let f (p : Fin 4) : {x : Fin 4 ⊕ (R × Bool) // holeGroup x=none} := ⟨Sum.inl p,rfl⟩
      have bij : Function.Bijective f := by
        refine ⟨fun a b eq => Sum.inl.inj (congrArg Subtype.val eq),?_⟩
        rintro ⟨a|b,h⟩
        · exact ⟨a,rfl⟩
        · simp [holeGroup] at h
      simpa using (Fintype.card_congr (Equiv.ofBijective f bij)).symm
    | some r =>
      left
      let f (b : Bool) : {x : Fin 4 ⊕ (R × Bool) // holeGroup x=some r} := ⟨Sum.inr (r,b),rfl⟩
      have bij : Function.Bijective f := by
        refine ⟨fun a b eq => congrArg Prod.snd (Sum.inr.inj (congrArg Subtype.val eq)),?_⟩
        rintro ⟨a|⟨i,b⟩,h⟩
        · simp [holeGroup] at h
        · have hr : i=r := Option.some.inj h
          subst i
          exact ⟨b,rfl⟩
      simpa using (Fintype.card_congr (Equiv.ofBijective f bij)).symm
  have hole_relabel {R S : Type} (e : R ≃ S)
      (d : Design (holeGroup (H:=Fin 4) (R:=R))) : Design (holeGroup (H:=Fin 4) (R:=S)) := by
    let a := (Equiv.refl (Fin 4)).sumCongr (e.prodCongr (Equiv.refl Bool))
    apply transport a holeGroup holeGroup _ d
    intro x y
    cases x <;> cases y <;> simp [a,holeGroup]
  have step_of_fill {V I : Type} [Fintype V] [Fintype I] (g : V → I) (d : Design g)
      (h : ∀ i, Fintype.card {x // g x=i}=2 ∨ Fintype.card {x // g x=i}=4)
      (rows : ℕ) (count : 2*rows=3*Fintype.card V)
      (fill : ∀ {I : Type} {R : I → Type} [Fintype I] [∀ i,Fintype (R i)],
        Design (fun x : Σ i,R i × Bool => x.1) →
        (∀ i,Design (holeGroup (H:=Fin 4) (R:=R i))) →
        Design (holeGroup (H:=Fin 4) (R:=Σ i,R i))) :
      Design (holeGroup (H:=Fin 4) (R:=Fin rows)) := by
    classical
    let Z (i : I) := {x : V // g x=i}
    let R (i : I) := Fin (3*(Fintype.card (Z i)/2))
    let lab (i : I) : (Z i × Fin 3) ≃ (R i × Bool) := Fintype.equivOfCardEq (by
      dsimp only [R]
      simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool]
      rcases h i with h|h <;> dsimp only [Z] <;> rw [h])
    let chart : V × Fin 3 ≃ Σ i,R i × Bool :=
      (((Equiv.sigmaFiberEquiv g).symm.prodCongr (Equiv.refl (Fin 3))).trans
        (Equiv.sigmaProdDistrib Z (Fin 3))).trans (Equiv.sigmaCongrRight lab)
    have outer := transport chart (fun x : V × Fin 3 => g x.1) (fun x : Σ i,R i × Bool => x.1)
      (fun _ _ => Iff.rfl) (inflate g d)
    have inner (i : I) : Design (holeGroup (H:=Fin 4) (R:=R i)) := by
      change Design (holeGroup (H:=Fin 4) (R:=Fin (3*(Fintype.card {x // g x=i}/2))))
      rcases h i with h|h
      · rw [h]; exact seed_3
      · rw [h]; exact seed_6
    have q := fill outer inner
    have size := Fintype.card_congr (chart.trans (Equiv.sigmaProdDistrib R Bool).symm)
    simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool] at size
    exact hole_relabel (Fintype.equivFinOfCardEq (by omega)) q
  have fiber_card_irrel {A : Type} {fa fb : Fintype A}
      (h : @Fintype.card A fa=2 ∨ @Fintype.card A fa=4) :
      @Fintype.card A fb=2 ∨ @Fintype.card A fb=4 := by
    have eq : fa=fb := Subsingleton.elim _ _
    cases eq
    exact h
  have four_hole (u : ℕ) : Design (holeGroup (H:=Fin 4) (R:=Fin (3*u))) := by
    classical
    induction u using Nat.strong_induction_on with
    | h u ih =>
      by_cases good : u%3=0 ∨ u%3=1
      · apply step_of_fill Prod.fst (paired_design u good) (fun i => Or.inl (row_card i)) _ _ (@fill_shared)
        simp
        omega
      · let v := u/3
        have small : v<u := by dsimp [v]; omega
        have eq : 3*v+2=u := by dsimp [v]; omega
        apply step_of_fill (holeGroup (H:=Fin 4) (R:=Fin (3*v))) (ih v small) _ (3*u) _ (@fill_shared)
        · intro i
          exact fiber_card_irrel (hole_card (R:=Fin (3*v)) i)
        · simp only [Fintype.card_sum,Fintype.card_fin,Fintype.card_prod,Fintype.card_bool]
          omega
  have master_for (u : ℕ) :
      ∃ (V K : Type) (fv : Fintype V) (_fk : Fintype K) (g : V → K),
        letI := fv
        Design g ∧ Fintype.card V=2*u ∧
          ∀ i, Fintype.card {x // g x=i}=2 ∨ Fintype.card {x // g x=i}=4 := by
    classical
    by_cases good : u%3=0 ∨ u%3=1
    · refine ⟨Fin u × Bool,Fin u,inferInstance,inferInstance,Prod.fst,paired_design u good,?_,
        fun i => Or.inl (row_card i)⟩
      simp; omega
    · let v := u/3
      have eq : 3*v+2=u := by dsimp [v]; omega
      refine ⟨Fin 4 ⊕ (Fin (3*v) × Bool), Option (Fin (3*v)),inferInstance,inferInstance,
        holeGroup,four_hole v,?_,?_⟩
      · simp only [Fintype.card_sum,Fintype.card_fin,Fintype.card_prod,Fintype.card_bool]
        omega
      · intro i
        exact fiber_card_irrel (hole_card (R:=Fin (3*v)) i)
  exact ⟨four_hole,master_for⟩

end AlspachGdd

namespace AlspachBlowup
open Finset SimpleGraph AlspachConjecture
open scoped Classical

/-- Turn a finite collection of cyclic vertex orders into actual graph cycles;
count the cycles at an edge by testing those vertex orders. -/
theorem realizations {W : Type} [DecidableEq W] {G : SimpleGraph W} {n l : ℕ} (hl : 3≤l)
    (v : Fin n → Fin l → W) (next : Fin l → Fin l) (hnext : ∀ i,(next i).val=(i.val+1)%l)
    (inj : ∀ r,Function.Injective (v r)) (adj : ∀ r j,G.Adj (v r j) (v r (next j))) :
    ∃ C : Multiset (Cycle G), lengths C=Multiset.replicate n l ∧ ∀ x y,
      (C.filter fun c => s(x,y)∈c.edges).card = (univ.filter fun r => ∃ j, s(x,y)=s(v r j,v r (next j))).card := by
  classical
  choose c len edges using fun r => AlspachLift.cycleFromListing hl (⟨v r,inj r⟩ : Fin l ↪ W) next hnext (adj r)
  refine ⟨univ.val.map c,?_,?_⟩
  · rw [lengths,Multiset.map_map,show (SimpleGraph.Cycle.length ∘ c) = fun _ => l from funext len,Multiset.map_const']
    simp
  · intro x y
    rw [Multiset.filter_map,Multiset.card_map]
    change (univ.filter (fun r => s(x,y)∈(c r).edges)).card = _
    congr 1
    ext r
    simp only [mem_filter,mem_univ,true_and,edges,Function.Embedding.coeFn_mk]

/-- A Latin square gives a nine-triangle decomposition of K₃,₃,₃. Choosing one
distinguished point in each group instead gives five triangles and three squares. -/
theorem face_options (G : SimpleGraph (Fin 3 × Fin 3))
    (adj : ∀ x y : Fin 3 × Fin 3, x.1≠y.1 → G.Adj x y) :
    let E (L : Multiset ℕ) := ∃ C : Multiset (Cycle G), lengths C=L ∧ ∀ x y,
      (C.filter fun c => s(x,y)∈c.edges).card = if x.1≠y.1 then 1 else 0
    E (Multiset.replicate 9 3) ∧ E (Multiset.replicate 5 3 + Multiset.replicate 3 4) := by
  intro E
  let latin : Fin 9 → Fin 3 → Fin 3 × Fin 3 := fun r j =>
    match r.val,j.val with
    | 0,0 => (0,0)
    | 0,1 => (1,0)
    | 0,2 => (2,0)
    | 1,0 => (0,0)
    | 1,1 => (1,1)
    | 1,2 => (2,1)
    | 2,0 => (0,0)
    | 2,1 => (1,2)
    | 2,2 => (2,2)
    | 3,0 => (0,1)
    | 3,1 => (1,0)
    | 3,2 => (2,1)
    | 4,0 => (0,1)
    | 4,1 => (1,1)
    | 4,2 => (2,2)
    | 5,0 => (0,1)
    | 5,1 => (1,2)
    | 5,2 => (2,0)
    | 6,0 => (0,2)
    | 6,1 => (1,0)
    | 6,2 => (2,2)
    | 7,0 => (0,2)
    | 7,1 => (1,1)
    | 7,2 => (2,0)
    | 8,0 => (0,2)
    | 8,1 => (1,2)
    | 8,2 => (2,1)
    | _,_ => (0,0)
  have latinInj : ∀ r, Function.Injective (latin r) := by decide
  have latinAdj : ∀ r j, (latin r j).1 ≠ (latin r (j+1)).1 := by decide
  obtain ⟨latinC,latinL,latinN⟩ := realizations (by decide : 3≤3) latin (·+1) (by decide) latinInj
    (fun r j => adj _ _ (latinAdj r j))
  let five : Fin 5 → Fin 3 → Fin 3 × Fin 3 := fun r j =>
    match r.val,j.val with
    | 0,0 => (0,0)
    | 0,1 => (1,0)
    | 0,2 => (2,0)
    | 1,0 => (0,1)
    | 1,1 => (1,1)
    | 1,2 => (2,1)
    | 2,0 => (0,1)
    | 2,1 => (1,2)
    | 2,2 => (2,2)
    | 3,0 => (0,2)
    | 3,1 => (1,1)
    | 3,2 => (2,2)
    | 4,0 => (0,2)
    | 4,1 => (1,2)
    | 4,2 => (2,1)
    | _,_ => (0,0)
  have fiveInj : ∀ r, Function.Injective (five r) := by decide
  have fiveAdj : ∀ r j, (five r j).1 ≠ (five r (j+1)).1 := by decide
  obtain ⟨fiveC,fiveL,fiveN⟩ := realizations (by decide : 3≤3) five (·+1) (by decide) fiveInj
    (fun r j => adj _ _ (fiveAdj r j))
  let square : Fin 3 → Fin 4 → Fin 3 × Fin 3 := fun r j =>
    match r.val,j.val with
    | 0,0 => (0,1)
    | 0,1 => (1,0)
    | 0,2 => (0,2)
    | 0,3 => (2,0)
    | 1,0 => (1,1)
    | 1,1 => (2,0)
    | 1,2 => (1,2)
    | 1,3 => (0,0)
    | 2,0 => (2,1)
    | 2,1 => (0,0)
    | 2,2 => (2,2)
    | 2,3 => (1,0)
    | _,_ => (0,0)
  have squareInj : ∀ r, Function.Injective (square r) := by decide
  have squareAdj : ∀ r j, (square r j).1 ≠ (square r (j+1)).1 := by decide
  obtain ⟨squareC,squareL,squareN⟩ := realizations (by decide : 3≤4) square (·+1) (by decide) squareInj
    (fun r j => adj _ _ (squareAdj r j))
  have exactLatin : ∀ x y : Fin 3 × Fin 3,
      (univ.filter fun r => ∃ j, s(x,y)=s(latin r j,latin r (j+1))).card =
        if x.1≠y.1 then 1 else 0 := by decide
  have exactMix : ∀ x y : Fin 3 × Fin 3,
      (univ.filter fun r => ∃ j, s(x,y)=s(five r j,five r (j+1))).card +
      (univ.filter fun r => ∃ j, s(x,y)=s(square r j,square r (j+1))).card =
        if x.1≠y.1 then 1 else 0 := by decide
  refine ⟨⟨latinC,latinL,fun x y => (latinN x y).trans (exactLatin x y)⟩,
    ⟨fiveC+squareC,?_,?_⟩⟩
  · exact (Multiset.map_add _ _ _).trans (congrArg₂ (·+·) fiveL squareL)
  · intro x y
    rw [Multiset.filter_add,Multiset.card_add,fiveN,squareN]
    exact exactMix x y

end AlspachBlowup

namespace AlspachBlowup
open SimpleGraph AlspachConjecture
open scoped Classical

/-- Transport a counted cycle family along a vertex embedding and give every
edge outside its image multiplicity zero. -/
theorem embed_family {W V : Type*} [DecidableEq W] [DecidableEq V] (f : W ↪ V) (G : SimpleGraph V)
    (P : W → W → Prop) [DecidableRel P] (L : Multiset ℕ)
    (localFamily : ∃ C : Multiset (Cycle (G.comap f)), lengths C=L ∧ ∀ a b,
      (C.filter fun c => s(a,b)∈c.edges).card = if P a b then 1 else 0) :
    ∃ D : Multiset (Cycle G), lengths D=L ∧ ∀ x y : V,
      (D.filter fun c => s(x,y)∈c.edges).card = if ∃ a b,x=f a ∧ y=f b ∧ P a b then 1 else 0 := by
  classical
  let H := G.comap f
  let h : H →g G := ⟨f,fun hab => hab⟩
  obtain ⟨C,hl,hc⟩ := localFamily
  let move (c : Cycle H) : Cycle G := ⟨f c.base,c.walk.map h,c.isCycle.map (f := h) f.injective⟩
  have mem (c : Cycle H) (a b : W) : s(f a,f b) ∈ (move c).edges ↔ s(a,b) ∈ c.edges := by
    change s(f a,f b) ∈ (c.walk.map h).edges ↔ _
    rw [Walk.edges_map]
    change Sym2.map f s(a,b) ∈ List.map (Sym2.map f) c.edges ↔ _
    exact List.mem_map_of_injective (Sym2.map.injective f.injective)
  have in_image {c : Cycle H} {x y : V} (hc : s(x,y) ∈ (move c).edges) :
      ∃ a b : W, x=f a ∧ y=f b := by
    change s(x,y) ∈ (c.walk.map h).edges at hc
    rw [Walk.edges_map,List.mem_map] at hc
    obtain ⟨e,_,he⟩ := hc
    induction e using Sym2.ind with
    | h a b =>
      change s(f a,f b)=s(x,y) at he
      rcases Sym2.eq_iff.mp he with ⟨p,q⟩|⟨p,q⟩
      · exact ⟨a,b,p.symm,q.symm⟩
      · exact ⟨b,a,q.symm,p.symm⟩
  refine ⟨C.map move,?_,?_⟩
  · have len (c : Cycle H) : (move c).length=c.length := Walk.length_map _ _
    simpa [lengths,Multiset.map_map,Function.comp_def,len] using hl
  · intro x y
    rw [Multiset.filter_map,Multiset.card_map]
    by_cases inside : ∃ a b : W, x=f a ∧ y=f b
    · obtain ⟨a,b,rfl,rfl⟩ := inside
      have hcount := hc a b
      change (C.filter fun c => s(a,b) ∈ c.edges).card = (if P a b then 1 else 0) at hcount
      simpa [Function.comp_def,mem] using hcount
    · have outside (c : Cycle H) : s(x,y) ∉ (move c).edges := fun he => inside (in_image he)
      have hnone : ¬∃ a b : W, x=f a ∧ y=f b ∧ P a b := by
        rintro ⟨a,b,ha,hb,_⟩
        exact inside ⟨a,b,ha,hb⟩
      rw [if_neg hnone]
      simp [outside]

end AlspachBlowup

namespace AlspachGdd
open AlspachBlowup SimpleGraph Finset AlspachConjecture
open scoped Classical

/-- A triple of base vertices yields either cycle family in the ambient
three-clone graph; the returned count is zero outside this triple. -/
theorem generic_region_options {V : Type} [DecidableEq V] (G : SimpleGraph (V × Fin 3)) (B : Finset (V)) (three : B.card=3)
    (adj : ∀ x y : V × Fin 3, x.1∈B → y.1∈B → x.1≠y.1 → G.Adj x y) :
    let E (L : Multiset ℕ) := ∃ C : Multiset (Cycle G), lengths C=L ∧ ∀ x y,
      (C.filter fun c => s(x,y)∈c.edges).card = if x.1≠y.1 ∧ x.1∈B ∧ y.1∈B then 1 else 0
    E (Multiset.replicate 9 3) ∧ E (Multiset.replicate 5 3 + Multiset.replicate 3 4) := by
  classical
  intro E
  let label : Fin 3 ≃ B := (Fintype.equivFinOfCardEq (by simpa only [Fintype.card_coe] using three)).symm
  let f : Fin 3 × Fin 3 ↪ V × Fin 3 := ⟨fun v => ((label v.1).val,v.2),by
    intro x y eq
    exact Prod.ext (label.injective (Subtype.ext (congrArg Prod.fst eq))) (congrArg (fun z : V × Fin 3 => z.2) eq)⟩
  let H := G.comap f
  have across (x y : Fin 3 × Fin 3) (diff : x.1≠y.1) : H.Adj x y := by
    apply adj (f x) (f y) (label x.1).property (label y.1).property
    exact fun h => diff (label.injective (Subtype.ext h))
  obtain ⟨plain,traded⟩ := face_options H across
  have equivalence (x y : V × Fin 3) : (∃ a b, x=f a ∧ y=f b ∧ a.1≠b.1) ↔ x.1≠y.1 ∧ x.1∈B ∧ y.1∈B := by
    constructor
    · rintro ⟨a,b,rfl,rfl,ne⟩
      exact ⟨fun eq => ne (label.injective (Subtype.ext eq)),(label a.1).property,(label b.1).property⟩
    · rintro ⟨ne,hx,hy⟩
      let a : Fin 3 := label.symm ⟨x.1,hx⟩
      let b : Fin 3 := label.symm ⟨y.1,hy⟩
      have hxa : (label a).val = x.1 := congrArg Subtype.val (label.apply_symm_apply _)
      have hyb : (label b).val = y.1 := congrArg Subtype.val (label.apply_symm_apply _)
      refine ⟨(a,x.2),(b,y.2),Prod.ext hxa.symm rfl,Prod.ext hyb.symm rfl,?_⟩
      intro h
      exact ne (hxa.symm.trans ((congrArg (fun w => (label w).val) h).trans hyb))
  have lift (L : Multiset ℕ) (family : ∃ C : Multiset (Cycle H), lengths C=L ∧ ∀ a b,
      (C.filter fun c => s(a,b)∈c.edges).card = if a.1≠b.1 then 1 else 0) : E L := by
    obtain ⟨C,len,count⟩ := embed_family f G (fun a b => a.1≠b.1) L family
    exact ⟨C,len,fun x y => by simpa only [equivalence] using count x y⟩
  exact ⟨lift _ plain,lift _ traded⟩

/-- Replace any t of the base triangles by the five-triangle, three-square
cover, leaving nine triangles over every unselected base triangle. -/
theorem stack_groups {N : ℕ} {V K : Type} [DecidableEq V] (G : SimpleGraph (V × Fin 3)) (g : V → K)
    (across : ∀ x y : V × Fin 3, g x.1≠g y.1 → G.Adj x y)
    (B : Fin N → Finset (V)) (three : ∀ i,(B i).card=3)
    (inside : ∀ i x, x∈B i → ∀ y, y∈B i → x≠y → g x≠g y)
    (pairs : ∀ x y,g x≠g y → ∃! i,x∈B i ∧ y∈B i)
    (t : ℕ) (ht : t≤N) :
    ∃ C : Multiset (Cycle G), lengths C=Multiset.replicate (9*(N-t)+5*t) 3+Multiset.replicate (3*t) 4 ∧
      ∀ x y : V × Fin 3, (C.filter fun c => s(x,y)∈c.edges).card =
        if g x.1≠g y.1 then 1 else 0 := by
  classical
  obtain ⟨T,_,size⟩ := Finset.exists_subset_card_eq (s:=(univ : Finset (Fin N))) (by simpa using ht)
  let L (i : Fin N) : Multiset ℕ := if i∈T then Multiset.replicate 5 3+Multiset.replicate 3 4 else Multiset.replicate 9 3
  have option (i : Fin N) : ∃ C : Multiset (Cycle G), lengths C=L i ∧ ∀ x y,
      (C.filter fun c => s(x,y)∈c.edges).card=if x.1≠y.1 ∧ x.1∈B i ∧ y.1∈B i then 1 else 0 := by
    obtain ⟨plain,traded⟩ := generic_region_options G (B i) (three i)
      (fun x y hx hy ne => across x y (inside i _ hx _ hy ne))
    by_cases h : i∈T
    · simpa only [L,if_pos h] using traded
    · simpa only [L,if_neg h] using plain
  choose C len count using option
  let D := ∑ i, C i
  have sumLen (S : Finset (Fin N)) : lengths (∑ i ∈ S,C i) = ∑ i ∈ S,L i := by
    induction S using Finset.induction_on with
    | empty => simp [lengths]
    | @insert i S hi ih => rw [sum_insert hi,sum_insert hi,show lengths (C i+∑ j∈S,C j)=lengths (C i)+lengths (∑ j∈S,C j) from Multiset.map_add _ _ _,len,ih]
  have lengthsD := sumLen univ
  have others : (univ.filter fun i => i∉T).card=N-t := by
    have id : (univ.filter fun i => i∉T) = univ \ T := by ext i; simp
    rw [id,card_sdiff_of_subset (subset_univ _),card_univ,Fintype.card_fin,size]
  have selected : univ.filter (fun i => i∈T) = T := by ext i; simp
  have lengthsAll : lengths D=Multiset.replicate (9*(N-t)+5*t) 3 + Multiset.replicate (3*t) 4 := by
    change lengths (∑ i,C i) = _
    rw [lengthsD]
    simp only [L,sum_ite,sum_const,selected,size,others,nsmul_add,Multiset.nsmul_replicate]
    rw [Multiset.replicate_add]
    simp only [Nat.mul_comm t 5,Nat.mul_comm t 3,Nat.mul_comm (N-t) 9]
    ac_rfl
  refine ⟨D,lengthsAll,?_⟩
  intro x y
  let P (i : Fin N) := x.1≠y.1 ∧ x.1∈B i ∧ y.1∈B i
  have sumCount (S : Finset (Fin N)) : ((∑ i∈S,C i).filter fun c => s(x,y)∈c.edges).card=
      ∑ i∈S,(if P i then 1 else 0) := by
    induction S using Finset.induction_on with
    | empty => simp
    | @insert i S hi ih => rw [sum_insert hi,sum_insert hi,Multiset.filter_add,Multiset.card_add,count,ih]
  rw [show D = ∑ i,C i from rfl,sumCount,← sum_filter]
  simp only [sum_const,nsmul_eq_mul,mul_one]
  change (univ.filter P).card = if g x.1≠g y.1 then 1 else 0
  by_cases h : g x.1≠g y.1
  · rw [if_pos h,Finset.card_eq_one]
    obtain ⟨i,hi,uniq⟩ := pairs _ _ h
    refine ⟨i,?_⟩
    ext j
    simp only [mem_filter,mem_univ,true_and,mem_singleton]
    exact ⟨fun hj => uniq _ hj.2,fun e => e ▸ And.intro (fun he => h (congrArg g he)) hi⟩
  · rw [if_neg h,Finset.card_eq_zero]
    apply Finset.filter_eq_empty_iff.mpr
    rintro i _ ⟨ne,hi,hj⟩
    exact h (inside i _ hi _ hj ne)

/-- Over t selected master blocks take the five triangles and three squares of
K₃,₃,₃, keeping nine triangles on all other master blocks. The embedding may
land in a larger graph; every edge outside the design has multiplicity zero. -/
theorem outer_traded {N : ℕ} {V K W : Type} [Fintype V] [DecidableEq V] [DecidableEq W]
    (g : V → K) (f : (V × Fin 3) ↪ W) (G : SimpleGraph W)
    (adj : ∀ x y : V × Fin 3,g x.1≠g y.1 → G.Adj (f x) (f y))
    (B : Fin N → Finset V) (three : ∀ i,(B i).card=3)
    (apart : ∀ i x, x∈B i → ∀ y, y∈B i → x≠y → g x≠g y)
    (unique : ∀ x y,g x≠g y → ∃! i,x∈B i ∧ y∈B i) (t : ℕ) (lim : t≤N) :
    ∃ C : Multiset (Cycle G), lengths C=Multiset.replicate (9*(N-t)+5*t) 3 + Multiset.replicate (3*t) 4 ∧
      ∀ x y : W, (C.filter fun c => s(x,y)∈c.edges).card =
        if ∃ a b, x=f a ∧ y=f b ∧ g a.1≠g b.1 then 1 else 0 := by
  obtain ⟨C,len,count⟩ := embed_family f G (fun a b => g a.1≠g b.1) _
    (stack_groups (G.comap f) g adj B three apart unique t lim)
  refine ⟨C,len,fun x y => ?_⟩
  by_cases h : ∃ a b,x=f a ∧ y=f b ∧ g a.1≠g b.1 <;> simpa only [h,if_true,if_false] using count x y

end AlspachGdd

namespace AlspachGdd
open Finset SimpleGraph AlspachConjecture
open scoped Classical

/-- The local designs cover the common-hole incidences and the within-group
edges. A single square fills the four edges between the two hole pairs. -/
theorem inner_cycles {I : Type} {R : I → Type} [Fintype I] [∀ i, Fintype (R i)]
    {n : ℕ} :
    let Design {V K : Type} (group : V → K) : Prop :=
      ∃ blocks : Finset (Finset V),
        (∀ B∈blocks, B.card=3) ∧
        (∀ B∈blocks, ∀ x∈B, ∀ y∈B, x≠y → group x≠group y) ∧
        ∀ x y, group x≠group y → ∃! B : {B // B∈blocks}, x∈B.val ∧ y∈B.val


    let holeGroup {H R : Type} : H ⊕ (R × Bool) → Option R := Sum.elim (fun _ => none) (fun x => some x.1)
    (∀ i, Design (holeGroup (H:=Fin 4) (R:=R i))) →
    ∀ (f : (Fin 4 ⊕ ((Σ i,R i) × Bool)) ≃ Fin n) (G : SimpleGraph (Fin n)),
    let pairRow : (Fin 4 ⊕ ((Σ i,R i) × Bool)) → Fin 2 ⊕ (Σ i,R i)
      | .inl x => .inl ⟨x.val/2,by have := x.isLt; omega⟩
      | .inr x => .inr x.1
    let seedRegion : (Fin 4 ⊕ ((Σ i,R i) × Bool)) → (Fin 4 ⊕ ((Σ i,R i) × Bool)) → Prop
      | .inr (a,_), .inr (b,_) => a.1=b.1
      | _,_ => True
    (∀ x y, G.Adj (f x) (f y) ↔ pairRow x ≠ pairRow y) →
    ∃ (p : ℕ) (C : Multiset (Cycle G)), lengths C = {4} + Multiset.replicate p 3 ∧ ∀ x y,
      (C.filter fun c => s(f x,f y) ∈ c.edges).card =
        if pairRow x ≠ pairRow y ∧ seedRegion x y then 1 else 0 := by
  classical
  intro Design holeGroup design f G pairRow seedRegion adj
  have spanning_cycles {V : Type} [Fintype V] [DecidableEq V] {T G : SimpleGraph V}
      [DecidableRel T.Adj] (sub : T ≤ G) (C : Multiset (Cycle T)) (dc : IsCycleDecomposition T C) :
      ∃ D : Multiset (Cycle G), lengths D=lengths C ∧ ∀ x y : V,
        (D.filter fun c => s(x,y)∈c.edges).card=if T.Adj x y then 1 else 0 := by
    classical
    let hom : T →g G := ⟨id,fun h => sub h⟩
    let move (c : Cycle T) : Cycle G := ⟨c.base,c.walk.map hom,c.isCycle.map (by exact Function.injective_id)⟩
    have len (c : Cycle T) : (move c).length=c.length := Walk.length_map _ _
    have edges (c : Cycle T) : (move c).edges=c.edges := by
      change (c.walk.map hom).edges=_
      rw [Walk.edges_map]
      change List.map (Sym2.map id) c.edges=c.edges
      simp
    refine ⟨C.map move,by simp [lengths,Multiset.map_map,len],?_⟩
    intro x y
    rw [Multiset.filter_map,Multiset.card_map]
    have eq : (C.filter ((fun c : Cycle G => s(x,y)∈c.edges) ∘ move)) =
        (C.filter (fun c : Cycle T => s(x,y)∈c.edges)) :=
      Multiset.filter_congr (fun c _ => by simp [edges])
    rw [eq]
    by_cases h : T.Adj x y
    · rw [if_pos h]
      apply Eq.trans _ (dc s(x,y) (SimpleGraph.mem_edgeFinset.mpr h))
      exact congrArg Multiset.card (Multiset.filter_congr (fun c _ => Iff.rfl))
    · have none (c : Cycle T) : s(x,y)∉c.edges := fun hit =>
        h (Walk.edges_subset_edgeSet c.walk hit)
      simp [h,none]
  have cycles_from_pieces {V I : Type} {W A : I → Type}
      [Fintype V] [DecidableEq V] [Fintype I] (T G : SimpleGraph V) (sub : T ≤ G)
      (localGroup : (i : I) → W i → A i) (emb : (i : I) → W i ↪ V)
      (design : ∀ i, Design (localGroup i))
      (sound : ∀ i a b, localGroup i a ≠ localGroup i b → T.Adj (emb i a) (emb i b))
      (cover : ∀ x y, T.Adj x y → ∃! i, ∃ a b : W i,
        emb i a=x ∧ emb i b=y ∧ localGroup i a≠localGroup i b) :
      ∃ (q : ℕ) (C : Multiset (Cycle G)), lengths C=Multiset.replicate q 3 ∧
        ∀ x y, (C.filter fun c => s(x,y)∈c.edges).card=if T.Adj x y then 1 else 0 := by
    classical
    choose blocks size valid complete using design
    let J := Σ i, {s // s ∈ blocks i}
    let tri (j : J) := j.2.val.map (emb j.1)
    obtain ⟨C,dc,sz,_⟩ := TriangleBridge.blocks_in_graph T tri
      (fun j => by simp [tri,size j.1 j.2.val j.2.property]) (by
        rintro ⟨i,B,hB⟩ x hx y hy ne
        obtain ⟨a,ha,rfl⟩ := mem_map.mp hx
        obtain ⟨b,hb,rfl⟩ := mem_map.mp hy
        exact sound i a b (valid i B hB a ha b hb (fun eq => ne (congrArg (emb i) eq)))) (by
        intro x y hxy
        obtain ⟨i,⟨a,b,rfl,rfl,ab⟩,only⟩ := cover x y hxy
        obtain ⟨B,⟨ha,hb⟩,unique⟩ := complete i a b ab
        refine ⟨⟨i,B⟩,⟨mem_map.mpr ⟨a,ha,rfl⟩,mem_map.mpr ⟨b,hb,rfl⟩⟩,?_⟩
        rintro ⟨j,D⟩ ⟨hx,hy⟩
        obtain ⟨v,hv,ex⟩ := mem_map.mp hx
        obtain ⟨w,hw,ey⟩ := mem_map.mp hy
        have ne : v ≠ w := fun eq => hxy.ne (ex.symm.trans ((congrArg (emb j) eq).trans ey))
        have ji := only j ⟨v,w,ex,ey,valid j D.val D.property v hv w hw ne⟩
        subst j
        obtain rfl := (emb i).injective ex
        obtain rfl := (emb i).injective ey
        exact congrArg (Sigma.mk i) (unique D ⟨hv,hw⟩))
    obtain ⟨D,sz',cnt⟩ := spanning_cycles sub C dc
    exact ⟨Fintype.card J,D,sz'.trans sz,cnt⟩
  let X := Fin 4 ⊕ ((Σ i,R i) × Bool)
  let W (i : I) := Fin 4 ⊕ (R i × Bool)
  let hg := holeGroup (H:=Fin 4) (R:=Σ i,R i)
  let allowed (x y : X) := hg x ≠ hg y ∧ seedRegion x y
  let A : SimpleGraph X := ⟨allowed,⟨by
    intro x y h
    exact ⟨Ne.symm h.1,by cases x <;> cases y <;> first | trivial | exact h.2.symm⟩⟩,
    ⟨fun _ h => h.1 rfl⟩⟩
  let T := A.comap f.symm
  have tiff (x y : X) : T.Adj (f x) (f y) ↔ allowed x y := by
    change allowed (f.symm (f x)) (f.symm (f y)) ↔ _
    simp
  have sub : T ≤ G := by
    intro x y e
    obtain ⟨x,rfl⟩ := f.surjective x
    obtain ⟨y,rfl⟩ := f.surjective y
    have h := ((tiff x y).mp e).1
    apply (adj _ _).mpr
    cases x <;> cases y <;> simp [pairRow,hg,holeGroup] at h ⊢
    exact h
  let into (i : I) : R i ↪ (Σ j,R j) := ⟨Sigma.mk i,fun _ _ h => by simpa using h⟩
  let emb (i : I) : W i ↪ X := (Function.Embedding.refl (Fin 4)).sumMap
    ((into i).prodMap (Function.Embedding.refl Bool))
  let owner : X → X → Option I
    | .inl _,.inl _ => none
    | .inl _,.inr (r,_) => some r.1
    | .inr (r,_),.inl _ => some r.1
    | .inr (r,_),.inr (s,_) => if r.1=s.1 then some r.1 else none
  have tag (i) (x y : W i) (h : holeGroup x ≠ holeGroup y) :
      owner (emb i x) (emb i y)=some i ∧ allowed (emb i x) (emb i y) := by
    cases x with
    | inl a => cases y with
      | inl b => exact False.elim (h rfl)
      | inr b => exact ⟨rfl,⟨fun e => (by cases e),trivial⟩⟩
    | inr a => cases y with
      | inl b => exact ⟨rfl,⟨fun e => (by cases e),trivial⟩⟩
      | inr b => exact ⟨if_pos rfl,fun e => h (congrArg some ((into i).injective (Option.some.inj e))),rfl⟩
  have cover (x y : X) (h : allowed x y) : ∃! i, ∃ a b : W i,
      emb i a=x ∧ emb i b=y ∧ holeGroup a ≠ holeGroup b := by
    have found : ∃ i, ∃ a b : W i, emb i a=x ∧ emb i b=y ∧ holeGroup a ≠ holeGroup b := by
      cases x with
      | inl x => cases y with
        | inl y => exact False.elim (h.1 rfl)
        | inr p =>
          obtain ⟨⟨i,a⟩,b⟩ := p
          exact ⟨i,Sum.inl x,Sum.inr (a,b),rfl,rfl,fun e => by cases e⟩
      | inr p =>
        obtain ⟨⟨i,a⟩,b⟩ := p
        cases y with
        | inl y => exact ⟨i,Sum.inr (a,b),Sum.inl y,rfl,rfl,fun e => by cases e⟩
        | inr p =>
          obtain ⟨⟨j,c⟩,d⟩ := p
          have ij : i=j := h.2
          subst j
          exact ⟨i,Sum.inr (a,b),Sum.inr (c,d),rfl,rfl,fun e =>
            h.1 (congrArg some (congrArg (Sigma.mk i) (Option.some.inj e)))⟩
    obtain ⟨i,a,b,rfl,rfl,hab⟩ := found
    refine ⟨i,⟨a,b,rfl,rfl,hab⟩,?_⟩
    rintro j ⟨v,w,ex,ey,vw⟩
    have e := (tag j v w vw).1
    rw [ex,ey,(tag i a b hab).1] at e
    exact Option.some.inj e.symm
  obtain ⟨p,D,sz,count⟩ := cycles_from_pieces T G sub
    (fun i => holeGroup (H:=Fin 4) (R:=R i)) (fun i => (emb i).trans f.toEmbedding)
    design (fun i a b h => (tiff _ _).mpr (tag i a b h).2) (by
      intro x y e
      obtain ⟨x,rfl⟩ := f.surjective x
      obtain ⟨y,rfl⟩ := f.surjective y
      simpa only [Function.Embedding.trans_apply,Equiv.coe_toEmbedding,Equiv.apply_eq_iff_eq]
        using cover x y ((tiff _ _).mp e))
  let holeCount : X → X → ℕ
    | .inl h,.inl k => if h.val/2 ≠ k.val/2 then 1 else 0
    | _,_ => 0
  have square : ∃ Q : Multiset (Cycle G), lengths Q={4} ∧ ∀ x y : X,
      (Q.filter fun c => s(f x,f y)∈c.edges).card=holeCount x y := by
    let v (i : Fin 4) := f (.inl i)
    let w : G.Walk (v 0) (v 0) :=
      .cons ((adj (.inl 0) (.inl 2)).mpr (by simp [pairRow]))
      (.cons ((adj (.inl 2) (.inl 1)).mpr (by simp [pairRow]))
      (.cons ((adj (.inl 1) (.inl 3)).mpr (by simp [pairRow]))
      (.cons ((adj (.inl 3) (.inl 0)).mpr (by simp [pairRow])) .nil)))
    have simple : w.IsCycle := by simp [w,v,Walk.isCycle_def]
    let c : Cycle G := ⟨_,w,simple⟩
    refine ⟨{c},rfl,?_⟩
    intro x y
    change (Multiset.filter _ (c ::ₘ 0)).card = _
    simp only [Multiset.filter_cons, Multiset.filter_zero, add_zero]
    change (if s(f x,f y) ∈ [s(v 0,v 2),s(v 2,v 1),s(v 1,v 3),s(v 3,v 0)]
      then ({c} : Multiset (Cycle G)) else 0).card = _
    cases x with
    | inl i => cases y with
      | inl j => fin_cases i <;> fin_cases j <;> simp [v,holeCount]
      | inr p => simp [v,holeCount]
    | inr p => cases y <;> simp [v,holeCount]
  obtain ⟨Q,qs,qc⟩ := square
  refine ⟨p,Q+D,?_,?_⟩
  · exact (Multiset.map_add _ _ _).trans (congrArg₂ (· + ·) qs sz)
  · intro x y
    rw [Multiset.filter_add,Multiset.card_add,qc,count]
    simp only [tiff]
    cases x with
    | inl a => cases y with
      | inl b => simp [holeCount,pairRow,seedRegion,allowed,hg,holeGroup,Fin.ext_iff]
      | inr b => simp [holeCount,pairRow,seedRegion,allowed,hg,holeGroup]
    | inr a => cases y with
      | inl b => simp [holeCount,pairRow,seedRegion,allowed,hg,holeGroup]
      | inr b => simp [holeCount,pairRow,seedRegion,allowed,hg,holeGroup]

end AlspachGdd

namespace AlspachGdd
open SimpleGraph Finset AlspachConjecture
open scoped Classical

theorem traded_chart {u t n : ℕ} (large : 3≤u) (bound : t≤u-1) {V K : Type}
    [Fintype V] [DecidableEq V] (g : V→K) :
    let Design {V K : Type} (group : V → K) : Prop :=
      ∃ blocks : Finset (Finset V),
        (∀ B∈blocks, B.card=3) ∧
        (∀ B∈blocks, ∀ x∈B, ∀ y∈B, x≠y → group x≠group y) ∧
        ∀ x y, group x≠group y → ∃! B : {B // B∈blocks}, x∈B.val ∧ y∈B.val
    let TradeX {K : Type} (R : K → Type) := Fin 4 ⊕ ((Σ i, R i) × Bool)
    let tradeRow {K : Type} {R : K → Type} : TradeX R → Fin 2 ⊕ (Σ i,R i)
      | .inl h => .inl ⟨h.val/2,by have := h.isLt; omega⟩
      | .inr x => .inr x.1
    let samePiece {K : Type} {R : K → Type} : TradeX R → TradeX R → Prop
      | .inr (r,_),.inr (s,_) => r.1=s.1
      | _,_ => True
    Design g → Fintype.card V=2*u →
    (∀ i,Fintype.card {x // g x=i} ≤4) →
    ∀ (R : K → Type) (ch : V × Fin 3 ≃ (Σ i,R i) × Bool), (∀ a,(ch a).1.1=g a.1) →
    ∀ (f : TradeX R ≃ Fin n) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    (∀ x y,G.Adj (f x) (f y) ↔ tradeRow x≠tradeRow y) →
    (∃ (p : ℕ) (C : Multiset (Cycle G)), lengths C={4}+Multiset.replicate p 3 ∧
      ∀ x y,(C.filter fun c => s(f x,f y)∈c.edges).card =
        if tradeRow x≠tradeRow y ∧ samePiece x y then 1 else 0) →
    ∃ (p : ℕ) (C : Multiset (Cycle G)), IsCycleDecomposition G C ∧
      lengths C= Multiset.replicate p 3 + Multiset.replicate (1+3*t) 4 := by
  intro Design TradeX tradeRow samePiece design size small R ch at_group f G _ adj inner
  classical
  have block_degree_sum {V K : Type} [Fintype V] (g : V → K) (blocks : Finset (Finset V))
      (three : ∀ B∈blocks,B.card=3)
      (apart : ∀ B∈blocks,∀ x∈B,∀ y∈B,x≠y → g x≠g y)
      (cover : ∀ x y,g x≠g y → ∃! B : {B // B∈blocks},x∈B.val ∧ y∈B.val) :
      6*blocks.card = ∑ x : V,(Fintype.card V - Fintype.card {y : V // g y=g x}) := by
    classical
    let G := (⊤ : SimpleGraph K).comap g
    let b (s : {B // B∈blocks}) := s.val
    obtain ⟨_,_,_,size⟩ := TriangleBridge.blocks_in_graph G b (fun i => three _ i.property)
      (fun i => apart _ i.property) cover
    rw [Fintype.card_coe] at size
    have deg (x : V) : G.degree x = Fintype.card V - Fintype.card {y : V // g y=g x} := by
      rw [←G.card_neighborFinset_eq_degree,G.neighborFinset_eq_filter]
      have eq : univ.filter (G.Adj x) = univ.filter (fun y => ¬g y=g x) := by
        ext y
        simp only [mem_filter,mem_univ,true_and]
        exact ne_comm
      rw [eq,←Fintype.card_subtype,Fintype.card_subtype_compl]
    have h := G.sum_degrees_eq_twice_card_edges
    simp only [deg] at h
    rw [size] at h
    omega
  have blocks_lower_bound {V K : Type} [Fintype V] (g : V → K) (blocks : Finset (Finset V))
      (three : ∀ B∈blocks,B.card=3)
      (apart : ∀ B∈blocks,∀ x∈B,∀ y∈B,x≠y → g x≠g y)
      (cover : ∀ x y,g x≠g y → ∃! B : {B // B∈blocks},x∈B.val ∧ y∈B.val)
      (small : ∀ i,Fintype.card {x : V // g x=i} ≤ 4) :
      Fintype.card V * (Fintype.card V-4) ≤ 6*blocks.card := by
    rw [block_degree_sum g blocks three apart cover]
    have h : ∑ _x : V,(Fintype.card V-4) ≤ ∑ x : V,(Fintype.card V-Fintype.card {y : V // g y=g x}) :=
      sum_le_sum (fun x _ => Nat.sub_le_sub_left (small (g x)) _)
    simpa only [sum_const,card_univ,smul_eq_mul] using h
  have indexed_master {u : ℕ} (large : 3≤u) {V K : Type} [Fintype V] (g : V → K)
      (master : Design g) (size : Fintype.card V=2*u)
      (small : ∀ i, Fintype.card {x // g x=i}≤4) :
      ∃ (N : ℕ) (B : Fin N → Finset V), u-1≤N ∧ (∀ i,(B i).card=3) ∧
        (∀ i,∀ x∈B i,∀ y∈B i,x≠y → g x≠g y) ∧
        (∀ x y,g x≠g y → ∃! i,x∈B i ∧ y∈B i) := by
    classical
    obtain ⟨F,three,apart,cover⟩ := master
    have h := blocks_lower_bound g F three apart cover small
    rw [size] at h
    have rem : 2*u-4 + 4 = 2*u := by omega
    have arith := Nat.zero_le ((2*u-1)*(u-3))
    have a : 2*u-1+1=2*u := by omega
    have b : u-3+3=u := by omega
    have goal : u-1 ≤ F.card := by
      have prod : 2*u*(2*u-4) + 8*u = 4*u*u := by nlinarith [congrArg (fun z : ℕ => 2*u*z) rem]
      nlinarith [congrArg (fun z : ℕ => z*(u-3)) a,congrArg (fun z : ℕ => 2*u*z) b,
        Nat.sub_add_cancel (show 1≤u by omega)]
    let label : Fin F.card ≃ F := (Fintype.equivFinOfCardEq (Fintype.card_coe F)).symm
    refine ⟨F.card,fun j => (label j).val,goal,fun j => three _ (label j).property,
      fun j => apart _ (label j).property,?_⟩
    intro x y h
    obtain ⟨i,hi,only⟩ := cover x y h
    refine ⟨label.symm i,by simpa only [Equiv.apply_symm_apply] using hi,?_⟩
    intro j hj
    exact label.injective ((only _ hj).trans (label.apply_symm_apply i).symm)
  obtain ⟨N,B,hn,three,apart,covers⟩ := indexed_master large g design size small
  let embed : V × Fin 3 ↪ Fin n := ⟨fun a => f (.inr (ch a)), fun _ _ eq => ch.injective (Sum.inr.inj (f.injective eq))⟩
  have across (a b : V × Fin 3) (ne : g a.1≠g b.1) : G.Adj (embed a) (embed b) := by
    apply (adj _ _).mpr
    change Sum.inr (α:=Fin 2) (ch a).1 ≠ Sum.inr (ch b).1
    intro eq
    exact ne ((at_group a).symm.trans ((congrArg Sigma.fst (Sum.inr.inj eq)).trans (at_group b)))
  obtain ⟨D,lD,dCount⟩ := outer_traded g embed G across B three apart covers t (bound.trans hn)
  obtain ⟨p,C,lC,cCount⟩ := inner
  have coverage (x y : TradeX R) : (∃ a b : V × Fin 3, f x=embed a ∧ f y=embed b ∧
        g a.1≠g b.1) ↔ ¬samePiece x y := by
    constructor
    · rintro ⟨a,b,ha,hb,neq⟩
      have ex : x=Sum.inr (ch a) := f.injective ha
      have ey : y=Sum.inr (ch b) := f.injective hb
      rw [ex,ey]
      change (ch a).1.1 ≠ (ch b).1.1
      simpa only [at_group] using neq
    · cases x with
      | inl x => exact fun h => False.elim (h trivial)
      | inr x =>
        cases y with
        | inl y => exact fun h => False.elim (h trivial)
        | inr y =>
          intro diff
          refine ⟨ch.symm x,ch.symm y,?_,?_,?_⟩
          · change f (Sum.inr x)=f (Sum.inr (ch (ch.symm x)))
            rw [ch.apply_symm_apply]
          · change f (Sum.inr y)=f (Sum.inr (ch (ch.symm y)))
            rw [ch.apply_symm_apply]
          · simpa only [←at_group,Equiv.apply_symm_apply] using (show x.1.1≠y.1.1 from diff)
  refine ⟨p+(9*(N-t)+5*t),C+D,?_,?_⟩
  · intro e
    induction e using Sym2.ind with
    | _ a b =>
      obtain ⟨x,rfl⟩ := f.surjective a
      obtain ⟨y,rfl⟩ := f.surjective b
      intro he
      have edge : G.Adj (f x) (f y) := SimpleGraph.mem_edgeFinset.mp he
      have ne := (adj x y).mp edge
      rw [Multiset.filter_add,Multiset.card_add,cCount,dCount]
      simp only [coverage]
      by_cases h : samePiece x y <;> simp [h,ne]
  · change (C+D).map SimpleGraph.Cycle.length=_
    rw [Multiset.map_add]
    change lengths C+lengths D=_
    rw [lC,lD,Multiset.replicate_add p (9*(N-t)+5*t),Multiset.replicate_add 1 (3*t),Multiset.replicate_one]
    ac_rfl

end AlspachGdd

namespace AlspachGdd
open Finset SimpleGraph AlspachConjecture
open scoped Classical

theorem four_chart : ∃ d : Fin 4 ≃ (Fin 2 × Bool), ∀ x : Fin 4,
    ((d x).1 : ℕ) = x.val/2 := by
  let code (x : Fin 4) : Fin 2 × Bool := (⟨x.val/2,by have := x.isLt; omega⟩, decide (x.val%2=1))
  have bij : Function.Bijective code := by dsimp [code]; decide
  exact ⟨Equiv.ofBijective code bij, fun _ => rfl⟩

/-- At orders 6u+4, start with a square around the shared hole and trade on
any t of the original master blocks before tripling their vertices. -/
theorem master_traded (u t : ℕ) (large : 3≤u) (lim : t≤u-1) :
    ∃ J : (completeGraph (Fin (6*u+4))).Subgraph, J.IsPerfectMatching ∧
      ∃ (p : ℕ) (C : Multiset (Cycle (completeGraph (Fin (6*u+4)) \ J.spanningCoe))),
        IsCycleDecomposition _ C ∧ lengths C=Multiset.replicate p 3 + Multiset.replicate (1+3*t) 4 := by
  classical
  let Design {V K : Type} (group : V → K) : Prop :=
    ∃ blocks : Finset (Finset V),
      (∀ B∈blocks, B.card=3) ∧
      (∀ B∈blocks, ∀ x∈B, ∀ y∈B, x≠y → group x≠group y) ∧
      ∀ x y, group x≠group y → ∃! B : {B // B∈blocks}, x∈B.val ∧ y∈B.val
  let holeGroup {H R : Type} : H ⊕ (R × Bool) → Option R := Sum.elim (fun _ => none) (fun x => some x.1)
  obtain ⟨V,K,instV,instK,g,master,size,fiber⟩ := recursive_designs.2 u
  let := instV
  let := instK
  let Z (i : K) := {x : V // g x=i}
  let R (i : K) := Fin (3*(Fintype.card (Z i)/2))
  let pairing (i : K) : Z i × Fin 3 ≃ R i × Bool := Fintype.equivOfCardEq (by
    dsimp only [R]
    simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool]
    rcases fiber i with h|h <;> dsimp only [Z] <;> rw [h])
  let hc : V × Fin 3 ≃ Σ i,R i × Bool :=
    (((Equiv.sigmaFiberEquiv g).symm.prodCongr (Equiv.refl (Fin 3))).trans
      (Equiv.sigmaProdDistrib Z (Fin 3))).trans (Equiv.sigmaCongrRight pairing)
  have inGroup (a : V × Fin 3) : (hc a).1=g a.1 := rfl
  let P := Σ i,R i
  let ch : V × Fin 3 ≃ P × Bool := hc.trans (Equiv.sigmaProdDistrib R Bool).symm
  have at_group (a : V × Fin 3) : (ch a).1.1=g a.1 := inGroup a
  have rows : Fintype.card P = 3*u := by
    have eq := Fintype.card_congr ch
    simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool,size] at eq
    omega
  have localDesign (i : K) : Design (holeGroup (H:=Fin 4) (R:=R i)) := by
    change Design (holeGroup (H:=Fin 4) (R:=Fin (3*(Fintype.card {x // g x=i}/2))))
    rcases fiber i with h|h
    · rw [h]; exact four_hole_seeds.1
    · rw [h]; exact four_hole_seeds.2
  let X := Fin 4 ⊕ (P × Bool)
  let tradeRow : X → Fin 2 ⊕ P
    | .inl h => .inl ⟨h.val/2,by have := h.isLt; omega⟩
    | .inr x => .inr x.1
  obtain ⟨hole,holeHalf⟩ := four_chart
  let m := 3*u+2
  let row : (Fin 2 ⊕ P) ≃ Fin m := Fintype.equivOfCardEq (by simp [m,rows]; omega)
  let f : (Fin m × Bool) ≃ Fin (6*u+4) := Fintype.equivOfCardEq (by simp [m]; omega)
  let lab : X ≃ Fin (6*u+4) := ((Equiv.sumCongr hole (Equiv.refl (P × Bool))).trans
    (Equiv.sumProdDistrib (Fin 2) P Bool).symm).trans ((row.prodCongr (Equiv.refl Bool)).trans f)
  have proj (x : X) : (f.symm (lab x)).1 = row (tradeRow x) := by
    cases x with
    | inl x =>
      simp only [lab,Equiv.trans_apply,Equiv.symm_apply_apply]
      exact congrArg (fun v : Fin 2 => row (Sum.inl v)) (Fin.ext (holeHalf x))
    | inr x => simp only [lab,Equiv.trans_apply,Equiv.symm_apply_apply]; rfl
  have build (G : SimpleGraph (Fin (6*u+4))) [DecidableRel G.Adj]
      (adj : ∀ x y, G.Adj x y ↔ (f.symm x).1≠(f.symm y).1) :
      ∃ (p : ℕ) (C : Multiset (Cycle G)), IsCycleDecomposition G C ∧
        lengths C=Multiset.replicate p 3 + Multiset.replicate (1+3*t) 4 := by
    have at_chart (x y : X) : G.Adj (lab x) (lab y) ↔ tradeRow x≠tradeRow y := by
      rw [adj,proj,proj,row.injective.ne_iff]
    apply traded_chart large lim g master size (fun i => by rcases fiber i with h|h <;> omega) R ch at_group lab G
      (by intro x y; cases x <;> cases y <;> exact at_chart _ _)
    obtain ⟨p,C,len,cov⟩ := inner_cycles localDesign lab G (by intro x y; cases x <;> cases y <;> exact at_chart _ _)
    refine ⟨p,C,len,?_⟩
    intro x y
    cases x <;> cases y <;> exact cov _ _
  obtain ⟨J,hJ,adj⟩ := AlspachSquares.pair_matching f
  exact ⟨J,hJ,build _ adj⟩

theorem minimal_from_raw (s : ℕ) (residue : (2*s)%6=4) :
    let Design {V K : Type} (group : V → K) : Prop :=
      ∃ blocks : Finset (Finset V),
        (∀ B∈blocks, B.card=3) ∧
        (∀ B∈blocks, ∀ x∈B, ∀ y∈B, x≠y → group x≠group y) ∧
        ∀ x y, group x≠group y → ∃! B : {B // B∈blocks}, x∈B.val ∧ y∈B.val


    let holeGroup {H R : Type} : H ⊕ (R × Bool) → Option R := Sum.elim (fun _ => none) (fun x => some x.1)
    (∀ u : ℕ, Design (holeGroup (H:=Fin 4) (R:=Fin (3*u)))) →
    ∃ J : (completeGraph (Fin (2*s))).Subgraph, J.IsPerfectMatching ∧
      ∃ (k : ℕ) (C : Multiset (Cycle (completeGraph (Fin (2*s)) \ J.spanningCoe))),
        IsCycleDecomposition _ C ∧ lengths C=Multiset.replicate k 3+{4} := by
  intro Design holeGroup designs
  classical
  have spanning_cycles {V : Type} [Fintype V] [DecidableEq V] {T G : SimpleGraph V}
      [DecidableRel T.Adj] (sub : T ≤ G) (C : Multiset (Cycle T)) (dc : IsCycleDecomposition T C) :
      ∃ D : Multiset (Cycle G), lengths D=lengths C ∧ ∀ x y : V,
        (D.filter fun c => s(x,y)∈c.edges).card=if T.Adj x y then 1 else 0 := by
    classical
    let hom : T →g G := ⟨id,fun h => sub h⟩
    let move (c : Cycle T) : Cycle G := ⟨c.base,c.walk.map hom,c.isCycle.map (by exact Function.injective_id)⟩
    have len (c : Cycle T) : (move c).length=c.length := Walk.length_map _ _
    have edges (c : Cycle T) : (move c).edges=c.edges := by
      change (c.walk.map hom).edges=_
      rw [Walk.edges_map]
      change List.map (Sym2.map id) c.edges=c.edges
      simp
    refine ⟨C.map move,by simp [lengths,Multiset.map_map,len],?_⟩
    intro x y
    rw [Multiset.filter_map,Multiset.card_map]
    have eq : (C.filter ((fun c : Cycle G => s(x,y)∈c.edges) ∘ move)) =
        (C.filter (fun c : Cycle T => s(x,y)∈c.edges)) :=
      Multiset.filter_congr (fun c _ => by simp [edges])
    rw [eq]
    by_cases h : T.Adj x y
    · rw [if_pos h]
      apply Eq.trans _ (dc s(x,y) (SimpleGraph.mem_edgeFinset.mpr h))
      exact congrArg Multiset.card (Multiset.filter_congr (fun c _ => Iff.rfl))
    · have none (c : Cycle T) : s(x,y)∉c.edges := fun hit =>
        h (Walk.edges_subset_edgeSet c.walk hit)
      simp [h,none]
  have design_cycles {W V K : Type} [Fintype V] [DecidableEq V] [DecidableEq W]
      (group : W → K) (design : Design group) (e : W ≃ V) (G : SimpleGraph V)
      (allowed : ∀ x y, group (e.symm x)≠group (e.symm y) → G.Adj x y) :
      ∃ (q : ℕ) (C : Multiset (Cycle G)), lengths C=Multiset.replicate q 3 ∧
        ∀ x y, (C.filter fun c => s(x,y)∈c.edges).card =
          if group (e.symm x)≠group (e.symm y) then 1 else 0 := by
    classical
    obtain ⟨blocks,three,valid,cover⟩ := design
    let T : SimpleGraph V := SimpleGraph.comap (fun x => group (e.symm x)) ⊤
    have adj (x y) : T.Adj x y ↔ group (e.symm x)≠group (e.symm y) := Iff.rfl
    let B := {b // b∈blocks}
    let tri (b : B) := b.val.map e.toEmbedding
    have mem (b : B) (x : V) : x∈tri b ↔ e.symm x∈b.val := by simp [tri]
    obtain ⟨cs,dec,lens,_⟩ := TriangleBridge.blocks_in_graph T tri
      (fun b => by simp [tri,three b.val b.property]) (by
        intro i x hx y hy ne
        exact (adj x y).mpr (valid i.val i.property _ ((mem i x).mp hx) _ ((mem i y).mp hy)
          (fun he => ne (e.symm.injective he)))) (by
        intro x y he
        obtain ⟨b,hb,one⟩ := cover (e.symm x) (e.symm y) ((adj x y).mp he)
        exact ⟨b,⟨(mem b x).mpr hb.1,(mem b y).mpr hb.2⟩,fun j hj =>
          one j ⟨(mem j x).mp hj.1,(mem j y).mp hj.2⟩⟩)
    obtain ⟨D,sz,count⟩ := spanning_cycles (T:=T) (G:=G) (fun _ _ he => allowed _ _ ((adj _ _).mp he)) cs dec
    exact ⟨Fintype.card B,D,sz.trans lens,count⟩
  have one_square_of_design {r n : ℕ} (order : n = 2*r+4)
      (design : Design (holeGroup (H:=Fin 4) (R:=Fin r))) :
      ∃ J : (completeGraph (Fin n)).Subgraph, J.IsPerfectMatching ∧
        ∃ (q : ℕ) (C : Multiset (Cycle (completeGraph (Fin n) \ J.spanningCoe))),
          IsCycleDecomposition _ C ∧ lengths C=Multiset.replicate q 3+{4} := by
    classical
    let k := r+2
    let f : (Fin k × Bool) ≃ Fin n := Fintype.equivOfCardEq (by simp [k]; omega)
    let p : (Fin 2 ⊕ Fin r) ≃ Fin k := Fintype.equivOfCardEq (by simp [k]; omega)
    let h : Fin 4 ≃ (Fin 2 × Bool) := Fintype.equivOfCardEq (by decide)
    let b := ((Equiv.sumCongr h (Equiv.refl (Fin r × Bool))).trans
      (Equiv.sumProdDistrib (Fin 2) (Fin r) Bool).symm).trans
      ((Equiv.prodCongr p (Equiv.refl Bool)).trans f)
    let key (a : Fin k) : Option (Fin r) := (p.symm a).elim (fun _ => none) some
    let row (x : Fin n) := (f.symm x).1
    have key_at (x : Fin n) : holeGroup (b.symm x) = key (row x) := by
      obtain ⟨⟨i,c⟩,rfl⟩ := f.surjective x
      obtain ⟨v,rfl⟩ := p.surjective i
      cases v <;> simp [b,key,row,holeGroup,Equiv.sumProdDistrib]
    obtain ⟨J,jp,adj⟩ := AlspachSquares.pair_matching f
    let G := completeGraph (Fin n) \ J.spanningCoe
    have allow (x y : Fin n) (different : holeGroup (b.symm x)≠holeGroup (b.symm y)) : G.Adj x y := by
      rw [key_at,key_at] at different
      exact (adj x y).mpr (fun eq => different (congrArg key eq))
    obtain ⟨q,D,dsz,dc⟩ := design_cycles _ design b G allow
    let l : Fin k := p (Sum.inl 0)
    let u : Fin k := p (Sum.inl 1)
    have lu : l≠u := by simp [l,u]
    obtain ⟨square,sz,edges⟩ := AlspachSquares.square f G adj lu
    have collision (i j : Fin k) (ne : i≠j) :
        key i=key j ↔ (i=l ∧ j=u) ∨ (i=u ∧ j=l) := by
      obtain ⟨i,rfl⟩ := p.surjective i
      obtain ⟨j,rfl⟩ := p.surjective j
      rcases i with i|i <;> rcases j with j|j
      · fin_cases i <;> fin_cases j <;> simp_all [l,u,key]
      · simp [key,l,u]
      · simp [key,l,u]
      · simpa [key,l,u] using ne
    refine ⟨J,jp,q,square ::ₘ D,?_,?_⟩
    · intro edge
      induction edge using Sym2.ind with
      | _ x y =>
        intro he
        simp only [mem_edgeFinset] at he
        have ne := (adj x y).mp he
        have sq : s(x,y)∈square.edges ↔ key (row x)=key (row y) :=
          (edges x y).trans (collision _ _ ne).symm
        have count := dc x y
        rw [key_at,key_at] at count
        rw [Multiset.filter_cons]
        by_cases same : key (row x)=key (row y)
        · rw [if_pos (sq.mpr same),Multiset.card_add,Multiset.card_singleton,count,if_neg (not_not_intro same)]
        · rw [if_neg (fun hit => same (sq.mp hit)),zero_add,count,if_pos same]
    · rw [add_comm,Multiset.singleton_add]
      simpa only [lengths,Multiset.map_cons,sz]
        using congrArg (Multiset.cons 4) dsz
  have one_square_order (designs : ∀ u : ℕ, Design (holeGroup (H:=Fin 4) (R:=Fin (3*u))))
      (s : ℕ) (residue : (2*s)%6=4) :
      ∃ J : (completeGraph (Fin (2*s))).Subgraph, J.IsPerfectMatching ∧
        ∃ (k : ℕ) (C : Multiset (Cycle (completeGraph (Fin (2*s)) \ J.spanningCoe))),
          IsCycleDecomposition _ C ∧ lengths C=Multiset.replicate k 3+{4} := by
    let u := (2*s)/6
    exact one_square_of_design (r:=3*u) (by dsimp [u]; omega) (designs u)
  exact one_square_order designs s residue

end AlspachGdd

namespace AlspachTripartite
open SimpleGraph AlspachConjecture Finset
open scoped Classical

/-- Three disjoint copies of one matched graph on W share the ambient vertex
set. The matching is replicated in each group, and so is the cycle decomposition. -/
theorem inner_copies_any {V W : Type*} [DecidableEq V] [Fintype W] [DecidableEq W]
    (e : (Fin 3 × W) ≃ V) (I : (completeGraph W).Subgraph) (perfect : I.IsPerfectMatching)
    (C : Multiset (Cycle (completeGraph W \ I.spanningCoe)))
    (DC : IsCycleDecomposition _ C) (K : Multiset ℕ) (sizes : lengths C=K) :
    ∃ J : (completeGraph V).Subgraph, J.IsPerfectMatching ∧
      (∀ x y : V,(e.symm x).1≠(e.symm y).1 → (completeGraph V \ J.spanningCoe).Adj x y) ∧
      ∃ (D : Multiset (Cycle (completeGraph V \ J.spanningCoe))),
        lengths D=K+K+K ∧ ∀ x y : V,(completeGraph V \ J.spanningCoe).Adj x y →
          (D.filter (fun v => s(x,y)∈v.edges)).card = if (e.symm x).1=(e.symm y).1 then 1 else 0 := by
  classical
  let J : (completeGraph V).Subgraph :=
    { verts := Set.univ
      Adj := fun x y => (e.symm x).1=(e.symm y).1 ∧ I.Adj (e.symm x).2 (e.symm y).2
      adj_sub := fun h xy => I.adj_sub h.2 (congrArg (fun z => (e.symm z).2) xy)
      edge_vert := fun _ => Set.mem_univ _
      symm := ⟨fun _ _ h => ⟨h.1.symm,h.2.symm⟩⟩ }
  have jp : J.IsPerfectMatching := by
    apply Subgraph.isPerfectMatching_iff.mpr
    intro x
    obtain ⟨b,adj,unique⟩ := Subgraph.isPerfectMatching_iff.mp perfect (e.symm x).2
    refine ⟨e ((e.symm x).1,b), ?_, ?_⟩
    · change _=(e.symm (e _)).1 ∧ I.Adj _ (e.symm (e _)).2
      rw [e.symm_apply_apply]
      exact ⟨rfl,adj⟩
    · rintro z ⟨hz,hb⟩
      apply e.symm.injective
      rw [e.symm_apply_apply]
      exact Prod.ext hz.symm (unique _ hb)
  let G := completeGraph V \ J.spanningCoe
  let F := completeGraph W \ I.spanningCoe
  have adj (x y : V) : G.Adj x y ↔ x≠y ∧
      ¬((e.symm x).1=(e.symm y).1 ∧ I.Adj (e.symm x).2 (e.symm y).2) := Iff.rfl
  have same (g : Fin 3) (a b : W) : G.Adj (e (g,a)) (e (g,b)) ↔ F.Adj a b := by
    change _ ↔ a≠b ∧ ¬I.Adj a b
    simp [adj,ne_eq]
  have cross (x y : V) (nn : (e.symm x).1≠(e.symm y).1) : G.Adj x y :=
    (adj _ _).mpr ⟨fun h => nn (congrArg (fun z => (e.symm z).1) h),fun k => nn k.1⟩
  let inc (g : Fin 3) : F →g G := ⟨fun x => e (g,x),fun h => (same g _ _).mpr h⟩
  have inj (g) : Function.Injective (inc g) := fun a b h => congrArg Prod.snd (e.injective h)
  let move (g : Fin 3) (c : Cycle F) : Cycle G := ⟨_,c.walk.map (inc g),c.isCycle.map (inj g)⟩
  have mem (k i j : Fin 3) (a b : W) (c : Cycle F) :
      s(e (i,a),e (j,b)) ∈ (move k c).edges ↔ i=k ∧ j=k ∧ s(a,b)∈c.edges := by
    change _ ∈ (c.walk.map (inc k)).edges ↔ _
    rw [Walk.edges_map,List.mem_map]
    constructor
    · rintro ⟨edge,hit,eq⟩
      induction edge using Sym2.ind with
      | h x y =>
        change s(e (k,x), e (k,y))=s(e (i,a),e (j,b)) at eq
        rcases Sym2.eq_iff.mp eq with ⟨hx,hy⟩|⟨hx,hy⟩
        · obtain ⟨rfl,rfl⟩ := Prod.mk.inj (e.injective hx)
          obtain ⟨_,rfl⟩ := Prod.mk.inj (e.injective hy)
          exact ⟨rfl,(congrArg Prod.fst (e.injective hy)).symm,hit⟩
        · obtain ⟨rfl,rfl⟩ := Prod.mk.inj (e.injective hx)
          obtain ⟨_,rfl⟩ := Prod.mk.inj (e.injective hy)
          refine ⟨(congrArg Prod.fst (e.injective hy)).symm,rfl,?_⟩
          rw [Sym2.eq_swap]; exact hit
    · rintro ⟨rfl,rfl,h⟩
      exact ⟨s(a,b),h,rfl⟩
  let part (g : Fin 3) := C.map (move g)
  have part_len (g) : lengths (part g)=K := by
    have len (c : Cycle F) : (move g c).length = c.length := Walk.length_map _ _
    simpa [part,lengths,Multiset.map_map,Function.comp_def,len] using sizes
  have part_count (k i j : Fin 3) (a b : W) (d : DecidablePred
      (fun c : Cycle G => s(e (i,a),e (j,b))∈c.edges)) :
      (@Multiset.filter _ (fun c => s(e (i,a),e (j,b))∈c.edges) d (part k)).card =
        if i=k ∧ j=k then (C.filter (fun c => s(a,b)∈c.edges)).card else 0 := by
    simp only [part,Multiset.filter_map,Multiset.card_map,Function.comp_def]
    by_cases h : i=k ∧ j=k
    · rw [if_pos h]
      exact congrArg Multiset.card (Multiset.filter_congr (fun c _ =>
        by simpa [h.1,h.2] using mem k i j a b c))
    · have no (c : Cycle F) : s(e (i,a),e (j,b))∉(move k c).edges :=
        fun h' => h ⟨((mem _ _ _ _ _ _).mp h').1,((mem _ _ _ _ _ _).mp h').2.1⟩
      simp [h,no]
  let D := part 0 + part 1 + part 2
  refine ⟨J,jp,cross,D,?_,?_⟩
  · change lengths (part 0+part 1+part 2)=_
    simp only [lengths,Multiset.map_add] at part_len ⊢
    rw [part_len,part_len,part_len]
  · intro x y hxy
    obtain ⟨⟨i,a⟩,rfl⟩ := e.surjective x
    obtain ⟨⟨j,b⟩,rfl⟩ := e.surjective y
    simp only [D,Multiset.filter_add,Multiset.card_add,e.symm_apply_apply]
    have one (eq : i=j) : (C.filter (fun c => s(a,b)∈c.edges)).card=1 := by
      subst j
      apply Eq.trans _ (DC s(a,b) ?_)
      · exact congrArg Multiset.card (Multiset.filter_congr (fun c _ => Iff.rfl))
      · refine (@SimpleGraph.mem_edgeFinset W F s(a,b) ?_).mpr ?_
        exact (same i a b).mp hxy
    have eval (i j : Fin 3) (N : ℕ) :
        (if i=0 ∧ j=0 then N else 0) + (if i=1 ∧ j=1 then N else 0) +
          (if i=2 ∧ j=2 then N else 0) = if i=j then N else 0 := by
      fin_cases i <;> fin_cases j <;> simp
    refine Eq.trans (congrArg₂ Nat.add (congrArg₂ Nat.add
      (part_count 0 i j a b _) (part_count 1 i j a b _)) (part_count 2 i j a b _)) ?_
    refine Eq.trans (eval i j _) ?_
    split_ifs with h
    · exact one h
    · rfl

end AlspachTripartite

namespace AlspachTripartite
open Finset SimpleGraph AlspachConjecture
open scoped Classical

/-- Fill the three parts with triangles, then use Latin-square octahedra between
the parts for the prescribed number of four-cycles. -/
theorem join_with_inner_squares {s n : ℕ} (f : ((Fin 3 × Fin s) × Bool) ≃ Fin n)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (across : ∀ x y, (f.symm x).1.1 ≠ (f.symm y).1.1 → G.Adj x y)
    {h k : ℕ} (inner : Multiset (Cycle G)) (insideLengths : lengths inner=Multiset.replicate h 3+Multiset.replicate k 4)
    (inside : ∀ x y, G.Adj x y → (inner.filter fun c => s(x,y)∈c.edges).card =
      if (f.symm x).1.1=(f.symm y).1.1 then 1 else 0)
    (L : Multiset ℕ) (shape : ∀ a∈L,a=3 ∨ a=4) (budget : L.sum=G.edgeFinset.card)
    {t : ℕ} (ht : t≤ s*s) (target : k+3*(s*s-t)=L.count 4) :
    ∃ C : Multiset (Cycle G), IsCycleDecomposition G C ∧ lengths C=L := by
  obtain ⟨outer,outLengths,outside⟩ := tripartite_trades f G (fun i j a b ne =>
    across _ _ (by simpa using ne)) t ht
  have dec : IsCycleDecomposition G (inner+outer) := by
    intro edge
    induction edge using Sym2.ind with
    | _ x y =>
      intro he
      have adj := G.mem_edgeFinset.mp he
      rw [Multiset.filter_add,Multiset.card_add,inside x y adj,outside x y]
      by_cases same : (f.symm x).1.1=(f.symm y).1.1 <;> simp [same]
  have lengthsAll : lengths (inner+outer) =
      Multiset.replicate (h+4*t) 3+Multiset.replicate (k+3*(s*s-t)) 4 := by
    rw [show lengths (inner+outer)=lengths inner+lengths outer by exact Multiset.map_add ..,
      insideLengths,outLengths,Multiset.replicate_add,Multiset.replicate_add]
    ac_rfl
  refine ⟨inner+outer,dec,lengthsAll.trans (match_list shape target ?_)⟩
  rw [←lengthsAll,AlspachLadder.decomposition_budget _ dec,budget]

/-- A single square in each of the three parts accounts for the first three
squares. Additional squares come in threes from the edges crossing the parts. -/
theorem twelve_from_one_square {s : ℕ} (residue : s%6=2)
    (one : ∃ J : (completeGraph (Fin (2*s))).Subgraph, J.IsPerfectMatching ∧
      ∃ (u : ℕ) (C : Multiset (Cycle (completeGraph (Fin (2*s)) \ J.spanningCoe))),
        IsCycleDecomposition _ C ∧ lengths C=Multiset.replicate u 3+{4})
    (I : (completeGraph (Fin (6*s))).Subgraph) (hI : I.IsPerfectMatching) (L : Multiset ℕ)
    (shape : ∀a∈L,a=3 ∨ a=4) (budget : L.sum=(6*s).choose 2-(6*s)/2) :
    ∃ C : Multiset (Cycle (completeGraph (Fin (6*s)) \ I.spanningCoe)), IsCycleDecomposition _ C ∧ lengths C=L := by
  classical
  by_cases high : (3*s)/2 ≤ L.count 4
  · have forOrder (n : ℕ) (hn : n=2*(3*s)) (J : (completeGraph (Fin n)).Subgraph)
        (hJ : J.IsPerfectMatching) (bud : L.sum=n.choose 2-n/2) :
        ∃ C : Multiset (Cycle (completeGraph (Fin n) \ J.spanningCoe)), IsCycleDecomposition _ C ∧ lengths C=L := by
      subst n
      have d : (3*s)%6=0 := by omega
      exact AlspachTrades.triangle_square_leave_lists (by omega) J hJ L shape bud (by simpa [d] using high)
    exact forOrder (6*s) (by omega) I hI budget
  by_cases no : 4∉L
  · obtain ⟨J,hJ,C,dc,sizes⟩ := AlspachTriple.all_triangles (6*s) (show Even (6*s) from ⟨3*s,by omega⟩)
      L (fun a ha => (shape a ha).resolve_right (fun eq => no (eq ▸ ha))) budget
    obtain ⟨iso⟩ := OMA.R_AlspachConjecture_alspach_conjecture_variants_even_R2.matchings_complements_iso J I hJ hI
    exact OMA.R_AlspachConjecture_alspach_conjecture_variants_even_R2.iso_decomposition iso dc sizes
  have pos : 0<L.count 4 := Multiset.count_pos.mpr (not_not.mp no)
  obtain ⟨k,hk⟩ := square_count_multiple s (by omega) L shape budget
  have divisible : 3 ∣ L.count 4 - 3 := ⟨k-1,by omega⟩
  obtain ⟨t,ht,hq⟩ := small_cross_square (s:=s) (by omega) (show L.count 4-3 < (3*s)/2 by omega) divisible
  obtain ⟨I0,p0,u,C0,d0,h0⟩ := one
  let f : ((Fin 3 × Fin s) × Bool) ≃ Fin (6*s) := Fintype.equivOfCardEq (by simp; omega)
  let labels : (Fin s × Bool) ≃ Fin (2*s) := Fintype.equivOfCardEq (by simp; omega)
  let e := (((Equiv.refl (Fin 3)).prodCongr labels.symm).trans
    (Equiv.prodAssoc (Fin 3) (Fin s) Bool).symm).trans f
  obtain ⟨J,perf,across,D,hD,count⟩ := inner_copies_any e I0 p0 C0 d0 _ h0
  let G := completeGraph (Fin (6*s)) \ J.spanningCoe
  have sizes : lengths D=Multiset.replicate (u+u+u) 3+Multiset.replicate 3 4 := by
    rw [hD,Multiset.replicate_add,Multiset.replicate_add]
    rw [show Multiset.replicate 3 (4 : ℕ) = {4}+{4}+{4} by decide]
    ac_rfl
  have edgeCount := TriangleBridge.matching_budget J perf
  rw [Fintype.card_fin] at edgeCount
  obtain ⟨C,dc,sz⟩ := join_with_inner_squares f G across D sizes count L shape (by
    rw [budget]
    convert edgeCount.symm using 1
    congr 1
    ext ed
    simp only [mem_edgeFinset,G]) ht (show 3+3*(s*s-t)=L.count 4 by omega)
  obtain ⟨iso⟩ := OMA.R_AlspachConjecture_alspach_conjecture_variants_even_R2.matchings_complements_iso J I perf hI
  exact OMA.R_AlspachConjecture_alspach_conjecture_variants_even_R2.iso_decomposition iso dc sz

end AlspachTripartite

namespace AlspachTripartite
open SimpleGraph AlspachConjecture
open scoped Classical

/-- At order 12 modulo 36, glue three matched complements with one square
each and choose the number of square decompositions on the crossing blocks. -/
theorem triangle_square_twelve_mod36 (n : ℕ) (residue : n%36=12)
    (I : (completeGraph (Fin n)).Subgraph) (hI : I.IsPerfectMatching) (L : Multiset ℕ)
    (shape : ∀a∈L,a=3 ∨ a=4) (budget : L.sum=n.choose 2-n/2) :
    ∃ C : Multiset (Cycle (completeGraph (Fin n) \ I.spanningCoe)),
      IsCycleDecomposition _ C ∧ lengths C=L := by
  obtain ⟨s,hr,rfl⟩ : ∃ s : ℕ, s%6=2 ∧ n=6*s := ⟨n/6,by omega,by omega⟩
  exact twelve_from_one_square hr (AlspachGdd.minimal_from_raw s (by omega)
    AlspachGdd.recursive_designs.1) I hI L shape budget

end AlspachTripartite

namespace AlspachGdd
open SimpleGraph AlspachConjecture
open scoped Classical

/-- For an order four modulo six, the edge budget forces one square modulo
three. The smallest positive square counts come from the four-point hole,
and the packing on matching pairs gives the larger counts. -/
theorem triangle_square_four_mod_six (n : ℕ) (residue : n%6=4)
    (I : (completeGraph (Fin n)).Subgraph) (hI : I.IsPerfectMatching)
    (L : Multiset ℕ) (shape : ∀ a∈L, a=3 ∨ a=4) (budget : L.sum=n.choose 2-n/2) :
    ∃ C : Multiset (Cycle (completeGraph (Fin n) \ I.spanningCoe)),
      IsCycleDecomposition _ C ∧ lengths C=L := by
  classical
  obtain ⟨u,rfl⟩ : ∃ u, n=6*u+4 := ⟨n/6,by omega⟩
  let m := 3*u+2
  have evenOrder : 6*u+4=2*m := by dsimp [m]; omega
  have hm : 0< m := by dsimp [m]; omega
  let leave := if m%6=1 ∨ m%6=3 then 0 else if m%6=0 ∨ m%6=2 then m/2 else m-1
  by_cases enough : leave ≤ L.count 4
  · have realize (N : ℕ) (order : N=2*m) (K : (completeGraph (Fin N)).Subgraph)
        (perfect : K.IsPerfectMatching) (size : L.sum=N.choose 2-N/2) :
        ∃ C : Multiset (Cycle (completeGraph (Fin N) \ K.spanningCoe)),
          IsCycleDecomposition _ C ∧ lengths C=L := by
      subst N
      exact AlspachTrades.triangle_square_leave_lists hm K perfect L shape size enough
    exact realize _ evenOrder I hI budget
  obtain ⟨j,upper,hL⟩ := AlspachTrades.classify_trades m hm L shape (by rwa [←evenOrder])
  have sq : L.count 4=m.choose 2-3*j := by simp [hL,Multiset.count_replicate]
  have step (a : ℕ) : (a+1).choose 2=a.choose 2+a := by
    simpa only [Nat.choose_one_right,Nat.add_comm] using Nat.choose_succ_succ a 1
  have count (v : ℕ) : (3*v+2).choose 2=9*v.choose 2+9*v+1 := by
    induction v with
    | zero => decide
    | succ v ih =>
      have size : 3*(v+1)+2=3*v+2+1+1+1 := by omega
      rw [size,step (3*v+2+1+1),step (3*v+2+1),step (3*v+2),step v,ih]
      omega
  have card : m.choose 2=9*u.choose 2+9*u+1 := count u
  have modulo : L.count 4 % 3=1 := by omega
  let Family (N k : ℕ) := ∃ J : (completeGraph (Fin N)).Subgraph, J.IsPerfectMatching ∧
    ∃ (p : ℕ) (C : Multiset (Cycle (completeGraph (Fin N) \ J.spanningCoe))),
      IsCycleDecomposition _ C ∧ lengths C=Multiset.replicate p 3 + Multiset.replicate k 4
  have family : Family (6*u+4) (L.count 4) := by
    by_cases large : 3≤u
    · have leave_le : leave ≤ 3*u+1 := by dsimp only [leave,m]; split_ifs <;> omega
      let t := L.count 4 / 3
      have ht : L.count 4=1+3*t := by dsimp [t]; omega
      rw [ht]
      exact master_traded u t large (by dsimp [t]; omega)
    · have small : u≤2 := by omega
      have tiny : leave ≤ 4 := by
        dsimp only [leave,m]
        have cases : u=0 ∨ u=1 ∨ u=2 := by omega
        rcases cases with rfl|rfl|rfl <;> decide
      have one : L.count 4=1 := by omega
      rw [one,evenOrder]
      obtain ⟨J,hJ,p,C,dec,sz⟩ := minimal_from_raw m (by omega) recursive_designs.1
      exact ⟨J,hJ,p,C,dec,by simpa only [Multiset.replicate_one] using sz⟩
  obtain ⟨J,hJ,p,C,dec,sz⟩ := family
  have edgeCount := TriangleBridge.matching_budget J hJ
  rw [Fintype.card_fin] at edgeCount
  have sums : (lengths C).sum=L.sum := by
    rw [AlspachLadder.decomposition_budget C dec,budget]
    convert edgeCount using 1
    congr 1
    ext e
    simp only [mem_edgeFinset]
  rw [sz,sq,hL,Multiset.sum_add,Multiset.sum_add] at sums
  simp only [Multiset.sum_replicate,smul_eq_mul] at sums
  have tri : p=4*j := by omega
  obtain ⟨iso⟩ := OMA.R_AlspachConjecture_alspach_conjecture_variants_even_R2.matchings_complements_iso J I hJ hI
  apply OMA.R_AlspachConjecture_alspach_conjecture_variants_even_R2.iso_decomposition iso dec
  rw [sz,tri,sq,hL]

end AlspachGdd

namespace AlspachTrades
open SimpleGraph AlspachConjecture
open scoped Classical

/-- Every admissible triangle/square list decomposes the complement of each
prescribed perfect matching of an even complete graph. -/
theorem all_triangle_square (n : ℕ) (even : Even n)
    (I : (completeGraph (Fin n)).Subgraph) (hI : I.IsPerfectMatching)
    (L : Multiset ℕ) (shape : ∀ a∈L,a=3 ∨ a=4) (budget : L.sum=n.choose 2-n/2) :
    ∃ C : Multiset (Cycle (completeGraph (Fin n) \ I.spanningCoe)),
      IsCycleDecomposition _ C ∧ lengths C=L := by
  by_cases zero : n=0
  · subst n
    have sum : L.sum=0 := by simpa using budget
    have empty (x) (hx : x∈L) : False := by
      have h := Multiset.sum_eq_zero_iff.mp sum x hx
      rcases shape x hx with h3 | h4 <;> omega
    exact AlspachPaired.all_square_hamilton 0 even I hI L (fun x hx => (empty x hx).elim)
      (fun x hx => (empty x hx).elim) budget
  by_cases steiner : n%12=2 ∨ n%12=6
  · exact triangle_square_lists n steiner I hI L shape budget
  by_cases eight : n%12=8
  · exact triangle_square_eight_mod_twelve n eight I hI L shape budget
  by_cases ten : n%12=10
  · exact triangle_square_ten_mod_twelve n ten I hI L shape budget
  by_cases tripartite : n%36=0 ∨ n%36=24
  · exact AlspachTripartite.triangle_square_0_24_mod36 n tripartite (by omega) I hI L shape budget
  obtain ⟨k,hk⟩ := even
  by_cases hole : n%6=4
  · exact AlspachGdd.triangle_square_four_mod_six n hole I hI L shape budget
  · exact AlspachTripartite.triangle_square_twelve_mod36 n (by omega) I hI L shape budget

end AlspachTrades

namespace AlspachTriHam

/-- The affine triples in the three layers cover every cross-layer pair once.
The first coordinate of the unique index is the shift. -/
theorem cross_faces {t : ℕ} [NeZero t] (odd : Odd t) :
    let V := Fin 3 × Fin t
    let face (a i : Fin t) : Finset V := {(0,i),(1,i+a),(2,i+a+a)}
    (∀ a i, (face a i).card=3) ∧
    (∀ a i (x y : V), x∈face a i → y∈face a i → x.1=y.1 → x=y) ∧
    (∀ x y : V, x.1 ≠ y.1 → ∃! z : Fin t × Fin t, x∈face z.1 z.2 ∧ y∈face z.1 z.2) := by
  obtain ⟨k,rfl⟩ : ∃ k, t=k+1 := ⟨t-1,by have := NeZero.ne t; omega⟩
  let : CommRing (Fin (k+1)) := inferInstanceAs (CommRing (ZMod (k+1)))
  intro V face
  let row (z : Fin (k+1) × Fin (k+1)) (k : Fin 3) :=
    if k.val=0 then z.2 else if k.val=1 then z.2+z.1 else z.2+z.1+z.1
  have mem (a i : Fin (k+1)) (x : V) : x∈face a i ↔ x.2=row (a,i) x.1 := by
    obtain ⟨c,v⟩ := x
    have h02 : (0 : Fin 3) ≠ 2 := by decide
    have h12 : (1 : Fin 3) ≠ 2 := by decide
    fin_cases c <;> norm_num [face,V,row,h02,h12]
    all_goals intros; rfl
  have twoZ : IsUnit (2 : ZMod (k+1)) := by
    simpa only [Nat.cast_ofNat] using (ZMod.isUnit_iff_coprime 2 (k+1)).2 odd.coprime_two_left
  have dblZ {a b : ZMod (k+1)} (same : a+a=b+b) : a=b := by
    apply twoZ.mul_right_inj.mp
    simpa only [two_mul] using same
  have dbl {a b : Fin (k+1)} (same : a+a=b+b) : a=b := @dblZ a b same
  have bij (c d : Fin 3) (distinct : c≠d) :
      Function.Bijective (fun z : Fin (k+1) × Fin (k+1) => (row z c,row z d)) := by
    have inj : Function.Injective (fun z : Fin (k+1) × Fin (k+1) => (row z c,row z d)) := by
      rintro ⟨a,i⟩ ⟨b,j⟩ eq
      have h := congrArg Prod.fst eq
      have k := congrArg Prod.snd eq
      change row (a,i) c=row (b,j) c at h
      change row (a,i) d=row (b,j) d at k
      fin_cases c <;> fin_cases d <;> first | contradiction | skip
      all_goals
        norm_num [row] at h k
        apply Prod.ext
        all_goals
          first
          | assumption
          | linear_combination h - k
          | linear_combination k - h
          | linear_combination h + h - k
          | linear_combination k + k - h
          | apply dbl; first | linear_combination h-k | linear_combination k-h
    exact ⟨inj,Finite.injective_iff_surjective.mp inj⟩
  refine ⟨?_,?_,?_⟩
  · intro a i
    simp [V,face]
  · intro a i x y hx hy same
    exact Prod.ext same (((mem a i x).mp hx).trans ((congrArg (row (a,i)) same).trans ((mem a i y).mp hy).symm))
  · intro x y distinct
    obtain ⟨z,hz⟩ := (bij _ _ distinct).2 (x.2,y.2)
    have hx : row z x.1=x.2 := congrArg Prod.fst hz
    have hy : row z y.1=y.2 := congrArg Prod.snd hz
    refine ⟨z,⟨(mem _ _ _).mpr hx.symm,(mem _ _ _).mpr hy.symm⟩,?_⟩
    intro w hw
    apply (bij _ _ distinct).1
    exact Prod.ext (((mem _ _ _).mp hw.1).symm.trans hx.symm) (((mem _ _ _).mp hw.2).symm.trans hy.symm)

end AlspachTriHam

namespace AlspachTriHam
open Finset

end AlspachTriHam

namespace AlspachTriHam

end AlspachTriHam



namespace AlspachTriHam
open Finset

/-- Visit the three colors cyclically and advance one row when the color wraps. -/
theorem round_robin (t : ℕ) [NeZero t] :
    let next := fun i : Fin (3*t) => (⟨(i.val+1)%(3*t),Nat.mod_lt _ (by have := i.isLt; omega)⟩ : Fin (3*t))
    ∃ chart : Fin (3*t) ≃ Fin 3 × Fin t, ∀ i,
      (chart (next i)).1=(chart i).1+1 ∧
      (chart (next i)).2=if (chart i).1=2 then (chart i).2+1 else (chart i).2 := by
  intro next
  have pos : 0<t := Nat.pos_of_ne_zero (NeZero.ne t)
  let split (i : Fin (3*t)) : Fin 3 × Fin t :=
    (⟨i.val%3,Nat.mod_lt _ (by decide)⟩,⟨i.val/3,by have := i.isLt; omega⟩)
  let join (p : Fin 3 × Fin t) : Fin (3*t) := ⟨3*p.2.val+p.1.val,by have := p.1.isLt; have := p.2.isLt; omega⟩
  let e : Fin (3*t) ≃ Fin 3 × Fin t := {
    toFun := split
    invFun := join
    left_inv := fun i => Fin.ext (by dsimp [split,join]; omega)
    right_inv := fun p => Prod.ext (Fin.ext (by dsimp [split,join]; have := p.1.isLt; omega))
      (Fin.ext (by dsimp [split,join]; have := p.1.isLt; omega)) }
  refine ⟨e,?_⟩
  intro i
  have hi := i.isLt
  have color2 : (e i).1=2 ↔ i.val%3=2 := by change (⟨i.val%3,_⟩ : Fin 3)=2 ↔ _; exact Fin.ext_iff
  have following : (next i).val=(i.val+1)%(3*t) := rfl
  by_cases wrap : i.val+1=3*t
  · have htwo : i.val%3=2 := by omega
    have row : i.val/3+1=t := by omega
    have endrow : (e i).2.val+1=t := row
    have zero : (next i).val=0 := by rw [following,wrap,Nat.mod_self]
    constructor
    · apply Fin.ext
      change (next i).val%3=(i.val%3+1)%3
      rw [zero,htwo]
    · rw [if_pos (color2.mpr htwo)]
      apply Fin.ext
      simp only [Fin.val_add,Fin.val_one',Nat.add_mod_mod]
      change (next i).val/3=_
      rw [zero,endrow,Nat.mod_self]
  · have before : i.val+1<3*t := by omega
    have val : (next i).val=i.val+1 := by rw [following,Nat.mod_eq_of_lt before]
    constructor
    · apply Fin.ext
      change (next i).val%3=(i.val%3+1)%3
      rw [val]
      omega
    · by_cases h : i.val%3=2
      · rw [if_pos (color2.mpr h)]
        apply Fin.ext
        simp only [Fin.val_add,Fin.val_one',Nat.add_mod_mod]
        change (next i).val/3=(i.val/3+1)%t
        rw [val,Nat.mod_eq_of_lt (by omega)]
        omega
      · rw [if_neg (fun h' => h (color2.mp h'))]
        apply Fin.ext
        change (next i).val/3=i.val/3
        rw [val]
        omega

end AlspachTriHam

namespace AlspachTriangleHamilton
open Finset SimpleGraph AlspachConjecture
open scoped Classical

/-- Double each base vertex. A Hamilton support contributes two Hamilton cycles;
an octahedron over a base triangle contributes four triangles. -/
theorem double_design {m r h : ℕ} (hm : 3≤ m) (σ : Fin r → (Fin m ≃ Fin m))
    (B : Fin h → Finset (Fin m)) (three : ∀ i,(B i).card=3) :
    let next (i : Fin m) : Fin m := ⟨(i.val+1)%m, Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩
    let H (i : Fin r) := univ.image fun z => s(σ i z,σ i (next z))
    let T (i : Fin h) := (⊤ : SimpleGraph (Fin m)).edgeFinset.filter fun e => e.toFinset ⊆ B i
    Pairwise (fun i j => Disjoint (H i) (H j)) → Pairwise (fun i j => Disjoint (T i) (T j)) →
    Disjoint (univ.biUnion H) (univ.biUnion T) →
    (⊤ : SimpleGraph (Fin m)).edgeFinset ⊆ univ.biUnion H ∪ univ.biUnion T →
    ∃ I : (completeGraph (Fin (2*m))).Subgraph, I.IsPerfectMatching ∧
      ∃ C : Multiset (Cycle (completeGraph (Fin (2*m)) \ I.spanningCoe)), IsCycleDecomposition _ C ∧
        lengths C=Multiset.replicate (2*r) (2*m)+Multiset.replicate (4*h) 3 := by
  classical
  intro next H T hs ts disjoint exhaustive
  let f : (Fin m × Bool) ≃ Fin (2*m) := Fintype.equivOfCardEq (by simp; omega)
  obtain ⟨I,hI,adj⟩ := AlspachSquares.pair_matching f
  let G := completeGraph (Fin (2*m)) \ I.spanningCoe
  let π := fun x : Fin (2*m) => (f.symm x).1
  let Covers (S : Finset (Sym2 (Fin m))) (L : Multiset ℕ) : Prop :=
    ∃ C : Multiset (Cycle G), lengths C = L ∧ ∀ x y : Fin (2*m),
      (C.filter fun c => s(x,y) ∈ c.edges).card = if s(π x,π y) ∈ S then 1 else 0
  obtain ⟨covers_union,covers_many⟩ := AlspachRegions.collect G π
  have across (i : Fin m) (a : Bool) (j : Fin m) (b : Bool) (ne : i≠j) :
      G.Adj (f (i,a)) (f (j,b)) := (adj _ _).mpr (by simpa using ne)
  have next_ne (x : Fin m) : x≠next x := by
    intro eq
    have q := congrArg Fin.val eq
    change x.val=(x.val+1)%m at q
    have hi := x.isLt
    by_cases lt : x.val+1< m
    · rw [Nat.mod_eq_of_lt lt] at q; omega
    · have equal : x.val+1=m := by omega
      rw [equal,Nat.mod_self] at q
      omega
  have hr (i : Fin r) : Covers (H i) (Multiset.replicate 2 (2*m)) :=
    AlspachLadder.hamilton_region hm f G (σ i) fun z a b =>
      across _ _ _ _ (fun eq => next_ne z ((σ i).injective eq))
  have tr (i : Fin h) : Covers (T i) (Multiset.replicate 4 3) :=
    AlspachLift.region_of_three f G across (B i) (three i)
  have left : Covers (univ.biUnion H) (Multiset.replicate (2*r) (2*m)) := by
    have a := covers_many univ H (fun _ => Multiset.replicate 2 (2*m)) (fun i _ => hr i)
      (fun _ _ _ _ ij => hs ij)
    simpa only [sum_const,card_univ,Fintype.card_fin,Multiset.nsmul_replicate,Nat.mul_comm r 2] using a
  have right : Covers (univ.biUnion T) (Multiset.replicate (4*h) 3) := by
    have a := covers_many univ T (fun _ => Multiset.replicate 4 3) (fun i _ => tr i)
      (fun _ _ _ _ ij => ts ij)
    simpa only [sum_const,card_univ,Fintype.card_fin,Multiset.nsmul_replicate,Nat.mul_comm h 4] using a
  obtain ⟨C,lens,occurs⟩ := covers_union left right disjoint
  refine ⟨I,hI,C,?_,lens⟩
  intro edge
  induction edge using Sym2.ind with
  | _ x y =>
    intro he
    have extract {ft : Fintype G.edgeSet} (q : s(x,y) ∈ @SimpleGraph.edgeFinset _ G ft) : G.Adj x y :=
      (@SimpleGraph.mem_edgeFinset _ G s(x,y) ft).mp q
    have a : G.Adj x y := extract he
    have base : s(π x,π y) ∈ (⊤ : SimpleGraph (Fin m)).edgeFinset := SimpleGraph.mem_edgeFinset.mpr ((adj _ _).mp a)
    exact (occurs x y).trans (if_pos (exhaustive base))

/-- Lift any disjoint selection of Hamilton and triangle supports, then cover
every unused base edge by the square joining its two pairs of vertices. -/
theorem double_partial {m r h : ℕ} (hm : 3≤ m) (σ : Fin r → (Fin m ≃ Fin m))
    (B : Fin h → Finset (Fin m)) (three : ∀ i,(B i).card=3) :
    let next (i : Fin m) : Fin m := ⟨(i.val+1)%m, Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩
    let H (i : Fin r) := univ.image fun z => s(σ i z,σ i (next z))
    let T (i : Fin h) := (⊤ : SimpleGraph (Fin m)).edgeFinset.filter fun e => e.toFinset ⊆ B i
    Pairwise (fun i j => Disjoint (H i) (H j)) → Pairwise (fun i j => Disjoint (T i) (T j)) →
    Disjoint (univ.biUnion H) (univ.biUnion T) →
    ∃ I : (completeGraph (Fin (2*m))).Subgraph, I.IsPerfectMatching ∧
      ∃ (q : ℕ) (C : Multiset (Cycle (completeGraph (Fin (2*m)) \ I.spanningCoe))), IsCycleDecomposition _ C ∧
        lengths C=Multiset.replicate (2*r) (2*m)+Multiset.replicate (4*h) 3 + Multiset.replicate q 4 ∧
        q+m*r+3*h=m.choose 2 := by
  classical
  intro next H T hs ts disjoint
  let f : (Fin m × Bool) ≃ Fin (2*m) := Fintype.equivOfCardEq (by simp; omega)
  obtain ⟨I,hI,adj⟩ := AlspachSquares.pair_matching f
  let G := completeGraph (Fin (2*m)) \ I.spanningCoe
  let π := fun x : Fin (2*m) => (f.symm x).1
  let Covers (S : Finset (Sym2 (Fin m))) (L : Multiset ℕ) : Prop :=
    ∃ C : Multiset (Cycle G), lengths C = L ∧ ∀ x y : Fin (2*m),
      (C.filter fun c => s(x,y) ∈ c.edges).card = if s(π x,π y) ∈ S then 1 else 0
  obtain ⟨covers_union,covers_many⟩ := AlspachRegions.collect G π
  have across (i : Fin m) (a : Bool) (j : Fin m) (b : Bool) (ne : i≠j) :
      G.Adj (f (i,a)) (f (j,b)) := (adj _ _).mpr (by simpa using ne)
  have next_ne (x : Fin m) : x≠next x := by
    intro eq
    have q := congrArg Fin.val eq
    change x.val=(x.val+1)%m at q
    have hi := x.isLt
    by_cases lt : x.val+1< m
    · rw [Nat.mod_eq_of_lt lt] at q; omega
    · have equal : x.val+1=m := by omega
      rw [equal,Nat.mod_self] at q
      omega
  have hr (i : Fin r) : Covers (H i) (Multiset.replicate 2 (2*m)) :=
    AlspachLadder.hamilton_region hm f G (σ i) fun z a b =>
      across _ _ _ _ (fun eq => next_ne z ((σ i).injective eq))
  have tr (i : Fin h) : Covers (T i) (Multiset.replicate 4 3) :=
    AlspachLift.region_of_three f G across (B i) (three i)
  have left : Covers (univ.biUnion H) (Multiset.replicate (2*r) (2*m)) := by
    have a := covers_many univ H (fun _ => Multiset.replicate 2 (2*m)) (fun i _ => hr i)
      (fun _ _ _ _ ij => hs ij)
    simpa only [sum_const,card_univ,Fintype.card_fin,Multiset.nsmul_replicate,Nat.mul_comm r 2] using a
  have right : Covers (univ.biUnion T) (Multiset.replicate (4*h) 3) := by
    have a := covers_many univ T (fun _ => Multiset.replicate 4 3) (fun i _ => tr i)
      (fun _ _ _ _ ij => ts ij)
    simpa only [sum_const,card_univ,Fintype.card_fin,Multiset.nsmul_replicate,Nat.mul_comm h 4] using a
  let used := univ.biUnion H ∪ univ.biUnion T
  let rest := (⊤ : SimpleGraph (Fin m)).edgeFinset \ used
  have sq (e : Sym2 (Fin m)) (he : e∈rest) : Covers {e} {4} := by
    induction e using Sym2.ind with
    | _ i j =>
      have ne : i≠j := SimpleGraph.mem_edgeFinset.mp (mem_sdiff.mp he).1
      exact AlspachLadder.square_region f G ne (fun a b => across i a j b ne)
  have tail : Covers rest (Multiset.replicate rest.card 4) := by
    have a := covers_many rest (fun e => {e}) (fun _ => ({4} : Multiset ℕ)) sq
      (fun i _ j _ ne => by simpa using ne)
    simpa [sum_const,Multiset.nsmul_singleton] using a
  have dj : Disjoint used rest := disjoint_left.mpr fun _ hx hr => (mem_sdiff.mp hr).2 hx
  obtain ⟨C,lens,occurs⟩ := covers_union (covers_union left right disjoint) tail dj
  have dec : IsCycleDecomposition (completeGraph (Fin (2*m)) \ I.spanningCoe) C := by
    intro edge
    induction edge using Sym2.ind with
    | _ x y =>
      intro he
      have extract {ft : Fintype G.edgeSet} (q : s(x,y) ∈ @SimpleGraph.edgeFinset _ G ft) : G.Adj x y :=
        (@SimpleGraph.mem_edgeFinset _ G s(x,y) ft).mp q
      have a : G.Adj x y := extract he
      have base : s(π x,π y) ∈ (⊤ : SimpleGraph (Fin m)).edgeFinset := SimpleGraph.mem_edgeFinset.mpr ((adj _ _).mp a)
      have member : s(π x,π y) ∈ used ∪ rest := by
        by_cases hx : s(π x,π y) ∈ used
        · exact mem_union_left _ hx
        · exact mem_union_right _ (mem_sdiff.mpr ⟨base,hx⟩)
      exact (occurs x y).trans (if_pos member)
  refine ⟨I,hI,rest.card,C,dec,lens,?_⟩
  have total := AlspachLadder.decomposition_budget C dec
  have ec := TriangleBridge.matching_budget I hI
  rw [Fintype.card_fin] at ec
  have agree : G.edgeFinset.card=(2*m).choose 2-(2*m)/2 := by
    exact ec
  have exactsum : (lengths C).sum=(2*m).choose 2-(2*m)/2 := by
    rw [total]
    convert agree using 1
    congr 1
    ext e
    simp only [mem_edgeFinset,G]
  rw [lens,Multiset.sum_add,Multiset.sum_add,Multiset.sum_replicate,
    Multiset.sum_replicate,Multiset.sum_replicate,AlspachPaired.paired_budget m (by omega)] at exactsum
  simp only [smul_eq_mul] at exactsum
  nlinarith only [exactsum]


theorem classify_mixed {m r h : ℕ} (hm : 3≤ m) (cells : m*r+3*h=m.choose 2)
    (L : Multiset ℕ) (shape : ∀ a∈L, a=3 ∨ a=4 ∨ a=2*m)
    (budget : L.sum=(2*m).choose 2-(2*m)/2) (ham : L.count (2*m)=2*r) :
    ∃ t, t≤h ∧ L.count 3=4*t ∧ L.count 4=3*(h-t) ∧
      L=Multiset.replicate (2*r) (2*m)+Multiset.replicate (4*t) 3+Multiset.replicate (3*(h-t)) 4 := by
  have n3 : 2*m≠3 := by omega
  have n4 : 2*m≠4 := by omega
  have split : L=Multiset.replicate (2*r) (2*m) + Multiset.replicate (L.count 3) 3 +
      Multiset.replicate (L.count 4) 4 := by
    ext a
    rcases eq_or_ne a (2*m) with rfl|hn
    · simp [Multiset.count_replicate,ham,Ne.symm n3,Ne.symm n4]
    rcases eq_or_ne a 3 with rfl|h3
    · simp [Multiset.count_replicate,n3]
    rcases eq_or_ne a 4 with rfl|h4
    · simp [Multiset.count_replicate,n4]
    have no : a∉L := fun h => (shape a h).elim h3 (fun v => v.elim h4 hn)
    simp [Multiset.count_replicate,Multiset.count_eq_zero.mpr no,Ne.symm h3,Ne.symm h4,Ne.symm hn]
  have eq := congrArg Multiset.sum split
  rw [budget,AlspachPaired.paired_budget m (by omega),Multiset.sum_add,Multiset.sum_add,
    Multiset.sum_replicate,Multiset.sum_replicate,Multiset.sum_replicate] at eq
  simp only [smul_eq_mul] at eq
  have left : 3*L.count 3+4*L.count 4=12*h := by nlinarith only [eq,cells]
  let t := L.count 3/4
  have hc : L.count 3=4*t := by dsimp [t]; omega
  have lim : t≤h := by omega
  have fours : L.count 4=3*(h-t) := by omega
  exact ⟨t,lim,hc,fours,by rwa [hc,fours] at split⟩

/-- Each complete Hamilton/triangle partition of the base realizes every
admissible mixture of 3, 4 and 2m with the prescribed number of Hamilton cycles. -/
theorem double_lists {m r h : ℕ} (hm : 3≤ m) (σ : Fin r → (Fin m ≃ Fin m))
    (B : Fin h → Finset (Fin m)) (three : ∀ i,(B i).card=3) :
    let next (i : Fin m) : Fin m := ⟨(i.val+1)%m, Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩
    let H (i : Fin r) := univ.image fun z => s(σ i z,σ i (next z))
    let T (i : Fin h) := (⊤ : SimpleGraph (Fin m)).edgeFinset.filter fun e => e.toFinset ⊆ B i
    Pairwise (fun i j => Disjoint (H i) (H j)) → Pairwise (fun i j => Disjoint (T i) (T j)) →
    Disjoint (univ.biUnion H) (univ.biUnion T) →
    (⊤ : SimpleGraph (Fin m)).edgeFinset ⊆ univ.biUnion H ∪ univ.biUnion T →
    ∀ (I : (completeGraph (Fin (2*m))).Subgraph), I.IsPerfectMatching → ∀ L : Multiset ℕ,
      (∀ a∈L, a=3 ∨ a=4 ∨ a=2*m) → L.sum=(2*m).choose 2-(2*m)/2 → L.count (2*m)=2*r →
      ∃ C : Multiset (Cycle (completeGraph (Fin (2*m)) \ I.spanningCoe)), IsCycleDecomposition _ C ∧ lengths C=L := by
  classical
  intro next H T hs ts dj full I hi L shape budget ham
  obtain ⟨I₀,h₀,C₀,dc,lens⟩ := double_design hm σ B three hs ts dj full
  have ecount := TriangleBridge.matching_budget I₀ h₀
  rw [Fintype.card_fin] at ecount
  have total : (lengths C₀).sum=(2*m).choose 2-(2*m)/2 := by
    rw [AlspachLadder.decomposition_budget C₀ dc]
    convert ecount using 1
    congr 1
    ext edge
    simp only [mem_edgeFinset]
  rw [lens,Multiset.sum_add,Multiset.sum_replicate,Multiset.sum_replicate,
    AlspachPaired.paired_budget m (by omega)] at total
  simp only [smul_eq_mul] at total
  have cells : m*r+3*h=m.choose 2 := by nlinarith only [total]
  obtain ⟨t,lim,_,_,sz⟩ := classify_mixed hm cells L shape budget ham
  let idx (i : Fin t) : Fin h := i.castLE lim
  have inj : Function.Injective idx := fun i j eq => Fin.ext (congrArg (fun z : Fin h => z.val) eq)
  have sep : Pairwise fun i j => Disjoint (T (idx i)) (T (idx j)) :=
    fun _ _ ne => ts (fun eq => ne (inj eq))
  have disj : Disjoint (univ.biUnion H) (univ.biUnion (fun i => T (idx i))) := by
    apply Finset.disjoint_left.mpr
    intro e he ht
    obtain ⟨i,_,hit⟩ := mem_biUnion.mp ht
    exact Finset.disjoint_left.mp dj he (mem_biUnion.mpr ⟨idx i,mem_univ _,hit⟩)
  obtain ⟨J,hJ,q,C,dec,len,square⟩ := double_partial hm σ (fun i => B (idx i)) (fun _ => three _) hs sep disj
  have hq : q=3*(h-t) := by omega
  obtain ⟨f⟩ := OMA.R_AlspachConjecture_alspach_conjecture_variants_even_R2.matchings_complements_iso J I hJ hi
  exact OMA.R_AlspachConjecture_alspach_conjecture_variants_even_R2.iso_decomposition f dec
    (by rwa [sz,←hq])

theorem relabel_cross_listings {m k : ℕ} {V A K : Type} [DecidableEq V]
    (f : Fin m ≃ V) (slot : Fin k ≃ A) (g : V→K) (σ : A → (Fin m ≃ V))
    (D : Finset (Finset V)) (three : ∀ B∈D,B.card=3) :
    let next (i : Fin m) : Fin m := ⟨(i.val+1)%m,Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩
    let ring (j : A) (x y : V) := ∃ i,s(x,y)=s(σ j i,σ j (next i))
    (∀ j x y, ring j x y → g x≠g y) →
    (∀ B∈D,∀ x∈B,∀ y∈B,x≠y → g x≠g y) →
    (∀ x y,g x≠g y → ∀ j k,ring j x y → ring k x y → j=k) →
    (∀ B∈D,∀ x∈B,∀ y∈B,g x≠g y → ∀ j,¬ring j x y) →
    (∀ x y,g x≠g y → (∀ j,¬ring j x y) → ∃! B : {B // B∈D},x∈B.val ∧ y∈B.val) →
    ∃ (order : Fin k → (Fin m ≃ Fin m)) (B : Fin D.card → Finset (Fin m)),
      let H (i : Fin k) := univ.image fun z => s(order i z,order i (next z))
      let T (i : Fin D.card) := (⊤ : SimpleGraph (Fin m)).edgeFinset.filter fun e => e.toFinset ⊆ B i
      (∀ j,(B j).card=3) ∧ (Pairwise fun i j => Disjoint (H i) (H j)) ∧
      (Pairwise fun i j => Disjoint (T i) (T j)) ∧ Disjoint (univ.biUnion H) (univ.biUnion T) ∧
      ∀ x y,s(x,y)∈univ.biUnion H ∪ univ.biUnion T ↔ g (f x)≠g (f y) := by
  classical
  intro next ring hCross tCross single avoids complete
  let block : Fin D.card ≃ D := (Fintype.equivFinOfCardEq (Fintype.card_coe D)).symm
  let order (j : Fin k) := (σ (slot j)).trans f.symm
  let B (i : Fin D.card) := (block i).val.map f.symm.toEmbedding
  refine ⟨order,B,?_⟩
  intro H T
  have hmem (i : Fin k) (x y : Fin m) : s(x,y)∈H i ↔ ring (slot i) (f x) (f y) := by
    constructor
    · rintro h
      obtain ⟨z,_,ez⟩ := mem_image.mp h
      exact ⟨z,by simpa [order] using congrArg (Sym2.map f) ez.symm⟩
    · rintro ⟨z,ez⟩
      exact mem_image.mpr ⟨z,mem_univ _,by simpa [order] using congrArg (Sym2.map f.symm) ez.symm⟩
  have tmem (i : Fin D.card) (x y : Fin m) : s(x,y)∈T i ↔
      x≠y ∧ f x∈(block i).val ∧ f y∈(block i).val := by
    simp [T,B,Sym2.toFinset_mk_eq,Finset.insert_subset_iff]
  refine ⟨fun i => by simp [B,three _ (block i).property],?_,?_,?_,?_⟩
  · intro i j ij
    apply Finset.disjoint_left.mpr
    intro e
    induction e using Sym2.ind with
    | _ x y =>
      intro hi hj
      have h := (hmem i x y).mp hi
      exact ij (slot.injective (single _ _ (hCross _ _ _ h) _ _ h ((hmem j x y).mp hj)))
  · intro i j ij
    apply Finset.disjoint_left.mpr
    intro e
    induction e using Sym2.ind with
    | _ x y =>
      intro hi hj
      obtain ⟨ne,xa,ya⟩ := (tmem _ _ _).mp hi
      obtain ⟨_,xb,yb⟩ := (tmem _ _ _).mp hj
      have diff := tCross _ (block i).property _ xa _ ya (f.injective.ne ne)
      have free := avoids _ (block i).property _ xa _ ya diff
      exact ij (block.injective ((complete _ _ diff free).unique ⟨xa,ya⟩ ⟨xb,yb⟩))
  · apply Finset.disjoint_left.mpr
    intro e
    induction e using Sym2.ind with
    | _ x y =>
      rintro he ht
      obtain ⟨i,_,hi⟩ := mem_biUnion.mp he
      obtain ⟨j,_,hj⟩ := mem_biUnion.mp ht
      obtain ⟨_,xa,ya⟩ := (tmem j x y).mp hj
      have hit := (hmem i x y).mp hi
      exact avoids _ (block j).property _ xa _ ya (hCross _ _ _ hit) _ hit
  · intro x y
    constructor
    · rintro he
      rcases mem_union.mp he with hit|hit
      · obtain ⟨i,_,h⟩ := mem_biUnion.mp hit
        exact hCross _ _ _ ((hmem _ _ _).mp h)
      · obtain ⟨i,_,h⟩ := mem_biUnion.mp hit
        obtain ⟨ne,a,b⟩ := (tmem _ _ _).mp h
        exact tCross _ (block i).property _ a _ b (f.injective.ne ne)
    · intro diff
      by_cases some : ∃ j,ring j (f x) (f y)
      · obtain ⟨j,hj⟩ := some
        obtain ⟨i,rfl⟩ := slot.surjective j
        exact mem_union_left _ (mem_biUnion.mpr ⟨i,mem_univ _,(hmem _ _ _).mpr hj⟩)
      · obtain ⟨d,hd,_⟩ := complete _ _ diff (fun j h => some ⟨j,h⟩)
        obtain ⟨i,rfl⟩ := block.surjective d
        exact mem_union_right _ (mem_biUnion.mpr ⟨i,mem_univ _,(tmem _ _ _).mpr ⟨fun eq => diff (congrArg (g ∘ f) eq),hd⟩⟩)

end AlspachTriangleHamilton

namespace AlspachTriHam
open Finset

end AlspachTriHam

namespace AlspachTriHam
open Finset SimpleGraph
open scoped Classical

end AlspachTriHam

namespace AlspachHamiltonMix
open Finset SimpleGraph AlspachConjecture
open scoped Classical

theorem cross_hamilton_region {V : Type} [DecidableEq V] {m : ℕ} (hm : 3 ≤ m) (f : (Fin m × Bool) ≃ V)
    (G : SimpleGraph V) (σ : Fin m ≃ Fin m) :
    let next (i : Fin m) : Fin m := ⟨(i.val+1)%m, Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩
    let baseSupport := univ.image (fun i => s(σ i,σ (next i)))
    (∀ i a b, G.Adj (f (σ i,a)) (f (σ (next i),b))) →
    ∃ C : Multiset (Cycle G), lengths C = Multiset.replicate 2 (2*m) ∧ ∀ x y : V,
      (C.filter fun c => s(x,y) ∈ c.edges).card =
        if s((f.symm x).1,(f.symm y).1) ∈ baseSupport then 1 else 0 := by
  intro next baseSupport adj
  let g := (Equiv.prodCongr σ (Equiv.refl Bool)).trans f
  obtain ⟨c,len,only,one⟩ := AlspachLift.liftPair_any hm g G next (fun _ => rfl) adj
  have support (i j : Fin m) : s(i,j) ∈ baseSupport ↔
      next (σ.symm i) = σ.symm j ∨ next (σ.symm j) = σ.symm i := by
    constructor
    · intro h
      obtain ⟨a,_,eq⟩ := mem_image.mp h
      rcases Sym2.eq_iff.mp eq with ⟨hi,hj⟩ | ⟨hj,hi⟩
      · exact Or.inl (by simp [← hi,← hj])
      · exact Or.inr (by simp [← hi,← hj])
    · rintro (h|h)
      · refine mem_image.mpr ⟨σ.symm i,mem_univ _,?_⟩
        simp [h]
      · refine mem_image.mpr ⟨σ.symm j,mem_univ _,?_⟩
        simp [h,Sym2.eq_swap]
  refine ⟨c false ::ₘ c true ::ₘ 0, by simp [lengths,len,Multiset.replicate_succ],?_⟩
  intro x y
  by_cases h : s((f.symm x).1,(f.symm y).1) ∈ baseSupport
  · obtain ⟨t,ht,unique⟩ := one x y ((support _ _).mp h)
    cases t with
    | false =>
      have hn : s(x,y) ∉ (c true).edges := fun ht' => by simpa using unique true ht'
      simp only [if_pos h,Multiset.filter_cons,if_pos ht,if_neg hn,Multiset.filter_zero]
      simp
    | true =>
      have hn : s(x,y) ∉ (c false).edges := fun ht' => by simpa using unique false ht'
      simp only [if_pos h,Multiset.filter_cons,if_pos ht,if_neg hn,Multiset.filter_zero]
      simp
  · have hn (t : Bool) : s(x,y) ∉ (c t).edges := fun ht => h ((support _ _).mpr (only t x y ht))
    simp [h,hn]

theorem cross_square_region {V : Type} [DecidableEq V] {m : ℕ} (f : (Fin m × Bool) ≃ V) (G : SimpleGraph V)
    {i j : Fin m} (diff : i ≠ j) (adj : ∀ a b, G.Adj (f (i,a)) (f (j,b))) :
    ∃ C : Multiset (Cycle G), lengths C = {4} ∧ ∀ x y : V,
      (C.filter fun c => s(x,y) ∈ c.edges).card =
        if s((f.symm x).1,(f.symm y).1) ∈ ({s(i,j)} : Finset _) then 1 else 0 := by
  let w : G.Walk (f (i,false)) (f (i,false)) :=
    .cons (adj false false) (.cons (adj true false).symm
      (.cons (adj true true) (.cons (adj false true).symm .nil)))
  have cycle : w.IsCycle := by simp [w,Walk.isCycle_def,diff,diff.symm]
  let c : Cycle G := ⟨_,w,cycle⟩
  have mem (x y : V) : s(x,y) ∈ c.edges ↔ s((f.symm x).1,(f.symm y).1) = s(i,j) := by
    obtain ⟨⟨r,a⟩,rfl⟩ := f.surjective x
    obtain ⟨⟨s,b⟩,rfl⟩ := f.surjective y
    change s(f (r,a), f (s,b)) ∈ [s(f (i,false), f (j,false)), s(f (j,false), f (i,true)),
      s(f (i,true), f (j,true)), s(f (j,true), f (i,false))] ↔ _
    rw [Sym2.eq_iff]
    cases a <;> cases b <;> simp
    grind
  refine ⟨{c},rfl,?_⟩
  intro x y
  change (Multiset.filter _ (c ::ₘ 0)).card = _
  simp only [Multiset.filter_cons,Multiset.filter_zero,Finset.mem_singleton,mem]
  split <;> simp_all

theorem cross_triangle_region {V : Type*} [DecidableEq V] {m : ℕ} (f : (Fin m × Bool) ≃ V)
    (G : SimpleGraph V)
    (i j k : Fin m) (hij : i≠j) (hik : i≠k) (hjk : j≠k)
    (ab : ∀ a b, G.Adj (f (i,a)) (f (j,b))) (bc : ∀ b d, G.Adj (f (j,b)) (f (k,d)))
    (ca : ∀ d a, G.Adj (f (k,d)) (f (i,a))) :
    ∃ C : Multiset (Cycle G), lengths C=Multiset.replicate 4 3 ∧ ∀ x y : V,
      (C.filter fun c => s(x,y) ∈ c.edges).card =
        if s((f.symm x).1,(f.symm y).1) ∈ ({s(i,j),s(i,k),s(j,k)} : Finset (Sym2 (Fin m))) then 1 else 0 := by
  classical
  let w (a b : Bool) : G.Walk (f (i,a)) (f (i,a)) :=
    .cons (ab a b) (.cons (bc b (a ^^ b)) (.cons (ca (a ^^ b) a) .nil))
  have simple (a b : Bool) : (w a b).IsCycle := by
    simp [w,Walk.isCycle_def,hij,hik,hjk,Ne.symm hij,Ne.symm hik]
  let c (a b : Bool) : Cycle G := ⟨f (i,a), w a b, simple a b⟩
  have length (a b : Bool) : (c a b).length=3 := rfl
  have edges (a b : Bool) (x y : Fin m × Bool) :
      s(f x,f y) ∈ (c a b).edges ↔
      s(x,y)=s((i,a),(j,b)) ∨ s(x,y)=s((j,b),(k,a ^^ b)) ∨ s(x,y)=s((k,a ^^ b),(i,a)) := by
    change s(f x,f y) ∈ [s(f (i,a),f (j,b)),s(f (j,b),f (k,a ^^ b)),s(f (k,a ^^ b),f (i,a))] ↔ _
    simp only [List.mem_cons,List.not_mem_nil,or_false,Sym2.eq_iff,Equiv.apply_eq_iff_eq]
  let C := c false false ::ₘ c false true ::ₘ c true false ::ₘ c true true ::ₘ 0
  refine ⟨C,by simp [C,lengths,length,Multiset.replicate_succ],?_⟩
  intro X Y
  obtain ⟨⟨x,u⟩,rfl⟩ := f.surjective X
  obtain ⟨⟨y,v⟩,rfl⟩ := f.surjective Y
  simp only [Equiv.symm_apply_apply]
  by_cases h : s(x,y) ∈ ({s(i,j),s(i,k),s(j,k)} : Finset (Sym2 (Fin m)))
  · rw [if_pos h]
    simp only [Finset.mem_insert,Finset.mem_singleton,Sym2.eq_iff] at h
    rcases h with (⟨rfl,rfl⟩|⟨rfl,rfl⟩) | (⟨rfl,rfl⟩|⟨rfl,rfl⟩) | (⟨rfl,rfl⟩|⟨rfl,rfl⟩)
    all_goals cases u <;> cases v <;>
      simp [C,Multiset.filter_singleton,edges,hij,hik,hjk,Ne.symm hij,Ne.symm hik,Ne.symm hjk]
  · rw [if_neg h]
    have none (a b : Bool) : s(f (x,u),f (y,v)) ∉ (c a b).edges := by
      intro he
      apply h
      rw [edges] at he
      simp only [Finset.mem_insert,Finset.mem_singleton,Sym2.eq_iff] at he ⊢
      simp only [Prod.mk.injEq] at he
      grind
    simp [C,Multiset.filter_singleton,none]

/-- Double a partition of the cross-color edges into cyclic listings and triples.
Each listing gives two Hamilton cycles. Each triple independently gives four
triangles or three squares, while no edge within a color is used. -/
theorem double_cross {m s h k : ℕ} (hm : 3≤ m) (hk : k≤h) {V K : Type}
    [DecidableEq V] [DecidableEq K] (f : (Fin m × Bool) ≃ V) (G : SimpleGraph V)
    (g : Fin m → K) (adj : ∀ i a j b, g i ≠ g j → G.Adj (f (i,a)) (f (j,b)))
    (σ : Fin s → (Fin m ≃ Fin m)) (B : Fin h → Finset (Fin m)) (three : ∀ i,(B i).card=3) :
    let next (i : Fin m) : Fin m := ⟨(i.val+1)%m, Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩
    let H (i : Fin s) := univ.image fun z => s(σ i z,σ i (next z))
    let T (i : Fin h) := (⊤ : SimpleGraph (Fin m)).edgeFinset.filter fun e => e.toFinset ⊆ B i
    Pairwise (fun i j => Disjoint (H i) (H j)) → Pairwise (fun i j => Disjoint (T i) (T j)) →
    Disjoint (univ.biUnion H) (univ.biUnion T) →
    (∀ a b : Fin m, s(a,b) ∈ univ.biUnion H ∪ univ.biUnion T ↔ g a ≠ g b) →
    ∃ C : Multiset (Cycle G), lengths C = Multiset.replicate (2*s) (2*m) +
      Multiset.replicate (4*k) 3 + Multiset.replicate (3*(h-k)) 4 ∧
      ∀ x y : V, (C.filter fun c => s(x,y)∈c.edges).card =
        if g (f.symm x).1 ≠ g (f.symm y).1 then 1 else 0 := by
  classical
  intro next H T hs ts sep all
  let π := fun x : V => (f.symm x).1
  let Covers (S : Finset (Sym2 (Fin m))) (L : Multiset ℕ) : Prop :=
    ∃ C : Multiset (Cycle G), lengths C = L ∧ ∀ x y : V,
      (C.filter fun c => s(x,y) ∈ c.edges).card = if s(π x,π y) ∈ S then 1 else 0
  obtain ⟨covers_union,covers_many⟩ := AlspachRegions.collect G π
  have hr (i : Fin s) : Covers (H i) (Multiset.replicate 2 (2*m)) := by
    apply cross_hamilton_region hm f G (σ i)
    intro z a b
    apply adj
    apply (all _ _).mp
    exact mem_union_left _ (mem_biUnion.mpr ⟨i,mem_univ _,mem_image.mpr ⟨z,mem_univ _,rfl⟩⟩)
  have left : Covers (univ.biUnion H) (Multiset.replicate (2*s) (2*m)) := by
    have a := covers_many univ H (fun _ => Multiset.replicate 2 (2*m)) (fun i _ => hr i)
      (fun _ _ _ _ ij => hs ij)
    simpa only [sum_const,card_univ,Fintype.card_fin,Multiset.nsmul_replicate,Nat.mul_comm s 2] using a
  have pieces (i : Fin h) :
      Covers (T i) (Multiset.replicate 4 3) ∧ Covers (T i) (Multiset.replicate 3 4) := by
    obtain ⟨a,b,c,ab,ac,bc,eq⟩ := Finset.card_eq_three.mp (three i)
    have support : T i = {s(a,b),s(a,c),s(b,c)} := by
      ext e
      induction e using Sym2.ind with
      | _ x y =>
        simp only [T,eq,mem_filter,SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet,
          SimpleGraph.top_adj,Sym2.toFinset_mk_eq,insert_subset_iff,singleton_subset_iff,
          mem_insert,mem_singleton,Sym2.eq_iff]
        grind
    have valid {x y : Fin m} (he : s(x,y)∈T i) : g x≠g y :=
      (all x y).mp (mem_union_right _ (mem_biUnion.mpr ⟨i,mem_univ _,he⟩))
    constructor
    · rw [support]
      apply cross_triangle_region f G a b c ab ac bc
      · exact fun p q => adj _ p _ q (valid (by simp [support]))
      · exact fun p q => adj _ p _ q (valid (by simp [support]))
      · exact fun p q => (adj _ q _ p (valid (by simp [support]))).symm
    · have sz : (T i).card=3 := by
        rw [support]
        simp [ab,ac,bc,Ne.symm ab,Ne.symm bc]
      have square (e : Sym2 (Fin m)) (he : e∈T i) : Covers {e} {4} := by
        induction e using Sym2.ind with
        | _ x y =>
          have different := valid he
          exact cross_square_region f G (fun eq => different (congrArg g eq)) (fun p q => adj _ p _ q different)
      have family := covers_many (T i) (fun e => {e}) (fun _ => ({4} : Multiset ℕ)) square
        (fun i _ j _ ne => by simpa using ne)
      simpa [sum_const,Multiset.nsmul_singleton,sz] using family
  obtain ⟨A,sub,hA⟩ := exists_subset_card_eq (s:=(univ : Finset (Fin h))) (show k≤univ.card by simpa using hk)
  let R := (univ : Finset (Fin h)) \ A
  have hR : R.card=h-k := by
    change (univ \ A).card=h-k
    rw [card_sdiff_of_subset sub,card_univ,Fintype.card_fin,hA]
  have toTri : Covers (A.biUnion T) (Multiset.replicate (4*k) 3) := by
    have a := covers_many A T (fun _ => Multiset.replicate 4 3) (fun i _ => (pieces i).1)
      (fun _ _ _ _ ij => ts ij)
    simpa only [sum_const,Multiset.nsmul_replicate,hA,Nat.mul_comm k 4] using a
  have toSq : Covers (R.biUnion T) (Multiset.replicate (3*(h-k)) 4) := by
    have a := covers_many R T (fun _ => Multiset.replicate 3 4) (fun i _ => (pieces i).2)
      (fun _ _ _ _ ij => ts ij)
    simpa only [sum_const,Multiset.nsmul_replicate,hR,Nat.mul_comm (h-k) 3] using a
  have split : A.biUnion T ∪ R.biUnion T = univ.biUnion T := by
    rw [←union_biUnion,show A ∪ R=univ from union_sdiff_of_subset sub]
  have ds : Disjoint (A.biUnion T) (R.biUnion T) := by
    apply Finset.disjoint_left.mpr
    intro e h1 h2
    obtain ⟨i,hi,hei⟩ := mem_biUnion.mp h1
    obtain ⟨j,hj,hej⟩ := mem_biUnion.mp h2
    have ij : i≠j := fun eq => (mem_sdiff.mp hj).2 (eq ▸ hi)
    exact Finset.disjoint_left.mp (ts ij) hei hej
  have right := covers_union toTri toSq ds
  rw [split] at right
  obtain ⟨C,lens,freq⟩ := covers_union left right sep
  refine ⟨C,by simpa only [add_assoc] using lens,?_⟩
  intro x y
  simpa only [all] using freq x y

/-- The doubled outer construction takes any partition of the three-part
edges into s Hamilton cycles and t(t−s) triangles. -/
theorem outer_of_base {t s : ℕ} (large : 3≤t)
    (base : ∀ e : Fin (3*t) ≃ Fin 3 × Fin t,
      let next (i : Fin (3*t)) : Fin (3*t) := ⟨(i.val+1)%(3*t),Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩
      ∃ (order : Fin s → (Fin (3*t) ≃ Fin (3*t))) (B : Fin (t*(t-s)) → Finset (Fin (3*t))),
        let H (i : Fin s) := univ.image fun z => s(order i z,order i (next z))
        let T (i : Fin (t*(t-s))) := (⊤ : SimpleGraph (Fin (3*t))).edgeFinset.filter fun d => d.toFinset ⊆ B i
        (∀ j,(B j).card=3) ∧ (Pairwise fun i j => Disjoint (H i) (H j)) ∧
        (Pairwise fun i j => Disjoint (T i) (T j)) ∧ Disjoint (univ.biUnion H) (univ.biUnion T) ∧
        ∀ a b,s(a,b)∈univ.biUnion H ∪ univ.biUnion T ↔ (e a).1≠(e b).1)
    {V : Type} [DecidableEq V] (f : ((Fin 3 × Fin t) × Bool) ≃ V) (G : SimpleGraph V)
    (cross : ∀ x y : V, (f.symm x).1.1≠(f.symm y).1.1 → G.Adj x y)
    (k : ℕ) (hk : k ≤ t*(t-s)) :
    ∃ C : Multiset (Cycle G), lengths C = Multiset.replicate (2*s) (6*t) +
      Multiset.replicate (4*k) 3 + Multiset.replicate (3*(t*(t-s)-k)) 4 ∧
      ∀ x y : V, (C.filter fun c => s(x,y)∈c.edges).card =
        if (f.symm x).1.1 ≠ (f.symm y).1.1 then 1 else 0 := by
  classical
  let e : Fin (3*t) ≃ Fin 3 × Fin t := Fintype.equivOfCardEq (by simp)
  let p := (Equiv.prodCongr e (Equiv.refl Bool)).trans f
  let g (i : Fin (3*t)) := (e i).1
  obtain ⟨order,B,three,hs,ts,sep,full⟩ := base e
  have adj (i : Fin (3*t)) (a : Bool) (j : Fin (3*t)) (b : Bool) (different : g i≠g j) :
      G.Adj (p (i,a)) (p (j,b)) := by
    apply cross
    simpa [p,g] using different
  obtain ⟨C,lens,freq⟩ := double_cross (m:=3*t) (by omega) hk p G g adj order B three hs ts sep full
  refine ⟨C,by simpa only [show 2*(3*t)=6*t by omega] using lens,?_⟩
  intro x y
  simpa [p,g] using freq x y

end AlspachHamiltonMix

namespace AlspachHamiltonMix
open SimpleGraph Finset AlspachConjecture
open scoped Classical

/-- Prescribe separate cycle lengths in the three matched groups. The ambient
graph can have any edges between different groups. -/
theorem inner_families {t : ℕ} {V : Type} [DecidableEq V]
    (f : ((Fin 3 × Fin t) × Bool) ≃ V) (G : SimpleGraph V)
    (within : ∀ (i : Fin 3) (r s : Fin t) (a b : Bool),
      G.Adj (f ((i,r),a)) (f ((i,s),b)) ↔ r≠s)
    (L : Fin 3 → Multiset ℕ) (shape : ∀ i a,a∈L i → a=3 ∨ a=4)
    (budget : ∀ i,(L i).sum=(2*t).choose 2-(2*t)/2) :
    ∃ D : Multiset (Cycle G), lengths D = L 0+L 1+L 2 ∧ ∀ x y : V, G.Adj x y →
      (D.filter fun c => s(x,y)∈c.edges).card = if (f.symm x).1.1=(f.symm y).1.1 then 1 else 0 := by
  classical
  let cl : (Fin t × Bool) ≃ Fin (2*t) := Fintype.equivOfCardEq (by simp; omega)
  obtain ⟨I,perfect,localAdj⟩ := AlspachSquares.pair_matching cl
  let H := completeGraph (Fin (2*t)) \ I.spanningCoe
  have inner (k : Fin 3) := AlspachTrades.all_triangle_square (2*t) ⟨t,by omega⟩ I perfect (L k) (shape k) (budget k)
  let inc (k : Fin 3) : Fin (2*t) ↪ V := ⟨fun z => f ((k,(cl.symm z).1),(cl.symm z).2),by
    intro x y h
    have eq := f.injective h
    exact cl.symm.injective (Prod.ext (congrArg (fun u : (Fin 3 × Fin t) × Bool => u.1.2) eq)
      (congrArg (fun u : (Fin 3 × Fin t) × Bool => u.2) eq))⟩
  have equal (k : Fin 3) : G.comap (inc k)=H := by
    ext a b
    exact (within k _ _ _ _).trans (localAdj a b).symm
  have part (k : Fin 3) : ∃ C : Multiset (Cycle G), lengths C=L k ∧ ∀ i j : Fin 3, ∀ x y : Fin t, ∀ a b : Bool,
      (C.filter fun c => s(f ((i,x),a),f ((j,y),b))∈c.edges).card = if i=k ∧ j=k ∧ x≠y then 1 else 0 := by
    obtain ⟨C,dec,len⟩ := inner k
    let P (a b : Fin (2*t)) := (cl.symm a).1≠(cl.symm b).1
    have cover : ∃ C : Multiset (Cycle (G.comap (inc k))), lengths C=L k ∧ ∀ a b,
        (C.filter fun c => s(a,b)∈c.edges).card = if P a b then 1 else 0 := by
      rw [equal]
      refine ⟨C,len,fun a b => ?_⟩
      by_cases h : P a b
      · rw [if_pos h]
        apply Eq.trans _ (dec s(a,b) ?_)
        · exact congrArg Multiset.card (Multiset.filter_congr (fun c _ => Iff.rfl))
        · refine (@SimpleGraph.mem_edgeFinset _ H s(a,b) ?_).mpr ?_
          exact (localAdj a b).mpr h
      · rw [if_neg h,Multiset.card_eq_zero]
        apply Multiset.filter_eq_nil.mpr
        intro c _ he
        exact h ((localAdj a b).mp (Walk.edges_subset_edgeSet c.walk he))
    obtain ⟨D,ld,count⟩ := AlspachBlowup.embed_family (inc k) G P (L k) cover
    refine ⟨D,ld,fun i j x y a b => ?_⟩
    have place (r : Fin t) (b : Bool) : (inc k) (cl (r,b))=f ((k,r),b) := by
      change f ((k,(cl.symm (cl (r,b))).1),(cl.symm (cl (r,b))).2)=_
      rw [Equiv.symm_apply_apply]
    have criterion : (∃ z w, f ((i,x),a)=inc k z ∧ f ((j,y),b)=inc k w ∧ P z w) ↔ i=k ∧ j=k ∧ x≠y := by
      constructor
      · rintro ⟨p,q,hp,hq,hpq⟩
        have e1 := f.injective hp
        have e2 := f.injective hq
        have e1x := congrArg (fun w : (Fin 3 × Fin t) × Bool => w.1.2) e1
        have e2y := congrArg (fun w : (Fin 3 × Fin t) × Bool => w.1.2) e2
        exact ⟨congrArg (fun w => w.1.1) e1,congrArg (fun w => w.1.1) e2,
          fun xy => hpq (e1x.symm.trans (xy.trans e2y))⟩
      · rintro ⟨rfl,rfl,hxy⟩
        exact ⟨cl (x,a),cl (y,b),(place x a).symm,(place y b).symm,by simpa [P] using hxy⟩
    by_cases h : i=k ∧ j=k ∧ x≠y
    · simpa only [if_pos h,if_pos (criterion.mpr h)] using count (f ((i,x),a)) (f ((j,y),b))
    · simpa only [if_neg h,if_neg (fun z => h (criterion.mp z))] using count (f ((i,x),a)) (f ((j,y),b))
  choose C len count using part
  refine ⟨C 0+C 1+C 2,?_,?_⟩
  · simpa only [lengths,Multiset.map_add] using congrArg₂ (·+·) (congrArg₂ (·+·) (len 0) (len 1)) (len 2)
  · intro X Y adj
    obtain ⟨⟨⟨i,x⟩,a⟩,rfl⟩ := f.surjective X
    obtain ⟨⟨⟨j,y⟩,b⟩,rfl⟩ := f.surjective Y
    simp only [Multiset.filter_add,Multiset.card_add,count,Equiv.symm_apply_apply]
    by_cases same : i=j
    · subst j
      have ne := (within i x y a b).mp adj
      fin_cases i <;> simp [ne]
    · have no (k : Fin 3) : ¬(i=k ∧ j=k ∧ x≠y) := fun h => same (h.1.trans h.2.1.symm)
      simp [no,same]

/-- Combine an exact outside decomposition with three independently prescribed
triangle/square lists, and carry the result to the requested perfect matching. -/
theorem glue_three {t : ℕ}
    (I : (completeGraph (Fin (6*t))).Subgraph) (hI : I.IsPerfectMatching)
    (L : Fin 3 → Multiset ℕ) (shape : ∀ i a,a∈L i → a=3 ∨ a=4)
    (budget : ∀ i,(L i).sum=(2*t).choose 2-(2*t)/2) (O : Multiset ℕ)
    (outside : ∀ (f : ((Fin 3 × Fin t) × Bool) ≃ Fin (6*t)) (G : SimpleGraph (Fin (6*t))),
      (∀ x y, (f.symm x).1.1≠(f.symm y).1.1 → G.Adj x y) →
      ∃ C : Multiset (Cycle G), lengths C=O ∧ ∀ x y,
        (C.filter fun c => s(x,y)∈c.edges).card = if (f.symm x).1.1≠(f.symm y).1.1 then 1 else 0) :
    ∃ C : Multiset (Cycle (completeGraph (Fin (6*t)) \ I.spanningCoe)),
      IsCycleDecomposition _ C ∧ lengths C=O+(L 0+L 1+L 2) := by
  classical
  let f : ((Fin 3 × Fin t) × Bool) ≃ Fin (6*t) := Fintype.equivOfCardEq (by simp; omega)
  let row : Fin (3*t) ≃ (Fin 3 × Fin t) := Fintype.equivOfCardEq (by simp)
  let f' := (Equiv.prodCongr row (Equiv.refl Bool)).trans f
  obtain ⟨J,hJ,adj⟩ := AlspachSquares.pair_matching f'
  let G := completeGraph (Fin (6*t)) \ J.spanningCoe
  have same (x y) : G.Adj x y ↔ (f.symm x).1≠(f.symm y).1 := by
    rw [show G.Adj x y ↔ (f'.symm x).1≠(f'.symm y).1 from adj x y]
    change row.symm (f.symm x).1 ≠ row.symm (f.symm y).1 ↔ _
    exact not_congr row.symm.injective.eq_iff
  have within (i : Fin 3) (r s : Fin t) (a b : Bool) :
      G.Adj (f ((i,r),a)) (f ((i,s),b)) ↔ r≠s := by simp [same]
  have cross (x y : Fin (6*t)) (ne : (f.symm x).1.1≠(f.symm y).1.1) : G.Adj x y :=
    (same x y).mpr fun h => ne (congrArg Prod.fst h)
  obtain ⟨A,lenA,cntA⟩ := outside f G cross
  obtain ⟨B,lenB,cntB⟩ := inner_families f G within L shape budget
  have dec : IsCycleDecomposition G (A+B) := by
    intro edge
    induction edge using Sym2.ind with
    | _ x y =>
      intro he
      have hxy : G.Adj x y := (@SimpleGraph.mem_edgeFinset _ G s(x,y) G.fintypeEdgeSet).mp he
      rw [Multiset.filter_add,Multiset.card_add,cntA,cntB x y hxy]
      by_cases h : (f.symm x).1.1=(f.symm y).1.1 <;> simp [h]
  have len : lengths (A+B)=O+(L 0+L 1+L 2) := by
    rw [show lengths (A+B)=lengths A+lengths B by exact Multiset.map_add ..,lenA,lenB]
  obtain ⟨iso⟩ := OMA.R_AlspachConjecture_alspach_conjecture_variants_even_R2.matchings_complements_iso J I hJ hI
  exact OMA.R_AlspachConjecture_alspach_conjecture_variants_even_R2.iso_decomposition iso dec len

end AlspachHamiltonMix

namespace AlspachHamiltonMix

/-- Partition the lengths into a crossing family and three internal lists.
The only lower bound comes from the minimum square count in each part. -/
theorem split_counts {t s : ℕ} (positive : 0<t) (limit : s≤t)
    (L : Multiset ℕ) (shape : ∀ a∈L,a=3 ∨ a=4 ∨ a=6*t)
    (budget : L.sum=(6*t).choose 2-(6*t)/2) (ham : L.count (6*t)=2*s)
    (squares : 3*(t.choose 2 % 3)≤L.count 4) :
    let h := t*(t-s)
    ∃ k, k≤h ∧ ∃ W : Fin 3 → Multiset ℕ,
      (∀ i,∀ a∈W i,a=3 ∨ a=4) ∧ (∀ i,(W i).sum=(2*t).choose 2-(2*t)/2) ∧
      L=(Multiset.replicate (2*s) (6*t)+Multiset.replicate (4*k) 3+
         Multiset.replicate (3*(h-k)) 4)+(W 0+W 1+W 2) := by
  intro h
  let v := t.choose 2
  have twice (n : ℕ) (hn : 0<n) : 2*n.choose 2=n*(n-1) := by
    obtain ⟨j,rfl⟩ : ∃ j, n=j+1 := ⟨n-1,by omega⟩
    simpa [Nat.mul_comm] using (Nat.add_one_mul_choose_eq j 1).symm
  have v2 := twice t positive
  have v3 := twice (3*t) (by omega)
  have cell : (3*t)*s+3*(h+v)=(3*t).choose 2 := by
    dsimp [h,v]
    have mul1 := congrArg (fun z : ℕ => t*z) (Nat.sub_add_cancel limit)
    have mul2 := Nat.sub_add_cancel (show 1≤t by omega)
    have mul3 := Nat.sub_add_cancel (show 1≤3*t by omega)
    nlinarith only [v2,v3,mul1,mul2,mul3,
      congrArg (fun z : ℕ => t*z) mul2,congrArg (fun z : ℕ => (3*t)*z) mul3]
  have norder : 6*t=2*(3*t) := by omega
  rw [norder] at shape budget ham ⊢
  obtain ⟨A,_,three,four,split⟩ := AlspachTriangleHamilton.classify_mixed (by omega : 3≤3*t)
    (r:=s) cell L shape budget ham
  have cap : A≤h+3*(v/3) := by dsimp [v] at *; omega
  let k := min A h
  let a := min (A-k) (v/3)
  let b := min (A-k-a) (v/3)
  let c := A-k-a-b
  have bounds : k≤h ∧ a≤v/3 ∧ b≤v/3 ∧ c≤v/3 ∧ k+a+b+c=A := by
    dsimp [c,b,a,k]
    omega
  obtain ⟨hk,ha,hb,hc,hall⟩ := bounds
  let W0 (w : ℕ) : Multiset ℕ := Multiset.replicate (4*w) 3 + Multiset.replicate (v-3*w) 4
  let W (i : Fin 3) := if i=0 then W0 a else if i=1 then W0 b else W0 c
  have wf (i : Fin 3) (x : ℕ) (hx : x∈W i) : x=3 ∨ x=4 := by
    have each (w : ℕ) (hw : x∈W0 w) : x=3 ∨ x=4 := by
      rcases Multiset.mem_add.mp hw with h|h
      · exact Or.inl (Multiset.eq_of_mem_replicate h)
      · exact Or.inr (Multiset.eq_of_mem_replicate h)
    fin_cases i <;> exact each _ hx
  have sums (w : ℕ) (hw : w≤v/3) :
      (W0 w).sum=(2*t).choose 2-(2*t)/2 := by
    rw [AlspachPaired.paired_budget t positive]
    simp only [W0,Multiset.sum_add,Multiset.sum_replicate,smul_eq_mul]
    dsimp [v] at *
    omega
  refine ⟨k,hk,W,wf,?_,?_⟩
  · intro i
    fin_cases i
    · exact sums a ha
    · exact sums b hb
    · exact sums c hc
  · have q : 3*(h+v-A)=3*(h-k)+(v-3*a)+(v-3*b)+(v-3*c) := by omega
    have tr : 4*A=4*k+4*a+4*b+4*c := by omega
    rw [split,q,tr]
    change _=_+((W0 a+W0 b)+W0 c)
    simp only [W0,Multiset.replicate_add]
    ac_rfl
theorem minimum_squares (t : ℕ) : t.choose 2%3=(if t%3=2 then 1 else 0) := by
  by_cases zero : t=0
  · subst t
    decide
  have two : 2*t.choose 2=t*(t-1) := by
    obtain ⟨k,rfl⟩ : ∃ k, t=k+1 := ⟨t-1,by omega⟩
    simpa [Nat.mul_comm] using (Nat.add_one_mul_choose_eq k 1).symm
  have eq := congrArg (· % 3) two
  change (2*t.choose 2)%3=t*(t-1)%3 at eq
  rw [Nat.mul_mod t] at eq
  rcases show t%3=0 ∨ t%3=1 ∨ t%3=2 by omega with r|r|r
  · rw [r] at eq ⊢
    norm_num at eq ⊢
    omega
  · have prev : (t-1)%3=0 := by omega
    rw [r,prev] at eq
    rw [r]
    norm_num at eq ⊢
    omega
  · have prev : (t-1)%3=1 := by omega
    rw [r,prev] at eq
    rw [r]
    norm_num at eq ⊢
    omega
end AlspachHamiltonMix

namespace AlspachHamiltonMix
open SimpleGraph Finset AlspachConjecture
open scoped Classical

/-- Convert cross-group families into decompositions with any admissible
triangle/square counts above the three internal groups' minimum square count. -/
theorem lists_of_outer {t s : ℕ} (positive : 0<t) (limit : s≤t)
    (I : (completeGraph (Fin (6*t))).Subgraph) (hI : I.IsPerfectMatching)
    (L : Multiset ℕ) (shape : ∀ a∈L,a=3 ∨ a=4 ∨ a=6*t)
    (budget : L.sum=(6*t).choose 2-(6*t)/2) (ham : L.count (6*t)=2*s)
    (squares : 3*(t.choose 2%3)≤L.count 4)
    (outside : ∀ k, k≤t*(t-s) → ∀ (f : ((Fin 3 × Fin t) × Bool) ≃ Fin (6*t)) (G : SimpleGraph (Fin (6*t))),
      (∀ x y, (f.symm x).1.1≠(f.symm y).1.1 → G.Adj x y) →
      ∃ C : Multiset (Cycle G), lengths C=Multiset.replicate (2*s) (6*t)+Multiset.replicate (4*k) 3+
        Multiset.replicate (3*(t*(t-s)-k)) 4 ∧ ∀ x y,
        (C.filter fun c => s(x,y)∈c.edges).card = if (f.symm x).1.1≠(f.symm y).1.1 then 1 else 0) :
    ∃ C : Multiset (Cycle (completeGraph (Fin (6*t)) \ I.spanningCoe)),
      IsCycleDecomposition _ C ∧ lengths C=L := by
  obtain ⟨k,hk,W,wf,sums,parts⟩ := split_counts positive limit L shape budget ham squares
  obtain ⟨C,dec,len⟩ := glue_three I hI W wf sums _ (outside k hk)
  exact ⟨C,dec,len.trans parts.symm⟩

end AlspachHamiltonMix


namespace AlspachTriHam

/-- Swap successive pairs. When the order is odd, replace the last swap and
the remaining singleton by a three-cycle on the final three positions. -/
theorem shift_permutation (s : ℕ) (hs : 2 ≤ s) :
    ∃ d : Equiv.Perm (Fin s), ∀ j : Fin s,
      (d j).val=j.val+1 ∨ j.val=(d j).val+1 ∨ j.val=(d j).val+2 := by
  let step (n : ℕ) :=
    if n%2=0 then (if n+1<s then n+1 else n-2)
    else if n+2=s then n+1 else n-1
  let f (i : Fin s) : Fin s := ⟨step i.val,by
    have := i.isLt
    dsimp only [step]
    split_ifs <;> omega⟩
  have inj : Function.Injective f := by
    intro i j eq
    have e : step i.val=step j.val := congrArg Fin.val eq
    have := i.isLt
    have := j.isLt
    apply Fin.ext
    dsimp only [step] at e
    split_ifs at e <;> omega
  let d := Equiv.ofBijective f ⟨inj, Finite.injective_iff_surjective.mp inj⟩
  refine ⟨d,?_⟩
  intro j
  change step j.val=j.val+1 ∨ j.val=step j.val+1 ∨ j.val=step j.val+2
  have := j.isLt
  dsimp only [step]
  split_ifs <;> omega

end AlspachTriHam

namespace AlspachTriHam
open scoped Classical

theorem twice_injective {t : ℕ} [NeZero t] (odd : Odd t) :
    Function.Injective (fun x : Fin t => x+x) := by
  obtain ⟨k,hk⟩ := odd
  have value (x : Fin t) : (x+x).val = if x.val+x.val<t then x.val+x.val else x.val+x.val-t := by
    rw [Fin.val_add]
    split_ifs with h
    · exact Nat.mod_eq_of_lt h
    · rw [Nat.mod_eq_sub_mod (Nat.le_of_not_lt h),Nat.mod_eq_of_lt (by have := x.isLt; omega)]
  intro x y eq
  have v := congrArg Fin.val eq
  change (x+x).val=(y+y).val at v
  rw [value,value] at v
  apply Fin.ext
  have hx := x.isLt
  have hy := y.isLt
  split_ifs at v <;> omega

/-- The selected pairs and final triple give row advances 1, −1 or −2.
Each is conjugate to the ordinary cyclic successor at odd order. -/
theorem row_advance {t : ℕ} [NeZero t] (odd : Odd t) (a b : Fin t)
    (step : b=a+1 ∨ a=b+1 ∨ a=b+1+1) :
    ∃ f : Fin t ≃ Fin t, ∀ x, f (x+1)=f x + (b-a) := by
  rcases step with eq | eq | eq
  · refine ⟨Equiv.refl _,?_⟩
    intro x; change x+1=x+(b-a); rw [eq]; abel
  · let f (x : Fin t) := -x
    have inj : Function.Injective f := fun _ _ e => neg_injective e
    refine ⟨Equiv.ofBijective f ⟨inj,Finite.injective_iff_surjective.mp inj⟩,?_⟩
    intro x; change -(x+1)= -x+(b-a); rw [eq]; abel
  · let f (x : Fin t) := -(x+x)
    have inj : Function.Injective f := fun _ _ e => twice_injective odd (neg_injective e)
    refine ⟨Equiv.ofBijective f ⟨inj,Finite.injective_iff_surjective.mp inj⟩,?_⟩
    intro x; change -((x+1)+(x+1))= -(x+x)+(b-a); rw [eq]; abel

end AlspachTriHam

namespace AlspachTriHam
open Finset

/-- Use shift a on the first and last color transition and shift b on the
middle one. Three successive steps then advance the row by b-a. -/
theorem advanced_listing {t : ℕ} [NeZero t] (odd : Odd t) (a b : Fin t)
    (moves : b=a+1 ∨ a=b+1 ∨ a=b+1+1) :
    let next (i : Fin (3*t)) : Fin (3*t) := ⟨(i.val+1)%(3*t),Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩
    let jump (p : Fin 3) := if p=2 then -(a+a) else if p=1 then b else a
    ∃ σ : Fin (3*t) ≃ Fin 3 × Fin t, ∀ e : Sym2 (Fin 3 × Fin t),
      (∃ i,e=s(σ i,σ (next i))) ↔ ∃ (p : Fin 3) (x : Fin t),e=s((p,x),(p+1,x+jump p)) := by
  intro next jump
  obtain ⟨f,step⟩ := row_advance odd a b moves
  let offset (p : Fin 3) := if p=0 then 0 else if p=1 then a else a+b
  let g : Fin 3 × Fin t ≃ Fin 3 × Fin t := {
    toFun := fun v => (v.1,f v.2 + offset v.1)
    invFun := fun v => (v.1,f.symm (v.2-offset v.1))
    left_inv := fun v => by simp
    right_inv := fun v => by simp }
  obtain ⟨chart,route⟩ := round_robin t
  let σ := chart.trans g
  have shift (p : Fin 3) (x : Fin t) : f (if p=2 then x+1 else x) + offset (p+1) =
      f x + offset p + jump p := by
    fin_cases p
    · simp [offset,jump]
    · simp [offset,jump,show (1:Fin 3)+1=2 by decide,add_assoc]
    · simp [offset,jump,step,show (2:Fin 3)+1=0 by decide]
      abel
  have next_at (i : Fin (3*t)) :
      σ (next i) = ((σ i).1+1,(σ i).2+jump (σ i).1) := by
    obtain ⟨pc,px⟩ := route i
    apply Prod.ext
    · exact pc
    · change f (chart (next i)).2 + offset (chart (next i)).1 = f (chart i).2 + offset (chart i).1 + jump (chart i).1
      rw [show (chart (next i)).2=_ from px, show (chart (next i)).1=_ from pc]
      exact shift _ _
  refine ⟨σ,?_⟩
  intro e
  constructor
  · rintro ⟨i,rfl⟩
    exact ⟨(σ i).1,(σ i).2,by rw [next_at]⟩
  · rintro ⟨p,x,rfl⟩
    refine ⟨σ.symm (p,x),?_⟩
    rw [next_at,σ.apply_symm_apply]

end AlspachTriHam

namespace AlspachTriHam
open Finset
open scoped Classical

/-- The selected triangle factors partition into one Hamilton circuit per shift.
The middle transition permutes the shifts, preserving its occupied edges. -/
theorem selected_listings {t s : ℕ} [NeZero t] (odd : Odd t) (small : 2≤ s) (lim : s≤t) :
    let V := Fin 3 × Fin t
    let next (i : Fin (3*t)) : Fin (3*t) := ⟨(i.val+1)%(3*t), Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩
    let face (a i : Fin t) : Finset V := {(0,i),(1,i+a),(2,i+a+a)}
    ∃ σ : Fin s → (Fin (3*t) ≃ V),
      let ring (j : Fin s) (x y : V) := ∃ i,s(x,y)=s(σ j i,σ j (next i))
      (∀ j x y,ring j x y → x.1≠y.1) ∧
      (∀ j k x y,ring j x y → ring k x y → j=k) ∧
      (∀ x y,x≠y → ((∃ j,ring j x y) ↔ ∃ a : Fin t,a.val<s ∧ ∃ i,x∈face a i ∧ y∈face a i)) := by
  intro V next face
  let rowEdge (p : Fin 3) (x d : Fin t) : Sym2 (Fin 3 × Fin t) := s((p,x),(p+1,x+d))

  let triFace (a x : Fin t) : Finset (Fin 3 × Fin t) := {(0,x),(1,x+a),(2,x+a+a)}

  let shift (a : Fin t) (p : Fin 3) : Fin t := if p=2 then -(a+a) else a

  have rowEdge_inj {p q : Fin 3} {x y d e : Fin t} (h : rowEdge p x d=rowEdge q y e) :
      p=q ∧ x=y ∧ d=e := by
    rcases Sym2.eq_iff.mp h with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
    · have hp := congrArg Prod.fst h₁
      have hx := congrArg Prod.snd h₁
      have hd := congrArg Prod.snd h₂
      change x+d=y+e at hd
      change x=y at hx
      subst y
      exact ⟨hp,rfl,add_left_cancel hd⟩
    · have h₃ := congrArg Prod.fst h₁
      have h₄ := congrArg Prod.fst h₂
      change p=q+1 at h₃
      change p+1=q at h₄
      have impossible : p+1+1=p := (congrArg (·+1) h₄).trans h₃.symm
      fin_cases p <;> contradiction

  have face_darts (a : Fin t) (u v : Fin 3 × Fin t) (hne : u≠v) :
      (∃ x, u∈triFace a x ∧ v∈triFace a x) ↔
        ∃ (p : Fin 3) (x : Fin t), s(u,v)=rowEdge p x (shift a p) := by
    classical
    constructor
    · rintro ⟨x,hu,hv⟩
      simp only [triFace,mem_insert,mem_singleton] at hu hv
      rcases hu with rfl|rfl|rfl <;> rcases hv with rfl|rfl|rfl
      all_goals try exact (hne rfl).elim
      · exact ⟨0,x,rfl⟩
      · refine ⟨2,x+a+a,?_⟩
        rw [Sym2.eq_swap]
        simp [rowEdge,shift,add_assoc]
      · exact ⟨0,x,Sym2.eq_swap⟩
      · exact ⟨1,x+a,rfl⟩
      · refine ⟨2,x+a+a,?_⟩
        simp [rowEdge,shift,add_assoc]
      · exact ⟨1,x+a,Sym2.eq_swap⟩
    · rintro ⟨p,x,h⟩
      fin_cases p
      · refine ⟨x,?_⟩
        rcases Sym2.eq_iff.mp h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> simp [triFace,shift]
      · refine ⟨x-a,?_⟩
        rcases Sym2.eq_iff.mp h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> simp [triFace,shift]
      · refine ⟨x-(a+a),?_⟩
        rcases Sym2.eq_iff.mp h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;>
          simp [triFace,shift,sub_eq_add_neg,add_assoc]

  obtain ⟨d,moves⟩ := shift_permutation s small
  let lift (j : Fin s) : Fin t := ⟨j.val,lt_of_lt_of_le j.isLt lim⟩
  have lift_inj : Function.Injective lift := fun _ _ h => Fin.ext (congrArg (Fin.val : Fin t → ℕ) h)
  have inc (i j : Fin s) (h : i.val=j.val+1) : lift i=lift j+1 := by
    apply Fin.ext
    have upper : (lift j).val+1<t := by change j.val+1<t; have := i.isLt; omega
    rw [Fin.val_add_one_of_lt' upper]
    exact h
  have inc2 (i j : Fin s) (h : i.val=j.val+2) : lift i=lift j+1+1 := by
    have upper : (lift j).val+1<t := by change j.val+1<t; have := i.isLt; omega
    have first := Fin.val_add_one_of_lt' upper
    have upper' : (lift j+1).val+1<t := by
      rw [first]; change j.val+1+1<t; have := i.isLt; omega
    apply Fin.ext
    rw [Fin.val_add_one_of_lt' upper',first]
    exact h
  have jump_moves (j : Fin s) : lift (d j)=lift j+1 ∨ lift j=lift (d j)+1 ∨ lift j=lift (d j)+1+1 := by
    rcases moves j with h|h|h
    · exact Or.inl (inc _ _ h)
    · exact Or.inr (Or.inl (inc _ _ h))
    · exact Or.inr (Or.inr (inc2 _ _ h))
  choose σ certified using fun j => advanced_listing odd (lift j) (lift (d j)) (jump_moves j)
  refine ⟨σ,?_⟩
  intro ring
  let pick (j : Fin s) (p : Fin 3) := if p=1 then lift (d j) else lift j
  have step (j : Fin s) (p : Fin 3) :
      (if p=2 then -(lift j+lift j) else if p=1 then lift (d j) else lift j) = shift (pick j p) p := by
    by_cases h : p=2
    · subst p; simp [pick,shift,show (2:Fin 3)≠1 by decide]
    · simp [pick,shift,h]
  have route (j : Fin s) (x y : V) : ring j x y ↔
      ∃ (p : Fin 3) (z : Fin t), s(x,y)=rowEdge p z (shift (pick j p) p) := by
    simpa only [←step] using certified j s(x,y)
  have shift_inj (p : Fin 3) : Function.Injective (fun a => shift a p) := by
    intro a b hab
    by_cases h : p=2
    · exact twice_injective odd (neg_injective (by simpa only [shift,if_pos h] using hab))
    · simpa only [shift,if_neg h] using hab
  have pick_inj (p : Fin 3) : Function.Injective (fun j => pick j p) := by
    by_cases h : p=1
    · intro j k eq; exact d.injective (lift_inj (by simpa only [pick,if_pos h] using eq))
    · simpa only [pick,if_neg h] using lift_inj
  refine ⟨?_,?_,?_⟩
  · intro j x y h
    obtain ⟨p,z,h⟩ := (route j x y).mp h
    have no_fixed : ∀ p : Fin 3,p≠p+1 := by decide
    rcases Sym2.eq_iff.mp h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact no_fixed p
    · exact (no_fixed p).symm
  · intro j k x y hj hk
    obtain ⟨p,z,hj⟩ := (route j x y).mp hj
    obtain ⟨q,w,hk⟩ := (route k x y).mp hk
    obtain ⟨rfl,_,hd⟩ := rowEdge_inj (hj.symm.trans hk)
    exact pick_inj _ (shift_inj _ hd)
  · intro x y ne
    constructor
    · rintro ⟨j,h⟩
      obtain ⟨p,z,h⟩ := (route j x y).mp h
      have lt : (pick j p).val<s := by
        by_cases h : p=1
        · simpa only [pick,if_pos h,lift] using (d j).isLt
        · simpa only [pick,if_neg h,lift] using j.isLt
      exact ⟨pick j p,lt,(face_darts _ x y ne).mpr ⟨p,z,h⟩⟩
    · rintro ⟨a,lt,hit⟩
      obtain ⟨p,z,h⟩ := (face_darts a x y ne).mp hit
      let j : Fin s := ⟨a.val,lt⟩
      have ha : lift j=a := Fin.ext rfl
      have all : ∃ k,pick k p=a := by
        by_cases h : p=1
        · exact ⟨d.symm j,by simp [pick,h,ha]⟩
        · exact ⟨j,by simp [pick,h,ha]⟩
      obtain ⟨k,hk⟩ := all
      exact ⟨k,(route k x y).mpr ⟨p,z,by rw [hk]; exact h⟩⟩

end AlspachTriHam

namespace AlspachTriHam
open Finset

/-- Retain the triangles whose shifts are at or above the prescribed cutoff.
These triangles partition precisely the unused cross-color pairs. -/
theorem cross_inventory_after {t s : ℕ} [NeZero t] (odd : Odd t) :
    let V := Fin 3 × Fin t
    let face (a i : Fin t) : Finset V := {(0,i),(1,i+a),(2,i+a+a)}
    let selected (x y : V) := ∃ a : Fin t, a.val < s ∧ ∃ i, x∈face a i ∧ y∈face a i
    ∃ D : Finset (Finset V), D.card=t*(t-s) ∧
      (∀ B∈D, B.card=3) ∧
      (∀ B∈D, ∀ x∈B, ∀ y∈B, x.1=y.1 → x=y) ∧
      (∀ B∈D, ∀ x∈B, ∀ y∈B, x≠y → ¬selected x y) ∧
      ∀ x y : V, x.1≠y.1 → ¬selected x y → ∃! B : {B // B∈D}, x∈B.val ∧ y∈B.val := by
  classical
  intro V face selected
  obtain ⟨three,sep,unique⟩ := cross_faces odd
  have inject : Function.Injective (fun z : Fin t × Fin t => face z.1 z.2) := by
    intro z w same
    let x : V := (0,z.2)
    let y : V := (1,z.2+z.1)
    have hit : x∈face z.1 z.2 ∧ y∈face z.1 z.2 := by simp [x,y,face,V]
    change face z.1 z.2=face w.1 w.2 at same
    have diff : x.1 ≠ y.1 := (by decide : (0 : Fin 3) ≠ 1)
    have hitW : x∈face w.1 w.2 ∧ y∈face w.1 w.2 := same ▸ hit
    exact (unique x y diff).unique hit hitW
  let shift (i : Fin (t-s)) : Fin t := ⟨s+i.val, by have := i.isLt; omega⟩
  let I := Fin (t-s) × Fin t
  let emb : I ↪ Finset V := {
    toFun := fun z => face (shift z.1) z.2
    inj' := by
      intro z w h
      have eq : (shift z.1,z.2) = (shift w.1,w.2) := inject h
      have e : s+z.1.val=s+w.1.val := congrArg (fun v => v.1.val) eq
      exact Prod.ext (Fin.ext (by omega)) (congrArg (fun v : Fin t × Fin t => v.2) eq) }
  let D := univ.map emb
  have memD (B : Finset V) : B ∈ D ↔ ∃ z : Fin t × Fin t, s≤z.1.val ∧ face z.1 z.2=B := by
    constructor
    · intro h
      obtain ⟨z,_,rfl⟩ := mem_map.mp h
      exact ⟨(shift z.1,z.2),Nat.le_add_right _ _,rfl⟩
    · rintro ⟨z,lim,rfl⟩
      let j : Fin (t-s) := ⟨z.1.val-s,by have := z.1.isLt; omega⟩
      have eq : shift j=z.1 := Fin.ext (show s+(z.1.val-s)=z.1.val by omega)
      exact mem_map.mpr ⟨(j,z.2),mem_univ _, congrArg (fun a => face a z.2) eq⟩
  refine ⟨D,?_,?_,?_,?_,?_⟩
  · simp [D,I,Nat.mul_comm]
  · intro B h
    obtain ⟨z,_,rfl⟩ := (memD B).mp h
    exact three z.1 z.2
  · intro B h
    obtain ⟨z,_,rfl⟩ := (memD B).mp h
    exact fun x hx y hy => sep z.1 z.2 x y hx hy
  · intro B h x hx y hy ne sel
    obtain ⟨z,late,rfl⟩ := (memD B).mp h
    obtain ⟨a,early,i,sx,sy⟩ := sel
    have diff : x.1 ≠ y.1 := fun same => ne (sep z.1 z.2 x y hx hy same)
    have eq : z=(a,i) := (unique x y diff).unique ⟨hx,hy⟩ ⟨sx,sy⟩
    exact (Nat.not_le_of_lt early) (by rw [eq] at late; exact late)
  · intro x y diff miss
    obtain ⟨z,hit,sole⟩ := unique x y diff
    have late : s≤z.1.val := by
      by_contra! early
      exact miss ⟨z.1,early,z.2,hit⟩
    refine ⟨⟨face z.1 z.2,(memD _).mpr ⟨z,late,rfl⟩⟩,hit,?_⟩
    rintro ⟨B,hB⟩ h
    obtain ⟨w,_,rfl⟩ := (memD B).mp hB
    exact Subtype.ext (congrArg (fun v : Fin t × Fin t => face v.1 v.2) (sole w h))

end AlspachTriHam

namespace AlspachTriHam
open Finset SimpleGraph
open scoped Classical

/-- Relabel the cyclic listings of the selected shifts and the triangles of the
remaining shifts as a partition of the cross-color pairs. -/
theorem cross_base_from_selected {t s : ℕ} [NeZero t] (odd : Odd t)
    (e : Fin (3*t) ≃ Fin 3 × Fin t) :
    let V := Fin 3 × Fin t
    let next (i : Fin (3*t)) : Fin (3*t) := ⟨(i.val+1)%(3*t),Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩
    let face (a i : Fin t) : Finset V := {(0,i),(1,i+a),(2,i+a+a)}
    (∃ σ : Fin s → (Fin (3*t) ≃ V),
      let ring (j : Fin s) (x y : V) := ∃ i,s(x,y)=s(σ j i,σ j (next i))
      (∀ j x y,ring j x y → x.1≠y.1) ∧
      (∀ j k x y,ring j x y → ring k x y → j=k) ∧
      (∀ x y,x≠y → ((∃ j,ring j x y) ↔ ∃ a : Fin t,a.val<s ∧ ∃ i,x∈face a i ∧ y∈face a i))) →
    ∃ (order : Fin s → (Fin (3*t) ≃ Fin (3*t))) (B : Fin (t*(t-s)) → Finset (Fin (3*t))),
      let H (i : Fin s) := univ.image fun z => s(order i z,order i (next z))
      let T (i : Fin (t*(t-s))) := (⊤ : SimpleGraph (Fin (3*t))).edgeFinset.filter fun f => f.toFinset ⊆ B i
      (∀ j,(B j).card=3) ∧ (Pairwise fun i j => Disjoint (H i) (H j)) ∧
      (Pairwise fun i j => Disjoint (T i) (T j)) ∧ Disjoint (univ.biUnion H) (univ.biUnion T) ∧
      ∀ x y,s(x,y)∈univ.biUnion H ∪ univ.biUnion T ↔ (e x).1≠(e y).1 := by
  classical
  intro V next face listed
  obtain ⟨σ,cross,unique,hit⟩ := listed
  obtain ⟨D,card,three,sep,apart,complete⟩ := cross_inventory_after (s:=s) odd
  rw [←card]
  apply AlspachTriangleHamilton.relabel_cross_listings e (Equiv.refl (Fin s)) Prod.fst σ D three cross
    (fun b hb x hx y hy ne same => ne (sep b hb x hx y hy same))
    (fun x y _ j k hj hk => unique j k x y hj hk)
  · intro b hb x hx y hy diff j h
    have ne : x≠y := fun eq => diff (congrArg Prod.fst eq)
    exact apart b hb x hx y hy ne ((hit x y ne).mp ⟨j,h⟩)
  · intro x y diff miss
    have ne : x≠y := fun eq => diff (congrArg Prod.fst eq)
    apply complete x y diff
    intro sel
    obtain ⟨j,h⟩ := (hit x y ne).mpr sel
    exact miss j h

end AlspachTriHam

namespace AlspachTriHam
open Finset SimpleGraph AlspachConjecture
open scoped Classical

/-- An arbitrary initial segment of at least two shifts can be replaced by
disjoint cyclic orders, even when it has odd cardinality. -/
theorem cross_base_selected {t s : ℕ} [NeZero t] (odd : Odd t) (small : 2≤ s) (lim : s≤t)
    (e : Fin (3*t) ≃ Fin 3 × Fin t) :
    let next (i : Fin (3*t)) : Fin (3*t) := ⟨(i.val+1)%(3*t),Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩
    ∃ (order : Fin s → (Fin (3*t) ≃ Fin (3*t))) (B : Fin (t*(t-s)) → Finset (Fin (3*t))),
      let H (i : Fin s) := univ.image fun z => s(order i z,order i (next z))
      let T (i : Fin (t*(t-s))) := (⊤ : SimpleGraph (Fin (3*t))).edgeFinset.filter fun f => f.toFinset ⊆ B i
      (∀ j,(B j).card=3) ∧ (Pairwise fun i j => Disjoint (H i) (H j)) ∧
      (Pairwise fun i j => Disjoint (T i) (T j)) ∧ Disjoint (univ.biUnion H) (univ.biUnion T) ∧
      ∀ x y,s(x,y)∈univ.biUnion H ∪ univ.biUnion T ↔ (e x).1≠(e y).1 := by
  exact cross_base_from_selected odd e (selected_listings odd small lim)

end AlspachTriHam

namespace AlspachHamiltonMix
open SimpleGraph AlspachConjecture
open scoped Classical

/-- At orders six modulo twelve, prescribe an even number of Hamilton cycles
from four through one third of the order, along with triangles and squares.
The three internal groups need three squares at orders thirty modulo 36.
A list without Hamilton cycles can always be realized. -/
theorem triangle_square_hamilton_six_mod_twelve (n : ℕ) (residue : n%12=6)
    (I : (completeGraph (Fin n)).Subgraph) (hI : I.IsPerfectMatching)
    (L : Multiset ℕ) (shape : ∀ a∈L,a=3 ∨ a=4 ∨ a=n)
    (budget : L.sum=n.choose 2-n/2)
    (counts : L.count n=0 ∨ (Even (L.count n) ∧ 4≤L.count n ∧ L.count n≤n/3 ∧
      (n%36≠30 ∨ 3≤L.count 4))) :
    ∃ C : Multiset (Cycle (completeGraph (Fin n) \ I.spanningCoe)),
      IsCycleDecomposition _ C ∧ lengths C=L := by
  rcases counts with zero | ⟨⟨s,hs⟩,lo,hi,squares⟩
  · apply AlspachTrades.all_triangle_square n ⟨n/2,by omega⟩ I hI L _ budget
    intro a ha
    rcases shape a ha with a3|a4|rfl
    · exact Or.inl a3
    · exact Or.inr a4
    · exact False.elim ((Multiset.count_eq_zero.mp zero) ha)
  · obtain ⟨t,rfl⟩ : ∃ t,n=6*t := ⟨n/6,by omega⟩
    have odd : Odd t := ⟨t/2,by omega⟩
    have large : 3≤t := by omega
    let : NeZero t := ⟨by omega⟩
    have minimum : 3*(t.choose 2%3)≤L.count 4 := by
      rw [minimum_squares]
      split <;> omega
    apply lists_of_outer (s:=s) (by omega) (by omega) I hI L shape budget (by omega) minimum
    intro k hk f G cross
    exact outer_of_base large (AlspachTriHam.cross_base_selected odd (s:=s) (by omega) (by omega)) f G cross k hk

end AlspachHamiltonMix

namespace AlspachIterated
open Finset SimpleGraph AlspachConjecture
open scoped Classical

/-- In a cycle decomposition, cycles containing the same edge are equal.
One can therefore index any prescribed number of cycles of length k without
repeating a cycle. -/
theorem cycle_slots {m : ℕ} {G : SimpleGraph (Fin m)} [DecidableRel G.Adj]
    (C : Multiset (Cycle G)) (decomp : IsCycleDecomposition G C) :
    (∀ (c d : Cycle G), c∈C → d∈C → ∀ e, e∈c.edges → e∈d.edges → c=d) ∧
    ∀ k r : ℕ, r≤(lengths C).count k → ∃ choose : Fin r ↪ Cycle G,
      ∀ i, choose i ∈ C ∧ (choose i).length=k := by
  classical
  have card (e : Sym2 (Fin m)) {c : Cycle G} (he : e∈c.edges) :
      (C.filter fun p => e∈p.edges).card = 1 :=
    decomp e (G.mem_edgeFinset.mpr (c.walk.edges_subset_edgeSet he))
  constructor
  · intro c d hc hd e ec ed
    obtain ⟨z,hz⟩ := Multiset.card_eq_one.mp (card e ec)
    have h1 : c∈C.filter (fun p => e∈p.edges) := Multiset.mem_filter.mpr ⟨hc,ec⟩
    have h2 : d∈C.filter (fun p => e∈p.edges) := Multiset.mem_filter.mpr ⟨hd,ed⟩
    rw [hz,Multiset.mem_singleton] at h1 h2
    exact h1.trans h2.symm
  · have nodup : C.Nodup := by
      apply Multiset.nodup_iff_count_le_one.mpr
      intro c
      obtain ⟨e,he⟩ := c.walk.edges.exists_mem_of_ne_nil (by simp [c.isCycle.not_nil])
      have hle := Multiset.count_le_card c (C.filter fun p => e∈p.edges)
      rw [Multiset.count_filter_of_pos (p:=fun p : Cycle G => e∈p.edges) (show e∈c.edges from he),card e he] at hle
      exact hle
    intro k r le
    let F := C.filter fun c => k=c.length
    let S : Finset (Cycle G) := ⟨F,nodup.filter _⟩
    have size : Fintype.card S = (lengths C).count k := by
      rw [Fintype.card_coe]
      exact (Multiset.count_map SimpleGraph.Cycle.length C k).symm
    let index := (Fintype.equivFinOfCardEq size).symm
    let f : Fin r ↪ Cycle G := (Fin.castLEEmb le).trans (index.toEmbedding.trans (Function.Embedding.subtype _))
    refine ⟨f,fun i => ?_⟩
    have hi : f i∈F := (index (Fin.castLE le i)).property
    exact ⟨(Multiset.mem_filter.mp hi).1,(Multiset.mem_filter.mp hi).2.symm⟩

end AlspachIterated

namespace AlspachIterated
open SimpleGraph Finset

/-- Reading the vertices of a Hamilton cycle in walk order gives a permutation
whose consecutive pairs, including the closing pair, are exactly its edges. -/
theorem hamilton_support {m : ℕ} {G : SimpleGraph (Fin m)} (c : Cycle G) (len : c.length=m) :
    let next (i : Fin m) : Fin m := ⟨(i.val+1)%m,Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩
    ∃ σ : Fin m ≃ Fin m, univ.image (fun i => s(σ i,σ (next i))) = c.edges.toFinset := by
  classical
  intro next
  have hlen : c.walk.length=m := len
  let a (i : Fin m) := c.walk.getVert i.val
  have inj : Function.Injective a := by
    intro i j ij
    apply Fin.ext
    have hi := i.isLt
    have hj := j.isLt
    exact c.isCycle.getVert_injOn' (by change i.val≤ c.walk.length-1; omega)
      (by change j.val≤ c.walk.length-1; omega) ij
  let σ := Equiv.ofBijective a ⟨inj, Finite.injective_iff_surjective.mp inj⟩
  have atNext (i : Fin m) : σ (next i)=c.walk.getVert (i.val+1) := by
    change c.walk.getVert ((i.val+1)%m) = _
    have hi := i.isLt
    by_cases h : i.val+1< m
    · rw [Nat.mod_eq_of_lt h]
    · rw [show i.val+1=m by omega,Nat.mod_self]
      calc c.walk.getVert 0 = c.walk.getVert c.walk.length := by rw [Walk.getVert_length,Walk.getVert_zero]
           _ = c.walk.getVert m := congrArg c.walk.getVert hlen
  refine ⟨σ,?_⟩
  ext e
  induction e using Sym2.ind with
  | _ x y =>
    simp only [mem_image, mem_univ, true_and,List.mem_toFinset]
    change (∃ i,s(σ i,σ (next i))=s(x,y)) ↔ s(x,y)∈c.walk.edges
    rw [Walk.mk_mem_edges_iff_exists]
    constructor
    · rintro ⟨i,eq⟩
      exact ⟨i.val,by rw [hlen]; exact i.isLt,by rwa [←atNext i]⟩
    · rintro ⟨i,hi,eq⟩
      let j : Fin m := ⟨i,by omega⟩
      exact ⟨j,by rw [atNext]; exact eq⟩

end AlspachIterated

namespace AlspachIterated
open Finset SimpleGraph
open scoped Classical

/-- For a cycle of length three the three visited vertices span precisely
the three edges of its walk, viewed in the ambient complete graph. -/
theorem triangle_support {m : ℕ} {G : SimpleGraph (Fin m)} (c : Cycle G) (len : c.length=3) :
    ∃ B : Finset (Fin m), B.card=3 ∧
      ((⊤ : SimpleGraph (Fin m)).edgeFinset.filter fun e => e.toFinset ⊆ B)=c.edges.toFinset := by
  classical
  have size : c.walk.length=3 := len
  let a := c.walk.getVert 0
  let b := c.walk.getVert 1
  let d := c.walk.getVert 2
  have inj {i j : ℕ} (hi : i<3) (hj : j<3) (eq : c.walk.getVert i=c.walk.getVert j) : i=j :=
    c.isCycle.getVert_injOn' (by change i≤ c.walk.length-1; omega)
      (by change j≤ c.walk.length-1; omega) eq
  have ab : a≠b := fun eq => Nat.zero_ne_one (inj (i:=0) (j:=1) (by decide) (by decide) eq)
  have ad : a≠d := fun eq => (by decide : (0:ℕ)≠2) (inj (i:=0) (j:=2) (by decide) (by decide) eq)
  have bd : b≠d := fun eq => (by decide : (1:ℕ)≠2) (inj (i:=1) (j:=2) (by decide) (by decide) eq)
  have close : c.walk.getVert 3=a := by rw [←size,Walk.getVert_length]; exact (Walk.getVert_zero _).symm
  refine ⟨{a,b,d},by simp [ab,ad,bd],?_⟩
  have visited : c.edges.toFinset = {s(a,b),s(b,d),s(d,a)} := by
    ext edge
    induction edge using Sym2.ind with
    | _ x y =>
      simp only [List.mem_toFinset,Cycle.edges,Walk.mk_mem_edges_iff_exists,mem_insert,mem_singleton]
      constructor
      · rintro ⟨i,hi,eq⟩
        have choices : i=0 ∨ i=1 ∨ i=2 := by omega
        rcases choices with rfl|rfl|rfl
        · exact Or.inl eq.symm
        · exact Or.inr (Or.inl eq.symm)
        · exact Or.inr (Or.inr (by simpa only [close] using eq.symm))
      · rintro (eq|eq|eq)
        · exact ⟨0,by omega,eq.symm⟩
        · exact ⟨1,by omega,eq.symm⟩
        · exact ⟨2,by omega,by simpa only [close] using eq.symm⟩
  rw [visited]
  ext edge
  induction edge using Sym2.ind with
  | _ x y =>
    simp only [mem_filter,SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet,SimpleGraph.top_adj,
      Sym2.toFinset_mk_eq,insert_subset_iff,singleton_subset_iff,mem_insert,mem_singleton,Sym2.eq_iff]
    grind

end AlspachIterated

namespace AlspachIterated
open Finset SimpleGraph AlspachConjecture
open scoped Classical

/-- Extract any selected numbers of Hamilton cycles and triangles from a
decomposition. Their supports in the complete base graph are disjoint
within each family and between the two families. -/
theorem extract_supports {m r h : ℕ} (different : m≠3) {G : SimpleGraph (Fin m)} [DecidableRel G.Adj]
    (C : Multiset (Cycle G)) (dec : IsCycleDecomposition G C)
    (hr : r≤(lengths C).count m) (ht : h≤(lengths C).count 3) :
    let next (i : Fin m) : Fin m := ⟨(i.val+1)%m,Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩
    ∃ (σ : Fin r → (Fin m ≃ Fin m)) (B : Fin h → Finset (Fin m)),
      let H (i : Fin r) := univ.image fun z => s(σ i z,σ i (next z))
      let T (i : Fin h) := (⊤ : SimpleGraph (Fin m)).edgeFinset.filter fun e => e.toFinset ⊆ B i
      (∀ i,(B i).card=3) ∧ Pairwise (fun i j => Disjoint (H i) (H j)) ∧
      Pairwise (fun i j => Disjoint (T i) (T j)) ∧ Disjoint (univ.biUnion H) (univ.biUnion T) := by
  classical
  intro next
  obtain ⟨uniq,pick⟩ := cycle_slots C dec
  obtain ⟨A,hA⟩ := pick m r hr
  obtain ⟨D,hD⟩ := pick 3 h ht
  choose σ edges using fun i => hamilton_support (A i) (hA i).2
  choose B three faces using fun i => triangle_support (D i) (hD i).2
  refine ⟨σ,B,three,?_,?_,?_⟩
  · intro i j ne
    dsimp only [next]
    rw [edges i,edges j]
    apply Finset.disjoint_left.mpr
    exact fun e he hf => ne (A.injective (uniq _ _ (hA i).1 (hA j).1 e
      (List.mem_toFinset.mp he) (List.mem_toFinset.mp hf)))
  · intro i j ne
    dsimp only
    rw [faces i,faces j]
    apply Finset.disjoint_left.mpr
    exact fun e he hf => ne (D.injective (uniq _ _ (hD i).1 (hD j).1 e
      (List.mem_toFinset.mp he) (List.mem_toFinset.mp hf)))
  · apply Finset.disjoint_left.mpr
    intro e eh et
    obtain ⟨i,_,hi⟩ := mem_biUnion.mp eh
    obtain ⟨j,_,hj⟩ := mem_biUnion.mp et
    rw [edges i] at hi
    rw [faces j] at hj
    have eq := uniq _ _ (hA i).1 (hD j).1 e (List.mem_toFinset.mp hi) (List.mem_toFinset.mp hj)
    exact different (((hA i).2.symm.trans (congrArg SimpleGraph.Cycle.length eq)).trans (hD j).2)

/-- Doubling a decomposition replaces selected Hamilton cycles by two
Hamilton cycles each and selected triangular faces by four triangles each.
All remaining base pairs become squares. -/
theorem double_selected {m r h : ℕ} (hm : 4≤ m) {G : SimpleGraph (Fin m)} [DecidableRel G.Adj]
    (C : Multiset (Cycle G)) (dec : IsCycleDecomposition G C)
    (hr : r≤(lengths C).count m) (ht : h≤(lengths C).count 3)
    (I : (completeGraph (Fin (2*m))).Subgraph) (hI : I.IsPerfectMatching) :
    ∃ (q : ℕ) (D : Multiset (Cycle (completeGraph (Fin (2*m)) \ I.spanningCoe))),
      IsCycleDecomposition _ D ∧
      lengths D=Multiset.replicate (2*r) (2*m)+Multiset.replicate (4*h) 3+Multiset.replicate q 4 ∧
      q+m*r+3*h=m.choose 2 := by
  obtain ⟨σ,B,three,hs,ts,dj⟩ := extract_supports (by omega : m≠3) C dec hr ht
  obtain ⟨J,hJ,q,A,da,la,eq⟩ := AlspachTriangleHamilton.double_partial (by omega : 3≤ m) σ B three hs ts dj
  obtain ⟨iso⟩ := OMA.R_AlspachConjecture_alspach_conjecture_variants_even_R2.matchings_complements_iso J I hJ hI
  obtain ⟨D,dd,ld⟩ := OMA.R_AlspachConjecture_alspach_conjecture_variants_even_R2.iso_decomposition iso da la
  exact ⟨q,D,dd,ld,eq⟩

end AlspachIterated

namespace AlspachIterated

/-- When every unused base edge lifts to a square, the only numerical
restriction on the lifted list is the number of unavoidable squares. -/
theorem classify_leave {m r a u : ℕ} (hm : 3≤ m)
    (base : m*r+3*a+u=m.choose 2) (L : Multiset ℕ)
    (shape : ∀ x∈L,x=3 ∨ x=4 ∨ x=2*m) (budget : L.sum=(2*m).choose 2-(2*m)/2)
    (ham : L.count (2*m)=2*r) (squares : u≤L.count 4) :
    ∃ k, k≤a ∧ L=Multiset.replicate (2*r) (2*m)+Multiset.replicate (4*k) 3+
      Multiset.replicate (u+3*(a-k)) 4 := by
  have n3 : 2*m≠3 := by omega
  have n4 : 2*m≠4 := by omega
  have split : L=Multiset.replicate (2*r) (2*m)+Multiset.replicate (L.count 3) 3+
      Multiset.replicate (L.count 4) 4 := by
    ext x
    rcases eq_or_ne x (2*m) with rfl|hn
    · simp [Multiset.count_replicate,ham,Ne.symm n3,Ne.symm n4]
    rcases eq_or_ne x 3 with rfl|h₃
    · simp [Multiset.count_replicate,n3]
    rcases eq_or_ne x 4 with rfl|h₄
    · simp [Multiset.count_replicate,n4]
    have none : x∉L := fun h => (shape x h).elim h₃ (fun e => e.elim h₄ hn)
    simp [Multiset.count_replicate,Multiset.count_eq_zero.mpr none,Ne.symm h₃,Ne.symm h₄,Ne.symm hn]
  have eq := congrArg Multiset.sum split
  rw [budget,AlspachPaired.paired_budget m (by omega)] at eq
  simp only [Multiset.sum_add,Multiset.sum_replicate,smul_eq_mul] at eq
  have left : 3*L.count 3+4*L.count 4=12*a+4*u := by nlinarith only [eq,base]
  let k := L.count 3/4
  have tr : L.count 3=4*k := by dsimp [k]; omega
  have capacity : k≤a := by omega
  have qu : L.count 4=u+3*(a-k) := by omega
  exact ⟨k,capacity,by rwa [tr,qu] at split⟩
end AlspachIterated

namespace AlspachIterated
open SimpleGraph AlspachConjecture
open scoped Classical

theorem double_family {m r a u : ℕ} (hm : 4≤ m) {G : SimpleGraph (Fin m)} [DecidableRel G.Adj]
    (C : Multiset (Cycle G)) (dec : IsCycleDecomposition G C)
    (hr : r≤(lengths C).count m) (ha : a≤(lengths C).count 3)
    (base : m*r+3*a+u=m.choose 2)
    (I : (completeGraph (Fin (2*m))).Subgraph) (perfect : I.IsPerfectMatching)
    (L : Multiset ℕ) (shape : ∀ x∈L,x=3 ∨ x=4 ∨ x=2*m)
    (budget : L.sum=(2*m).choose 2-(2*m)/2) (ham : L.count (2*m)=2*r) (squares : u≤L.count 4) :
    ∃ D : Multiset (Cycle (completeGraph (Fin (2*m)) \ I.spanningCoe)), IsCycleDecomposition _ D ∧ lengths D=L := by
  obtain ⟨k,hk,eq⟩ := classify_leave (by omega) base L shape budget ham squares
  obtain ⟨q,D,hd,hl,size⟩ := double_selected hm C dec hr (hk.trans ha) I perfect
  refine ⟨D,hd,?_⟩
  rw [hl,eq,show q=u+3*(a-k) by omega]

/-- A complete matched base supported on three lengths leaves one unused base
edge per matching edge and four unused base edges per unselected square. -/
theorem base_counts {m r a q : ℕ} (hm : 5≤ m)
    (budget : (Multiset.replicate r m+Multiset.replicate a 3+Multiset.replicate q 4).sum=m.choose 2-m/2) :
    m*r+3*a+(m/2+4*q)=m.choose 2 := by
  simp only [Multiset.sum_add,Multiset.sum_replicate,smul_eq_mul] at budget
  have twice : 2*m.choose 2=m*(m-1) := by
    obtain ⟨j,rfl⟩ : ∃ j, m=j+1 := ⟨m-1,by omega⟩
    simpa [Nat.mul_comm] using (Nat.add_one_mul_choose_eq j 1).symm
  have bound : m*2≤ m*(m-1) := Nat.mul_le_mul_left m (by omega)
  have enough : m/2≤ m.choose 2 := by omega
  rw [Nat.mul_comm m r,Nat.mul_comm 3 a,Nat.mul_comm 4 q]
  omega
end AlspachIterated

namespace AlspachIterated
open SimpleGraph AlspachConjecture Finset
open scoped Classical

theorem matched_budget {m r a q : ℕ} (hm : 5≤ m) (J : (completeGraph (Fin m)).Subgraph)
    (perf : J.IsPerfectMatching) (C : Multiset (Cycle (completeGraph (Fin m) \ J.spanningCoe)))
    (dec : IsCycleDecomposition _ C)
    (lens : lengths C=Multiset.replicate r m+Multiset.replicate a 3+Multiset.replicate q 4) :
    m*r+3*a+(m/2+4*q)=m.choose 2 := by
  apply base_counts hm
  rw [←lens,AlspachLadder.decomposition_budget C dec]
  have edges := TriangleBridge.matching_budget J perf
  rw [Fintype.card_fin] at edges
  convert edges using 1
  congr 1
  ext edge
  simp only [mem_edgeFinset]

theorem seed_step {m r a q : ℕ} (hm : 5≤ m)
    (seed : ∃ J : (completeGraph (Fin m)).Subgraph, J.IsPerfectMatching ∧
      ∃ C : Multiset (Cycle (completeGraph (Fin m) \ J.spanningCoe)), IsCycleDecomposition _ C ∧
        lengths C=Multiset.replicate r m+Multiset.replicate a 3+Multiset.replicate q 4) :
    ∃ I : (completeGraph (Fin (2*m))).Subgraph, I.IsPerfectMatching ∧
      ∃ D : Multiset (Cycle (completeGraph (Fin (2*m)) \ I.spanningCoe)), IsCycleDecomposition _ D ∧
        lengths D=Multiset.replicate (2*r) (2*m)+Multiset.replicate (4*a) 3+Multiset.replicate (m/2+4*q) 4 := by
  classical
  obtain ⟨J,hJ,C,dc,sz⟩ := seed
  have budget := matched_budget hm J hJ C dc sz
  have cr : r≤(lengths C).count m := by simp [sz,Multiset.count_replicate,show 3≠m by omega,show 4≠m by omega]
  have ca : a≤(lengths C).count 3 := by simp [sz,Multiset.count_replicate]
  let f : Fin m × Bool ≃ Fin (2*m) := Fintype.equivOfCardEq (by simp; omega)
  obtain ⟨I,hI,_⟩ := AlspachSquares.pair_matching f
  obtain ⟨u,D,dd,lens,cnt⟩ := double_selected (by omega) C dc cr ca I hI
  exact ⟨I,hI,D,dd,by rwa [show u=m/2+4*q by omega] at lens⟩
end AlspachIterated

namespace AlspachIterated
open SimpleGraph AlspachConjecture
open scoped Classical

theorem choose_double (d : ℕ) (pos : 0<d) : (2*d).choose 2=4*d.choose 2+d := by
  have twice (z : ℕ) (hz : 0<z) : 2*z.choose 2=z*(z-1) := by
    obtain ⟨j,rfl⟩ : ∃ j,z=j+1 := ⟨z-1,by omega⟩
    simpa [Nat.mul_comm] using (Nat.add_one_mul_choose_eq j 1).symm
  have e := twice d pos
  have f := twice (2*d) (by omega)
  have a := congrArg (fun x : ℕ => d*x) (Nat.sub_add_cancel (show 1≤d by omega))
  have b := congrArg (fun x : ℕ => d*x) (Nat.sub_add_cancel (show 1≤2*d by omega))
  nlinarith only [e,f,a,b]

theorem square_step {m : ℕ} (even : Even m) (q e : ℕ) :
    4^(e+1)*q+(2^(e+1)).choose 2*(m/2)=
      (2^e*m)/2+4*(4^e*q+(2^e).choose 2*(m/2)) := by
  have dvd : 2∣m := by obtain ⟨k,h⟩ := even; exact ⟨k,by omega⟩
  rw [pow_succ' (2:ℕ),pow_succ' (4:ℕ),choose_double _ (by positivity),Nat.mul_div_assoc (2^e) dvd]
  ring

/-- After e doublings an original square gives 4^e squares. The matching
edges of all intermediate orders give an additional binomial coefficient. -/
theorem iterated_seed {m r a q : ℕ} (hm : 5≤ m) (even : Even m)
    (seed : ∃ J : (completeGraph (Fin m)).Subgraph, J.IsPerfectMatching ∧
      ∃ C : Multiset (Cycle (completeGraph (Fin m) \ J.spanningCoe)), IsCycleDecomposition _ C ∧
        lengths C=Multiset.replicate r m+Multiset.replicate a 3+Multiset.replicate q 4) (e : ℕ) :
    ∃ I : (completeGraph (Fin (2^e*m))).Subgraph, I.IsPerfectMatching ∧
      ∃ D : Multiset (Cycle (completeGraph (Fin (2^e*m)) \ I.spanningCoe)), IsCycleDecomposition _ D ∧
      lengths D=Multiset.replicate (2^e*r) (2^e*m)+Multiset.replicate (4^e*a) 3+
        Multiset.replicate (4^e*q+(2^e).choose 2*(m/2)) 4 := by
  let good (n h u w : ℕ) : Prop := ∃ I : (completeGraph (Fin n)).Subgraph, I.IsPerfectMatching ∧
    ∃ D : Multiset (Cycle (completeGraph (Fin n) \ I.spanningCoe)), IsCycleDecomposition _ D ∧
      lengths D=Multiset.replicate h n+Multiset.replicate u 3+Multiset.replicate w 4
  change good (2^e*m) (2^e*r) (4^e*a) (4^e*q+(2^e).choose 2*(m/2))
  induction e with
  | zero =>
    simpa only [pow_zero,one_mul,show (1:ℕ).choose 2=0 by decide,zero_mul,add_zero] using (show good m r a q from seed)
  | succ e ih =>
    have large : 5≤2^e*m := by
      have big := Nat.mul_le_mul_right m (show 1≤2^e from pow_pos (by decide : 0<(2:ℕ)) _)
      omega
    have step : good (2*(2^e*m)) (2*(2^e*r)) (4*(4^e*a))
        ((2^e*m)/2+4*(4^e*q+(2^e).choose 2*(m/2))) := seed_step large ih
    rw [square_step even q e]
    simpa only [pow_succ' (2:ℕ),pow_succ' (4:ℕ),Nat.mul_assoc] using step
/-- Repeated doubling realizes every target list above the square threshold,
starting from any one matched decomposition using triangles, squares and
Hamilton cycles. -/
theorem iterated_lists {m r a q : ℕ} (hm : 5≤ m) (even : Even m)
    (seed : ∃ J : (completeGraph (Fin m)).Subgraph, J.IsPerfectMatching ∧
      ∃ C : Multiset (Cycle (completeGraph (Fin m) \ J.spanningCoe)), IsCycleDecomposition _ C ∧
        lengths C=Multiset.replicate r m+Multiset.replicate a 3+Multiset.replicate q 4)
    (e n : ℕ) (order : n=2^(e+1)*m) (I : (completeGraph (Fin n)).Subgraph) (hI : I.IsPerfectMatching)
    (L : Multiset ℕ) (shape : ∀ x∈L,x=3 ∨ x=4 ∨ x=n) (budget : L.sum=n.choose 2-n/2)
    (ham : L.count n=2^(e+1)*r)
    (squares : 4^(e+1)*q+(2^(e+1)).choose 2*(m/2)≤L.count 4) :
    ∃ D : Multiset (Cycle (completeGraph (Fin n) \ I.spanningCoe)), IsCycleDecomposition _ D ∧ lengths D=L := by
  classical
  rw [pow_succ',Nat.mul_assoc] at order
  subst n
  obtain ⟨J,hJ,C,dc,sz⟩ := iterated_seed hm even seed e
  have large : 5≤2^e*m := by
    have h := Nat.mul_le_mul_right m (show 1≤2^e from pow_pos (by decide : 0<(2:ℕ)) _)
    omega
  have cr : 2^e*r≤(lengths C).count (2^e*m) := by
    simp [sz,Multiset.count_replicate,show 3≠2^e*m by omega,show 4≠2^e*m by omega]
  have ca : 4^e*a≤(lengths C).count 3 := by simp [sz,Multiset.count_replicate]
  have base := matched_budget large J hJ C dc sz
  rw [square_step even q e] at squares
  rw [pow_succ' (2:ℕ) e,Nat.mul_assoc] at ham
  exact double_family (by omega) C dc cr ca base I hI L shape budget ham squares
/-- The requested Hamilton cycles, triangles and remaining squares exhaust the
edge budget of the complement of one perfect matching. -/
theorem odd_minimum_budget {t s : ℕ} (positive : 0<t) (hi : s≤t) :
    (Multiset.replicate (2*s) (6*t) + Multiset.replicate (4*(t*(t-s)+3*(t.choose 2/3))) 3 +
      Multiset.replicate (3*(t.choose 2%3)) 4).sum = (6*t).choose 2-(6*t)/2 := by
  have twice (n : ℕ) (hn : 0<n) : 2*n.choose 2=n*(n-1) := by
    obtain ⟨j,rfl⟩ : ∃ j, n=j+1 := ⟨n-1,by omega⟩
    simpa [Nat.mul_comm] using (Nat.add_one_mul_choose_eq j 1).symm
  have base : (3*t)*s+3*(t*(t-s)+t.choose 2)=(3*t).choose 2 := by
    have mul1 := congrArg (fun z : ℕ => t*z) (Nat.sub_add_cancel hi)
    have mul2 := Nat.sub_add_cancel (show 1≤t by omega)
    have mul3 := Nat.sub_add_cancel (show 1≤3*t by omega)
    nlinarith only [twice t positive,twice (3*t) (by omega),mul1,
      congrArg (fun z : ℕ => t*z) mul2,congrArg (fun z : ℕ => (3*t)*z) mul3]
  have remainder := Nat.mod_add_div (t.choose 2) 3
  simp only [Multiset.sum_add,Multiset.sum_replicate,smul_eq_mul]
  rw [show 6*t=2*(3*t) by omega,AlspachPaired.paired_budget (3*t) (by omega)]
  nlinarith only [base,remainder]

/-- On six times an odd order, attain the minimum square count from the
three internal groups, with any permitted even Hamilton count. -/
theorem odd_minimum_seed {t s : ℕ} (odd : Odd t) (large : 3≤t) (lo : 2≤ s) (hi : s≤t) :
    ∃ J : (completeGraph (Fin (6*t))).Subgraph, J.IsPerfectMatching ∧
      ∃ C : Multiset (Cycle (completeGraph (Fin (6*t)) \ J.spanningCoe)),
        IsCycleDecomposition _ C ∧ lengths C =
        Multiset.replicate (2*s) (6*t) + Multiset.replicate (4*(t*(t-s)+3*(t.choose 2/3))) 3 +
          Multiset.replicate (3*(t.choose 2%3)) 4 := by
  classical
  let L := Multiset.replicate (2*s) (6*t) + Multiset.replicate (4*(t*(t-s)+3*(t.choose 2/3))) 3 +
    Multiset.replicate (3*(t.choose 2%3)) 4
  have shape (a : ℕ) (ha : a∈L) : a=3 ∨ a=4 ∨ a=6*t := by
    rcases Multiset.mem_add.mp ha with left|four
    · rcases Multiset.mem_add.mp left with ham|tri
      · exact Or.inr (Or.inr (Multiset.eq_of_mem_replicate ham))
      · exact Or.inl (Multiset.eq_of_mem_replicate tri)
    · exact Or.inr (Or.inl (Multiset.eq_of_mem_replicate four))
  have countN : L.count (6*t)=2*s := by
    simp [L,Multiset.count_replicate,show (3:ℕ)≠6*t by omega,show (4:ℕ)≠6*t by omega]
  have count4 : L.count 4=3*(t.choose 2%3) := by
    simp [L,Multiset.count_replicate,show 6*t≠4 by omega]
  let f : (Fin (3*t) × Bool) ≃ Fin (6*t) := Fintype.equivOfCardEq (by simp; omega)
  obtain ⟨J,perf,_⟩ := AlspachSquares.pair_matching f
  refine ⟨J,perf,?_⟩
  apply AlspachHamiltonMix.triangle_square_hamilton_six_mod_twelve (6*t)
    (by obtain ⟨j,hj⟩ := odd; omega) J perf L shape (odd_minimum_budget (by omega) hi)
  right
  rw [countN]
  refine ⟨⟨s,by omega⟩,by omega,by omega,?_⟩
  by_cases residue : (6*t)%36=30
  · right
    rw [count4,AlspachHamiltonMix.minimum_squares,if_pos (show t%3=2 by omega)]
  · exact Or.inl residue

/-- Write the target order as 6td, with t odd and d a positive power of two
greater than one. The starting complement has 2s Hamilton cycles. At each
doubling, unused edges of the base matching contribute one square each. -/
theorem tripartite_doublings {t s : ℕ} (odd : Odd t) (large : 3≤t) (lo : 2≤ s) (hi : s≤t)
    (e n : ℕ) (order : n=2^(e+1)*(6*t)) (I : (completeGraph (Fin n)).Subgraph) (hI : I.IsPerfectMatching)
    (L : Multiset ℕ) (shape : ∀ x∈L,x=3 ∨ x=4 ∨ x=n) (budget : L.sum=n.choose 2-n/2)
    (ham : L.count n=2^(e+1)*(2*s))
    (squares : 4^(e+1)*(3*(t.choose 2%3))+(2^(e+1)).choose 2*(3*t)≤L.count 4) :
    ∃ D : Multiset (Cycle (completeGraph (Fin n) \ I.spanningCoe)), IsCycleDecomposition _ D ∧ lengths D=L := by
  exact iterated_lists (m:=6*t) (by omega) (show Even (6*t) from ⟨3*t,by omega⟩)
    (odd_minimum_seed odd large lo hi) e n order I hI L shape budget ham (by simpa only [show 6*t/2=3*t by omega] using squares)
end AlspachIterated

namespace AlspachLangford
open Finset SimpleGraph AlspachConjecture
open scoped Classical
open Fin.NatCast

/-- A positive cyclic step of less than half the order determines both its
length and starting point from its unordered endpoints. -/
theorem segment_unique {m a b : ℕ} [NeZero m] (x y : Fin m)
    (ha : 0<a ∧ 2*a< m) (hb : 0<b ∧ 2*b< m)
    (eq : s(x,x+(a : Fin m))=s(y,y+(b : Fin m))) : x=y ∧ a=b := by
  rcases Sym2.eq_iff.mp eq with ⟨rfl,forward⟩ | ⟨back,forward⟩
  · have same := add_left_cancel forward
    have vals := congrArg Fin.val same
    refine ⟨rfl,?_⟩
    simpa [Fin.val_natCast,Nat.mod_eq_of_lt (show a< m by omega),Nat.mod_eq_of_lt (show b< m by omega)] using vals
  · have none : (a+b : Fin m)=0 := by
      apply add_left_cancel (a:=x)
      calc x+((a : Fin m)+b) = (x+a)+b := (add_assoc ..).symm
           _ = x := by rw [forward,←back]
           _ = x+0 := (add_zero x).symm
    have vals := congrArg Fin.val none
    rw [←Nat.cast_add,Fin.val_natCast,Nat.mod_eq_of_lt (show a+b< m by omega)] at vals
    change a+b=0 at vals
    omega

/-- Each non-loop edge on three vertices joins two of their three pairs. -/
theorem clique_three_edges {m : ℕ} {p q r : Fin m} {e : Sym2 (Fin m)}
    (he : e∈(⊤ : SimpleGraph (Fin m)).edgeFinset.filter (fun d => d.toFinset ⊆ ({p,q,r} : Finset _))) :
    e=s(p,q) ∨ e=s(q,r) ∨ e=s(p,r) := by
  induction e using Sym2.ind with
  | _ x y =>
    have h : x≠y ∧ (x=p ∨ x=q ∨ x=r) ∧ (y=p ∨ y=q ∨ y=r) := by
      simpa [Sym2.toFinset_mk_eq,Finset.insert_subset_iff] using he
    simp only [Sym2.eq_iff]
    grind

/-- The translates of the three partial sums of each signed difference triple
give three-vertex blocks. Different translates have disjoint clique edges,
and none contains an edge of the usual cyclic Hamilton ordering. -/
theorem signed_difference_blocks {k : ℕ} (d : Fin k → Fin 3 → ℕ)
    (bounds : ∀ i j,2≤d i j ∧ d i j≤3*k+1)
    (distinct : Function.Injective (fun z : Fin k × Fin 3 => d z.1 z.2))
    (law : ∀ i,d i 0+d i 1=d i 2 ∨ d i 0+d i 1+d i 2=6*k+3) :
    let m := 6*k+3
    let next (i : Fin m) : Fin m := ⟨(i.val+1)%m,Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩
    ∃ B : (Fin k × Fin m) → Finset (Fin m),
      let T (i : Fin k × Fin m) := (⊤ : SimpleGraph (Fin m)).edgeFinset.filter fun e => e.toFinset ⊆ B i
      (∀ i,(B i).card=3) ∧ Pairwise (fun i j => Disjoint (T i) (T j)) ∧
      ∀ i, Disjoint (univ.image fun z => s(z,next z)) (T i) := by
  classical
  intro m next
  let : NeZero m := ⟨by dsimp [m]; omega⟩
  let A (i : Fin k) := (d i 0 : Fin m)
  let V (i : Fin k) := (d i 1 : Fin m)
  let off (i : Fin k) (j : Fin 3) : Fin m :=
    if j=0 then 0 else if j=1 then A i else if d i 0+d i 1=d i 2 then 0 else A i+V i
  let B (z : Fin k × Fin m) := ({z.2,z.2+A z.1,z.2+(A z.1+V z.1)} : Finset (Fin m))
  let T (z : Fin k × Fin m) := (⊤ : SimpleGraph (Fin m)).edgeFinset.filter fun e => e.toFinset ⊆ B z
  have short (i : Fin k) (j : Fin 3) : 0<d i j ∧ 2*d i j< m := by
    have := bounds i j
    dsimp [m]
    omega
  have positive {a : ℕ} (lo : 0<a) (hi : a< m) : (a : Fin m)≠0 := by
    intro h
    have v := congrArg Fin.val h
    rw [Fin.val_cast_of_lt hi] at v
    change a=0 at v
    omega
  have three (i : Fin k) (p : Fin m) : (B (i,p)).card=3 := by
    have h0 := short i 0
    have h1 := short i 1
    have na : A i≠0 := positive h0.1 (by omega)
    have nb : V i≠0 := positive h1.1 (by omega)
    have nc : A i+V i≠0 := by
      change (d i 0 : Fin m)+(d i 1 : Fin m)≠0
      rw [←Nat.cast_add]
      exact positive (by omega) (by omega)
    simp [B,na,nb,nc]
  have which (z : Fin k × Fin m) (e : Sym2 (Fin m)) (he : e∈T z) :
      ∃ j : Fin 3, e=s(z.2+off z.1 j,z.2+off z.1 j+(d z.1 j : Fin m)) := by
    rcases z with ⟨i,p⟩
    obtain h|h|h := clique_three_edges he
    · exact ⟨0,by simpa [off,A] using h⟩
    · exact ⟨1,by simpa [off,A,V,add_assoc] using h⟩
    · by_cases plus : d i 0+d i 1=d i 2
      · have eq : A i+V i=(d i 2 : Fin m) := by
          change (d i 0 : Fin m)+(d i 1 : Fin m)=_
          rw [←Nat.cast_add,plus]
        exact ⟨2,by simpa [off,plus,eq] using h⟩
      · have total := (law i).resolve_left plus
        have zero : (A i+V i)+(d i 2 : Fin m)=0 := by
          change (d i 0 : Fin m)+(d i 1 : Fin m)+(d i 2 : Fin m)=0
          rw [←Nat.cast_add,←Nat.cast_add,total]
          exact Fin.natCast_self m
        refine ⟨2,?_⟩
        calc e = s(p,p+(A i+V i)) := h
             _ = s(p+(A i+V i),p) := Sym2.eq_swap
             _ = _ := by simp [off,plus,add_assoc p (A i+V i),zero]
  refine ⟨B,fun z => three z.1 z.2,?_,?_⟩
  · intro x y ne
    apply Finset.disjoint_left.mpr
    intro e hx hy
    obtain ⟨j,ej⟩ := which x e hx
    obtain ⟨l,el⟩ := which y e hy
    obtain ⟨start,values⟩ := segment_unique _ _ (short x.1 j) (short y.1 l) (ej.symm.trans el)
    have ij : (x.1,j)=(y.1,l) := distinct values
    have ij1 : x.1=y.1 := Prod.mk.inj ij |>.1
    have ij2 : j=l := Prod.mk.inj ij |>.2
    rw [ij1,ij2] at start
    exact ne (Prod.ext ij1 (add_right_cancel start))
  · intro z
    apply Finset.disjoint_left.mpr
    intro e hh ht
    obtain ⟨p,_,ep⟩ := mem_image.mp hh
    obtain ⟨j,ej⟩ := which z e ht
    have next_one : next p=p+(1 : ℕ) := by apply Fin.ext; rfl
    rw [next_one] at ep
    have eq := (segment_unique p _ (a:=1) (by dsimp [m]; omega) (short z.1 j) (ep.trans ej)).2
    have := bounds z.1 j
    omega

end AlspachLangford

namespace AlspachLangford
open Finset SimpleGraph
open scoped Classical

/-- A Hamilton ring and km edge-disjoint triples use every edge on 6k+3 points. -/
theorem complete_inventory (k : ℕ) :
    let m := 6*k+3
    let next (i : Fin m) : Fin m := ⟨(i.val+1)%m,Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩
    ∀ B : (Fin k × Fin m) → Finset (Fin m),
      let H := univ.image fun z => s(z,next z)
      let T (i : Fin k × Fin m) := (⊤ : SimpleGraph (Fin m)).edgeFinset.filter fun e => e.toFinset ⊆ B i
      (∀ i,(B i).card=3) → Pairwise (fun i j => Disjoint (T i) (T j)) →
      (∀ i, Disjoint H (T i)) →
      (⊤ : SimpleGraph (Fin m)).edgeFinset ⊆ H ∪ univ.biUnion T := by
  classical
  intro m next B H T three disjoint away
  have large : 3≤ m := by dsimp [m]; omega
  have advance (a : Fin m) : (next a).val=if a.val+1=m then 0 else a.val+1 := by
    change (a.val+1)%m=_
    have := a.isLt
    split
    · rename_i e
      rw [e,Nat.mod_self]
    · rw [Nat.mod_eq_of_lt (by omega)]
  have nofix (a : Fin m) : a≠next a := by
    intro eq
    have ha := congrArg Fin.val eq
    rw [advance] at ha
    split at ha <;> omega
  have notTwo (a : Fin m) : next (next a)≠a := by
    intro eq
    have ha := congrArg Fin.val eq
    rw [advance,advance] at ha
    split_ifs at ha <;> omega
  have smallH : H ⊆ (⊤ : SimpleGraph (Fin m)).edgeFinset := by
    rintro e he
    obtain ⟨a,_,rfl⟩ := mem_image.mp he
    exact SimpleGraph.mem_edgeFinset.mpr (nofix a)
  have sizeH : H.card=m := by
    change (univ.image (fun z => s(z,next z))).card=m
    rw [card_image_of_injective]
    · simp
    · intro a b eq
      rcases Sym2.eq_iff.mp eq with ⟨h,_⟩|⟨h,q⟩
      · exact h
      · exact False.elim (notTwo b ((congrArg next h.symm).trans q))
  have sizeT (p : Fin k × Fin m) : (T p).card=3 := by
    obtain ⟨a,b,c,ab,ac,bc,eq⟩ := card_eq_three.mp (three p)
    have support : T p={s(a,b),s(a,c),s(b,c)} := by
      ext e
      induction e using Sym2.ind with
      | _ x y =>
        simp only [T,eq,mem_filter,SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet,
          SimpleGraph.top_adj,Sym2.toFinset_mk_eq,insert_subset_iff,singleton_subset_iff,
          mem_insert,mem_singleton,Sym2.eq_iff]
        grind
    rw [support]
    simp [ab,ac,bc,Ne.symm ab,Ne.symm bc]
  have small : H ∪ univ.biUnion T ⊆ (⊤ : SimpleGraph (Fin m)).edgeFinset := by
    intro e he
    rcases mem_union.mp he with h|h
    · exact smallH h
    · obtain ⟨i,_,hi⟩ := mem_biUnion.mp h
      exact (mem_filter.mp hi).1
  have separate : Disjoint H (univ.biUnion T) := by
    apply Finset.disjoint_left.mpr
    intro e he hit
    obtain ⟨i,_,ht⟩ := mem_biUnion.mp hit
    exact Finset.disjoint_left.mp (away i) he ht
  have twins : ((univ : Finset (Fin k × Fin m)) : Set _).PairwiseDisjoint T :=
    fun _ _ _ _ ne => disjoint ne
  have edges : m.choose 2=m+(k*m)*3 := by
    rw [Nat.choose_two_right,show m-1=6*k+2 by dsimp [m]]
    have prod : m*(6*k+2)=2*(m+(k*m)*3) := by ring
    rw [prod,Nat.mul_div_cancel_left _ (by decide : 0<2)]
  apply (Finset.eq_of_subset_of_card_le small ?_).ge
  rw [card_union_of_disjoint separate,sizeH,card_biUnion twins,card_edgeFinset_top_eq_card_choose_two]
  simp only [sizeT,sum_const,card_univ,Fintype.card_prod,Fintype.card_fin,smul_eq_mul,edges]
  exact le_rfl

end AlspachLangford

namespace AlspachLangford
open Finset SimpleGraph AlspachConjecture
open scoped Classical

/-- Double one cyclic Hamilton ordering and a complete family of translated
triangle supports, with any incidence-preserving indexing of the blocks. -/
theorem lists_from_inventory {m : ℕ} (hm : 3≤ m) {A : Type} [Fintype A] [DecidableEq A]
    (B : A → Finset (Fin m)) (three : ∀ i,(B i).card=3) :
    let next (i : Fin m) : Fin m := ⟨(i.val+1)%m,Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩
    let H := univ.image fun z => s(z,next z)
    let T (i : A) := (⊤ : SimpleGraph (Fin m)).edgeFinset.filter fun e => e.toFinset ⊆ B i
    Pairwise (fun i j => Disjoint (T i) (T j)) → (∀ i,Disjoint H (T i)) →
    (⊤ : SimpleGraph (Fin m)).edgeFinset ⊆ H ∪ univ.biUnion T →
    ∀ (I : (completeGraph (Fin (2*m))).Subgraph), I.IsPerfectMatching → ∀ L : Multiset ℕ,
      (∀ a∈L,a=3 ∨ a=4 ∨ a=2*m) → L.sum=(2*m).choose 2-(2*m)/2 → L.count (2*m)=2 →
      ∃ C : Multiset (Cycle (completeGraph (Fin (2*m)) \ I.spanningCoe)), IsCycleDecomposition _ C ∧ lengths C=L := by
  classical
  intro next H T pair sep all I hI L shape budget ham
  let e := (Fintype.equivFin A).symm
  let σ (_ : Fin 1) := Equiv.refl (Fin m)
  have hs : Pairwise (fun i j : Fin 1 => Disjoint H H) := fun i j ne => False.elim (ne (Subsingleton.elim i j))
  have ts : Pairwise (fun i j => Disjoint (T (e i)) (T (e j))) := fun i j ij => pair (e.injective.ne_iff.mpr ij)
  have dj : Disjoint (univ.biUnion (fun _ : Fin 1 => H)) (univ.biUnion (fun i => T (e i))) := by
    apply Finset.disjoint_left.mpr
    intro edge ha hb
    obtain ⟨_,_,a⟩ := mem_biUnion.mp ha
    obtain ⟨i,_,b⟩ := mem_biUnion.mp hb
    exact Finset.disjoint_left.mp (sep _) a b
  have fill : (⊤ : SimpleGraph (Fin m)).edgeFinset ⊆
      (univ.biUnion (fun _ : Fin 1 => H)) ∪ (univ.biUnion fun i => T (e i)) := by
    intro edge he
    obtain a|b := mem_union.mp (all he)
    · exact mem_union_left _ (mem_biUnion.mpr ⟨0,mem_univ _,a⟩)
    · obtain ⟨i,_,hi⟩ := mem_biUnion.mp b
      obtain ⟨j,rfl⟩ := e.surjective i
      exact mem_union_right _ (mem_biUnion.mpr ⟨j,mem_univ _,hi⟩)
  exact AlspachTriangleHamilton.double_lists hm σ (fun i => B (e i)) (fun i => three _) hs ts dj fill I hI L shape budget ham

end AlspachLangford

/- The four position tables formalize defect-two Langford pairings. The ordinary
orders use the patterns of R. O. Davies, “On Langford’s problem (II),”
Mathematical Gazette 43 (1959), 253–255. The hooked orders use explicit
placements for the remaining two congruence classes. The general existence
result for perfect and hooked sequences is due to J. E. Simpson,
Discrete Mathematics 44 (1983), 97–104, doi:10.1016/0012-365X(83)90008-0. -/

namespace AlspachLangford

/-- A checked inverse of the packed difference table proves disjointness. -/
theorem packed_differences {k : ℕ} (digits inverse : ℕ) :
    let d (i : Fin k) (j : Fin 3) := (digits >>> (6*(3*i.val+j.val))) &&& 63
    let index (x : ℕ) := (inverse >>> (6*x)) &&& 63
    (∀ i j, 2≤d i j ∧ d i j≤3*k+1) →
    (∀ (i : Fin k) (j : Fin 3), index (d i j)=3*i.val+j.val) →
    (∀ i, d i 0+d i 1=d i 2 ∨ d i 0+d i 1+d i 2=6*k+3) →
    ∃ d : Fin k → Fin 3 → ℕ,
      (∀ i j, 2≤d i j ∧ d i j≤3*k+1) ∧
      Function.Injective (fun z : Fin k × Fin 3 => d z.1 z.2) ∧
      (∀ i, d i 0+d i 1=d i 2 ∨ d i 0+d i 1+d i 2=6*k+3) := by
  intro d index bounds lookup laws
  refine ⟨d,bounds,?_,laws⟩
  rintro ⟨a,b⟩ ⟨c,e⟩ h
  change d a b=d c e at h
  have eq := congrArg index h
  rw [lookup,lookup] at eq
  have hb := b.isLt
  have he := e.isLt
  have ac : a=c := Fin.ext (by omega)
  have be : b=e := Fin.ext (by omega)
  simp [ac,be]

/-- Signed cyclic difference triples for the first six orders 6k+3. -/
theorem first_six (k : ℕ) (positive : 1≤k) (upper : k≤6) :
    ∃ d : Fin k → Fin 3 → ℕ,
      (∀ i j, 2≤d i j ∧ d i j≤3*k+1) ∧
      Function.Injective (fun z : Fin k × Fin 3 => d z.1 z.2) ∧
      (∀ i, d i 0+d i 1=d i 2 ∨ d i 0+d i 1+d i 2=6*k+3) := by
  have cases : k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 ∨ k=6 := by omega
  rcases cases with rfl|rfl|rfl|rfl|rfl|rfl
  · exact packed_differences 0x40c2 0x2040000 (by decide) (by decide) (by decide)
  · exact packed_differences 0x1c50c6102 0x1421010c0000 (by decide) (by decide) (by decide)
  · exact packed_differences 0xa1842050c91c2 0x80850471060c0000 (by decide) (by decide) (by decide)
  · exact packed_differences 0x28920d1c630b1050c2 0x20510b2891c6083040000 (by decide) (by decide) (by decide)
  · exact packed_differences 0xe2c840a1cf3063491050c2 0xb20e14734a10c246083040000 (by decide) (by decide) (by decide)
  · exact packed_differences 0x3ce29330848b1d14063491050c2 0x38b20745014d28f10c246083040000 (by decide) (by decide) (by decide)

/-- Pairs of positions at distances two through k+1 give signed difference
triples. A terminal hole permits the last occupied position to fold down
one place, changing its additive triple into a complementary triple. -/
theorem position_differences {k : ℕ} (hk : 0<k) (hole : ℕ)
    (endhole : hole=2*k-1 ∨ hole=2*k) (owner : ℕ→ℕ)
    (pairs : ∀ x : ℕ,1≤x → x≤k → ∃ p : ℕ, p+x+1≤2*k ∧ p≠hole ∧ p+x+1≠hole ∧
      owner p=x ∧ owner (p+x+1)=x) :
    ∃ d : Fin k → Fin 3 → ℕ,
      (∀ i j,2≤d i j ∧ d i j≤3*k+1) ∧
      Function.Injective (fun z : Fin k × Fin 3 => d z.1 z.2) ∧
      (∀ i,d i 0+d i 1=d i 2 ∨ d i 0+d i 1+d i 2=6*k+3) := by
  classical
  choose start sites using fun i : Fin k => pairs (i.val+1) (by omega) (by omega)
  let finish (i : Fin k) := start i+(i.val+1)+1
  let pos (i : Fin k) (b : Bool) := if b then finish i else start i
  let fold (z : ℕ) := if z=2*k then 2*k-1 else z
  have valid (i : Fin k) (b : Bool) :
      pos i b≤2*k ∧ pos i b≠hole ∧ owner (pos i b)=i.val+1 := by
    obtain ⟨hi,loHole,hiHole,loOwner,hiOwner⟩ := sites i
    cases b
    · exact ⟨by dsimp [pos]; omega,loHole,loOwner⟩
    · exact ⟨hi,hiHole,hiOwner⟩
  have bound (i : Fin k) (b : Bool) : fold (pos i b) < 2*k := by
    have q := (valid i b).1
    unfold fold
    split <;> omega
  have inject (i j : Fin k) (b c : Bool) (h : fold (pos i b)=fold (pos j c)) :
      i=j ∧ b=c := by
    obtain ⟨ib,ih,io⟩ := valid i b
    obtain ⟨jb,jh,jo⟩ := valid j c
    have eq : pos i b=pos j c := by
      unfold fold at h
      split at h <;> split at h <;> omega
    have ij : i=j := Fin.ext (by rw [eq,jo] at io; omega)
    subst j
    refine ⟨rfl,?_⟩
    cases b <;> cases c
    · rfl
    · change start i=start i+(i.val+1)+1 at eq
      omega
    · change start i+(i.val+1)+1=start i at eq
      omega
    · rfl
  let d (i : Fin k) (j : Fin 3) := if j=0 then i.val+2 else k+2+fold (pos i (decide (j=2)))
  refine ⟨d,?_,?_,?_⟩
  · intro i j
    have := bound i (decide (j=2))
    have := i.isLt
    dsimp [d]
    split <;> omega
  · rintro ⟨i,b⟩ ⟨j,c⟩ h
    change d i b=d j c at h
    by_cases hb : b=0 <;> by_cases hc : c=0
    · have ij : i=j := Fin.ext (by simpa [d,hb,hc] using h)
      exact Prod.ext ij (hb.trans hc.symm)
    · simp only [d,if_pos hb,if_neg hc] at h
      have := i.isLt
      omega
    · simp only [d,if_neg hb,if_pos hc] at h
      have := j.isLt
      omega
    · simp only [d,if_neg hb,if_neg hc,Nat.add_left_cancel_iff] at h
      have eq := inject i j _ _ h
      refine Prod.ext eq.1 ?_
      have tags := eq.2
      fin_cases b <;> fin_cases c <;> simp_all
  · intro i
    have hs := (sites i).1
    have lo : start i≠2*k := by omega
    by_cases last : finish i=2*k
    · right
      simp [d,pos,fold,lo,last]
      dsimp [finish] at last
      omega
    · left
      simp [d,pos,fold,lo,last,finish]
      omega

/-- Affine run construction for Langford order 4*r. -/
theorem affine_zero (r : ℕ) (large : 2≤ r) :
    let k := 4*r
    ∃ hole, (hole=2*k-1 ∨ hole=2*k) ∧ ∃ owner : ℕ → ℕ,
      ∀ x : ℕ, 1≤x → x≤k → ∃ p : ℕ,
      p+x+1≤2*k ∧ p≠hole ∧ p+x+1≠hole ∧ owner p=x ∧ owner (p+x+1)=x := by
  dsimp only
  let owner (z : ℕ) :=
    if z<(r-1) then (4*r-4)-2*(z-(0)) else
    if z<(2*r-2) then (2*r-3)-2*(z-(r-1)) else
    if z<(2*r-1) then 4*r-2 else
    if z<(3*r-2) then (1)+2*(z-(2*r-1)) else
    if z<(3*r-1) then 4*r-1 else
    if z<(4*r-2) then (2*r)+2*(z-(3*r-1)) else
    if z<(4*r-1) then 4*r else
    if z<(5*r-2) then (4*r-3)-2*(z-(4*r-1)) else
    if z<(6*r-3) then (2*r-2)-2*(z-(5*r-2)) else
    if z<(6*r-2) then 4*r-2 else
    if z<(6*r-1) then 2*r-1 else
    if z<(7*r-2) then (2)+2*(z-(6*r-1)) else
    if z<(7*r-1) then 4*r-1 else
    if z<(8*r-2) then (2*r+1)+2*(z-(7*r-1)) else
    if z<(8*r-1) then 2*r-1 else
    if z<(8*r) then 4*r else
    0
  refine ⟨8*r,by omega,owner,?_⟩
  intro x lo hi
  by_cases h0 : (2*r)≤x ∧ x≤(4*r-4) ∧ x%2=0
  · refine ⟨(0)+((4*r-4)-x)/2,by omega,by omega,by omega,?_,?_⟩
    all_goals
      dsimp only [owner]
      repeat' first | rw [if_pos (by omega)] | rw [if_neg (by omega)]
      omega
  by_cases h1 : (1)≤x ∧ x≤(2*r-3) ∧ x%2=1
  · clear h0
    refine ⟨(r-1)+((2*r-3)-x)/2,by omega,by omega,by omega,?_,?_⟩
    all_goals
      dsimp only [owner]
      repeat' first | rw [if_pos (by omega)] | rw [if_neg (by omega)]
      omega
  by_cases h2 : x=4*r-2
  · clear h0 h1
    refine ⟨2*r-2,by omega,by omega,by omega,?_,?_⟩
    all_goals
      dsimp only [owner]
      repeat' first | rw [if_pos (by omega)] | rw [if_neg (by omega)]
      omega
  by_cases h3 : x=4*r-1
  · clear h0 h1 h2
    refine ⟨3*r-2,by omega,by omega,by omega,?_,?_⟩
    all_goals
      dsimp only [owner]
      repeat' first | rw [if_pos (by omega)] | rw [if_neg (by omega)]
      omega
  by_cases h4 : x=4*r
  · clear h0 h1 h2 h3
    refine ⟨4*r-2,by omega,by omega,by omega,?_,?_⟩
    all_goals
      dsimp only [owner]
      repeat' first | rw [if_pos (by omega)] | rw [if_neg (by omega)]
      omega
  by_cases h5 : (2*r+1)≤x ∧ x≤(4*r-3) ∧ x%2=1
  · clear h0 h1 h2 h3 h4
    refine ⟨(4*r-1)+((4*r-3)-x)/2,by omega,by omega,by omega,?_,?_⟩
    all_goals
      dsimp only [owner]
      repeat' first | rw [if_pos (by omega)] | rw [if_neg (by omega)]
      omega
  by_cases h6 : (2)≤x ∧ x≤(2*r-2) ∧ x%2=0
  · clear h0 h1 h2 h3 h4 h5
    refine ⟨(5*r-2)+((2*r-2)-x)/2,by omega,by omega,by omega,?_,?_⟩
    all_goals
      dsimp only [owner]
      repeat' first | rw [if_pos (by omega)] | rw [if_neg (by omega)]
      omega
  by_cases h7 : x=2*r-1
  · clear h0 h1 h2 h3 h4 h5 h6
    refine ⟨6*r-2,by omega,by omega,by omega,?_,?_⟩
    all_goals
      dsimp only [owner]
      repeat' first | rw [if_pos (by omega)] | rw [if_neg (by omega)]
      omega
  omega

/-- Affine run construction for Langford order 4*r+1. -/
theorem affine_one (r : ℕ) (large : 2≤ r) :
    let k := 4*r+1
    ∃ hole, (hole=2*k-1 ∨ hole=2*k) ∧ ∃ owner : ℕ → ℕ,
      ∀ x : ℕ, 1≤x → x≤k → ∃ p : ℕ,
      p+x+1≤2*k ∧ p≠hole ∧ p+x+1≠hole ∧ owner p=x ∧ owner (p+x+1)=x := by
  dsimp only
  let owner (z : ℕ) :=
    if z<(1) then 4*r-2 else
    if z<(r) then (4*r-4)-2*(z-(1)) else
    if z<(2*r-1) then (2*r-3)-2*(z-(r)) else
    if z<(2*r) then 4*r-1 else
    if z<(3*r-1) then (1)+2*(z-(2*r)) else
    if z<(3*r) then 4*r else
    if z<(4*r-1) then (2*r)+2*(z-(3*r)) else
    if z<(4*r) then 4*r-2 else
    if z<(4*r+1) then 4*r+1 else
    if z<(5*r) then (4*r-3)-2*(z-(4*r+1)) else
    if z<(6*r-1) then (2*r-2)-2*(z-(5*r)) else
    if z<(6*r) then 4*r-1 else
    if z<(6*r+1) then 2*r-1 else
    if z<(7*r) then (2)+2*(z-(6*r+1)) else
    if z<(7*r+1) then 4*r else
    if z<(8*r) then (2*r+1)+2*(z-(7*r+1)) else
    if z<(8*r+1) then 2*r-1 else
    if z<(8*r+2) then 0 else
    if z<(8*r+3) then 4*r+1 else
    0
  refine ⟨8*r+1,by omega,owner,?_⟩
  intro x lo hi
  by_cases h0 : x=4*r-2
  · refine ⟨0,by omega,by omega,by omega,?_,?_⟩
    all_goals
      dsimp only [owner]
      repeat' first | rw [if_pos (by omega)] | rw [if_neg (by omega)]
      omega
  by_cases h1 : (2*r)≤x ∧ x≤(4*r-4) ∧ x%2=0
  · clear h0
    refine ⟨(1)+((4*r-4)-x)/2,by omega,by omega,by omega,?_,?_⟩
    all_goals
      dsimp only [owner]
      repeat' first | rw [if_pos (by omega)] | rw [if_neg (by omega)]
      omega
  by_cases h2 : (1)≤x ∧ x≤(2*r-3) ∧ x%2=1
  · clear h0 h1
    refine ⟨(r)+((2*r-3)-x)/2,by omega,by omega,by omega,?_,?_⟩
    all_goals
      dsimp only [owner]
      repeat' first | rw [if_pos (by omega)] | rw [if_neg (by omega)]
      omega
  by_cases h3 : x=4*r-1
  · clear h0 h1 h2
    refine ⟨2*r-1,by omega,by omega,by omega,?_,?_⟩
    all_goals
      dsimp only [owner]
      repeat' first | rw [if_pos (by omega)] | rw [if_neg (by omega)]
      omega
  by_cases h4 : x=4*r
  · clear h0 h1 h2 h3
    refine ⟨3*r-1,by omega,by omega,by omega,?_,?_⟩
    all_goals
      dsimp only [owner]
      repeat' first | rw [if_pos (by omega)] | rw [if_neg (by omega)]
      omega
  by_cases h5 : x=4*r+1
  · clear h0 h1 h2 h3 h4
    refine ⟨4*r,by omega,by omega,by omega,?_,?_⟩
    all_goals
      dsimp only [owner]
      repeat' first | rw [if_pos (by omega)] | rw [if_neg (by omega)]
      omega
  by_cases h6 : (2*r+1)≤x ∧ x≤(4*r-3) ∧ x%2=1
  · clear h0 h1 h2 h3 h4 h5
    refine ⟨(4*r+1)+((4*r-3)-x)/2,by omega,by omega,by omega,?_,?_⟩
    all_goals
      dsimp only [owner]
      repeat' first | rw [if_pos (by omega)] | rw [if_neg (by omega)]
      omega
  by_cases h7 : (2)≤x ∧ x≤(2*r-2) ∧ x%2=0
  · clear h0 h1 h2 h3 h4 h5 h6
    refine ⟨(5*r)+((2*r-2)-x)/2,by omega,by omega,by omega,?_,?_⟩
    all_goals
      dsimp only [owner]
      repeat' first | rw [if_pos (by omega)] | rw [if_neg (by omega)]
      omega
  by_cases h8 : x=2*r-1
  · clear h0 h1 h2 h3 h4 h5 h6 h7
    refine ⟨6*r,by omega,by omega,by omega,?_,?_⟩
    all_goals
      dsimp only [owner]
      repeat' first | rw [if_pos (by omega)] | rw [if_neg (by omega)]
      omega
  omega

/-- Affine run construction for Langford order 4*r+2. -/
theorem affine_two (r : ℕ) (large : 2≤ r) :
    let k := 4*r+2
    ∃ hole, (hole=2*k-1 ∨ hole=2*k) ∧ ∃ owner : ℕ → ℕ,
      ∀ x : ℕ, 1≤x → x≤k → ∃ p : ℕ,
      p+x+1≤2*k ∧ p≠hole ∧ p+x+1≠hole ∧ owner p=x ∧ owner (p+x+1)=x := by
  dsimp only
  let owner (z : ℕ) :=
    if z<(r) then (4*r+1)-2*(z-(0)) else
    if z<(2*r) then (2*r-1)-2*(z-(r)) else
    if z<(2*r+1) then 4*r+2 else
    if z<(3*r+1) then (1)+2*(z-(2*r+1)) else
    if z<(3*r+2) then 2*r else
    if z<(3*r+3) then 4*r else
    if z<(4*r+3) then (2*r+3)+2*(z-(3*r+3)) else
    if z<(5*r+2) then (4*r-2)-2*(z-(4*r+3)) else
    if z<(5*r+3) then 2*r else
    if z<(6*r+2) then (2*r-2)-2*(z-(5*r+3)) else
    if z<(6*r+3) then 2*r+1 else
    if z<(6*r+4) then 4*r+2 else
    if z<(7*r+3) then (2)+2*(z-(6*r+4)) else
    if z<(7*r+4) then 4*r else
    if z<(8*r+3) then (2*r+2)+2*(z-(7*r+4)) else
    if z<(8*r+4) then 0 else
    if z<(8*r+5) then 2*r+1 else
    0
  refine ⟨8*r+3,by omega,owner,?_⟩
  intro x lo hi
  by_cases h0 : (2*r+3)≤x ∧ x≤(4*r+1) ∧ x%2=1
  · refine ⟨(0)+((4*r+1)-x)/2,by omega,by omega,by omega,?_,?_⟩
    all_goals
      dsimp only [owner]
      repeat' first | rw [if_pos (by omega)] | rw [if_neg (by omega)]
      omega
  by_cases h1 : (1)≤x ∧ x≤(2*r-1) ∧ x%2=1
  · clear h0
    refine ⟨(r)+((2*r-1)-x)/2,by omega,by omega,by omega,?_,?_⟩
    all_goals
      dsimp only [owner]
      repeat' first | rw [if_pos (by omega)] | rw [if_neg (by omega)]
      omega
  by_cases h2 : x=4*r+2
  · clear h0 h1
    refine ⟨2*r,by omega,by omega,by omega,?_,?_⟩
    all_goals
      dsimp only [owner]
      repeat' first | rw [if_pos (by omega)] | rw [if_neg (by omega)]
      omega
  by_cases h3 : x=2*r
  · clear h0 h1 h2
    refine ⟨3*r+1,by omega,by omega,by omega,?_,?_⟩
    all_goals
      dsimp only [owner]
      repeat' first | rw [if_pos (by omega)] | rw [if_neg (by omega)]
      omega
  by_cases h4 : x=4*r
  · clear h0 h1 h2 h3
    refine ⟨3*r+2,by omega,by omega,by omega,?_,?_⟩
    all_goals
      dsimp only [owner]
      repeat' first | rw [if_pos (by omega)] | rw [if_neg (by omega)]
      omega
  by_cases h5 : (2*r+2)≤x ∧ x≤(4*r-2) ∧ x%2=0
  · clear h0 h1 h2 h3 h4
    refine ⟨(4*r+3)+((4*r-2)-x)/2,by omega,by omega,by omega,?_,?_⟩
    all_goals
      dsimp only [owner]
      repeat' first | rw [if_pos (by omega)] | rw [if_neg (by omega)]
      omega
  by_cases h6 : (2)≤x ∧ x≤(2*r-2) ∧ x%2=0
  · clear h0 h1 h2 h3 h4 h5
    refine ⟨(5*r+3)+((2*r-2)-x)/2,by omega,by omega,by omega,?_,?_⟩
    all_goals
      dsimp only [owner]
      repeat' first | rw [if_pos (by omega)] | rw [if_neg (by omega)]
      omega
  by_cases h7 : x=2*r+1
  · clear h0 h1 h2 h3 h4 h5 h6
    refine ⟨6*r+2,by omega,by omega,by omega,?_,?_⟩
    all_goals
      dsimp only [owner]
      repeat' first | rw [if_pos (by omega)] | rw [if_neg (by omega)]
      omega
  omega

/-- Affine run construction for Langford order 4*r-1. -/
theorem affine_three (r : ℕ) (large : 2≤ r) :
    let k := 4*r-1
    ∃ hole, (hole=2*k-1 ∨ hole=2*k) ∧ ∃ owner : ℕ → ℕ,
      ∀ x : ℕ, 1≤x → x≤k → ∃ p : ℕ,
      p+x+1≤2*k ∧ p≠hole ∧ p+x+1≠hole ∧ owner p=x ∧ owner (p+x+1)=x := by
  dsimp only
  let owner (z : ℕ) :=
    if z<(r-1) then (4*r-4)-2*(z-(0)) else
    if z<(2*r-2) then (2*r-3)-2*(z-(r-1)) else
    if z<(2*r-1) then 4*r-2 else
    if z<(3*r-2) then (1)+2*(z-(2*r-1)) else
    if z<(3*r-1) then 4*r-1 else
    if z<(4*r-2) then (2*r)+2*(z-(3*r-1)) else
    if z<(4*r-1) then 2*r-1 else
    if z<(5*r-2) then (4*r-3)-2*(z-(4*r-1)) else
    if z<(6*r-3) then (2*r-2)-2*(z-(5*r-2)) else
    if z<(6*r-2) then 4*r-2 else
    if z<(6*r-1) then 2*r-1 else
    if z<(7*r-2) then (2)+2*(z-(6*r-1)) else
    if z<(7*r-1) then 4*r-1 else
    if z<(8*r-2) then (2*r+1)+2*(z-(7*r-1)) else
    0
  refine ⟨8*r-2,by omega,owner,?_⟩
  intro x lo hi
  by_cases h0 : (2*r)≤x ∧ x≤(4*r-4) ∧ x%2=0
  · refine ⟨(0)+((4*r-4)-x)/2,by omega,by omega,by omega,?_,?_⟩
    all_goals
      dsimp only [owner]
      repeat' first | rw [if_pos (by omega)] | rw [if_neg (by omega)]
      omega
  by_cases h1 : (1)≤x ∧ x≤(2*r-3) ∧ x%2=1
  · clear h0
    refine ⟨(r-1)+((2*r-3)-x)/2,by omega,by omega,by omega,?_,?_⟩
    all_goals
      dsimp only [owner]
      repeat' first | rw [if_pos (by omega)] | rw [if_neg (by omega)]
      omega
  by_cases h2 : x=4*r-2
  · clear h0 h1
    refine ⟨2*r-2,by omega,by omega,by omega,?_,?_⟩
    all_goals
      dsimp only [owner]
      repeat' first | rw [if_pos (by omega)] | rw [if_neg (by omega)]
      omega
  by_cases h3 : x=4*r-1
  · clear h0 h1 h2
    refine ⟨3*r-2,by omega,by omega,by omega,?_,?_⟩
    all_goals
      dsimp only [owner]
      repeat' first | rw [if_pos (by omega)] | rw [if_neg (by omega)]
      omega
  by_cases h4 : x=2*r-1
  · clear h0 h1 h2 h3
    refine ⟨4*r-2,by omega,by omega,by omega,?_,?_⟩
    all_goals
      dsimp only [owner]
      repeat' first | rw [if_pos (by omega)] | rw [if_neg (by omega)]
      omega
  by_cases h5 : (2*r+1)≤x ∧ x≤(4*r-3) ∧ x%2=1
  · clear h0 h1 h2 h3 h4
    refine ⟨(4*r-1)+((4*r-3)-x)/2,by omega,by omega,by omega,?_,?_⟩
    all_goals
      dsimp only [owner]
      repeat' first | rw [if_pos (by omega)] | rw [if_neg (by omega)]
      omega
  by_cases h6 : (2)≤x ∧ x≤(2*r-2) ∧ x%2=0
  · clear h0 h1 h2 h3 h4 h5
    refine ⟨(5*r-2)+((2*r-2)-x)/2,by omega,by omega,by omega,?_,?_⟩
    all_goals
      dsimp only [owner]
      repeat' first | rw [if_pos (by omega)] | rw [if_neg (by omega)]
      omega
  omega

/-- Ordinary and hooked Langford pairs at defect two give the required cyclic
difference triples in all four congruence classes. -/
theorem all_differences (k : ℕ) :
    ∃ d : Fin k → Fin 3 → ℕ,
      (∀ i j, 2≤d i j ∧ d i j≤3*k+1) ∧
      Function.Injective (fun z : Fin k × Fin 3 => d z.1 z.2) ∧
      (∀ i, d i 0+d i 1=d i 2 ∨ d i 0+d i 1+d i 2=6*k+3) := by
  by_cases zero : k=0
  · subst k
    exact ⟨fun i => i.elim0,fun i => i.elim0,fun a => a.1.elim0,fun i => i.elim0⟩
  by_cases small : k≤6
  · exact first_six k (by omega) small
  have pairs : ∃ hole, (hole=2*k-1 ∨ hole=2*k) ∧ ∃ owner : ℕ → ℕ,
      ∀ x : ℕ, 1≤x → x≤k → ∃ p : ℕ,
      p+x+1≤2*k ∧ p≠hole ∧ p+x+1≠hole ∧ owner p=x ∧ owner (p+x+1)=x := by
    by_cases z : k%4=0
    · obtain ⟨r,rfl,hr⟩ : ∃ r,k=4*r ∧ 2≤ r := ⟨k/4,by omega,by omega⟩
      exact affine_zero r hr
    by_cases o : k%4=1
    · obtain ⟨r,rfl,hr⟩ : ∃ r,k=4*r+1 ∧ 2≤ r := ⟨k/4,by omega,by omega⟩
      exact affine_one r hr
    by_cases t : k%4=2
    · obtain ⟨r,rfl,hr⟩ : ∃ r,k=4*r+2 ∧ 2≤ r := ⟨k/4,by omega,by omega⟩
      exact affine_two r hr
    obtain ⟨r,rfl,hr⟩ : ∃ r,k=4*r-1 ∧ 2≤ r := ⟨(k+1)/4,by omega,by omega⟩
    exact affine_three r hr
  obtain ⟨hole,endhole,owner,cert⟩ := pairs
  exact position_differences (by omega) hole endhole owner cert

end AlspachLangford

namespace AlspachLangford
open SimpleGraph AlspachConjecture
open scoped Classical

/-- At every order six modulo twelve, any admissible list with exactly two
Hamilton cycles and all other lengths three or four has the required decomposition. -/
theorem two_hamilton_six_mod_twelve (n : ℕ) (residue : n%12=6)
    (I : (completeGraph (Fin n)).Subgraph) (hI : I.IsPerfectMatching)
    (L : Multiset ℕ) (shape : ∀ a∈L,a=3 ∨ a=4 ∨ a=n)
    (budget : L.sum=n.choose 2-n/2) (two : L.count n=2) :
    ∃ C : Multiset (Cycle (completeGraph (Fin n) \ I.spanningCoe)), IsCycleDecomposition _ C ∧ lengths C=L := by
  obtain ⟨k,rfl⟩ : ∃ k,n=2*(6*k+3) := ⟨n/12,by omega⟩
  obtain ⟨d,bounds,distinct,law⟩ := all_differences k
  obtain ⟨B,three,pair,away⟩ := signed_difference_blocks d bounds distinct law
  exact lists_from_inventory (m:=6*k+3) (by omega) B three pair away
    (complete_inventory k B three pair away) I hI L shape budget two

end AlspachLangford

namespace AlspachIterated
open SimpleGraph AlspachConjecture
open scoped Classical

/-- Each unselected Hamilton cycle in the final base is replaced by one
square on each of its edges. This permits every smaller even Hamilton count
when the requested square count covers the unused edges. -/
theorem iterated_subcounts {m r a q : ℕ} (hm : 5≤ m) (even : Even m)
    (seed : ∃ J : (completeGraph (Fin m)).Subgraph, J.IsPerfectMatching ∧
      ∃ C : Multiset (Cycle (completeGraph (Fin m) \ J.spanningCoe)), IsCycleDecomposition _ C ∧
        lengths C=Multiset.replicate r m+Multiset.replicate a 3+Multiset.replicate q 4)
    (e n j : ℕ) (limit : j≤2^e*r) (order : n=2^(e+1)*m) (I : (completeGraph (Fin n)).Subgraph) (hI : I.IsPerfectMatching)
    (L : Multiset ℕ) (shape : ∀ x∈L,x=3 ∨ x=4 ∨ x=n) (budget : L.sum=n.choose 2-n/2)
    (ham : L.count n=2*j)
    (squares : 4^(e+1)*q+(2^(e+1)).choose 2*(m/2)+(2^e*m)*(2^e*r-j)≤L.count 4) :
    ∃ D : Multiset (Cycle (completeGraph (Fin n) \ I.spanningCoe)), IsCycleDecomposition _ D ∧ lengths D=L := by
  classical
  rw [pow_succ',Nat.mul_assoc] at order
  subst n
  obtain ⟨J,hJ,C,dc,sz⟩ := iterated_seed hm even seed e
  have large : 5≤2^e*m := by
    have h := Nat.mul_le_mul_right m (show 1≤2^e from pow_pos (by decide : 0<(2:ℕ)) _)
    omega
  have cr : 2^e*r≤(lengths C).count (2^e*m) := by
    simp [sz,Multiset.count_replicate,show 3≠2^e*m by omega,show 4≠2^e*m by omega]
  have ca : 4^e*a≤(lengths C).count 3 := by simp [sz,Multiset.count_replicate]
  have base := matched_budget large J hJ C dc sz
  rw [square_step even q e] at squares
  have used := congrArg (fun z : ℕ => (2^e*m)*z) (Nat.sub_add_cancel limit)
  have account : (2^e*m)*j+3*(4^e*a)+((2^e*m)/2+4*(4^e*q+(2^e).choose 2*(m/2))+
      (2^e*m)*(2^e*r-j))=(2^e*m).choose 2 := by
    change (2^e*m)*(2^e*r-j+j)=(2^e*m)*(2^e*r) at used
    rw [Nat.mul_add] at used
    omega
  exact double_family (by omega) C dc (limit.trans cr) ca account I hI L shape budget ham squares
/-- Prescribe any smaller even number of spanning cycles after repeated
doubling, with one additional square per dropped base-cycle edge. -/
theorem tripartite_subcounts {t s : ℕ} (odd : Odd t) (large : 3≤t) (lo : 2≤ s) (hi : s≤t)
    (e n j : ℕ) (limit : j≤2^e*(2*s)) (order : n=2^(e+1)*(6*t))
    (I : (completeGraph (Fin n)).Subgraph) (hI : I.IsPerfectMatching)
    (L : Multiset ℕ) (shape : ∀ x∈L,x=3 ∨ x=4 ∨ x=n) (budget : L.sum=n.choose 2-n/2)
    (ham : L.count n=2*j)
    (squares : 4^(e+1)*(3*(t.choose 2%3))+(2^(e+1)).choose 2*(3*t)+
      (2^e*(6*t))*(2^e*(2*s)-j)≤L.count 4) :
    ∃ D : Multiset (Cycle (completeGraph (Fin n) \ I.spanningCoe)), IsCycleDecomposition _ D ∧ lengths D=L := by
  exact iterated_subcounts (m:=6*t) (by omega) (show Even (6*t) from ⟨3*t,by omega⟩)
    (odd_minimum_seed odd large lo hi) e n j limit order I hI L shape budget ham
    (by simpa only [show 6*t/2=3*t by omega] using squares)
/-- Two Hamilton cycles and triangles exhaust the edge budget at every positive
order six modulo twelve. At order six the list consists of the two Hamilton cycles. -/
theorem two_seed {t : ℕ} (odd : Odd t) :
    ∃ J : (completeGraph (Fin (6*t))).Subgraph, J.IsPerfectMatching ∧
      ∃ C : Multiset (Cycle (completeGraph (Fin (6*t)) \ J.spanningCoe)),
        IsCycleDecomposition _ C ∧ lengths C=Multiset.replicate 2 (6*t) +
          Multiset.replicate (6*t*(t-1)) 3 + Multiset.replicate 0 4 := by
  classical
  have positive : 0<t := by obtain ⟨j,hj⟩ := odd; omega
  let L := Multiset.replicate 2 (6*t) + Multiset.replicate (6*t*(t-1)) 3
  have budget : L.sum=(6*t).choose 2-(6*t)/2 := by
    simp only [L,Multiset.sum_add,Multiset.sum_replicate,smul_eq_mul]
    rw [Nat.choose_two_right,show 6*t*(6*t-1)=(3*t*(6*t-1))*2 by ring,
      Nat.mul_div_cancel _ (by decide : 0<2),show 6*t/2=3*t by omega]
    apply Nat.eq_sub_of_add_eq
    rw [show 6*t-1=6*(t-1)+5 by omega]
    ring
  let f : (Fin (3*t) × Bool) ≃ Fin (6*t) := Fintype.equivOfCardEq (by simp; omega)
  obtain ⟨J,perf,_⟩ := AlspachSquares.pair_matching f
  obtain ⟨C,dec,sz⟩ := AlspachLangford.two_hamilton_six_mod_twelve (6*t)
    (by obtain ⟨j,hj⟩ := odd; omega) J perf L (fun x hx => by
      rcases Multiset.mem_add.mp hx with h|h
      · exact Or.inr (Or.inr (Multiset.eq_of_mem_replicate h))
      · exact Or.inl (Multiset.eq_of_mem_replicate h)) budget
    (by simp [L,Multiset.count_replicate,show (3:ℕ)≠6*t by omega])
  exact ⟨J,perf,C,dec,by simpa only [Multiset.replicate_zero,add_zero] using sz⟩

/-- Dropping a Hamilton pair during the final doubling exchanges it for
squares from the edges of its base cycle. -/
theorem two_seed_subcounts {t : ℕ} (odd : Odd t) (e n j : ℕ) (limit : j≤2^(e+1))
    (order : n=2^(e+1)*(6*t)) (I : (completeGraph (Fin n)).Subgraph) (hI : I.IsPerfectMatching)
    (L : Multiset ℕ) (shape : ∀ x∈L,x=3 ∨ x=4 ∨ x=n) (budget : L.sum=n.choose 2-n/2)
    (ham : L.count n=2*j)
    (squares : (2^(e+1)).choose 2*(3*t)+(2^e*(6*t))*(2^(e+1)-j)≤L.count 4) :
    ∃ D : Multiset (Cycle (completeGraph (Fin n) \ I.spanningCoe)), IsCycleDecomposition _ D ∧ lengths D=L := by
  have ht : 0<t := by obtain ⟨a,h⟩ := odd; omega
  apply iterated_subcounts (by omega) ⟨3*t,by omega⟩ (two_seed odd) e n j _ order I hI L shape budget ham
  · simpa only [Nat.mul_zero,Nat.zero_add,show 6*t/2=3*t by omega,←pow_succ] using squares
  · simpa only [←pow_succ] using limit

/-- Keeping every lifted Hamilton cycle leaves one square per pair of copies
of each of the 3t original matching edges. -/
theorem two_seed_doublings {t : ℕ} (odd : Odd t) (e n : ℕ)
    (order : n=2^(e+1)*(6*t)) (I : (completeGraph (Fin n)).Subgraph) (hI : I.IsPerfectMatching)
    (L : Multiset ℕ) (shape : ∀ x∈L,x=3 ∨ x=4 ∨ x=n) (budget : L.sum=n.choose 2-n/2)
    (ham : L.count n=2^(e+2)) (squares : (2^(e+1)).choose 2*(3*t)≤L.count 4) :
    ∃ D : Multiset (Cycle (completeGraph (Fin n) \ I.spanningCoe)), IsCycleDecomposition _ D ∧ lengths D=L := by
  apply two_seed_subcounts odd e n (2^(e+1)) le_rfl order I hI L shape budget
  · simpa only [pow_succ' 2 (e+1)] using ham
  · simpa using squares

end AlspachIterated

namespace AlspachAvoid
open Finset

/-- Removing a forbidden set from a pairwise disjoint indexed family loses
at most one index per forbidden element. -/
theorem avoid_edges {E : Type*} {a b : ℕ} (T : Fin (a+b) → Finset E)
    (pair : Pairwise fun i j => Disjoint (T i) (T j))
    (S : Finset E) (small : S.card≤b) :
    ∃ f : Fin a ↪ Fin (a+b), ∀ i, Disjoint (T (f i)) S := by
  classical
  let ok (i : Fin (a+b)) := Disjoint (T i) S
  let good := univ.filter ok
  let bad := univ.filter fun i => ¬ok i
  have witness (i : bad) : ∃ x : S, x.val∈T i.val := by
    have hit := (mem_filter.mp i.property).2
    obtain ⟨e,ei,es⟩ := Finset.not_disjoint_iff.mp hit
    exact ⟨⟨e,es⟩,ei⟩
  choose mark used using witness
  have inj : Function.Injective mark := by
    intro i j same
    apply Subtype.ext
    by_contra ne
    have left := used i
    rw [same] at left
    exact Finset.disjoint_left.mp (pair ne) left (used j)
  have lost : bad.card≤S.card := by
    simpa using Fintype.card_le_of_injective mark inj
  have total : good.card+bad.card=a+b := by
    simpa only [good,bad,card_univ,Fintype.card_fin] using
      (Finset.card_filter_add_card_filter_not (s:=univ) ok)
  have enough : a≤good.card := by omega
  let index := (Fintype.equivFinOfCardEq (Fintype.card_coe good)).symm
  let f : Fin a ↪ Fin (a+b) := (Fin.castLEEmb enough).trans (index.toEmbedding.trans (Function.Embedding.subtype _))
  exact ⟨f,fun i => (mem_filter.mp ((index (Fin.castLE enough i)).property)).2⟩

end AlspachAvoid

namespace AlspachAvoid
open Finset SimpleGraph
open scoped Classical

/-- Choose edge-disjoint Hamilton rings and reserve k edge-disjoint triangles
avoiding the rings, allowing one discarded triangle for each ring edge. -/
theorem avoiding_packing {m r k : ℕ} (large : 3≤ m) (limit : r≤(m-1)/2) :
    let leave := if m%6=1 ∨ m%6=3 then 0 else if m%6=0 ∨ m%6=2 then m/2 else m-1
    k+m*r≤(m.choose 2-leave)/3 →
    let next (i : Fin m) : Fin m := ⟨(i.val+1)%m,Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩
    ∃ (σ : Fin r → (Fin m ≃ Fin m)) (B : Fin k → Finset (Fin m)),
      let H (i : Fin r) := univ.image fun z => s(σ i z,σ i (next z))
      let T (i : Fin k) := (⊤ : SimpleGraph (Fin m)).edgeFinset.filter fun e => e.toFinset ⊆ B i
      (∀ i,(B i).card=3) ∧ Pairwise (fun i j => Disjoint (H i) (H j)) ∧
      Pairwise (fun i j => Disjoint (T i) (T j)) ∧ Disjoint (univ.biUnion H) (univ.biUnion T) := by
  classical
  intro leave cap next
  let supp (B : Finset (Fin m)) := (⊤ : SimpleGraph (Fin m)).edgeFinset.filter fun e => e.toFinset ⊆ B
  have packed : ∃ A : Fin (k+m*r) → Finset (Fin m), (∀ i,(A i).card=3) ∧
      Pairwise (fun i j => Disjoint (supp (A i)) (supp (A j))) := by
    by_cases full : m%6=1 ∨ m%6=3
    · exact AlspachTrades.triangle_packing m _ full (by simpa [leave,full] using cap)
    by_cases even : m%6=0 ∨ m%6=2
    · exact AlspachTrades.triangle_packing_even m _ even (by simpa [leave,full,even] using cap)
    have bound : k+m*r≤(m.choose 2-(m-1))/3 := by simpa [leave,full,even] using cap
    by_cases four : m%6=4
    · exact AlspachTrades.triangle_packing_four four bound
    · exact AlspachTrades.triangle_packing_five m _ (by omega) bound
  obtain ⟨A,three,apart⟩ := packed
  obtain ⟨σ,_,card,pair⟩ := AlspachPaired.packed_base_family_of_limit large limit
  let H (i : Fin r) := univ.image fun z => s(σ i z,σ i (next z))
  have sizeH (i : Fin r) : (H i).card=m := card i
  have disj : ((univ : Finset (Fin r)) : Set _).PairwiseDisjoint H := fun _ _ _ _ ne => pair ne
  have total : (univ.biUnion H).card=m*r := by
    rw [card_biUnion disj]
    simp only [sizeH,sum_const,card_univ,Fintype.card_fin,smul_eq_mul,Nat.mul_comm r m]
  obtain ⟨f,free⟩ := avoid_edges (fun i => supp (A i)) apart (univ.biUnion H) total.le
  refine ⟨σ,fun i => A (f i),fun i => three _,pair,fun _ _ ne => apart (f.injective.ne ne),?_⟩
  apply Finset.disjoint_left.mpr
  intro e fromRing fromTriangle
  obtain ⟨i,_,used⟩ := mem_biUnion.mp fromTriangle
  exact Finset.disjoint_left.mp (free i) used fromRing

end AlspachAvoid

namespace AlspachAvoid

theorem counts_for_packing {m r : ℕ} (hm : 3≤ m) (L : Multiset ℕ)
    (shape : ∀ x∈L,x=3 ∨ x=4 ∨ x=2*m) (budget : L.sum=(2*m).choose 2-(2*m)/2)
    (ham : L.count (2*m)=2*r) :
    ∃ k, r≤(m-1)/2 ∧ m*r+3*k+L.count 4=m.choose 2 ∧
      L=Multiset.replicate (2*r) (2*m)+Multiset.replicate (4*k) 3+Multiset.replicate (L.count 4) 4 := by
  have n3 : 2*m≠3 := by omega
  have n4 : 2*m≠4 := by omega
  have split : L=Multiset.replicate (2*r) (2*m)+Multiset.replicate (L.count 3) 3+
      Multiset.replicate (L.count 4) 4 := by
    ext x
    rcases eq_or_ne x (2*m) with rfl|hn
    · simp [Multiset.count_replicate,ham,Ne.symm n3,Ne.symm n4]
    rcases eq_or_ne x 3 with rfl|h₃
    · simp [Multiset.count_replicate,n3]
    rcases eq_or_ne x 4 with rfl|h₄
    · simp [Multiset.count_replicate,n4]
    have none : x∉L := fun h => (shape x h).elim h₃ (fun e => e.elim h₄ hn)
    simp [Multiset.count_replicate,Multiset.count_eq_zero.mpr none,Ne.symm h₃,Ne.symm h₄,Ne.symm hn]
  have eq := congrArg Multiset.sum split
  rw [budget,AlspachPaired.paired_budget m (by omega)] at eq
  simp only [Multiset.sum_add,Multiset.sum_replicate,smul_eq_mul] at eq
  have equation : 3*L.count 3+4*L.count 4+4*(m*r)=4*m.choose 2 := by nlinarith only [eq]
  let k := L.count 3/4
  have triangles : L.count 3=4*k := by dsimp [k]; omega
  have twice : 2*m.choose 2=m*(m-1) := by
    obtain ⟨z,rfl⟩ : ∃ z, m=z+1 := ⟨m-1,by omega⟩
    simpa [Nat.mul_comm] using (Nat.add_one_mul_choose_eq z 1).symm
  have limit : m*(2*r)≤ m*(m-1) := by nlinarith only [twice,equation]
  have le : 2*r≤ m-1 := Nat.le_of_mul_le_mul_left limit (by omega)
  exact ⟨k,by omega,by omega,by rwa [triangles] at split⟩

end AlspachAvoid

namespace AlspachAvoid
open SimpleGraph AlspachConjecture
open scoped Classical

/-- Avoid all edges of the selected Walecki cycles in a large base triangle
packing. Each removed base triangle contributes at most two additional squares
for each forbidden edge. -/
theorem square_rich_every_even {m r : ℕ} (hm : 3≤ m)
    (I : (completeGraph (Fin (2*m))).Subgraph) (hI : I.IsPerfectMatching) (L : Multiset ℕ)
    (shape : ∀ x∈L,x=3 ∨ x=4 ∨ x=2*m) (budget : L.sum=(2*m).choose 2-(2*m)/2)
    (ham : L.count (2*m)=2*r)
    (squares : (if m%6=1 ∨ m%6=3 then 0 else if m%6=0 ∨ m%6=2 then m/2 else m-1)+2*(m*r)≤L.count 4) :
    ∃ C : Multiset (Cycle (completeGraph (Fin (2*m)) \ I.spanningCoe)), IsCycleDecomposition _ C ∧ lengths C=L := by
  classical
  let leave := if m%6=1 ∨ m%6=3 then 0 else if m%6=0 ∨ m%6=2 then m/2 else m-1
  change leave+2*(m*r)≤L.count 4 at squares
  obtain ⟨k,limit,total,eq⟩ := counts_for_packing hm L shape budget ham
  have cap : k+m*r≤(m.choose 2-leave)/3 := by omega
  obtain ⟨σ,B,three,hs,ts,dj⟩ := avoiding_packing hm limit cap
  obtain ⟨J,hJ,q,D,dc,lens,count⟩ := AlspachTriangleHamilton.double_partial hm σ B three hs ts dj
  obtain ⟨iso⟩ := OMA.R_AlspachConjecture_alspach_conjecture_variants_even_R2.matchings_complements_iso J I hJ hI
  exact OMA.R_AlspachConjecture_alspach_conjecture_variants_even_R2.iso_decomposition iso dc
    (by rw [lens,eq,show q=L.count 4 by omega])
theorem all_orders_above_leave (n : ℕ) (even : Even n) (large : 6≤n)
    (I : (completeGraph (Fin n)).Subgraph) (hI : I.IsPerfectMatching) (L : Multiset ℕ)
    (shape : ∀ x∈L,x=3 ∨ x=4 ∨ x=n) (budget : L.sum=n.choose 2-n/2) (ham : Even (L.count n))
    (squares : (if (n/2)%6=1 ∨ (n/2)%6=3 then 0 else if (n/2)%6=0 ∨ (n/2)%6=2 then (n/2)/2 else n/2-1)+
      n/2*(L.count n)≤L.count 4) :
    ∃ C : Multiset (Cycle (completeGraph (Fin n) \ I.spanningCoe)), IsCycleDecomposition _ C ∧ lengths C=L := by
  obtain ⟨m,rfl⟩ : ∃ m,n=2*m := by obtain ⟨m,h⟩ := even; exact ⟨m,by omega⟩
  obtain ⟨r,hr⟩ : ∃ r,L.count (2*m)=2*r := by obtain ⟨r,h⟩ := ham; exact ⟨r,by omega⟩
  rw [show (2*m)/2=m by omega,hr,show m*(2*r)=2*(m*r) by ring] at squares
  exact square_rich_every_even (by omega) I hI L shape budget hr squares
end AlspachAvoid

namespace AlspachLangford
open Finset SimpleGraph AlspachConjecture
open scoped Classical

/-- From disjoint base Hamilton cycles and triangle supports, realize every
mixed doubled list whose square count covers all the unused base edges. -/
theorem partial_lists {m r : ℕ} (hm : 3≤ m) {A : Type} [Fintype A] [DecidableEq A]
    (σ : Fin r → (Fin m ≃ Fin m)) (B : A → Finset (Fin m)) (three : ∀ i,(B i).card=3) :
    let next (i : Fin m) : Fin m := ⟨(i.val+1)%m,Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩
    let H (i : Fin r) := univ.image fun z => s(σ i z,σ i (next z))
    let T (i : A) := (⊤ : SimpleGraph (Fin m)).edgeFinset.filter fun e => e.toFinset ⊆ B i
    Pairwise (fun i j => Disjoint (H i) (H j)) → Pairwise (fun i j => Disjoint (T i) (T j)) →
    Disjoint (univ.biUnion H) (univ.biUnion T) →
    ∀ (I : (completeGraph (Fin (2*m))).Subgraph), I.IsPerfectMatching → ∀ L : Multiset ℕ,
      (∀ a∈L,a=3 ∨ a=4 ∨ a=2*m) → L.sum=(2*m).choose 2-(2*m)/2 → L.count (2*m)=2*r →
      m.choose 2-m*r-3*Fintype.card A≤L.count 4 →
      ∃ C : Multiset (Cycle (completeGraph (Fin (2*m)) \ I.spanningCoe)), IsCycleDecomposition _ C ∧ lengths C=L := by
  classical
  intro next H T hs ts sep I hi L shape budget ham squares
  let index := (Fintype.equivFin A).symm
  have build (k : ℕ) (hk : k≤Fintype.card A) :
      ∃ J : (completeGraph (Fin (2*m))).Subgraph, J.IsPerfectMatching ∧
        ∃ (q : ℕ) (C : Multiset (Cycle (completeGraph (Fin (2*m)) \ J.spanningCoe))),
          IsCycleDecomposition _ C ∧ lengths C=Multiset.replicate (2*r) (2*m) + Multiset.replicate (4*k) 3 +
            Multiset.replicate q 4 ∧ q+m*r+3*k=m.choose 2 := by
    let f (i : Fin k) := index (i.castLE hk)
    have inj : Function.Injective f := fun _ _ eq => Fin.ext (congrArg (fun v : Fin (Fintype.card A) => v.val) (index.injective eq))
    apply AlspachTriangleHamilton.double_partial hm σ (fun i => B (f i)) (fun i => three _) hs
    · exact fun i j ne => ts (inj.ne ne)
    · apply Finset.disjoint_left.mpr
      intro edge hh chosen
      obtain ⟨i,_,hit⟩ := mem_biUnion.mp chosen
      exact Finset.disjoint_left.mp sep hh (mem_biUnion.mpr ⟨f i,mem_univ _,hit⟩)
  obtain ⟨_,_,u,_,_,_,eq⟩ := build (Fintype.card A) le_rfl
  have base : m*r+3*Fintype.card A+u=m.choose 2 := by omega
  have lower : u≤L.count 4 := by omega
  obtain ⟨k,hk,list⟩ := AlspachIterated.classify_leave hm base L shape budget ham lower
  obtain ⟨J,hJ,q,C,dec,len,size⟩ := build k hk
  obtain ⟨iso⟩ := OMA.R_AlspachConjecture_alspach_conjecture_variants_even_R2.matchings_complements_iso J I hJ hi
  apply OMA.R_AlspachConjecture_alspach_conjecture_variants_even_R2.iso_decomposition iso dec
  rw [len,list,show q=u+3*(Fintype.card A-k) by omega]

/-- For the identity cyclic listing, two Hamilton cycles can be retained and
every unused triangle support contributes three squares. -/
theorem lists_from_partial_inventory {m : ℕ} (hm : 3≤ m) {A : Type} [Fintype A] [DecidableEq A]
    (B : A → Finset (Fin m)) (three : ∀ i,(B i).card=3) :
    let next (i : Fin m) : Fin m := ⟨(i.val+1)%m,Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩
    let H := univ.image fun z => s(z,next z)
    let T (i : A) := (⊤ : SimpleGraph (Fin m)).edgeFinset.filter fun e => e.toFinset ⊆ B i
    Pairwise (fun i j => Disjoint (T i) (T j)) → (∀ i,Disjoint H (T i)) →
    ∀ (I : (completeGraph (Fin (2*m))).Subgraph), I.IsPerfectMatching → ∀ L : Multiset ℕ,
      (∀ a∈L,a=3 ∨ a=4 ∨ a=2*m) → L.sum=(2*m).choose 2-(2*m)/2 → L.count (2*m)=2 →
      m.choose 2-m-3*Fintype.card A≤L.count 4 →
      ∃ C : Multiset (Cycle (completeGraph (Fin (2*m)) \ I.spanningCoe)), IsCycleDecomposition _ C ∧ lengths C=L := by
  classical
  intro next H T ts sep I hi L shape budget ham squares
  let σ (_ : Fin 1) := Equiv.refl (Fin m)
  have hs : Pairwise (fun _ _ : Fin 1 => Disjoint H H) := fun i j ne => False.elim (ne (Subsingleton.elim i j))
  apply partial_lists hm σ B three hs ts _ I hi L shape budget ham (by simpa using squares)
  apply Finset.disjoint_left.mpr
  intro edge hh ht
  obtain ⟨_,_,a⟩ := mem_biUnion.mp hh
  obtain ⟨i,_,b⟩ := mem_biUnion.mp ht
  exact Finset.disjoint_left.mp (sep i) a b

/-- Enlarging the standard cyclic ordering preserves every old triangle
whose edges avoid the smaller ordering. -/
theorem stretch_inventory {v m : ℕ} (le : v≤ m) {A : Type}
    (B : A → Finset (Fin v)) (three : ∀ i,(B i).card=3) :
    let next {n : ℕ} (i : Fin n) : Fin n := ⟨(i.val+1)%n,Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩
    let H (n : ℕ) := univ.image fun z : Fin n => s(z,next z)
    let T {n : ℕ} (F : Finset (Fin n)) := (⊤ : SimpleGraph (Fin n)).edgeFinset.filter fun e => e.toFinset⊆F
    Pairwise (fun i j => Disjoint (T (B i)) (T (B j))) → (∀ i,Disjoint (H v) (T (B i))) →
    ∃ P : A → Finset (Fin m), (∀ i,(P i).card=3) ∧
      Pairwise (fun i j => Disjoint (T (P i)) (T (P j))) ∧ (∀ i,Disjoint (H m) (T (P i))) := by
  intro next H T pair avoid
  let f : Fin v ↪ Fin m := ⟨fun x => ⟨x.val,lt_of_lt_of_le x.isLt le⟩,
    fun _ _ h => Fin.ext (congrArg (Fin.val : Fin m→ℕ) h)⟩
  let P (i : A) := (B i).map f
  have step (x y : Fin v) (h : next (f x)=f y) : next x=y := by
    apply Fin.ext
    have eq := congrArg Fin.val h
    change (x.val+1)%m=y.val at eq
    change (x.val+1)%v=y.val
    have hx := x.isLt
    have hy := y.isLt
    by_cases last : x.val+1=m
    · have vm : v=m := by omega
      simpa only [vm] using eq
    · rw [Nat.mod_eq_of_lt (by omega)] at eq
      rw [Nat.mod_eq_of_lt (by omega),eq]
  have pull (x y : Fin v) (h : s(f x,f y)∈H m) : s(x,y)∈H v := by
    obtain ⟨z,_,eq⟩ := mem_image.mp h
    rcases Sym2.eq_iff.mp eq with ⟨rfl,hy⟩|⟨rfl,hx⟩
    · exact mem_image.mpr ⟨x,mem_univ _,by rw [step _ _ hy]⟩
    · exact mem_image.mpr ⟨y,mem_univ _,by rw [step _ _ hx,Sym2.eq_swap]⟩
  have edge {n : ℕ} (S : Finset (Fin n)) (x y : Fin n) :
      s(x,y)∈T S ↔ x≠y ∧ x∈S ∧ y∈S := by
    simp [T,Finset.insert_subset_iff,Sym2.toFinset_mk_eq]
  have image_edge (i : A) (x y : Fin v) : s(f x,f y)∈T (P i) ↔ s(x,y)∈T (B i) := by
    simp [edge,P]
  have endpoints (i : A) (x y : Fin m) (h : s(x,y)∈T (P i)) :
      ∃ a b : Fin v,x=f a ∧ y=f b := by
    obtain ⟨_,hx,hy⟩ := (edge _ _ _).mp h
    obtain ⟨a,_,rfl⟩ := mem_map.mp hx
    obtain ⟨b,_,rfl⟩ := mem_map.mp hy
    exact ⟨a,b,rfl,rfl⟩
  refine ⟨P,fun i => by simpa [P] using three i,?_,?_⟩
  · intro i j diff
    apply Finset.disjoint_left.mpr
    intro e
    induction e using Sym2.ind with
    | _ x y =>
      intro hi hj
      obtain ⟨a,b,rfl,rfl⟩ := endpoints _ _ _ hi
      exact Finset.disjoint_left.mp (pair diff) ((image_edge i a b).mp hi) ((image_edge j a b).mp hj)
  · intro i
    apply Finset.disjoint_left.mpr
    intro e
    induction e using Sym2.ind with
    | _ x y =>
      intro ring block
      obtain ⟨a,b,rfl,rfl⟩ := endpoints _ _ _ block
      exact Finset.disjoint_left.mp (avoid i) (pull a b ring) ((image_edge i a b).mp block)

/-- Prescribe exactly two Hamilton cycles at any even order by embedding a
cyclic difference design on its largest suborder congruent to three modulo six. -/
theorem two_hamilton_suborder (m : ℕ) (hm : 3≤ m)
    (I : (completeGraph (Fin (2*m))).Subgraph) (hI : I.IsPerfectMatching)
    (L : Multiset ℕ) (shape : ∀ a∈L,a=3 ∨ a=4 ∨ a=2*m)
    (budget : L.sum=(2*m).choose 2-(2*m)/2) (two : L.count (2*m)=2) :
    let k := (m-3)/6
    let v := 6*k+3
    m.choose 2-m-3*(k*v)≤L.count 4 →
    ∃ C : Multiset (Cycle (completeGraph (Fin (2*m)) \ I.spanningCoe)), IsCycleDecomposition _ C ∧ lengths C=L := by
  intro k v squares
  have le : v≤ m := by dsimp [v,k]; omega
  obtain ⟨d,bounds,distinct,law⟩ := all_differences k
  obtain ⟨B,three,pair,away⟩ := signed_difference_blocks d bounds distinct law
  obtain ⟨F,sz,df,sf⟩ := stretch_inventory (v:=v) le B three pair away
  apply lists_from_partial_inventory hm F sz df sf I hI L shape budget two
  simpa only [Fintype.card_prod,Fintype.card_fin] using squares

/-- If e vertices extend the suborder, the minimum required square count is
e times the sum of the two orders minus three, divided by two. -/
theorem suborder_square_threshold (m : ℕ) (hm : 3≤ m) :
    let k := (m-3)/6
    let v := 6*k+3
    let q := m.choose 2-m-3*(k*v)
    2*q=(m-v)*(m+v-3) ∧ q≤5*m := by
  intro k v q
  have low : 3≤v := by dsimp [v]; omega
  have le : v≤ m := by dsimp [v,k]; omega
  have close : m-v≤5 := by dsimp [v,k]; omega
  have pair : 2*m.choose 2=m*(m-1) := by
    obtain ⟨j,h⟩ : ∃ j,m=j+1 := ⟨m-1,by omega⟩
    rw [h]
    simpa [Nat.mul_comm] using (Nat.add_one_mul_choose_eq j 1).symm
  have split := Nat.sub_add_cancel le
  let e := m-v
  have ev : e+v=m := split
  have div : 2*m.choose 2 = 2*(m+3*(k*v)) + e*(m+v-3) := by
    have a := Nat.sub_add_cancel (show 1≤ m by omega)
    have b := Nat.sub_add_cancel (show 3≤ m+v by omega)
    rw [pair]
    dsimp [v] at ev b ⊢
    nlinarith only [congrArg (m*·) a,congrArg (e*·) b,
      congrArg (m*·) ev,congrArg ((6*k+3)*·) ev]
  have eq : 2*q=e*(m+v-3) := by dsimp [q]; omega
  refine ⟨eq,?_⟩
  have bound : e*(m+v-3) ≤ 5*(2*m) := Nat.mul_le_mul close (by omega)
  omega

end AlspachLangford

namespace AlspachLangford
open SimpleGraph AlspachConjecture
open scoped Classical

theorem suborder_even (n : ℕ) (even : Even n) (large : 6≤n)
    (I : (completeGraph (Fin n)).Subgraph) (hI : I.IsPerfectMatching) (L : Multiset ℕ)
    (shape : ∀ a∈L,a=3 ∨ a=4 ∨ a=n) (budget : L.sum=n.choose 2-n/2) (two : L.count n=2) :
    let m := n/2
    let k := (m-3)/6
    m.choose 2-m-3*(k*(6*k+3))≤L.count 4 →
    ∃ C : Multiset (Cycle (completeGraph (Fin n) \ I.spanningCoe)), IsCycleDecomposition _ C ∧ lengths C=L := by
  obtain ⟨m,rfl⟩ : ∃ m,n=2*m := by obtain ⟨m,h⟩ := even; exact ⟨m,by omega⟩
  simpa only [show 2*m/2=m by omega] using two_hamilton_suborder m (by omega) I hI L shape budget two

end AlspachLangford

namespace AlspachAvoid
open Finset SimpleGraph
open scoped Classical

/-- Reserve the canonical cyclic order along with the selected Hamilton cycles.
At most one triangle in the packing is lost for each edge of these cycles. -/
theorem off_path_packing {m r k : ℕ} (even : Even m) (large : 4≤ m) (limit : r≤ m/2-2) :
    let leave := if m%6=1 ∨ m%6=3 then 0 else if m%6=0 ∨ m%6=2 then m/2 else m-1
    k+m*(r+1)≤(m.choose 2-leave)/3 →
    let next (i : Fin m) : Fin m := ⟨(i.val+1)%m,Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩
    let R := univ.image fun z => s(z,next z)
    ∃ (σ : Fin r → (Fin m ≃ Fin m)) (B : Fin k → Finset (Fin m)),
      let H (i : Fin r) := univ.image fun z => s(σ i z,σ i (next z))
      let T (i : Fin k) := (⊤ : SimpleGraph (Fin m)).edgeFinset.filter fun e => e.toFinset ⊆ B i
      (∀ i,(B i).card=3) ∧ Pairwise (fun i j => Disjoint (H i) (H j)) ∧
      (∀ i, Disjoint (H i) R) ∧ Pairwise (fun i j => Disjoint (T i) (T j)) ∧
      Disjoint (univ.biUnion T) (univ.biUnion H ∪ R) := by
  classical
  intro leave cap next R
  let supp (B : Finset (Fin m)) := (⊤ : SimpleGraph (Fin m)).edgeFinset.filter fun e => e.toFinset ⊆ B
  have packed : ∃ A : Fin (k+m*(r+1)) → Finset (Fin m), (∀ i,(A i).card=3) ∧
      Pairwise (fun i j => Disjoint (supp (A i)) (supp (A j))) := by
    by_cases full : m%6=1 ∨ m%6=3
    · exact AlspachTrades.triangle_packing m _ full (by simpa [leave,full] using cap)
    by_cases matched : m%6=0 ∨ m%6=2
    · exact AlspachTrades.triangle_packing_even m _ matched (by simpa [leave,full,matched] using cap)
    have bound : k+m*(r+1)≤(m.choose 2-(m-1))/3 := by simpa [leave,full,matched] using cap
    by_cases four : m%6=4
    · exact AlspachTrades.triangle_packing_four four bound
    · exact AlspachTrades.triangle_packing_five m _ (by omega) bound
  obtain ⟨A,three,apart⟩ := packed
  obtain ⟨σ,_,card,pair,reserve⟩ := AlspachPaired.path_avoiding_family even large limit
  let H (i : Fin r) := univ.image fun z => s(σ i z,σ i (next z))
  have sizeH (i : Fin r) : (H i).card=m := card i
  have disj : ((univ : Finset (Fin r)) : Set _).PairwiseDisjoint H := fun _ _ _ _ ne => pair ne
  have total : (univ.biUnion H).card=m*r := by
    rw [card_biUnion disj]
    simp only [sizeH,sum_const,card_univ,Fintype.card_fin,smul_eq_mul,Nat.mul_comm r m]
  have ring : R.card≤ m := calc
    _ ≤ (univ : Finset (Fin m)).card := card_image_le
    _ = m := by simp
  have capacity : (univ.biUnion H ∪ R).card≤ m*(r+1) := calc
    _ ≤ (univ.biUnion H).card+R.card := card_union_le ..
    _ ≤ m*r+m := by omega
    _ = _ := (Nat.mul_succ m r).symm
  obtain ⟨f,free⟩ := avoid_edges (fun i => supp (A i)) apart (univ.biUnion H ∪ R) capacity
  refine ⟨σ,fun i => A (f i),fun i => three _,pair,reserve,fun _ _ ne => apart (f.injective.ne ne),?_⟩
  apply Finset.disjoint_left.mpr
  intro e fromTriangle forbidden
  obtain ⟨i,_,used⟩ := mem_biUnion.mp fromTriangle
  exact Finset.disjoint_left.mp (free i) used forbidden

/-- Choose triangles avoiding the reserved ring first. Each triangle then
excludes at most three cycles in an edge-disjoint Hamilton family. -/
theorem off_path_packing_reverse {m r k : ℕ} (even : Even m) (large : 4≤ m) :
    let leave := if m%6=1 ∨ m%6=3 then 0 else if m%6=0 ∨ m%6=2 then m/2 else m-1
    (k+m≤(m.choose 2-leave)/3 ∧ r+3*k≤ m/2-2) →
    let next (i : Fin m) : Fin m := ⟨(i.val+1)%m,Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩
    let R := univ.image fun z => s(z,next z)
    ∃ (σ : Fin r → (Fin m ≃ Fin m)) (B : Fin k → Finset (Fin m)),
      let H (i : Fin r) := univ.image fun z => s(σ i z,σ i (next z))
      let T (i : Fin k) := (⊤ : SimpleGraph (Fin m)).edgeFinset.filter fun e => e.toFinset ⊆ B i
      (∀ i,(B i).card=3) ∧ Pairwise (fun i j => Disjoint (H i) (H j)) ∧
      (∀ i, Disjoint (H i) R) ∧ Pairwise (fun i j => Disjoint (T i) (T j)) ∧
      Disjoint (univ.biUnion T) (univ.biUnion H ∪ R) := by
  classical
  intro leave cap next R
  obtain ⟨_,B,three,_,_,apart,away⟩ := off_path_packing (r:=0) (k:=k) even large (by omega) (by simpa using cap.1)
  let T (i : Fin k) := (⊤ : SimpleGraph (Fin m)).edgeFinset.filter fun e => e.toFinset ⊆ B i
  have sizeT (i : Fin k) : (T i).card=3 := by
    obtain ⟨a,b,c,ab,ac,bc,eq⟩ := card_eq_three.mp (three i)
    have support : T i={s(a,b),s(a,c),s(b,c)} := by
      ext e
      induction e using Sym2.ind with
      | _ x y =>
        simp only [T,eq,mem_filter,SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet,
          SimpleGraph.top_adj,Sym2.toFinset_mk_eq,insert_subset_iff,singleton_subset_iff,
          mem_insert,mem_singleton,Sym2.eq_iff]
        grind
    rw [support]
    simp [ab,ac,bc,Ne.symm ab,Ne.symm bc]
  let U := univ.biUnion T
  have size : U.card≤3*k := calc
    _ ≤ ∑ i : Fin k, (T i).card := Finset.card_biUnion_le
    _ = _ := by simp [sizeT,Nat.mul_comm]
  obtain ⟨σ,_,_,pair,ring⟩ := AlspachPaired.path_avoiding_family even large cap.2
  let H (i : Fin (r+3*k)) := univ.image fun z => s(σ i z,σ i (next z))
  obtain ⟨f,free⟩ := avoid_edges H pair U size
  refine ⟨fun i => σ (f i),B,three,fun _ _ ne => pair (f.injective.ne ne),fun i => ring (f i),apart,?_⟩
  apply Finset.disjoint_left.mpr
  intro edge selected prohibited
  rcases mem_union.mp prohibited with path|reserved
  · obtain ⟨i,_,used⟩ := mem_biUnion.mp path
    exact Finset.disjoint_left.mp (free i) used selected
  · exact Finset.disjoint_left.mp away selected (mem_union_right _ reserved)

end AlspachAvoid

namespace AlspachLadder
open Finset SimpleGraph AlspachConjecture
open scoped Classical

/-- Lift selected Hamilton orders and triangles off the ladder. Use a square on
each remaining pair of nonconsecutive rows. -/
theorem off_path_trades {m n r k : ℕ} (large : 3 ≤ m) (f : (Fin m × Bool) ≃ Fin n)
    (G : SimpleGraph (Fin n)) (σ : Fin r → (Fin m ≃ Fin m))
    (B : Fin k → Finset (Fin m)) (three : ∀ i,(B i).card=3) :
    let next (a : Fin m) : Fin m := ⟨(a.val+1)%m, Nat.mod_lt _ (Nat.zero_lt_of_lt a.isLt)⟩
    let support (p : Fin m ≃ Fin m) := univ.image (fun a => s(p a,p (next a)))
    let T (i : Fin k) := (⊤ : SimpleGraph (Fin m)).edgeFinset.filter fun e => e.toFinset ⊆ B i
    (Pairwise fun i j => Disjoint (support (σ i)) (support (σ j))) →
    (∀ i, Disjoint (support (σ i)) (support (Equiv.refl _))) →
    (Pairwise fun i j => Disjoint (T i) (T j)) →
    Disjoint (univ.biUnion T) (univ.biUnion (fun i => support (σ i)) ∪ support (Equiv.refl _)) →
    (∀ (i j : Fin m), i≠j → i.val+1≠j.val → j.val+1≠i.val →
      ∀ a b, G.Adj (f (i,a)) (f (j,b))) →
    ∃ (q : ℕ) (cs : Multiset (Cycle G)),
      lengths cs = Multiset.replicate (2*r) (2*m) + Multiset.replicate (4*k) 3 + Multiset.replicate q 4 ∧
      ∀ (i : Fin m) (a : Bool) (j : Fin m) (b : Bool),
        (cs.filter fun c => s(f (i,a),f (j,b)) ∈ c.edges).card =
        if i=j ∨ i.val+1=j.val ∨ j.val+1=i.val then 0 else 1 := by
  intro next support T disj avoid ts sep across
  let π := fun x : Fin n => (f.symm x).1
  let Covers (S : Finset (Sym2 (Fin m))) (L : Multiset ℕ) : Prop :=
    ∃ C : Multiset (Cycle G), lengths C = L ∧ ∀ x y : Fin n,
      (C.filter fun c => s(x,y) ∈ c.edges).card = if s(π x,π y) ∈ S then 1 else 0
  obtain ⟨covers_union,covers_many⟩ := AlspachRegions.collect G π
  let A := (⊤ : SimpleGraph (Fin m)).edgeFinset.filter (fun e =>
    ¬∃ i j : Fin m, i.val+1=j.val ∧ e=s(i,j))
  have mem (i j : Fin m) : s(i,j) ∈ A ↔ i≠j ∧ i.val+1≠j.val ∧ j.val+1≠i.val := by
    rw [show A=(⊤ : SimpleGraph (Fin m)).edgeFinset.filter _ by rfl,mem_filter]
    have inBase : s(i,j) ∈ (⊤ : SimpleGraph (Fin m)).edgeFinset ↔ i≠j := SimpleGraph.mem_edgeFinset
    rw [inBase]
    constructor
    · rintro ⟨ne,none⟩
      exact ⟨ne,fun h => none ⟨i,j,h,rfl⟩,fun h => none ⟨j,i,h,Sym2.eq_swap⟩⟩
    · rintro ⟨ne,fwd,bwd⟩
      refine ⟨ne,?_⟩
      rintro ⟨u,v,step,eq⟩
      rcases Sym2.eq_iff.mp eq with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
      · exact fwd step
      · exact bwd step
  have sub (t : Fin r) : support (σ t) ⊆ A := by
    intro e he
    apply mem_filter.mpr
    constructor
    · obtain ⟨v,_,rfl⟩ := mem_image.mp he
      apply SimpleGraph.mem_edgeFinset.mpr
      intro eq
      have val := congrArg Fin.val ((σ t).injective eq)
      change v.val=(v.val+1)%m at val
      have hv := v.isLt
      by_cases last : v.val+1=m
      · rw [last,Nat.mod_self] at val
        omega
      · rw [Nat.mod_eq_of_lt (by omega)] at val
        omega
    · rintro ⟨i,j,h,rfl⟩
      apply Finset.disjoint_left.mp (avoid t) he
      have nx : next i = j := Fin.ext (show (i.val+1)%m=j.val by rw [h,Nat.mod_eq_of_lt j.isLt])
      exact mem_image.mpr ⟨i,mem_univ i,by change s(i,next i)=s(i,j); rw [nx]⟩
  let S := fun t => support (σ t)
  have triangle_sub (t : Fin k) : T t ⊆ A := by
    intro e he
    refine mem_filter.mpr ⟨(mem_filter.mp he).1,?_⟩
    rintro ⟨i,j,h,rfl⟩
    apply Finset.disjoint_left.mp sep (mem_biUnion.mpr ⟨t,mem_univ _,he⟩)
    apply mem_union_right
    have nx : next i = j := Fin.ext (show (i.val+1)%m=j.val by rw [h,Nat.mod_eq_of_lt j.isLt])
    exact mem_image.mpr ⟨i,mem_univ i,by change s(i,next i)=s(i,j); rw [nx]⟩
  let used := univ.biUnion S ∪ univ.biUnion T
  let unused := A \ used
  have contained : used ⊆ A := union_subset (biUnion_subset.mpr fun t _ => sub t)
    (biUnion_subset.mpr fun t _ => triangle_sub t)
  have paired (t : Fin r) : Covers (S t) (Multiset.replicate 2 (2*m)) := by
    apply hamilton_region large f G (σ t)
    intro i a b
    have h := (mem _ _).mp (sub t (mem_image.mpr ⟨i,mem_univ i,rfl⟩))
    exact across _ _ h.1 h.2.1 h.2.2 a b
  have square (e : Sym2 (Fin m)) (he : e ∈ unused) : Covers {e} {4} := by
    induction e using Sym2.ind with
    | _ i j =>
      obtain ⟨ne,fwd,bwd⟩ := (mem i j).mp (mem_sdiff.mp he).1
      exact square_region f G ne (across i j ne fwd bwd)
  have rings : Covers (univ.biUnion S) (Multiset.replicate (2*r) (2*m)) := by
    have h := covers_many univ S (fun _ => Multiset.replicate 2 (2*m))
      (fun i _ => paired i) (fun _ _ _ _ hij => disj hij)
    simpa only [sum_const,card_univ,Fintype.card_fin,Multiset.nsmul_replicate,Nat.mul_comm r 2] using h
  have triple (i : Fin k) : Covers (T i) (Multiset.replicate 4 3) := by
    obtain ⟨a,b,c,ab,ac,bc,eq⟩ := Finset.card_eq_three.mp (three i)
    have edges : T i = {s(a,b),s(a,c),s(b,c)} := by
      ext e
      induction e using Sym2.ind with
      | _ x y =>
        simp only [T,eq,mem_filter,SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet,
          SimpleGraph.top_adj,Sym2.toFinset_mk_eq,insert_subset_iff,singleton_subset_iff,
          mem_insert,mem_singleton,Sym2.eq_iff]
        grind
    have adj {x y : Fin m} (h : s(x,y) ∈ T i) : ∀ p q, G.Adj (f (x,p)) (f (y,q)) := by
      obtain ⟨ne,fw,bw⟩ := (mem x y).mp (triangle_sub i h)
      exact across x y ne fw bw
    rw [edges]
    apply AlspachHamiltonMix.cross_triangle_region f G a b c ab ac bc
    · exact adj (by simp [edges])
    · exact adj (by simp [edges])
    · exact fun p q => (adj (by simp [edges]) q p).symm
  have triangle : Covers (univ.biUnion T) (Multiset.replicate (4*k) 3) := by
    have h := covers_many univ T (fun _ => Multiset.replicate 4 3) (fun i _ => triple i)
      (fun _ _ _ _ hij => ts hij)
    simpa only [sum_const,card_univ,Fintype.card_fin,Multiset.nsmul_replicate,Nat.mul_comm k 4] using h
  have disjoint : Disjoint (univ.biUnion S) (univ.biUnion T) := Finset.disjoint_left.mpr
    fun _ hs ht => Finset.disjoint_left.mp sep ht (mem_union_left _ hs)
  have left : Covers used _ := covers_union rings triangle disjoint
  have right : Covers unused (Multiset.replicate unused.card 4) := by
    have h := covers_many unused (fun e => {e}) (fun _ => ({4} : Multiset ℕ))
      square (fun i _ j _ ne => by simpa using ne)
    simpa [sum_const,Multiset.nsmul_singleton] using h
  have dj : Disjoint used unused := Finset.disjoint_left.mpr fun _ h h' => (mem_sdiff.mp h').2 h
  have union : used ∪ unused = A := Finset.union_sdiff_of_subset contained
  obtain ⟨cs,len,coverage⟩ := covers_union left right dj
  refine ⟨unused.card,cs,len,?_⟩
  intro i a j b
  have h := coverage (f (i,a)) (f (j,b))
  simp only [π,Equiv.symm_apply_apply,union,mem] at h
  rw [h]
  by_cases onPath : i=j ∨ i.val+1=j.val ∨ j.val+1=i.val
  · simp [onPath,show ¬(i≠j ∧ i.val+1≠j.val ∧ j.val+1≠i.val) by tauto]
  · simp [show i≠j ∧ i.val+1≠j.val ∧ j.val+1≠i.val by tauto]
/-- One ladder cycle covers the rails and caps. Its accompanying band squares
and the two-cycle lifts cover disjoint complementary parts of the row graph. -/
theorem odd_row_trades_either {m n r k : ℕ} (large : 4≤ m) (even : Even m) (limit : r≤ m/2-2)
    (f : (Fin m × Bool) ≃ Fin n) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (adj : ∀ i a j b, G.Adj (f (i,a)) (f (j,b)) ↔
      (i≠j ∨ a≠b) ∧ ¬(((i.val%2=0 ∧ i.val+1=j.val) ∨ (j.val%2=0 ∧ j.val+1=i.val)) ∧ a≠b)) :
    let leave := if m%6=1 ∨ m%6=3 then 0 else if m%6=0 ∨ m%6=2 then m/2 else m-1
    (k+m*(r+1)≤(m.choose 2-leave)/3 ∨
      k+m≤(m.choose 2-leave)/3 ∧ r+3*k≤ m/2-2) →
    ∃ (q : ℕ) (C : Multiset (Cycle G)), IsCycleDecomposition G C ∧
      lengths C=Multiset.replicate (2*r+1) (2*m) + Multiset.replicate (4*k) 3 + Multiset.replicate q 4 := by
  classical
  intro leave cap
  obtain ⟨σ,B,three,disj,avoid,ts,sep⟩ := cap.elim
    (AlspachAvoid.off_path_packing even large limit) (AlspachAvoid.off_path_packing_reverse even large)
  obtain ⟨q₁,S,ls,seed⟩ := seed_family large even f G adj
  obtain ⟨q₂,T,lt,away⟩ := off_path_trades (by omega : 3≤ m) f G σ B three disj avoid ts sep
    (fun i j ne fwd bwd a b => (adj i a j b).mpr ⟨Or.inl ne,fun ⟨band,_⟩ =>
      band.elim (fun h => fwd h.2) (fun h => bwd h.2)⟩)
  refine ⟨q₁+q₂,S+T,?_,?_⟩
  · intro e
    induction e using Sym2.ind with
    | _ x y =>
      obtain ⟨⟨i,a⟩,rfl⟩ := f.surjective x
      obtain ⟨⟨j,b⟩,rfl⟩ := f.surjective y
      intro he
      have hs := seed i a j b (G.mem_edgeFinset.mp he)
      have ht := away i a j b
      rw [Multiset.filter_add,Multiset.card_add,hs,ht]
      split <;> rfl
  · change (S+T).map SimpleGraph.Cycle.length=_
    rw [Multiset.map_add]
    change lengths S + lengths T = _
    rw [ls,lt,Multiset.replicate_add (2*r) 1,Multiset.replicate_add q₁ q₂,Multiset.replicate_one]
    ac_rfl

/-- The ladder realizes an odd Hamilton count with selected groups of four triangles. -/
theorem odd_hamilton_trade_build_either {m r k : ℕ} (large : 4≤ m) (even : Even m) (limit : r≤ m/2-2) :
    let leave := if m%6=1 ∨ m%6=3 then 0 else if m%6=0 ∨ m%6=2 then m/2 else m-1
    (k+m*(r+1)≤(m.choose 2-leave)/3 ∨
      k+m≤(m.choose 2-leave)/3 ∧ r+3*k≤ m/2-2) →
    ∃ J : (completeGraph (Fin (2*m))).Subgraph, J.IsPerfectMatching ∧
      ∃ (q : ℕ) (C : Multiset (Cycle (completeGraph (Fin (2*m)) \ J.spanningCoe))),
        IsCycleDecomposition _ C ∧ lengths C=Multiset.replicate (2*r+1) (2*m) +
          Multiset.replicate (4*k) 3 + Multiset.replicate q 4 := by
  classical
  intro leave cap
  let f : (Fin m × Bool) ≃ Fin (2*m) := Fintype.equivOfCardEq (by simp; omega)
  obtain ⟨J,hJ,adj⟩ := matched_row_graph even f
  exact ⟨J,hJ,odd_row_trades_either large even limit f _ adj cap⟩

end AlspachLadder

namespace AlspachAvoid
open SimpleGraph AlspachConjecture
open scoped Classical

/-- Matching the edge budgets recovers the requested triangle and square
multiplicities from a construction with the prescribed odd Hamilton count. -/
theorem odd_trade_lists_of_build {m r : ℕ} (large : 3≤ m)
    (I : (completeGraph (Fin (2*m))).Subgraph) (hI : I.IsPerfectMatching)
    (L : Multiset ℕ) (shape : ∀ a∈L,a=3 ∨ a=4 ∨ a=2*m) (budget : L.sum=(2*m).choose 2-(2*m)/2)
    (ham : L.count (2*m)=2*r+1)
    (build : ∃ J : (completeGraph (Fin (2*m))).Subgraph, J.IsPerfectMatching ∧
      ∃ (q : ℕ) (C : Multiset (Cycle (completeGraph (Fin (2*m)) \ J.spanningCoe))), IsCycleDecomposition _ C ∧
        lengths C=Multiset.replicate (2*r+1) (2*m)+Multiset.replicate (4*(L.count 3/4)) 3+Multiset.replicate q 4) :
    ∃ C : Multiset (Cycle (completeGraph (Fin (2*m)) \ I.spanningCoe)), IsCycleDecomposition _ C ∧ lengths C=L := by
  classical
  have n3 : 2*m≠3 := by omega
  have n4 : 2*m≠4 := by omega
  have split : L=Multiset.replicate (2*r+1) (2*m)+Multiset.replicate (L.count 3) 3+Multiset.replicate (L.count 4) 4 := by
    rw [←ham]
    ext a
    rcases eq_or_ne a (2*m) with rfl|hn
    · simp [Multiset.count_replicate,n3.symm,n4.symm]
    rcases eq_or_ne a 3 with rfl|h3
    · simp [Multiset.count_replicate,n3]
    rcases eq_or_ne a 4 with rfl|h4
    · simp [Multiset.count_replicate,n4]
    have none : a∉L := fun h => (shape a h).elim h3 (fun eq => eq.elim h4 hn)
    simp [Multiset.count_replicate,Multiset.count_eq_zero.mpr none,hn.symm,h3.symm,h4.symm]
  obtain ⟨J,perfect,q,C,dec,sizes⟩ := build
  have graph := TriangleBridge.matching_budget J perfect
  rw [Fintype.card_fin] at graph
  have sums : (lengths C).sum=L.sum := by
    rw [AlspachLadder.decomposition_budget C dec,budget]
    convert graph using 1
    congr 1
    ext f
    simp only [mem_edgeFinset]
  have arithmetic := sums.trans (congrArg Multiset.sum split)
  rw [sizes] at arithmetic
  simp only [Multiset.sum_add,Multiset.sum_replicate,smul_eq_mul] at arithmetic
  have tri : 4*(L.count 3/4)=L.count 3 := by omega
  have sq : q=L.count 4 := by omega
  obtain ⟨iso⟩ := OMA.R_AlspachConjecture_alspach_conjecture_variants_even_R2.matchings_complements_iso J I perfect hI
  apply OMA.R_AlspachConjecture_alspach_conjecture_variants_even_R2.iso_decomposition iso dec
  rw [sizes,tri,sq]
  exact split.symm

/-- At even base order, leave the ladder free and place triangle trades in
the remaining rows. The resulting odd Hamilton count is prescribed. -/
theorem odd_hamilton_trades {m r : ℕ} (large : 4≤ m) (even : Even m) (limit : r≤ m/2-2)
    (I : (completeGraph (Fin (2*m))).Subgraph) (hI : I.IsPerfectMatching)
    (L : Multiset ℕ) (shape : ∀ a∈L,a=3 ∨ a=4 ∨ a=2*m) (budget : L.sum=(2*m).choose 2-(2*m)/2)
    (ham : L.count (2*m)=2*r+1) :
    let leave := if m%6=1 ∨ m%6=3 then 0 else if m%6=0 ∨ m%6=2 then m/2 else m-1
    let k := L.count 3/4
    (k+m*(r+1)≤(m.choose 2-leave)/3 ∨ k+m≤(m.choose 2-leave)/3 ∧ r+3*k≤ m/2-2) →
    ∃ C : Multiset (Cycle (completeGraph (Fin (2*m)) \ I.spanningCoe)), IsCycleDecomposition _ C ∧ lengths C=L := by
  intro leave k cap
  exact odd_trade_lists_of_build (by omega) I hI L shape budget ham
    (AlspachLadder.odd_hamilton_trade_build_either large even limit cap)

end AlspachAvoid

namespace AlspachZero
open Finset SimpleGraph AlspachConjecture
open scoped Classical

theorem lists_of_ownership {m s h : ℕ} (large : 3≤ m) (cells : m*s+3*h=m.choose 2)
    (rows inv : Fin s → Fin m → Fin m) (undo : ∀ i z,inv i (rows i z)=z)
    (B : Fin h → Fin 3 → Fin m) (three : ∀ j,Function.Injective (B j))
    (owner : Fin m → Fin m → ℕ) (symm : ∀ x y,owner x y=owner y x) :
    let next (i : Fin m) : Fin m := ⟨(i.val+1)%m,Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩
    (∀ i z,owner (rows i z) (rows i (next z))=i.val) →
    (∀ j (a b : Fin 3),a≠b → owner (B j a) (B j b)=s+j.val) →
    ∀ (I : (completeGraph (Fin (2*m))).Subgraph), I.IsPerfectMatching → ∀ L : Multiset ℕ,
      (∀ a∈L,a=3 ∨ a=4 ∨ a=2*m) → L.sum=(2*m).choose 2-(2*m)/2 → L.count (2*m)=2*s →
      ∃ C : Multiset (Cycle (completeGraph (Fin (2*m)) \ I.spanningCoe)), IsCycleDecomposition _ C ∧ lengths C=L := by
  classical
  intro next ringOwner triOwner I hi L shape budget ham
  have rowInj (i : Fin s) : Function.Injective (rows i) := Function.LeftInverse.injective (undo i)
  let σ (i : Fin s) : Fin m ≃ Fin m := Equiv.ofBijective (rows i)
    ⟨rowInj i,Finite.injective_iff_surjective.mp (rowInj i)⟩
  let blocks (j : Fin h) := univ.image (B j)
  let H (i : Fin s) := univ.image fun z => s(σ i z,σ i (next z))
  let T (j : Fin h) := (⊤ : SimpleGraph (Fin m)).edgeFinset.filter fun e => e.toFinset ⊆ blocks j
  let tag := Sym2.lift ⟨owner,symm⟩
  have ring (i : Fin s) (e : Sym2 (Fin m)) (he : e∈H i) : tag e=i.val := by
    obtain ⟨z,_,rfl⟩ := mem_image.mp he
    exact ringOwner i z
  have tri (j : Fin h) (e : Sym2 (Fin m)) (he : e∈T j) : tag e=s+j.val := by
    induction e using Sym2.ind with
    | _ x y =>
      obtain ⟨ne, inX, inY⟩ : x≠y ∧ x∈blocks j ∧ y∈blocks j := by
        simpa [T,Sym2.toFinset_mk_eq,Finset.insert_subset_iff] using he
      obtain ⟨a,_,rfl⟩ := mem_image.mp inX
      obtain ⟨b,_,rfl⟩ := mem_image.mp inY
      exact triOwner j a b (fun eq => ne (congrArg (B j) eq))
  have hsep : Pairwise fun i j => Disjoint (H i) (H j) := by
    intro i j ne
    apply Finset.disjoint_left.mpr
    intro e hx hy
    exact ne (Fin.ext ((ring i e hx).symm.trans (ring j e hy)))
  have tsep : Pairwise fun i j => Disjoint (T i) (T j) := by
    intro i j ne
    apply Finset.disjoint_left.mpr
    intro e hx hy
    have eq := (tri i e hx).symm.trans (tri j e hy)
    exact ne (Fin.ext (by omega))
  have sep : Disjoint (univ.biUnion H) (univ.biUnion T) := by
    apply Finset.disjoint_left.mpr
    rintro e he te
    obtain ⟨i,_,hx⟩ := mem_biUnion.mp he
    obtain ⟨j,_,hy⟩ := mem_biUnion.mp te
    have eq := (ring i e hx).symm.trans (tri j e hy)
    have := i.isLt
    omega
  have size (j : Fin h) : (blocks j).card=3 := by
    simp [blocks,card_image_of_injective _ (three j)]
  apply AlspachLangford.partial_lists large σ blocks size hsep tsep sep I hi L shape budget ham
  rw [Fintype.card_fin]
  omega

end AlspachZero

namespace AlspachZero
open SimpleGraph AlspachConjecture
open scoped Classical

theorem thirty_lists (I : (completeGraph (Fin 30)).Subgraph) (hI : I.IsPerfectMatching)
    (L : Multiset ℕ) (shape : ∀ a∈L,a=3 ∨ a=4 ∨ a=30) (budget : L.sum=(30 : ℕ).choose 2-30/2)
    (even : Even (L.count 30)) (lo : 4≤L.count 30) (hi : L.count 30≤10) :
    ∃ C : Multiset (Cycle (completeGraph (Fin 30) \ I.spanningCoe)), IsCycleDecomposition _ C ∧ lengths C=L := by
  obtain ⟨s,hs⟩ := even
  have run {s h : ℕ} (ham : L.count 30=2*s) (cells : 15*s+3*h=105) (R J F E : ℕ) :
      let read (v n : ℕ) : Fin 15 := Fin.ofNat 15 ((v >>> (4*n)) &&& 15)
      let row (v : ℕ) (i : Fin s) (x : Fin 15) := read v (15*i.val+x.val)
      let face (j : Fin h) (a : Fin 3) := read F (3*j.val+a.val)
      let owner (a b : Fin 15) := (E >>> (5*((max a.val b.val)*(max a.val b.val-1)/2+min a.val b.val))) &&& 31
      (∀ i x,row J i (row R i x)=x) → (∀ j a b,face j a=face j b → a=b) →
      (∀ i (x : Fin 15),owner (row R i x) (row R i ⟨(x.val+1)%15,Nat.mod_lt _ (by decide)⟩)=i.val) →
      (∀ j a b,a≠b → owner (face j a) (face j b)=s+j.val) →
      ∃ C : Multiset (Cycle (completeGraph (Fin 30) \ I.spanningCoe)), IsCycleDecomposition _ C ∧ lengths C=L := by
    intro read row face owner inv distinct ring tri
    exact lists_of_ownership (by decide) cells (row R) (row J) inv face (fun j _ _ eq => distinct j _ _ eq)
      owner (fun a b => by simp [owner,max_comm,min_comm]) ring tri I hI L shape budget ham
  have cases : s=2 ∨ s=3 ∨ s=4 ∨ s=5 := by omega
  rcases cases with rfl|rfl|rfl|rfl
  · exact run (s:=2) (h:=25) hs (by decide) 0x2dc5ab68e49173012ca6d85e97b340 0x6dc9a4728b51e3069c3b584a712de0 0xb95c83a72641ed0e76da4982531cb0d75b84632ec1a90ea3542db1870c96c74d93eb2a81650 0x16691600d6a00ac8db053428200850a14da203e4c709b206c43a7803a780898b0780068bc0d9301f412cc2c4040fccc68ac0c1c0502bb9d712a4a9080ab81d208020 (by decide) (by decide) (by decide) (by decide)
  · exact run (s:=3) (h:=20) hs (by decide) 0x1a8e56b2c749d305a681793be2dc406d85cab734e9120 0xb268d3c59a417e05326d8b9ce174a04da893c7eb56120 0xb95c83a72641ed0e76da4982531cb0d75b84632ec1a90ea3542db1870c96 0x12484e01462201c29904b010180640412c9a01d443006a24b41658056584456a05408607a090f08ec20bc082040babc248b040a04829a953019c6704069854e10002 (by decide) (by decide) (by decide) (by decide)
  · exact run (s:=4) (h:=15) hs (by decide) 0x1a8524e3dc96b705ac68e9d2b173403aebd874912c56081d6ab397c45e20 0x8652d4c13b97ae097c5d8a3be12640ca3bd698127e4502c59a7e6b3481d0 0xb95c83a72641ed0e76da4982531cb0d75b84632ec1a90 0xe28422135a018c0570c2c1050043062039221c402082212a41238c7238042490700098180c8b00e4102c24088678ac006a02280861798cf0814350843788ca08403 (by decide) (by decide) (by decide) (by decide)
  · exact run (s:=5) (h:=10) hs (by decide) 0xac2e17b68493d5047c1ab2d85e963019dce4578b3a620973eb421d6c5a807db18ea9c432560 0xb2d8e4697153ca047c9a36d25e18b0acb53d6728941e0b64a2e1d539c8709d6c87ae12543b0 0xb95c83a72641ed0e76da4982531cb0 0xa1040302523104845080810c01220830a8a403461081a41946e1108e088602802c1050260c8708dc421c411106469c01488616100058c4b008c03100158c0618442 (by decide) (by decide) (by decide) (by decide)

end AlspachZero

namespace AlspachZero
open SimpleGraph AlspachConjecture
open scoped Classical

/-- Subsets of four edge-disjoint trades in the Bose design on 33 vertices
realize ten Hamilton counts with arbitrary admissible triangle and square multiplicities. -/
theorem sixtysix_lists (I : (completeGraph (Fin 66)).Subgraph) (hI : I.IsPerfectMatching)
    (L : Multiset ℕ) (shape : ∀ a∈L,a=3 ∨ a=4 ∨ a=66) (budget : L.sum=(66 : ℕ).choose 2-66/2)
    (even : Even (L.count 66)) (lo : 4≤L.count 66) (hi : L.count 66≤22) :
    ∃ C : Multiset (Cycle (completeGraph (Fin 66) \ I.spanningCoe)), IsCycleDecomposition _ C ∧ lengths C=L := by
  obtain ⟨s,hs⟩ := even
  let R : ℕ := 0x513a050829f5d519b3090d670b3c568779375035848464200878150c11b75168d24658e3c314a4937078195c260b7d054044371a2965ce4cf7d21cb11e26005b64534675440861508c0091167cd29418348b31705974571e6da8114d840e5470883c049d1c429b50b81e59321960f70c0465c57ce69008d4495430043d73481cc69278519881d0c270159024e65351f44a54b6c058f50965a10d4c339805d7827dc2a018b5c855b48c4501c500d2d648f69751971b38824140611f31878a09d5600c74454c071d3d50486897e01100d929779448e3061cd6d309159814b01a09634c1526504d545e18f04439472020b0df1d725b60a74040a2d16df79564c2035044c11cf08e71760915681235d68600a04b6513db1d874c4174df55225c20580d51669e0c40863805117067d93c91d32da60328c54504e35e4120a06d621d1170205dd7c86c20527102de38511558c0da4c928f3591916141c0
  let F : ℕ := 0x5f68079901f6047180db5c97561d959a5545d246040f7153604cc78f31d38b38a1d32864881912042c909414234305b40526078779c05e6c675b1e068571a29b68181915d6446d92196057d70995ca7d611e5837161975984d275345855075441c4cf5d53964ce81139a40e7cf39a44d7d035b50c8142df48b60f2dc30b50a20d24634a15228430910b1c44490d51833c50d020254709418154900f20048300c08044101e4c87521d83425cc04481f0e074279d09f70175c01c6ca71925a64681815e60a79721a5c16166544de51259141d54f5d43d648f6d239b4cd69231f44c60e31b54b5cd2ce2483481cc1c644714b1854061101c344a0930c24090552014c500d10081529f50968f11938358b0037de2207077db19e68075a29d6096d825c5c76171605826967d54d95527954574d06d13dc50e59436048d65031d34c6512d224530814b2035040cf18238408b2813c705310140a00e18021f74281b19f6436980205c475721b5985117124193cd78e35654c6932de40b3ca25324754510c28338505208150701c446
  let E : ℕ := 0x62599961835414195a92c5a81102d33b67bda4f24381aa6fa6f81d242a4f7b93b799b35495c5a72d262561614192b1103631505f7343aff131adf8ed8ca2b23a82b27ab4c87dc7fb7f97da4c67ac8cd3a51503441318e96263645f7affadf60798a97a332aef5965858b929354566d548294081a3f0b00b1a3f08058699b66c98d3345988bb36260797caef5e596c32391a312100aaf52685b87d65987c85d525a2f223222a2f314aaf15165996b91a1016186065e73245d694b5c6acf2f38ada5f26484c0d00010d0849263a5f78978d5c72f235298c00194aacf8ab5f85e85d593a90b304abf0f14a77c94e54f72739af2724f64e57cd4a89393040f034296d9af90cabf14097b5d85b71215762c2a8fa8f0904d87ec8093968097ec4d809193b5b557595d33394d3971202c4aff3248f98dca9f2a35565582a42122340c13880c02332125c55b78f9a9f13091b90d3858dd92aaef2e356586b0e088a88d0e086a7994b764d4b679c3143038fb2e25a8595acf12164c567adf89b83d516282a7fa7f28251883b49863a4975852f45772e48998e9101abf8dc63a1110a025282950653553850782c2540a03768cbaaf0f1a9f89c2d38ba8ad2c4568377a8f2b42a229486c52583aa5f0a14a83b86b93e76da70d0510507096db3e56bc5585450e185b5172642527cc7b977a3a777d0106ca9cf1d31d39cf6cc01188c87a28484b82b4e7a4f091a0f060669061a0f3d61834074051833d6a7f0d15064f52434d77aa74c2029ff65b9ff20474d69a02102069953727281d7e94c72134187199ef4560004569ef71b41567d67ba6f80a7dd2320801733f86eb4274369af4354256e93f61737fc0c0a3f79d0700716aa1931c46fd3986fc1c31946aa0b14b5a2fa1f488486a1f1620301b43871b303116222449675a76c47847576b75b3c79bf6499bf3c678a04173d1f34684651f473c04068b63968b1a39df1e472b44744572b1e49df1a237507077da1fa0f75c7490414161a217248606176c20373a71d9df3f66ba4789ff1f29ef1e36ea3e56ac4654577294266da19301044843670a1c26c91630506fc9cf0313d71d21b21843c84089bf69902068d67d
  let digit (v w n : ℕ) := (v >>> (w*n)) &&& (2^w-1)
  have run {s h : ℕ} (ham : L.count 66=2*s) (cells : 33*s+3*h=528) (π κ : ℕ) :
      let row v (i : Fin s) (z : Fin 33) := Fin.ofNat 33 (digit v 6 (33*digit π 4 i+z))
      let inverse (i : Fin s) (a : Fin 33) := ((List.finRange 33).find? fun z => row R i z=a).getD 0
      let face (j : Fin h) (a : Fin 3) := Fin.ofNat 33 (digit F 6 (3*(11*digit π 4 (s+j.val/11)+j.val%11)+a))
      let owner (a b : Fin 33) :=
        let e := digit E 12 (max a.val b.val*(max a.val b.val-1)/2+min a.val b.val)
        let c := digit κ 4 (e/16/11)
        if c<s then digit κ 4 (e%16) else s+11*(c-s)+e/16%11
      (∀ i z,inverse i (row R i z)=z) → (∀ j a b,face j a=face j b → a=b) →
      (∀ i (z : Fin 33),owner (row R i z) (row R i ⟨(z.val+1)%33,Nat.mod_lt _ (by decide)⟩)=i.val) →
      (∀ j a b,a≠b → owner (face j a) (face j b)=s+j.val) →
      ∃ C : Multiset (Cycle (completeGraph (Fin 66) \ I.spanningCoe)), IsCycleDecomposition _ C ∧ lengths C=L := by
    intro row inverse face owner inv three ring tri
    exact lists_of_ownership (by decide) cells (row R) inverse inv face (fun j _ _ eq => three j _ _ eq)
      owner (fun a b => by simp [owner,max_comm,min_comm]) ring tri I hI L shape budget ham
  have cases : s=2 ∨ s=3 ∨ s=4 ∨ s=5 ∨ s=6 ∨ s=7 ∨ s=8 ∨ s=9 ∨ s=10 ∨ s=11 := by omega
  rcases cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · apply run (s:=2) (h:=154) hs (by decide) 0xfedcba9876543210 0xfedcba9876543210 <;> decide +kernel
  · apply run (s:=3) (h:=143) hs (by decide) 0xfedcba9876510432 0xfedcba9876521043 <;> decide +kernel
  · apply run (s:=4) (h:=132) hs (by decide) 0xfedcba9432108765 0xfedcba9321087654 <;> decide +kernel
  · apply run (s:=5) (h:=121) hs (by decide) 0xfe876543210dcba9 0xfe43210dcba98765 <;> decide +kernel
  · apply run (s:=6) (h:=110) hs (by decide) 0xfedcba9432876510 0xfedcba9543287610 <;> decide +kernel
  · apply run (s:=7) (h:=99) hs (by decide) 0xfe8765432dcba910 0xfe65432dcba98710 <;> decide +kernel
  · apply run (s:=8) (h:=88) hs (by decide) 0xfe876510dcba9432 0xfe76543dcba21098 <;> decide +kernel
  · apply run (s:=9) (h:=77) hs (by decide) 0xfe43210dcba98765 0xfe876543210dcba9 <;> decide +kernel
  · apply run (s:=10) (h:=66) hs (by decide) 0xfe8765dcba943210 0xfe98765dcba43210 <;> decide +kernel
  · apply run (s:=11) (h:=55) hs (by decide) 0xfe432dcba9876510 0xfea98765432dcb10 <;> decide +kernel

end AlspachZero

namespace OMA.R_AlspachConjecture_alspach_conjecture_variants_even_R2_H3_R1

open SimpleGraph AlspachConjecture
open scoped Classical

/-- At most one Hamilton length, with a shorter length different from four
and a length different from both three and four. -/
def H1 : Prop :=
  ∀ (n : ℕ), Even n → 15 ≤ n →
    let half := n/2
    let leave := if half%6=1 ∨ half%6=3 then 0 else if half%6=0 ∨ half%6=2 then half/2 else half-1
    let admissible := fun m : Multiset ℕ =>
      (∀ k ∈ m, 3 ≤ k ∧ k ≤ n) ∧ m.sum = n.choose 2 - n / 2
    let ancestor := fun m : Multiset ℕ =>
      (m.filter (fun k => 6 ≤ k ∧ k < n)).card ≤ 1 ∧
      (3 ≤ m.count 5 → 2 * m.count 4 + 6 ≤ n) ∧
      (2 ≤ m.count 5 → 3 * m.count 3 + 10 ≤ n) ∧
      (1 ≤ m.count 4 → 1 ≤ m.count 5 → 3 * m.count 3 + 9 ≤ n) ∧
      (1 ≤ m.count 4 → m.count (n - 2) = 0 ∧ m.count (n - 1) = 0) ∧
      (1 ≤ m.count 5 → m.count (n - 4) = 0 ∧ m.count (n - 3) = 0 ∧
        m.count (n - 2) = 0 ∧ m.count (n - 1) = 0)
    let realizes := fun m : Multiset ℕ =>
      ∃ J : (completeGraph (Fin n)).Subgraph, J.IsPerfectMatching ∧
        ∃ C : Multiset (Cycle (completeGraph (Fin n) \ J.spanningCoe)),
          IsCycleDecomposition (completeGraph (Fin n) \ J.spanningCoe) C ∧ lengths C = m
    ∀ m, admissible m → ancestor m → m.count n ≤ 1 →
      (∃ k ∈ m, k ≠ 4 ∧ k < n) → (∃ k ∈ m, k ≠ 3 ∧ k ≠ 4) →
      ¬ (let r := m.count n/2
        let t := m.count 3/4
        let p := (half.choose 2-leave)/3
        Even half ∧ m.count n=2*r+1 ∧ r≤half/2-2 ∧
        (t+half*(r+1)≤p ∨ t+half≤p ∧ r+3*t≤half/2-2) ∧ ∀ a∈m,a=3 ∨ a=4 ∨ a=n) → realizes m

/-- At least two Hamilton cycles and one or more triangles, outside the families
covered by three groups and their successive doublings. -/
def H2 : Prop :=
  ∀ (n : ℕ), Even n → 15 ≤ n →
    let half := n/2
    let k := (half-3)/6
    let leave := if half%6=1 ∨ half%6=3 then 0 else if half%6=0 ∨ half%6=2 then half/2 else half-1
    let admissible := fun m : Multiset ℕ =>
      (∀ k ∈ m, 3 ≤ k ∧ k ≤ n) ∧ m.sum = n.choose 2 - n / 2
    let ancestor := fun m : Multiset ℕ =>
      (m.filter (fun k => 6 ≤ k ∧ k < n)).card ≤ 1 ∧
      (3 ≤ m.count 5 → 2 * m.count 4 + 6 ≤ n) ∧
      (2 ≤ m.count 5 → 3 * m.count 3 + 10 ≤ n) ∧
      (1 ≤ m.count 4 → 1 ≤ m.count 5 → 3 * m.count 3 + 9 ≤ n) ∧
      (1 ≤ m.count 4 → m.count (n - 2) = 0 ∧ m.count (n - 1) = 0) ∧
      (1 ≤ m.count 5 → m.count (n - 4) = 0 ∧ m.count (n - 3) = 0 ∧
        m.count (n - 2) = 0 ∧ m.count (n - 1) = 0)
    let realizes := fun m : Multiset ℕ =>
      ∃ J : (completeGraph (Fin n)).Subgraph, J.IsPerfectMatching ∧
        ∃ C : Multiset (Cycle (completeGraph (Fin n) \ J.spanningCoe)),
          IsCycleDecomposition (completeGraph (Fin n) \ J.spanningCoe) C ∧ lengths C = m
    ∀ m, admissible m → ancestor m → 2 ≤ m.count n → 3 ∈ m → (∀ k ∈ m, k = 3 ∨ k = n) →
      ¬ ((Even (m.count n) ∧ leave + half*m.count n ≤ m.count 4) ∨
        (m.count n = 2 ∧ half.choose 2-half-3*(k*(6*k+3)) ≤ m.count 4) ∨
        (n % 12 = 6 ∧
          ((Even (m.count n) ∧ 4 ≤ m.count n ∧ m.count n ≤ n/3 ∧ (n = 30 ∨ n = 66 ∨ n % 36 ≠ 30 ∨ 3 ≤ m.count 4)) ∨
            m.count n = 2)) ∨
        (∃ e t s j : ℕ, Odd t ∧ 1 ≤ s ∧ s ≤ t ∧ j ≤ 2^e*(2*s) ∧ n = 2^(e+1)*(6*t) ∧
          m.count n = 2*j ∧ 4^(e+1)*(if s=1 then 0 else 3*(t.choose 2%3)) + (2^(e+1)).choose 2*(3*t) + (2^e*(6*t))*(2^e*(2*s)-j) ≤ m.count 4)) →
      ¬ (let r := m.count n/2
        let t := m.count 3/4
        let p := (half.choose 2-leave)/3
        Even half ∧ m.count n=2*r+1 ∧ r≤half/2-2 ∧
        (t+half*(r+1)≤p ∨ t+half≤p ∧ r+3*t≤half/2-2) ∧ ∀ a∈m,a=3 ∨ a=4 ∨ a=n) → realizes m

/-- At least two Hamilton cycles and a cycle whose length is strictly between three and the order.
The paired and ladder constructions cover squares and Hamilton cycles. The three-layer
construction also covers specific Hamilton counts with triangles and squares. -/
def H3 : Prop :=
  ∀ (n : ℕ), Even n → 15 ≤ n →
    let half := n/2
    let k := (half-3)/6
    let leave := if half%6=1 ∨ half%6=3 then 0 else if half%6=0 ∨ half%6=2 then half/2 else half-1
    let admissible := fun m : Multiset ℕ =>
      (∀ k ∈ m, 3 ≤ k ∧ k ≤ n) ∧ m.sum = n.choose 2 - n / 2
    let ancestor := fun m : Multiset ℕ =>
      (m.filter (fun k => 6 ≤ k ∧ k < n)).card ≤ 1 ∧
      (3 ≤ m.count 5 → 2 * m.count 4 + 6 ≤ n) ∧
      (2 ≤ m.count 5 → 3 * m.count 3 + 10 ≤ n) ∧
      (1 ≤ m.count 4 → 1 ≤ m.count 5 → 3 * m.count 3 + 9 ≤ n) ∧
      (1 ≤ m.count 4 → m.count (n - 2) = 0 ∧ m.count (n - 1) = 0) ∧
      (1 ≤ m.count 5 → m.count (n - 4) = 0 ∧ m.count (n - 3) = 0 ∧
        m.count (n - 2) = 0 ∧ m.count (n - 1) = 0)
    let realizes := fun m : Multiset ℕ =>
      ∃ J : (completeGraph (Fin n)).Subgraph, J.IsPerfectMatching ∧
        ∃ C : Multiset (Cycle (completeGraph (Fin n) \ J.spanningCoe)),
          IsCycleDecomposition (completeGraph (Fin n) \ J.spanningCoe) C ∧ lengths C = m
    ∀ m, admissible m → ancestor m → 2 ≤ m.count n → (∃ k ∈ m, 3 < k ∧ k < n) →
      (∃ k ∈ m, k ≠ 4 ∧ k < n) →
      ¬ (((Even (m.count n) ∧ leave + half*m.count n ≤ m.count 4) ∨
        (m.count n = 2 ∧ half.choose 2-half-3*(k*(6*k+3)) ≤ m.count 4) ∨
        (n % 12 = 6 ∧
          ((Even (m.count n) ∧ 4 ≤ m.count n ∧ m.count n ≤ n/3 ∧ (n = 30 ∨ n = 66 ∨ n % 36 ≠ 30 ∨ 3 ≤ m.count 4)) ∨
            m.count n = 2)) ∨
        (∃ e t s j : ℕ, Odd t ∧ 1 ≤ s ∧ s ≤ t ∧ j ≤ 2^e*(2*s) ∧ n = 2^(e+1)*(6*t) ∧
          m.count n = 2*j ∧ 4^(e+1)*(if s=1 then 0 else 3*(t.choose 2%3)) + (2^(e+1)).choose 2*(3*t) + (2^e*(6*t))*(2^e*(2*s)-j) ≤ m.count 4)) ∧
        ∀ k ∈ m, k = 3 ∨ k = 4 ∨ k = n) →
      ¬ (let r := m.count n/2
        let t := m.count 3/4
        let p := (half.choose 2-leave)/3
        Even half ∧ m.count n=2*r+1 ∧ r≤half/2-2 ∧
        (t+half*(r+1)≤p ∨ t+half≤p ∧ r+3*t≤half/2-2) ∧ ∀ a∈m,a=3 ∨ a=4 ∨ a=n) → realizes m

theorem main : H1 → H2 → H3 → OMA.R_AlspachConjecture_alspach_conjecture_variants_even_R2.H3 := by
  intro few triangles mixed n even large
  dsimp only
  intro L admissible ancestor
  let half := n/2
  let leave := if half%6=1 ∨ half%6=3 then 0 else if half%6=0 ∨ half%6=2 then half/2 else half-1
  by_cases ladder : (let r := L.count n/2
        let t := L.count 3/4
        let p := (half.choose 2-leave)/3
        Even half ∧ L.count n=2*r+1 ∧ r≤half/2-2 ∧
        (t+half*(r+1)≤p ∨ t+half≤p ∧ r+3*t≤half/2-2) ∧ ∀ a∈L,a=3 ∨ a=4 ∨ a=n)
  · obtain ⟨baseEven,ham,limit,cap,sizes⟩ := ladder
    obtain ⟨u,rfl⟩ : ∃ u, n=2*u := by obtain ⟨u,hu⟩ := even; exact ⟨u,by omega⟩
    have half_eq : 2*u/2=u := by omega
    simp only [half,leave,half_eq] at baseEven limit cap
    let f : (Fin u × Bool) ≃ Fin (2*u) := Fintype.equivOfCardEq (by simp; omega)
    obtain ⟨J,hJ,_⟩ := AlspachSquares.pair_matching f
    exact ⟨J,hJ,AlspachAvoid.odd_hamilton_trades (by omega) baseEven limit J hJ L sizes admissible.2 ham cap⟩
  by_cases shape : ∀ a ∈ L, a=4 ∨ a=n
  · exact AlspachPaired.realize_square_hamilton n even L (fun a ha => (admissible.1 a ha).1) shape admissible.2
  · have other : ∃ k ∈ L, k ≠ 4 ∧ k < n := by
      by_contra! no
      apply shape
      intro k hk
      by_cases h4 : k = 4
      · exact Or.inl h4
      · exact Or.inr (Nat.le_antisymm (admissible.1 k hk).2 (no k hk h4))
    by_cases low : L.count n ≤ 1
    · by_cases trade : ∀ k ∈ L, k = 3 ∨ k = 4
      · obtain ⟨k,rfl⟩ : ∃ k, n=2*k := by obtain ⟨k,hk⟩ := even; exact ⟨k,by omega⟩
        let f : (Fin k × Bool) ≃ Fin (2*k) := Fintype.equivOfCardEq (by simp; omega)
        obtain ⟨J,perfect,_⟩ := AlspachSquares.pair_matching f
        exact ⟨J,perfect,AlspachTrades.all_triangle_square _ even J perfect L trade admissible.2⟩
      · refine few n even large L admissible ancestor low other ?_ ladder
        by_contra! none
        apply trade
        intro k hk
        by_cases tri : k = 3
        · exact Or.inl tri
        · exact Or.inr (none k hk tri)
    · have high : 2 ≤ L.count n := by omega
      let k := (half-3)/6
      by_cases routed : (((Even (L.count n) ∧ leave + half*L.count n ≤ L.count 4) ∨
        (L.count n = 2 ∧ half.choose 2-half-3*(k*(6*k+3)) ≤ L.count 4) ∨
        (n % 12 = 6 ∧
          ((Even (L.count n) ∧ 4 ≤ L.count n ∧ L.count n ≤ n/3 ∧ (n = 30 ∨ n = 66 ∨ n % 36 ≠ 30 ∨ 3 ≤ L.count 4)) ∨
            L.count n = 2)) ∨
        (∃ e t s j : ℕ, Odd t ∧ 1 ≤ s ∧ s ≤ t ∧ j ≤ 2^e*(2*s) ∧ n = 2^(e+1)*(6*t) ∧
          L.count n = 2*j ∧ 4^(e+1)*(if s=1 then 0 else 3*(t.choose 2%3)) + (2^(e+1)).choose 2*(3*t) + (2^e*(6*t))*(2^e*(2*s)-j) ≤ L.count 4)) ∧
        ∀ a∈L, a=3 ∨ a=4 ∨ a=n)
      · obtain ⟨parameters,sizes⟩ := routed
        obtain ⟨k,hk⟩ := even
        let f : (Fin k × Bool) ≃ Fin n := Fintype.equivOfCardEq (by simp; omega)
        obtain ⟨J,hJ,_⟩ := AlspachSquares.pair_matching f
        refine ⟨J,hJ,?_⟩
        rcases parameters with ⟨parity,rich⟩ | ⟨two,rich⟩ | ⟨residue,wide|two⟩ | ⟨e,t,s,j,odd,lo,hi,limit,order,hc,sq⟩
        · exact AlspachAvoid.all_orders_above_leave n ⟨k,hk⟩ (by omega) J hJ L sizes admissible.2 parity rich
        · exact AlspachLangford.suborder_even n ⟨k,hk⟩ (by omega) J hJ L sizes admissible.2 two rich
        · obtain ⟨parity,lo,hi,eq|eq|squares⟩ := wide
          · cases eq
            exact AlspachZero.thirty_lists J hJ L sizes admissible.2 parity lo hi
          · cases eq
            exact AlspachZero.sixtysix_lists J hJ L sizes admissible.2 parity lo hi
          · exact AlspachHamiltonMix.triangle_square_hamilton_six_mod_twelve n residue J hJ L sizes
              admissible.2 (Or.inr ⟨parity,lo,hi,squares⟩)
        · exact AlspachLangford.two_hamilton_six_mod_twelve n residue J hJ L sizes admissible.2 two
        · by_cases one : s=1
          · subst s
            apply AlspachIterated.two_seed_subcounts odd e n j _ order J hJ L sizes admissible.2 hc
            · simpa only [if_true,Nat.mul_zero,Nat.zero_add,Nat.mul_one,pow_succ] using sq
            · simpa only [Nat.mul_one,pow_succ] using limit
          · have largeT : 3≤t := by obtain ⟨k,hk⟩ := odd; omega
            exact AlspachIterated.tripartite_subcounts odd largeT (by omega) hi e n j limit order J hJ L sizes
              admissible.2 hc (by simpa only [if_neg one] using sq)
      · by_cases middle : ∃ k ∈ L, 3 < k ∧ k < n
        · exact mixed n even large L admissible ancestor high middle other routed ladder
        · have support (k : ℕ) (hk : k ∈ L) : k=3 ∨ k=n := by
            have bounds := admissible.1 k hk
            by_cases ht : k=3
            · exact Or.inl ht
            · exact Or.inr (by
                by_contra hn
                exact middle ⟨k,hk,by omega,by omega⟩)
          obtain ⟨k,hk,_,lt⟩ := other
          have tri : 3 ∈ L := by
            rcases support k hk with rfl | rfl
            · exact hk
            · omega
          exact triangles n even large L admissible ancestor high tri support (fun numeric => routed ⟨numeric,
              fun a ha => (support a ha).elim Or.inl (fun eq => Or.inr (Or.inr eq))⟩) ladder

end OMA.R_AlspachConjecture_alspach_conjecture_variants_even_R2_H3_R1
