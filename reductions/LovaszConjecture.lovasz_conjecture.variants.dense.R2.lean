import FormalConjectures.Wikipedia.LovaszConjecture
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Set.Card
import Mathlib.Tactic.Push
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Tactic.Ring
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.List.Chain
import Mathlib.Data.List.OfFn
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Data.Setoid.Basic

/-!
A finite reduction of the dense Hamiltonian-path theorem of Christofides, Hladký
and Máthé. Credit: @sturdy4days. The path rotation, minimum-atom and
Chvátal–Erdős arguments build on contributions #699, #4047 and #5270.
-/

namespace LovaszDense
open SimpleGraph
/-- A finite vertex-transitive graph is regular, with its minimum degree
equal to the degree of each vertex. -/
theorem regular_minDegree {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (transitive : ∀ u v : V, ∃ f : G ≃g G, f u = v) :
    G.IsRegularOfDegree G.minDegree := by
  intro v
  let : Nonempty V := ⟨v⟩
  obtain ⟨u, hu⟩ := G.exists_minimal_degree_vertex
  obtain ⟨f, hf⟩ := transitive u v
  subst v
  exact (f.degree_eq u).trans hu.symm
end LovaszDense

/-! The endpoint-index argument and list rotation below adapt the public proof
of the one-parameter Bondy conjecture by @philipsaint (OMA PR #699). For paths, the closing
chords are needed only when the longest path has fewer than the required
number of vertices. This gives the extra one at odd orders. -/
namespace LovaszDegree

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

theorem rotate_chain {c : List V} (hc : c.IsChain G.Adj ∧ ∀ a ∈ c.getLast?, ∀ b ∈ c.head?, G.Adj a b) {q : V} (hq : q ∈ c) :
    ∃ c' : List V, c'.Perm c ∧ c'.IsChain G.Adj ∧ c'.head? = some q := by
  obtain ⟨A, B, rfl⟩ := List.append_of_mem hq
  refine ⟨(q :: B) ++ A, List.perm_append_comm, ?_, by simp⟩
  obtain ⟨hch, hcl⟩ := hc
  rw [List.isChain_append] at hch
  refine List.isChain_append.2 ⟨hch.2.1, hch.1, ?_⟩
  intro x hx y hy
  apply hcl
  · rw [List.getLast?_append]
    have : (q :: B).getLast? = some x := hx
    simp [this]
  · rw [List.head?_append, hy]
    rfl

theorem getD_eq_getElem (l : List V) (d : V) {n : ℕ} (hn : n< l.length) :
    l.getD n d=l[n] := by simp [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hn]

theorem getD_zero (l : List V) (hl : l ≠ []) (d : V) : l.getD 0 d = l.head hl := by
  cases l with
  | nil => exact absurd rfl hl
  | cons a t => rfl

theorem getD_last (l : List V) (hl : l ≠ []) (d : V) : l.getD (l.length - 1) d = l.getLast hl := by
  rw [List.getLast_eq_getElem, getD_eq_getElem]

variable [Fintype V] [DecidableEq V]

/-- A finite connected graph has a path on at least the minimum of its
order and twice its minimum degree plus one vertices. -/
theorem long_path [DecidableRel G.Adj] (connected : G.Connected) :
    ∃ l : List V, l ≠ [] ∧ l.Nodup ∧ l.IsChain G.Adj ∧
      min (Fintype.card V) (2*G.minDegree+1) ≤ l.length := by
  classical
  have hconn := connected.preconnected
  set n := Fintype.card V with hn
  obtain ⟨v0⟩ := connected.nonempty
  have hnpos : 0< n := Fintype.card_pos_iff.mpr ⟨v0⟩
  let PP : ℕ → Prop := fun k => ∃ l : List V, (l.Nodup ∧ l.IsChain G.Adj) ∧ l.length = k
  have h1 : PP 1 := ⟨[v0], ⟨by simp, List.isChain_singleton _⟩, rfl⟩
  set M := Nat.findGreatest PP n
  obtain ⟨l, ⟨hlnd, hlch⟩, hlM⟩ : PP M := Nat.findGreatest_spec (by omega) h1
  have hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → l'.length ≤ M :=
    fun l' h1 h2 => Nat.le_findGreatest h1.length_le_card ⟨l', ⟨h1, h2⟩, rfl⟩
  have hM1 : 1 ≤ M := Nat.le_findGreatest (by omega) h1
  have hl_ne : l ≠ [] := by
    rintro rfl
    simp at hlM
    omega
  refine ⟨l,hl_ne,hlnd,hlch,?_⟩
  by_contra! short
  have unsaturated : l.length< n := lt_of_lt_of_le short (min_le_left _ _)
  have below : l.length<2*G.minDegree+1 := lt_of_lt_of_le short (min_le_right _ _)
  set q0 := l.head hl_ne
  set z := l.getLast hl_ne
  have hmn : l.length ≤ n := hlnd.length_le_card
  have ext_head : ∀ y, G.Adj q0 y → y ∈ l := by
    intro y hy
    by_contra hyl
    have := hmax (y :: l) (List.nodup_cons.2 ⟨hyl, hlnd⟩)
      (List.IsChain.cons_of_ne_nil hl_ne hlch ((hy).symm))
    simp at this
    omega
  have ext_last : ∀ y, G.Adj z y → y ∈ l := by
    intro y hy
    by_contra hyl
    have hch : (l ++ [y]).IsChain G.Adj := by
      refine List.isChain_append.2 ⟨hlch, List.isChain_singleton _, ?_⟩
      intro x hx y' hy'
      rw [List.getLast?_eq_some_getLast hl_ne] at hx
      simp at hx hy'
      subst hx hy'
      exact hy
    have hnd : (l ++ [y]).Nodup := by
      rw [List.nodup_append]
      refine ⟨hlnd, List.nodup_singleton _, ?_⟩
      intro a ha b hb
      simp at hb
      subst hb
      rintro rfl
      exact hyl ha
    have := hmax _ hnd hch
    simp at this
    omega
  set m := l.length with hm
  have hq0 : l.getD 0 q0 = q0 := getD_zero l hl_ne q0
  have hz : l.getD (m - 1) q0 = z := getD_last l hl_ne q0
  -- the two index sets
  let S := (Finset.range (m - 1)).filter (fun j => G.Adj q0 (l.getD (j + 1) q0))
  let T := (Finset.range (m - 1)).filter (fun j => G.Adj (l.getD j q0) z)
  have hS : G.degree q0 ≤ S.card := by
    rw [← card_neighborFinset_eq_degree]
    refine le_trans (Finset.card_le_card ?_) (Finset.card_image_le (s := S)
      (f := fun j => l.getD (j + 1) q0))
    intro y hy
    rw [mem_neighborFinset] at hy
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem (ext_head y hy)
    have hk0 : k ≠ 0 := by
      rintro rfl
      apply hy.ne
      rw [← getD_eq_getElem (d := q0), hq0]
    rw [Finset.mem_image]
    refine ⟨k - 1, ?_, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_range]
      refine ⟨by omega, ?_⟩
      rw [show k - 1 + 1 = k by omega, getD_eq_getElem _ _ hk]
      exact hy
    · rw [show k - 1 + 1 = k by omega, getD_eq_getElem _ _ hk]
  have hT : G.degree z ≤ T.card := by
    rw [← card_neighborFinset_eq_degree]
    refine le_trans (Finset.card_le_card ?_) (Finset.card_image_le (s := T)
      (f := fun j => l.getD j q0))
    intro y hy
    rw [mem_neighborFinset] at hy
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem (ext_last y hy)
    have hkm : k ≠ m - 1 := by
      rintro rfl
      apply hy.ne
      rw [← getD_eq_getElem (d := q0), hz]
    rw [Finset.mem_image]
    refine ⟨k, ?_, getD_eq_getElem _ _ hk⟩
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, ?_⟩
    rw [getD_eq_getElem _ _ hk]
    exact (hy).symm
  have hdq := G.minDegree_le_degree q0
  have hdz := G.minDegree_le_degree z
  obtain ⟨j, hjS, hjT⟩ : ∃ j, j ∈ S ∧ j ∈ T := by
    by_contra hcon
    push Not at hcon
    have hdisj : Disjoint S T := Finset.disjoint_left.mpr hcon
    have hsub : S ∪ T ⊆ Finset.range (m - 1) := by
      intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact (Finset.mem_filter.mp hx).1
      · exact (Finset.mem_filter.mp hx).1
    have := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdisj, Finset.card_range] at this
    omega
  rw [Finset.mem_filter, Finset.mem_range] at hjS hjT
  obtain ⟨hjm, hA⟩ := hjS
  obtain ⟨-, hB⟩ := hjT
  -- the cycle
  set c := l.take (j + 1) ++ (l.drop (j + 1)).reverse with hcdef
  have hperm : c.Perm l := by
    have := (List.Perm.append_left (l.take (j + 1)) (List.reverse_perm (l.drop (j + 1))))
    rw [List.take_append_drop] at this
    exact this
  have hcnd : c.Nodup := hperm.nodup_iff.mpr hlnd
  have hj1 : j < m := by omega
  have hj2 : j + 1 < m := by omega
  have e1 : (l.take (j + 1)).getLast? = some (l.getD j q0) := by
    rw [List.getLast?_take, getD_eq_getElem _ _ hj1]
    simp [List.getElem?_eq_getElem hj1]
  have e2 : (l.drop (j + 1)).reverse.head? = some z := by
    rw [List.head?_reverse, List.getLast?_drop, if_neg (by omega), List.getLast?_eq_some_getLast hl_ne]
  have e3 : c.getLast? = some (l.getD (j + 1) q0) := by
    rw [hcdef, List.getLast?_append, List.getLast?_reverse, List.head?_drop,
      List.getElem?_eq_getElem hj2, getD_eq_getElem _ _ hj2]
    rfl
  have e4 : c.head? = some q0 := by
    rw [hcdef, List.head?_append, List.head?_take]
    simp [List.head?_eq_some_head hl_ne, q0]
  have hcyc : c.IsChain G.Adj ∧ ∀ a ∈ c.getLast?, ∀ b ∈ c.head?, G.Adj a b := by
    refine ⟨List.isChain_append.2 ⟨hlch.take _, ?_, ?_⟩, ?_⟩
    · rw [List.isChain_reverse]
      exact (hlch.drop _).imp (fun a b h => h.symm)
    · intro x hx y hy
      rw [e1] at hx
      rw [e2] at hy
      simp at hx hy
      subst hx hy
      exact hB
    · intro a ha b hb
      rw [e3] at ha
      rw [e4] at hb
      simp at ha hb
      subst ha hb
      exact (hA).symm
  -- every vertex lies on the path
  have hall : ∀ w, w ∈ l := by
    intro w
    by_contra hw
    obtain ⟨p⟩ := hconn q0 w
    obtain ⟨d, -, hd1, hd2⟩ := p.exists_boundary_dart {x | x ∈ l} (List.head_mem hl_ne) hw
    have hqc : d.fst ∈ c := hperm.mem_iff.mpr hd1
    obtain ⟨c', hc'p, hc'ch, hc'h⟩ := rotate_chain hcyc hqc
    have hnd' : (d.snd :: c').Nodup := by
      refine List.nodup_cons.2 ⟨?_, (hc'p.trans hperm).nodup_iff.mpr hlnd⟩
      intro hmem
      exact hd2 ((hc'p.trans hperm).mem_iff.mp hmem)
    have hch' : (d.snd :: c').IsChain G.Adj := by
      refine List.isChain_cons.2 ⟨?_, hc'ch⟩
      intro y hy
      rw [hc'h] at hy
      simp at hy
      subst hy
      exact (d.adj).symm
    have := hmax _ hnd' hch'
    rw [List.length_cons, (hc'p.trans hperm).length_eq] at this
    omega
  have hmn' : m = n := by
    have h1 : l.toFinset = Finset.univ := by
      ext w
      simp [hall w]
    have h2 := List.toFinset_card_of_nodup hlnd
    rw [h1, Finset.card_univ] at h2
    omega
  omega

/-- The Dirac degree threshold for a Hamiltonian path, including odd orders. -/
theorem hamilton_path [DecidableRel G.Adj] (connected : G.Connected)
    (bound : Fintype.card V≤2*G.minDegree+1) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  obtain ⟨l,ne,nodup,chain,long⟩ := long_path connected
  rw [min_eq_left bound] at long
  let p := Walk.ofSupport l ne chain
  refine ⟨_,_,p,Walk.isHamiltonian_iff_isPath_and_length_eq.mpr ⟨?_,?_⟩⟩
  · apply (Walk.isPath_def _).mpr
    simpa only [p,Walk.support_ofSupport] using nodup
  · have upper := nodup.length_le_card
    have len := Walk.length_support p
    rw [show p.support=l from Walk.support_ofSupport ne chain] at len
    omega

end LovaszDegree

/-! Bipartite Hamiltonian closure. The crossed-chord construction on a list
uses the path ordering argument from @philipsaint's OMA proof #699. -/
namespace LovaszBipDirac
open SimpleGraph LovaszDegree
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Close a spanning alternating path if the degrees of its opposite
endpoints sum to more than the size of the first endpoint's part. -/
theorem close_path (side : V → Bool) (bip : ∀ ⦃u v⦄, G.Adj u v → side u ≠ side v)
    (l : List V) (hl_ne : l ≠ []) (hlnd : l.Nodup) (hlch : l.IsChain G.Adj)
    (span : ∀ v, v∈l) (opp : side (l.head hl_ne) ≠ side (l.getLast hl_ne))
    (bound : (Finset.univ.filter (fun v => side v = side (l.head hl_ne))).card <
      G.degree (l.head hl_ne) + G.degree (l.getLast hl_ne)) :
    ∃ c : List V, c.Perm l ∧ c.IsChain G.Adj ∧
      ∀ a ∈ c.getLast?, ∀ b ∈ c.head?, G.Adj a b := by
  classical
  set q0 := l.head hl_ne
  set z := l.getLast hl_ne
  have ext_head (y) (_ : G.Adj q0 y) := span y
  have ext_last (y) (_ : G.Adj z y) := span y
  set m := l.length with hm
  have hq0 : l.getD 0 q0 = q0 := getD_zero l hl_ne q0
  have hz : l.getD (m - 1) q0 = z := getD_last l hl_ne q0
  -- the two index sets
  let S := (Finset.range (m - 1)).filter (fun j => G.Adj q0 (l.getD (j + 1) q0))
  let T := (Finset.range (m - 1)).filter (fun j => G.Adj (l.getD j q0) z)
  have hS : G.degree q0 ≤ S.card := by
    rw [← card_neighborFinset_eq_degree]
    refine le_trans (Finset.card_le_card ?_) (Finset.card_image_le (s := S)
      (f := fun j => l.getD (j + 1) q0))
    intro y hy
    rw [mem_neighborFinset] at hy
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem (ext_head y hy)
    have hk0 : k ≠ 0 := by
      rintro rfl
      apply hy.ne
      rw [← getD_eq_getElem (d := q0), hq0]
    rw [Finset.mem_image]
    refine ⟨k - 1, ?_, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_range]
      refine ⟨by omega, ?_⟩
      rw [show k - 1 + 1 = k by omega, getD_eq_getElem _ _ hk]
      exact hy
    · rw [show k - 1 + 1 = k by omega, getD_eq_getElem _ _ hk]
  have hT : G.degree z ≤ T.card := by
    rw [← card_neighborFinset_eq_degree]
    refine le_trans (Finset.card_le_card ?_) (Finset.card_image_le (s := T)
      (f := fun j => l.getD j q0))
    intro y hy
    rw [mem_neighborFinset] at hy
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem (ext_last y hy)
    have hkm : k ≠ m - 1 := by
      rintro rfl
      apply hy.ne
      rw [← getD_eq_getElem (d := q0), hz]
    rw [Finset.mem_image]
    refine ⟨k, ?_, getD_eq_getElem _ _ hk⟩
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, ?_⟩
    rw [getD_eq_getElem _ _ hk]
    exact (hy).symm
  obtain ⟨j, hjS, hjT⟩ : ∃ j, j ∈ S ∧ j ∈ T := by
    by_contra hcon
    push Not at hcon
    have hdisj : Disjoint S T := Finset.disjoint_left.mpr hcon
    let A := Finset.univ.filter fun v => side v=side q0
    let f := fun j => l.getD j q0
    have inside (j) (hx : j∈S ∪ T) : j< m-1 := by
      rcases Finset.mem_union.mp hx with h|h <;> exact Finset.mem_range.mp (Finset.mem_filter.mp h).1
    have col (j) (hj : j∈S ∪ T) : f j∈A := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
      have h := inside j hj
      have low : j+1< l.length := by omega
      have step := List.isChain_iff_getElem.mp hlch j low
      change side (l.getD j q0)=side q0
      rcases Finset.mem_union.mp hj with hs|ht
      · have a := bip (Finset.mem_filter.mp hs).2
        have b := bip step
        rw [getD_eq_getElem _ _ low] at a
        rw [getD_eq_getElem _ _ (by omega)]
        cases cs : side l[j] <;> cases cq : side q0 <;> cases cp : side l[j+1] <;> simp_all
      · have a := bip (Finset.mem_filter.mp ht).2
        change side q0≠side z at opp
        cases cs : side (l.getD j q0) <;> cases cq : side q0 <;> cases cz : side z <;> simp_all
    have inj : Set.InjOn f (S ∪ T : Finset ℕ) := by
      intro i hi j hj eq
      have hi' := inside i hi
      have hj' := inside j hj
      exact (List.getD_inj (by omega) (by omega) hlnd).mp eq
    have size : (S ∪ T).card≤ A.card := by
      rw [←Finset.card_image_of_injOn inj]
      exact Finset.card_le_card (Finset.image_subset_iff.mpr col)
    rw [Finset.card_union_of_disjoint hdisj] at size
    change A.card < G.degree q0 + G.degree z at bound
    omega
  rw [Finset.mem_filter, Finset.mem_range] at hjS hjT
  obtain ⟨hjm, hA⟩ := hjS
  obtain ⟨-, hB⟩ := hjT
  -- the cycle
  set c := l.take (j + 1) ++ (l.drop (j + 1)).reverse with hcdef
  have hperm : c.Perm l := by
    have := (List.Perm.append_left (l.take (j + 1)) (List.reverse_perm (l.drop (j + 1))))
    rw [List.take_append_drop] at this
    exact this
  have hcnd : c.Nodup := hperm.nodup_iff.mpr hlnd
  have hj1 : j < m := by omega
  have hj2 : j + 1 < m := by omega
  have e1 : (l.take (j + 1)).getLast? = some (l.getD j q0) := by
    rw [List.getLast?_take, getD_eq_getElem _ _ hj1]
    simp [List.getElem?_eq_getElem hj1]
  have e2 : (l.drop (j + 1)).reverse.head? = some z := by
    rw [List.head?_reverse, List.getLast?_drop, if_neg (by omega), List.getLast?_eq_some_getLast hl_ne]
  have e3 : c.getLast? = some (l.getD (j + 1) q0) := by
    rw [hcdef, List.getLast?_append, List.getLast?_reverse, List.head?_drop,
      List.getElem?_eq_getElem hj2, getD_eq_getElem _ _ hj2]
    rfl
  have e4 : c.head? = some q0 := by
    rw [hcdef, List.head?_append, List.head?_take]
    simp [List.head?_eq_some_head hl_ne, q0]
  have hcyc : c.IsChain G.Adj ∧ ∀ a ∈ c.getLast?, ∀ b ∈ c.head?, G.Adj a b := by
    refine ⟨List.isChain_append.2 ⟨hlch.take _, ?_, ?_⟩, ?_⟩
    · rw [List.isChain_reverse]
      exact (hlch.drop _).imp (fun a b h => h.symm)
    · intro x hx y hy
      rw [e1] at hx
      rw [e2] at hy
      simp at hx hy
      subst hx hy
      exact hB
    · intro a ha b hb
      rw [e3] at ha
      rw [e4] at hb
      simp at ha hb
      subst ha hb
      exact (hA).symm
  exact ⟨c,hperm,hcyc⟩

end LovaszBipDirac

namespace LovaszBipDirac
open SimpleGraph

/-- Rotate a cyclic chain to a chosen first vertex, retaining the closing edge. -/
theorem cycle_from (G : SimpleGraph V) {L : List V}
    (chain : L.IsChain G.Adj)
    (closing : ∀ a∈L.getLast?, ∀ b∈L.head?, G.Adj a b) (x : V) (hx : x∈L) :
    ∃ T : List V, (x::T).Perm L ∧ (x::T).IsChain G.Adj ∧
      ∀ a∈(x::T).getLast?, G.Adj a x := by
  obtain ⟨A,B,rfl⟩ := List.append_of_mem hx
  change (A++(x::B)).IsChain G.Adj at chain
  obtain ⟨a,b,cross⟩ := List.isChain_append.mp chain
  refine ⟨B++A, (List.perm_append_comm : ((x::B)++A).Perm (A++x::B)),?_ ,?_⟩
  · change ((x::B)++A).IsChain G.Adj
    apply List.isChain_append.mpr ⟨b,a,?_⟩
    intro p hp q hq
    apply closing
    · rw [List.getLast?_append]
      simp [show (x::B).getLast?=some p from hp]
    · rw [List.head?_append,show A.head?=some q from hq]
      rfl
  · intro p hp
    change p∈((x::B)++A).getLast? at hp
    cases A with
    | nil => exact closing p (by simpa using hp) x (by simp)
    | cons z zs =>
      apply cross p _ x (by simp)
      simpa [List.getLast?_append,List.getLast?_eq_some_getLast] using hp

/-- Opening a spanning cycle at the unique extra edge either keeps the
cycle intact or leaves a spanning path between the extra edge's endpoints. -/
theorem open_added {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (three : 3≤ Fintype.card V)
    (x y : V) (diff : x≠y) :
    let C := fun J : SimpleGraph V => ∃ l : List V, l.Nodup ∧ l.length=Fintype.card V ∧
      l.IsChain J.Adj ∧ ∀ a∈l.getLast?, ∀ b∈l.head?, J.Adj a b
    C (G ⊔ SimpleGraph.fromEdgeSet {s(x,y)}) →
      C G ∨ ∃ (l : List V) (ne : l ≠ []), l.Nodup ∧ l.length=Fintype.card V ∧ l.IsChain G.Adj ∧
        ((l.head ne=x ∧ l.getLast ne=y) ∨ (l.head ne=y ∧ l.getLast ne=x)) := by
  intro C
  rintro ⟨l,nd,len,chain,close⟩
  classical
  let H := G ⊔ SimpleGraph.fromEdgeSet {s(x,y)}
  have old {a b : V} (h : H.Adj a b) :
      G.Adj a b ∨ (a=x ∧ b=y) ∨ (a=y ∧ b=x) := by
    rcases h with h|h
    · exact Or.inl h
    · exact Or.inr (Sym2.eq_iff.mp h.1)
  have span (L : List V) (hp : L.Perm l) (v : V) : v∈L := by
    have full : L.toFinset=Finset.univ := Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
      (by rw [Finset.card_univ,List.toFinset_card_of_nodup (hp.nodup_iff.mpr nd),hp.length_eq,len])
    exact List.mem_toFinset.mp (full ▸ Finset.mem_univ v)
  have opened (L : List V) (hp : L.Perm l) (ne : L≠[]) (ch : L.IsChain G.Adj)
      (ends : (L.head ne=x ∧ L.getLast ne=y) ∨ (L.head ne=y ∧ L.getLast ne=x)) :
      C G ∨ ∃ (l : List V) (ne : l ≠ []), l.Nodup ∧ l.length=Fintype.card V ∧
        l.IsChain G.Adj ∧ ((l.head ne=x ∧ l.getLast ne=y) ∨ (l.head ne=y ∧ l.getLast ne=x)) :=
    Or.inr ⟨L,ne,hp.nodup_iff.mpr nd,hp.length_eq.trans len,ch,ends⟩
  obtain ⟨T,perm,hch,last⟩ := cycle_from H chain close x (span l (.refl _) x)
  have nt : T≠[] := by
    have sz := perm.length_eq.trans len
    intro e
    simp [e] at sz
    omega
  let a := T.head nt
  let b := T.getLast nt
  have headAdj : H.Adj x a := (List.isChain_cons.mp hch).1 _ (List.head?_eq_some_head nt)
  have lastAdj : H.Adj b x := last b (by
    rw [List.getLast?_eq_some_getLast (List.cons_ne_nil x T)]; simp only [List.getLast_cons nt,b]; rfl)
  have ndd := List.nodup_cons.mp (perm.nodup_iff.mpr nd)
  have tail : T.IsChain G.Adj := List.IsChain.imp_of_mem_imp
    (fun v w hv hw h => (old h).resolve_right (by
      rintro (⟨eq,_⟩|⟨_,eq⟩)
      · exact ndd.1 (eq ▸ hv)
      · exact ndd.1 (eq ▸ hw))) hch.of_cons
  have ab : a≠b := by
    have sz := perm.length_eq.trans len
    have first := LovaszDegree.getD_zero T nt a
    have final := LovaszDegree.getD_last T nt a
    intro eq
    have ff := (List.getD_inj (fallback:=a) (xs:=T) (i:=0) (j:=T.length-1)
      (by simp at sz; omega) (by simp at sz; omega) ndd.2).mp (first.trans (eq.trans final.symm))
    simp at sz
    omega
  by_cases left : G.Adj x a
  · have allch : (x::T).IsChain G.Adj := List.IsChain.cons_of_ne_nil nt tail left
    by_cases right : G.Adj b x
    · refine Or.inl ⟨_,perm.nodup_iff.mpr nd,perm.length_eq.trans len,allch,?_⟩
      intro z hz v hv
      have hz' : (x::T).getLast?=some b := by
        rw [List.getLast?_eq_some_getLast (List.cons_ne_nil x T)]; simp only [List.getLast_cons nt,b]
      rw [hz'] at hz
      simp at hz hv
      exact hz ▸ hv ▸ right
    · have byy : b=y := by rcases (old lastAdj).resolve_left right with h|h <;> grind
      exact opened (x::T) perm (by simp) allch (Or.inl ⟨rfl,by simpa [List.getLast_cons nt,b] using byy⟩)
  · have ayy : a=y := by rcases (old headAdj).resolve_left left with h|h <;> grind
    have right : G.Adj b x := (old lastAdj).resolve_right (by
      rintro (⟨h,k⟩|⟨h,k⟩)
      · exact diff k
      · exact ab (ayy.trans h.symm))
    have perm' : (T++[x]).Perm l := List.perm_append_comm.trans perm
    have ch' : (T++[x]).IsChain G.Adj := by
      apply List.isChain_append.mpr ⟨tail,List.isChain_singleton _,?_⟩
      intro v hv w hw
      rw [List.getLast?_eq_some_getLast nt] at hv
      simp at hv hw
      exact hv ▸ hw ▸ right
    exact opened _ perm' (by simp) ch' (Or.inr ⟨by simpa [List.head_append_of_ne_nil nt,a] using ayy,by simp⟩)

/-- Removing one missing opposite-part edge preserves the existence of a
Hamiltonian cyclic ordering under the bipartite Ore degree-sum condition. -/
theorem remove_edge {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (side : V→Bool) (t : ℕ)
    (size : ∀ b : Bool, (Finset.univ.filter (fun v => side v=b)).card=t)
    (bip : ∀ ⦃v w⦄, G.Adj v w → side v≠side w) (three : 3≤ Fintype.card V)
    (x y : V) (opp : side x≠side y) (sum : t< G.degree x+G.degree y) :
    let C := fun J : SimpleGraph V => ∃ l : List V, l.Nodup ∧ l.length=Fintype.card V ∧
      l.IsChain J.Adj ∧ ∀ a∈l.getLast?, ∀ b∈l.head?, J.Adj a b
    C (G ⊔ SimpleGraph.fromEdgeSet {s(x,y)}) → C G := by
  intro C added
  rcases open_added G three x y (fun eq => opp (congrArg side eq)) added with done|⟨l,ne,nd,len,ch,ends⟩
  · exact done
  have full : l.toFinset=Finset.univ := Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    (by rw [Finset.card_univ,List.toFinset_card_of_nodup nd,len])
  obtain ⟨c,perm,cc,last⟩ := close_path side bip l ne nd ch
    (fun v => List.mem_toFinset.mp (full ▸ Finset.mem_univ v))
    (by rcases ends with ⟨h,k⟩|⟨h,k⟩ <;> rw [h,k] <;> first | exact opp | exact Ne.symm opp)
    (by rw [size]; rcases ends with ⟨h,k⟩|⟨h,k⟩ <;> rw [h,k] <;> omega)
  exact ⟨c,perm.nodup_iff.mpr nd,perm.length_eq.trans len,cc,last⟩

end LovaszBipDirac

namespace LovaszDense
open SimpleGraph Finset

/-- An edge-closure proof within a finite host may start at the host and
remove one admissible edge at a time. -/
theorem fill_selected {V : Type*} [Fintype V] [DecidableEq V] {P : SimpleGraph V → Prop}
    (G B : SimpleGraph V) (sub : G ≤ B) (top : P B)
    (step : ∀ J : SimpleGraph V, G ≤ J → J ≤ B →
      ¬B≤ J → ∃ x y : V, B.Adj x y ∧ ¬J.Adj x y ∧
        (P (J ⊔ fromEdgeSet {s(x,y)}) → P J)) : P G := by
  classical
  let m (J : SimpleGraph V) := B.edgeSet.ncard - J.edgeSet.ncard
  suffices all : ∀ k (J : SimpleGraph V), m J = k → G ≤ J → J ≤ B → P J by
    exact all _ G rfl le_rfl sub
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro J size bot host
    by_cases isFull : B ≤ J
    · simpa [le_antisymm host isFull] using top
    obtain ⟨x,y,hit,miss,undo⟩ := step J bot host isFull
    let F := J ⊔ fromEdgeSet {s(x,y)}
    have more : J < F := by
      refine lt_iff_le_not_ge.mpr ⟨le_sup_left,?_⟩
      intro h
      exact miss (h (show F.Adj x y from Or.inr ⟨rfl,hit.ne⟩))
    have upper : F ≤ B := by
      refine sup_le host ?_
      intro a b edge
      have eq : s(a,b) = s(x,y) := edge.1
      exact B.mem_edgeSet.mp (eq ▸ B.mem_edgeSet.mpr hit)
    have inc : J.edgeSet.ncard < F.edgeSet.ncard := Set.ncard_lt_ncard (edgeSet_strict_mono more) (Set.toFinite _)
    have cap : F.edgeSet.ncard ≤ B.edgeSet.ncard := Set.ncard_le_ncard (edgeSet_mono upper)
    have decrease : m F < k := by
      change B.edgeSet.ncard - J.edgeSet.ncard = k at size
      change B.edgeSet.ncard - F.edgeSet.ncard < k
      omega
    exact undo (ih _ decrease F rfl (bot.trans more.le) upper)

end LovaszDense

namespace LovaszDense
open SimpleGraph Finset

/-- An edge-closure proof within a finite host may start at the host and
remove one admissible edge at a time. -/
theorem fill_edges {V : Type*} [Fintype V] [DecidableEq V] {P : SimpleGraph V → Prop}
    (G B : SimpleGraph V) (sub : G ≤ B) (top : P B)
    (step : ∀ J : SimpleGraph V, G ≤ J → J ≤ B →
      ∀ x y : V, B.Adj x y → ¬J.Adj x y →
        P (J ⊔ fromEdgeSet {s(x,y)}) → P J) : P G := by
  apply fill_selected G B sub top
  intro J bot cap not_full
  change ¬(∀ ⦃v w : V⦄, B.Adj v w → J.Adj v w) at not_full
  push Not at not_full
  obtain ⟨x,y,hit,miss⟩ := not_full
  exact ⟨x,y,hit,miss,step J bot cap x y hit miss⟩

end LovaszDense

namespace LovaszDense
open SimpleGraph Finset

/-- A regular bipartite graph of positive degree has equally large color classes. -/
theorem balanced_sides {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (bp : G.IsBipartite) {d : ℕ} (reg : G.IsRegularOfDegree d)
    (pos : 0 < d) : ∃ (side : V → Bool) (t : ℕ), Fintype.card V = 2*t ∧
      (∀ b : Bool, (univ.filter fun v => side v=b).card=t) ∧
      (∀ {v w : V}, G.Adj v w → side v≠side w) := by
  classical
  obtain ⟨c,hc⟩ := bp
  let side (v : V) := finTwoEquiv (c v)
  have proper {v w : V} (edge : G.Adj v w) : side v ≠ side w :=
    fun eq => hc edge (finTwoEquiv.injective eq)
  let part (b : Bool) := univ.filter fun v => side v=b
  have bip : G.IsBipartiteWith (part false) (part true) := by
    constructor
    · rw [Set.disjoint_left]
      intro v h0 h1
      simpa [part] using (show v∈part false ∧ v∈part true from ⟨h0,h1⟩)
    · intro v w h
      have p := proper h
      cases h0 : side v <;> cases h1 : side w <;> simp_all [part]
  have sums := isBipartiteWith_sum_degrees_eq (s:=part false) (t:=part true) bip
  simp only [reg.degree_eq, sum_const, nsmul_eq_mul] at sums
  have eqn : (part false).card = (part true).card := Nat.mul_right_cancel pos sums
  have dis : Disjoint (part false) (part true) := Finset.disjoint_coe.mp bip.disjoint
  have cov : part false ∪ part true = univ := by
    ext v
    cases h : side v <;> simp [part,h]
  refine ⟨side,(part false).card, ?_,?_,@proper⟩
  · have total := card_union_of_disjoint dis
    rw [cov,card_univ,← eqn] at total
    omega
  · intro b
    cases b with
    | false => rfl
    | true => exact eqn.symm

end LovaszDense

namespace LovaszDense
open Finset SimpleGraph

/-- A complete bipartite graph with equally large nonempty parts has an
alternating, cyclically adjacent list of every vertex. -/
theorem complete_bipartite_list {V : Type*} [Fintype V] (G : SimpleGraph V)
    (side : V → Bool) (t : ℕ) (pos : 0 < t) (size : Fintype.card V=2*t)
    (parts : ∀ b : Bool, (univ.filter fun v => side v=b).card=t)
    (complete : ∀ {x y : V}, side x≠side y → G.Adj x y) :
    ∃ l : List V, l.Nodup ∧ l.length=Fintype.card V ∧ l.IsChain G.Adj ∧
      (∀ a∈l.getLast?, ∀ b∈l.head?, G.Adj a b) := by
  classical
  let label (b : Bool) : Fin t ≃ {v : V // side v=b} :=
    (Fintype.equivFinOfCardEq (by rw [Fintype.card_subtype,parts])).symm
  let parity (k : ℕ) := decide (k%2=1)
  let idx (i : Fin (2*t)) : Fin t := ⟨i.val/2,by have := i.isLt; omega⟩
  let f (i : Fin (2*t)) : V := label (parity i.val) (idx i)
  have color (i : Fin (2*t)) : side (f i) = parity i.val := (label _ _).property
  have inj : Function.Injective f := by
    intro i j eq
    have p : parity i.val = parity j.val := (color i).symm.trans ((congrArg side eq).trans (color j))
    have halves : i.val/2 = j.val/2 := by
      change (label (parity i.val) (idx i)).val = (label (parity j.val) (idx j)).val at eq
      rw [p] at eq
      exact congrArg Fin.val ((label _).injective (Subtype.ext eq))
    apply Fin.ext
    dsimp [parity] at p
    by_cases a : i.val%2=1 <;> by_cases b : j.val%2=1 <;> simp_all <;> omega
  have separates (i j : ℕ) (h : i%2≠j%2) : parity i≠parity j := by
    by_cases a : i%2=1 <;> by_cases b : j%2=1 <;> simp_all [parity]
  let l := List.ofFn f
  have len : l.length=2*t := List.length_ofFn
  have ne : l≠[] := fun h => by simp [h] at len; omega
  refine ⟨l,List.nodup_ofFn_ofInjective inj,len.trans size.symm,?_,?_⟩
  · apply List.isChain_iff_getElem.mpr
    intro i hi
    apply complete
    simp only [l,List.getElem_ofFn,color]
    apply separates
    omega
  · intro a ha b hb
    rw [List.getLast?_eq_some_getLast ne] at ha
    rw [List.head?_eq_some_head ne] at hb
    have ra : a=l.getLast ne := (Option.mem_some_iff.mp ha).symm
    have rb : b=l.head ne := (Option.mem_some_iff.mp hb).symm
    subst a b
    apply complete
    simp only [List.getLast_eq_getElem,List.head_eq_getElem,l,List.getElem_ofFn,
      List.length_ofFn,color]
    apply separates
    omega

end LovaszDense

namespace LovaszDense
open Finset SimpleGraph

/-- The balanced bipartite Ore criterion. Every missing cross edge has
endpoint degree sum greater than the size of one color class. -/
theorem bipartite_ore {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (side : V → Bool) (t : ℕ) (three : 3 ≤ Fintype.card V)
    (order : Fintype.card V = 2*t) (parts : ∀ b : Bool, (univ.filter fun v => side v=b).card=t)
    (bip : ∀ {x y : V}, G.Adj x y → side x ≠ side y)
    (degree : ∀ x y : V, side x ≠ side y → ¬G.Adj x y → t < G.degree x + G.degree y) :
    ∃ l : List V, l.Nodup ∧ l.length = Fintype.card V ∧ l.IsChain G.Adj ∧
      ∀ a ∈ l.getLast?, ∀ b ∈ l.head?, G.Adj a b := by
  classical
  let B : SimpleGraph V :=
    { Adj := fun x y => side x ≠ side y
      symm := ⟨fun _ _ h => h.symm⟩
      loopless := ⟨fun _ h => h rfl⟩ }
  let C (J : SimpleGraph V) := ∃ l : List V, l.Nodup ∧ l.length = Fintype.card V ∧
    l.IsChain J.Adj ∧ ∀ a ∈ l.getLast?, ∀ b ∈ l.head?, J.Adj a b
  apply fill_edges (P:=C) G B (fun _ _ h => bip h)
  · exact complete_bipartite_list B side t (by omega) order parts (fun h => h)
  · intro J sub host x y cross missing
    have need := degree x y cross (fun h => missing (sub h))
    have dx : G.degree x ≤ J.degree x := G.degree_le_of_le sub
    have dy : G.degree y ≤ J.degree y := G.degree_le_of_le sub
    exact LovaszBipDirac.remove_edge J side t parts (fun _ _ h => host h) three x y cross (by omega)

/-- The quarter-density case of the vertex-transitive Hamiltonian path problem,
in the more general class of positive regular bipartite graphs. -/
theorem bipartite_quarter {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (reg : G.IsRegularOfDegree G.minDegree) (bip : G.IsBipartite)
    (three : 3 ≤ Fintype.card V) (density : Fintype.card V < 4*G.minDegree) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  obtain ⟨side,t,ord,parts,cross⟩ := balanced_sides G bip reg (by omega)
  obtain ⟨l,nodup,len,chain,_⟩ := bipartite_ore G side t three ord parts @cross
    (fun x y _ _ => by have hx := G.minDegree_le_degree x; have hy := G.minDegree_le_degree y; omega)
  have ne : l ≠ [] := by rintro rfl; simp at len; omega
  let p := Walk.ofSupport l ne chain
  refine ⟨_,_,p,Walk.isHamiltonian_iff_isPath_and_length_eq.mpr ⟨?_,?_⟩⟩
  · apply (Walk.isPath_def _).mpr
    simpa only [p,Walk.support_ofSupport] using nodup
  · have h := Walk.length_support p
    rw [show p.support = l from Walk.support_ofSupport ne chain] at h
    omega
end LovaszDense

namespace LovaszDense
open SimpleGraph Finset

/-- At the half-density threshold inside a balanced bipartition, the
bipartite complement of a connected regular graph is connected as well. -/
theorem bipartite_complement_connected {V : Type*} [Fintype V] [DecidableEq V]
    (G H : SimpleGraph V) [DecidableRel G.Adj] (side : V → Bool) (d : ℕ)
    (pos : 0< d) (parts : ∀ b : Bool, (univ.filter fun v => side v=b).card=2*d)
    (proper : ∀ {v w}, G.Adj v w → side v≠side w) (reg : G.IsRegularOfDegree d)
    (conn : G.Connected) (comp : ∀ x y, H.Adj x y ↔ side x≠side y ∧ ¬G.Adj x y) :
    H.Connected := by
  classical
  let : Nonempty V := conn.nonempty
  let P (b : Bool) := univ.filter fun v => side v=b
  have toggle {x y : Bool} : x≠y ↔ y=(!x) := by cases x <;> cases y <;> decide
  have cardH (x : V) : (H.neighborFinset x).card=d := by
    have eq : G.neighborFinset x ∪ H.neighborFinset x=P (!(side x)) := by
      ext y
      simp only [mem_union,G.mem_neighborFinset,H.mem_neighborFinset,P,mem_filter,
        mem_univ,true_and,comp,← toggle]
      constructor
      · rintro (h|⟨h,_⟩)
        · exact proper h
        · exact h
      · intro h
        by_cases adj : G.Adj x y
        · exact Or.inl adj
        · exact Or.inr ⟨h,adj⟩
    have dis : Disjoint (G.neighborFinset x) (H.neighborFinset x) := by
      apply Finset.disjoint_left.mpr
      intro y h k
      exact ((comp x y).mp ((H.mem_neighborFinset ..).mp k)).2 ((G.mem_neighborFinset ..).mp h)
    have card := card_union_of_disjoint dis
    rw [eq,parts,G.card_neighborFinset_eq_degree,reg.degree_eq] at card
    omega
  have near (x : V) : ∃ y, H.Adj x y := by
    have : (H.neighborFinset x).Nonempty := card_pos.mp ((cardH x).symm ▸ pos)
    exact this.elim fun y h => ⟨y,(H.mem_neighborFinset ..).mp h⟩
  refine ⟨?_⟩
  by_contra bad
  obtain ⟨u,v,apart⟩ : ∃ u v, ¬H.Reachable u v := by
    simpa only [Preconnected,not_forall] using bad
  let C (x : V) := decide (H.Reachable u x)
  have cH {a b : V} (h : H.Adj a b) : C a=C b := by
    simp only [C,decide_eq_decide]
    exact ⟨fun h' => h'.trans h.reachable, fun h' => h'.trans h.symm.reachable⟩
  have occurs (k : Bool) : ∃ w, C w=k := by
    cases k with
    | false => exact ⟨v,decide_eq_false apart⟩
    | true => exact ⟨u,decide_eq_true (Reachable.rfl : H.Reachable u u)⟩
  have cells (k l : Bool) : ∃ w, C w=k ∧ side w=l := by
    obtain ⟨x,hx⟩ := occurs k
    by_cases h : side x=l
    · exact ⟨x,hx,h⟩
    obtain ⟨y,hy⟩ := near x
    refine ⟨y,(cH hy).symm.trans hx,?_⟩
    have opp := (comp x y).mp hy |>.1
    cases ax : side x <;> cases ay : side y <;> cases l <;> simp [ax,ay] at h opp ⊢
  let part (k l : Bool) := (P l).filter fun w => C w=k
  have contain (x : V) : H.neighborFinset x ⊆ part (C x) (!(side x)) := by
    intro y hy
    have adj := (H.mem_neighborFinset ..).mp hy
    have opp := toggle.mp ((comp _ _).mp adj).1
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,opp⟩,(cH adj).symm⟩
  have atLeast (k l : Bool) : d≤(part k l).card := by
    obtain ⟨x,c,s⟩ := cells k (!l)
    have lower := card_le_card (contain x)
    simpa only [cardH,c,s,Bool.not_not] using lower
  have exactSize (k l : Bool) : (part k l).card=d := by
    have sum : (part false l).card+(part true l).card=2*d := by
      have count := card_filter_add_card_filter_not (s:=P l) (p:=fun w => C w=false)
      simpa [part, P, parts] using count
    have h0 := atLeast false l
    have h1 := atLeast true l
    cases k <;> omega
  have all (x : V) : H.neighborFinset x = part (C x) (!(side x)) :=
    Finset.eq_of_subset_of_card_le (contain x) (by rw [exactSize,cardH])
  have cG {x y : V} (edge : G.Adj x y) : C x≠C y := by
    intro eq
    have hy : y∈H.neighborFinset x := by
      rw [all]
      exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,toggle.mp (proper edge)⟩,eq.symm⟩
    exact ((comp _ _).mp ((H.mem_neighborFinset ..).mp hy)).2 edge
  let color (x : V) := C x == side x
  have keep {x y : V} (h : G.Adj x y) : color x=color y := by
    have hc := cG h
    have hs := proper h
    dsimp only [color]
    cases x0 : C x <;> cases y0 : C y <;> cases xs : side x <;> cases ys : side y <;> simp [x0,y0,xs,ys] at hc hs ⊢
  have along {x y : V} (p : G.Walk x y) : color x=color y := by
    induction p with
    | nil => rfl
    | cons h p ih => exact (keep h).trans ih
  obtain ⟨a,ca,sa⟩ := cells false false
  obtain ⟨b,cb,sb⟩ := cells false true
  obtain ⟨p⟩ := conn.preconnected a b
  have eq := along p
  simp [color,ca,sa,cb,sb] at eq

end LovaszDense

namespace LovaszBipDirac
open SimpleGraph Finset

/-- When the two parts each have size twice the regular degree, connectedness
of the missing cross-edge graph allows a single extra edge to activate the
strict bipartite closure criterion throughout the graph. -/
theorem propagate {V : Type*} [Fintype V] [DecidableEq V] (G B M : SimpleGraph V)
    [DecidableRel G.Adj] (side : V→Bool) (d : ℕ) (regular : G.IsRegularOfDegree d)
    (size : ∀ b : Bool,(univ.filter fun v => side v=b).card=2*d)
    (host : ∀ u v, B.Adj u v ↔ side u≠side v) (sub : G≤ B)
    (missing : ∀ u v, M.Adj u v ↔ B.Adj u v ∧ ¬G.Adj u v)
    (connected : M.Connected) (three : 3≤ Fintype.card V) :
    let C := fun J : SimpleGraph V => ∃ l : List V, l.Nodup ∧ l.length=Fintype.card V ∧
      l.IsChain J.Adj ∧ ∀ a∈l.getLast?, ∀ b∈l.head?, J.Adj a b
    C B → ∃ l : List V, l.Nodup ∧ l.length=Fintype.card V ∧ l.IsChain G.Adj := by
  intro C full
  classical
  by_cases all : B≤ G
  · obtain ⟨l,h,k,c,_⟩ := full
    exact ⟨l,h,k,c.imp (fun _ _ e => all e)⟩
  change ¬(∀ ⦃v w : V⦄, B.Adj v w → G.Adj v w) at all
  push Not at all
  obtain ⟨x,y,across,absent⟩ := all
  let A := G ⊔ fromEdgeSet {s(x,y)}
  have base : G≤ A := le_sup_left
  have hostA : A≤ B := by
    apply sup_le sub
    intro a b edge
    have eq : s(a,b)=s(x,y) := edge.1
    exact B.mem_edgeSet.mp (eq ▸ B.mem_edgeSet.mpr across)
  have gain (J : SimpleGraph V) (inc : G≤ J) (p q : V) (no : ¬G.Adj p q)
      (yes : J.Adj p q) : d< J.degree p := by
    have lt : G.neighborFinset p ⊂ J.neighborFinset p := by
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨fun w hw => (J.mem_neighborFinset ..).mpr (inc ((G.mem_neighborFinset ..).mp hw)),?_⟩
      intro same
      have qmem := (J.mem_neighborFinset ..).mpr yes
      rw [←same] at qmem
      exact no ((G.mem_neighborFinset ..).mp qmem)
    simpa only [G.card_neighborFinset_eq_degree,J.card_neighborFinset_eq_degree,regular p] using card_lt_card lt
  have augmented : C A := by
    apply LovaszDense.fill_selected (P:=C) A B hostA full
    intro J up cap unfilled
    change ¬(∀ ⦃v w : V⦄, B.Adj v w → J.Adj v w) at unfilled
    push Not at unfilled
    obtain ⟨u,v,cross,miss⟩ := unfilled
    have lower := base.trans up
    have choose : ∃ p q : V, B.Adj p q ∧ ¬J.Adj p q ∧ d< J.degree p := by
      by_cases hot : d< J.degree u
      · exact ⟨u,v,cross,miss,hot⟩
      have start : d< J.degree x := gain J lower x y absent (up (show A.Adj x y from Or.inr ⟨rfl,across.ne⟩))
      obtain ⟨w⟩ := connected.preconnected x u
      obtain ⟨a,_,inside,outside⟩ := w.exists_boundary_dart {v | d< J.degree v} start hot
      obtain ⟨allowed,gap⟩ := (missing _ _).mp a.adj
      refine ⟨a.fst,a.snd,allowed,?_,inside⟩
      intro present
      exact outside (gain J lower a.snd a.fst (fun h => gap h.symm) present.symm)
    obtain ⟨p,q,allowed,gap,high⟩ := choose
    have low : d≤ J.degree q := (regular q) ▸ G.degree_le_of_le lower
    exact ⟨p,q,allowed,gap,remove_edge J side (2*d) size
      (fun _ _ h => (host ..).mp (cap h)) three p q ((host ..).mp allowed) (by omega)⟩
  rcases open_added G three x y across.ne augmented with kept|opened
  · obtain ⟨l,nd,len,ch,_⟩ := kept
    exact ⟨l,nd,len,ch⟩
  · obtain ⟨l,_,nd,len,ch,_⟩ := opened
    exact ⟨l,nd,len,ch⟩

end LovaszBipDirac

namespace LovaszBipDirac
open SimpleGraph Finset

/-- At equality in the quarter-density bound, a connected regular bipartite
graph still has a Hamiltonian path. -/
theorem equality_quarter {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (connected : G.Connected) (regular : G.IsRegularOfDegree G.minDegree)
    (bipartite : G.IsBipartite) (three : 3≤ Fintype.card V)
    (density : Fintype.card V = 4*G.minDegree) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  let d := G.minDegree
  have pos : 0< d := by dsimp [d]; omega
  obtain ⟨side,t,ord,parts,proper⟩ := LovaszDense.balanced_sides G bipartite regular pos
  have ts : t=2*d := by dsimp [d]; omega
  subst t
  let B : SimpleGraph V :=
    { Adj := fun x y => side x≠side y
      symm := ⟨fun _ _ h => h.symm⟩
      loopless := ⟨fun _ h => h rfl⟩ }
  let M := B \ G
  have missing (u v : V) : M.Adj u v ↔ side u≠side v ∧ ¬G.Adj u v := Iff.rfl
  have conn := LovaszDense.bipartite_complement_connected G M side d pos parts @proper regular connected missing
  obtain ⟨l,nd,len,ch⟩ := propagate G B M side d regular parts (fun _ _ => .rfl)
    (fun _ _ h => proper h) missing conn three
    (LovaszDense.complete_bipartite_list B side (2*d) (by omega) ord parts (fun h => h))
  have ne : l≠[] := by rintro rfl; simp at len; omega
  let p := Walk.ofSupport l ne ch
  refine ⟨_,_,p,Walk.isHamiltonian_iff_isPath_and_length_eq.mpr ⟨?_,?_⟩⟩
  · apply (Walk.isPath_def _).mpr
    simpa only [p,Walk.support_ofSupport] using nd
  · rw [show p.length=l.length-1 from Walk.length_ofSupport ne ch,len]

end LovaszBipDirac

namespace LovaszDense
open SimpleGraph

/-- A connected finite regular bipartite graph of order at most four times
its minimum degree has a Hamiltonian path, including at equality. -/
theorem bipartite_le_quarter {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (connected : G.Connected) (regular : G.IsRegularOfDegree G.minDegree)
    (bipartite : G.IsBipartite) (three : 3≤ Fintype.card V)
    (density : Fintype.card V ≤ 4*G.minDegree) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  rcases density.lt_or_eq with strict|equality
  · exact bipartite_quarter G regular bipartite three strict
  · exact LovaszBipDirac.equality_quarter G connected regular bipartite three equality

end LovaszDense

/-! Chvátal and Erdős (1972), traceability from vertex connectivity and
independence number. The path-splicing argument is @ali-hamdan-007's OMA
contribution #5270. Here connectivity is used in its explicit deletion form. -/
namespace LovaszDense.Trace
section

open SimpleGraph Finset

variable {V : Type*} {G : SimpleGraph V}

private theorem chain_join {L R : List V} {x y : V}
    (hL : L.IsChain G.Adj) (hR : R.IsChain G.Adj)
    (hx : L.getLast? = some x) (hy : R.head? = some y) (hxy : G.Adj x y) :
    (L ++ R).IsChain G.Adj := by
  apply hL.append hR
  intro a ha b hb
  have he : x = a := by simpa [hx] using ha
  have he' : y = b := by simpa [hy] using hb
  exact he ▸ he' ▸ hxy

/-- A longest vertex list may be chosen by maximizing its length. -/
theorem exists_longest_chain [Fintype V] [Nonempty V] :
    ∃ L : List V, L ≠ [] ∧ L.Nodup ∧ L.IsChain G.Adj ∧
      ∀ Q : List V, Q.Nodup → Q.IsChain G.Adj → Q.length ≤ L.length := by
  classical
  let T : Set ℕ := {n | ∃ l : List V, l.Nodup ∧ l.IsChain G.Adj ∧ l.length = n}
  have hf : T.Finite := (Set.finite_le_nat (Fintype.card V)).subset (by
    rintro _ ⟨l,hl,_,rfl⟩
    change l.length ≤ _
    simpa only [List.toFinset_card_of_nodup hl] using card_le_univ l.toFinset)
  let x : V := Classical.choice (inferInstance : Nonempty V)
  obtain ⟨n,⟨L,hn,hc,hlen⟩,hmax⟩ := hf.exists_maximal
    ⟨1,[x],by simp,List.IsChain.singleton x,rfl⟩
  refine ⟨L,?_,hn,hc,?_⟩
  · intro he
    have hh : n ≤ 1 → 1 ≤ n := hmax ⟨[x],by simp,List.IsChain.singleton x,rfl⟩
    simp [he] at hlen
    omega
  · intro Q hQn hQc
    have hh := hmax ⟨Q,hQn,hQc,rfl⟩
    omega

/-- Neither endpoint of a longest path has a neighbor off the path. -/
theorem longest_chain_endpoints {L : List V} (hn : L.Nodup) (hc : L.IsChain G.Adj)
    (hm : ∀ Q : List V, Q.Nodup → Q.IsChain G.Adj → Q.length ≤ L.length)
    {x : V} (hx : x ∉ L) :
    (∀ a ∈ L.head?, ¬ G.Adj a x) ∧ (∀ a ∈ L.getLast?, ¬ G.Adj a x) := by
  constructor
  · intro a ha hax
    have h := hm (x :: L) (List.nodup_cons.mpr ⟨hx,hn⟩) (hc.cons (by
      intro b hb
      rw [ha] at hb
      have he : a = b := by simpa using hb
      exact he ▸ hax.symm))
    simp at h
  · intro a ha hax
    have hn' : (L ++ [x]).Nodup := by
      refine List.nodup_append.mpr ⟨hn,by simp,?_⟩
      intro y hy z hz
      have he : z = x := by simpa using hz
      exact fun h => hx ((h.trans he) ▸ hy)
    have hc' := chain_join hc (List.IsChain.singleton x)
      ha (by simp : ([x] : List V).head? = some x) hax
    have h := hm (L ++ [x]) hn' hc'
    simp at h

/-- The start of a longest path cannot see the successor of a vertex with an
off-path neighbor. -/
theorem longest_chain_head_misses_successor (P B : List V) (a x y c : V)
    (hhead : (P ++ x :: y :: B).head? = some a)
    (hn : (P ++ x :: y :: B).Nodup) (hc : (P ++ x :: y :: B).IsChain G.Adj)
    (hm : ∀ Q : List V, Q.Nodup → Q.IsChain G.Adj → Q.length ≤ (P ++ x :: y :: B).length)
    (hco : c ∉ P ++ x :: y :: B) (hxc : G.Adj x c) : ¬ G.Adj a y := by
  intro hay
  let A := P ++ [x]
  let D := y :: B
  have hsplit : A ++ D = P ++ x :: y :: B := by simp [A,D,List.append_assoc]
  have hAn : A.Nodup := (hsplit ▸ hn : (A ++ D).Nodup).of_append_left
  have hDn : D.Nodup := (hsplit ▸ hn : (A ++ D).Nodup).of_append_right
  have hAc : A.IsChain G.Adj := (hsplit ▸ hc : (A ++ D).IsChain G.Adj).left_of_append
  have hDc : D.IsChain G.Adj := (hsplit ▸ hc : (A ++ D).IsChain G.Adj).right_of_append
  have hAl : A.getLast? = some x := by simp [A]
  have hAh : A.head? = some a := by
    have hAne : A ≠ [] := by simp [A]
    rw [← List.head?_append_of_ne_nil _ hAne, hsplit, hhead]
  have hR : A.reverse.IsChain G.Adj :=
    List.isChain_reverse.mpr (hAc.imp fun _ _ h => h.symm)
  have hR' : (A.reverse ++ D).IsChain G.Adj :=
    chain_join hR hDc (by simpa using hAh) rfl hay
  have hc' : (c :: (A.reverse ++ D)).IsChain G.Adj := by
    apply hR'.cons
    intro z hz
    have hAne : A.reverse ≠ [] := by simp [A]
    rw [List.head?_append_of_ne_nil _ hAne, List.head?_reverse, hAl] at hz
    have he : x = z := by simpa using hz
    exact he ▸ hxc.symm
  have hn' : (A.reverse ++ D).Nodup := by
    refine List.nodup_append.mpr ⟨List.nodup_reverse.mpr hAn,hDn,?_⟩
    intro u hu z hz
    exact (List.nodup_append.mp (hsplit ▸ hn : (A ++ D).Nodup)).2.2
      u (List.mem_reverse.mp hu) z hz
  have hcc : c ∉ A.reverse ++ D := by
    simpa only [List.mem_append,List.mem_reverse,hsplit.symm] using hco
  have hh := hm _ (List.nodup_cons.mpr ⟨hcc,hn'⟩) hc'
  rw [← hsplit] at hh
  simp at hh

/-- An off-path connecting path may replace any split into two consecutive
pieces, contradicting maximality. -/
theorem longest_chain_no_detour_gap {A D M : List V} {x y c d : V}
    (hAn : A.Nodup) (hDn : D.Nodup) (hMn : M.Nodup)
    (hAc : A.IsChain G.Adj) (hDc : D.IsChain G.Adj) (hMc : M.IsChain G.Adj)
    (hAD : A.Disjoint D) (hAM : A.Disjoint M) (hMD : M.Disjoint D)
    (hAl : A.getLast? = some x) (hDh : D.head? = some y)
    (hMh : M.head? = some c) (hMl : M.getLast? = some d)
    (hxc : G.Adj x c) (hdy : G.Adj d y)
    (hm : ∀ Q : List V, Q.Nodup → Q.IsChain G.Adj → Q.length ≤ (A ++ D).length) : False := by
  have hAMn := hAn.append hMn hAM
  have hAMc := chain_join hAc hMc hAl hMh hxc
  have hAMl : (A ++ M).getLast? = some d := by simp [hMl]
  have hAMD : (A ++ M).Disjoint D := by
    intro z hz hz'
    exact (List.mem_append.mp hz).elim (fun h => hAD h hz') (fun h => hMD h hz')
  have h := hm ((A ++ M) ++ D) (hAMn.append hDn hAMD)
    (chain_join hAMc hDc hAMl hDh hdy)
  have hne : M ≠ [] := by intro he; simp [he] at hMh
  have hp : 0 < M.length := List.length_pos_iff.mpr hne
  simp only [List.length_append] at h
  omega

/-- The successors of two separated attachments cannot see each other. A
detour joins the attachments and the intervening piece is traversed backwards. -/
theorem longest_chain_no_detour_chord {A B D M : List V} {x y z t c d : V}
    (hA : A.getLast? = some x) (hB : B.head? = some y) (hB' : B.getLast? = some z)
    (hD : D.head? = some t) (hM : M.head? = some c) (hM' : M.getLast? = some d)
    (hn : ((A ++ B) ++ D).Nodup) (hc : ((A ++ B) ++ D).IsChain G.Adj)
    (hMn : M.Nodup) (hMc : M.IsChain G.Adj)
    (hdis : M.Disjoint ((A ++ B) ++ D)) (hxc : G.Adj x c) (hdz : G.Adj d z)
    (hm : ∀ Q : List V, Q.Nodup → Q.IsChain G.Adj →
      Q.length ≤ ((A ++ B) ++ D).length) : ¬ G.Adj y t := by
  intro hyt
  have hAc := hc.left_of_append.left_of_append
  have hBc := hc.left_of_append.right_of_append
  have hDc := hc.right_of_append
  have hR : B.reverse.IsChain G.Adj := List.isChain_reverse.mpr (hBc.imp fun _ _ h => h.symm)
  have hAMc := chain_join hAc hMc hA hM hxc
  have hAMl : (A ++ M).getLast? = some d := by simp [hM']
  have hARc := chain_join hAMc hR hAMl (by simpa using hB') hdz
  have hARl : ((A ++ M) ++ B.reverse).getLast? = some y := by simp [hB]
  have hnewc := chain_join hARc hDc hARl hD hyt
  have hperm : (((A ++ M) ++ B.reverse) ++ D).Perm (((A ++ B) ++ D) ++ M) := by
    calc
      (((A ++ M) ++ B.reverse) ++ D).Perm (((A ++ M) ++ B) ++ D) :=
        ((List.reverse_perm B).append_left (A ++ M)).append_right D
      _ = A ++ (M ++ (B ++ D)) := by simp [List.append_assoc]
      (A ++ (M ++ (B ++ D))).Perm (A ++ ((B ++ D) ++ M)) := (show (M ++ (B ++ D)).Perm ((B ++ D) ++ M) from List.perm_append_comm).append_left A
      _ = (((A ++ B) ++ D) ++ M) := by simp [List.append_assoc]
  have hnewn := hperm.nodup_iff.mpr (hn.append hMn hdis.symm)
  have h := hm _ hnewn hnewc
  have hne : M ≠ [] := by intro he; simp [he] at hM
  have hp : 0 < M.length := List.length_pos_iff.mpr hne
  simp only [List.length_append,List.length_reverse] at h
  omega

end

section

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

omit [Fintype V] [DecidableEq V] in
private theorem pathSuccGivesMem {L : List V} {x y : V} (h : (∃ P B : List _, L = P ++ x :: y :: B)) :
    x ∈ L ∧ y ∈ L := by
  obtain ⟨P,B,rfl⟩ := h
  simp

omit [Fintype V] in
private theorem pathSuccIndex {L : List V} (hn : L.Nodup) {x y : V}
    (h : (∃ P B : List _, L = P ++ x :: y :: B)) : L.idxOf y = L.idxOf x + 1 := by
  obtain ⟨P,B,rfl⟩ := h
  have hp := List.nodup_append.mp hn
  have hx : x ∉ P := fun h => hp.2.2 x h x (by simp) rfl
  have hy : y ∉ P := fun h => hp.2.2 y h y (by simp) rfl
  have hxy : x ≠ y := fun h => (List.nodup_cons.mp hp.2.1).1 (by simp [h])
  rw [List.idxOf_append_of_notMem hx,List.idxOf_append_of_notMem hy]
  simp [List.idxOf_cons_ne _ hxy]

omit [Fintype V] in
private theorem eq_of_same_idx {L : List V} {x y : V}
    (hx : x ∈ L) (hy : y ∈ L) (h : L.idxOf x = L.idxOf y) : x = y := by
  have hx' := List.getElem?_idxOf hx
  have hy' := List.getElem?_idxOf hy
  rw [h,hy'] at hx'
  exact (Option.some.inj hx').symm

omit [Fintype V] in
private theorem pathSuccRightUnique {L : List V} (hn : L.Nodup) {x y z : V}
    (h : (∃ P B : List _, L = P ++ x :: y :: B)) (h' : (∃ P B : List _, L = P ++ x :: z :: B)) : y = z :=
  eq_of_same_idx (pathSuccGivesMem h).2 (pathSuccGivesMem h').2
    ((pathSuccIndex hn h).trans (pathSuccIndex hn h').symm)

omit [Fintype V] in
private theorem pathSuccLeftUnique {L : List V} (hn : L.Nodup) {x y z : V}
    (h : (∃ P B : List _, L = P ++ x :: z :: B)) (h' : (∃ P B : List _, L = P ++ y :: z :: B)) : x = y := by
  apply eq_of_same_idx (pathSuccGivesMem h).1 (pathSuccGivesMem h').1
  have hx := pathSuccIndex hn h
  have hy := pathSuccIndex hn h'
  omega

omit [Fintype V] [DecidableEq V] in
private theorem outside_path_list {C : Set V} (hc : (G.induce C).Connected)
    {a b : V} (ha : a ∈ C) (hb : b ∈ C) :
    ∃ L : List V, L.Nodup ∧ L.IsChain G.Adj ∧ L.head? = some a ∧
      L.getLast? = some b ∧ (∀ x ∈ L, x ∈ C) := by
  obtain ⟨p,hp⟩ := (hc ⟨a,ha⟩ ⟨b,hb⟩).exists_isPath
  let q := p.map (SimpleGraph.Embedding.induce C).toHom
  refine ⟨q.support, ?_, q.isChain_adj_support, ?_, ?_, ?_⟩
  · rw [Walk.support_map]
    exact hp.support_nodup.map Subtype.val_injective
  · rw [List.head?_eq_some_head q.support_ne_nil, q.head_support]
    rfl
  · rw [List.getLast?_eq_some_getLast q.support_ne_nil, q.getLast_support]
    rfl
  · intro x hx
    rw [Walk.support_map,List.mem_map] at hx
    obtain ⟨z,_,rfl⟩ := hx
    exact z.property

omit [Fintype V] [DecidableEq V] in
/-- A vertex separator surrounding an off-path component has at least κ
vertices. -/
theorem longest_chain_attachment_card (k : ℕ) (robust : ∀ S : Finset V, S.card < k → (G.induce ((S : Set V)ᶜ)).Preconnected)
    (L : List V) (C : Set V) (a : V)
    (hC : C.Nonempty) (hdis : ∀ x ∈ C, x ∉ L)
    (hclosed : ∀ x ∈ C, ∀ y ∉ L, G.Adj x y → y ∈ C)
    (ha : a ∈ L) (hna : ∀ x ∈ C, ¬ G.Adj a x)
    (S : Finset V) (hS : ∀ x, x ∈ S ↔ x ∈ L ∧ ∃ y ∈ C, G.Adj x y) :
    k ≤ S.card := by
  by_contra! hlt
  have hConn := robust S hlt
  obtain ⟨c,hc⟩ := hC
  have hcs : c ∉ S := fun h => hdis c hc ((hS c).mp h).1
  have has : a ∉ S := by
    intro hs
    obtain ⟨_,hx,hax⟩ := ((hS a).mp hs).2
    exact hna _ hx hax
  let W := ↥((S : Set V)ᶜ)
  let K := G.induce ((S : Set V)ᶜ)
  let c' : W := ⟨c,hcs⟩
  let a' : W := ⟨a,has⟩
  have chain_closed {y : W} (hy : Relation.ReflTransGen K.Adj c' y) : y.val ∈ C := by
    induction hy with
    | refl => exact hc
    | tail _ hxy ih =>
      rename_i x y _
      have he : G.Adj x.val y.val := hxy
      have hyL : y.val ∉ L := fun h => y.property ((hS y.val).mpr ⟨h,x.val,ih,he.symm⟩)
      exact hclosed _ ih _ hyL he
  exact hdis a (chain_closed ((K.reachable_iff_reflTransGen _ _).mp (hConn c' a'))) ha

omit [Fintype V] [DecidableEq V] in
private theorem pathSucc_of_attachment {L : List V} {C : Set V} {x : V}
    (hn : L.Nodup) (hc : L.IsChain G.Adj)
    (hm : ∀ Q : List V, Q.Nodup → Q.IsChain G.Adj → Q.length ≤ L.length)
    (hdis : ∀ x ∈ C, x ∉ L) (hx : x ∈ L) (hxc : ∃ c ∈ C, G.Adj x c) :
    ∃ y, (∃ P B : List _, L = P ++ x :: y :: B) := by
  obtain ⟨P,B,hL⟩ := List.append_of_mem hx
  obtain ⟨c,hcC,hAdj⟩ := hxc
  cases B with
  | nil =>
    have hl : L.getLast? = some x := by simp [hL]
    exact ((longest_chain_endpoints hn hc hm (hdis c hcC)).2 _ hl hAdj).elim
  | cons y B => exact ⟨y,P,B,hL⟩

omit [Fintype V] [DecidableEq V] in
private theorem pathSucc_not_attachment {L : List V} {C : Set V} {x y : V}
    (hn : L.Nodup) (hc : L.IsChain G.Adj)
    (hm : ∀ Q : List V, Q.Nodup → Q.IsChain G.Adj → Q.length ≤ L.length)
    (hC : (G.induce C).Connected) (hdis : ∀ x ∈ C, x ∉ L)
    (hs : (∃ P B : List _, L = P ++ x :: y :: B)) (hx : ∃ c ∈ C, G.Adj x c) :
    ¬ ∃ d ∈ C, G.Adj y d := by
  intro hy
  obtain ⟨P,B,rfl⟩ := hs
  obtain ⟨c,hcC,hxc⟩ := hx
  obtain ⟨d,hdC,hyd⟩ := hy
  obtain ⟨M,hMn,hMc,hMh,hMl,hMC⟩ := outside_path_list hC hcC hdC
  let A := P ++ [x]
  let D := y :: B
  have hL : A ++ D = P ++ x :: y :: B := by simp [A,D,List.append_assoc]
  have hADn : (A ++ D).Nodup := by rwa [hL]
  have hADc : (A ++ D).IsChain G.Adj := by rwa [hL]
  have hDM : M.Disjoint (A ++ D) := by
    intro z hz hz'
    exact hdis z (hMC z hz) (hL ▸ hz')
  exact longest_chain_no_detour_gap hADn.of_append_left hADn.of_append_right hMn
    hADc.left_of_append hADc.right_of_append hMc hADn.disjoint
    (fun _ ha hm => hDM hm (List.mem_append_left _ ha))
    (fun _ hm hd => hDM hm (List.mem_append_right _ hd))
    (by simp [A]) rfl hMh hMl hxc hyd.symm (by rw [hL]; exact hm)

omit [Fintype V] in
private theorem pathSucc_pair_no_adjacency_aux {L : List V} {C : Set V} {x x' y y' : V}
    (hn : L.Nodup) (hc : L.IsChain G.Adj)
    (hm : ∀ Q : List V, Q.Nodup → Q.IsChain G.Adj → Q.length ≤ L.length)
    (hC : (G.induce C).Connected) (hdis : ∀ x ∈ C, x ∉ L)
    (hs : (∃ P B : List _, L = P ++ x :: y :: B)) (hs' : (∃ P B : List _, L = P ++ x' :: y' :: B))
    (hx : ∃ c ∈ C, G.Adj x c) (hx' : ∃ d ∈ C, G.Adj x' d)
    (hind : L.idxOf x < L.idxOf x') :
    ¬ G.Adj y y' := by
  have hney : x' ≠ y := fun he => pathSucc_not_attachment hn hc hm hC hdis hs hx (he ▸ hx')
  have hne : x' ≠ x := fun he => (Nat.ne_of_lt hind) (congrArg L.idxOf he).symm
  obtain ⟨P,B,hP⟩ := hs
  have hmem := (pathSuccGivesMem hs').1
  have hnod : (P ++ x :: y :: B).Nodup := hP ▸ hn
  have hnot : x' ∉ P := by
    intro hp
    have hxP : x ∉ P := fun h =>
      (List.nodup_append.mp hnod).2.2 _ h _ (by simp) rfl
    have hxi : L.idxOf x = P.length := by
      rw [hP,List.idxOf_append_of_notMem hxP]
      simp
    have hl : P.idxOf x' < P.length := List.idxOf_lt_length_iff.mpr hp
    rw [hxi,hP,List.idxOf_append_of_mem hp] at hind
    omega
  have hxB : x' ∈ B := by
    rw [hP,List.mem_append,List.mem_cons,List.mem_cons] at hmem
    exact ((hmem.resolve_left hnot).resolve_left hne).resolve_left hney
  obtain ⟨Q,R,hBR⟩ := List.append_of_mem hxB
  have hR : R ≠ [] := by
    intro he
    have hl : L.getLast? = some x' := by
      rw [hP,hBR,he]
      simp [List.getLast?_cons]
    obtain ⟨d,hd,hdx⟩ := hx'
    exact (longest_chain_endpoints hn hc hm (hdis d hd)).2 _ hl hdx
  cases R with
  | nil => contradiction
  | cons t D =>
    let A := P ++ [x]
    let B' := (y :: Q) ++ [x']
    have hEq : L = (A ++ B') ++ t :: D := by
      simp only [hP,hBR,A,B',List.append_assoc,List.cons_append,List.nil_append]
    have hsT : (∃ P B : List _, L = P ++ x' :: t :: B) := by
      refine ⟨P ++ [x,y] ++ Q,D,?_⟩
      simp [hP,hBR,List.append_assoc]
    have he : t = y' := pathSuccRightUnique hn hsT hs'
    obtain ⟨c,hcC,hxc⟩ := hx
    obtain ⟨d,hdC,hxd⟩ := hx'
    obtain ⟨M,hMn,hMc,hMh,hMl,hMC⟩ := outside_path_list hC hcC hdC
    have hdisM : M.Disjoint ((A ++ B') ++ t :: D) :=
      fun z hz hz' => hdis z (hMC z hz) (hEq.symm ▸ hz')
    rw [← he]
    exact longest_chain_no_detour_chord (by simp [A]) (by simp [B'])
      (by change ((y :: Q) ++ [x']).getLast? = some x';
          simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or])
      rfl hMh hMl (hEq ▸ hn) (hEq ▸ hc) hMn hMc hdisM hxc hxd.symm
      (by rw [← hEq]; exact hm)

/-- A longest path with an outside component forces an independent set of at
least two more vertices than the vertex connectivity. -/
theorem indepNum_at_least_of_longest_outside (k : ℕ) (robust : ∀ S : Finset V, S.card < k → (G.induce ((S : Set V)ᶜ)).Preconnected)
    (L : List V) (a : V) (C : Set V)
    (hhead : L.head? = some a) (hn : L.Nodup) (hc : L.IsChain G.Adj)
    (hm : ∀ Q : List V, Q.Nodup → Q.IsChain G.Adj → Q.length ≤ L.length)
    (hC : (G.induce C).Connected) (hdis : ∀ x ∈ C, x ∉ L)
    (hclosed : ∀ x ∈ C, ∀ y ∉ L, G.Adj x y → y ∈ C) :
    k + 2 ≤ G.indepNum := by
  classical
  let S := L.toFinset.filter (fun x => ∃ y ∈ C, G.Adj x y)
  have hS (x : V) : x ∈ S ↔ x ∈ L ∧ ∃ y ∈ C, G.Adj x y := by simp [S]
  have haL : a ∈ L := List.mem_of_mem_head? hhead
  have hna (x : V) (hx : x ∈ C) : ¬ G.Adj a x :=
    (longest_chain_endpoints hn hc hm (hdis x hx)).1 _ hhead
  obtain ⟨c⟩ := hC.nonempty
  have hκ := longest_chain_attachment_card k robust L C a ⟨c.val,c.property⟩ hdis hclosed haL hna S hS
  have hsucc (x : S) : ∃ y, (∃ P B : List _, L = P ++ x.val :: y :: B) :=
    pathSucc_of_attachment hn hc hm hdis ((hS x.val).mp x.property).1 ((hS x.val).mp x.property).2
  choose f hf using hsucc
  have hfi : Function.Injective f := by
    intro x y he
    apply Subtype.ext
    exact pathSuccLeftUnique hn (hf x) (he ▸ hf y)
  let Y := S.attach.image f
  have hY : Y.card = S.card := by simp [Y,card_image_of_injective _ hfi]
  have hfL (x : V) (hx : x ∈ Y) : x ∈ L := by
    obtain ⟨y,_,rfl⟩ := mem_image.mp hx
    exact (pathSuccGivesMem (hf y)).2
  have hfc (x : V) (hx : x ∈ Y) : ¬ G.Adj x c.val := by
    obtain ⟨y,_,rfl⟩ := mem_image.mp hx
    intro he
    exact pathSucc_not_attachment hn hc hm hC hdis (hf y) ((hS y.val).mp y.property).2
      ⟨c.val,c.property,he⟩
  have hfa (x : V) (hx : x ∈ Y) : ¬ G.Adj a x := by
    obtain ⟨y,_,rfl⟩ := mem_image.mp hx
    obtain ⟨P,B,hPB⟩ := hf y
    obtain ⟨z,hz,haz⟩ := ((hS y.val).mp y.property).2
    apply longest_chain_head_misses_successor P B a y.val (f y) z
    · rwa [← hPB]
    · rwa [← hPB]
    · rwa [← hPB]
    · rw [← hPB]; exact hm
    · rw [← hPB]; exact hdis z hz
    · exact haz
  have hYa : a ∉ Y := by
    intro he
    obtain ⟨x,_,hfx⟩ := mem_image.mp he
    have hidx := pathSuccIndex hn (hf x)
    rw [hfx] at hidx
    have ha0 : L.idxOf a = 0 := by
      cases L with
      | nil => simp at hhead
      | cons h t =>
        have he : h = a := Option.some.inj hhead
        subst h
        simp
    omega
  have hYc : c.val ∉ Y := fun h => hdis c.val c.property (hfL _ h)
  have hYind : G.IsIndepSet (Y : Set V) := by
    intro x hx y hy hne
    obtain ⟨x',_,rfl⟩ := mem_image.mp hx
    obtain ⟨y',_,rfl⟩ := mem_image.mp hy
    have hxc := ((hS x'.val).mp x'.property).2
    have hyc := ((hS y'.val).mp y'.property).2
    rcases lt_trichotomy (L.idxOf x'.val) (L.idxOf y'.val) with h | h | h
    · exact pathSucc_pair_no_adjacency_aux hn hc hm hC hdis (hf x') (hf y') hxc hyc h
    · have hxy : x' = y' := Subtype.ext (eq_of_same_idx
        (pathSuccGivesMem (hf x')).1 (pathSuccGivesMem (hf y')).1 h)
      exact (hne (congrArg f hxy)).elim
    · exact fun he => pathSucc_pair_no_adjacency_aux hn hc hm hC hdis (hf y') (hf x') hyc hxc h he.symm
  have hI : G.IsIndepSet (↑(insert c.val Y) : Set V) := by
    rw [coe_insert]
    apply Set.Pairwise.insert_of_notMem hYc hYind
    intro x hx
    exact ⟨fun he => hfc x hx he.symm,hfc x hx⟩
  have hca : a ≠ c.val := fun he => hdis c.val c.property (he ▸ haL)
  have haI : a ∉ insert c.val Y := by simp [hca,hYa]
  have hI' : G.IsIndepSet (↑(insert a (insert c.val Y)) : Set V) := by
    rw [coe_insert]
    apply Set.Pairwise.insert_of_notMem haI hI
    intro x hx
    rcases mem_insert.mp hx with rfl | hx
    · exact ⟨hna _ c.property,fun h => hna _ c.property h.symm⟩
    · exact ⟨hfa x hx,fun h => hfa x hx h.symm⟩
  have hbig := hI'.card_le_indepNum
  rw [card_insert_of_notMem haI,card_insert_of_notMem hYc,hY] at hbig
  omega

/-- The traceability form of the Chvátal–Erdős theorem. -/
theorem path_of_cut_bound (G : SimpleGraph V) (hG : G.Connected) (k : ℕ) (robust : ∀ S : Finset V, S.card < k → (G.induce ((S : Set V)ᶜ)).Preconnected)
    (hα : G.indepNum ≤ k + 1) : LovaszConjecture.HasHamiltonianPath G := by
  classical
  let _ : Nonempty V := hG.nonempty
  obtain ⟨L,hLe,hn,hc,hm⟩ := exists_longest_chain (G := G)
  let a := L.head hLe
  have ha : L.head? = some a := List.head?_eq_some_head hLe
  let p := Walk.ofSupport L hLe hc
  have hp : p.support = L := Walk.support_ofSupport hLe hc
  have hpath : p.IsPath := by
    apply Walk.IsPath.mk'
    rwa [hp]
  refine ⟨_,_,p,hpath.isHamiltonian_of_mem ?_⟩
  intro x
  rw [hp]
  by_contra hx
  let T := {x | x ∉ L}
  let K := G.induce T
  let q : T := ⟨x,hx⟩
  let i := K.connectedComponentMk q
  let C : Set V := Subtype.val '' i.supp
  have hdis (z : V) (hz : z ∈ C) : z ∉ L := by
    obtain ⟨y,_,rfl⟩ := hz
    exact y.property
  have hclosed (z : V) (hz : z ∈ C) (y : V) (hy : y ∉ L) (he : G.Adj z y) : y ∈ C := by
    obtain ⟨s,hs,rfl⟩ := hz
    let t : T := ⟨y,hy⟩
    have hst : K.Adj s t := he
    exact ⟨t,i.mem_supp_of_adj_mem_supp hs hst,rfl⟩
  have hC : (G.induce C).Connected := by
    let f : i.supp → C := fun x => ⟨x.val.val,x.val,x.property,rfl⟩
    have hinj : Function.Injective f := by
      intro a b h
      exact Subtype.ext (Subtype.ext (congrArg (fun x : C => x.val) h))
    have hsurj : Function.Surjective f := by
      rintro ⟨x,y,hy,rfl⟩
      exact ⟨⟨y,hy⟩,rfl⟩
    let iso : K.induce i.supp ≃g G.induce C :=
      ⟨Equiv.ofBijective f ⟨hinj,hsurj⟩, by intro a b; rfl⟩
    exact iso.connected_iff.mp i.maximal_connected_induce_supp.1
  have h := indepNum_at_least_of_longest_outside k robust L a C ha hn hc hm hC hdis hclosed
  omega

end

end LovaszDense.Trace

namespace LovaszDense.Trace

open SimpleGraph Finset

/-- A connected graph without a spanning path has a minimum vertex cut
at least two smaller than its independence number. -/
theorem cut_of_no_path {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (conn : G.Connected) (noPath : ¬LovaszConjecture.HasHamiltonianPath G) :
    ∃ S : Finset V, S.card + 2 ≤ G.indepNum ∧
      ¬(G.induce ((S : Set V)ᶜ)).Preconnected ∧
      ∀ T : Finset V, T.card < S.card → (G.induce ((T : Set V)ᶜ)).Preconnected := by
  classical
  let cut (k : ℕ) := ∃ S : Finset V, S.card = k ∧ ¬(G.induce ((S : Set V)ᶜ)).Preconnected
  have bounded : ∃ k : ℕ, k + 2 ≤ G.indepNum ∧ cut k := by
    by_contra missing
    apply noPath
    apply path_of_cut_bound G conn (G.indepNum - 1) _ (by omega)
    intro S small
    by_contra disconnected
    exact missing ⟨S.card, by omega, S, rfl, disconnected⟩
  obtain ⟨j, bound, witness⟩ := bounded
  have existsCut : ∃ k, cut k := ⟨j, witness⟩
  obtain ⟨S, size, disconnect⟩ := Nat.find_spec existsCut
  have least := Nat.find_min' existsCut witness
  refine ⟨S, by omega, disconnect, ?_⟩
  intro T small
  by_contra disconnectT
  exact Nat.find_min existsCut (size ▸ small) ⟨T, rfl, disconnectT⟩

end LovaszDense.Trace

namespace LovaszDense.Watkins
open SimpleGraph LovaszConjecture Finset
/- Watkins' connectivity bound for finite connected vertex-transitive graphs.
The proof uses Mader's minimum-atom intersection argument. The walk and atom
setup adapts the project's kernel-checked proof of Babai's theorem (PR 4047). -/
set_option maxHeartbeats 2500000 in
theorem robust_two_thirds {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (connected : G.Connected) (transitive : IsVertexTransitive G)
    (d : ℕ) (degree : ∀ x, d≤ G.degree x) (S0 : Finset V)
    (small : 3*S0.card < 2*(d+1)) : (G.induce ((S0 : Set V)ᶜ)).Preconnected := by
  classical
  let ReachAvoiding (S : Finset V) (u v : V) : Prop :=
    ∃ p : G.Walk u v, ∀ w ∈ p.support, w ∉ S

  have reachAvoiding_refl {S : Finset V} {u : V} (hu : u ∉ S) : ReachAvoiding S u u :=
    ⟨Walk.nil, fun w hw => by simp only [Walk.support_nil, List.mem_singleton] at hw; subst hw; exact hu⟩

  have reachAvoiding_symm {S : Finset V} {u v : V} (h : ReachAvoiding S u v) :
      ReachAvoiding S v u := by
    obtain ⟨p, hp⟩ := h
    exact ⟨p.reverse, fun w hw => hp w (by simpa using hw)⟩

  have reachAvoiding_trans {S : Finset V} {u v w : V}
      (h1 : ReachAvoiding S u v) (h2 : ReachAvoiding S v w) :
      ReachAvoiding S u w := by
    obtain ⟨p1, hp1⟩ := h1
    obtain ⟨p2, hp2⟩ := h2
    refine ⟨p1.append p2, fun x hx => ?_⟩
    rcases (Walk.mem_support_append_iff p1 p2).mp hx with h | h
    · exact hp1 x h
    · exact hp2 x h


  let compAvoiding (S : Finset V) (u : V) : Finset V := by
    classical
    exact Finset.univ.filter (fun v => ReachAvoiding S u v)

  have mem_compAvoiding {S : Finset V} {u v : V} :
      v ∈ compAvoiding S u ↔ ReachAvoiding S u v := by
    classical simp [compAvoiding]

  have self_mem_compAvoiding {S : Finset V} {u : V} (hu : u ∉ S) :
      u ∈ compAvoiding S u :=
    (mem_compAvoiding).mpr (reachAvoiding_refl hu)

  have compAvoiding_disjoint_S {S : Finset V} {u : V} :
      Disjoint (compAvoiding S u) S := by
    rw [Finset.disjoint_left]
    intro x hx hxS
    obtain ⟨p, hp⟩ := (mem_compAvoiding).mp hx
    exact hp x (Walk.end_mem_support p) hxS

  have compAvoiding_closed {S : Finset V} {u a b : V}
      (ha : a ∈ compAvoiding S u) (hab : G.Adj a b) (hbS : b ∉ S) :
      b ∈ compAvoiding S u := by
    rw [mem_compAvoiding] at ha ⊢
    exact reachAvoiding_trans ha ⟨Walk.cons hab Walk.nil, fun w hw => by
      simp only [Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with h | h
      · rw [h]; obtain ⟨p, hp⟩ := ha; exact hp a (Walk.end_mem_support p)
      · rw [h]; exact hbS⟩


  let IsSeparating (S : Finset V) : Prop :=
    ∃ u v : V, u ∉ S ∧ v ∉ S ∧ ¬ ReachAvoiding S u v


  have isSeparating_of_closed_subset {S X : Finset V}
      (hXne : X.Nonempty) (hXdisj : Disjoint X S)
      (hYne : (Finset.univ \ (X ∪ S)).Nonempty)
      (hclosed : ∀ a ∈ X, ∀ b : V, G.Adj a b → b ∈ X ∪ S) :
      IsSeparating S := by
    obtain ⟨u, huX⟩ := hXne
    obtain ⟨v, hvY⟩ := hYne
    simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_union, true_and, not_or] at hvY
    refine ⟨u, v, Finset.disjoint_left.mp hXdisj huX, hvY.2, fun ⟨p, hp⟩ => ?_⟩
    have hstay : ∀ {a b : V} (q : G.Walk a b), a ∈ X → (∀ w ∈ q.support, w ∉ S) → b ∈ X := by
      intro a b q
      induction q with
      | nil => intro ha _; exact ha
      | @cons a c b hac r ih =>
        intro ha hq
        have hcS : c ∉ S := hq c (by simp)
        have hcXS := hclosed a ha c hac
        have hcX : c ∈ X := (Finset.mem_union.mp hcXS).resolve_right hcS
        exact ih hcX (fun w hw => hq w (by simp [hw]))
    exact hvY.1 (hstay p huX hp)


  have card_compAvoiding_le_of_closed {S X : Finset V} {u : V}
      (huX : u ∈ X) (hXdisj : Disjoint X S)
      (hclosed : ∀ a ∈ X, ∀ b : V, G.Adj a b → b ∈ X ∪ S) :
      (compAvoiding S u).card ≤ X.card := by
    apply Finset.card_le_card
    intro v hv
    obtain ⟨p, hp⟩ := (mem_compAvoiding).mp hv
    have hstay : ∀ {a b : V} (q : G.Walk a b), a ∈ X → (∀ w ∈ q.support, w ∉ S) → b ∈ X := by
      intro a b q
      induction q with
      | nil => intro ha _; exact ha
      | @cons a c b hac r ih =>
        intro ha hq
        have hcS : c ∉ S := hq c (by simp)
        have hcX : c ∈ X := (Finset.mem_union.mp (hclosed a ha c hac)).resolve_right hcS
        exact ih hcX (fun w hw => hq w (by simp [hw]))
    exact hstay p huX hp
  have no : ¬ IsSeparating S0 := by
    intro hsep0
    -- Choose a minimum separator and a smallest component after removing such a separator.
    have hex_κ : ∃ k : ℕ, ∃ S : Finset V, S.card = k ∧ IsSeparating S := ⟨S0.card, S0, rfl, hsep0⟩
    let κ := Nat.find hex_κ
    have hκ_spec : ∃ S : Finset V, S.card = κ ∧ IsSeparating S := Nat.find_spec hex_κ
    have hκ_min : ∀ S : Finset V, IsSeparating S → κ ≤ S.card := fun S hS =>
      Nat.find_min' hex_κ ⟨S, rfl, hS⟩
    have hκ_pos : 1 ≤ κ := by
      obtain ⟨S, hSc, u, v, _, _, hnr⟩ := hκ_spec
      by_contra h0
      have hSe : S = ∅ := Finset.card_eq_zero.mp (by omega)
      obtain ⟨p⟩ := connected u v
      exact hnr ⟨p, fun w _ => by simp [hSe]⟩
    -- Let a be the minimum cardinality of a component of G - S over all minimum separating sets S
    have hex_a : ∃ m : ℕ, ∃ (S : Finset V) (u : V),
        S.card = κ ∧ IsSeparating S ∧ u ∉ S ∧ (compAvoiding S u).card = m := by
      obtain ⟨S, hSc, u, _, hu, _, _⟩ := hκ_spec
      exact ⟨(compAvoiding S u).card, S, u, hSc, ⟨u, _, hu, by assumption, by assumption⟩, hu, rfl⟩
    let a := Nat.find hex_a
    obtain ⟨S, u0, hScard, hSsep, hu0S, hAcard⟩ := Nat.find_spec hex_a
    have ha_min : ∀ (T : Finset V) (w : V), T.card = κ → IsSeparating T → w ∉ T →
        a ≤ (compAvoiding T w).card := fun T w hTc hTs hw =>
      Nat.find_min' hex_a ⟨T, w, hTc, hTs, hw, rfl⟩
    set A := compAvoiding S u0
    set A' := Finset.univ \ (A ∪ S)
    have hA_disj_S : Disjoint A S := compAvoiding_disjoint_S
    have hA_closed : ∀ x ∈ A, ∀ y : V, G.Adj x y → y ∈ A ∪ S := fun x hx y hxy => by
      by_cases hyS : y ∈ S
      · exact Finset.mem_union_right _ hyS
      · exact Finset.mem_union_left _ (compAvoiding_closed hx hxy hyS)
    have hA'_ne : A'.Nonempty := by
      obtain ⟨x, y, hxS, hyS, hnr⟩ := hSsep
      by_cases hxA : x ∈ A
      · refine ⟨y, ?_⟩
        simp only [A', Finset.mem_sdiff, Finset.mem_univ, Finset.mem_union, true_and, not_or]
        exact ⟨fun hyA => hnr (reachAvoiding_trans (reachAvoiding_symm ((mem_compAvoiding).mp hxA)) ((mem_compAvoiding).mp hyA)), hyS⟩
      · refine ⟨x, ?_⟩
        simp only [A', Finset.mem_sdiff, Finset.mem_univ, Finset.mem_union, true_and, not_or]
        exact ⟨hxA, hxS⟩
    have hA'_card : a ≤ A'.card := by
      obtain ⟨w, hw⟩ := hA'_ne
      simp only [A', Finset.mem_sdiff, Finset.mem_univ, Finset.mem_union, true_and, not_or] at hw
      have hcomp_sub : compAvoiding S w ⊆ A' := by
        intro z hz
        simp only [A', Finset.mem_sdiff, Finset.mem_univ, Finset.mem_union, true_and, not_or]
        refine ⟨fun hzA => hw.1 ((mem_compAvoiding).mpr (reachAvoiding_trans ((mem_compAvoiding).mp hzA) (reachAvoiding_symm ((mem_compAvoiding).mp hz)))),
          Finset.disjoint_left.mp (compAvoiding_disjoint_S) hz⟩
      exact (ha_min S w hScard hSsep hw.2).trans (Finset.card_le_card hcomp_sub)
    have atom_degree : G.degree u0 + 1 ≤ a + κ := by
      have hu0A : u0 ∈ A := self_mem_compAvoiding hu0S
      have hnbr_sub : G.neighborFinset u0 ⊆ (A.erase u0) ∪ S := by
        intro w hw
        have hadj := (G.mem_neighborFinset _ _).mp hw
        rcases Finset.mem_union.mp (hA_closed u0 hu0A w hadj) with hwA | hwS
        · exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hadj.ne', hwA⟩)
        · exact Finset.mem_union_right _ hwS
      have hcard_le := (Finset.card_le_card hnbr_sub).trans (Finset.card_union_le _ _)
      have hAcard' : A.card = a := hAcard
      rw [Finset.card_erase_of_mem hu0A, hAcard', hScard] at hcard_le
      change G.degree u0 ≤ _ at hcard_le
      have ha_pos : 1 ≤ a := by rw [← hAcard']; exact Finset.card_pos.mpr ⟨u0, hu0A⟩
      omega
    let Side := {t : Finset V × Finset V × Finset V //
      Disjoint t.1 t.2.1 ∧ Disjoint t.1 t.2.2 ∧ Disjoint t.2.1 t.2.2 ∧
      (∀ x, x∈t.1 ∨ x∈t.2.1 ∨ x∈t.2.2) ∧
      (∀ x∈t.1, ∀ y, G.Adj x y → y∈t.1 ∪ t.2.1) ∧
      (∀ x∈t.2.2, ∀ y, G.Adj x y → y∈t.2.2 ∪ t.2.1) ∧ t.1.Nonempty ∧ t.2.2.Nonempty}
    let left (p : Side) := p.val.1
    let mid (p : Side) := p.val.2.1
    let right (p : Side) := p.val.2.2
    have lm (p : Side) : Disjoint (left p) (mid p) := p.property.1
    have lr (p : Side) : Disjoint (left p) (right p) := p.property.2.1
    have mr (p : Side) : Disjoint (mid p) (right p) := p.property.2.2.1
    have allv (p : Side) : ∀ x, x∈left p ∨ x∈mid p ∨ x∈right p := p.property.2.2.2.1
    have leftClosed (p : Side) : ∀ x∈left p, ∀ y, G.Adj x y → y∈left p∪mid p := p.property.2.2.2.2.1
    have rightClosed (p : Side) : ∀ x∈right p, ∀ y, G.Adj x y → y∈right p∪mid p := p.property.2.2.2.2.2.1
    have nl (p : Side) : (left p).Nonempty := p.property.2.2.2.2.2.2.1
    have nr (p : Side) : (right p).Nonempty := p.property.2.2.2.2.2.2.2
    let flip (p : Side) : Side :=
      ⟨(right p, mid p, left p), (mr p).symm, (lr p).symm, (lm p).symm,
       fun x => by rcases allv p x with h|h|h <;> first | exact Or.inl h | exact Or.inr (Or.inl h) | exact Or.inr (Or.inr h),
       rightClosed p, leftClosed p, nr p, nl p⟩
    have part (p : Side) (x : Finset V) :
        x.card = (x ∩ (left p)).card + (x ∩ (mid p)).card + (x ∩ (right p)).card := by
      have dl : Disjoint (x ∩ (left p)) (x ∩ (mid p)) := (lm p).mono inter_subset_right inter_subset_right
      have dr : Disjoint ((x ∩ (left p)) ∪ (x ∩ (mid p))) (x ∩ (right p)) :=
        Finset.disjoint_union_left.mpr ⟨(lr p).mono inter_subset_right inter_subset_right,(mr p).mono inter_subset_right inter_subset_right⟩
      rw [←card_union_of_disjoint dl,←card_union_of_disjoint dr]
      have u : x = (x ∩ (left p)) ∪ (x ∩ (mid p)) ∪ (x ∩ (right p)) := by
        ext w
        have := (allv p) w
        simp only [mem_inter,mem_union]
        tauto
      exact congrArg Finset.card u

    have corner (p q : Side) (h : ((left p) ∩ (left q)).Nonempty) :
        κ ≤ ((left p) ∩ (mid q)).card + ((mid p) ∩ (left q)).card + ((mid p) ∩ (mid q)).card ∧
        (((left p) ∩ (left q)).card < a →
          κ < ((left p) ∩ (mid q)).card + ((mid p) ∩ (left q)).card + ((mid p) ∩ (mid q)).card) := by
      let X := (left p) ∩ (left q)
      let U := ((left p) ∩ (mid q)) ∪ ((mid p) ∩ (left q)) ∪ ((mid p) ∩ (mid q))
      have apart : Disjoint X U := by
        rw [Finset.disjoint_left]
        intro x hx hu
        simp only [X,U,mem_inter,mem_union] at hx hu
        have pl := Finset.disjoint_left.mp (lm p) hx.1
        have ql := Finset.disjoint_left.mp (lm q) hx.2
        tauto
      have outside : (univ \ (X ∪ U)).Nonempty := by
        obtain ⟨w, hw⟩ := (nr q)
        have a := Finset.disjoint_right.mp (lr q) hw
        have b := Finset.disjoint_right.mp (mr q) hw
        exact ⟨w,by simp [X,U,a,b]⟩
      have closed : ∀ x∈X, ∀ y, G.Adj x y → y ∈ X ∪ U := by
        intro x hx y hxy
        have h1 := (leftClosed p) x (mem_inter.mp hx).1 y hxy
        have h2 := (leftClosed q) x (mem_inter.mp hx).2 y hxy
        simp only [X,U,mem_union,mem_inter] at h1 h2 ⊢
        tauto
      have sep := isSeparating_of_closed_subset h apart outside closed
      have le := hκ_min U sep
      have sz : U.card ≤ ((left p) ∩ (mid q)).card + ((mid p) ∩ (left q)).card + ((mid p) ∩ (mid q)).card :=
        (card_union_le _ _).trans (Nat.add_le_add_right (card_union_le _ _) _)
      refine ⟨le.trans sz,?_⟩
      intro small
      by_contra! contra
      have eq : U.card=κ := by omega
      obtain ⟨w,hw⟩ := h
      have lower := ha_min U w eq sep (Finset.disjoint_left.mp apart hw)
      have upper := card_compAvoiding_le_of_closed hw apart closed
      omega

    have grid (p q : Side) (hpa : (left p).card = a) (hpm : (mid p).card = κ) (hqm : (mid q).card = κ)
        (hbl : a ≤ (left q).card) (hbr : a ≤ (right q).card) (meet : ((left p) ∩ (mid q)).Nonempty) :
        2*a ≤ κ := by
      have cross0 (t : Side) (htm : (mid t).card=κ) (htr : a≤(right t).card) (meet' : ((left p)∩(mid t)).Nonempty) :
          ((left p) ∩ (left t)).card = 0 := by
        by_contra nz
        have pos : ((left p) ∩ (left t)).Nonempty := card_pos.mp (by omega)
        have positive := card_pos.mpr meet'
        have partA := part t (left p)
        have small : ((left p)∩(left t)).card< a := by omega
        have lhs :=  (corner p t pos).2 small
        have partS := part t (mid p)
        have partT := part p (mid t)
        rw [inter_comm (mid t) (left p),inter_comm (mid t) (mid p),inter_comm (mid t) (right p)] at partT
        have partC := part p (right t)
        rw [inter_comm (right t) (left p),inter_comm (right t) (mid p),inter_comm (right t) (right p)] at partC
        by_cases hn : ((right p) ∩ (right t)).Nonempty
        · have rhs :=  (corner (flip p) (flip t) hn).1
          change κ ≤ ((right p) ∩ (mid t)).card + ((mid p) ∩ (right t)).card + ((mid p) ∩ (mid t)).card at rhs
          omega
        · have emp : ((right p)∩(right t)).card = 0 := by
            by_contra ne
            exact hn (card_pos.mp (by omega))
          omega
      have cap (t : Side) (htm : (mid t).card=κ) (htr : a≤(right t).card) (htl : a≤(left t).card)
          (mt : ((left p)∩(mid t)).Nonempty) : a ≤ ((mid p) ∩ (left t)).card := by
        have hl := cross0 t htm htr mt
        have hr := cross0 (flip t) htm htl mt
        change ((left p)∩(right t)).card=0 at hr
        have partA := part t (left p)
        have partS := part t (mid p)
        have partT := part p (mid t)
        rw [inter_comm (mid t) (left p),inter_comm (mid t) (mid p),inter_comm (mid t) (right p)] at partT
        have partB := part p (left t)
        rw [inter_comm (left t) (left p),inter_comm (left t) (mid p),inter_comm (left t) (right p)] at partB
        by_cases hn : ((right p) ∩ (left t)).Nonempty
        · have rhs :=  (corner (flip p) t hn).1
          change κ ≤ ((right p)∩(mid t)).card+((mid p)∩(left t)).card+((mid p)∩(mid t)).card at rhs
          omega
        · have emp : ((right p)∩(left t)).card=0 := by
            by_contra ne
            exact hn (card_pos.mp (by omega))
          omega
      have lhs :=  cap q hqm hbr hbl meet
      have rhs :=  cap (flip q) hqm hbl hbr meet
      change a ≤ ((mid p) ∩ (right q)).card at rhs
      have := part q (mid p)
      omega

    have hA'closed : ∀ x∈A', ∀ y, G.Adj x y → y ∈ A' ∪ S := by
      intro x hx y hxy
      by_cases h : y∈S
      · exact mem_union_right _ h
      · apply mem_union_left
        apply mem_sdiff.mpr
        refine ⟨mem_univ _,?_⟩
        intro hy
        rcases mem_union.mp hy with hyA|hyS
        · exact (mem_sdiff.mp hx).2 (hA_closed y hyA x hxy.symm)
        · exact h hyS
    let P : Side := ⟨(A,S,A'), hA_disj_S, by
      apply Finset.disjoint_left.mpr
      intro x ha hc
      exact (mem_sdiff.mp hc).2 (mem_union_left _ ha), by
      apply Finset.disjoint_left.mpr
      intro x hs hc
      exact (mem_sdiff.mp hc).2 (mem_union_right _ hs),
      by intro x; by_cases ha:x∈A <;> by_cases hs:x∈S <;> simp_all [A'],
      hA_closed,hA'closed,⟨u0,self_mem_compAvoiding hu0S⟩,hA'_ne⟩
    obtain ⟨w,hw⟩ := Finset.card_pos.mp (show 0 < S.card by omega)
    obtain ⟨f,hf⟩ := transitive w u0
    have dis (X Y : Finset V) (h : Disjoint X Y) : Disjoint (X.image f) (Y.image f) := by
      rw [Finset.disjoint_left]
      rintro x hx hy
      obtain ⟨u,hu,rfl⟩ := mem_image.mp hx
      obtain ⟨v,hv,he⟩ := mem_image.mp hy
      exact Finset.disjoint_left.mp h hu (f.injective he ▸ hv)
    have closedImage (X : Finset V) (h : ∀ x∈X, ∀ y, G.Adj x y → y∈X∪S) :
        ∀ x∈X.image f, ∀ y, G.Adj x y → y∈X.image f ∪ S.image f := by
      rintro x hx y hy
      obtain ⟨v,hv,rfl⟩ := mem_image.mp hx
      have edge : G.Adj v (f.symm y) := f.map_adj_iff.mp (by simpa using hy)
      rcases mem_union.mp (h v hv _ edge) with inX|inS
      · exact mem_union_left _ (mem_image.mpr ⟨f.symm y,inX,f.apply_symm_apply y⟩)
      · exact mem_union_right _ (mem_image.mpr ⟨f.symm y,inS,f.apply_symm_apply y⟩)
    let Q : Side := ⟨(A.image f,S.image f,A'.image f), dis A S (lm P),
      dis A A' (lr P), dis S A' (mr P), by
        intro y
        rcases allv P (f.symm y) with h|h|h
        · exact Or.inl (mem_image.mpr ⟨f.symm y,h,f.apply_symm_apply y⟩)
        · exact Or.inr (Or.inl (mem_image.mpr ⟨f.symm y,h,f.apply_symm_apply y⟩))
        · exact Or.inr (Or.inr (mem_image.mpr ⟨f.symm y,h,f.apply_symm_apply y⟩)),
      closedImage A hA_closed,closedImage A' hA'closed,(nl P).image _,(nr P).image _⟩
    have meet : ((left P)∩(mid Q)).Nonempty :=
      ⟨u0,mem_inter.mpr ⟨self_mem_compAvoiding hu0S,mem_image.mpr ⟨w,hw,hf⟩⟩⟩
    have hc (X : Finset V) : (X.image f).card = X.card := card_image_of_injective _ f.injective
    have bound := grid P Q hAcard hScard ((hc S).trans hScard)
      (by change a ≤ (A.image f).card; rw [hc,hAcard])
      (by change a ≤ (A'.image f).card; rw [hc]; exact hA'_card) meet
    have cut := hκ_min S0 hsep0
    have deg := degree u0
    omega
  intro u v
  have r : ReachAvoiding S0 u.val v.val := by
    by_contra h
    exact no ⟨u.val, v.val, u.property, v.property, h⟩
  obtain ⟨walk,h⟩ := r
  exact ⟨walk.induce _ h⟩

end LovaszDense.Watkins

/-! The bounded iron decomposition for dense vertex-transitive graphs, adapted
from Christofides, Hladký and Máthé, *Hamilton cycles in dense vertex-transitive
graphs*, J. Combin. Theory Ser. B 109 (2014), Section 4, Theorem 8. We use a
decreasing integer reciprocal-density parameter and transport the partition of
a representative block to the entire graph under its automorphism group. -/

namespace LovaszDensity
open SimpleGraph Finset

/-- Splitting the survivors of a disconnected deletion gives two sides large
enough to contain the closed surviving neighborhood of any vertex on them. -/
theorem separator_sides {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (S : Finset V) (cut : ¬(G.induce (Sᶜ : Finset V)).Preconnected) :
    ∃ A B : Finset V, Disjoint A B ∧ A∪B=Sᶜ ∧ A.Nonempty ∧ B.Nonempty ∧
      A.card≤ B.card ∧ G.minDegree+1≤ A.card+S.card ∧ G.minDegree+1≤ B.card+S.card ∧
      (∀ a∈A, ∀ b∈B, ∀ p : G.Walk a b, ∃ s∈S, s∈p.support) := by
  classical
  let U := Sᶜ
  let H := G.induce (U : Set V)
  obtain ⟨x,y,nr⟩ : ∃ x y, ¬H.Reachable x y := by
    simpa only [SimpleGraph.Preconnected,not_forall] using cut
  let A := U.filter fun a => ∃ h : a∈U, H.Reachable x ⟨a,h⟩
  let B := U \ A
  have reach {a : V} (ha : a∈A) : ∃ h : a∈U, H.Reachable x ⟨a,h⟩ :=
    (mem_filter.mp ha).2
  have no {b : V} (hb : b∈B) (h : b∈U) : ¬ H.Reachable x ⟨b,h⟩ :=
    fun he => (mem_sdiff.mp hb).2 (mem_filter.mpr ⟨h,h,he⟩)
  have na : A.Nonempty := ⟨x.val, mem_filter.mpr ⟨x.property,x.property,.rfl⟩⟩
  have nb : B.Nonempty := ⟨y.val, mem_sdiff.mpr ⟨y.property,fun h =>
    (reach h).elim (fun _ hr => nr hr)⟩⟩
  have dis : Disjoint A B := disjoint_sdiff
  have full : A∪B=U := by
    ext v
    simp only [B,mem_union,mem_sdiff]
    exact ⟨fun h => h.elim (fun a => (reach a).choose) And.left, fun h => or_iff_not_imp_left.mpr (fun hn => ⟨h,hn⟩)⟩
  have apart {a b : V} (ha : a∈A) (hb : b∈B) : ¬G.Adj a b := by
    intro adj
    obtain ⟨h,r⟩ := reach ha
    have h' := (mem_sdiff.mp hb).1
    exact no hb h' (r.trans (show H.Adj ⟨a,h⟩ ⟨b,h'⟩ from adj).reachable)
  have bound (C D : Finset V) (cv : C.Nonempty) (cov : C∪D=U)
      (sep : ∀ {a b : V}, a∈C → b∈D → ¬ G.Adj a b) : G.minDegree+1 ≤ C.card+S.card := by
    obtain ⟨z,hz⟩ := cv
    have subset : insert z (G.neighborFinset z) ⊆ C∪S := by
      intro w hw
      rcases mem_insert.mp hw with rfl|hn
      · exact mem_union_left _ hz
      by_cases hs : w∈S
      · exact mem_union_right _ hs
      have mem : w∈C∪D := cov ▸ mem_compl.mpr hs
      exact mem_union_left _ ((mem_union.mp mem).resolve_right fun h =>
        sep hz h ((G.mem_neighborFinset _ _).mp hn))
    have card := (card_le_card subset).trans (card_union_le ..)
    rw [card_insert_of_notMem (G.notMem_neighborFinset_self _),G.card_neighborFinset_eq_degree] at card
    exact (Nat.add_le_add_right (G.minDegree_le_degree z) 1).trans card
  have ba := bound A B na full (fun h k => apart h k)
  have bb := bound B A nb ((union_comm B A).trans full) (fun h k adj => apart k h adj.symm)
  have hit {a b : V} (ha : a∈A) (hb : b∈B) (p : G.Walk a b) : ∃ s∈S, s∈p.support := by
    by_contra! none
    have safe (v : V) (hv : v∈p.support) : v∈(U : Set V) :=
      mem_compl.mpr (fun h => none v h hv)
    obtain ⟨_,r⟩ := reach ha
    exact no hb (safe b p.end_mem_support) (r.trans (p.induce (U : Set V) safe).reachable)
  by_cases le : A.card≤ B.card
  · exact ⟨A,B,dis,full,na,nb,le,ba,bb,fun _ h _ k p => hit h k p⟩
  · refine ⟨B,A,dis.symm,(union_comm B A).trans full,nb,na,by omega,bb,ba,?_⟩
    intro b hb a ha p
    obtain ⟨s,hs,hp⟩ := hit ha hb p.reverse
    exact ⟨s,hs,by simpa only [Walk.support_reverse,List.mem_reverse] using hp⟩

end LovaszDensity

namespace LovaszIron
open Finset SimpleGraph

/-- Bounded vertex and edge deletions disconnect the surviving graph exactly
when its vertices can be partitioned into a small deleted set and two nonempty
sides of bounded crossing degree. The two deletion budgets are independent. -/
theorem iron_cut_iff {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (vBudget eBudget : ℕ) :
    (¬ ∀ (F : SimpleGraph V) [DecidableRel F.Adj] (S : Finset V),
      S.card ≤ vBudget → (∀ x, F.degree x ≤ eBudget) →
      ((G \ F).induce (Sᶜ : Finset V)).Preconnected) ↔
    ∃ S A B : Finset V, S.card ≤ vBudget ∧ Disjoint A B ∧ A ∪ B = Sᶜ ∧
      A.Nonempty ∧ B.Nonempty ∧ A.card ≤ B.card ∧
      (∀ a ∈ A, (G.neighborFinset a ∩ B).card ≤ eBudget) ∧
      (∀ b ∈ B, (G.neighborFinset b ∩ A).card ≤ eBudget) := by
  classical
  constructor
  · intro fail
    simp only [not_forall] at fail
    obtain ⟨F, instF, S, small, loss, cut⟩ := fail
    let := instF
    obtain ⟨A,B,dis,cov,na,nb,order,_,_,hit⟩ := LovaszDensity.separator_sides (G \ F) S cut
    have outside {x : V} (hx : x ∈ A ∪ B) : x ∉ S := mem_compl.mp (cov ▸ hx)
    have across {a b : V} (ha : a ∈ A) (hb : b ∈ B) (edge : G.Adj a b) : F.Adj a b := by
      by_contra h
      have live : (G \ F).Adj a b := ⟨edge,h⟩
      obtain ⟨s,hs,mem⟩ := hit a ha b hb live.toWalk
      rw [live.support_toWalk] at mem
      rcases List.mem_cons.mp mem with rfl | mem
      · exact outside (mem_union_left _ ha) hs
      · obtain rfl := List.mem_singleton.mp mem
        exact outside (mem_union_right _ hb) hs
    have bound {C : Finset V} (x : V) (forced : ∀ y ∈ C, G.Adj x y → F.Adj x y) :
        (G.neighborFinset x ∩ C).card ≤ eBudget := by
      have incl : G.neighborFinset x ∩ C ⊆ F.neighborFinset x := by
        intro y mem
        obtain ⟨adj,hc⟩ := mem_inter.mp mem
        exact (F.mem_neighborFinset ..).mpr (forced y hc ((G.mem_neighborFinset ..).mp adj))
      exact (card_le_card incl).trans (by simpa using loss x)
    exact ⟨S,A,B,small,dis,cov,na,nb,order,
      fun a ha => bound a (fun _ hb => across ha hb),
      fun b hb => bound b (fun _ ha e => (across ha hb e.symm).symm)⟩
  · rintro ⟨S,A,B,small,dis,cov,⟨a,ha⟩,⟨b,hb⟩,_,ab,ba⟩ robust
    let F : SimpleGraph V :=
      { Adj := fun x y => G.Adj x y ∧ ((x ∈ A ∧ y ∈ B) ∨ (x ∈ B ∧ y ∈ A))
        symm := ⟨fun _ _ h => ⟨h.1.symm,h.2.elim (fun h => Or.inr h.symm) (fun h => Or.inl h.symm)⟩⟩
        loopless := ⟨fun x h => G.loopless.irrefl x h.1⟩ }
    have bound (x : V) : F.degree x ≤ eBudget := by
      rw [← F.card_neighborFinset_eq_degree]
      by_cases hA : x ∈ A
      · refine (card_le_card (t := G.neighborFinset x ∩ B) ?_).trans (ab x hA)
        intro y h
        obtain ⟨edge,inAB | inBA⟩ := (F.mem_neighborFinset ..).mp h
        · exact mem_inter.mpr ⟨(G.mem_neighborFinset ..).mpr edge,inAB.2⟩
        · exact (disjoint_left.mp dis hA inBA.1).elim
      by_cases hB : x ∈ B
      · refine (card_le_card (t := G.neighborFinset x ∩ A) ?_).trans (ba x hB)
        intro y h
        obtain ⟨edge,inAB | inBA⟩ := (F.mem_neighborFinset ..).mp h
        · exact (hA inAB.1).elim
        · exact mem_inter.mpr ⟨(G.mem_neighborFinset ..).mpr edge,inBA.2⟩
      have empty : F.neighborFinset x = ∅ := eq_empty_iff_forall_notMem.mpr (by
        intro y h
        obtain ⟨_,fromA | fromB⟩ := (F.mem_neighborFinset ..).mp h
        · exact hA fromA.1
        · exact hB fromB.1)
      simp [empty]
    let U : Set V := ↑(Sᶜ : Finset V)
    let H := (G \ F).induce U
    have stay : ∀ {x y : U}, (H.Walk x y) → x.val ∈ A → y.val ∈ A := by
      intro x y p
      induction p with
      | nil => exact id
      | @cons x z y e p ih =>
        intro start
        have cover : z.val ∈ A ∪ B := cov.symm ▸ z.property
        exact ih ((mem_union.mp cover).resolve_right (fun endB => e.2 ⟨e.1,Or.inl ⟨start,endB⟩⟩))
    have conn := robust F S small bound
    let x : U := ⟨a,show a ∈ Sᶜ from cov ▸ mem_union_left _ ha⟩
    let y : U := ⟨b,show b ∈ Sᶜ from cov ▸ mem_union_right _ hb⟩
    obtain ⟨p⟩ := conn x y
    exact disjoint_left.mp dis (stay p ha) hb

end LovaszIron

namespace LovaszIron
open SimpleGraph Finset

/-- Intersect the first sides of two sparse cuts. A vertex on the first side
of one cut and the second side of the other has many neighbors in their
difference, giving a lower bound on the decrease in side size. -/
theorem intersect_sparse_cuts {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (S A B T C D : Finset V) (t m : ℕ)
    (smallS : S.card ≤ t) (smallT : T.card ≤ t)
    (dis' : Disjoint C D)
    (cov : A ∪ B = Sᶜ) (cov' : C ∪ D = Tᶜ)
    (ab : ∀ a ∈ A, (G.neighborFinset a ∩ B).card ≤ t)
    (ba : ∀ b ∈ B, (G.neighborFinset b ∩ A).card ≤ t)
    (cd : ∀ c ∈ C, (G.neighborFinset c ∩ D).card ≤ t)
    (dc : ∀ d ∈ D, (G.neighborFinset d ∩ C).card ≤ t)
    (overlap : (A ∩ C).Nonempty)
    (cross : ∃ x ∈ A, x ∈ D ∧ m + 4*t ≤ G.degree x) :
    ∃ U P Q : Finset V, U.card ≤ 2*t ∧ Disjoint P Q ∧ P ∪ Q = Uᶜ ∧
      P.Nonempty ∧ Q.Nonempty ∧ P.card + m ≤ A.card ∧
      (∀ p ∈ P, (G.neighborFinset p ∩ Q).card ≤ 2*t) ∧
      (∀ q ∈ Q, (G.neighborFinset q ∩ P).card ≤ 2*t) := by
  classical
  obtain ⟨x,hx,hd,deg⟩ := cross
  let N := G.neighborFinset x
  let U := S ∪ T
  let P := A ∩ C
  let Q := Uᶜ \ P
  have into {a : V} (h : a ∈ A ∪ B) : a ∉ S := mem_compl.mp (cov ▸ h)
  have into' {a : V} (h : a ∈ C ∪ D) : a ∉ T := mem_compl.mp (cov' ▸ h)
  have part {a : V} (h : a ∉ S) : a ∈ A ∨ a ∈ B :=
    mem_union.mp (show a ∈ A ∪ B from cov.symm ▸ mem_compl.mpr h)
  have part' {a : V} (h : a ∉ T) : a ∈ C ∨ a ∈ D :=
    mem_union.mp (show a ∈ C ∪ D from cov'.symm ▸ mem_compl.mpr h)
  have live (y : V) (h : y ∈ A ∪ B) (h' : y ∈ C ∪ D) : y ∈ Uᶜ :=
    mem_compl.mpr (fun hU => (mem_union.mp hU).elim (into h) (into' h'))
  have liveP : P ⊆ Uᶜ := fun _ h =>
    live _ (mem_union_left _ (mem_inter.mp h).1) (mem_union_left _ (mem_inter.mp h).2)
  have coverQ {y : V} (h : y ∈ Q) : y ∈ B ∨ y ∈ D := by
    obtain ⟨hu,hp⟩ := mem_sdiff.mp h
    have hs : y ∉ S := fun e => mem_compl.mp hu (mem_union_left _ e)
    have ht : y ∉ T := fun e => mem_compl.mp hu (mem_union_right _ e)
    rcases part hs with hA | hB
    · exact Or.inr ((part' ht).resolve_left fun hC => hp (mem_inter.mpr ⟨hA,hC⟩))
    · exact Or.inl hB
  have near : N ⊆ (A ∩ D) ∪ ((N ∩ B) ∪ S) ∪ ((N ∩ C) ∪ T) := by
    intro y hy
    by_cases hs : y ∈ S
    · exact mem_union_left _ (mem_union_right _ (mem_union_right _ hs))
    by_cases ht : y ∈ T
    · exact mem_union_right _ (mem_union_right _ ht)
    rcases part hs with l | r
    · rcases part' ht with l' | r'
      · exact mem_union_right _ (mem_union_left _ (mem_inter.mpr ⟨hy,l'⟩))
      · exact mem_union_left _ (mem_union_left _ (mem_inter.mpr ⟨l,r'⟩))
    · exact mem_union_left _ (mem_union_right _ (mem_union_left _ (mem_inter.mpr ⟨hy,r⟩)))
  have large : m ≤ (A ∩ D).card := by
    have total := (card_le_card near).trans (card_union_le ..)
    have sub := card_union_le (A ∩ D) ((N ∩ B) ∪ S)
    have left := card_union_le (N ∩ B) S
    have right := card_union_le (N ∩ C) T
    have one : (N ∩ B).card ≤ t := ab x hx
    have two : (N ∩ C).card ≤ t := dc x hd
    have nd : N.card = G.degree x := G.card_neighborFinset_eq_degree _
    omega
  have separate : Disjoint P (A ∩ D) := disjoint_left.mpr (fun _ h k =>
    disjoint_left.mp dis' (mem_inter.mp h).2 (mem_inter.mp k).2)
  have contained : P ∪ (A ∩ D) ⊆ A := by
    intro y h
    exact (mem_union.mp h).elim (fun h => (mem_inter.mp h).1) (fun h => (mem_inter.mp h).1)
  have shrink := card_le_card contained
  rw [card_union_of_disjoint separate] at shrink
  have xQ : x ∈ Q := mem_sdiff.mpr
    ⟨live _ (mem_union_left _ hx) (mem_union_right _ hd),
     fun k => disjoint_left.mp dis' (mem_inter.mp k).2 hd⟩
  refine ⟨U,P,Q,by have := card_union_le S T; dsimp [U]; omega,
    disjoint_sdiff,union_sdiff_of_subset liveP,overlap,⟨x,xQ⟩,by omega,?_,?_⟩
  · intro y h
    let M := G.neighborFinset y
    have incl : M ∩ Q ⊆ (M ∩ B) ∪ (M ∩ D) := by
      intro z hz
      obtain ⟨adj,hQ⟩ := mem_inter.mp hz
      exact (coverQ hQ).elim (fun k => mem_union_left _ (mem_inter.mpr ⟨adj,k⟩))
        (fun k => mem_union_right _ (mem_inter.mpr ⟨adj,k⟩))
    have bound := (card_le_card incl).trans (card_union_le ..)
    have bb : (M ∩ B).card ≤ t := ab y (mem_inter.mp h).1
    have dd : (M ∩ D).card ≤ t := cd y (mem_inter.mp h).2
    change (M ∩ Q).card ≤ 2*t
    omega
  · intro y h
    rcases coverQ h with hB | hD
    · have incl : G.neighborFinset y ∩ P ⊆ G.neighborFinset y ∩ A :=
        fun z hz => mem_inter.mpr ⟨(mem_inter.mp hz).1,(mem_inter.mp (mem_inter.mp hz).2).1⟩
      have b := (card_le_card incl).trans (ba y hB)
      omega
    · have incl : G.neighborFinset y ∩ P ⊆ G.neighborFinset y ∩ C :=
        fun z hz => mem_inter.mpr ⟨(mem_inter.mp hz).1,(mem_inter.mp (mem_inter.mp hz).2).2⟩
      have d := (card_le_card incl).trans (dc y hD)
      omega

end LovaszIron

namespace LovaszIron
open SimpleGraph Finset

/-- Iteratively intersect a side with an automorphic image until every
translate meeting that side avoids the opposite side. At most N iterations
suffice, with one doubling of the two cut budgets at each step. -/
theorem stabilize_sparse_cut {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (l m N : ℕ) (rounds : Fintype.card V ≤ N*m)
    (degree : ∀ x, m + 4 * (2^N*l) ≤ G.degree x)
    (start : ∃ S A B : Finset V, S.card ≤ l ∧ Disjoint A B ∧ A ∪ B = Sᶜ ∧
      A.Nonempty ∧ B.Nonempty ∧
      (∀ a ∈ A, (G.neighborFinset a ∩ B).card ≤ l) ∧
      (∀ b ∈ B, (G.neighborFinset b ∩ A).card ≤ l)) :
    ∃ S A B : Finset V, S.card ≤ 2^N*l ∧ Disjoint A B ∧ A ∪ B = Sᶜ ∧
      A.Nonempty ∧ B.Nonempty ∧
      (∀ a ∈ A, (G.neighborFinset a ∩ B).card ≤ 2^N*l) ∧
      (∀ b ∈ B, (G.neighborFinset b ∩ A).card ≤ 2^N*l) ∧
      (∀ (f : G ≃g G), (∃ a ∈ A, f a ∈ A) → ∀ b ∈ B, f b ∉ A) := by
  classical
  let Cut (t : ℕ) (S A B : Finset V) :=
    S.card ≤ t ∧ Disjoint A B ∧ A ∪ B = Sᶜ ∧ A.Nonempty ∧ B.Nonempty ∧
    (∀ a ∈ A, (G.neighborFinset a ∩ B).card ≤ t) ∧
    (∀ b ∈ B, (G.neighborFinset b ∩ A).card ≤ t)
  let Stable (A B : Finset V) :=
    ∀ (f : G ≃g G), (∃ a ∈ A, f a ∈ A) → ∀ b ∈ B, f b ∉ A
  by_contra none
  have seq (i : ℕ) (hi : i ≤ N) :
      ∃ S A B : Finset V, Cut (2^i*l) S A B ∧ A.card+i*m≤ Fintype.card V := by
    induction i with
    | zero =>
      obtain ⟨S,A,B,init⟩ := start
      exact ⟨S,A,B,by simpa [Cut] using init,by simpa using A.card_le_univ⟩
    | succ i ih =>
      obtain ⟨S,A,B,cur,measure⟩ := ih (by omega)
      obtain ⟨small,dis,cov,na,nb,ab,ba⟩ := cur
      let t := 2^i*l
      have bt : t ≤ 2^N*l := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) (by omega))
      by_cases stable : Stable A B
      · exact (none ⟨S,A,B,small.trans bt,dis,cov,na,nb,
          fun _ h => (ab _ h).trans bt,fun _ h => (ba _ h).trans bt,stable⟩).elim
      simp only [Stable,not_forall] at stable
      obtain ⟨f,⟨a,ha,hfa⟩,b,hb,hfb⟩ := stable
      have fb : f b ∈ A := not_not.mp hfb
      let e := f.toEquiv.toEmbedding
      let T := S.map e
      let C := A.map e
      let D := B.map e
      have mapm (K : Finset V) (x : V) : f x ∈ K.map e ↔ x ∈ K := mem_map' e
      have dis' : Disjoint C D := disjoint_left.mpr (by
        intro z hc hd
        obtain ⟨x,rfl⟩ := f.surjective z
        exact disjoint_left.mp dis ((mapm _ _).mp hc) ((mapm _ _).mp hd))
      have cov' : C ∪ D = Tᶜ := by
        ext z
        obtain ⟨x,rfl⟩ := f.surjective z
        simp only [C,D,T,mem_union,mem_compl,mapm]
        rw [← mem_union, cov, mem_compl]
      have mapN (x : V) : (G.neighborFinset x).map e = G.neighborFinset (f x) := by
        ext z
        obtain ⟨y,rfl⟩ := f.surjective z
        rw [mapm,G.mem_neighborFinset,G.mem_neighborFinset,f.map_adj_iff]
      have crosscard (x : V) (K : Finset V) :
          (G.neighborFinset (f x) ∩ K.map e).card = (G.neighborFinset x ∩ K).card := by
        rw [← mapN x,← map_inter,card_map]
      have transported (K L : Finset V) (h : ∀ k ∈ K, (G.neighborFinset k ∩ L).card ≤ t) :
          ∀ k ∈ K.map e, (G.neighborFinset k ∩ L.map e).card ≤ t := by
        intro z hz
        obtain ⟨x,rfl⟩ := f.surjective z
        rw [crosscard]
        exact h x ((mapm _ _).mp hz)
      have thick : m + 4*t ≤ G.degree (f b) := (Nat.add_le_add_left (Nat.mul_le_mul_left _ bt) _).trans (degree _)
      obtain ⟨U,P,Q,budget,pq,cover,pne,qne,shrink,forward,backward⟩ :=
        intersect_sparse_cuts G S A B T C D t m small (by simpa [T] using small)
          dis' cov cov' ab ba (transported _ _ ab) (transported _ _ ba)
          ⟨f a,mem_inter.mpr ⟨hfa,(mapm _ _).mpr ha⟩⟩
          ⟨f b,fb,(mapm _ _).mpr hb,thick⟩
      have dbl : 2^(i+1)*l = 2*t := by dsimp [t]; rw [pow_succ]; ring
      refine ⟨U,P,Q,?_,?_⟩
      · rw [dbl]
        exact ⟨budget,pq,cover,pne,qne,forward,backward⟩
      · rw [Nat.succ_mul]
        omega
  obtain ⟨S,A,B,cur,h⟩ := seq N le_rfl
  have pos := card_pos.mpr cur.2.2.2.1
  omega

end LovaszIron

namespace LovaszIron
open Finset SimpleGraph

/-- At a terminal partition in CHM Lemma 12, place each exceptional vertex
on the side where most of its surviving neighbors lie. This exposes an edge
cut with maximum degree at most three times the current budget. -/
theorem terminal_not_robust {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (vt : LovaszConjecture.IsVertexTransitive G)
    (S A B : Finset V) (t : ℕ) (hs : S.card≤ t) (apart : Disjoint A B)
    (cov : A∪B=Sᶜ) (na : A.Nonempty) (nb : B.Nonempty)
    (ab : ∀ a∈A,(G.neighborFinset a∩B).card≤ t)
    (ba : ∀ b∈B,(G.neighborFinset b∩A).card≤ t)
    (stable : ∀ (f : G ≃g G), (∃ a∈A,f a∈A) → ∀ b∈B,f b∉A) :
    ¬∀ (F : SimpleGraph V) [DecidableRel F.Adj], (∀ z,F.degree z≤3*t) → (G \ F).Preconnected := by
  classical
  let N := G.neighborFinset
  have abS {z} (mem : z∈A ∨ z∈B) : z∉S := mem_compl.mp (cov ▸ mem_union.mpr mem)
  have side (u : V) : (N u∩A).card≤2*t ∨ (N u∩B).card≤2*t := by
    by_contra! many
    obtain ⟨a,ha⟩ := na
    obtain ⟨f,hit⟩ := vt u a
    have avail (T : Finset V) (h : 2*t<(N u∩T).card) : ∃ w∈T,f w∈A := by
      by_contra! outside
      have sub : (N u∩T).map f.toEquiv.toEmbedding ⊆ S∪(N a∩B) := by
        intro z hz
        obtain ⟨w,hw,rfl⟩ := mem_map.mp hz
        by_cases exc : f w∈S
        · exact mem_union_left _ exc
        have span : f w∈A∪B := cov ▸ mem_compl.mpr exc
        have adj : G.Adj a (f w) := hit ▸ f.map_adj_iff.mpr ((G.mem_neighborFinset ..).mp (mem_inter.mp hw).1)
        exact mem_union_right _ (mem_inter.mpr ⟨(G.mem_neighborFinset ..).mpr adj,
          (mem_union.mp span).resolve_left (outside w (mem_inter.mp hw).2)⟩)
      have card := (card_le_card sub).trans (card_union_le ..)
      rw [card_map] at card
      have cross : (N a∩B).card≤ t := ab a ha
      omega
    obtain ⟨b,hb,fb⟩ := avail B many.2
    exact stable f (avail A many.1) b hb fb
  let P := S.filter fun u => (N u∩B).card≤2*t
  let X := A∪P
  let Y := B∪(S\P)
  have dis : Disjoint X Y := by
    apply Finset.disjoint_left.mpr
    intro z x y
    rcases mem_union.mp x with a|p <;> rcases mem_union.mp y with b|s
    · exact Finset.disjoint_left.mp apart a b
    · exact abS (Or.inl a) (mem_sdiff.mp s).1
    · exact abS (Or.inr b) (mem_filter.mp p).1
    · exact (mem_sdiff.mp s).2 p
  have all : X∪Y=univ := by
    apply eq_univ_of_forall
    intro z
    by_cases exc : z∈S
    · by_cases p : z∈P
      · exact mem_union_left _ (mem_union_right _ p)
      · exact mem_union_right _ (mem_union_right _ (mem_sdiff.mpr ⟨exc,p⟩))
    · have span : z∈A∪B := cov ▸ mem_compl.mpr exc
      exact (mem_union.mp span).elim (fun h => mem_union_left _ (mem_union_left _ h))
        (fun h => mem_union_right _ (mem_union_left _ h))
  have extend (z : V) (T U : Finset V) (us : U⊆S) (bound : (N z∩T).card≤2*t) :
      (N z∩(T∪U)).card≤3*t := by
    have sub : N z∩(T∪U) ⊆ (N z∩T)∪S := by
      intro w hw
      obtain ⟨adj,mem⟩ := mem_inter.mp hw
      exact (mem_union.mp mem).elim (fun h => mem_union_left _ (mem_inter.mpr ⟨adj,h⟩)) (fun h => mem_union_right _ (us h))
    have := (card_le_card sub).trans (card_union_le ..)
    omega
  have bdX (x) (hx : x∈X) : (N x∩Y).card≤3*t := by
    apply extend x B (S\P) sdiff_subset
    rcases mem_union.mp hx with a|p
    · exact (ab x a).trans (by omega)
    · exact (mem_filter.mp p).2
  have bdY (y) (hy : y∈Y) : (N y∩X).card≤3*t := by
    apply extend y A P (filter_subset ..)
    rcases mem_union.mp hy with b|s
    · exact (ba y b).trans (by omega)
    · exact (side y).resolve_right (fun h => (mem_sdiff.mp s).2 (mem_filter.mpr ⟨(mem_sdiff.mp s).1,h⟩))
  have xy : X.Nonempty := na.mono subset_union_left
  have yy : Y.Nonempty := nb.mono subset_union_left
  have fail := (iron_cut_iff G 0 (3*t)).mpr (by
    by_cases le : X.card≤ Y.card
    · exact ⟨∅,X,Y,by simp,dis,by simpa using all,xy,yy,le,bdX,bdY⟩
    · exact ⟨∅,Y,X,by simp,dis.symm,by simpa [union_comm] using all,yy,xy,by omega,bdY,bdX⟩)
  intro robust
  apply fail
  intro F dec D sz loss
  have eq : D=∅ := card_eq_zero.mp (by omega)
  subst D
  have h := robust F loss
  have e : (((∅ : Finset V)ᶜ : Finset V) : Set V) = Set.univ := by ext; simp
  rw [e]
  exact (SimpleGraph.induceUnivIso (G \ F)).preconnected_iff.mpr h

end LovaszIron

namespace LovaszIron
open SimpleGraph Finset

/-- A quantitative form of Christofides–Hladký–Máthé, Lemma 12. Edge
robustness of a dense transitive graph also permits simultaneous deletion of
vertices, with the density controlling the number of cut refinements. -/
theorem robust_to_iron {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (vt : LovaszConjecture.IsVertexTransitive G)
    (l m N : ℕ) (rounds : Fintype.card V ≤ N*m) (degree : ∀ x,m + 4*(2^N*l) ≤ G.degree x)
    (robust : ∀ (F : SimpleGraph V) [DecidableRel F.Adj],
      (∀ z, F.degree z ≤ 3*(2^N*l)) → (G \ F).Preconnected) :
    ∀ (F : SimpleGraph V) [DecidableRel F.Adj] (S : Finset V),
      S.card ≤ l → (∀ z,F.degree z ≤ l) → ((G \ F).induce (Sᶜ : Finset V)).Preconnected := by
  classical
  by_contra fail
  obtain ⟨S,A,B,s,dis,cov,na,nb,_,ab,ba⟩ := (iron_cut_iff G l l).mp fail
  obtain ⟨T,C,D,t,apart,cover,nc,nd,cd,dc,stable⟩ :=
    stabilize_sparse_cut G l m N rounds degree ⟨S,A,B,s,dis,cov,na,nb,ab,ba⟩
  exact terminal_not_robust G vt T C D (2^N*l) t apart cover nc nd cd dc stable robust

/-- In density at least 1/k, an edge budget r yields an iron budget depending
only on r, the minimum degree d, and k. In particular, proportional edge
robustness gives proportional iron connectivity for fixed density. -/
theorem robust_to_iron_density {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (vt : LovaszConjecture.IsVertexTransitive G)
    (k d r : ℕ) (d2 : 2 ≤ d) (density : Fintype.card V ≤ k*d)
    (degree : ∀ x, d ≤ G.degree x)
    (robust : ∀ (F : SimpleGraph V) [DecidableRel F.Adj],
      (∀ z,F.degree z ≤ r) → (G \ F).Preconnected) :
    let l := min (d/(8*2^(3*k))) (r/(3*2^(3*k)))
    ∀ (F : SimpleGraph V) [DecidableRel F.Adj] (S : Finset V),
      S.card ≤ l → (∀ z,F.degree z ≤ l) → ((G \ F).induce (Sᶜ : Finset V)).Preconnected := by
  intro l
  have cut_le {b h : ℕ} (hl : l ≤ h / (b*2^(3*k))) : b*(2^(3*k)*l) ≤ h := by
    rw [← Nat.mul_assoc, Nat.mul_comm]
    exact (Nat.mul_le_mul_right _ hl).trans (Nat.div_mul_le_self ..)
  have eight : 8*(2^(3*k)*l) ≤ d := cut_le (min_le_left ..)
  have three : 3*(2^(3*k)*l) ≤ r := cut_le (min_le_right ..)
  apply robust_to_iron G vt l (d/2) (3*k)
  · apply density.trans
    have dd : d ≤ 3*(d/2) := by omega
    calc k*d ≤ k*(3*(d/2)) := Nat.mul_le_mul_left _ dd
         _ = 3*k*(d/2) := by ring
  · intro x
    exact (show d/2 + 4*(2^(3*k)*l) ≤ d by omega).trans (degree x)
  · intro F _ loss
    exact robust F (fun x => (loss x).trans three)

end LovaszIron

namespace LovaszIron
open SimpleGraph Finset

/-- The components of a disconnected graph that is invariant under every
automorphism of G give a nontrivial invariant partition of its vertices. -/
theorem invariant_components {V : Type*} [Fintype V] [DecidableEq V] (G H : SimpleGraph V)
    [DecidableRel H.Adj] (stable : ∀ (f : G ≃g G) (x y : V), H.Adj (f x) (f y) ↔ H.Adj x y)
    (split : ¬H.Preconnected) :
    ∃ (q : ℕ) (c : V → Fin q), 2≤ q ∧ Function.Surjective c ∧
      (∀ i, H.minDegree+1≤(univ.filter fun x => c x=i).card) ∧
      q*(H.minDegree+1)≤ Fintype.card V ∧
      (∀ (f : G ≃g G) (x y : V), c (f x)=c (f y) ↔ c x=c y) ∧
      (∀ x y, c x=c y ↔ H.Reachable x y) := by
  classical
  let := Fintype.ofFinite H.ConnectedComponent
  let q := Fintype.card H.ConnectedComponent
  let e : H.ConnectedComponent ≃ Fin q := Fintype.equivFin _
  let c (x : V) := e (H.connectedComponentMk x)
  have char (x y : V) : c x=c y ↔ H.Reachable x y :=
    e.injective.eq_iff.trans ConnectedComponent.eq
  have sur : Function.Surjective c := by
    intro i
    obtain ⟨C, rfl⟩ := e.surjective i
    exact C.ind (fun x => ⟨x,rfl⟩)
  obtain ⟨u,v,h⟩ : ∃ u v, ¬H.Reachable u v := by
    simpa only [Preconnected,not_forall] using split
  have nontriv : 2≤ q := by
    by_contra! small
    exact h ((char _ _).mp (Fin.ext (by have := (c u).isLt; have := (c v).isLt; omega)))
  have vol (i : Fin q) : H.minDegree+1≤(univ.filter fun x => c x=i).card := by
    obtain ⟨x,rfl⟩ := sur i
    have subset : insert x (H.neighborFinset x) ⊆ univ.filter fun z => c z=c x := by
      intro z hz
      apply mem_filter.mpr
      refine ⟨mem_univ _,?_⟩
      rcases mem_insert.mp hz with rfl|hw
      · rfl
      · exact (char _ _).mpr ((H.mem_neighborFinset ..).mp hw).symm.reachable
    have count := card_le_card subset
    rw [card_insert_of_notMem (H.notMem_neighborFinset_self _),H.card_neighborFinset_eq_degree] at count
    exact (Nat.add_le_add_right (H.minDegree_le_degree x) 1).trans count
  have total := Finset.sum_le_sum (s:=univ) (fun i _ => vol i)
  have fiber := Finset.card_eq_sum_card_fiberwise (s:=(univ : Finset V)) (t:=(univ : Finset (Fin q)))
    (f:=c) (fun _ _ => mem_univ _)
  rw [←fiber] at total
  refine ⟨q,c,nontriv,sur,vol,by simpa using total,?_,char⟩
  intro f x y
  let h : H ≃g H := ⟨f.toEquiv,stable f _ _⟩
  exact (char _ _).trans (h.reachable_iff.trans (char _ _).symm)

end LovaszIron

namespace LovaszIron
open SimpleGraph Finset

/-- A transitive automorphism group permutes the parts of an invariant
partition transitively, and the induced graph on every part is transitive. -/
theorem block_isomorphisms {V I : Type*} (G : SimpleGraph V) (c : V → I)
    (sur : Function.Surjective c) (transitive : ∀ x y : V, ∃ f : G ≃g G, f x=y)
    (invariant : ∀ (f : G ≃g G) x y, c (f x)=c (f y) ↔ c x=c y) :
    let K (i : I) := G.induce {x | c x=i}
    (∀ i j, Nonempty (K i ≃g K j)) ∧
    (∀ i, ∀ x y : {v // c v=i}, ∃ f : K i ≃g K i, f x=y) := by
  intro K
  have bij (f : G ≃g G) (x : V) : Set.BijOn f {v | c v=c x} {v | c v=c (f x)} := by
    refine ⟨fun v h => (invariant f v x).mpr h,f.injective.injOn,?_⟩
    intro w h
    refine ⟨f.symm w,(invariant f _ _).mp ?_,by simp⟩
    simpa using (show c w=c (f x) from h)
  constructor
  · intro i j
    obtain ⟨x,rfl⟩ := sur i
    obtain ⟨y,rfl⟩ := sur j
    obtain ⟨f,hf⟩ := transitive x y
    subst y
    exact ⟨f.induce (bij f x)⟩
  · intro i x y
    obtain ⟨f,h⟩ := transitive x.val y.val
    have bf : Set.BijOn f {v | c v=i} {v | c v=i} := by
      simpa only [x.property,h,y.property] using bij f x.val
    exact ⟨f.induce bf,Subtype.ext h⟩

end LovaszIron

namespace LovaszIron
open SimpleGraph Finset

/-- A vertex with more than k neighbors robustly connected to y is itself
robustly connected to y, since an edge to at least one neighbor survives. -/
theorem island_absorption {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (k : ℕ) :
    let R (x y : V) := ∀ (F : SimpleGraph V) [DecidableRel F.Adj],
      (∀ z, F.degree z≤ k) → (G \ F).Reachable x y
    ∀ (T : Finset V) (x y : V), (∀ z∈T, R z y) →
      k < (G.neighborFinset x ∩ T).card → R x y := by
  intro R T x y same many F _ loss
  have strict : (F.neighborFinset x).card < (G.neighborFinset x ∩ T).card :=
    (loss x).trans_lt many
  obtain ⟨z,good,retained⟩ := exists_mem_notMem_of_card_lt_card strict
  obtain ⟨adj,mem⟩ := mem_inter.mp good
  have step : (G \ F).Adj x z :=
    ⟨(G.mem_neighborFinset ..).mp adj,fun edge => retained ((F.mem_neighborFinset ..).mpr edge)⟩
  exact step.reachable.trans (same z mem F loss)

/-- If each outside class attracts at most k neighbors of x, the induced
degree in the class of x loses at most (q−1)k. -/
theorem island_degree {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {q k : ℕ} (c : V → Fin q) (x : V)
    (outside : ∀ j, c x≠j → (G.neighborFinset x ∩ (univ.filter fun v => c v=j)).card≤ k) :
    let U : Set V := {v | c v=c x}
    let K := G.induce U
    G.degree x ≤ K.degree (⟨x,by simp [U]⟩ : U) + (q-1)*k := by
  intro U K
  let B (j : Fin q) := (G.neighborFinset x).filter (fun y => c y=j)
  have eq (j : Fin q) : G.neighborFinset x ∩ (univ.filter fun v => c v=j) = B j := by
    ext v; simp [B]
  have total := Finset.card_eq_sum_card_fiberwise (s:=G.neighborFinset x) (t:=(univ : Finset (Fin q)))
    (f:=c) (fun _ _ => mem_univ _)
  have count : K.degree (⟨x,by simp [U]⟩ : U) = (B (c x)).card := by
    have h := congrArg Finset.card (G.map_neighborFinset_induce (s:=(U : Set V)) ⟨x,by simp [U]⟩)
    simp only [card_map, SimpleGraph.card_neighborFinset_eq_degree] at h
    rw [show U.toFinset=univ.filter (fun v => c v=c x) by ext; simp [U],eq] at h
    exact h
  have bound := Finset.sum_le_sum (s:=univ.erase (c x)) (f:=fun j => (B j).card)
    (g:=fun _ => k) (fun j hj => (eq j) ▸ outside j (Ne.symm (mem_erase.mp hj).1))
  have split := sum_erase_add (univ : Finset (Fin q)) (fun j => (B j).card) (mem_univ (c x))
  have budget : (univ.erase (c x)).card=q-1 := by simp
  simp only [sum_const,nsmul_eq_mul,budget,Nat.cast_id] at bound
  change G.degree x=∑j,(B j).card at total
  omega

end LovaszIron

namespace LovaszIron
open SimpleGraph Finset

/-- Robust islands are the equivalence classes for reachability after every
allowed local edge deletion. When that relation is nontrivial, it gives
isomorphic transitive parts with few neighbors in each other part. -/
theorem robust_islands {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (k : ℕ) (transitive : ∀ x y : V, ∃ f : G ≃g G, f x=y) :
    let R (x y : V) := ∀ (F : SimpleGraph V) [DecidableRel F.Adj],
      (∀ z,F.degree z≤ k) → (G \ F).Reachable x y
    (∀ x y, R x y) ∨ ∃ (q : ℕ) (c : V → Fin q),
      2≤ q ∧ Function.Surjective c ∧ (∀ x y, c x=c y ↔ R x y) ∧
      (∀ (f : G ≃g G) x y, c (f x)=c (f y) ↔ c x=c y) ∧
      (∀ x j, c x≠j → (G.neighborFinset x ∩ (univ.filter fun v => c v=j)).card≤ k) ∧
      (∀ x, G.degree x≤(G.induce {y | c y=c x}).degree (⟨x,rfl⟩ : {y // c y=c x})+(q-1)*k) ∧
      (∀ i j, Nonempty (G.induce {v | c v=i} ≃g G.induce {v | c v=j})) ∧
      (∀ i, ∀ x y : {v // c v=i}, ∃ f : G.induce {v | c v=i} ≃g G.induce {v | c v=i}, f x=y) := by
  classical
  intro R
  by_cases universal : ∀ x y,R x y
  · exact Or.inl universal
  right
  let J : SimpleGraph V := {
    Adj x y := x≠y ∧ R x y
    symm := ⟨fun x y h => ⟨Ne.symm h.1,fun F _ loss => (h.2 F loss).symm⟩⟩
    loopless := ⟨fun x h => h.1 rfl⟩ }
  have jiff (x y : V) : J.Reachable x y ↔ R x y := by
    constructor
    · rintro ⟨p⟩ F inst loss
      induction p with
      | nil => exact .rfl
      | cons h p ih => exact (h.2 F loss).trans ih
    · intro r
      by_cases eq : x=y
      · subst y
        exact .rfl
      · exact (show J.Adj x y from ⟨eq,r⟩).reachable
  have mapR (f : G ≃g G) (x y : V) (r : R x y) : R (f x) (f y) := by
    intro F inst loss
    let F' := F.comap f
    let e : F' ≃g F := Iso.comap f.toEquiv F
    have bound (z : V) : F'.degree z≤ k := (e.degree_eq z) ▸ loss (f z)
    let h : (G \ F') →g (G \ F) :=
      ⟨f,fun edge => ⟨f.map_adj_iff.mpr edge.1,edge.2⟩⟩
    exact (r F' bound).map h
  have stable (f : G ≃g G) (x y : V) : J.Adj (f x) (f y) ↔ J.Adj x y := by
    change (f x≠f y ∧ R (f x) (f y)) ↔ (x≠y ∧ R x y)
    rw [f.injective.ne_iff]
    exact and_congr_right fun _ => ⟨fun r => by simpa using mapR f.symm _ _ r,mapR f x y⟩
  have split : ¬ J.Preconnected := fun j => universal (fun x y => (jiff _ _).mp (j x y))
  obtain ⟨q,c,many,sur,_,_,inv,lab⟩ := invariant_components G J stable split
  have cls (x y : V) : c x=c y ↔ R x y := (lab x y).trans (jiff x y)
  have outside (x : V) (j : Fin q) (diff : c x≠j) :
      (G.neighborFinset x ∩ (univ.filter fun v => c v=j)).card≤ k := by
    by_contra! extra
    obtain ⟨v,rfl⟩ := sur j
    apply diff
    exact (cls x v).mpr (island_absorption G k _ x v
      (fun z hz => (cls z v).mp ((mem_filter.mp hz).2)) extra)
  have maps := block_isomorphisms G c sur transitive inv
  exact ⟨q,c,many,sur,cls,inv,outside,fun x => island_degree G c x (outside x),maps⟩

end LovaszIron

namespace LovaszIron
open SimpleGraph Finset

/-- The degree-squared mass of all two-step walks starting at x is carried
either by its robust block or by pairs with at most twice the deletion budget
in common neighbors. -/
theorem robust_fiber_bound {V I : Type*} [Fintype V] [DecidableEq V] [DecidableEq I]
    (G : SimpleGraph V) [DecidableRel G.Adj] (d k : ℕ) (regular : G.IsRegularOfDegree d)
    (c : V → I) (x : V) :
    let R (x y : V) := ∀ (F : SimpleGraph V) [DecidableRel F.Adj],
      (∀ z,F.degree z≤ k) → (G \ F).Reachable x y
    (∀ x y, R x y → c x=c y) →
      let m := (univ.filter fun y => c y=c x).card
      d*d ≤ d*m+2*k*(Fintype.card V-m) := by
  intro R same m
  classical
  let N := G.neighborFinset x
  let common (y : V) := (N ∩ G.neighborFinset y).card
  have formula (y : V) : common y = ∑ z ∈ N, (if G.Adj z y then 1 else 0 : ℕ) := by
    dsimp only [common]
    rw [Finset.sum_boole]
    congr 1
    ext z
    simp [G.adj_comm]
  have total : (∑ y,common y)=d*d := by
    simp_rw [formula]
    rw [Finset.sum_comm]
    simp only [Finset.sum_boole]
    simp_rw [← SimpleGraph.neighborFinset_eq_filter,G.card_neighborFinset_eq_degree,regular.degree_eq]
    simp [N,regular.degree_eq]
  let A := univ.filter (fun y => c y=c x)
  have close {y : V} (large : 2*k< common y) : R x y := by
    intro F inst loss
    let bad := F.neighborFinset x ∪ F.neighborFinset y
    have limited : bad.card≤2*k :=
      (card_union_le ..).trans (by change F.degree x+F.degree y≤2*k; have := loss x; have := loss y; omega)
    obtain ⟨z,hz,safe⟩ := exists_mem_notMem_of_card_lt_card (limited.trans_lt large)
    obtain ⟨sx,sy⟩ := mem_inter.mp hz
    have notF : z∉F.neighborFinset x ∧ z∉F.neighborFinset y := by simpa [bad,not_or] using safe
    have xz : (G \ F).Adj x z :=
      ⟨(G.mem_neighborFinset ..).mp sx, fun h => notF.1 ((F.mem_neighborFinset ..).mpr h)⟩
    have yz : (G \ F).Adj y z :=
      ⟨(G.mem_neighborFinset ..).mp sy, fun h => notF.2 ((F.mem_neighborFinset ..).mpr h)⟩
    exact xz.reachable.trans yz.symm.reachable
  have upper (y : V) : common y ≤ (if y∈A then d else 2*k) := by
    by_cases hy : y∈A
    · rw [if_pos hy]
      exact (card_le_card (Finset.inter_subset_left : N ∩ G.neighborFinset y ⊆ N)).trans (regular.degree_eq x).le
    · rw [if_neg hy]
      by_contra! hi
      exact hy (mem_filter.mpr ⟨mem_univ _,(same x y (close hi)).symm⟩)
  have bound := Finset.sum_le_sum (s:=univ) (fun y _ => upper y)
  rw [total] at bound
  have inside : univ.filter (fun v => v∈A)=A := by ext; simp
  have out : univ.filter (fun v => v∉A)=Aᶜ := by ext; simp
  simpa only [Finset.sum_ite,inside,out,Finset.sum_const,nsmul_eq_mul,Finset.card_compl,
    Nat.cast_id,Nat.mul_comm] using bound

end LovaszIron

namespace LovaszIron
open SimpleGraph Finset

/-- Density improves in every proper robust-island part. The block size and
the surviving degree both retain at least three quarters of the old degree,
while each proper part has at most half the old number of vertices. -/
theorem density_increment {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (d k t : ℕ) (reg : G.IsRegularOfDegree d)
    (transitive : ∀ x y : V, ∃ f : G ≃g G, f x=y) (kpos : 0< k)
    (dense : Fintype.card V≤ k*d) (budget : 8*k^2*t≤ Fintype.card V) :
    let R (x y : V) := ∀ (F : SimpleGraph V) [DecidableRel F.Adj],
      (∀ z,F.degree z≤ t) → (G \ F).Reachable x y
    (∀ x y, R x y) ∨ ∃ (q m : ℕ) (c : V → Fin q),
      2≤ q ∧ q≤2*k ∧ Function.Surjective c ∧ Fintype.card V=q*m ∧ 3*d≤4*m ∧
      (∀ i, (univ.filter fun x => c x=i).card=m) ∧
      (∀ x, 3*d≤4*(G.induce {y | c y=c x}).degree (⟨x,rfl⟩ : {y // c y=c x})) ∧
      (∀ x y, c x=c y ↔ R x y) ∧
      (∀ (f : G ≃g G) x y, c (f x)=c (f y) ↔ c x=c y) ∧
      (∀ i j, Nonempty (G.induce {v | c v=i} ≃g G.induce {v | c v=j})) ∧
      (∀ i, ∀ x y : {v // c v=i}, ∃ f : G.induce {v | c v=i} ≃g G.induce {v | c v=i}, f x=y) := by
  classical
  intro R
  rcases robust_islands G t transitive with all|⟨q,c,two,sur,cls,inv,_,loss,iso,vt⟩
  · exact Or.inl all
  right
  obtain ⟨x,hx⟩ := sur (⟨0,by omega⟩ : Fin q)
  let n := Fintype.card V
  let m := (univ.filter fun y => c y=c x).card
  have : Nonempty V := ⟨x⟩
  have npos : 0< n := Fintype.card_pos
  have dpos : 0< d := by
    apply Nat.pos_of_ne_zero
    intro zero
    rw [zero,Nat.mul_zero] at dense
    exact (Nat.not_le_of_lt npos) dense
  have same (i : Fin q) : (univ.filter fun y => c y=i).card=m := by
    obtain ⟨e⟩ := iso i (c x)
    simpa only [Fintype.card_subtype,Set.mem_ofPred_eq,m] using Fintype.card_congr e.toEquiv
  have size : n=q*m := by
    simpa only [card_univ,same,Finset.sum_const,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] using
      (Finset.card_eq_sum_card_fiberwise (s:=(univ : Finset V)) (t:=(univ : Finset (Fin q))) (f:=c)
        (fun _ _ => mem_univ _))
  have kd : 8*t*k ≤ d := Nat.le_of_mul_le_mul_left
    (show k*(8*t*k)≤ k*d by simpa only [pow_two,Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using budget.trans dense) kpos
  have nt : 8*t*n≤ d*d := calc
    8*t*n ≤ 8*t*(k*d) := Nat.mul_le_mul_left _ dense
    _ = (8*t*k)*d := (Nat.mul_assoc ..).symm
    _ ≤ d*d := Nat.mul_le_mul_right _ kd
  have mass := robust_fiber_bound G d t reg c x (fun a b h => (cls a b).mpr h)
  change d*d≤ d*m+2*t*(n-m) at mass
  have crude := mass.trans (Nat.add_le_add_left (Nat.mul_le_mul_left (2*t) (Nat.sub_le n m)) (d*m))
  have big : 3*d≤4*m := Nat.le_of_mul_le_mul_left (show d*(3*d)≤ d*(4*m) by nlinarith) dpos
  have blocks : q≤2*k := by
    have qd : q*d ≤ q*(2*m) := Nat.mul_le_mul_left q (by omega)
    refine Nat.le_of_mul_le_mul_right (c:=d) ?_ dpos
    calc
      q*d ≤ 2*n := by simpa [size,Nat.mul_left_comm,Nat.mul_assoc] using qd
      _ ≤ 2*k*d := by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left 2 dense
  have lost : 4*((q-1)*t)≤ d := calc
    _ ≤ 4*((2*k)*t) := Nat.mul_le_mul_left 4 (Nat.mul_le_mul_right t (show q-1≤2*k by omega))
    _ = 8*t*k := by ring
    _ ≤ d := kd
  refine ⟨q,m,c,two,blocks,sur,size,big,same,?_,cls,inv,iso,vt⟩
  intro y
  have l := loss y
  rw [reg.degree_eq] at l
  omega

end LovaszIron

namespace LovaszBlocks
open SimpleGraph

/-- Extend an invariant partition of one representative block to the whole
graph. The refined label decodes as the original block and its inner label;
every refined induced graph is isomorphic to the corresponding inner graph. -/
theorem refine_partition {V : Type*} (G : SimpleGraph V) {q r : ℕ}
    (p : V→Fin q) (sur : Function.Surjective p) (root : Fin q)
    (trans : LovaszConjecture.IsVertexTransitive G)
    (stable : ∀ (f : G ≃g G) (x y : V), p (f x)=p (f y) ↔ p x=p y)
    (j : {v : V // p v=root} → Fin r) (jsur : Function.Surjective j)
    (localStable : ∀ (g : G.induce {v | p v=root} ≃g G.induce {v | p v=root}) a b,
      j (g a)=j (g b) ↔ j a=j b) :
    ∃ c : V→Fin (q*r), Function.Surjective c ∧
      (∀ (f : G ≃g G) (x y : V), c (f x)=c (f y) ↔ c x=c y) ∧
      (∀ v, (finProdFinEquiv.symm (c v)).1=p v) ∧
      (∀ b : Fin (q*r), Nonempty
        (G.induce {v | c v=b} ≃g (G.induce {v | p v=root}).induce
          {u | j u=(finProdFinEquiv.symm b).2})) := by
  classical
  let X (i : Fin q) := {v : V // p v=i}
  let K (i : Fin q) := G.induce {v | p v=i}
  have cut (i k) (f : G≃gG) (x : X i) (hit : p (f x.val)=k) :
      ∃ T : K i ≃g K k, ∀ u : X i, (T u).val=f u.val := by
    have agree (v : V) : p v=i ↔ p (f v)=k := by
      calc
        p v=i ↔ p v=p x.val := by rw [x.property]
        _ ↔ p (f v)=p (f x.val) := (stable f _ _).symm
        _ ↔ p (f v)=k := by rw [hit]
    let e : X i ≃ X k := f.toEquiv.subtypeEquiv agree
    let T : K i ≃g K k := ⟨e,by intro a b; exact f.map_adj_iff⟩
    exact ⟨T,fun _ => rfl⟩
  have ident (i) : Nonempty (K i ≃g K root) := by
    obtain ⟨x,hx⟩ := sur i
    obtain ⟨z,hz⟩ := sur root
    obtain ⟨f,eq⟩ := trans x z
    obtain ⟨T,_⟩ := cut i root f ⟨x,hx⟩ ((congrArg p eq).trans hz)
    exact ⟨T⟩
  let h (i) : K i ≃g K root := (ident i).some
  let E : Fin q × Fin r ≃ Fin (q*r) := finProdFinEquiv
  let c (v : V) := E (p v,j (h (p v) ⟨v,rfl⟩))
  have val (i) (a : X i) : c a.val=E (i,j (h i a)) := by
    obtain ⟨v,rfl⟩ := a
    rfl
  have forward (f : G ≃g G) (u v : V) (equal : c u=c v) : c (f u)=c (f v) := by
    have par := congrArg Prod.fst (E.injective equal)
    change p u=p v at par
    let i := p u
    let k := p (f u)
    let a : X i := ⟨u,rfl⟩
    let b : X i := ⟨v,par.symm⟩
    obtain ⟨T,hT⟩ := cut i k f a rfl
    have eq' : E (i,j (h i a))=E (i,j (h i b)) := (val i a).symm.trans (equal.trans (val i b))
    have same := congrArg Prod.snd (E.injective eq')
    let auto : K root ≃g K root := (h i).symm.trans (T.trans (h k))
    have transported := (localStable auto (h i a) (h i b)).2 same
    change j (h k (T ((h i).symm ((h i) a))))=j (h k (T ((h i).symm ((h i) b)))) at transported
    simp only [RelIso.symm_apply_apply] at transported
    change c (f a.val)=c (f b.val)
    rw [←hT a,←hT b,val,val,transported]
  refine ⟨c,?_,?_,?_,?_⟩
  · intro v
    obtain ⟨⟨i,s⟩,rfl⟩ := E.surjective v
    obtain ⟨z,hz⟩ := jsur s
    refine ⟨((h i).symm z).val,?_⟩
    rw [val,RelIso.apply_symm_apply,hz]
  · intro f u v
    refine ⟨fun eq => ?_,forward f u v⟩
    simpa using forward f.symm (f u) (f v) eq
  · intro v
    change (E.symm (E _)).1=p v
    rw [E.symm_apply_apply]
  · intro v
    obtain ⟨⟨i,s⟩,rfl⟩ := E.surjective v
    change Nonempty (G.induce {v | c v=E (i,s)} ≃g
      (K root).induce {u | j u=(E.symm (E (i,s))).2})
    rw [E.symm_apply_apply]
    let S := {v : V | c v=E (i,s)}
    let U := {u : X root | j u=s}
    have ip (v : S) : p v.val=i := congrArg Prod.fst (E.injective v.property)
    let inParent (v : S) : X i := ⟨v.val,ip v⟩
    have inner (v : S) : j (h i (inParent v))=s := by
      have eq := (val i (inParent v)).symm.trans v.property
      exact congrArg Prod.snd (E.injective eq)
    let into (v : S) : U := ⟨h i (inParent v),inner v⟩
    let back (z : U) : S := ⟨((h i).symm z.val).val,by
      change c ((h i).symm z.val).val=E (i,s)
      rw [val,RelIso.apply_symm_apply,show j z.val=s from z.property]⟩
    let e : S ≃ U :=
      { toFun := into
        invFun := back
        left_inv := fun v => Subtype.ext (congrArg (fun a : X i => a.val) ((h i).symm_apply_apply (inParent v)))
        right_inv := fun z => Subtype.ext ((h i).apply_symm_apply z.val) }
    exact ⟨⟨e,by intro a b; exact (h i).map_adj_iff⟩⟩

end LovaszBlocks

namespace LovaszBlocks

/-- Restricting to any one of at least two equal blocks increases the relative
degree, and decreases an integer reciprocal-density parameter. -/
theorem descend_density {k n d q m e : ℕ} (hk : 3≤ k) (order : n=q*m)
    (many : 2≤ q) (dense : 2*n≤ k*d) (gain : 3*d≤4*e) : 2*m≤(k-1)*e := by
  have twice := Nat.mul_le_mul_right m many
  have bound : 4*m≤ k*d := by rw [order] at dense; omega
  have step := Nat.mul_le_mul_left k gain
  have triple : 3*m≤ k*e := by nlinarith only [bound, step]
  have scale := Nat.mul_le_mul_right e (show 2*k≤3*(k-1) by omega)
  nlinarith only [triple,scale]

/-- Choose the parent size so that an iron block budget survives either a
robustness conversion at this order or descent to a smaller order. -/
theorem step_parameters (k P : ℕ) (hk : 0< k) :
    ∃ N : ℕ, 0< N ∧ ∀ b n d : ℕ, N*(b+1)≤ n → 2*n≤ k*d →
      4*k^2≤ n ∧ 2≤ d ∧ b≤ d/(8*2^(3*k)) ∧ b≤(n/(8*k^2))/(3*2^(3*k)) ∧
      ∀ q m : ℕ, q≤2*k → n=q*m → P*(b+1)≤ m := by
  let a := 8*2^(3*k)
  let h := 3*2^(3*k)
  let w := 8*k^2
  let N := max (w*h) (max (k*a) (max (2*k*P) (4*k^2)))+1
  refine ⟨N,by dsimp [N]; omega,?_⟩
  intro b n d large dense
  have bound (x : ℕ) (hx : x≤ N) : x*(b+1)≤ n := (Nat.mul_le_mul_right _ hx).trans large
  have ka := bound (k*a) (by dsimp [N]; omega)
  rw [Nat.mul_assoc] at ka
  have deg : a*(b+1)≤ d := Nat.le_of_mul_le_mul_left (ka.trans (show n≤ k*d by omega)) hk
  have wh := bound (w*h) (by dsimp [N]; omega)
  rw [Nat.mul_assoc] at wh
  have hp : 0<2^(3*k) := Nat.pow_pos (by decide)
  have ap : 0< a := by dsimp [a]; omega
  have hpos : 0< h := by dsimp [h]; omega
  have wpos : 0< w := by dsimp [w]; positivity
  have enough := bound (4*k^2) (by dsimp [N]; omega)
  have simple (x : ℕ) : x≤ x*(b+1) := by rw [Nat.mul_add_one]; omega
  have lo : 4*k^2≤ n := (simple _).trans enough
  have alo : 2≤ a := by dsimp [a]; omega
  refine ⟨lo,(alo.trans (simple _)).trans deg,?_,?_,?_⟩
  · apply (Nat.le_div_iff_mul_le ap).2
    rw [Nat.mul_comm]
    exact (Nat.mul_le_mul_left a (Nat.le_succ _)).trans deg
  · apply (Nat.le_div_iff_mul_le hpos).2
    apply (Nat.le_div_iff_mul_le wpos).2
    rw [Nat.mul_comm _ w,Nat.mul_comm b h]
    exact (Nat.mul_le_mul_left w (Nat.mul_le_mul_left h (Nat.le_succ _))).trans wh
  · intro q m cap split
    have amount := bound (2*k*P) (by dsimp [N]; omega)
    rw [Nat.mul_assoc,split] at amount
    exact Nat.le_of_mul_le_mul_left (amount.trans (Nat.mul_le_mul_right m cap)) (by omega)
end LovaszBlocks

namespace LovaszIron
open SimpleGraph Finset

/-- Iron connectivity is preserved by relabeling vertices. -/
theorem transfer_iron {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    {G : SimpleGraph V} {K : SimpleGraph W} (e : G ≃g K) (b : ℕ)
    (iron : ∀ (F : SimpleGraph V) [DecidableRel F.Adj] (S : Finset V),
      S.card≤ b → (∀ x,F.degree x≤ b) → ((G \ F).induce (Sᶜ : Finset V)).Preconnected) :
    ∀ (F : SimpleGraph W) [DecidableRel F.Adj] (S : Finset W),
      S.card≤ b → (∀ x,F.degree x≤ b) → ((K \ F).induce (Sᶜ : Finset W)).Preconnected := by
  classical
  intro F _ S size loss
  let T := S.map e.symm.toEquiv.toEmbedding
  let F' := F.comap e
  let f : F' ≃g F := Iso.comap e.toEquiv F
  have ft (v : V) : v∈T ↔ e v∈S := by
    constructor
    · intro h
      obtain ⟨w,hw,rfl⟩ := mem_map.mp h
      exact (show e (e.symm w)=w from e.apply_symm_apply w).symm ▸ hw
    · intro h
      exact mem_map.mpr ⟨e v,h,e.symm_apply_apply _⟩
  have good := iron F' T (by simpa [T] using size) (fun x => (f.degree_eq x) ▸ loss (e x))
  let d : (G \ F') ≃g (K \ F) := {
    toEquiv := e.toEquiv
    map_rel_iff' := by intro x y; exact and_congr e.map_adj_iff Iff.rfl }
  have bij : Set.BijOn d ((Tᶜ : Finset V) : Set V) ((Sᶜ : Finset W) : Set W) := by
    refine ⟨fun x hx => mem_compl.mpr (fun h => (mem_compl.mp hx) ((ft x).mpr h)),d.injective.injOn,?_⟩
    intro y hy
    refine ⟨e.symm y,mem_compl.mpr (fun h => ?_),e.apply_symm_apply _⟩
    exact (mem_compl.mp hy) (e.apply_symm_apply y ▸ (ft _).mp h)
  exact (d.induce bij).preconnected_iff.mp good

end LovaszIron

namespace LovaszIron
open SimpleGraph Finset

/-- Quantitative integer form of the iron decomposition of Christofides,
Hladký and Máthé, Theorem 8. For each density parameter k, both bounds are
independent of the graph and of the requested deletion budget. -/
theorem bounded_iron_decomposition (k : ℕ) :
    ∃ N R : ℕ, 0< N ∧ 0< R ∧ ∀ {V : Type} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ),
      LovaszConjecture.IsVertexTransitive G → 2*Fintype.card V≤ k*G.minDegree →
      N*(b+1)≤ Fintype.card V →
      ∃ (q : ℕ) (c : V→Fin q), q≤ R ∧ Function.Surjective c ∧
        (∀ (f : G ≃g G) (x y : V), c (f x)=c (f y) ↔ c x=c y) ∧
        ∀ i, let X : Set V := {v | c v=i}
          2*Fintype.card X ≤ k*(G.induce X).minDegree ∧
          ∀ (F : SimpleGraph X) [DecidableRel F.Adj] (S : Finset X),
            S.card≤ b → (∀ z, F.degree z≤ b) → (((G.induce X) \ F).induce (↑(Sᶜ) : Set X)).Preconnected := by
  classical
  induction k with
  | zero =>
    refine ⟨1,1,by decide,by decide,?_⟩
    intro V _ _ G _ b vt dense big
    simp only [Nat.zero_mul, Nat.one_mul] at dense big
    omega
  | succ j ih =>
    obtain ⟨P,Q,p0,q0,inside⟩ := ih
    let k := j+1
    have kp : 0< k := Nat.succ_pos _
    obtain ⟨N,n0,params⟩ := LovaszBlocks.step_parameters k P kp
    refine ⟨N,2*k*Q,n0,by positivity,?_⟩
    intro V _ _ G _ b vt dense big
    let n := Fintype.card V
    let d := G.minDegree
    change 2*n≤ k*d at dense
    obtain ⟨enough,d2,bd1,bd2,child⟩ := params b n d big dense
    have npos : 0< n := (Nat.mul_pos n0 (Nat.succ_pos b)).trans_le big
    have : Nonempty V := Fintype.card_pos_iff.mp npos
    obtain ⟨v,hv⟩ := G.exists_minimal_degree_vertex
    have dn : d< n := by change G.minDegree< Fintype.card V; rw [hv]; exact G.degree_lt_card_verts v
    have hk3 : 3≤ k := by
      by_contra! low
      have bound := Nat.mul_le_mul_right d (show k≤2 by omega)
      omega
    have regular : G.IsRegularOfDegree d := by
      intro w
      obtain ⟨f,h⟩ := vt w v
      have eq := f.degree_eq w
      rw [h] at eq
      exact eq.symm.trans hv.symm
    let t := n/(8*k^2)
    obtain robust|⟨q,m,p,two,lim,sur,order,_,sizes,gain,_,invariant,_,vparts⟩ :=
      density_increment G d k t regular vt kp (by omega) (by rw [Nat.mul_comm]; exact Nat.div_mul_le_self ..)
    · have good := robust_to_iron_density G vt k d t d2 (by omega) G.minDegree_le_degree
        (fun F _ loss u w => robust u w F loss)
      let c (_ : V) : Fin 1 := 0
      refine ⟨1,c,by have := Nat.mul_pos (Nat.mul_pos (by decide : 0<2) kp) q0; omega,
        fun i => ⟨v,Subsingleton.elim _ _⟩,fun _ _ _ => Iff.rfl,?_⟩
      intro i
      let e : G ≃g G.induce {v | c v=i} := {
        toFun := fun w => ⟨w,Subsingleton.elim _ _⟩
        invFun := Subtype.val
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_rel_iff' := Iff.rfl }
      constructor
      · have size := Fintype.card_congr e.toEquiv
        have deg := e.minDegree_eq
        exact (show 2*Fintype.card V ≤ k*G.minDegree from dense) |> (size ▸ deg ▸ ·)
      · exact transfer_iron e b (fun F _ S hs loss =>
        good F S (hs.trans (le_min bd1 bd2)) (fun z => (loss z).trans (le_min bd1 bd2)))
    · let i : Fin q := ⟨0,by omega⟩
      let W : Set V := {v | p v=i}
      let K := G.induce W
      have sz : Fintype.card W=m := by simpa only [W,Fintype.card_subtype,Set.mem_ofPred_eq] using sizes i
      have : Nonempty W := by obtain ⟨w,hw⟩ := sur i; exact ⟨⟨w,hw⟩⟩
      obtain ⟨w,mind⟩ := K.exists_minimal_degree_vertex
      have point (a : V) (label : Fin q) (ha : p a=label) :
          3*d≤4*(G.induce {x | p x=label}).degree (⟨a,ha⟩ : {x // p x=label}) := by
        subst label
        exact gain a
      have inc : 3*d≤4*K.minDegree := by
        rw [mind]
        exact point w.val i w.property
      have drop := LovaszBlocks.descend_density hk3 order two dense inc
      have newrate : 2*Fintype.card W≤ j*K.minDegree := by
        rw [sz]; simpa only [k,Nat.add_sub_cancel] using drop
      have localvt : LovaszConjecture.IsVertexTransitive K := vparts i
      obtain ⟨r,g,rq,onto,stable,iron⟩ := inside K b localvt newrate (sz ▸ child q m lim order)
      obtain ⟨c,full,inv,_,isos⟩ := LovaszBlocks.refine_partition G p sur i vt invariant g onto stable
      refine ⟨q*r,c,Nat.mul_le_mul lim rq,full,inv,?_⟩
      intro z
      obtain ⟨e⟩ := isos z
      obtain ⟨den,hiron⟩ := iron (finProdFinEquiv.symm z).2
      constructor
      · have card := Fintype.card_congr e.toEquiv
        have deg := e.minDegree_eq
        rw [card,deg]
        exact den.trans (Nat.mul_le_mul_right _ (Nat.le_succ j))
      · exact transfer_iron e.symm b hiron

end LovaszIron

namespace LovaszIron
open SimpleGraph Finset

/-- Any two binary colorings that are almost proper outside a small
exceptional set coincide there, up to a single interchange of the colors,
when the graph survives the corresponding vertex and local edge losses. -/
theorem color_rigidity {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (S : Finset V) (p q : V → Bool) (h k : ℕ)
    (pbound : ∀ x ∉ S, ((G.neighborFinset x).filter (fun y => p x=p y)).card≤ h)
    (qbound : ∀ x ∉ S, ((G.neighborFinset x).filter (fun y => q x=q y)).card≤ k)
    (iron : ∀ (F : SimpleGraph V) [DecidableRel F.Adj],
      (∀ z,F.degree z≤ h+k) → ((G \ F).induce (Sᶜ : Finset V)).Preconnected) :
    (∀ x ∉ S, p x=q x) ∨ (∀ x ∉ S, p x≠q x) := by
  classical
  let F : SimpleGraph V :=
    { Adj x y := G.Adj x y ∧ x∉S ∧ y∉S ∧ (p x=p y ∨ q x=q y)
      symm := ⟨fun _ _ e => ⟨e.1.symm,e.2.2.1,e.2.1,e.2.2.2.imp Eq.symm Eq.symm⟩⟩
      loopless := ⟨fun x e => G.loopless.irrefl x e.1⟩ }
  have loss (x : V) : F.degree x≤ h+k := by
    rw [← F.card_neighborFinset_eq_degree]
    by_cases hs : x∈S
    · have empty : F.neighborFinset x=∅ := eq_empty_iff_forall_notMem.mpr
        (fun _ hy => ((F.mem_neighborFinset ..).mp hy).2.1 hs)
      simp [empty]
    let N := G.neighborFinset x
    have sub : F.neighborFinset x ⊆ (N.filter fun y => p x=p y) ∪ (N.filter fun y => q x=q y) := by
      intro z hz
      obtain ⟨edge,_,_,mono⟩ := (F.mem_neighborFinset ..).mp hz
      have adj := (G.mem_neighborFinset ..).mpr edge
      exact mono.elim (fun e => mem_union_left _ (mem_filter.mpr ⟨adj,e⟩))
        (fun e => mem_union_right _ (mem_filter.mpr ⟨adj,e⟩))
    exact ((card_le_card sub).trans (card_union_le ..)).trans (Nat.add_le_add (pbound _ hs) (qbound _ hs))
  let U : Set V := ↑(Sᶜ : Finset V)
  let H := (G \ F).induce U
  have walk_color {x y : U} (r : H.Walk x y) : p x=q x ↔ p y=q y := by
    induction r with
    | nil => rfl
    | @cons x z y adj r ih =>
      have usable : ¬(p x=p z ∨ q x=q z) := fun e =>
        adj.2 ⟨adj.1,mem_compl.mp x.property,mem_compl.mp z.property,e⟩
      have flip (a b c d : Bool) : ¬(a=b ∨ c=d) → (a=c ↔ b=d) := by decide +revert
      exact (flip _ _ _ _ usable).trans ih
  by_cases yes : ∃ x ∉ S, p x=q x
  · left
    obtain ⟨x,hx,eq⟩ := yes
    intro y hy
    let u : U := ⟨x,mem_compl.mpr hx⟩
    let v : U := ⟨y,mem_compl.mpr hy⟩
    obtain ⟨r⟩ := iron F loss u v
    exact (walk_color r).mp eq
  · exact Or.inr (fun x hx hit => yes ⟨x,hx,hit⟩)

end LovaszIron

namespace LovaszIron
open SimpleGraph Finset

/-- A locally maximal cut with few exceptional vertices in an iron
vertex-transitive graph has uniformly small monochromatic degree. Every
automorphism exactly preserves or interchanges its two color classes. -/
theorem invariant_near_bipartition {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (vt : LovaszConjecture.IsVertexTransitive G) (p : V → Bool)
    (E : Finset V) (b h : ℕ) (small : E.card≤ b) (good : ∃ x, x ∉ E)
    (few : ∀ x ∉ E, ((G.neighborFinset x).filter (fun y => p y=p x)).card≤ h)
    (localCut : ∀ x, ((G.neighborFinset x).filter (fun y => p y=p x)).card ≤
      ((G.neighborFinset x).filter (fun y => p y≠p x)).card)
    (iron : ∀ (F : SimpleGraph V) [DecidableRel F.Adj] (S : Finset V),
      S.card≤2*b → (∀ z,F.degree z≤2*(h+2*b)) → ((G \ F).induce (Sᶜ : Finset V)).Preconnected) :
    (∀ x, ((G.neighborFinset x).filter (fun y => p y=p x)).card≤ h+2*b) ∧
    (∀ (f : G ≃g G), (∀ x, p (f x)=p x) ∨ (∀ x, p (f x)≠p x)) := by
  classical
  let N := G.neighborFinset
  let mono (q : V → Bool) (x : V) := ((N x).filter fun y => q y=q x).card
  have mapMono (f : G ≃g G) (x : V) : mono (fun y => p (f y)) x = mono p (f x) := by
    have rows : ((N x).filter (fun y => p (f y)=p (f x))).map f.toEquiv.toEmbedding =
        (N (f x)).filter (fun y => p y=p (f x)) := by
      ext z
      obtain ⟨y,rfl⟩ := f.surjective z
      rw [show f y ∈ _ ↔ _ from mem_map' f.toEquiv.toEmbedding]
      simp only [N,mem_filter,G.mem_neighborFinset,f.map_adj_iff]
    exact (card_map ..).symm.trans (congrArg Finset.card rows)
  have uniform (x : V) : mono p x≤ h+2*b := by
    obtain ⟨w,hw⟩ := good
    obtain ⟨f,hit⟩ := vt x w
    let q (y : V) := p (f y)
    let T := E.map f.symm.toEquiv.toEmbedding
    let S := E ∪ T
    have sSize : S.card≤2*b := by
      have sizeT : T.card = E.card := card_map ..
      have := card_union_le E T
      dsimp only [S]
      omega
    have pres (y : V) (hy : y∉S) : y∉E :=
      fun e => hy (mem_union_left _ e)
    have pres' (y : V) (hy : y∉S) : f y∉E := by
      intro e
      apply hy
      exact mem_union_right _ (mem_map.mpr ⟨f y,e,f.toEquiv.symm_apply_apply _⟩)
    have pbound (y : V) (hy : y∉S) : ((N y).filter (fun z => p y=p z)).card≤ h := by
      simpa only [eq_comm] using few y (pres y hy)
    have qbound (y : V) (hy : y∉S) : ((N y).filter (fun z => q y=q z)).card≤ h := by
      have bound : mono q y ≤ h := (mapMono f y).le.trans (few _ (pres' y hy))
      simpa only [mono,eq_comm] using bound
    have orient := color_rigidity G S p q h h pbound qbound
      (fun F _ loss => iron F S sSize (fun z => (loss z).trans (by omega)))
    have fiber : ∃ c : Bool, ∀ y ∉ S, p y=c → q y=q x := by
      rcases orient with same | flip
      · exact ⟨q x,fun y hy py => (same y hy).symm.trans py⟩
      · refine ⟨!(q x),fun y hy py => ?_⟩
        have binary (a b c : Bool) : a≠b → a=(!c) → b=c := by decide +revert
        exact binary _ _ _ (flip y hy) py
    obtain ⟨c,hc⟩ := fiber
    let W := (N x).filter fun y => p y=c
    have sub : W ⊆ ((N x).filter fun y => q y=q x) ∪ S := by
      intro y hy
      by_cases hs : y∈S
      · exact mem_union_right _ hs
      · exact mem_union_left _ (mem_filter.mpr ⟨(mem_filter.mp hy).1,hc y hs (mem_filter.mp hy).2⟩)
    have bounded := (card_le_card sub).trans (card_union_le ..)
    have qx : mono q x ≤ h := (mapMono f x).le.trans (hit ▸ few w hw)
    change W.card ≤ mono q x + S.card at bounded
    have localBound : mono p x ≤ W.card := by
      by_cases eq : p x=c
      · dsimp [mono,W]; rw [eq]
      · apply (localCut x).trans (card_le_card ?_)
        intro y hy
        obtain ⟨inN,ne⟩ := mem_filter.mp hy
        have two (a b c : Bool) : a≠c → b≠a → b=c := by decide +revert
        exact mem_filter.mpr ⟨inN,two _ _ _ eq ne⟩
    omega
  refine ⟨uniform,fun f => ?_⟩
  let q (x : V) := p (f x)
  have bp (y : V) (_ : y∉(∅ : Finset V)) : ((N y).filter (fun z => p y=p z)).card≤ h+2*b := by
    simpa only [mono,eq_comm] using uniform y
  have bq (y : V) (_ : y∉(∅ : Finset V)) : ((N y).filter (fun z => q y=q z)).card≤ h+2*b := by
    have bound : mono q y ≤ h+2*b := (mapMono f y).le.trans (uniform _)
    simpa only [mono,eq_comm] using bound
  rcases color_rigidity G ∅ p q _ _ bp bq
    (fun F _ loss => iron F ∅ (by simp) (fun z => (loss z).trans (by omega))) with same | flip
  · exact Or.inl (fun x => (same x (notMem_empty _)).symm)
  · exact Or.inr (fun x => (flip x (notMem_empty _)).symm)

end LovaszIron

namespace LovaszIron
open SimpleGraph Finset

/-- A nontrivial locally maximal binary cut that is preserved up to interchange
by the automorphism group has equal sides and its crossing graph is again
vertex-transitive. -/
theorem balanced_transitive_cut {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (vt : LovaszConjecture.IsVertexTransitive G) (p : V → Bool)
    (positive : ∃ z, 0< G.degree z)
    (localCut : ∀ x, ((G.neighborFinset x).filter (fun y => p y=p x)).card ≤
      ((G.neighborFinset x).filter (fun y => p y≠p x)).card)
    (invariant : ∀ (f : G ≃g G), (∀ x, p (f x)=p x) ∨ (∀ x,p (f x)≠p x)) :
    (univ.filter (fun x => p x=false)).card = (univ.filter (fun x => p x=true)).card ∧
    ∃ H : SimpleGraph V, (∀ x y,H.Adj x y ↔ G.Adj x y ∧ p x≠p y) ∧
      LovaszConjecture.IsVertexTransitive H := by
  classical
  obtain ⟨z,hz⟩ := positive
  have both : ∃ y,p y≠p z := by
    by_contra! constant
    have mono : (G.neighborFinset z).filter (fun y => p y=p z) = G.neighborFinset z :=
      filter_true_of_mem (fun _ _ => constant _)
    have empty : (G.neighborFinset z).filter (fun y => p y≠p z) = ∅ :=
      filter_false_of_mem (fun _ _ h => h (constant _))
    have bound := localCut z
    rw [mono,empty,card_empty,G.card_neighborFinset_eq_degree] at bound
    omega
  obtain ⟨y,hy⟩ := both
  obtain ⟨f,hit⟩ := vt z y
  have flip := (invariant f).resolve_left fun same => hy (hit ▸ same z)
  constructor
  · have rows : (univ.filter (fun v => p v=false)).map f.toEquiv.toEmbedding =
        univ.filter (fun v => p v=true) := by
      ext v
      obtain ⟨x,rfl⟩ := f.surjective v
      rw [show f x ∈ _ ↔ _ from mem_map' f.toEquiv.toEmbedding]
      simp only [mem_filter,mem_univ,true_and]
      have bool (a b : Bool) : b≠a → (a=false ↔ b=true) := by decide +revert
      exact bool _ _ (flip x)
    exact (card_map ..).symm.trans (congrArg Finset.card rows)
  · let H : SimpleGraph V :=
      { Adj x y := G.Adj x y ∧ p x ≠ p y
        symm := ⟨fun _ _ h => ⟨h.1.symm,h.2.symm⟩⟩
        loopless := ⟨fun _ h => h.2 rfl⟩ }
    refine ⟨H,fun _ _ => Iff.rfl,?_⟩
    intro a b
    obtain ⟨g,hit⟩ := vt a b
    have colors (x y : V) : p (g x)≠p (g y) ↔ p x≠p y := by
      rcases invariant g with same | flip
      · rw [same,same]
      · have bool (a b c d : Bool) : c≠a → d≠b → (c≠d ↔ a≠b) := by decide +revert
        exact bool _ _ _ _ (flip x) (flip y)
    exact ⟨⟨g.toEquiv,fun {x y} => and_congr g.map_adj_iff (colors x y)⟩,hit⟩

end LovaszIron

namespace LovaszDense
open SimpleGraph Finset

/-- In a symmetric array with zero diagonal, deleting one row and column
removes twice the sum of that row. -/
theorem sum_remove_row_column {V : Type*} [Fintype V] [DecidableEq V]
    (a : V → V → ℕ) (symm : ∀ x y, a x y=a y x) (v : V) (loop : a v v=0) :
    (∑ i, ∑ j, a i j) =
      (∑ i ∈ univ.erase v, ∑ j ∈ univ.erase v, a i j) + 2*(∑ j, a v j) := by
  classical
  let U := univ.erase v
  have split (f : V → ℕ) : (∑ j,f j) = (∑ j∈U,f j)+f v := (sum_erase_add _ _ (mem_univ _)).symm
  have col : (∑ i∈U,a i v) = ∑ j,a v j := by
    rw [split (a v),loop,add_zero]
    exact sum_congr rfl (fun i _ => symm i v)
  calc
    _ = (∑ i∈U, ∑ j, a i j)+(∑ j,a v j) := split _
    _ = (∑ i∈U, ((∑ j∈U,a i j)+a i v)) + (∑ j,a v j) := by
      exact congrArg (· + (∑ j,a v j)) (sum_congr rfl (fun i _ => split (a i)))
    _ = _ := by rw [sum_add_distrib,col]; dsimp [U]; omega

/-- A bipartition minimizing the number of internal edges has at least as
many opposite neighbors as same-side neighbors at every vertex. Its total
internal degree is no larger than that of the given partition. -/
theorem max_cut_improvement {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (p₀ : V → Bool) :
    let inside (p : V → Bool) (v : V) := ((G.neighborFinset v).filter fun w => p w=p v).card
    let outside (p : V → Bool) (v : V) := ((G.neighborFinset v).filter fun w => p w≠p v).card
    ∃ p : V → Bool, (∑ v,inside p v) ≤ ∑ v,inside p₀ v ∧ ∀ v,inside p v ≤ outside p v := by
  classical
  intro inside outside
  let W (p : V → Bool) (v w : V) : ℕ := if G.Adj v w ∧ p w=p v then 1 else 0
  have row (p : V → Bool) (v : V) : (∑ w,W p v w) = inside p v := by
    simp only [W,Finset.sum_boole,inside]
    apply congrArg Finset.card
    ext w
    simp [G.mem_neighborFinset]
  have symmetry p (v w : V) : W p v w=W p w v := by simp [W,G.adj_comm v w,@eq_comm _ (p v) (p w)]
  have diag p (v : V) : W p v v=0 := by simp [W]
  let cost (p : V → Bool) := ∑ v,inside p v
  let achieved (n : ℕ) := ∃ p, cost p=n
  have ex : ∃ n,achieved n := ⟨cost p₀,p₀,rfl⟩
  obtain ⟨p, optimal⟩ := Nat.find_spec ex
  have minimal (q : V → Bool) : cost p ≤ cost q := optimal ▸ Nat.find_min' ex (show achieved (cost q) from ⟨q,rfl⟩)
  refine ⟨p,minimal p₀,?_⟩
  intro v
  let q (x : V) := if x=v then !(p x) else p x
  have equal : (∑ i∈univ.erase v, ∑ j∈univ.erase v,W q i j) =
      ∑ i∈univ.erase v, ∑ j∈univ.erase v,W p i j := by
    refine sum_congr rfl fun i hi => sum_congr rfl fun j hj => ?_
    simp [W,q,(mem_erase.mp hi).1,(mem_erase.mp hj).1]
  have flipped : inside q v = outside p v := by
    change ((G.neighborFinset v).filter _).card = ((G.neighborFinset v).filter _).card
    congr 1
    ext w
    by_cases same : w=v
    · subst w; simp
    · cases hp : p v <;> cases hw : p w <;> simp [q,same,hp,hw]
  have before := sum_remove_row_column (W p) (symmetry p) v (diag p v)
  have after := sum_remove_row_column (W q) (symmetry q) v (diag q v)
  rw [equal] at after
  simp only [row] at before after
  rw [flipped] at after
  have opt := minimal q
  change (∑ x,inside p x) ≤ ∑ x,inside q x at opt
  omega

/-- Counting vertices whose weight reaches a threshold. -/
theorem threshold_bad_vertices {V : Type*} [Fintype V] (f : V → ℕ) (t : ℕ) :
    (univ.filter (fun x => t≤ f x)).card*t ≤ ∑ x, f x := by
  classical
  let B := univ.filter (fun x => t≤ f x)
  calc
    _ = ∑ _x∈B,t := by simp [B]
    _ ≤ ∑ x∈B,f x := sum_le_sum (fun x hx => (mem_filter.mp hx).2)
    _ ≤ _ := sum_le_univ_sum_of_nonneg (fun x => Nat.zero_le _)

end LovaszDense

namespace LovaszIron
open SimpleGraph Finset

/-- Quantitative near-bipartite structure from an arbitrary low-cost
coloring. An iron transitive graph then contains a balanced spanning
vertex-transitive bipartite subgraph with small lost degree at every vertex. -/
theorem near_bipartite_cut_cost {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (vt : LovaszConjecture.IsVertexTransitive G)
    (b h : ℕ) (nlarge : b < Fintype.card V) (positive : ∃ x, 0< G.degree x)
    (p₀ : V → Bool)
    (few : (∑ x, ((G.neighborFinset x).filter fun y => p₀ y=p₀ x).card) < (b+1)*(h+1))
    (iron : ∀ (F : SimpleGraph V) [DecidableRel F.Adj] (S : Finset V),
      S.card≤2*b → (∀ z,F.degree z≤2*(h+2*b)) → ((G \ F).induce (Sᶜ : Finset V)).Preconnected) :
    ∃ (p : V → Bool) (H : SimpleGraph V),
      (univ.filter (fun x => p x=false)).card = (univ.filter (fun x => p x=true)).card ∧
      (∀ x, ((G.neighborFinset x).filter (fun y => p y=p x)).card≤ h+2*b) ∧
      (∀ (f : G ≃g G), (∀ x,p (f x)=p x) ∨ (∀ x,p (f x)≠p x)) ∧
      (∀ x y,H.Adj x y ↔ G.Adj x y ∧ p x≠p y) ∧ LovaszConjecture.IsVertexTransitive H ∧
      (∑ x, ((G.neighborFinset x).filter fun y => p y=p x).card) ≤
        ∑ x, ((G.neighborFinset x).filter fun y => p₀ y=p₀ x).card := by
  classical
  let inside (p : V → Bool) (x : V) := ((G.neighborFinset x).filter fun y => p y=p x).card
  obtain ⟨p,minSum,localCut⟩ := LovaszDense.max_cut_improvement G p₀
  let E := univ.filter fun x => h+1 ≤ inside p x
  have count : E.card*(h+1) ≤ ∑ x,inside p x := LovaszDense.threshold_bad_vertices _ _
  have es : E.card ≤ b := by
    by_contra! large
    have bound := Nat.mul_le_mul_right (h+1) large
    exact (not_le_of_gt few) (bound.trans (count.trans minSum))
  have good : ∃ x,x∉E := by
    obtain ⟨x,_,hx⟩ := exists_mem_notMem_of_card_lt_card
      (show E.card < (univ : Finset V).card from es.trans_lt nlarge)
    exact ⟨x,hx⟩
  have remaining (x : V) (hx : x∉E) : inside p x≤ h := by
    by_contra! many
    exact hx (mem_filter.mpr ⟨mem_univ _,many⟩)
  obtain ⟨all,inv⟩ := invariant_near_bipartition G vt p E b h es good remaining localCut iron
  obtain ⟨equal,H,adj,hvt⟩ := balanced_transitive_cut G vt p positive localCut inv
  exact ⟨p,H,equal,all,inv,adj,hvt,minSum⟩

end LovaszIron

namespace LovaszIron
open SimpleGraph Finset

/-- The near-bipartite quarter-density regime has a spanning path, including
equality after subtracting the average number of monochromatic neighbors. -/
theorem near_bipartite_hamilton_by_total {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (vt : LovaszConjecture.IsVertexTransitive G)
    (b h : ℕ) (nlarge : b< Fintype.card V) (three : 3≤ Fintype.card V)
    (p₀ : V → Bool)
    (few : (∑ x, ((G.neighborFinset x).filter fun y => p₀ y=p₀ x).card) < (b+1)*(h+1))
    (iron : ∀ (F : SimpleGraph V) [DecidableRel F.Adj] (S : Finset V),
      S.card≤2*b → (∀ z,F.degree z≤2*(h+2*b)) → ((G \ F).induce (Sᶜ : Finset V)).Preconnected)
    (density : Fintype.card V * Fintype.card V +
      4*(∑ x, ((G.neighborFinset x).filter fun y => p₀ y=p₀ x).card) ≤ 4*(Fintype.card V*G.minDegree)) : LovaszConjecture.HasHamiltonianPath G := by
  classical
  let : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  have positive : ∃ x, 0< G.degree x := by
    obtain ⟨x,hx⟩ := G.exists_minimal_degree_vertex
    refine ⟨x,?_⟩
    by_contra! zero
    rw [hx, Nat.eq_zero_of_le_zero zero, Nat.mul_zero, Nat.mul_zero] at density
    have : 0< Fintype.card V*Fintype.card V := Nat.mul_pos (by omega) (by omega)
    omega
  obtain ⟨p,H,_,cost,_,edges,hvt,minSum⟩ := near_bipartite_cut_cost G vt b h nlarge positive p₀ few iron
  let F := G \ H
  have rows (x : V) : F.neighborFinset x = (G.neighborFinset x).filter (fun y => p y=p x) := by
    ext y
    simp only [mem_filter,SimpleGraph.mem_neighborFinset]
    change G.Adj x y ∧ ¬H.Adj x y ↔ _
    rw [edges]
    tauto
  have loss (x : V) : F.degree x ≤ h+2*b :=
    (F.card_neighborFinset_eq_degree x).symm.le.trans (rows x ▸ cost x)
  have remain : G \ F = H := by
    ext x y
    change (G.Adj x y ∧ ¬(G.Adj x y ∧ ¬H.Adj x y)) ↔ H.Adj x y
    rw [edges]
    tauto
  have connected : H.Connected := by
    have pre := iron F ∅ (by simp) (fun z => (loss z).trans (by omega))
    rw [remain, show (((∅ : Finset V)ᶜ : Finset V) : Set V)=Set.univ from by ext; simp] at pre
    exact ⟨(SimpleGraph.induceUnivIso H).preconnected_iff.mp pre⟩
  have reg : H.IsRegularOfDegree H.minDegree := by
    intro x
    obtain ⟨y,hy⟩ := H.exists_minimal_degree_vertex
    obtain ⟨f,hf⟩ := hvt x y
    rw [hy,←hf,f.degree_eq]
  have proper : H.IsBipartite := by
    refine ⟨⟨fun x => if p x then (1 : Fin 2) else 0,?_⟩⟩
    intro x y e
    have ne := ((edges x y).mp e).2
    cases hx : p x <;> cases hy : p y <;> simp_all
  let n := Fintype.card V
  let mono (q : V → Bool) (x : V) := ((G.neighborFinset x).filter fun y => q y=q x).card
  have vertex (x : V) : G.minDegree ≤ H.minDegree + mono p x := by
    have cover : G.neighborFinset x ⊆ H.neighborFinset x ∪ F.neighborFinset x := by
      intro y hy
      by_cases ht : H.Adj x y
      · exact mem_union_left _ ((H.mem_neighborFinset ..).mpr ht)
      · exact mem_union_right _ ((F.mem_neighborFinset ..).mpr ⟨(G.mem_neighborFinset ..).mp hy,ht⟩)
    have bound := (card_le_card cover).trans (card_union_le ..)
    rw [G.card_neighborFinset_eq_degree,H.card_neighborFinset_eq_degree,reg x,rows x] at bound
    exact (G.minDegree_le_degree x).trans bound
  have sum := sum_le_sum (s:=univ) (fun x _ => vertex x)
  simp only [sum_add_distrib,sum_const,card_univ,nsmul_eq_mul] at sum
  have total : n*G.minDegree ≤ n*H.minDegree + ∑ x,mono p₀ x :=
    sum.trans (Nat.add_le_add_left minSum _)
  change n*n+4*(∑ x, mono p₀ x) ≤ 4*(n*G.minDegree) at density
  have rem : n*n ≤ 4*(n*H.minDegree) := by omega
  have quarter : n ≤ 4*H.minDegree := Nat.le_of_mul_le_mul_left
    (show n*n ≤ n*(4*H.minDegree) from rem.trans_eq (by ring)) (by dsimp [n]; omega)
  have path := LovaszDense.bipartite_le_quarter H connected reg proper three quarter
  obtain ⟨a,b,w,hw⟩ := path
  let emb : H →g G := ⟨id,fun {x y} e => ((edges x y).mp e).1⟩
  exact ⟨a,b,w.map emb,hw.map emb Function.bijective_id⟩

end LovaszIron

namespace LovaszIron
open SimpleGraph Finset

/-- A single iron budget suffices for the near-bipartite quarter-density
criterion. The measured cost counts each monochromatic edge twice. -/
theorem near_quarter_iron {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (vt : LovaszConjecture.IsVertexTransitive G)
    (l : ℕ) (three : 3 ≤ Fintype.card V) (small : l < Fintype.card V)
    (iron : ∀ (F : SimpleGraph V) [DecidableRel F.Adj] (S : Finset V),
      S.card ≤ l → (∀ z, F.degree z ≤ l) → ((G \ F).induce (Sᶜ : Finset V)).Preconnected)
    (c : V → Bool) :
    let M := ∑ x, ((G.neighborFinset x).filter fun y => c y=c x).card
    let t := l / 8
    M < (t+1)^2 → Fintype.card V ^ 2 + 4*M ≤ 4*Fintype.card V*G.minDegree →
    LovaszConjecture.HasHamiltonianPath G := by
  intro M t few density
  refine near_bipartite_hamilton_by_total G vt t t (by dsimp [t]; omega) three c ?_ ?_ ?_
  · simpa only [M,pow_two] using few
  · intro F inst S hs loss
    have sb : 2*t≤ l := by dsimp [t]; omega
    have eb : 2*(t+2*t)≤ l := by dsimp [t]; omega
    exact iron F S (hs.trans sb) (fun z => (loss z).trans eb)
  · simpa only [M,pow_two,Nat.mul_assoc] using density

/-- Every binary coloring of a counterexample at the reciprocal-scale iron
budget violates either the low monochromatic cost or the quarter-density
criterion. The connectivity hypothesis has the same order as the block API. -/
theorem near_quarter_obstruction {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (vt : LovaszConjecture.IsVertexTransitive G) (k : ℕ) (hk : 0< k)
    (three : 3 ≤ Fintype.card V)
    (iron : ∀ (S : Finset V) (F : SimpleGraph V) [DecidableRel F.Adj],
      S.card ≤ Fintype.card V/(8*k^2) → (∀ z, F.degree z ≤ Fintype.card V/(8*k^2)) →
      ((G \ F).induce (Sᶜ : Finset V)).Connected)
    (absent : ¬LovaszConjecture.HasHamiltonianPath G) :
    ∀ c : V → Bool,
      let M := ∑ x, ((G.neighborFinset x).filter fun y => c y=c x).card
      let t := (Fintype.card V/(8*k^2))/8
      (t+1)^2 ≤ M ∨ 4*Fintype.card V*G.minDegree < Fintype.card V^2+4*M := by
  intro c M t
  by_contra! hit
  have powpos : 0< k^2 := Nat.pow_pos hk
  have small : Fintype.card V/(8*k^2) < Fintype.card V :=
    Nat.div_lt_self (by omega) (by omega)
  exact absent (near_quarter_iron G vt _ three small
    (fun F _ S hs hf => (iron S F hs hf).preconnected) c hit.1 hit.2)

end LovaszIron

namespace LovaszDensity
open Finset SimpleGraph

/-- The total vertex load summed over all automorphisms is the same at every vertex. -/
theorem uniform_load {V : Type*} [Fintype V] (G : SimpleGraph V) [Fintype (G ≃g G)]
    (transitive : LovaszConjecture.IsVertexTransitive G) (w : V → ℕ) (s : V) :
    Fintype.card V * (∑ g : G ≃g G, w (g s)) = Fintype.card (G ≃g G) * ∑ a, w a := by
  classical
  have uniform (a : V) : (∑ g : G ≃g G, w (g s)) = ∑ g : G ≃g G, w (g a) := by
    obtain ⟨f,hf⟩ := transitive a s
    let e : (G ≃g G) ≃ (G ≃g G) := {
      toFun := fun g => f.trans g
      invFun := fun g => f.symm.trans g
      left_inv := fun g => RelIso.ext (fun x => by change g (f (f.symm x)) = g x; simp)
      right_inv := fun g => RelIso.ext (fun x => by change g (f.symm (f x)) = g x; simp) }
    exact Fintype.sum_equiv e _ _ (fun g => by change w (g s) = w (g (f a)); rw [hf])
  calc
    _ = ∑ a : V, ∑ g : G ≃g G, w (g s) := by simp
    _ = ∑ a : V, ∑ g : G ≃g G, w (g a) := sum_congr rfl (fun a _ => uniform a)
    _ = ∑ g : G ≃g G, ∑ a : V, w (g a) := sum_comm
    _ = ∑ _ : G ≃g G, ∑ a : V, w a := sum_congr rfl (fun g _ => g.toEquiv.sum_comp w)
    _ = _ := by simp

end LovaszDensity

namespace LovaszIron
open SimpleGraph Finset

/-- A common translate of two vertices avoids any set smaller than half the graph. -/
theorem translate_pair_avoiding {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (transitive : LovaszConjecture.IsVertexTransitive G) (x y : V) (T : Finset V)
    (size : 2*T.card < Fintype.card V) : ∃ f : G ≃g G, f x∉T ∧ f y∉T := by
  classical
  have : Finite (G ≃g G) := Finite.of_injective (fun f : G ≃g G => (f : V→V))
    (fun _ _ h => RelIso.ext (congrFun h))
  let : Fintype (G ≃g G) := Fintype.ofFinite _
  have : Nonempty (G ≃g G) := ⟨RelIso.refl _⟩
  let t (z : V) : ℕ := if z∈T then 1 else 0
  let n := Fintype.card V
  let m := Fintype.card (G ≃g G)
  have pos : 0< m := Fintype.card_pos
  have total (a : V) : n*(∑ f : G ≃g G, t (f a)) = m*T.card := by
    simpa [n,m,t] using LovaszDensity.uniform_load G transitive t a
  by_contra! none
  have one (f : G ≃g G) : 1 ≤ t (f x)+t (f y) := by
    by_cases h : f x∈T
    · simp [t,h]
    · simp [t,h,none f h]
  have sum := Finset.sum_le_sum (s:=univ) (fun f _ => one f)
  simp only [sum_add_distrib,sum_const,card_univ,nsmul_eq_mul,Nat.cast_id,mul_one] at sum
  have bound := Nat.mul_le_mul_left n sum
  rw [Nat.mul_add,total,total] at bound
  have strict := Nat.mul_lt_mul_of_pos_left size pos
  change m*(2*T.card)< m*n at strict
  change n*m≤ m*T.card+m*T.card at bound
  rw [Nat.mul_comm n m] at bound
  rw [show m*(2*T.card)=m*T.card+m*T.card by rw [Nat.mul_left_comm, Nat.two_mul]] at strict
  omega

/-- An edge joining two prescribed blocks of an invariant partition has
another representative whose endpoints avoid a small forbidden set. -/
theorem quotient_edge_avoiding {V Q : Type*} [Fintype V] [Fintype Q] [DecidableEq V]
    (G : SimpleGraph V) (c : V → Q) (transitive : LovaszConjecture.IsVertexTransitive G)
    (invariant : ∀ (f : G ≃g G) (a b : V), c (f a)=c (f b) ↔ c a=c b)
    (x y : V) (edge : G.Adj x y) (S : Finset V)
    (small : 2*(Fintype.card Q)^2*S.card< Fintype.card V) :
    ∃ a b, a∉S ∧ b∉S ∧ c a=c x ∧ c b=c y ∧ G.Adj a b := by
  classical
  let hits (p : Q × Q) (g : G ≃g G) := c (g x)=p.1 ∧ c (g y)=p.2
  let rep (p : Q × Q) : G ≃g G := if h : ∃ g, hits p g then h.choose else RelIso.refl _
  have claim (g : G ≃g G) :
      hits (c (g x),c (g y)) (rep (c (g x),c (g y))) := by
    let p := (c (g x),c (g y))
    have h : ∃ f, hits p f := ⟨g,rfl,rfl⟩
    exact (show hits p (rep p) by simpa only [rep,dif_pos h] using h.choose_spec)
  let T := univ.biUnion fun p : Q × Q => S.map (rep p).toEquiv.toEmbedding
  have bound : T.card ≤ (Fintype.card Q)^2*S.card := by
    simpa [T, Fintype.card_prod, pow_two] using
      Finset.card_biUnion_le (s:=univ) (t:=fun p : Q × Q => S.map (rep p).toEquiv.toEmbedding)
  obtain ⟨g,hx,hy⟩ := translate_pair_avoiding G transitive x y T ((Nat.mul_le_mul_left 2 bound).trans_lt (by simpa only [Nat.mul_assoc] using small))
  let f := rep (c (g x),c (g y))
  have h := claim g
  change c (f x)=c (g x) ∧ c (f y)=c (g y) at h
  have absent (z : V) (hz : z∉T) : f.symm z∉S := by
    intro bad
    apply hz
    refine mem_biUnion.mpr ⟨(c (g x),c (g y)),mem_univ _,?_⟩
    exact mem_map.mpr ⟨f.symm z,bad, f.apply_symm_apply z⟩
  refine ⟨f.symm (g x),f.symm (g y),absent _ hx,absent _ hy,?_,?_,?_⟩
  · exact (invariant f _ _).mp (by simpa using h.1.symm)
  · exact (invariant f _ _).mp (by simpa using h.2.symm)
  · exact f.symm.map_adj_iff.mpr (g.map_adj_iff.mpr edge)

end LovaszIron

namespace LovaszQuotient
open SimpleGraph Finset

/-- Grow a closed walk by a single two-edge excursion whenever its support
does not yet contain every vertex. -/
theorem spanning_tour {Q : Type*} [Fintype Q] (H : SimpleGraph Q) (conn : H.Connected) (start : Q) :
    ∃ w : H.Walk start start, w.length=2*(Fintype.card Q-1) ∧ ∀ i,i∈w.support := by
  classical
  let n := Fintype.card Q
  have extend (k : ℕ) (less : k< n) (w : H.Walk start start) (size : w.support.toFinset.card=k) :
      ∃ t : H.Walk start start,t.length=w.length+2 ∧ t.support.toFinset.card=k+1 := by
    obtain ⟨z,absent⟩ : ∃ z : Q,z∉w.support := by
      by_contra! allv
      have full : w.support.toFinset=univ := by ext x; simp [allv x]
      rw [full,card_univ] at size
      omega
    obtain ⟨p⟩ := conn.preconnected start z
    obtain ⟨d,_,inside,outside⟩ := p.exists_boundary_dart {x | x∈w.support} w.start_mem_support absent
    obtain ⟨a,b,split⟩ := Walk.mem_support_iff_exists_append.mp inside
    let t := a.append (.cons d.adj (.cons d.adj.symm b))
    have sup : t.support.toFinset=insert d.snd w.support.toFinset := by
      ext y
      simp only [t,split,List.mem_toFinset,Walk.mem_support_append_iff,Walk.support_cons,
        List.mem_cons,mem_insert]
      have inner : d.fst∈a.support := a.end_mem_support
      aesop
    refine ⟨t,?_,?_⟩
    · simp only [t,split,Walk.length_append,Walk.length_cons]
      omega
    · rw [sup,card_insert_of_notMem (by simpa only [List.mem_toFinset,Set.mem_ofPred_eq] using outside),size]
  have build (k : ℕ) (bound : k+1≤ n) :
      ∃ w : H.Walk start start,w.length=2*k ∧ w.support.toFinset.card=k+1 := by
    induction k with
    | zero => exact ⟨.nil,by simp,by simp⟩
    | succ k ih =>
      obtain ⟨w,len,size⟩ := ih (by omega)
      obtain ⟨t,grows,card⟩ := extend (k+1) (by omega) w size
      exact ⟨t,by omega,card⟩
  have positive : 0< n := Fintype.card_pos_iff.mpr ⟨start⟩
  obtain ⟨w,len,size⟩ := build (n-1) (by omega)
  have full : w.support.toFinset=univ := eq_univ_of_card _ (by change _=n; omega)
  exact ⟨w,len,fun i => List.mem_toFinset.mp (full ▸ mem_univ i)⟩

end LovaszQuotient

namespace LovaszQuotient
open SimpleGraph Finset

/-- Choose lifts for any ordered list of quotient darts, using distinct original
vertices for every departure and arrival. Repeated quotient edges are allowed. -/
theorem lift_darts {V Q : Type*} [DecidableEq V] (G : SimpleGraph V) (H : SimpleGraph Q)
    (c : V → Q) (D : List H.Dart)
    (available : ∀ d : H.Dart,∀ S : Finset V,S.card≤2*(D.length-1) →
      ∃ x y : V,x∉S ∧ y∉S ∧ c x=d.fst ∧ c y=d.snd ∧ G.Adj x y) :
    ∃ E : List (V × V),
      List.Forall₂ (fun e (d : H.Dart) => c e.1=d.fst ∧ c e.2=d.snd ∧ G.Adj e.1 e.2) E D ∧
      (E.flatMap fun e => [e.1,e.2]).Nodup := by
  classical
  have twice (E : List (V×V)) : (E.flatMap fun e => [e.1,e.2]).length=2*E.length := by
    induction E with
    | nil => simp
    | cons e es ih => simp [ih]; omega
  have build (ds : List H.Dart) (bound : ds.length≤ D.length) :
      ∃ E : List (V×V),
        List.Forall₂ (fun e (d : H.Dart) => c e.1=d.fst ∧ c e.2=d.snd ∧ G.Adj e.1 e.2) E ds ∧
        (E.flatMap fun e => [e.1,e.2]).Nodup := by
    induction ds with
    | nil => exact ⟨[],.nil,by simp⟩
    | cons d ds ih =>
      simp only [List.length_cons] at bound
      obtain ⟨E,align,dis⟩ := ih (by omega)
      let prev := E.flatMap fun e => [e.1,e.2]
      have len := align.length_eq
      have used : prev.toFinset.card≤2*(D.length-1) := by
        have h := List.toFinset_card_of_nodup dis
        have h2 := twice E
        change (E.flatMap _).toFinset.card≤ _
        omega
      obtain ⟨x,y,hx,hy,cx,cy,edge⟩ := available d prev.toFinset used
      refine ⟨(x,y)::E,.cons ⟨cx,cy,edge⟩ align,?_⟩
      change (x::y::prev).Nodup
      simp only [List.nodup_cons,List.mem_cons,not_or]
      exact ⟨⟨edge.ne,fun h => hx (List.mem_toFinset.mpr h)⟩,fun h => hy (List.mem_toFinset.mpr h),dis⟩
  exact build D le_rfl

/-- A connected quotient has a short closed spanning tour whose successive
crossing edges can all be lifted to pairwise vertex-disjoint edges. -/
theorem lifted_tour {V Q : Type*} [Fintype Q] [DecidableEq V]
    (G : SimpleGraph V) (H : SimpleGraph Q) (c : V → Q) (conn : H.Connected) (start : Q)
    (available : ∀ i j : Q,H.Adj i j → ∀ S : Finset V,S.card≤2*(2*(Fintype.card Q-1)-1) →
      ∃ x y : V,x∉S ∧ y∉S ∧ c x=i ∧ c y=j ∧ G.Adj x y) :
    ∃ (w : H.Walk start start) (E : List (V×V)),
      w.length=2*(Fintype.card Q-1) ∧ (∀ i,i∈w.support) ∧
      List.Forall₂ (fun e (d : H.Dart) => c e.1=d.fst ∧ c e.2=d.snd ∧ G.Adj e.1 e.2) E w.darts ∧
      (E.flatMap fun e => [e.1,e.2]).Nodup := by
  obtain ⟨w,length,cover⟩ := spanning_tour H conn start
  have avail (d : H.Dart) (S : Finset V) (small : S.card≤2*(w.darts.length-1)) :=
    available d.fst d.snd d.adj S (by simpa only [w.length_darts,length] using small)
  obtain ⟨E,align,dis⟩ := lift_darts G H c w.darts avail
  exact ⟨w,E,length,cover,align,dis⟩

end LovaszQuotient

namespace LovaszQuotient
open SimpleGraph Finset

/-- A bounded invariant quotient of a sufficiently large vertex-transitive graph
admits a closed spanning tour lifted by pairwise vertex-disjoint crossing edges. -/
theorem invariant_tour {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    {q k : ℕ} (c : V → Fin q) (trans : LovaszConjecture.IsVertexTransitive G)
    (invariant : ∀ (f : G ≃g G) (a b : V),c (f a)=c (f b) ↔ c a=c b)
    (conn : (G.map c).Connected) (count : q≤2*k)
    (order : 64*k^3+1≤ Fintype.card V) (start : Fin q) :
    ∃ (w : (G.map c).Walk start start) (E : List (V×V)),
      w.length=2*(q-1) ∧ (∀ i,i∈w.support) ∧
      List.Forall₂ (fun e (d : (G.map c).Dart) => c e.1=d.fst ∧ c e.2=d.snd ∧ G.Adj e.1 e.2) E w.darts ∧
      (E.flatMap fun e => [e.1,e.2]).Nodup := by
  apply (by simpa only [Fintype.card_fin] using lifted_tour G (G.map c) c conn start)
  intro i j h S size
  obtain ⟨_,x,y,adj,cx,cy⟩ := (map_adj' c G i j).mp h
  have bound : 2*q^2*S.card≤64*k^3 := calc
    2*q^2*S.card ≤ 2*(2*k)^2*(4*(2*k)) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left count 2)) (by omega)
    _ = 64*k^3 := by ring
  have small : 2*(Fintype.card (Fin q))^2*S.card< Fintype.card V := by
    rw [Fintype.card_fin]; omega
  obtain ⟨a,b,na,nb,ca,cb,ab⟩ := LovaszIron.quotient_edge_avoiding G c trans invariant x y adj S small
  exact ⟨a,b,na,nb,ca.trans cx,cb.trans cy,ab⟩

end LovaszQuotient

namespace LovaszBlocks
open SimpleGraph

/-- Concatenate the disjoint path segments in tour order. Segment i starts at
the arrival endpoint of crossing edge i and ends at the departure endpoint
of crossing edge i+1, with cyclic indexing. -/
theorem stitch {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (E : List (V×V)) (positive : 0< E.length) (edge : ∀ e∈E, G.Adj e.1 e.2) :
    let next (i : Fin E.length) : Fin E.length := ⟨(i.val+1)%E.length,Nat.mod_lt _ positive⟩
    ∀ L : Fin E.length → List V,
      (∀ i, (L i).head?=some (E.get i).2 ∧ (L i).getLast?=some (E.get (next i)).1 ∧
        (L i).Nodup ∧ (L i).IsChain G.Adj) →
      Pairwise (fun i j => (L i).Disjoint (L j)) →
      (∀ v, ∃ i, v∈L i) → LovaszConjecture.HasHamiltonianPath G := by
  intro next L localData disjoint cover
  let parts := List.ofFn L
  have ne (i) : L i≠[] := by
    intro h
    have eq := (localData i).1
    simp [h] at eq
  have none : []∉parts := by
    rintro bad
    obtain ⟨i,hi⟩ := List.mem_ofFn.mp bad
    exact ne i hi
  have spans (v) : v∈parts.flatten := by
    obtain ⟨i,hit⟩ := cover v
    exact List.mem_flatten.mpr ⟨L i,List.mem_ofFn.mpr ⟨i,rfl⟩,hit⟩
  have nd : parts.flatten.Nodup := List.nodup_flatten.mpr ⟨by
    intro l hl
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hl
    exact (localData i).2.2.1, List.pairwise_ofFn.mpr (fun _ _ lt => disjoint lt.ne)⟩
  have chain : parts.flatten.IsChain G.Adj := by
    apply (List.isChain_flatten none).mpr
    constructor
    · intro l hl
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hl
      exact (localData i).2.2.2
    · apply List.isChain_iff_getElem.mpr
      intro j hj u hu v hv
      have hj' : j+1< E.length := by simpa [parts] using hj
      let i : Fin E.length := ⟨j,by omega⟩
      let k : Fin E.length := ⟨j+1,hj'⟩
      have step : next i=k := Fin.ext (Nat.mod_eq_of_lt hj')
      change parts[j].getLast?=some u at hu
      change parts[j+1].head?=some v at hv
      have hu' : (L i).getLast?=some u := by simpa only [parts,i,List.getElem_ofFn] using hu
      have hv' : (L k).head?=some v := by simpa only [parts,k,List.getElem_ofFn] using hv
      have source := (localData i).2.1
      rw [step,hu'] at source
      have target := (localData k).1
      rw [hv'] at target
      rw [Option.some.inj source,Option.some.inj target]
      exact edge _ (List.get_mem E k)
  let first : Fin E.length := ⟨0,positive⟩
  have nonempty : parts.flatten≠[] := List.flatten_ne_nil_iff.mpr
    ⟨L first,List.mem_ofFn.mpr ⟨first,rfl⟩,ne first⟩
  let p := Walk.ofSupport parts.flatten nonempty chain
  have sup : p.support=parts.flatten := Walk.support_ofSupport nonempty chain
  exact ⟨_,_,p,Walk.IsPath.isHamiltonian_of_mem ((p.isPath_def).mpr (by rw [sup]; exact nd))
    (fun v => by rw [sup]; exact spans v)⟩

/-- If there is no Hamiltonian path, some class cannot simultaneously join
its prescribed pairs by vertex-disjoint paths that cover the entire class. -/
theorem deficient_class {V Q : Type*} [DecidableEq V] (G : SimpleGraph V) (c : V→Q)
    (E : List (V×V)) (positive : 0< E.length) (edge : ∀ e∈E, G.Adj e.1 e.2)
    (absent : ¬ LovaszConjecture.HasHamiltonianPath G) :
    let tag (i : Fin E.length) := c (E.get i).2
    let next (i : Fin E.length) : Fin E.length := ⟨(i.val+1)%E.length,Nat.mod_lt _ positive⟩
    ∃ a : Q, ¬ ∃ L : Fin E.length → List V,
      (∀ i, tag i=a → (L i).head?=some (E.get i).2 ∧ (L i).getLast?=some (E.get (next i)).1 ∧
        (L i).Nodup ∧ (L i).IsChain G.Adj ∧ (∀ z∈L i,c z=a)) ∧
      (∀ i j, tag i=a → tag j=a → i≠j → (L i).Disjoint (L j)) ∧
      (∀ z, c z=a → ∃ i, tag i=a ∧ z∈L i) := by
  intro tag next
  classical
  by_contra! each
  choose L specs apart spans using each
  let pieces := fun i => L (tag i) i
  apply absent (stitch G E positive edge pieces ?_ ?_ ?_)
  · intro i
    obtain ⟨head,last,nodup,ch,_⟩ := specs (tag i) i rfl
    exact ⟨head,last,nodup,ch⟩
  · intro i j ne
    by_cases same : tag i=tag j
    · change (L (tag i) i).Disjoint (L (tag j) j)
      rw [←same]
      exact apart (tag i) i j rfl same.symm ne
    · apply List.disjoint_left.mpr
      intro z hi hj
      have ci := (specs (tag i) i rfl).2.2.2.2 z hi
      have cj := (specs (tag j) j rfl).2.2.2.2 z hj
      exact same (ci.symm.trans cj)
  · intro z
    obtain ⟨i,hi,mem⟩ := spans (c z) z rfl
    exact ⟨i,by simpa [pieces,hi] using mem⟩

end LovaszBlocks

namespace LovaszQuotient
open SimpleGraph Finset

/-- The arrival of each lifted crossing edge and the departure of the next
one have the same label. Every label occurs as an arrival, including the
starting label, which is visited again on the final step. -/
theorem tour_junctions {V Q : Type*} (G : SimpleGraph V) (H : SimpleGraph Q)
    (c : V→Q) {s : Q} (w : H.Walk s s) (E : List (V×V)) (positive : 0< w.length)
    (cover : ∀ i,i∈w.support)
    (align : List.Forall₂ (fun e (d : H.Dart) => c e.1=d.fst ∧ c e.2=d.snd ∧ G.Adj e.1 e.2) E w.darts) :
    ∃ hn : 0< E.length,
      let tag (i : Fin E.length) := c (E.get i).2
      let next (i : Fin E.length) : Fin E.length := ⟨(i.val+1)%E.length,Nat.mod_lt _ hn⟩
      (∀ e∈E,G.Adj e.1 e.2) ∧ Function.Surjective tag ∧ (∀ i,c (E.get (next i)).1=tag i) := by
  have len := align.length_eq.trans w.length_darts
  have pos : 0< E.length := len ▸ positive
  refine ⟨pos,?_⟩
  intro tag next
  have atIndex (i : Fin E.length) :
      c (E.get i).1=w.getVert i.val ∧ c (E.get i).2=w.getVert (i.val+1) ∧ G.Adj (E.get i).1 (E.get i).2 := by
    have inside : i.val< w.darts.length := by rw [← align.length_eq]; exact i.isLt
    have h := align.get i.isLt inside
    simpa only [List.get_eq_getElem, Walk.fst_darts_getElem,Walk.snd_darts_getElem,
      List.getElem_dropLast,List.getElem_tail,Walk.support_getElem_eq_getVert] using h
  refine ⟨?_,?_,?_⟩
  · intro e he
    obtain ⟨j,hj,eq⟩ := List.getElem_of_mem he
    exact eq ▸ (atIndex ⟨j,hj⟩).2.2
  · intro a
    obtain ⟨j,hj,eq⟩ := List.getElem_of_mem (cover a)
    rw [Walk.support_getElem_eq_getVert] at eq
    by_cases zero : j=0
    · subst j
      let i : Fin E.length := ⟨E.length-1,by omega⟩
      have last : i.val+1=w.length := by dsimp [i]; omega
      exact ⟨i,by simpa only [tag,(atIndex i).2.1,last,w.getVert_length,w.getVert_zero] using eq⟩
    · have js := w.length_support
      let i : Fin E.length := ⟨j-1,by omega⟩
      have pre : i.val+1=j := by dsimp [i]; omega
      exact ⟨i,by simpa only [tag,(atIndex i).2.1,pre] using eq⟩
  · intro i
    change c (E.get (next i)).1=c (E.get i).2
    rw [(atIndex (next i)).1,(atIndex i).2.1]
    by_cases small : i.val+1< E.length
    · exact congrArg w.getVert (Nat.mod_eq_of_lt small)
    · have wrap : i.val+1=E.length := by have := i.isLt; omega
      change w.getVert ((i.val+1)%E.length)=w.getVert (i.val+1)
      simp only [wrap,Nat.mod_self,len,w.getVert_zero,w.getVert_length]

end LovaszQuotient

namespace LovaszQuotient
open SimpleGraph

/-- A nontraceable vertex-transitive graph with a bounded invariant quotient
has a concrete cyclic system of disjoint crossing edges and a block whose
specified terminal pairs admit no disjoint spanning path cover. -/
theorem deficient_tour {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    {q k : ℕ} (c : V → Fin q) (trans : LovaszConjecture.IsVertexTransitive G)
    (invariant : ∀ (f : G ≃g G) (a b : V),c (f a)=c (f b) ↔ c a=c b)
    (conn : (G.map c).Connected) (two : 2≤ q) (count : q≤2*k)
    (order : 64*k^3+1≤ Fintype.card V) (absent : ¬LovaszConjecture.HasHamiltonianPath G)
    (start : Fin q) :
    ∃ (w : (G.map c).Walk start start) (E : List (V×V)),
      w.length=2*(q-1) ∧ (∀ i,i∈w.support) ∧
      List.Forall₂ (fun e (d : (G.map c).Dart) => c e.1=d.fst ∧ c e.2=d.snd ∧ G.Adj e.1 e.2) E w.darts ∧
      (E.flatMap fun e => [e.1,e.2]).Nodup ∧ E.length=2*(q-1) ∧
      ∃ pos : 0< E.length,
        let tag (i : Fin E.length) := c (E.get i).2
        let next (i : Fin E.length) : Fin E.length := ⟨(i.val+1)%E.length,Nat.mod_lt _ pos⟩
        (∀ e∈E,G.Adj e.1 e.2) ∧ Function.Surjective tag ∧ (∀ i,c (E.get (next i)).1=tag i) ∧
        ∃ a : Fin q, ¬∃ L : Fin E.length → List V,
          (∀ i,tag i=a → (L i).head?=some (E.get i).2 ∧ (L i).getLast?=some (E.get (next i)).1 ∧
            (L i).Nodup ∧ (L i).IsChain G.Adj ∧ ∀ z∈L i,c z=a) ∧
          (∀ i j,tag i=a → tag j=a → i≠j → (L i).Disjoint (L j)) ∧
          (∀ z,c z=a → ∃ i,tag i=a ∧ z∈L i) := by
  obtain ⟨w,E,len,cover,align,dis⟩ := invariant_tour G c trans invariant conn count order start
  obtain ⟨pos,edges,surj,joins⟩ := tour_junctions G _ c w E (by omega) cover align
  exact ⟨w,E,len,cover,align,dis,align.length_eq.trans (w.length_darts.trans len),pos,
    edges,surj,joins,LovaszBlocks.deficient_class G c E pos edges absent⟩

end LovaszQuotient

namespace LovaszQuotient
open SimpleGraph

/-- In an ordered matching, its departure and arrival labels together index
distinct endpoints. -/
theorem edge_endpoints_injective {V : Type*} (E : List (V×V))
    (nd : (E.flatMap fun e => [e.1,e.2]).Nodup) :
    Function.Injective (fun p : Fin E.length×Bool => if p.2 then (E.get p.1).1 else (E.get p.1).2) := by
  let e (i : Fin E.length) (b : Bool) := if b then (E.get i).1 else (E.get i).2
  have member (i : Fin E.length) (b : Bool) : e i b ∈ [(E.get i).1,(E.get i).2] := by cases b <;> simp [e]
  have ⟨distinct,apart⟩ := List.nodup_flatMap.mp nd
  have unequal (i : Fin E.length) : (E.get i).1 ≠ (E.get i).2 := by
    simpa using distinct _ (List.get_mem E i)
  have cannot {i j : Fin E.length} (hj : i.val< j.val) (a b : Bool) : e i a≠e j b := by
    have dis := (List.pairwise_iff_getElem.mp apart) i.val j.val i.isLt j.isLt hj
    intro eq
    exact List.disjoint_left.mp dis (member i a) (eq ▸ member j b)
  rintro ⟨i,a⟩ ⟨j,b⟩ eq
  change e i a=e j b at eq
  have ij : i=j := by
    rcases lt_trichotomy i.val j.val with h|h|h
    · exact (cannot h a b eq).elim
    · exact Fin.ext h
    · exact (cannot h b a eq.symm).elim
  subst j
  have h := unequal i
  have hh := h.symm
  cases a <;> cases b <;> simp_all [e]

/-- The cyclic successor on a nonempty finite ordinal is injective. -/
theorem cyclic_injective {n : ℕ} (pos : 0< n) :
    Function.Injective (fun i : Fin n => (⟨(i.val+1)%n,Nat.mod_lt _ pos⟩ : Fin n)) := by
  intro i j eq
  have h := congrArg Fin.val eq
  change (i.val+1)%n=(j.val+1)%n at h
  apply Fin.ext
  have hi := i.isLt
  have hj := j.isLt
  by_cases a : i.val+1< n <;> by_cases b : j.val+1< n
  · rwa [Nat.mod_eq_of_lt a,Nat.mod_eq_of_lt b,Nat.add_right_cancel_iff] at h
  · rw [Nat.mod_eq_of_lt a,show j.val+1=n by omega,Nat.mod_self] at h; omega
  · rw [Nat.mod_eq_of_lt b,show i.val+1=n by omega,Nat.mod_self] at h; omega
  · omega

end LovaszQuotient

namespace LovaszQuotient
open SimpleGraph

/-- A large nontraceable vertex-transitive graph with a bounded invariant
partition has a block and at most q-1 pairs of distinct terminals that cannot
be linked disjointly by paths covering the entire block. -/
theorem local_obstruction {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    {q k : ℕ} (c : V → Fin q) (trans : LovaszConjecture.IsVertexTransitive G)
    (invariant : ∀ (f : G ≃g G) (a b : V),c (f a)=c (f b) ↔ c a=c b)
    (conn : (G.map c).Connected) (two : 2≤ q) (count : q≤2*k)
    (order : 64*k^3+1≤ Fintype.card V) (absent : ¬LovaszConjecture.HasHamiltonianPath G) :
    ∃ (a : Fin q) (r : ℕ) (T : (Fin r×Bool) ↪ V), 1≤ r ∧ r≤ q-1 ∧
      (∀ h,c (T h)=a) ∧ ¬ ∃ paths : Fin r→List V,
        (∀ i,(paths i).head?=some (T (i,false)) ∧ (paths i).getLast?=some (T (i,true)) ∧
          (paths i).Nodup ∧ (paths i).IsChain G.Adj ∧ ∀ z∈paths i,c z=a) ∧
        (∀ i j,i≠j → (paths i).Disjoint (paths j)) ∧
        (∀ z,c z=a → ∃ i,z∈paths i) := by
  classical
  obtain ⟨w,E,_,_,align,dis,elen,pos,_,surj,joins,a,fail⟩ :=
    deficient_tour G c trans invariant conn two count order absent ⟨0,by omega⟩
  let tag (i : Fin E.length) := c (E.get i).2
  let next (i : Fin E.length) : Fin E.length := ⟨(i.val+1)%E.length,Nat.mod_lt _ pos⟩
  let A := {i : Fin E.length // tag i=a}
  let r := Fintype.card A
  let f : Fin r ≃ A := (Fintype.equivFin A).symm
  have nj : Function.Injective next := cyclic_injective pos
  have distinct (i : Fin E.length) : c (E.get i).1≠c (E.get i).2 := by
    have len := align.length_eq
    have hj : i.val< w.darts.length := len ▸ i.isLt
    obtain ⟨l,r,_⟩ := align.get i.isLt hj
    exact l ▸ r ▸ (w.darts.get ⟨i.val,hj⟩).adj.ne
  have diff (i : A) : tag (next i.val)≠a := by
    intro eq
    exact distinct (next i.val) ((joins i.val).trans (i.property.trans eq.symm))
  let other (i : A) : {j : Fin E.length // ¬tag j=a} := ⟨next i.val,diff i⟩
  have bound := Fintype.card_le_of_injective other (fun _ _ eq => Subtype.ext (nj (congrArg Subtype.val eq)))
  rw [Fintype.card_subtype_compl,Fintype.card_fin] at bound
  have lim : r≤ q-1 := by change r≤ E.length-r at bound; omega
  let slot (h : Fin r×Bool) : Fin E.length×Bool :=
    (if h.2 then next (f h.1).val else (f h.1).val,h.2)
  have slots : Function.Injective slot := by
    rintro ⟨i,a⟩ ⟨j,b⟩ eq
    have last : a=b := congrArg Prod.snd eq
    subst b
    have first := congrArg Prod.fst eq
    suffices i=j by congr
    apply f.injective
    apply Subtype.ext
    cases a
    · exact first
    · exact nj first
  let T : (Fin r×Bool) ↪ V := ⟨fun h => if (slot h).2 then (E.get (slot h).1).1 else (E.get (slot h).1).2,
    (edge_endpoints_injective E dis).comp slots⟩
  obtain ⟨i,hi⟩ := surj a
  have rn : 0< r := Fintype.card_pos_iff.mpr ⟨(⟨i,hi⟩ : A)⟩
  refine ⟨a,r,T,rn,lim,?_,?_⟩
  · rintro ⟨j,b⟩
    cases b
    · exact (f j).property
    · exact (joins (f j).val).trans (f j).property
  · rintro ⟨paths,good,apart,allv⟩
    apply fail
    let L (i : Fin E.length) := if h : tag i=a then paths (f.symm ⟨i,h⟩) else []
    have hL (i : Fin E.length) (hi : tag i=a) : L i=paths (f.symm ⟨i,hi⟩) := dif_pos hi
    refine ⟨L,?_,?_,?_⟩
    · intro i h
      let ai : A := ⟨i,h⟩
      have eq : f (f.symm ai)=ai := f.apply_symm_apply ai
      rw [hL i h]
      simpa only [T,Function.Embedding.coeFn_mk,slot,Bool.false_eq_true,if_false,if_true,
        eq,ai] using good (f.symm ai)
    · intro i j hi hj ne
      have different : f.symm (⟨i,hi⟩ : A)≠f.symm ⟨j,hj⟩ :=
        fun eq => ne (congrArg Subtype.val (f.symm.injective eq))
      rw [hL i hi,hL j hj]
      exact apart _ _ different
    · intro z hz
      obtain ⟨j,hj⟩ := allv z hz
      refine ⟨(f j).val,(f j).property,?_⟩
      rw [hL _ (f j).property]
      change z∈paths (f.symm (f j))
      simpa only [Equiv.symm_apply_apply] using hj

end LovaszQuotient

namespace LovaszDensity
open SimpleGraph

/-- An edge whose endpoints have equal distance parity closes two shortest walks to the root. -/
theorem odd_walk_from_nonbipartite {V : Type*} (G : SimpleGraph V) (conn : G.Connected)
    (nonbip : ¬G.IsBipartite) (x : V) :
    ∃ (a b : V) (p : G.Walk x x), Odd p.length ∧ p.length = G.dist x a + 1 + G.dist x b := by
  let color (a : V) : Fin 2 := ⟨G.dist x a % 2, Nat.mod_lt _ (by decide)⟩
  obtain ⟨a,b,adj,same⟩ : ∃ a b : V, G.Adj a b ∧ color a = color b := by
    by_contra! proper
    exact nonbip ⟨SimpleGraph.Coloring.mk color (fun {u v} h => proper u v h)⟩
  obtain ⟨pa,la⟩ := conn.exists_walk_length_eq_dist x a
  obtain ⟨pb,lb⟩ := conn.exists_walk_length_eq_dist x b
  let p := pa.append (Walk.cons adj pb.reverse)
  have len : p.length = G.dist x a + 1 + G.dist x b := by simp [p,la,lb]; omega
  have parity : G.dist x a % 2 = G.dist x b % 2 := congrArg Fin.val same
  refine ⟨a,b,p,?_,len⟩
  rw [len]
  exact ⟨(G.dist x a + 1 + G.dist x b)/2,by omega⟩

end LovaszDensity

namespace LovaszDense
open SimpleGraph Finset

/-- On a closed odd walk, consecutive vertices cannot both lie in an
independent set. Summing the two endpoint indicators over oriented edges
counts every occurrence twice. -/
theorem walk_independent_count {V : Type*} {G : SimpleGraph V}
    (w : V → ℕ) (edge : ∀ {a b}, G.Adj a b → w a + w b ≤ 1) {x y : V}
    (p : G.Walk x y) : 2*(p.support.tail.map w).sum + w x ≤ p.length + w y := by
  induction p with
  | nil => simp
  | @cons x y z h p ih =>
    have support : (Walk.cons h p).support.tail = y :: p.support.tail := p.cons_tail_support.symm
    rw [support, List.map_cons, List.sum_cons, Walk.length_cons]
    have := edge h
    omega

/-- The independent-set bound from an arbitrary closed walk of odd length.
We average the half-length bound over all graph automorphisms; repeated
vertices of the walk retain their multiplicities. -/
theorem independent_odd_walk {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (vt : LovaszConjecture.IsVertexTransitive G) {x : V} (p : G.Walk x x) (odd : Odd p.length) :
    Fintype.card V + 2 * (p.length * G.indepNum) ≤ p.length * Fintype.card V := by
  classical
  obtain ⟨I, hi⟩ := G.exists_isNIndepSet_indepNum
  let w (v : V) : ℕ := if v ∈ I then 1 else 0
  have weight : (∑ v, w v) = G.indepNum := by simpa [w] using hi.card_eq
  have edge (g : G ≃g G) {a b : V} (h : G.Adj a b) : w (g a) + w (g b) ≤ 1 := by
    have adj : G.Adj (g a) (g b) := g.map_rel_iff.mpr h
    have exclude (ha : g a ∈ I) (hb : g b ∈ I) : False :=
      (G.isIndepSet_iff.mp hi.isIndepSet ha hb adj.ne) adj
    by_cases ha : g a ∈ I <;> by_cases hb : g b ∈ I <;> simp_all [w]
  let : Finite (G ≃g G) := Finite.of_injective (fun g : G ≃g G => (g : V → V))
    (fun _ _ h => RelIso.ext (congrFun h))
  let : Fintype (G ≃g G) := Fintype.ofFinite _
  have : Nonempty (G ≃g G) := ⟨RelIso.refl _⟩
  let n := Fintype.card V
  let a := Fintype.card (G ≃g G)
  have pos : 0 < a := Fintype.card_pos
  let load (l : List V) (g : G ≃g G) := (l.map (fun v => w (g v))).sum
  have average (l : List V) : n*(∑ g : G ≃g G, load l g) = a*(l.length*G.indepNum) := by
    induction l with
    | nil => simp [load]
    | cons v l ih =>
      have atV := LovaszDensity.uniform_load G vt w v
      rw [weight] at atV
      change n*(∑ g : G ≃g G, w (g v)) = a*G.indepNum at atV
      simp only [load, List.map_cons, List.sum_cons, List.length_cons, sum_add_distrib,
        mul_add] at ih ⊢
      rw [atV, ih]
      ring
  let L := p.support.tail
  have size : L.length = p.length := by simp [L,Walk.length_support]
  have bounded (g : G ≃g G) : load L g ≤ p.length/2 := by
    have := walk_independent_count _ (edge g) p
    change 2*load L g + _ ≤ _ at this
    omega
  have total := sum_le_sum (s:=univ) fun g _ => bounded g
  simp only [sum_const,card_univ,nsmul_eq_mul] at total
  have h := Nat.mul_le_mul_left n total
  rw [average, size] at h
  have h' : a*(p.length*G.indepNum) ≤ a*((p.length/2)*n) := by
    calc
      _ ≤ n * (a * (p.length / 2)) := h
      _ = _ := by ac_rfl
  have half := Nat.le_of_mul_le_mul_left h' pos
  obtain ⟨k,hk⟩ := odd
  have hd : p.length / 2 = k := by omega
  rw [hd] at half
  calc
    _ ≤ n+2*(k*n) := by change n+2*(p.length*G.indepNum) ≤ _; omega
    _ = p.length*n := by rw [hk]; ring

end LovaszDense

namespace LovaszDense
open SimpleGraph Finset

/-- Two neighbors of a vertex on a shortest odd closed walk must lie two
steps apart along one of the two orientations of that walk. -/
theorem neighbor_positions {V : Type*} {G : SimpleGraph V} {x w : V} (p : G.Walk x x)
    (odd : Odd p.length)
    (least : ∀ {v : V} (q : G.Walk v v), Odd q.length → p.length ≤ q.length)
    {i j : ℕ} (lt : i < j) (stop : j < p.length)
    (hi : G.Adj w (p.getVert i)) (hj : G.Adj w (p.getVert j)) :
    j = i+2 ∨ j+2 = i+p.length := by
  let s := (p.drop i).take (j-i)
  have endpoint : (p.drop i).getVert (j-i) = p.getVert j := by
    rw [Walk.drop_getVert, Nat.add_sub_of_le lt.le]
  let q := (s.copy rfl endpoint).append (Walk.cons hj.symm (Walk.cons hi Walk.nil))
  have qlen : q.length = (j-i)+2 := by
    simp [q,s,Walk.take_length,Walk.drop_length,inf_eq_left.mpr (show j-i ≤ p.length-i by omega)]
  let r := ((p.drop j).append (p.take i)).append (Walk.cons hi.symm (Walk.cons hj Walk.nil))
  have rlen : r.length = p.length-j+i+2 := by
    simp [r,Walk.drop_length,Walk.take_length,inf_eq_left.mpr (show i ≤ p.length by omega)]
  obtain ⟨a,ha⟩ := odd
  by_cases d : (j-i)%2=1
  · have bound := least q ⟨q.length/2,by omega⟩
    omega
  · have bound := least r ⟨r.length/2,by omega⟩
    omega

/-- A shortest odd closed walk of length at least five receives at most two
incidences per vertex. Summing the degrees along the walk bounds its length. -/
theorem shortest_odd_degree {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {x : V} (p : G.Walk x x) (odd : Odd p.length) (five : 5≤ p.length)
    (least : ∀ {v : V} (q : G.Walk v v), Odd q.length → p.length ≤ q.length) :
    p.length * G.minDegree ≤ 2*Fintype.card V := by
  classical
  let R (i : ℕ) (w : V) := G.Adj w (p.getVert i)
  have neighbors (w : V) : ((range p.length).bipartiteBelow R w).card ≤ 2 := by
    by_contra! large
    obtain ⟨i,j,k,hi,hj,hk,ij,ik,jk⟩ := two_lt_card_iff.mp large
    have facts {i : ℕ} (h : i ∈ (range p.length).bipartiteBelow R w) :
        i< p.length ∧ G.Adj w (p.getVert i) := ⟨mem_range.mp (mem_filter.mp h).1,(mem_filter.mp h).2⟩
    have sep (i j : ℕ) (hi : i ∈ (range p.length).bipartiteBelow R w)
        (hj : j ∈ (range p.length).bipartiteBelow R w) (ne : i ≠ j) :
        i=j+2 ∨ j=i+2 ∨ i+2=j+p.length ∨ j+2=i+p.length := by
      rcases lt_or_gt_of_ne ne with lt | gt
      · have := neighbor_positions p odd least lt (facts hj).1 (facts hi).2 (facts hj).2
        omega
      · have := neighbor_positions p odd least gt (facts hi).1 (facts hj).2 (facts hi).2
        omega
    have ab := sep i j hi hj ij
    have ac := sep i k hi hk ik
    have bc := sep j k hj hk jk
    have := (facts hi).1
    have := (facts hj).1
    have := (facts hk).1
    obtain ⟨s,hs⟩ := odd
    omega
  have degree (i : ℕ) : G.minDegree ≤ (univ.bipartiteAbove R i).card := by
    have eq : univ.bipartiteAbove R i = G.neighborFinset (p.getVert i) := by
      ext w
      simp [bipartiteAbove,R,adj_comm]
    rw [eq, G.card_neighborFinset_eq_degree]
    exact G.minDegree_le_degree _
  have count := Finset.card_mul_le_card_mul (s:=range p.length) (t:=univ) R
    (fun i _ => degree i) (fun w _ => neighbors w)
  simpa [Nat.mul_comm] using count

end LovaszDense

namespace LovaszDense
open SimpleGraph Finset

/-- For a nonempty independent set, every neighbor of one of its vertices
lies in its complement. -/
theorem independence_plus_degree {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (x : V) : G.indepNum + G.minDegree ≤ Fintype.card V := by
  classical
  obtain ⟨I,hI⟩ := G.exists_isNIndepSet_indepNum
  by_cases nonempty : I.Nonempty
  · obtain ⟨v,hv⟩ := nonempty
    have sep : Disjoint I (G.neighborFinset v) := by
      apply Finset.disjoint_left.mpr
      intro w hw edge
      have adj := (G.mem_neighborFinset ..).mp edge
      exact (G.isIndepSet_iff.mp hI.isIndepSet hv hw adj.ne) adj
    have bound := (I ∪ G.neighborFinset v).card_le_univ
    rw [card_union_of_disjoint sep,hI.card_eq,G.card_neighborFinset_eq_degree] at bound
    have := G.minDegree_le_degree v
    omega
  · have zero : G.indepNum = 0 := by rw [←hI.card_eq,not_nonempty_iff_eq_empty.mp nonempty,card_empty]
    rw [zero, zero_add]
    exact (G.minDegree_le_degree x).trans (G.neighborFinset x).card_le_univ

/-- The sharp independence gap for connected vertex-transitive nonbipartite
graphs. Replacing every vertex in an odd cycle by an independent set of
the same size shows the degree coefficient is attained. -/
theorem nonbip_sharp_gap {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (conn : G.Connected) (vt : LovaszConjecture.IsVertexTransitive G)
    (nonbip : ¬G.IsBipartite) : 4*G.indepNum + G.minDegree ≤ 2*Fintype.card V := by
  classical
  obtain ⟨v⟩ := conn.nonempty
  let has (l : ℕ) := ∃ (x : V) (p : G.Walk x x), Odd p.length ∧ p.length=l
  have existsOdd : ∃ l, has l := by
    obtain ⟨_,_,p,odd,_⟩ := LovaszDensity.odd_walk_from_nonbipartite G conn nonbip v
    exact ⟨p.length,v,p,odd,rfl⟩
  obtain ⟨x,p,odd,size⟩ := Nat.find_spec existsOdd
  have least {z : V} (q : G.Walk z z) (hq : Odd q.length) : p.length ≤ q.length :=
    size ▸ Nat.find_min' existsOdd (show has q.length from ⟨z,q,hq,rfl⟩)
  let n := Fintype.card V
  have : Nonempty V := ⟨v⟩
  have pos : 0 < n := Fintype.card_pos
  have counter := independent_odd_walk G vt p odd
  change n + 2*(p.length*G.indepNum) ≤ p.length*n at counter
  by_cases five : 5 ≤ p.length
  · have twice : 2*G.indepNum ≤ n := by
      have simpBound : p.length * (2*G.indepNum) ≤ p.length*n := by nlinarith only [counter]
      exact Nat.le_of_mul_le_mul_left simpBound (by omega)
    let gap := n - 2*G.indepNum
    have decomp : n = gap + 2*G.indepNum := by dsimp [gap]; omega
    have lower : n ≤ p.length*gap := by
      have sum : p.length*n = p.length*gap + 2*(p.length*G.indepNum) := by
        calc
          _ = p.length*(gap+2*G.indepNum) := congrArg (p.length*·) decomp
          _ = _ := by ring
      omega
    have upper := shortest_odd_degree p odd five @least
    have capped : G.minDegree ≤ 2*gap := by
      suffices h : n*G.minDegree ≤ n*(2*gap) from Nat.le_of_mul_le_mul_left h pos
      calc
        n*G.minDegree ≤ (p.length*gap)*G.minDegree := Nat.mul_le_mul_right _ lower
        _ = (p.length*G.minDegree)*gap := by ac_rfl
        _ ≤ (2*n)*gap := Nat.mul_le_mul_right _ upper
        _ = n*(2*gap) := by ac_rfl
    change 4*G.indepNum + G.minDegree ≤ 2*n
    omega
  · have small : p.length = 1 ∨ p.length = 3 := by obtain ⟨a,ha⟩ := odd; omega
    have bounded : 3*G.indepNum ≤ n := by
      rcases small with one|three
      · rw [one] at counter
        omega
      · rw [three] at counter
        omega
    have neighbor := independence_plus_degree G v
    change G.indepNum+G.minDegree ≤ n at neighbor
    change 4*G.indepNum+G.minDegree ≤ 2*n
    omega

/-- Natural reciprocal-density form. The denominator two is sharp over all
odd-cycle blow-ups. -/
theorem nonbip_sharp_reciprocal {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (conn : G.Connected) (vt : LovaszConjecture.IsVertexTransitive G)
    (nonbip : ¬G.IsBipartite) (k : ℕ) (density : Fintype.card V ≤ k*G.minDegree) :
    Fintype.card V ≤ 2*k*(Fintype.card V-2*G.indepNum) := by
  have bound := nonbip_sharp_gap G conn vt nonbip
  have : G.minDegree ≤ 2*(Fintype.card V-2*G.indepNum) := by omega
  calc
    _ ≤ k*G.minDegree := density
    _ ≤ k*(2*(Fintype.card V-2*G.indepNum)) := Nat.mul_le_mul_left k this
    _ = _ := by ac_rfl

end LovaszDense

namespace LovaszBlocks
open SimpleGraph

/-- An ambient automorphism mapping the root into another block restricts
to an isomorphism of the two induced block graphs. -/
theorem restrict_automorphism {V : Type*} (G : SimpleGraph V) (r : Setoid V)
    (invariant : ∀ (f : G ≃g G) (u v : V), r.r (f u) (f v) ↔ r.r u v)
    (f : G ≃g G) (x y : V) (hit : r.r y (f x)) :
    ∃ h : G.induce {z | r.r x z} ≃g G.induce {z | r.r y z},
      ∀ a, (h a).val = f a.val := by
  have cls (z : V) : r.r x z ↔ r.r y (f z) :=
    ⟨fun h => r.trans hit ((invariant f x z).2 h),
      fun h => (invariant f x z).1 (r.trans (r.symm hit) h)⟩
  let E := f.toEquiv.subtypeEquiv cls
  let T : G.induce {z | r.r x z} ≃g G.induce {z | r.r y z} :=
    ⟨E, by intro a b; exact f.map_adj_iff⟩
  exact ⟨T,fun _ => rfl⟩

/-- The setwise stabilizer of a block acts transitively on that block, by
automorphisms of its induced graph. -/
theorem block_stabilizer {V : Type*} (G : SimpleGraph V) (r : Setoid V)
    (invariant : ∀ (f : G ≃g G) (u v : V), r.r (f u) (f v) ↔ r.r u v)
    (transitive : LovaszConjecture.IsVertexTransitive G) (x : V)
    (a b : {z : V // r.r x z}) :
    ∃ f : G ≃g G, ∃ g : G.induce {z | r.r x z} ≃g G.induce {z | r.r x z},
      (∀ z, r.r x (f z) ↔ r.r x z) ∧ (∀ c, (g c).val = f c.val) ∧ g a=b := by
  obtain ⟨f,move⟩ := transitive a.val b.val
  have hit : r.r x (f x) := r.trans (move ▸ b.property) ((invariant f a.val x).2 (r.symm a.property))
  obtain ⟨g,action⟩ := restrict_automorphism G r invariant f x x hit
  refine ⟨f,g,?_,action,Subtype.ext ((action a).trans move)⟩
  intro z
  exact ⟨fun h => (invariant f x z).1 (r.trans (r.symm hit) h),
    fun h => r.trans hit ((invariant f x z).2 h)⟩

/-- Collapsing adjacent vertices to the same quotient point shortens the
projected walk. -/
theorem quotient_connected {V : Type*} (G : SimpleGraph V) (r : Setoid V)
    (connected : G.Connected) : (G.map (Quotient.mk r)).Connected := by
  let q := Quotient.mk r
  have mapped {a b : V} (p : G.Walk a b) : (G.map q).Reachable (q a) (q b) := by
    induction p with
    | nil => exact .rfl
    | @cons a b c edge tail ih =>
      by_cases eq : q a=q b
      · exact eq ▸ ih
      · exact (G.map_adj_apply' edge eq).reachable.trans ih
  obtain ⟨v⟩ := connected.nonempty
  have : Nonempty (Quotient r) := ⟨q v⟩
  apply SimpleGraph.Connected.mk
  · intro i j
    induction i using Quotient.inductionOn with | _ x =>
      induction j using Quotient.inductionOn with | _ y =>
        exact mapped (Classical.choice (connected x y))

/-- Automorphisms descend to the simple quotient graph and retain their
original action on the projected vertices. -/
theorem quotient_automorphism {V : Type*} (G : SimpleGraph V) (r : Setoid V)
    (invariant : ∀ (f : G ≃g G) (u v : V), r.r (f u) (f v) ↔ r.r u v)
    (f : G ≃g G) : ∃ F : G.map (Quotient.mk r) ≃g G.map (Quotient.mk r),
      ∀ a, F (Quotient.mk r a)=Quotient.mk r (f a) := by
  let q := Quotient.mk r
  let E : Quotient r ≃ Quotient r := Quotient.congr f.toEquiv (fun a b => (invariant f a b).symm)
  have acts (a : V) : E (q a)=q (f a) := rfl
  refine ⟨⟨E,?_⟩,acts⟩
  intro u v
  change (G.map q).Adj (E u) (E v) ↔ (G.map q).Adj u v
  simp only [SimpleGraph.map_adj']
  constructor
  · rintro ⟨ne,a,b,hit,ha,hb⟩
    refine ⟨fun h => ne (congrArg E h),f.symm a,f.symm b,f.symm.map_rel_iff.mpr hit,E.injective ?_,E.injective ?_⟩
    · simpa only [acts,RelIso.apply_symm_apply] using ha
    · simpa only [acts,RelIso.apply_symm_apply] using hb
  · rintro ⟨ne,a,b,hit,ha,hb⟩
    exact ⟨fun h => ne (E.injective h),f a,f b,f.map_rel_iff.mpr hit,
      (acts a).symm.trans (congrArg E ha),(acts b).symm.trans (congrArg E hb)⟩

/-- On every finite vertex-transitive graph, the quotient order times the
size of one block is the original order. -/
theorem block_product {V : Type*} [Fintype V] (G : SimpleGraph V) (r : Setoid V)
    (invariant : ∀ (f : G ≃g G) (u v : V), r.r (f u) (f v) ↔ r.r u v)
    (transitive : LovaszConjecture.IsVertexTransitive G) (x : V) :
    Fintype.card V = Nat.card (Quotient r) * Nat.card {z : V // r.r x z} := by
  classical
  let q := Quotient.mk r
  have fiber (k : Quotient r) : Nonempty ({z : V // q z=k} ≃ {z : V // r.r x z}) := by
    induction k using Quotient.inductionOn with | _ y =>
      obtain ⟨f,move⟩ := transitive y x
      obtain ⟨g,_⟩ := restrict_automorphism G r invariant f y x (by rw [move])
      have cls (z : V) : q z=q y ↔ r.r y z :=
        ⟨fun h => r.symm (Quotient.exact h), fun h => Quotient.sound (r.symm h)⟩
      exact ⟨(Equiv.subtypeEquivRight cls).trans g.toEquiv⟩
  let E : V ≃ (Quotient r × {z : V // r.r x z}) :=
    ((Equiv.sigmaFiberEquiv q).symm.trans (Equiv.sigmaCongrRight fun k => (fiber k).some)).trans
      (Equiv.sigmaEquivProd _ _)
  simpa only [Nat.card_eq_fintype_card (α:=V),Nat.card_prod] using Nat.card_congr E

/-- The quotient is connected and vertex-transitive, each induced class is
vertex-transitive, and the class sizes all agree. -/
theorem invariant_quotient {V : Type*} [Fintype V] (G : SimpleGraph V) (r : Setoid V)
    (connected : G.Connected) (transitive : LovaszConjecture.IsVertexTransitive G)
    (invariant : ∀ (f : G ≃g G) (u v : V), r.r (f u) (f v) ↔ r.r u v) :
    (G.map (Quotient.mk r)).Connected ∧
    LovaszConjecture.IsVertexTransitive (G.map (Quotient.mk r)) ∧
    (∀ x : V, LovaszConjecture.IsVertexTransitive (G.induce {z | r.r x z})) ∧
    (∀ x y : V, Nat.card {z : V // r.r x z} = Nat.card {z : V // r.r y z}) ∧
    (∀ x : V, Fintype.card V = Nat.card (Quotient r) * Nat.card {z : V // r.r x z}) := by
  refine ⟨quotient_connected G r connected,?_,?_,?_,block_product G r invariant transitive⟩
  · intro i j
    induction i using Quotient.inductionOn with | _ x =>
      induction j using Quotient.inductionOn with | _ y =>
        obtain ⟨f,eq⟩ := transitive x y
        obtain ⟨F,h⟩ := quotient_automorphism G r invariant f
        exact ⟨F,(h x).trans (congrArg (Quotient.mk r) eq)⟩
  · intro x a b
    obtain ⟨_,g,_,_,hit⟩ := block_stabilizer G r invariant transitive x a b
    exact ⟨g,hit⟩
  · intro x y
    obtain ⟨f,eq⟩ := transitive x y
    obtain ⟨g,_⟩ := restrict_automorphism G r invariant f x y (by rw [eq])
    exact Nat.card_congr g.toEquiv

end LovaszBlocks

namespace LovaszBlocks
open SimpleGraph

/-- For a surjective labeling of the blocks, the quotient is the graph on
those very labels obtained by mapping the original graph along the label map. -/
theorem labeled_blocks {V : Type*} [Fintype V] (G : SimpleGraph V) {q : ℕ} (c : V→Fin q)
    (onto : Function.Surjective c) (conn : G.Connected) (trans : LovaszConjecture.IsVertexTransitive G)
    (invariant : ∀ (f : G ≃g G) (u v : V), c (f u)=c (f v) ↔ c u=c v) :
    (G.map c).Connected ∧ LovaszConjecture.IsVertexTransitive (G.map c) ∧
    (∀ i, LovaszConjecture.IsVertexTransitive (G.induce {z | c z=i})) ∧
    (∀ i j, Nat.card {z : V // c z=i} = Nat.card {z : V // c z=j}) ∧
    (∀ i, Fintype.card V = q*Nat.card {z : V // c z=i}) := by
  let r := Setoid.ker c
  let Q := G.map (Quotient.mk r)
  let E : Quotient r ≃ Fin q := Setoid.quotientKerEquivOfSurjective c onto
  have changeMap : Q.map E = G.map c := by
    rw [show Q=G.map (Quotient.mk r) from rfl,SimpleGraph.map_map]
    rfl
  let F : Q ≃g G.map c := changeMap ▸ Iso.map E Q
  obtain ⟨con,vt,cls,same,card⟩ := invariant_quotient G r conn trans invariant
  have rset (x : V) : {z | r.r x z} = {z | c z=c x} := Set.ext fun _ => eq_comm
  have rcard (x : V) : Nat.card {z : V // r.r x z}=Nat.card {z : V // c z=c x} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun _ => eq_comm)
  refine ⟨con.map F.toHom F.toEquiv.surjective,?_,?_,?_,?_⟩
  · intro i j
    obtain ⟨e,h⟩ := vt (F.symm i) (F.symm j)
    exact ⟨F.symm.trans (e.trans F),by change F (e (F.symm i))=j; rw [h,F.apply_symm_apply]⟩
  · intro i
    obtain ⟨x,rfl⟩ := onto i
    exact rset x ▸ cls x
  · intro i j
    obtain ⟨x,rfl⟩ := onto i
    obtain ⟨y,rfl⟩ := onto j
    exact (rcard x).symm.trans ((same x y).trans (rcard y))
  · intro i
    obtain ⟨x,rfl⟩ := onto i
    simpa only [Nat.card_congr E,Nat.card_fin,rcard] using card x

end LovaszBlocks

namespace LovaszBlocks
open SimpleGraph

/-- Two traceable, vertex-transitive parts of a connected graph can be
joined at a crossing edge, by moving endpoints independently in each part. -/
theorem join_two {V : Type*} [DecidableEq V] (G : SimpleGraph V) (side : V→Bool)
    (onto : Function.Surjective side) (conn : G.Connected)
    (trans : ∀ b, LovaszConjecture.IsVertexTransitive (G.induce {v | side v=b}))
    (paths : ∀ b, LovaszConjecture.HasHamiltonianPath (G.induce {v | side v=b})) :
    LovaszConjecture.HasHamiltonianPath G := by
  classical
  obtain ⟨u,hu⟩ := onto false
  obtain ⟨v,hv⟩ := onto true
  obtain ⟨w⟩ := conn u v
  obtain ⟨d,_,ha,hn⟩ := w.exists_boundary_dart {x | side x=false} hu (by simp [hv])
  have hb : side d.snd=true := by
    change ¬side d.snd=false at hn
    cases h : side d.snd <;> simp_all
  let X := {x : V | side x=false}
  let Y := {x : V | side x=true}
  obtain ⟨a,b,p,hp⟩ := paths false
  obtain ⟨c,e,q,hq⟩ := paths true
  obtain ⟨f,move⟩ := trans false b ⟨d.fst,ha⟩
  obtain ⟨g,send⟩ := trans true c ⟨d.snd,hb⟩
  let P := p.map f.toHom
  let Q := q.map g.toHom
  have first : P.IsHamiltonian := Walk.IsHamiltonian.map f.toHom f.toEquiv.bijective hp
  have second : Q.IsHamiltonian := Walk.IsHamiltonian.map g.toHom g.toEquiv.bijective hq
  let left := (Embedding.induce (G:=G) X).toHom
  let right := (Embedding.induce (G:=G) Y).toHom
  let L := P.map left
  let R := Q.map right
  have cut : G.Adj (left (f b)) (right (g c)) := by
    change G.Adj (f b).val (g c).val
    rw [move,send]
    exact d.adj
  let total := L.append (.cons cut R)
  have list : total.support = P.support.map (fun x => x.val) ++ Q.support.map (fun x => x.val) := by
    simp only [total,Walk.support_append,Walk.support_cons,List.tail_cons,L,R,Walk.support_map]
    rfl
  refine ⟨_,_,total,Walk.IsPath.isHamiltonian_of_mem ?_ ?_⟩
  · apply (Walk.isPath_def _).mpr
    rw [list,List.nodup_append]
    refine ⟨first.isPath.support_nodup.map Subtype.val_injective,
      second.isPath.support_nodup.map Subtype.val_injective,?_⟩
    rintro x hx y hy rfl
    obtain ⟨s,_,rfl⟩ := List.mem_map.mp hx
    obtain ⟨t,_,eq⟩ := List.mem_map.mp hy
    have h1 : side s.val=false := s.property
    have h2 : side t.val=true := t.property
    rw [eq,h1] at h2
    contradiction
  · intro x
    rw [list,List.mem_append]
    cases h : side x with
    | false => exact Or.inl (List.mem_map.mpr ⟨⟨x,h⟩,first.mem_support _,rfl⟩)
    | true => exact Or.inr (List.mem_map.mpr ⟨⟨x,h⟩,second.mem_support _,rfl⟩)

end LovaszBlocks

namespace LovaszBlocks
open SimpleGraph Finset LovaszConjecture

/-- For a nonempty surviving vertex set, preconnectivity is connectivity. -/
theorem connected_iron_of_preconnected {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (b : ℕ) (small : b < Fintype.card V)
    (all : ∀ (F : SimpleGraph V) [DecidableRel F.Adj] (S : Finset V), S.card≤ b →
      (∀ x, F.degree x≤ b) → ((G \ F).induce (Sᶜ : Finset V)).Preconnected) :
    ∀ (S : Finset V) (F : SimpleGraph V) [DecidableRel F.Adj], S.card≤ b →
      (∀ x, F.degree x≤ b) → ((G \ F).induce (Sᶜ : Finset V)).Connected := by
  intro S F inst cap loss
  have pos : 0< Sᶜ.card := by rw [Finset.card_compl]; omega
  obtain ⟨v,hv⟩ := Finset.card_pos.mp pos
  let : Nonempty (↑(Sᶜ : Finset V) : Set V) := ⟨⟨v,hv⟩⟩
  exact ⟨all F S cap loss⟩

/-- Iron connectivity on the trivial deletion implies connectivity of the original graph. -/
theorem connected_of_iron {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) {b : ℕ}
    (all : ∀ (F : SimpleGraph V) [DecidableRel F.Adj] (S : Finset V), S.card≤ b →
      (∀ x, F.degree x≤ b) → ((G \ F).induce (Sᶜ : Finset V)).Preconnected) :
    G.Connected := by
  classical
  let S : Finset V := ∅
  have whole := all ⊥ S (by simp [S]) (by simp)
  refine ⟨?_⟩
  intro u v
  have hu : u ∈ Sᶜ := by simp [S]
  have hv : v ∈ Sᶜ := by simp [S]
  obtain ⟨p⟩ := whole ⟨u,hu⟩ ⟨v,hv⟩
  let e := SimpleGraph.Embedding.induce (G:=G \ ⊥) (Sᶜ : Finset V)
  have reach : (G \ ⊥).Reachable u v := ⟨p.map e.toHom⟩
  simpa using reach

/-- A connected counterexample partitioned into traceable transitive classes
needs at least three classes. -/
theorem three_traceable_blocks {V : Type*} [DecidableEq V] (G : SimpleGraph V) {q : ℕ}
    (c : V → Fin q) (onto : Function.Surjective c) (conn : G.Connected)
    (trans : ∀ i, IsVertexTransitive (G.induce {x | c x=i}))
    (paths : ∀ i, HasHamiltonianPath (G.induce {x | c x=i}))
    (absent : ¬HasHamiltonianPath G) : 3≤ q := by
  classical
  obtain ⟨v⟩ := conn.nonempty
  have pos := (c v).isLt
  by_contra! short
  obtain rfl|rfl : q=1 ∨ q=2 := by omega
  · let r : Fin 1 := 0
    let e : G ≃g G.induce {x|c x=r} :=
      { toFun := fun w => ⟨w,Subsingleton.elim _ _⟩
        invFun := Subtype.val
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_rel_iff' := Iff.rfl }
    obtain ⟨x,y,p,hp⟩ := paths r
    exact absent ⟨e.symm x,e.symm y,p.map e.symm.toHom,hp.map e.symm.toHom e.symm.toEquiv.bijective⟩
  · let side := fun x => finTwoEquiv (c x)
    have classes (b : Bool) : {x | side x=b} = {x | c x=finTwoEquiv.symm b} := by
      ext x
      exact finTwoEquiv.eq_symm_apply.symm
    apply absent (join_two G side (finTwoEquiv.surjective.comp onto) conn ?_ ?_)
    · intro b
      rw [classes]
      exact trans _
    · intro b
      rw [classes]
      exact paths _

end LovaszBlocks

namespace LovaszDense
open Finset SimpleGraph LovaszConjecture

/-- An asymptotic path theorem at every reciprocal integer density covers every
positive real density in the original conjecture. -/
theorem from_integer_densities
    (integer : ∀ k : ℕ, 0 < k → ∃ b : ℕ,
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        b ≤ Fintype.card V → G.Connected → IsVertexTransitive G →
        Fintype.card V ≤ k * G.minDegree → HasHamiltonianPath G) :
    type_of% @LovaszConjecture.lovasz_conjecture.variants.dense := by
  intro ε positive
  obtain ⟨j,inv⟩ := exists_nat_one_div_lt positive
  obtain ⟨b,atK⟩ := integer (j+1) (by omega)
  refine ⟨b,?_⟩
  intro V _ _ G _ size conn vt dense
  apply atK G size conn vt
  have kpos : 0 < (j:ℝ)+1 := by positivity
  have one : 1 ≤ ε*((j:ℝ)+1) := ((div_lt_iff₀ kpos).mp inv).le
  have mult := mul_le_mul_of_nonneg_right one (show 0 ≤ (Fintype.card V : ℝ) by positivity)
  have deg := mul_le_mul_of_nonneg_right dense kpos.le
  have bound : (Fintype.card V:ℝ) ≤ ((j:ℝ)+1)*G.minDegree := by nlinarith only [mult,deg]
  exact_mod_cast bound

/-- A counterexample simultaneously fails the half/quarter path criteria and admits
a minimum vertex cut between the Watkins lower bound and the traceability upper bound. -/
theorem counterexample_profile {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : 3 ≤ Fintype.card V)
    (conn : G.Connected) (vt : IsVertexTransitive G) (noPath : ¬HasHamiltonianPath G) :
    ((G.IsBipartite ∧ 4*G.minDegree < Fintype.card V) ∨
     (¬G.IsBipartite ∧ 2*G.minDegree+1 < Fintype.card V ∧
       4*G.indepNum + G.minDegree ≤ 2*Fintype.card V)) ∧
    (∃ S : Finset V, 2*(G.minDegree+1) ≤ 3*S.card ∧ S.card+2 ≤ G.indepNum ∧
      ¬(G.induce ((S : Set V)ᶜ)).Preconnected ∧
      ∀ T : Finset V, T.card < S.card → (G.induce ((T : Set V)ᶜ)).Preconnected) := by
  constructor
  · by_cases bip : G.IsBipartite
    · refine Or.inl ⟨bip,?_⟩
      by_contra! high
      exact noPath (bipartite_le_quarter G conn (regular_minDegree G vt) bip order high)
    · refine Or.inr ⟨bip,?_,nonbip_sharp_gap G conn vt bip⟩
      by_contra! high
      exact noPath (LovaszDegree.hamilton_path conn high)
  · obtain ⟨S,size,disc,least⟩ := Trace.cut_of_no_path G conn noPath
    refine ⟨S,?_,size,disc,least⟩
    by_contra! small
    exact disc (Watkins.robust_two_thirds G conn vt G.minDegree G.minDegree_le_degree S small)

end LovaszDense

namespace OMA.R_LovaszConjecture_lovasz_conjecture_variants_dense_R2
open Finset SimpleGraph LovaszConjecture

/-- The iron-connected case at reciprocal density 1/k. Simultaneous removal
of up to n/(8k²) vertices and a graph with that maximum degree preserves connectivity. -/
def H1 : Prop :=
  ∀ k : ℕ, 0 < k → ∃ b : ℕ,
    ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      let n := Fintype.card V
      let d := G.minDegree
      b ≤ n → G.Connected → IsVertexTransitive G → n ≤ k*d →
      ((G.IsBipartite ∧ 4*d < n) ∨
        (¬G.IsBipartite ∧ 2*d+1 < n ∧ 4*G.indepNum+d ≤ 2*n)) →
      (∃ S : Finset V, 2*(d+1) ≤ 3*S.card ∧ S.card+2 ≤ G.indepNum ∧
        ¬(G.induce ((S : Set V)ᶜ)).Preconnected ∧
        ∀ T : Finset V, T.card < S.card → (G.induce ((T : Set V)ᶜ)).Preconnected) →
      (∀ (S : Finset V) (F : SimpleGraph V) [DecidableRel F.Adj],
        S.card ≤ n/(8*k^2) → (∀ x, F.degree x ≤ n/(8*k^2)) →
        ((G \ F).induce (Sᶜ : Finset V)).Connected) →
      (∀ c : V → Bool, let M := ∑ x, ((G.neighborFinset x).filter fun y => c y=c x).card
        let t := (n/(8*k^2))/8
        (t+1)^2 ≤ M ∨ 4*n*d < n^2+4*M) → HasHamiltonianPath G

/-- The block assembly case. Three or more isomorphic vertex-transitive
blocks are individually traceable and iron-connected on the ambient scale.
In one block, at most q−1 prescribed disjoint terminal pairs have no spanning
linkage. The eventual path is free to choose different crossing edges. -/
def H2 : Prop :=
  ∀ k : ℕ, 0 < k → ∃ b : ℕ,
    ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      let n := Fintype.card V
      let d := G.minDegree
      b ≤ n → G.Connected → IsVertexTransitive G → n ≤ k*d →
      ((G.IsBipartite ∧ 4*d < n) ∨
        (¬G.IsBipartite ∧ 2*d+1 < n ∧ 4*G.indepNum+d ≤ 2*n)) →
      (∃ S : Finset V, 2*(d+1) ≤ 3*S.card ∧ S.card+2 ≤ G.indepNum ∧
        ¬(G.induce ((S : Set V)ᶜ)).Preconnected ∧
        ∀ T : Finset V, T.card < S.card → (G.induce ((T : Set V)ᶜ)).Preconnected) →
      (∃ S A B : Finset V, S.card ≤ n/(8*k^2) ∧ Disjoint A B ∧ A ∪ B=Sᶜ ∧
        A.Nonempty ∧ B.Nonempty ∧ A.card ≤ B.card ∧
        (∀ a∈A, (G.neighborFinset a ∩ B).card ≤ n/(8*k^2)) ∧
        (∀ b∈B, (G.neighborFinset b ∩ A).card ≤ n/(8*k^2))) →
      ∀ (q : ℕ) (c : V → Fin q), 3 ≤ q → q ≤ 2*k → Function.Surjective c →
        (∀ (f : G ≃g G) (x y : V), c (f x)=c (f y) ↔ c x=c y) →
        (G.map c).Connected → IsVertexTransitive (G.map c) →
        (∀ i j, Nonempty (G.induce {v | c v=i} ≃g G.induce {v | c v=j})) →
        (∀ i, let X : Set V := {v | c v=i}
          let K := G.induce X
          n = q*Fintype.card X ∧ Fintype.card X ≤ k*K.minDegree ∧
          IsVertexTransitive K ∧ HasHamiltonianPath K ∧
          ∀ (F : SimpleGraph X) [DecidableRel F.Adj] (S : Finset X),
            S.card ≤ n/(8*k^2) → (∀ x, F.degree x ≤ n/(8*k^2)) →
            ((K \ F).induce (Sᶜ : Finset X)).Connected) →
        (∃ (a : Fin q) (r : ℕ) (T : (Fin r × Bool) ↪ V), 1 ≤ r ∧ r ≤ q-1 ∧
          (∀ h, c (T h)=a) ∧ ¬ ∃ paths : Fin r → List V,
            (∀ i, (paths i).head?=some (T (i,false)) ∧ (paths i).getLast?=some (T (i,true)) ∧
              (paths i).Nodup ∧ (paths i).IsChain G.Adj ∧ ∀ z∈paths i, c z=a) ∧
            (∀ i j, i≠j → (paths i).Disjoint (paths j)) ∧
            (∀ z, c z=a → ∃ i, z∈paths i)) → HasHamiltonianPath G

theorem main : H1 → H2 → type_of% @LovaszConjecture.lovasz_conjecture.variants.dense := by
  classical
  intro iron blocks
  apply LovaszDense.from_integer_densities
  intro k₀ kpos
  obtain ⟨N,R,npos,rpos,split⟩ := LovaszIron.bounded_iron_decomposition (2*k₀)
  let k := max k₀ (max N R)+1
  have hk : 0< k := by dsimp [k]; omega
  have dom : k₀≤ k ∧ N≤ k ∧ R≤ k := by dsimp [k]; omega
  obtain ⟨b₁,h₁⟩ := iron k hk
  obtain ⟨b₂,h₂⟩ := blocks k hk
  refine ⟨max (max (64*k^3+1) (2*N)) (max (R*(b₁+3)) (max b₂ (8*k^2+1))),?_⟩
  intro V _ _ G _ large conn vt dense
  let n := Fintype.card V
  have largeTour : 64*k^3+1 ≤ n := by dsimp [n]; omega
  have largeN : 2*N ≤ n := by dsimp [n]; omega
  have largeBlocks : R*(b₁+3) ≤ n := by dsimp [n]; omega
  have b2 : b₂≤ n := by dsimp [n]; omega
  have big : 8*k^2+1≤ n := by dsimp [n]; omega
  have n3 : 3 ≤ Fintype.card V := by dsimp [n] at largeBlocks; nlinarith only [largeBlocks, rpos, Nat.zero_le b₁]
  let b := n/(2*N)
  let l := n/(8*k^2)
  have budget : N*(b+1) ≤ n := by
    have h := Nat.div_mul_le_self n (2*N)
    change b*(2*N) ≤ n at h
    rw [Nat.mul_comm b, Nat.mul_assoc] at h
    rw [Nat.mul_add_one]
    omega
  have denom : 2*N ≤ 8*k^2 := by nlinarith only [dom.2.1, Nat.one_le_pow 2 k hk, Nat.le_mul_self k]
  have lcap : l ≤ b := Nat.div_le_div_left denom (by omega)
  have den : 2*Fintype.card V ≤ (2*k₀)*G.minDegree := by
    rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ dense
  obtain ⟨q,c,cap,onto,invariant,properties⟩ := split G b vt den budget
  obtain ⟨qconn,qvt,fvt,_,cards⟩ := LovaszBlocks.labeled_blocks G c onto conn vt invariant
  obtain ⟨isos,_⟩ := LovaszIron.block_isomorphisms G c onto vt invariant
  have qpos : 0< q := by obtain ⟨v⟩ := conn.nonempty; have := (c v).isLt; omega
  have limit : q ≤ 2*k := by omega
  have fibers (i : Fin q) :
      let X : Set V := {v | c v=i}
      let K := G.induce X
      n = q*Fintype.card X ∧ Fintype.card X ≤ k*K.minDegree ∧
      IsVertexTransitive K ∧ HasHamiltonianPath K ∧
      ∀ (F : SimpleGraph X) [DecidableRel F.Adj] (S : Finset X),
        S.card ≤ l → (∀ x, F.degree x ≤ l) → ((K \ F).induce (Sᶜ : Finset X)).Connected := by
    intro X K
    have order : n=q*Fintype.card X := by
      calc n = q*Nat.card X := cards i
           _ = q*Fintype.card X := by rw [Nat.card_eq_fintype_card]
    obtain ⟨density,robust⟩ := properties i
    change 2*Fintype.card X ≤ (2*k₀)*K.minDegree at density
    rw [Nat.mul_assoc] at density
    have denX := Nat.le_of_mul_le_mul_left density (by decide : 0<2)
    have dX : Fintype.card X ≤ k*K.minDegree := denX.trans (Nat.mul_le_mul_right _ dom.1)
    have mpos : b₁+3 ≤ Fintype.card X := Nat.le_of_mul_le_mul_left
      (largeBlocks.trans (order.symm ▸ Nat.mul_le_mul_right (Fintype.card X) cap)) rpos
    have vtX : IsVertexTransitive K := fvt i
    have : Nonempty X := Fintype.card_pos_iff.mp (by omega)
    have conX : K.Connected := LovaszBlocks.connected_of_iron K robust
    have qm : n ≤ R*Fintype.card X := order ▸ Nat.mul_le_mul_right _ cap
    have mm : Fintype.card X ≤ n := order ▸ (by simpa only [Nat.one_mul] using Nat.mul_le_mul_right (Fintype.card X) qpos)
    have count : l < Fintype.card X := by
      have denGreat : R < 8*k^2 := by nlinarith only [dom.2.2,hk,Nat.le_mul_self k]
      apply (Nat.div_lt_iff_lt_mul (by positivity : 0<8*k^2)).2
      rw [Nat.mul_comm]
      exact qm.trans_lt (Nat.mul_lt_mul_of_pos_right denGreat (by omega))
    have keep := LovaszBlocks.connected_iron_of_preconnected K l count
      (fun F _ S hS hF => robust F S (hS.trans lcap) (fun x => (hF x).trans lcap))
    refine ⟨order,dX,vtX,?_,fun F _ S hS hF => keep S F hS hF⟩
    by_contra absent
    obtain ⟨degree,cut⟩ := LovaszDense.counterexample_profile K (by omega) conX vtX absent
    have loc : Fintype.card X/(8*k^2) ≤ l := Nat.div_le_div_right mm
    have innerIron (S : Finset X) (F : SimpleGraph X) [DecidableRel F.Adj]
        (hS : S.card ≤ Fintype.card X/(8*k^2)) (hF : ∀ x, F.degree x ≤ Fintype.card X/(8*k^2)) :=
      keep S F (hS.trans loc) (fun x => (hF x).trans loc)
    have near := LovaszIron.near_quarter_obstruction K vtX k hk (by omega) innerIron absent
    exact absent (h₁ K (by omega) conX vtX dX degree cut innerIron near)
  by_contra absent
  have three := LovaszBlocks.three_traceable_blocks G c onto conn fvt (fun i => (fibers i).2.2.2.1) absent
  obtain ⟨degree,cut⟩ := LovaszDense.counterexample_profile G n3 conn vt absent
  have obstruction := LovaszQuotient.local_obstruction G c vt invariant qconn (by omega) limit largeTour absent
  have fullDense := dense.trans (Nat.mul_le_mul_right _ dom.1)
  have b1 : b₁ ≤ n := by
    have z := Nat.mul_le_mul_right (b₁+3) rpos
    simp only [Nat.one_mul] at z
    omega
  have low : l< n := Nat.div_lt_self (by omega) (by nlinarith only [Nat.one_le_pow 2 k hk])
  have failure : ¬∀ (F : SimpleGraph V) [DecidableRel F.Adj] (S : Finset V), S.card ≤ l →
      (∀ x, F.degree x≤ l) → ((G \ F).induce (Sᶜ : Finset V)).Preconnected := by
    intro pre
    have globalIron := LovaszBlocks.connected_iron_of_preconnected G l low pre
    have near := LovaszIron.near_quarter_obstruction G vt k hk n3 globalIron absent
    exact absent (h₁ G b1 conn vt fullDense degree cut globalIron near)
  have sparse := (LovaszIron.iron_cut_iff G l l).mp failure
  exact absent (h₂ G b2 conn vt fullDense degree cut sparse q c
    three limit onto invariant qconn qvt isos fibers obstruction)

end OMA.R_LovaszConjecture_lovasz_conjecture_variants_dense_R2

