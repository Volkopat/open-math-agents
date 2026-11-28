import OMAReductions.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R2
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import Mathlib.Combinatorics.SimpleGraph.Diam
import Mathlib.Algebra.Order.BigOperators.Group.Finset

-- Reduction WrittenOnTheWallII.GraphConjecture189.conjecture189.R2.H2.R1 of step WrittenOnTheWallII.GraphConjecture189.conjecture189.R2.H2
-- Credit: @ali-hamdan-007

namespace OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R2_H2_R1

open SimpleGraph Finset
open scoped BigOperators

section PathProof

variable {V : Type*} {G : SimpleGraph V} {z u : V}

private theorem bound_list {v : V} (P : G.Walk z v)
    (longest : ∀ {b} (Q : G.Walk z b), Q.IsPath → Q.length ≤ P.length)
    (L : List V) (h : L.head? = some z) (hc : L.IsChain G.Adj) (hn : L.Nodup) :
    L.length ≤ P.support.length := by
  have ne : L ≠ [] := by rintro rfl; simp at h
  have he : L.head ne = z := by simpa [List.head?_eq_some_head ne] using h
  subst z
  let Q := Walk.ofSupport L ne hc
  have qs : Q.support = L := Walk.support_ofSupport _ _
  have qp : Q.IsPath := Walk.IsPath.mk' (qs.symm ▸ hn)
  have le := longest Q qp
  have ql := Q.length_support
  rw [qs] at ql
  have pl := P.length_support
  omega

private theorem pos_eq (L : List V) (i : ℕ) (hi : i < L.length) (d : V) : L.getD i d = L[i] := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]

private theorem take_last (L : List V) (i : ℕ) (hi : i < L.length) (d : V) :
    (L.take (i+1)).getLast? = some (L.getD i d) := by
  rw [List.getLast?_take, pos_eq _ _ hi _]
  simp [List.getElem?_eq_getElem hi]

private theorem drop_head (L : List V) (i : ℕ) (hi : i < L.length) (d : V) :
    (L.drop i).head? = some (L.getD i d) := by
  rw [List.head?_drop, pos_eq _ _ hi _, List.getElem?_eq_getElem hi]

private theorem bridge {A B : List V} {a b : V} (ca : A.IsChain G.Adj) (cb : B.IsChain G.Adj)
    (ha : A.getLast? = some a) (hb : B.head? = some b) (e : G.Adj a b) :
    (A ++ B).IsChain G.Adj := by
  apply ca.append cb
  simpa [ha,hb] using e

private theorem insert_chain {L : List V} (hL : L.IsChain G.Adj) (i : ℕ) (hi : i < L.length)
    (X : List V) (x y : V) (hX : X.IsChain G.Adj) (hx : X.head? = some x)
    (hy : X.getLast? = some y) (d : V) (left : G.Adj (L.getD i d) x)
    (right : i+1 < L.length → G.Adj y (L.getD (i+1) d)) :
    ((L.take (i+1) ++ X) ++ L.drop (i+1)).IsChain G.Adj := by
  have pre := bridge (hL.take _) hX (take_last L i hi d) hx left
  apply pre.append (hL.drop _)
  intro a ha b hb
  have last : (L.take (i+1) ++ X).getLast? = some y := by simp [List.getLast?_append,hy]
  rw [last] at ha
  have eq : a = y := by simpa using ha.symm
  subst a
  by_cases hs : i+1 < L.length
  · rw [drop_head L _ hs d] at hb
    have eq : b = L.getD (i+1) d := by simpa using hb.symm
    exact eq ▸ right hs
  · have emp : L.drop (i+1) = [] := by simp [List.drop_eq_nil_iff.mpr (by omega : L.length ≤ i+1)]
    simp [emp] at hb

private theorem forbid_insert {L : List V} (head : L.head? = some z) (chain : L.IsChain G.Adj)
    (nodup : L.Nodup) (maximal : ∀ K : List V, K.head? = some z → K.IsChain G.Adj → K.Nodup → K.length ≤ L.length)
    (i : ℕ) (hi : i < L.length) (X : List V) (x y : V) (hX : X.IsChain G.Adj)
    (hx : X.head? = some x) (hy : X.getLast? = some y) (hn : X.Nodup) (dis : X.Disjoint L)
    (left : G.Adj (L.getD i z) x) (right : i+1 < L.length → G.Adj y (L.getD (i+1) z)) : False := by
  let A := L.take (i+1)
  let B := L.drop (i+1)
  have split : A ++ B = L := List.take_append_drop _ _
  have perm : ((A ++ X) ++ B).Perm (X ++ L) := by
    rw [← split, ← List.append_assoc]
    exact List.perm_append_comm.append_right _
  have n := perm.nodup_iff.mpr (List.nodup_append'.mpr ⟨hn,nodup,dis⟩)
  have hd : ((A ++ X) ++ B).head? = some z := by simp [A,List.head?_append,List.head?_take,head]
  have le := maximal _ hd (insert_chain chain i hi X x y hX hx hy z left right) n
  have equal := perm.length_eq
  have nx : 0 < X.length := by cases X <;> simp_all
  rw [equal] at le
  simp only [List.length_append] at le
  omega

private theorem forbid_cross {L : List V} (head : L.head? = some z) (chain : L.IsChain G.Adj)
    (nodup : L.Nodup) (maximal : ∀ K : List V, K.head? = some z → K.IsChain G.Adj → K.Nodup → K.length ≤ L.length)
    (outside : u ∉ L) (i j : ℕ) (hij : i < j) (hj : j+1 < L.length)
    (left : G.Adj (L.getD i z) u) (mid : G.Adj u (L.getD j z))
    (chord : G.Adj (L.getD (i+1) z) (L.getD (j+1) z)) : False := by
  let A := L.take (i+1)
  let B := (L.take (j+1)).drop (i+1)
  let C := L.drop (j+1)
  have ab : A ++ B = L.take (j+1) := by
    have h := List.take_append_drop (i+1) (L.take (j+1))
    simpa [A,B,List.take_take,Nat.min_eq_left (by omega : i+1 ≤ j+1)] using h
  have split : (A ++ B) ++ C = L := by rw [ab]; exact List.take_append_drop _ _
  have blen : (L.take (j+1)).length = j+1 := by simp [Nat.min_eq_left (by omega : j+1 ≤ L.length)]
  have bst : B.head? = some (L.getD (i+1) z) := by
    simp [B,List.head?_drop,show i+1 < j+1 by omega,
      List.getElem?_eq_getElem (by omega : i+1 < L.length)]
  have ben : B.getLast? = some (L.getD j z) := by
    dsimp only [B]
    rw [List.getLast?_drop,if_neg (by rw [blen]; omega)]
    exact take_last L _ (by omega) _
  have br := List.isChain_reverse.mpr (((chain.take (j+1)).drop (i+1)).imp fun _ _ h => h.symm)
  have c1 := bridge (chain.take (i+1)) (List.isChain_singleton u) (take_last L i (by omega) z) (by simp) left
  have c2 : ((A ++ [u]) ++ B.reverse).IsChain G.Adj := by
    apply bridge c1 br (a := u) (b := L.getD j z) (by simp) (by simpa using ben) mid
  have c3 : (((A ++ [u]) ++ B.reverse) ++ C).IsChain G.Adj := by
    apply bridge c2 (chain.drop _) (a := L.getD (i+1) z) (b := L.getD (j+1) z) _ (drop_head L _ hj z) chord
    rw [List.getLast?_append,List.getLast?_reverse,bst]
    rfl
  have p1 : ((A ++ [u]) ++ B.reverse).Perm ([u] ++ (A ++ B)) := by
    exact (List.perm_append_comm.append_right B.reverse).trans
      ((B.reverse_perm.append_left ([u] ++ A)).trans (by simp))
  have perm : (((A ++ [u]) ++ B.reverse) ++ C).Perm (u :: L) := by
    rw [← split]; simpa [List.append_assoc] using p1.append_right C
  have n := perm.nodup_iff.mpr (List.nodup_cons.mpr ⟨outside,nodup⟩)
  have hd : (((A ++ [u]) ++ B.reverse) ++ C).head? = some z := by simp [A,List.head?_append,List.head?_take,head]
  have le := maximal _ hd c3 n
  have equal := perm.length_eq
  rw [equal] at le
  simp only [List.length_cons] at le
  omega

/-- Contacts and their oriented successors along a longest path with prescribed start. -/
private theorem successors_of_rooted_longest {v : V} (P : G.Walk z v) (hp : P.IsPath)
    (longest : ∀ {b} (Q : G.Walk z b), Q.IsPath → Q.length ≤ P.length)
    (outside : u ∉ P.support) (touches : ∃ w ∈ P.support, G.Adj u w) :
    ∃ (W : Finset V) (succ : V → V), W.Nonempty ∧ Set.InjOn succ (↑W : Set V) ∧
      (∀ w ∈ W, G.Adj u w) ∧ (∀ w ∈ W, succ w ≠ u ∧ ¬G.Adj u (succ w)) ∧
      (∀ a ∈ W, ∀ b ∈ W, ¬G.Adj (succ a) (succ b)) ∧
      (∀ w ∈ W, ∀ y, G.Adj u y → G.Adj (succ w) y → y ∈ W) ∧
      (∀ w ∈ W, G.Adj w (succ w) ∧ succ w ≠ z) ∧ u ≠ z := by
  classical
  let L := P.support
  have head : L.head? = some z := by cases P <;> rfl
  have chain : L.IsChain G.Adj := P.isChain_adj_support
  have nodup : L.Nodup := hp.support_nodup
  have maximal := bound_list P longest
  let W := L.toFinset.filter (G.Adj u)
  have memW (w : V) : w ∈ W ↔ w ∈ L ∧ G.Adj u w := by simp [W]
  let idx (w : V) := L.idxOf w
  have at_idx (w : V) (hw : w ∈ L) : ∃ h : idx w < L.length, L[idx w] = w := by
    have hi := List.idxOf_lt_length_iff.mpr hw
    exact ⟨hi,List.getElem_idxOf hi⟩
  have at_w (w : V) (hw : w ∈ W) : L.getD (idx w) z = w := by
    obtain ⟨hi,eq⟩ := at_idx w ((memW w).mp hw).1
    exact (pos_eq _ _ hi _).trans eq
  have next_lt (w : V) (hw : w ∈ W) : idx w + 1 < L.length := by
    by_contra hn
    obtain ⟨hi,_⟩ := at_idx w ((memW w).mp hw).1
    exact forbid_insert head chain nodup maximal (idx w) hi [u] u u (by simp) (by simp) (by simp)
      (by simp) (by simpa using outside) (by rw [at_w w hw]; exact ((memW w).mp hw).2.symm) (fun h => (hn h).elim)
  let succ (w : V) := L.getD (idx w+1) z
  have succmem (w : V) (hw : w ∈ W) : succ w ∈ L := by
    change L.getD (idx w+1) z ∈ L
    rw [pos_eq _ _ (next_lt w hw) _]; exact List.getElem_mem _
  have noedge (w : V) (hw : w ∈ W) : ¬G.Adj u (succ w) := by
    intro e
    have hi := next_lt w hw
    exact forbid_insert head chain nodup maximal (idx w) (by omega) [u] u u (by simp) (by simp)
      (by simp) (by simp) (by simpa using outside)
      (by rw [at_w w hw]; exact ((memW w).mp hw).2.symm) (fun _ => e)
  have same (a b : V) (ha : a ∈ W) (hb : b ∈ W) (h : idx a = idx b) : a = b :=
    (at_w a ha).symm.trans ((congrArg (fun i => L.getD i z) h).trans (at_w b hb))
  have no_cross (a b : V) (ha : a ∈ W) (hb : b ∈ W) (h : idx a < idx b) : ¬G.Adj (succ a) (succ b) := by
    intro e
    apply forbid_cross head chain nodup maximal outside (idx a) (idx b) h (next_lt b hb) _ _ e
    · rw [at_w a ha]; exact ((memW a).mp ha).2.symm
    · rw [at_w b hb]; exact ((memW b).mp hb).2
  obtain ⟨w₀,hw₀,e₀⟩ := touches
  refine ⟨W,succ,⟨w₀,(memW _).mpr ⟨hw₀,e₀⟩⟩,?_,fun w hw => ((memW w).mp hw).2,
    fun w hw => ⟨fun he => outside (he ▸ succmem w hw),noedge w hw⟩,?_,?_,?_,?_⟩
  · intro a ha b hb he
    change L.getD (idx a+1) z = L.getD (idx b+1) z at he
    rw [pos_eq _ _ (next_lt a ha) _,pos_eq _ _ (next_lt b hb) _] at he
    have h := nodup.getElem_inj_iff.mp he
    exact same a b ha hb (by omega)
  · intro a ha b hb e
    rcases lt_trichotomy (idx a) (idx b) with h | h | h
    · exact no_cross a b ha hb h e
    · have eq := same a b ha hb h
      subst b
      exact e.ne rfl
    · exact no_cross b a hb ha h e.symm
  · intro w hw y uy sy
    apply (memW _).mpr
    refine ⟨?_,uy⟩
    by_contra hy
    have hi := next_lt w hw
    apply forbid_insert head chain nodup maximal (idx w) (by omega) [u,y] u y
      (by simpa using uy) (by simp) (by simp) (by simp [uy.ne]) _ _ (fun _ => sy.symm)
    · simpa [List.disjoint_cons_left,hy] using (show u ∉ L from outside)
    · rw [at_w w hw]; exact ((memW w).mp hw).2.symm
  · intro w hw
    have hn := next_lt w hw
    have hi : idx w < L.length := by omega
    have gadj : G.Adj (L.getD (idx w) z) (L.getD (idx w+1) z) := by
      rw [pos_eq _ _ hi _,pos_eq _ _ hn _]
      exact chain.getElem _ hn
    refine ⟨?_,?_⟩
    · rw [at_w w hw] at gadj
      exact gadj
    · intro he
      have h0 : 0 < L.length := by omega
      have hz : L.getD 0 z = z := by
        have eq := drop_head L 0 h0 z
        simpa [head] using eq.symm
      change L.getD (idx w+1) z = z at he
      rw [← hz,pos_eq _ _ hn _,pos_eq _ _ h0 _] at he
      have eq := nodup.getElem_inj_iff.mp he
      omega
  · intro h
    apply outside
    rw [h]
    exact P.start_mem_support

/-- A longest path starting at the prescribed vertex exists in every finite graph. -/
private theorem exists_rooted_longest [Fintype V] (G : SimpleGraph V) (z : V) :
    ∃ (v : V) (P : G.Walk z v), P.IsPath ∧
      ∀ {b} (Q : G.Walk z b), Q.IsPath → Q.length ≤ P.length := by
  classical
  let Good (m : ℕ) := ∃ (v : V) (P : G.Walk z v), P.IsPath ∧ P.length = m
  have base : Good 0 := ⟨z,.nil,by simp,rfl⟩
  obtain ⟨v,P,hp,hlen⟩ := Nat.findGreatest_spec (Nat.zero_le (Fintype.card V)) base
  refine ⟨v,P,hp,?_⟩
  intro b Q hQ
  rw [hlen]
  have card := hQ.support_nodup.length_le_card
  have size := Q.length_support
  exact Nat.le_findGreatest (by omega) (show Good Q.length from ⟨b,Q,hQ,rfl⟩)

/-- Connectivity supplies an omitted vertex that touches any nonspanning rooted path. -/
private theorem exists_exterior_contact {v : V} (P : G.Walk z v) (connected : G.Connected)
    (missing : ∃ x, x ∉ P.support) : ∃ u ∉ P.support, ∃ w ∈ P.support, G.Adj u w := by
  obtain ⟨x,hx⟩ := missing
  obtain ⟨R⟩ := connected z x
  obtain ⟨d,_,hin,hout⟩ := R.exists_boundary_dart {y | y ∈ P.support} P.start_mem_support hx
  exact ⟨d.snd,hout,d.fst,hin,d.adj.symm⟩

end PathProof

section ContactCount

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A path contact and its successor violate local Ore for at least one
contact. The other hypotheses isolate the path-splicing part of the proof. -/
private theorem bad_wedge_of_successors (u : V) (W : Finset V) (succ : V → V)
    (hn : W.Nonempty) (inj : Set.InjOn succ (↑W : Set V))
    (touch : ∀ w ∈ W, G.Adj u w)
    (miss : ∀ w ∈ W, succ w ≠ u ∧ ¬G.Adj u (succ w))
    (indep : ∀ a ∈ W, ∀ b ∈ W, ¬G.Adj (succ a) (succ b))
    (common : ∀ w ∈ W, ∀ v, G.Adj u v → G.Adj (succ w) v → v ∈ W) :
    ∃ w ∈ W, G.degree u + G.degree (succ w) <
      (G.neighborFinset u ∪ G.neighborFinset w ∪ G.neighborFinset (succ w)).card := by
  classical
  let U := W.image succ
  by_contra! hall
  have row (w : V) (hw : w ∈ W) :
      ((U.filter fun v => G.Adj w v)).card + 1 ≤ ((W.filter fun v => G.Adj v (succ w))).card := by
    let A := G.neighborFinset u
    let B := G.neighborFinset (succ w)
    let C := G.neighborFinset w
    let D := C \ (A ∪ B)
    have hu : D ∪ (A ∪ B) = (A ∪ C) ∪ B := by ext a; simp [D]; tauto
    have dis : Disjoint D (A ∪ B) := by
      rw [Finset.disjoint_left]
      exact fun _ h => (Finset.mem_sdiff.mp h).2
    have join := Finset.card_union_of_disjoint dis
    rw [hu] at join
    have oi := Finset.card_union_add_card_inter A B
    have ah : A.card = G.degree u := G.card_neighborFinset_eq_degree u
    have bh : B.card = G.degree (succ w) := G.card_neighborFinset_eq_degree _
    have localbound := hall w hw
    change ((A ∪ C) ∪ B).card ≤ G.degree u + G.degree (succ w) at localbound
    have bound : D.card ≤ (A ∩ B).card := by omega
    have hsub : insert u ((U.filter fun v => G.Adj w v)) ⊆ D := by
      intro v hv
      rcases Finset.mem_insert.mp hv with rfl | hv
      · apply Finset.mem_sdiff.mpr
        refine ⟨(G.mem_neighborFinset _ _).mpr (touch w hw).symm,?_⟩
        intro hum
        rcases Finset.mem_union.mp hum with ha | hb
        · exact ((G.mem_neighborFinset _ _).mp ha).ne rfl
        · exact (miss _ hw).2 ((G.mem_neighborFinset _ _).mp hb).symm
      · obtain ⟨hvU,hvA⟩ := Finset.mem_filter.mp hv
        obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hvU
        apply Finset.mem_sdiff.mpr
        refine ⟨(G.mem_neighborFinset _ _).mpr hvA,?_⟩
        intro h
        rcases Finset.mem_union.mp h with ha | hB
        · exact (miss _ hb).2 ((G.mem_neighborFinset _ _).mp ha)
        · exact (indep _ hw _ hb) ((G.mem_neighborFinset _ _).mp hB)
    have hout : u ∉ (U.filter fun v => G.Adj w v) := by
      intro hu
      obtain ⟨b,hb,he⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hu).1
      exact (miss _ hb).1 he
    have small := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem hout] at small
    have other : A ∩ B ⊆ (W.filter fun v => G.Adj v (succ w)) := by
      intro v hv
      obtain ⟨h₁,h₂⟩ := Finset.mem_inter.mp hv
      have e₁ := (G.mem_neighborFinset _ _).mp h₁
      have e₂ := (G.mem_neighborFinset _ _).mp h₂
      exact Finset.mem_filter.mpr ⟨common _ hw v e₁ e₂,e₂.symm⟩
    exact small.trans (bound.trans (Finset.card_le_card other))
  have rows := Finset.sum_le_sum row
  have dbl : (∑ w ∈ W, (U.filter fun v => G.Adj w v).card) =
      ∑ v ∈ U, (W.filter fun w => G.Adj w v).card := by
    classical
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    exact Finset.sum_comm
  have im : (∑ v ∈ U, ((W.filter fun w => G.Adj w v)).card) =
      ∑ w ∈ W, ((W.filter fun v => G.Adj v (succ w))).card := Finset.sum_image inj
  rw [im] at dbl
  rw [Finset.sum_add_distrib] at rows
  simp only [Finset.sum_const, smul_eq_mul, mul_one] at rows
  have pos := hn.card_pos
  omega

end ContactCount

section WedgeCount

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem predecessor {x z : V} {j : ℕ} (hz : G.dist x z = j+1) :
    ∃ a, G.dist x a = j ∧ G.Adj a z := by
  have hr : G.dist z x = j+1 := by rwa [dist_comm]
  have hp : G.Reachable z x := Reachable.of_dist_ne_zero (by omega)
  obtain ⟨walk,hlen⟩ := hp.exists_walk_length_eq_dist
  cases walk with
  | nil => simp at hz
  | cons he tail =>
    rename_i a
    have ht : tail.length = j := by rw [Walk.length_cons,hr] at hlen; omega
    have hh : G.dist x a ≤ j := by rw [dist_comm]; exact ht ▸ G.dist_le tail
    have := he.diff_dist_adj (u := x)
    exact ⟨a,by omega,he.symm⟩

/-- The order bound at an induced two-edge path with center x. -/
private theorem wedge_order (hc : G.Connected) {x y z : V} (hxy : G.Adj x y) (hxz : G.Adj x z)
    (_hyz : ¬G.Adj y z) {k : ℕ} (cap : ∀ v, G.distEven v ≤ k+1) :
    Fintype.card V + (k+1) * ((G.neighborFinset x ∪
        (G.neighborFinset y ∪ G.neighborFinset z)).card) ≤
        3*k+2 + k*(G.degree x + G.distEven x) + G.degree y + G.degree z := by
  classical
  let E (v : V) := Finset.univ.filter (fun w => Even (G.dist v w))
  let X := G.neighborFinset x
  let Y := G.neighborFinset y
  let Z := G.neighborFinset z
  let S := Y ∪ Z
  let U := X ∪ S
  let Q := X \ S
  let C := Y ∩ Z
  let I := C ∩ X
  let A := E x \ S
  let T := univ.filter (fun w => 3 ≤ G.dist x w ∧ 3 ≤ G.dist y w ∧ 3 ≤ G.dist z w ∧ ¬Even (G.dist x w))
  have ecap (v : V) : (E v).card ≤ k+1 := cap v
  have memN (v w : V) : w ∈ G.neighborFinset v ↔ G.Adj v w := G.mem_neighborFinset v w
  have near_even (a v w : V) (ha : G.Adj a v) (hw : G.Adj v w) (hn : ¬G.Adj a w) : w ∈ E a := by
    have h := hc.dist_triangle (u:=a) (v:=v) (w:=w)
    rw [dist_eq_one_iff_adj.mpr ha, dist_eq_one_iff_adj.mpr hw] at h
    have hne : G.dist a w ≠ 1 := fun hh => hn (dist_eq_one_iff_adj.mp hh)
    exact mem_filter.mpr ⟨mem_univ _,by rw [Nat.even_iff]; omega⟩
  have scset : S \ X ⊆ E x := by
    intro v hv
    obtain ⟨hs,hn⟩ := mem_sdiff.mp hv
    have hna : ¬G.Adj x v := fun hh => hn ((memN _ _).mpr hh)
    rcases mem_union.mp hs with hy|hz
    · exact near_even x y v hxy ((memN _ _).mp hy) hna
    · exact near_even x z v hxz ((memN _ _).mp hz) hna
  have ac : A.card + U.card ≤ G.distEven x + G.degree x := by
    have dj : Disjoint A (S \ X) := by
      rw [Finset.disjoint_left]
      exact fun _ ha hb => (mem_sdiff.mp ha).2 (mem_sdiff.mp hb).1
    have sub : A ∪ (S \ X) ⊆ E x := by
      intro v hv
      exact (mem_union.mp hv).elim (fun ha => (mem_sdiff.mp ha).1) (fun hb => scset hb)
    have h := card_le_card sub
    rw [card_union_of_disjoint dj] at h
    have hc1 := Finset.card_sdiff_add_card_inter S X
    have hc2 := Finset.card_union_add_card_inter X S
    rw [Finset.inter_comm S X] at hc1
    have hd : X.card = G.degree x := G.card_neighborFinset_eq_degree x
    change _ ≤ G.distEven x at h
    change _ + (X ∪ S).card ≤ _
    omega
  have qc : Q.card + G.degree y + G.degree z = U.card + C.card := by
    have h1 := Finset.card_sdiff_add_card_inter X S
    have h2 := Finset.card_union_add_card_inter X S
    have h3 := Finset.card_union_add_card_inter Y Z
    have hy : Y.card = G.degree y := G.card_neighborFinset_eq_degree y
    have hz : Z.card = G.degree z := G.card_neighborFinset_eq_degree z
    change S.card+C.card=Y.card+Z.card at h3
    change (X \ S).card+_+_=(X ∪ S).card+C.card
    omega
  have ics : I.card + 1 ≤ C.card := by
    have notI : x ∉ I := fun h => (G.loopless.irrefl x) ((memN _ _).mp (mem_inter.mp h).2)
    have sub : insert x I ⊆ C := by
      intro b hb
      rcases mem_insert.mp hb with rfl|hh
      · exact mem_inter.mpr ⟨(memN _ _).mpr hxy.symm,(memN _ _).mpr hxz.symm⟩
      · exact (mem_inter.mp hh).1
    have hh := card_le_card sub
    rwa [card_insert_of_notMem notI] at hh
  have qs : Q ⊆ E y ∩ E z := by
    intro w hw
    obtain ⟨hh,hn⟩ := mem_sdiff.mp hw
    exact mem_inter.mpr ⟨near_even y x w hxy.symm ((memN _ _).mp hh)
      (fun h => hn (mem_union_left _ ((memN _ _).mpr h))),
      near_even z x w hxz.symm ((memN _ _).mp hh)
      (fun h => hn (mem_union_right _ ((memN _ _).mpr h)))⟩
  let row (a : V) := T.filter (fun w => G.Adj a w ∧ G.dist x w = G.dist x a+1)
  have rcap (a : V) : (row a).card ≤ k := by
    by_cases hn : (row a).Nonempty
    · obtain ⟨w,hw⟩ := hn
      obtain ⟨ht,_,he⟩ := mem_filter.mp hw
      have hh := (mem_filter.mp ht).2.1
      obtain ⟨b,hb,hab⟩ := predecessor (G := G) (x := x) (z := a) (j := G.dist x a-1) (by omega)
      have hs : insert b (row a) ⊆ E b := by
        intro v hv
        rcases mem_insert.mp hv with rfl | hv
        · exact mem_filter.mpr ⟨mem_univ _,by simp⟩
        · obtain ⟨_,hav,hvlen⟩ := mem_filter.mp hv
          have hlu := hc.dist_triangle (u := b) (v := a) (w := v)
          rw [dist_eq_one_iff_adj.mpr hab,dist_eq_one_iff_adj.mpr hav] at hlu
          have hlo := hc.dist_triangle (u := x) (v := b) (w := v)
          exact mem_filter.mpr ⟨mem_univ _,by rw [Nat.even_iff]; omega⟩
      have hnb : b ∉ row a := by intro h; have := (mem_filter.mp h).2.2; omega
      have hsize := (card_le_card hs).trans (ecap b)
      rw [Finset.card_insert_of_notMem hnb] at hsize
      omega
    · simp [Finset.not_nonempty_iff_eq_empty.mp hn]
  have tr : T ⊆ A.biUnion row := by
    intro w hw
    obtain ⟨hx,hy,hz,ho⟩ := (mem_filter.mp hw).2
    obtain ⟨a,ha,haw⟩ := predecessor (G := G) (x := x) (z := w) (j := G.dist x w-1) (by omega)
    have he : Even (G.dist x a) := by rw [Nat.even_iff] at ho ⊢; omega
    have naux (v : V) (hf : 3 ≤ G.dist v w) (hh : G.Adj v a) : False := by
      have ht := hc.dist_triangle (u := v) (v := a) (w := w)
      rw [dist_eq_one_iff_adj.mpr hh,dist_eq_one_iff_adj.mpr haw] at ht
      omega
    have hs : a ∉ S := by
      intro h
      rcases mem_union.mp h with yy|zz
      · exact naux y hy ((memN _ _).mp yy)
      · exact naux z hz ((memN _ _).mp zz)
    exact mem_biUnion.mpr ⟨a,mem_sdiff.mpr ⟨mem_filter.mpr ⟨mem_univ _,he⟩,hs⟩,
      mem_filter.mpr ⟨hw,haw,by omega⟩⟩
  have tc : T.card ≤ k*A.card := calc
    T.card ≤ (A.biUnion row).card := card_le_card tr
    _ ≤ ∑ a ∈ A, (row a).card := Finset.card_biUnion_le
    _ ≤ ∑ _a ∈ A, k := Finset.sum_le_sum fun a _ => rcap a
    _ = _ := by simp [Nat.mul_comm]
  have all : univ ⊆ (((E y ∪ E z) ∪ E x) ∪ I) ∪ T := by
    intro v _
    by_cases ey : Even (G.dist y v)
    · exact mem_union_left _ (mem_union_left _ (mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨mem_univ _,ey⟩))))
    by_cases ez : Even (G.dist z v)
    · exact mem_union_left _ (mem_union_left _ (mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨mem_univ _,ez⟩))))
    by_cases ex : Even (G.dist x v)
    · exact mem_union_left _ (mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨mem_univ _,ex⟩)))
    have y1 := hc.dist_triangle (u:=x) (v:=y) (w:=v)
    have y2 := hc.dist_triangle (u:=y) (v:=x) (w:=v)
    have z1 := hc.dist_triangle (u:=x) (v:=z) (w:=v)
    have z2 := hc.dist_triangle (u:=z) (v:=x) (w:=v)
    rw [dist_eq_one_iff_adj.mpr hxy] at y1
    rw [dist_eq_one_iff_adj.mpr hxy.symm] at y2
    rw [dist_eq_one_iff_adj.mpr hxz] at z1
    rw [dist_eq_one_iff_adj.mpr hxz.symm] at z2
    have ox := ex
    rw [Nat.even_iff] at ox ey ez
    by_cases hl : 3 ≤ G.dist x v
    · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _,hl,by omega,by omega,ex⟩)
    · have nx (a : V) (h : G.dist a v = 1) := (memN a v).mpr (dist_eq_one_iff_adj.mp h)
      exact mem_union_left _ (mem_union_right _ (mem_inter.mpr ⟨mem_inter.mpr ⟨nx y (by omega),nx z (by omega)⟩,nx x (by omega)⟩))
  have count := card_le_card all
  rw [card_univ] at count
  have h1 := Finset.card_union_add_card_inter (E y) (E z)
  have h2 := Finset.card_union_le (E y ∪ E z) (E x)
  have h3 := Finset.card_union_le ((E y ∪ E z) ∪ E x) I
  have h4 := Finset.card_union_le (((E y ∪ E z) ∪ E x) ∪ I) T
  have h5 := card_le_card qs
  have ecx := ecap x
  have ecy := ecap y
  have ecz := ecap z
  have hh : Fintype.card V + Q.card ≤ 3*k+2+C.card + k*A.card := by omega
  have hm := Nat.mul_le_mul_left k ac
  rw [Nat.mul_add, Nat.add_comm (G.distEven x) (G.degree x)] at hm
  change Fintype.card V + (k+1)*U.card ≤ _
  rw [Nat.add_mul, Nat.one_mul]
  omega

end WedgeCount

section WedgeOrder

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Above the local degree-excess threshold, this wedge satisfies the local Ore condition. -/
private theorem local_ore_of_order (hc : G.Connected) {x y z : V}
    (hxy : G.Adj x y) (hxz : G.Adj x z) (hyz : ¬G.Adj y z)
    {k r : ℕ} (cap : ∀ v, G.distEven v ≤ k+1)
    (hdeg : G.degree x + G.distEven x ≤ G.degree y + G.degree z + r + 1)
    (hn : (3+r)*k+1 < Fintype.card V) :
    (G.neighborFinset x ∪ (G.neighborFinset y ∪ G.neighborFinset z)).card ≤ G.degree y + G.degree z := by
  have h := wedge_order hc hxy hxz hyz cap
  let U := (G.neighborFinset x ∪ (G.neighborFinset y ∪ G.neighborFinset z)).card
  change U ≤ G.degree y + G.degree z
  change Fintype.card V + (k+1)*U ≤ _ at h
  by_contra! bad
  have hm := Nat.mul_le_mul_left k (show G.degree y+G.degree z+1 ≤ U by omega)
  have hd := Nat.mul_le_mul_left k hdeg
  rw [Nat.add_mul, Nat.one_mul, Nat.mul_add k (G.degree x) (G.distEven x)] at h
  rw [Nat.add_mul, Nat.mul_comm r k] at hn
  simp only [Nat.mul_add, Nat.mul_one] at hm hd
  omega

end WedgeOrder

section RootedTrace

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A local Ore bound away from a single prescribed vertex gives a spanning
path starting at that vertex. -/
private theorem rooted_local_ore (hc : G.Connected) (z : V)
    (ore : ∀ {u w v : V}, u ≠ z → v ≠ z → G.Adj u w → G.Adj w v → ¬G.Adj u v →
      (G.neighborFinset u ∪ G.neighborFinset w ∪ G.neighborFinset v).card ≤
        G.degree u + G.degree v) :
    ∃ v, ∃ p : G.Walk z v, p.IsHamiltonian := by
  obtain ⟨v,P,hp,longest⟩ := exists_rooted_longest G z
  refine ⟨v,P,hp.isHamiltonian_iff.mpr ?_⟩
  intro x
  by_contra hx
  obtain ⟨u,hu,hcP⟩ := exists_exterior_contact P hc ⟨x,hx⟩
  obtain ⟨W,succ,hn,hi,ht,hm,ha,hc',hs,huz⟩ :=
    successors_of_rooted_longest P hp longest hu hcP
  obtain ⟨w,hw,hbad⟩ := bad_wedge_of_successors u W succ hn hi ht hm ha hc'
  exact (not_lt_of_ge (ore huz (hs _ hw).2 (ht _ hw) (hs _ hw).1 (hm _ hw).2)) hbad

end RootedTrace
/-- The range from the parent order threshold through three times the second-smallest degree plus two. -/
def H1 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] [Nontrivial V]
    (G : SimpleGraph V) [DecidableRel G.Adj], G.Connected →
    (∀ x, distEven G x ≤ 1 + secondSmallestDegree G) →
    2 * secondSmallestDegree G + 3 ≤ Fintype.card V →
    (∀ c : V, (G.induce {x | x ≠ c}).Connected) →
    Fintype.card V ≤ 3 * secondSmallestDegree G + 2 →
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian

/-- The larger-order range with a local Ore obstruction at a higher-degree center. -/
def H2 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] [Nontrivial V]
    (G : SimpleGraph V) [DecidableRel G.Adj], G.Connected →
    (∀ x, distEven G x ≤ 1 + secondSmallestDegree G) →
    2 * secondSmallestDegree G + 3 ≤ Fintype.card V →
    (∀ c : V, (G.induce {x | x ≠ c}).Connected) →
    3 * secondSmallestDegree G + 3 ≤ Fintype.card V →
    (∃ u w v : V,
      G.Adj u w ∧ G.Adj w v ∧ ¬ G.Adj u v ∧
      secondSmallestDegree G ≤ G.degree u ∧ secondSmallestDegree G ≤ G.degree v ∧
      G.degree u < G.degree w ∧ G.degree v < G.degree w ∧
      G.degree u + G.degree v <
        (G.neighborFinset u ∪ G.neighborFinset w ∪ G.neighborFinset v).card ∧
      Fintype.card V ≤ 3 * secondSmallestDegree G + 1 +
        secondSmallestDegree G * (G.degree w - max (G.degree u) (G.degree v))) →
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian

theorem main : H1 → H2 → OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R2.H2 := by
  intro smallCase obstructionCase V _ _ _ G _ hc cap parentOrder connectedDeletion
  classical
  by_cases small : Fintype.card V ≤ 3 * secondSmallestDegree G + 2
  · exact smallCase G hc cap parentOrder connectedDeletion small
  let k := secondSmallestDegree G
  have large : 3 * k + 3 ≤ Fintype.card V := by
    change ¬ Fintype.card V ≤ 3 * k + 2 at small
    omega
  have evenCap (x : V) : G.distEven x ≤ k + 1 := by
    simpa only [k, Nat.add_comm] using cap x
  obtain ⟨z, hz⟩ := G.exists_minimal_degree_vertex
  have high (x : V) (hx : x ≠ z) : k ≤ G.degree x := by
    rcases OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R2.degree_pair
        (G := G) x z hx with h | h
    · exact h
    · exact h.trans (hz ▸ G.minDegree_le_degree x)
  by_contra fail
  have ore {u w v : V} (huz : u ≠ z) (hvz : v ≠ z)
      (huw : G.Adj u w) (hwv : G.Adj w v) (huv : ¬ G.Adj u v) :
      (G.neighborFinset u ∪ G.neighborFinset w ∪ G.neighborFinset v).card ≤
        G.degree u + G.degree v := by
    by_contra! bad
    have hu := high u huz
    have hv := high v hvz
    have hd : max (G.degree u) (G.degree v) + k ≤ G.degree u + G.degree v := by
      rcases le_total (G.degree u) (G.degree v) with h | h
      · rw [max_eq_right h]
        omega
      · rw [max_eq_left h]
        omega
    have greater : max (G.degree u) (G.degree v) < G.degree w := by
      by_contra! le
      have localDeg : G.degree w + G.distEven w ≤ G.degree u + G.degree v + 0 + 1 := by
        have := evenCap w
        omega
      have highOrder : (3 + 0) * k + 1 < Fintype.card V := by
        omega
      have bound := local_ore_of_order hc huw.symm hwv huv evenCap localDeg highOrder
      have bound' :
          (G.neighborFinset u ∪ G.neighborFinset w ∪ G.neighborFinset v).card ≤
            G.degree u + G.degree v := by
        simpa only [Finset.union_assoc, Finset.union_left_comm, Finset.union_comm] using bound
      exact (not_lt_of_ge bound') bad
    have orderBound : Fintype.card V ≤ 3 * k + 1 +
        k * (G.degree w - max (G.degree u) (G.degree v)) := by
      by_contra! outside
      let r := G.degree w - max (G.degree u) (G.degree v)
      have localDeg : G.degree w + G.distEven w ≤ G.degree u + G.degree v + r + 1 := by
        have := evenCap w
        dsimp only [r]
        omega
      have highOrder : (3 + r) * k + 1 < Fintype.card V := by
        change 3 * k + 1 + k * r < Fintype.card V at outside
        rw [Nat.add_mul, Nat.mul_comm r k]
        omega
      have bound := local_ore_of_order hc huw.symm hwv huv evenCap localDeg highOrder
      have bound' :
          (G.neighborFinset u ∪ G.neighborFinset w ∪ G.neighborFinset v).card ≤
            G.degree u + G.degree v := by
        simpa only [Finset.union_assoc, Finset.union_left_comm, Finset.union_comm] using bound
      exact (not_lt_of_ge bound') bad
    exact fail (obstructionCase G hc cap parentOrder connectedDeletion large
      ⟨u, w, v, huw, hwv, huv, hu, hv, lt_of_le_of_lt (le_max_left _ _) greater,
        lt_of_le_of_lt (le_max_right _ _) greater, bad, orderBound⟩)
  obtain ⟨v, p, hp⟩ := rooted_local_ore hc z ore
  exact fail ⟨z, v, p, hp⟩

end OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R2_H2_R1
