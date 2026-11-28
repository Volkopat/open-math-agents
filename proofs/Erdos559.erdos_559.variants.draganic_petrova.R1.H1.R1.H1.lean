import OMAReductions.R_Erdos559_erdos_559_variants_draganic_petrova_R1_H1_R1

/-!
Step Erdos559.erdos_559.variants.draganic_petrova.R1.H1.R1.H1: hypothesis H1 of the reduction
Erdos559.erdos_559.variants.draganic_petrova.R1.H1.R1 (reduction by @marcusbuffett, PR 3863).

Written with Claude Code (AI-assisted).

Statement: a graph of maximum degree at most 3 whose vertex set J spans no induced cycle of
length at least l has a tree decomposition of G[J] with bags of size at most 2l+1.

The proof follows A. Kosowski, B. Li, N. Nisse and K. Suchan, k-Chordal graphs: from cops and
robber to compact routing via treewidth (ICALP 2012; Algorithmica 72 (2015)), Theorem 1, which is
the bounded-chordality treewidth bound quoted by Draganic and Petrova as Lemma 4.1. An induced
path P of at most l-2 vertices is maintained together with a set D of vertices not yet covered,
all of whose outside neighbours are neighbours of P. If no outside neighbour of D is private to
an end of P, that end is dropped. Otherwise P is extended by a private neighbour b of its last
vertex, and the new bag is N(D) together with the neighbours of b in D. When P already has l-2
vertices and both ends have private neighbours a and b whose neighbours in D are joined inside D,
closing P through D gives an induced cycle on at least l vertices; if they are not joined, D is
split. Bags are stored with parent pointers, so the tree is read off at the end.
-/

namespace OMA.KLNS

open Finset

section Paths

variable {V : Type} (H : SimpleGraph V)

/-- Induced paths, as lists: the head is adjacent to exactly the next vertex. -/
def IP : List V → Prop
  | [] => True
  | v :: l => v ∉ l ∧ (∀ u ∈ l, H.Adj v u ↔ l.head? = some u) ∧ IP l

variable {H}

lemma IP.nodup : ∀ {l : List V}, IP H l → l.Nodup
  | [], _ => List.nodup_nil
  | _ :: _, h => List.nodup_cons.mpr ⟨h.1, IP.nodup h.2.2⟩

lemma IP.single (v : V) : IP H [v] := ⟨by simp, by simp, trivial⟩

lemma IP.append : ∀ {l1 l2 : List V}, IP H l1 → IP H l2 → (∀ u ∈ l1, u ∉ l2) →
    (∀ u ∈ l1, ∀ w ∈ l2, H.Adj u w ↔ (l1.getLast? = some u ∧ l2.head? = some w)) →
    IP H (l1 ++ l2)
  | [], l2, _, h2, _, _ => by simpa using h2
  | [v], l2, _, h2, hd, hx => by
      refine ⟨hd v (by simp), ?_, h2⟩
      intro u hu
      have := hx v (by simp) u hu
      simpa using this
  | v :: w :: r, l2, h1, h2, hd, hx => by
      have ih := IP.append (l1 := w :: r) h1.2.2 h2 (fun u hu => hd u (List.mem_cons_of_mem _ hu))
        (fun u hu x hx' => by
          have := hx u (List.mem_cons_of_mem _ hu) x hx'
          simpa [List.getLast?_cons_cons] using this)
      refine ⟨?_, ?_, ih⟩
      · intro hmem
        rcases List.mem_append.mp hmem with h | h
        · exact h1.1 h
        · exact hd v (by simp) h
      · intro u hu
        rcases List.mem_append.mp hu with h | h
        · simpa using h1.2.1 u h
        · have e := hx v (by simp) u h
          constructor
          · intro hadj
            have h3 := (e.mp hadj).1
            rw [List.getLast?_cons_cons] at h3
            exact (h1.1 (List.mem_of_getLast? h3)).elim
          · intro hh
            have h4 : w = u := by simpa using hh
            exact (hd w (by simp) (h4 ▸ h)).elim

lemma IP.reverse : ∀ {l : List V}, IP H l → IP H l.reverse
  | [], _ => by simp [IP]
  | v :: l, h => by
      rw [List.reverse_cons]
      refine IP.append (IP.reverse h.2.2) (IP.single v) ?_ ?_
      · intro u hu
        have hu' : u ∈ l := by simpa using hu
        simp only [List.mem_singleton]
        rintro rfl
        exact h.1 hu'
      · intro u hu w hw
        have hu' : u ∈ l := by simpa using hu
        have hw' : w = v := by simpa using hw
        subst hw'
        rw [List.getLast?_reverse, H.adj_comm, h.2.1 u hu']
        simp

lemma IP.ext_head : ∀ {l : List V}, IP H l → l ≠ [] → ∀ x, (x ∈ l ∨ ∃ u ∈ l, H.Adj x u) →
    ∃ l', IP H l' ∧ l'.head? = some x ∧ l'.getLast? = l.getLast? ∧ ∀ u ∈ l', u = x ∨ u ∈ l
  | [], _, hne, _, _ => (hne rfl).elim
  | v :: r, h, _, x, hx => by
      by_cases hxv : x = v
      · subst hxv
        exact ⟨x :: r, h, rfl, rfl, fun u hu => Or.inr hu⟩
      by_cases hr : x ∈ r ∨ ∃ u ∈ r, H.Adj x u
      · have hrne : r ≠ [] := by
          rintro rfl
          simp at hr
        obtain ⟨l', h1, h2, h3, h4⟩ := IP.ext_head h.2.2 hrne x hr
        refine ⟨l', h1, h2, ?_, fun u hu => (h4 u hu).imp id (List.mem_cons_of_mem _)⟩
        obtain ⟨w, r', rfl⟩ := List.exists_cons_of_ne_nil hrne
        rw [h3, List.getLast?_cons_cons]
      · push Not at hr
        have hxv' : H.Adj x v := by
          rcases hx with hx | ⟨u, hu, hadj⟩
          · rcases List.mem_cons.mp hx with h' | h'
            · exact (hxv h').elim
            · exact (hr.1 h').elim
          · rcases List.mem_cons.mp hu with h' | h'
            · exact h' ▸ hadj
            · exact (hr.2 u h' hadj).elim
        refine ⟨x :: v :: r, ⟨?_, ?_, h⟩, rfl, ?_, fun u hu => ?_⟩
        · simp [hxv, hr.1]
        · intro u hu
          rcases List.mem_cons.mp hu with rfl | h'
          · simp [hxv']
          · have hne : v ≠ u := fun e => h.1 (e ▸ h')
            simp [hr.2 u h', hne]
        · rw [List.getLast?_cons_cons]
        · simpa using hu

lemma IP.adj_get : ∀ {l : List V}, IP H l → ∀ (i j : ℕ) (hi : i < l.length) (hj : j < l.length),
    i < j → (H.Adj l[i] l[j] ↔ j = i + 1)
  | [], _, i, _, hi, _, _ => by simp at hi
  | _ :: _, _, _, 0, _, _, hij => by omega
  | v :: l, h, 0, j + 1, _, hj, _ => by
      have hj' : j < l.length := by simpa using hj
      simp only [List.getElem_cons_zero, List.getElem_cons_succ]
      rw [h.2.1 _ (List.getElem_mem hj')]
      have hn := IP.nodup h.2.2
      have h0 : 0 < l.length := by omega
      rw [List.head?_eq_getElem?, List.getElem?_eq_getElem h0, Option.some_inj,
        List.Nodup.getElem_inj_iff hn]
      omega
  | v :: l, h, i + 1, j + 1, hi, hj, hij => by
      simp only [List.getElem_cons_succ]
      rw [IP.adj_get h.2.2 i j (by simpa using hi) (by simpa using hj) (by omega)]
      omega

/-- An induced path closed up by one more vertex is an induced cycle, in index form. -/
lemma IP.cycle {z : V} {R : List V} (hR : IP H R) (h2 : 2 ≤ R.length)
    (hadj : ∀ u ∈ R, H.Adj z u ↔ (R.head? = some u ∨ R.getLast? = some u))
    (i j : ℕ) (hi : i < (z :: R).length) (hj : j < (z :: R).length) :
    H.Adj (z :: R)[i] (z :: R)[j] ↔
      ((i + 1) % (z :: R).length = j ∨ (j + 1) % (z :: R).length = i) := by
  have hn := IP.nodup hR
  have hlen : (z :: R).length = R.length + 1 := rfl
  have key : ∀ (i j : ℕ) (hi : i < (z :: R).length) (hj : j < (z :: R).length), i < j →
      (H.Adj (z :: R)[i] (z :: R)[j] ↔
        ((i + 1) % (z :: R).length = j ∨ (j + 1) % (z :: R).length = i)) := by
    intro i j hi hj hij
    rw [hlen] at hi hj ⊢
    obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    have hj' : j < R.length := by omega
    have h0 : 0 < R.length := by omega
    have hl : R.length - 1 < R.length := by omega
    rcases Nat.eq_zero_or_pos i with rfl | hipos
    · simp only [List.getElem_cons_zero, List.getElem_cons_succ]
      rw [hadj _ (List.getElem_mem hj'), List.head?_eq_getElem?, List.getElem?_eq_getElem h0,
        List.getLast?_eq_getElem?, List.getElem?_eq_getElem hl, Option.some_inj, Option.some_inj,
        List.Nodup.getElem_inj_iff hn, List.Nodup.getElem_inj_iff hn]
      have e1 : (0 + 1) % (R.length + 1) = 1 := Nat.mod_eq_of_lt (by omega)
      rw [e1]
      rcases Nat.lt_or_ge (j + 1 + 1) (R.length + 1) with hlt | hge
      · rw [Nat.mod_eq_of_lt hlt]
        omega
      · have e2 : j + 1 + 1 = R.length + 1 := by omega
        rw [e2, Nat.mod_self]
        omega
    · obtain ⟨i, rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      simp only [List.getElem_cons_succ]
      rw [IP.adj_get hR i j (by omega) hj' (by omega)]
      have e1 : (i + 1 + 1) % (R.length + 1) = i + 1 + 1 := Nat.mod_eq_of_lt (by omega)
      rw [e1]
      rcases Nat.lt_or_ge (j + 1 + 1) (R.length + 1) with hlt | hge
      · rw [Nat.mod_eq_of_lt hlt]
        omega
      · have e2 : j + 1 + 1 = R.length + 1 := by omega
        rw [e2, Nat.mod_self]
        omega
  rcases lt_trichotomy i j with hij | rfl | hij
  · exact key i j hi hj hij
  · constructor
    · intro h
      exact (H.loopless.irrefl _ h).elim
    · rw [hlen] at hi ⊢
      rcases Nat.lt_or_ge (i + 1) (R.length + 1) with hlt | hge
      · rw [Nat.mod_eq_of_lt hlt]
        omega
      · have e2 : i + 1 = R.length + 1 := by omega
        rw [e2, Nat.mod_self]
        omega
  · rw [H.adj_comm, key j i hj hi hij]
    exact Or.comm

end Paths

section Deg

variable {V : Type} [Fintype V] [DecidableEq V] {H : SimpleGraph V} [DecidableRel H.Adj]

lemma offP_card (hdeg : ∀ v, (univ.filter (fun u => H.Adj v u)).card ≤ 3) :
    ∀ {l : List V}, IP H l → l ≠ [] →
    (univ.filter (fun u => u ∉ l ∧ ∃ v ∈ l, H.Adj v u)).card ≤ 2 * l.length + 1
  | [], _, hne => (hne rfl).elim
  | [v], _, _ => by
      refine le_trans (card_le_card ?_) (le_trans (hdeg v) (by simp))
      intro u hu
      simp only [mem_filter, mem_univ, true_and, List.mem_singleton, exists_eq_left] at hu ⊢
      exact hu.2
  | v :: w :: r, h, _ => by
      have ih := offP_card hdeg h.2.2 (by simp)
      have hvw : H.Adj v w := (h.2.1 w (by simp)).mpr (by simp)
      have hsub : (univ.filter (fun u => u ∉ v :: w :: r ∧ ∃ x ∈ v :: w :: r, H.Adj x u)) ⊆
          ((univ.filter (fun u => H.Adj v u)).erase w) ∪
          (univ.filter (fun u => u ∉ w :: r ∧ ∃ x ∈ w :: r, H.Adj x u)) := by
        intro u hu
        simp only [mem_filter, mem_univ, true_and, mem_union, mem_erase] at hu ⊢
        obtain ⟨hnot, x, hx, hadj⟩ := hu
        have hnot' : u ∉ w :: r := fun hm => hnot (List.mem_cons_of_mem _ hm)
        rcases List.mem_cons.mp hx with rfl | hx'
        · left
          exact ⟨fun e => hnot' (by simp [e]), hadj⟩
        · right
          exact ⟨hnot', x, hx', hadj⟩
      have h1 : ((univ.filter (fun u => H.Adj v u)).erase w).card ≤ 2 := by
        rw [card_erase_of_mem (by simp [hvw])]
        have := hdeg v
        omega
      have h3 := le_trans (card_le_card hsub) (le_trans (card_union_le _ _) (add_le_add h1 ih))
      simp only [List.length_cons] at h3 ⊢
      omega

end Deg

section Decomp

variable {V : Type} [DecidableEq V] (H : SimpleGraph V)

/-- A tree decomposition stored with parent pointers: node `i > 0` hangs below `par i < i`,
and every vertex of bag `i` already seen earlier lies in the parent bag. -/
def TD (K : ℕ) (t : ℕ) (B : ℕ → Finset V) (par : ℕ → ℕ) (W : Finset V) : Prop :=
  0 < t ∧ (∀ i, 0 < i → i < t → par i < i) ∧
  (∀ i, 0 < i → i < t → ∀ x ∈ B i, ∀ j < i, x ∈ B j → x ∈ B (par i)) ∧
  (∀ x, x ∈ W ↔ ∃ i < t, x ∈ B i) ∧
  (∀ x ∈ W, ∀ y ∈ W, H.Adj x y → ∃ i < t, x ∈ B i ∧ y ∈ B i) ∧
  (∀ i < t, (B i).card ≤ K)

variable {H}

lemma TD.add_leaf {K t : ℕ} {B : ℕ → Finset V} {par : ℕ → ℕ} {W : Finset V}
    (h : TD H K t B par W) {a : ℕ} (ha : a < t) (X : Finset V)
    (hXK : X.card ≤ K) (hXW : ∀ x ∈ X, x ∈ W → x ∈ B a)
    (hXn : ∀ x ∈ X, x ∉ W → ∀ y ∈ W, H.Adj x y → y ∈ X) :
    TD H K (t + 1) (Function.update B t X) (Function.update par t a) (W ∪ X) := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := h
  have upB : ∀ i < t, Function.update B t X i = B i :=
    fun i hi => Function.update_of_ne (by omega) _ _
  have upP : ∀ i < t, Function.update par t a i = par i :=
    fun i hi => Function.update_of_ne (by omega) _ _
  have upBt : Function.update B t X t = X := Function.update_self ..
  have upPt : Function.update par t a t = a := Function.update_self ..
  refine ⟨by omega, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi hit
    rcases Nat.lt_succ_iff_lt_or_eq.mp hit with h' | h'
    · rw [upP i h']
      exact h1 i hi h'
    · rw [h', upPt]
      exact ha
  · intro i hi hit x hx j hj hxj
    rcases Nat.lt_succ_iff_lt_or_eq.mp hit with h' | h'
    · rw [upB i h'] at hx
      rw [upB j (by omega)] at hxj
      rw [upP i h', upB _ (lt_trans (h1 i hi h') h')]
      exact h2 i hi h' x hx j hj hxj
    · rw [h'] at hj
      rw [h', upBt] at hx
      rw [upB j hj] at hxj
      rw [h', upPt, upB a ha]
      exact hXW x hx ((h3 x).mpr ⟨j, hj, hxj⟩)
  · intro x
    rw [mem_union, h3 x]
    constructor
    · rintro (⟨i, hi, hx⟩ | hx)
      · exact ⟨i, by omega, by rw [upB i hi]; exact hx⟩
      · exact ⟨t, by omega, by rw [upBt]; exact hx⟩
    · rintro ⟨i, hi, hx⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h' | h'
      · left
        exact ⟨i, h', by rw [upB i h'] at hx; exact hx⟩
      · right
        rw [h', upBt] at hx
        exact hx
  · intro x hx y hy hadj
    rw [mem_union] at hx hy
    by_cases hxW : x ∈ W <;> by_cases hyW : y ∈ W
    · obtain ⟨i, hi, hxi, hyi⟩ := h4 x hxW y hyW hadj
      exact ⟨i, by omega, by rw [upB i hi]; exact ⟨hxi, hyi⟩⟩
    · have hyX := hy.resolve_left hyW
      exact ⟨t, by omega, by rw [upBt]; exact ⟨hXn y hyX hyW x hxW hadj.symm, hyX⟩⟩
    · have hxX := hx.resolve_left hxW
      exact ⟨t, by omega, by rw [upBt]; exact ⟨hxX, hXn x hxX hxW y hyW hadj⟩⟩
    · exact ⟨t, by omega, by rw [upBt]; exact ⟨hx.resolve_left hxW, hy.resolve_left hyW⟩⟩
  · intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h' | h'
    · rw [upB i h']
      exact h5 i h'
    · rw [h', upBt]
      exact hXK

lemma TD.to_tree {K t : ℕ} {B : ℕ → Finset V} {par : ℕ → ℕ} {W : Finset V}
    (h : TD H K t B par W) :
    ∃ S : SimpleGraph (Fin t), S.IsTree ∧
      ∀ x ∈ W, (S.induce {a : Fin t | x ∈ B a.val}).Connected := by
  classical
  obtain ⟨h0, h1, h2, h3, -, -⟩ := h
  let pf : Fin t → Fin t := fun i =>
    if hi : 0 < i.val then ⟨par i.val, lt_trans (h1 i.val hi i.2) i.2⟩ else i
  have pf_val : ∀ i : Fin t, 0 < i.val → (pf i).val = par i.val := by
    intro i hi
    simp only [pf, dif_pos hi]
  have pf_lt : ∀ i : Fin t, 0 < i.val → (pf i).val < i.val := by
    intro i hi
    rw [pf_val i hi]
    exact h1 i.val hi i.2
  let S : SimpleGraph (Fin t) := SimpleGraph.fromRel (fun i j => 0 < i.val ∧ pf i = j)
  have hadj : ∀ i : Fin t, 0 < i.val → S.Adj i (pf i) := by
    intro i hi
    rw [SimpleGraph.fromRel_adj]
    refine ⟨fun e => ?_, Or.inl ⟨hi, rfl⟩⟩
    have := pf_lt i hi
    rw [← e] at this
    omega
  refine ⟨S, ?_, ?_⟩
  · rw [SimpleGraph.isTree_iff_connected_and_card]
    constructor
    · have hreach : ∀ k (i : Fin t), i.val = k → S.Reachable i ⟨0, h0⟩ := by
        intro k
        induction k using Nat.strong_induction_on with
        | _ k ih =>
          intro i hik
          by_cases hi : 0 < i.val
          · exact (hadj i hi).reachable.trans
              (ih (pf i).val (by have := pf_lt i hi; omega) (pf i) rfl)
          · have e : i = ⟨0, h0⟩ := Fin.ext (by simp only; omega)
            rw [e]
      have : Nonempty (Fin t) := ⟨⟨0, h0⟩⟩
      exact (SimpleGraph.connected_iff _).mpr
        ⟨fun u v => (hreach _ u rfl).trans (hreach _ v rfl).symm, inferInstance⟩
    · have hE : S.edgeSet = (fun i : Fin t => s(i, pf i)) ''
          ((Finset.univ.erase (⟨0, h0⟩ : Fin t) : Finset (Fin t)) : Set (Fin t)) := by
        ext e
        induction e using Sym2.ind with
        | _ x y =>
          simp only [SimpleGraph.mem_edgeSet, Set.mem_image, Finset.coe_erase, Finset.coe_univ,
            Set.mem_sdiff, Set.mem_univ, Set.mem_singleton_iff, true_and]
          constructor
          · intro hxy
            rw [SimpleGraph.fromRel_adj] at hxy
            rcases hxy.2 with ⟨hx, hp⟩ | ⟨hy, hp⟩
            · exact ⟨x, fun e => by rw [e] at hx; simp at hx, by rw [hp]⟩
            · exact ⟨y, fun e => by rw [e] at hy; simp at hy, by rw [hp, Sym2.eq_swap]⟩
          · rintro ⟨i, hi, he⟩
            have hi' : 0 < i.val := by
              rcases Nat.eq_zero_or_pos i.val with h' | h'
              · exact (hi (Fin.ext h')).elim
              · exact h'
            rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact hadj i hi'
            · exact (hadj i hi').symm
      have hinj : Set.InjOn (fun i : Fin t => s(i, pf i))
          ((Finset.univ.erase (⟨0, h0⟩ : Fin t) : Finset (Fin t)) : Set (Fin t)) := by
        intro i hi j hj he
        have hi' : 0 < i.val := by
          rcases Nat.eq_zero_or_pos i.val with h' | h'
          · exact ((Finset.mem_erase.mp hi).1 (Fin.ext h')).elim
          · exact h'
        have hj' : 0 < j.val := by
          rcases Nat.eq_zero_or_pos j.val with h' | h'
          · exact ((Finset.mem_erase.mp hj).1 (Fin.ext h')).elim
          · exact h'
        rcases Sym2.eq_iff.mp he with ⟨e1, -⟩ | ⟨e1, e2⟩
        · exact e1
        · have a1 := pf_lt i hi'
          have a2 := pf_lt j hj'
          rw [e2] at a1
          rw [← e1] at a2
          omega
      rw [_root_.Nat.card_coe_set_eq, hE, hinj.ncard_image, Set.ncard_coe_finset,
        Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin,
        Nat.card_eq_fintype_card, Fintype.card_fin]
      omega
  · intro x hx
    have hex : ∃ k, k < t ∧ x ∈ B k := by
      obtain ⟨i, hi, hxi⟩ := (h3 x).mp hx
      exact ⟨i, hi, hxi⟩
    have hm := Nat.find_spec hex
    have hmin : ∀ k, k < t → x ∈ B k → Nat.find hex ≤ k := fun k hk hxk => Nat.find_min' hex ⟨hk, hxk⟩
    let root : {a : Fin t | x ∈ B a.val} := ⟨⟨Nat.find hex, hm.1⟩, hm.2⟩
    have hreach : ∀ k (a : {a : Fin t | x ∈ B a.val}), a.val.val = k →
        (S.induce {a : Fin t | x ∈ B a.val}).Reachable a root := by
      intro k
      induction k using Nat.strong_induction_on with
      | _ k ih =>
        intro a hak
        by_cases hroot : a.val.val = Nat.find hex
        · have e : a = root := Subtype.ext (Fin.ext hroot)
          rw [e]
        · have hge := hmin a.val.val a.val.2 a.2
          have hi : 0 < a.val.val := by omega
          have hx' : x ∈ B (par a.val.val) :=
            h2 a.val.val hi a.val.2 x a.2 (Nat.find hex) (by omega) hm.2
          let pa : {a : Fin t | x ∈ B a.val} := ⟨pf a.val, by
            show x ∈ B (pf a.val).val
            rw [pf_val _ hi]
            exact hx'⟩
          have hadj' : (S.induce {a : Fin t | x ∈ B a.val}).Adj a pa := hadj a.val hi
          exact hadj'.reachable.trans
            (ih (pf a.val).val (by have := pf_lt a.val hi; omega) pa rfl)
    have : Nonempty {a : Fin t | x ∈ B a.val} := ⟨root⟩
    exact (SimpleGraph.connected_iff _).mpr
      ⟨fun u v => (hreach _ u rfl).trans (hreach _ v rfl).symm, inferInstance⟩

end Decomp

section Main

variable {V : Type} [Fintype V] [DecidableEq V] {H : SimpleGraph V} [DecidableRel H.Adj]

theorem main_rec (ℓ : ℕ) (hℓ : 5 ≤ ℓ)
    (hdeg : ∀ v, (univ.filter (fun u => H.Adj v u)).card ≤ 3)
    (hcyc : ∀ (z : V) (R : List V), IP H R → z ∉ R →
      (∀ u ∈ R, H.Adj z u ↔ (R.head? = some u ∨ R.getLast? = some u)) →
      ℓ ≤ R.length + 1 → False) :
    ∀ (m : ℕ) (P : List V) (D : Finset V), D.card * ℓ + P.length < m → IP H P →
      P.length + 2 ≤ ℓ →
      (∀ d ∈ D, d ∉ P ∧ ∀ v ∈ P, ¬ H.Adj v d) →
      (∀ u, u ∉ D → (∃ d ∈ D, H.Adj u d) → ∃ v ∈ P, H.Adj v u) →
      ∀ (t : ℕ) (B : ℕ → Finset V) (par : ℕ → ℕ) (W : Finset V) (a : ℕ),
      TD H (2 * ℓ + 1) t B par W → a < t → (∀ d ∈ D, d ∉ W) →
      (∀ u, u ∉ D → (∃ d ∈ D, H.Adj u d) → u ∈ B a) →
      ∃ (t' : ℕ) (B' : ℕ → Finset V) (par' : ℕ → ℕ),
        TD H (2 * ℓ + 1) t' B' par' (W ∪ D) ∧ t ≤ t' ∧ ∀ i < t, B' i = B i := by
  intro m
  induction m with
  | zero =>
    intro P D hm
    omega
  | succ m ih =>
    intro P D hm hIP hlen hDP hND t B par W a hTD hat hDW hNa
    have hBW : ∀ x, x ∈ B a → x ∈ W := fun x hx => (hTD.2.2.2.1 x).mpr ⟨a, hat, hx⟩
    have hmeas : ∀ D' : Finset V, D'.card < D.card → D'.card * ℓ + ℓ ≤ D.card * ℓ := by
      intro D' hlt
      have h1 : (D'.card + 1) * ℓ ≤ D.card * ℓ := Nat.mul_le_mul_right ℓ hlt
      rw [add_mul, one_mul] at h1
      exact h1
    by_cases hD : D = ∅
    · subst hD
      exact ⟨t, B, par, by simpa using hTD, le_rfl, fun _ _ => rfl⟩
    by_cases hN : ∃ u, u ∉ D ∧ ∃ d ∈ D, H.Adj u d
    swap
    · -- no outside neighbour: start afresh inside `D`
      push Not at hN
      obtain ⟨v, hv⟩ := Finset.nonempty_of_ne_empty hD
      have hXD : ∀ u ∈ insert v (univ.filter (fun u => H.Adj v u)), u ∈ D := by
        intro u hu
        rcases mem_insert.mp hu with rfl | hu
        · exact hv
        · by_contra hc
          exact hN u hc v hv (H.adj_symm (mem_filter.mp hu).2)
      have hXK : (insert v (univ.filter (fun u => H.Adj v u))).card ≤ 2 * ℓ + 1 := by
        have h1 := card_insert_le v (univ.filter (fun u => H.Adj v u))
        have h2 := hdeg v
        omega
      have hTD1 := hTD.add_leaf hat (insert v (univ.filter (fun u => H.Adj v u))) hXK
        (fun x hx hxW => (hDW x (hXD x hx) hxW).elim)
        (fun x hx _ y hyW hadj => by
          by_contra _
          exact hN y (fun hyD => hDW y hyD hyW) x (hXD x hx) (H.adj_symm hadj))
      have hcard : (D \ insert v (univ.filter (fun u => H.Adj v u))).card < D.card :=
        card_lt_card (sdiff_ssubset (by
          intro u hu
          exact hXD u hu) ⟨v, mem_insert_self _ _⟩)
      have hm' := hmeas _ hcard
      obtain ⟨t', B', par', hTD', htt', hB'⟩ := ih [v]
        (D \ insert v (univ.filter (fun u => H.Adj v u)))
        (by simp only [List.length_cons, List.length_nil]; omega) (IP.single v)
        (by simp only [List.length_cons, List.length_nil]; omega)
        (fun d hd => by
          have hd' := (mem_sdiff.mp hd).2
          simp only [mem_insert, mem_filter, mem_univ, true_and, not_or] at hd'
          simp only [List.mem_singleton, forall_eq]
          exact ⟨hd'.1, hd'.2⟩)
        (fun u hu ⟨d, hd, hadj⟩ => by
          have hdD := (mem_sdiff.mp hd).1
          have hd' := (mem_sdiff.mp hd).2
          simp only [mem_insert, mem_filter, mem_univ, true_and, not_or] at hd'
          have huD : u ∈ D := by
            by_contra hc
            exact hN u hc d hdD hadj
          have huX : u ∈ insert v (univ.filter (fun u => H.Adj v u)) := by
            by_contra hc
            exact hu (mem_sdiff.mpr ⟨huD, hc⟩)
          rcases mem_insert.mp huX with rfl | huX
          · exact (hd'.2 hadj).elim
          · exact ⟨v, by simp, (mem_filter.mp huX).2⟩)
        (t + 1) _ _ _ t hTD1 (by omega)
        (fun d hd => by
          rw [mem_union, not_or]
          exact ⟨hDW d (mem_sdiff.mp hd).1, (mem_sdiff.mp hd).2⟩)
        (fun u hu ⟨d, hd, hadj⟩ => by
          rw [Function.update_self]
          by_contra hc
          have hdD := (mem_sdiff.mp hd).1
          have huD : u ∈ D := by
            by_contra hc'
            exact hN u hc' d hdD hadj
          exact hu (mem_sdiff.mpr ⟨huD, hc⟩))
      have hW : W ∪ insert v (univ.filter (fun u => H.Adj v u)) ∪
          (D \ insert v (univ.filter (fun u => H.Adj v u))) = W ∪ D := by
        ext x
        simp only [mem_union, mem_sdiff]
        constructor
        · rintro ((h | h) | h)
          · exact Or.inl h
          · exact Or.inr (hXD x h)
          · exact Or.inr h.1
        · rintro (h | h)
          · exact Or.inl (Or.inl h)
          · by_cases hx : x ∈ insert v (univ.filter (fun u => H.Adj v u))
            · exact Or.inl (Or.inr hx)
            · exact Or.inr ⟨h, hx⟩
      rw [hW] at hTD'
      exact ⟨t', B', par', hTD', by omega, fun i hi => by
        rw [hB' i (by omega)]
        exact Function.update_of_ne (by omega) _ _⟩
    -- some outside vertex sees `D`, so the path is nonempty
    have hPne : P ≠ [] := by
      rintro rfl
      obtain ⟨u, hu, hd⟩ := hN
      obtain ⟨v, hv, -⟩ := hND u hu hd
      simp at hv
    -- dropping the head of a path when it is not needed
    have drop : ∀ Q : List V, IP H Q → Q.length = P.length →
        (∀ d ∈ D, d ∉ Q ∧ ∀ v ∈ Q, ¬ H.Adj v d) →
        (∀ u, u ∉ D → (∃ d ∈ D, H.Adj u d) → ∃ v ∈ Q, H.Adj v u) →
        (¬ ∃ a', a' ∉ D ∧ (∃ d ∈ D, H.Adj a' d) ∧ ∀ v ∈ Q.tail, ¬ H.Adj v a') →
        ∃ (t' : ℕ) (B' : ℕ → Finset V) (par' : ℕ → ℕ),
          TD H (2 * ℓ + 1) t' B' par' (W ∪ D) ∧ t ≤ t' ∧ ∀ i < t, B' i = B i := by
      intro Q hQ hQl hQD hQN hno
      cases Q with
      | nil =>
        have : P.length = 0 := by simpa using hQl.symm
        exact (hPne (List.length_eq_zero_iff.mp this)).elim
      | cons q Q' =>
        simp only [List.length_cons] at hQl
        refine ih Q' D (by omega) hQ.2.2 (by omega)
          (fun d hd => ⟨fun hm => (hQD d hd).1 (List.mem_cons_of_mem _ hm),
            fun v hv => (hQD d hd).2 v (List.mem_cons_of_mem _ hv)⟩)
          (fun u hu hd => ?_) t B par W a hTD hat hDW hNa
        by_contra hc
        push Not at hc
        exact hno ⟨u, hu, hd, fun v hv => hc v hv⟩
    by_cases h1 : ∃ a', a' ∉ D ∧ (∃ d ∈ D, H.Adj a' d) ∧ ∀ v ∈ P.tail, ¬ H.Adj v a'
    swap
    · exact drop P hIP rfl hDP hND h1
    by_cases h2 : ∃ a', a' ∉ D ∧ (∃ d ∈ D, H.Adj a' d) ∧ ∀ v ∈ P.reverse.tail, ¬ H.Adj v a'
    swap
    · exact drop P.reverse hIP.reverse (List.length_reverse ..)
        (fun d hd => ⟨fun hm => (hDP d hd).1 (List.mem_reverse.mp hm),
          fun v hv => (hDP d hd).2 v (List.mem_reverse.mp hv)⟩)
        (fun u hu hd => by
          obtain ⟨v, hv, hadj⟩ := hND u hu hd
          exact ⟨v, List.mem_reverse.mpr hv, hadj⟩) h2
    obtain ⟨a1, ha1D, ⟨da, hda, hada⟩, ha1⟩ := h1
    obtain ⟨b1, hb1D, ⟨db, hdb, hbdb⟩, hb1⟩ := h2
    have ha1P : a1 ∉ P := fun hm => (hDP da hda).2 a1 hm hada
    have hb1P : b1 ∉ P := fun hm => (hDP db hdb).2 b1 hm hbdb
    -- `a1` sees exactly the head of `P`, `b1` exactly its last vertex
    have haP : ∀ u ∈ P, H.Adj u a1 ↔ P.head? = some u := by
      obtain ⟨p0, ps, rfl⟩ := List.exists_cons_of_ne_nil hPne
      obtain ⟨v, hv, hadj⟩ := hND a1 ha1D ⟨da, hda, hada⟩
      have hp0 : H.Adj p0 a1 := by
        rcases List.mem_cons.mp hv with rfl | hv'
        · exact hadj
        · exact (ha1 v hv' hadj).elim
      intro u hu
      simp only [List.head?_cons, Option.some_inj]
      constructor
      · intro h
        rcases List.mem_cons.mp hu with rfl | hu'
        · rfl
        · exact (ha1 u hu' h).elim
      · rintro rfl
        exact hp0
    have hbP : ∀ u ∈ P, H.Adj u b1 ↔ P.getLast? = some u := by
      have hrne : P.reverse ≠ [] := fun e => hPne (List.reverse_eq_nil_iff.mp e)
      obtain ⟨x, xs, hrev⟩ := List.exists_cons_of_ne_nil hrne
      have hlast : P.getLast? = some x := by
        rw [← List.head?_reverse, hrev]
        rfl
      rw [hrev] at hb1
      obtain ⟨v, hv, hadj⟩ := hND b1 hb1D ⟨db, hdb, hbdb⟩
      have hmem : ∀ u, u ∈ P → u = x ∨ u ∈ xs := by
        intro u hu
        have : u ∈ P.reverse := List.mem_reverse.mpr hu
        rw [hrev] at this
        exact List.mem_cons.mp this
      have hx : H.Adj x b1 := by
        rcases hmem v hv with rfl | hv'
        · exact hadj
        · exact (hb1 v hv' hadj).elim
      intro u hu
      rw [hlast, Option.some_inj]
      constructor
      · intro h
        rcases hmem u hu with rfl | hu'
        · rfl
        · exact (hb1 u hu' h).elim
      · rintro rfl
        exact hx
    by_cases hlen2 : P.length + 3 ≤ ℓ
    · -- extend the path by `b1`
      have hIP' : IP H (P ++ [b1]) := IP.append hIP (IP.single b1)
        (fun u hu => by
          simp only [List.mem_singleton]
          rintro rfl
          exact hb1P hu)
        (fun u hu w hw => by
          have hw' : w = b1 := by simpa using hw
          subst hw'
          rw [hbP u hu]
          simp)
      have hXK : ((univ.filter (fun u => u ∉ D ∧ ∃ d ∈ D, H.Adj u d)) ∪
          (D.filter (fun d => H.Adj b1 d))).card ≤ 2 * ℓ + 1 := by
        have h1 : (univ.filter (fun u => u ∉ D ∧ ∃ d ∈ D, H.Adj u d)).card ≤
            2 * P.length + 1 := by
          refine le_trans (card_le_card ?_) (offP_card hdeg hIP hPne)
          intro u hu
          simp only [mem_filter, mem_univ, true_and] at hu ⊢
          obtain ⟨huD, d, hd, hadj⟩ := hu
          exact ⟨fun hm => (hDP d hd).2 u hm hadj, hND u huD ⟨d, hd, hadj⟩⟩
        have h2 : (D.filter (fun d => H.Adj b1 d)).card ≤ 3 := by
          refine le_trans (card_le_card ?_) (hdeg b1)
          intro u hu
          simp only [mem_filter, mem_univ, true_and] at hu ⊢
          exact hu.2
        have h3 := card_union_le (univ.filter (fun u => u ∉ D ∧ ∃ d ∈ D, H.Adj u d))
          (D.filter (fun d => H.Adj b1 d))
        omega
      have hTD1 := hTD.add_leaf hat _ hXK
        (fun x hx hxW => by
          rcases mem_union.mp hx with h | h
          · have h' := (mem_filter.mp h).2
            exact hNa x h'.1 h'.2
          · exact (hDW x (mem_filter.mp h).1 hxW).elim)
        (fun x hx hxW y hyW hadj => by
          rcases mem_union.mp hx with h | h
          · have h' := (mem_filter.mp h).2
            exact (hxW (hBW x (hNa x h'.1 h'.2))).elim
          · have hxD := (mem_filter.mp h).1
            exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _, fun hyD => hDW y hyD hyW,
              x, hxD, H.adj_symm hadj⟩))
      have hcard : (D.filter (fun d => ¬ H.Adj b1 d)).card < D.card :=
        card_lt_card (filter_ssubset.mpr ⟨db, hdb, by simpa using hbdb⟩)
      have hm' := hmeas _ hcard
      obtain ⟨t', B', par', hTD', htt', hB'⟩ := ih (P ++ [b1]) (D.filter (fun d => ¬ H.Adj b1 d))
        (by simp only [List.length_append, List.length_cons, List.length_nil]; omega) hIP'
        (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
        (fun d hd => by
          have hdD := (mem_filter.mp hd).1
          have hdb' := (mem_filter.mp hd).2
          refine ⟨fun hm => ?_, fun v hv => ?_⟩
          · rcases List.mem_append.mp hm with h | h
            · exact (hDP d hdD).1 h
            · have : d = b1 := by simpa using h
              exact hb1D (this ▸ hdD)
          · rcases List.mem_append.mp hv with h | h
            · exact (hDP d hdD).2 v h
            · have : v = b1 := by simpa using h
              rw [this]
              exact hdb')
        (fun u hu ⟨d, hd, hadj⟩ => by
          have hdD := (mem_filter.mp hd).1
          by_cases huD : u ∈ D
          · have : H.Adj b1 u := by
              by_contra hc
              exact hu (mem_filter.mpr ⟨huD, hc⟩)
            exact ⟨b1, by simp, this⟩
          · obtain ⟨v, hv, hvu⟩ := hND u huD ⟨d, hdD, hadj⟩
            exact ⟨v, List.mem_append_left _ hv, hvu⟩)
        (t + 1) _ _ _ t hTD1 (by omega)
        (fun d hd => by
          have hdD := (mem_filter.mp hd).1
          have hdb' := (mem_filter.mp hd).2
          simp only [mem_union, mem_filter, mem_univ, true_and, not_or, not_and]
          exact ⟨hDW d hdD, fun h => (h hdD).elim, fun _ => hdb'⟩)
        (fun u hu ⟨d, hd, hadj⟩ => by
          rw [Function.update_self]
          have hdD := (mem_filter.mp hd).1
          by_cases huD : u ∈ D
          · have : H.Adj b1 u := by
              by_contra hc
              exact hu (mem_filter.mpr ⟨huD, hc⟩)
            exact mem_union_right _ (mem_filter.mpr ⟨huD, this⟩)
          · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _, huD, d, hdD, hadj⟩))
      have hW : W ∪ ((univ.filter (fun u => u ∉ D ∧ ∃ d ∈ D, H.Adj u d)) ∪
          (D.filter (fun d => H.Adj b1 d))) ∪ (D.filter (fun d => ¬ H.Adj b1 d)) = W ∪ D := by
        ext x
        simp only [mem_union, mem_filter, mem_univ, true_and]
        constructor
        · rintro ((h | h | h) | h)
          · exact Or.inl h
          · exact Or.inl (hBW x (hNa x h.1 h.2))
          · exact Or.inr h.1
          · exact Or.inr h.1
        · rintro (h | h)
          · exact Or.inl (Or.inl h)
          · by_cases hx : H.Adj b1 x
            · exact Or.inl (Or.inr (Or.inr ⟨h, hx⟩))
            · exact Or.inr ⟨h, hx⟩
      rw [hW] at hTD'
      exact ⟨t', B', par', hTD', by omega, fun i hi => by
        rw [hB' i (by omega)]
        exact Function.update_of_ne (by omega) _ _⟩
    · -- the path has full length: either an induced cycle, or `D` is disconnected
      classical
      by_cases hreach : Relation.ReflTransGen (fun u v => H.Adj u v ∧ v ∈ D) da db
      · exfalso
        have hpath : ∀ y, Relation.ReflTransGen (fun u v => H.Adj u v ∧ v ∈ D) da y →
            ∃ l, IP H l ∧ l.head? = some y ∧ l.getLast? = some a1 ∧ ∀ u ∈ l, u ∈ D ∨ u = a1 := by
          intro y hy
          induction hy with
          | refl =>
            obtain ⟨l', h1, h2, h3, h4⟩ := IP.ext_head (IP.single a1) (by simp) da
              (Or.inr ⟨a1, by simp, H.adj_symm hada⟩)
            refine ⟨l', h1, h2, by simpa using h3, fun u hu => ?_⟩
            rcases h4 u hu with rfl | h
            · exact Or.inl hda
            · exact Or.inr (by simpa using h)
          | tail _ hyz ih' =>
            obtain ⟨l, h1, h2, h3, h4⟩ := ih'
            have hne : l ≠ [] := by
              rintro rfl
              simp at h2
            obtain ⟨l', h1', h2', h3', h4'⟩ := IP.ext_head h1 hne _
              (Or.inr ⟨_, List.mem_of_mem_head? (by rw [h2]; rfl), H.adj_symm hyz.1⟩)
            refine ⟨l', h1', h2', h3'.trans h3, fun u hu => ?_⟩
            rcases h4' u hu with rfl | h
            · exact Or.inl hyz.2
            · exact h4 u h
        obtain ⟨l, h1, h2, h3, h4⟩ := hpath db hreach
        have hne : l ≠ [] := by
          rintro rfl
          simp at h2
        obtain ⟨l', h1', h2', h3', h4'⟩ := IP.ext_head h1 hne b1
          (Or.inr ⟨db, List.mem_of_mem_head? (by rw [h2]; rfl), hbdb⟩)
        rw [h3] at h3'
        -- the last vertex of `P` lies in its tail, hence `a1 ≠ b1`
        have hab : a1 ≠ b1 := by
          rintro rfl
          obtain ⟨p0, ps, rfl⟩ := List.exists_cons_of_ne_nil hPne
          cases ps with
          | nil =>
            simp only [List.length_cons, List.length_nil] at hlen hlen2
            omega
          | cons p1 r =>
            have hl : ∃ x, (p0 :: p1 :: r).getLast? = some x := by
              cases hq : (p0 :: p1 :: r).getLast? with
              | none => simp at hq
              | some x => exact ⟨x, rfl⟩
            obtain ⟨x, hx⟩ := hl
            have hxm : x ∈ p1 :: r := by
              rw [List.getLast?_cons_cons] at hx
              exact List.mem_of_getLast? hx
            exact ha1 x hxm ((hbP x (List.mem_cons_of_mem _ hxm)).mpr hx)
        cases l' with
        | nil => simp at h2'
        | cons x T =>
          have hx : x = b1 := by simpa using h2'
          subst hx
          have hTne : T ≠ [] := by
            rintro rfl
            have : x = a1 := by simpa using h3'
            exact hab this.symm
          have hTlast : T.getLast? = some a1 := by
            obtain ⟨w, T', rfl⟩ := List.exists_cons_of_ne_nil hTne
            rw [List.getLast?_cons_cons] at h3'
            exact h3'
          have hTmem : ∀ u ∈ T, u ∈ D ∨ u = a1 := by
            intro u hu
            rcases h4' u (List.mem_cons_of_mem _ hu) with rfl | h
            · exact (h1'.1 hu).elim
            · exact h4 u h
          have hTP : ∀ u ∈ T, u ∉ P := by
            intro u hu
            rcases hTmem u hu with h | rfl
            · exact (hDP u h).1
            · exact ha1P
          have hR : IP H (T ++ P) := IP.append h1'.2.2 hIP hTP (fun u hu w hw => by
            rcases hTmem u hu with h | rfl
            · constructor
              · intro hadj
                exact ((hDP u h).2 w hw (H.adj_symm hadj)).elim
              · rintro ⟨hl, -⟩
                rw [hTlast, Option.some_inj] at hl
                exact (ha1D (hl ▸ h)).elim
            · rw [H.adj_comm, haP w hw]
              simp [hTlast])
          refine hcyc x (T ++ P) hR ?_ ?_ ?_
          · intro hm
            rcases List.mem_append.mp hm with h | h
            · exact h1'.1 h
            · exact hb1P h
          · intro u hu
            rw [List.head?_append_of_ne_nil _ hTne, List.getLast?_append_of_ne_nil _ hPne]
            rcases List.mem_append.mp hu with h | h
            · rw [h1'.2.1 u h]
              constructor
              · exact Or.inl
              · rintro (h' | h')
                · exact h'
                · exact (hTP u h (List.mem_of_getLast? h')).elim
            · rw [H.adj_comm, hbP u h]
              constructor
              · exact Or.inr
              · rintro (h' | h')
                · exact (hTP u (List.mem_of_mem_head? h') h).elim
                · exact h'
          · have : 0 < T.length := List.length_pos_iff.mpr hTne
            simp only [List.length_append]
            omega
      · -- split off the part of `D` reachable from `da`
        have hclos : ∀ u ∈ D.filter (fun y => Relation.ReflTransGen
            (fun u v => H.Adj u v ∧ v ∈ D) da y), ∀ v ∈ D, H.Adj u v →
            v ∈ D.filter (fun y => Relation.ReflTransGen (fun u v => H.Adj u v ∧ v ∈ D) da y) := by
          intro u hu v hv hadj
          exact mem_filter.mpr ⟨hv, Relation.ReflTransGen.tail (mem_filter.mp hu).2 ⟨hadj, hv⟩⟩
        have hc0 : (D.filter (fun y => Relation.ReflTransGen
            (fun u v => H.Adj u v ∧ v ∈ D) da y)).card < D.card :=
          card_lt_card (filter_ssubset.mpr ⟨db, hdb, hreach⟩)
        have hc1 : (D.filter (fun y => ¬ Relation.ReflTransGen
            (fun u v => H.Adj u v ∧ v ∈ D) da y)).card < D.card :=
          card_lt_card (filter_ssubset.mpr ⟨da, hda, by
            simpa using (Relation.ReflTransGen.refl : Relation.ReflTransGen
              (fun u v => H.Adj u v ∧ v ∈ D) da da)⟩)
        have hm0 := hmeas _ hc0
        have hm1 := hmeas _ hc1
        have hout0 : ∀ u, u ∉ D.filter (fun y => Relation.ReflTransGen
            (fun u v => H.Adj u v ∧ v ∈ D) da y) →
            (∃ d ∈ D.filter (fun y => Relation.ReflTransGen
              (fun u v => H.Adj u v ∧ v ∈ D) da y), H.Adj u d) →
            u ∉ D ∧ ∃ d ∈ D, H.Adj u d := by
          rintro u hu ⟨d, hd, hadj⟩
          exact ⟨fun huD => hu (hclos d hd u huD (H.adj_symm hadj)), d, (mem_filter.mp hd).1, hadj⟩
        have hout1 : ∀ u, u ∉ D.filter (fun y => ¬ Relation.ReflTransGen
            (fun u v => H.Adj u v ∧ v ∈ D) da y) →
            (∃ d ∈ D.filter (fun y => ¬ Relation.ReflTransGen
              (fun u v => H.Adj u v ∧ v ∈ D) da y), H.Adj u d) →
            u ∉ D ∧ ∃ d ∈ D, H.Adj u d := by
          rintro u hu ⟨d, hd, hadj⟩
          have hdD := (mem_filter.mp hd).1
          refine ⟨fun huD => ?_, d, hdD, hadj⟩
          have hur : Relation.ReflTransGen (fun u v => H.Adj u v ∧ v ∈ D) da u := by
            by_contra hc
            exact hu (mem_filter.mpr ⟨huD, hc⟩)
          exact (mem_filter.mp hd).2 (Relation.ReflTransGen.tail hur ⟨hadj, hdD⟩)
        obtain ⟨t1, B1, par1, hTD1, ht1, hB1⟩ := ih P
          (D.filter (fun y => Relation.ReflTransGen (fun u v => H.Adj u v ∧ v ∈ D) da y))
          (by omega) hIP hlen (fun d hd => hDP d (mem_filter.mp hd).1)
          (fun u hu hd => hND u (hout0 u hu hd).1 (hout0 u hu hd).2)
          t B par W a hTD hat (fun d hd => hDW d (mem_filter.mp hd).1)
          (fun u hu hd => hNa u (hout0 u hu hd).1 (hout0 u hu hd).2)
        obtain ⟨t2, B2, par2, hTD2, ht2, hB2⟩ := ih P
          (D.filter (fun y => ¬ Relation.ReflTransGen (fun u v => H.Adj u v ∧ v ∈ D) da y))
          (by omega) hIP hlen (fun d hd => hDP d (mem_filter.mp hd).1)
          (fun u hu hd => hND u (hout1 u hu hd).1 (hout1 u hu hd).2)
          t1 B1 par1 _ a hTD1 (by omega)
          (fun d hd => by
            rw [mem_union, not_or]
            exact ⟨hDW d (mem_filter.mp hd).1, fun h => (mem_filter.mp hd).2 (mem_filter.mp h).2⟩)
          (fun u hu hd => by
            rw [hB1 a hat]
            exact hNa u (hout1 u hu hd).1 (hout1 u hu hd).2)
        have hW : W ∪ (D.filter (fun y => Relation.ReflTransGen
            (fun u v => H.Adj u v ∧ v ∈ D) da y)) ∪ (D.filter (fun y => ¬ Relation.ReflTransGen
            (fun u v => H.Adj u v ∧ v ∈ D) da y)) = W ∪ D := by
          rw [union_assoc, filter_union_filter_not_eq]
        rw [hW] at hTD2
        exact ⟨t2, B2, par2, hTD2, by omega, fun i hi => by rw [hB2 i (by omega), hB1 i hi]⟩

end Main

end OMA.KLNS

theorem OMA.solution : OMA.R_Erdos559_erdos_559_variants_draganic_petrova_R1_H1_R1.H1 := by
  classical
  intro n ℓ G J hℓ hdeg hC
  let H : SimpleGraph (Fin n) := SimpleGraph.fromRel (fun u v => G.Adj u v ∧ u ∈ J ∧ v ∈ J)
  have hH : ∀ u v, H.Adj u v ↔ (G.Adj u v ∧ u ∈ J ∧ v ∈ J) := by
    intro u v
    rw [SimpleGraph.fromRel_adj]
    constructor
    · rintro ⟨-, h | h⟩
      · exact h
      · exact ⟨h.1.symm, h.2.2, h.2.1⟩
    · intro h
      exact ⟨G.ne_of_adj h.1, Or.inl h⟩
  have hdegH : ∀ v, (Finset.univ.filter (fun u => H.Adj v u)).card ≤ 3 := by
    intro v
    refine le_trans (Finset.card_le_card (fun u hu => ?_))
      (le_trans (G.degree_le_maxDegree v) hdeg)
    rw [SimpleGraph.mem_neighborFinset]
    exact ((hH v u).mp (Finset.mem_filter.mp hu).2).1
  have hcycH : ∀ (z : Fin n) (R : List (Fin n)), OMA.KLNS.IP H R → z ∉ R →
      (∀ u ∈ R, H.Adj z u ↔ (R.head? = some u ∨ R.getLast? = some u)) →
      ℓ ≤ R.length + 1 → False := by
    intro z R hR hz hadj hlen
    have h2 : 2 ≤ R.length := by omega
    have hnd : (z :: R).Nodup := List.nodup_cons.mpr ⟨hz, hR.nodup⟩
    have hcard : (z :: R).toFinset.card = (z :: R).length := List.toFinset_card_of_nodup hnd
    have hcyc := OMA.KLNS.IP.cycle hR h2 hadj
    have hJ : ∀ i (hi : i < (z :: R).length), (z :: R)[i] ∈ J := by
      intro i hi
      have hl : (z :: R).length = R.length + 1 := rfl
      by_cases h : i + 1 < (z :: R).length
      · have := (hcyc i (i + 1) hi h).mpr (Or.inl (Nat.mod_eq_of_lt h))
        exact ((hH _ _).mp this).2.1
      · have hi0 : (i - 1) < (z :: R).length := by omega
        have e : (i - 1 + 1) % (z :: R).length = i := by
          rw [Nat.mod_eq_of_lt (by omega)]
          omega
        have := (hcyc (i - 1) i hi0 hi).mpr (Or.inl e)
        exact ((hH _ _).mp this).2.2
    refine hC (z :: R).toFinset ?_ ⟨by rw [hcard]; exact hlen, ?_⟩
    · intro u hu
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp (List.mem_toFinset.mp hu)
      exact hJ i hi
    · let f : Fin (z :: R).toFinset.card → (z :: R).toFinset := fun i =>
        ⟨(z :: R)[i.val]'(hcard ▸ i.2), List.mem_toFinset.mpr (List.getElem_mem _)⟩
      have hf : Function.Bijective f := by
        rw [Fintype.bijective_iff_injective_and_card]
        refine ⟨fun i j hij => ?_, by rw [Fintype.card_fin, Fintype.card_coe]⟩
        have h1 : (z :: R)[i.val]'(hcard ▸ i.2) = (z :: R)[j.val]'(hcard ▸ j.2) :=
          congrArg Subtype.val hij
        exact Fin.ext ((List.Nodup.getElem_inj_iff hnd).mp h1)
      refine ⟨(Equiv.ofBijective f hf).symm, ?_⟩
      intro u v
      obtain ⟨i, rfl⟩ := hf.surjective u
      obtain ⟨j, rfl⟩ := hf.surjective v
      rw [Equiv.ofBijective_symm_apply_apply, Equiv.ofBijective_symm_apply_apply]
      have hi : i.val < (z :: R).length := hcard ▸ i.2
      have hj : j.val < (z :: R).length := hcard ▸ j.2
      have key := hcyc i.val j.val hi hj
      have gen : ∀ (p q c d : ℕ), c = d →
          (((p + 1) % c = q ∨ (q + 1) % c = p) ↔ ((p + 1) % d = q ∨ (q + 1) % d = p)) := by
        intro p q c d hcd
        rw [hcd]
      rw [gen _ _ _ _ hcard, ← key]
      show G.Adj (z :: R)[i.val] (z :: R)[j.val] ↔ H.Adj (z :: R)[i.val] (z :: R)[j.val]
      rw [hH]
      exact ⟨fun h => ⟨h, hJ _ hi, hJ _ hj⟩, fun h => h.1⟩
  have hTD0 : OMA.KLNS.TD H (2 * ℓ + 1) 1 (fun _ => (∅ : Finset (Fin n))) (fun _ => 0) ∅ := by
    refine ⟨by omega, fun i h1 h2 => by omega, fun i h1 h2 => by omega, fun x => by simp,
      fun x hx => by simp at hx, fun i _ => by simp⟩
  obtain ⟨t, B, par, hTD, -, -⟩ := OMA.KLNS.main_rec ℓ hℓ hdegH hcycH (J.card * ℓ + 1) [] J
    (by simp) trivial (by simp only [List.length_nil]; omega) (fun d _ => ⟨by simp, by simp⟩)
    (fun u hu ⟨d, _, hadj⟩ => (hu ((hH u d).mp hadj).2.1).elim)
    1 _ _ ∅ 0 hTD0 (by omega) (by simp)
    (fun u hu ⟨d, _, hadj⟩ => (hu ((hH u d).mp hadj).2.1).elim)
  rw [Finset.empty_union] at hTD
  obtain ⟨S, hS, hconn⟩ := hTD.to_tree
  obtain ⟨-, -, -, h3, h4, h5⟩ := hTD
  refine ⟨t, S, fun a => B a.val, hS, fun a => ⟨h5 a.val a.2, fun x hx => (h3 x).mpr ⟨a.val, a.2, hx⟩⟩,
    fun x hx => ?_, fun x hx y hy hadj => ?_, fun x hx => hconn x hx⟩
  · obtain ⟨i, hi, hxi⟩ := (h3 x).mp hx
    exact ⟨⟨i, hi⟩, hxi⟩
  · obtain ⟨i, hi, hxi, hyi⟩ := h4 x hx y hy ((hH x y).mpr ⟨hadj, hx, hy⟩)
    exact ⟨⟨i, hi⟩, hxi, hyi⟩
