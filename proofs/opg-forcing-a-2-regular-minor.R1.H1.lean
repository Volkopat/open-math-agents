import OMAReductions.R_opg_forcing_a_2_regular_minor_R1
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Data.List.Count
import Mathlib.Data.List.GetD
import Mathlib.Tactic.Linarith

/-!
A standalone formalization of the exact mathematical statement underlying
opg-forcing-a-2-regular-minor.R1.H1. This is a classical component of the
2-regular-minor problem; it does not settle the full parent conjecture.

The argument uses a longest path with a maximal terminal cycle, following
Erdős and Gallai, "On maximal paths and circuits of graphs" (1959):
https://www.renyi.hu/~p_erdos/1959-10.pdf

Build status and the exact site-registration state are recorded separately.
-/

namespace UnsolvedMath.LongCycle

open SimpleGraph

universe u

/-- Hamilton paths on exactly the vertices listed by `c`, with specified ends. -/
def HamiltonEnds {V : Type*} (G : SimpleGraph V) (c : List V) (a b : V) : Prop :=
  ∃ p : List V, p.Perm c ∧ p.IsChain G.Adj ∧
    p.head? = some a ∧ p.getLast? = some b

def LongestChain {V : Type*} (G : SimpleGraph V) (p : List V) : Prop :=
  p.Nodup ∧ p.IsChain G.Adj ∧
    ∀ q : List V, q.Nodup → q.IsChain G.Adj → q.length ≤ p.length

structure TerminalCycle {V : Type*} (G : SimpleGraph V) (stem cycle : List V) : Prop where
  nodup : (stem ++ cycle).Nodup
  chain : (stem ++ cycle).IsChain G.Adj
  three_le : 3 ≤ cycle.length
  close : ∀ a ∈ cycle.getLast?, ∀ b ∈ cycle.head?, G.Adj a b

/-- An auxiliary count for the two arcs obtained by cutting a Hamilton cycle.
Consecutive positions cannot simultaneously satisfy `q` then `p`.
Only the first position can contribute an unmatched `p`. -/
lemma countP_add_countP_le {V : Type*} (p q : V → Bool) :
    ∀ l : List V, l.IsChain (fun x y => ¬ (q x = true ∧ p y = true)) →
      l.countP p + l.countP q ≤ l.length +
        (if l.head?.any p then 1 else 0) := by
  intro l
  induction l with
  | nil => simp
  | cons a l ih =>
    intro h
    cases l with
    | nil =>
      cases hp : p a <;> cases hq : q a <;> simp [hp, hq]
    | cons b l =>
      have hab : ¬ (q a = true ∧ p b = true) := h.rel
      have ht := ih h.tail
      have ht' : (b :: l).countP p + (b :: l).countP q ≤
          (b :: l).length + (if p b then 1 else 0) := ht
      have hflags : (if p b then 1 else 0) + (if q a then 1 else 0) ≤ (1 : ℕ) := by
        cases hqa : q a <;> cases hpb : p b <;> simp_all
      rw [List.countP_cons (p := p) (a := a) (l := b :: l),
        List.countP_cons (p := q) (a := a) (l := b :: l)]
      change (b :: l).countP p + (if p a then 1 else 0) +
        ((b :: l).countP q + (if q a then 1 else 0)) ≤
        (b :: l).length + 1 + (if p a then 1 else 0)
      omega

variable {V : Type*} {G : SimpleGraph V}

lemma chain_reverse {p : List V} (h : p.IsChain G.Adj) : p.reverse.IsChain G.Adj :=
  List.isChain_reverse.mpr (h.imp (fun _ _ h => h.symm))

lemma chain_append {p q : List V} {a b : V}
    (hp : p.IsChain G.Adj) (hq : q.IsChain G.Adj)
    (ha : p.getLast? = some a) (hb : q.head? = some b) (hab : G.Adj a b) :
    (p ++ q).IsChain G.Adj := by
  apply hp.append hq
  intro x hx y hy
  rw [ha] at hx
  rw [hb] at hy
  have hx' : x = a := by simpa using hx.symm
  have hy' : y = b := by simpa using hy.symm
  simpa [hx', hy'] using hab

/-- The first of the two path reconnections used in the successor degree-sum argument. -/
lemma reconnect_first {L R Q : List V} {a b x y u v : V}
    (hL : L.IsChain G.Adj) (hR : R.IsChain G.Adj) (hQ : Q.IsChain G.Adj)
    (hLx : L.head? = some x) (hLu : L.getLast? = some u)
    (hRv : R.head? = some v) (hRb : R.getLast? = some b)
    (hQy : Q.head? = some y) (hQa : Q.getLast? = some a)
    (hyu : G.Adj y u) (hxv : G.Adj x v) :
    HamiltonEnds G ((L ++ R) ++ Q) a b := by
  have hQn : Q.reverse ≠ [] := by
    intro h
    have : Q = [] := List.reverse_eq_nil_iff.mp h
    simp [this] at hQa
  have hRn : R ≠ [] := by intro h; simp [h] at hRv
  have hLn : L.reverse ≠ [] := by
    intro h
    have : L = [] := List.reverse_eq_nil_iff.mp h
    simp [this] at hLx
  refine ⟨(Q.reverse ++ L.reverse) ++ R, ?_, ?_, ?_, ?_⟩
  · have h₁ : ((Q.reverse ++ L.reverse) ++ R).Perm ((Q ++ L) ++ R) :=
      ((List.reverse_perm Q).append (List.reverse_perm L)).append_right R
    have h₂ : ((Q ++ L) ++ R).Perm ((L ++ R) ++ Q) := by
      rw [List.append_assoc]
      exact List.perm_append_comm
    exact h₁.trans h₂
  · apply chain_append (chain_append (chain_reverse hQ) (chain_reverse hL)
      (by simpa using hQy) (by simpa using hLu) hyu) hR
      (by simpa [List.getLast?_append_of_ne_nil _ hLn] using hLx) hRv hxv
  · simp only [List.head?_append_of_ne_nil _ (List.append_ne_nil_of_left_ne_nil hQn _),
      List.head?_append_of_ne_nil _ hQn, List.head?_reverse, hQa]
  · simpa only [List.getLast?_append_of_ne_nil _ hRn] using hRb

/-- The other reconnection, cutting the second arc of a Hamilton cycle. -/
lemma reconnect_second {P L R : List V} {a b x y u v : V}
    (hP : P.IsChain G.Adj) (hL : L.IsChain G.Adj) (hR : R.IsChain G.Adj)
    (hPx : P.head? = some x) (hPb : P.getLast? = some b)
    (hLy : L.head? = some y) (hLu : L.getLast? = some u)
    (hRv : R.head? = some v) (hRa : R.getLast? = some a)
    (hxu : G.Adj x u) (hyv : G.Adj y v) :
    HamiltonEnds G (P ++ (L ++ R)) a b := by
  have hPn : P ≠ [] := by intro h; simp [h] at hPx
  have hLn : L ≠ [] := by intro h; simp [h] at hLy
  have hRn : R.reverse ≠ [] := by
    intro h
    have : R = [] := List.reverse_eq_nil_iff.mp h
    simp [this] at hRa
  refine ⟨(R.reverse ++ L) ++ P, ?_, ?_, ?_, ?_⟩
  · have h₁ : ((R.reverse ++ L) ++ P).Perm ((R ++ L) ++ P) :=
      ((List.reverse_perm R).append_right L).append_right P
    have h₂ : ((R ++ L) ++ P).Perm (P ++ (L ++ R)) :=
      List.perm_append_comm.trans (List.Perm.append_left P List.perm_append_comm)
    exact h₁.trans h₂
  · apply chain_append (chain_append (chain_reverse hR) hL
      (by simpa using hRv) hLy hyv.symm) hP
      (by simpa only [List.getLast?_append_of_ne_nil _ hLn] using hLu) hPx hxu.symm
  · simp only [List.head?_append_of_ne_nil _ (List.append_ne_nil_of_left_ne_nil hRn _),
      List.head?_append_of_ne_nil _ hRn, List.head?_reverse, hRa]
  · simpa only [List.getLast?_append_of_ne_nil _ hPn] using hPb

/-- If the ends of two arcs cannot be joined by a Hamilton path, the two
opposite starting vertices have at most one neighbor per position on average. -/
lemma arc_neighbor_count_le [DecidableRel G.Adj] {P Q : List V} {a b x y : V}
    (hP : P.IsChain G.Adj) (hQ : Q.IsChain G.Adj)
    (hPx : P.head? = some x) (hPb : P.getLast? = some b)
    (hQy : Q.head? = some y) (hQa : Q.getLast? = some a)
    (hno : ¬ HamiltonEnds G (P ++ Q) a b) :
    (P ++ Q).countP (fun z => decide (G.Adj x z)) +
      (P ++ Q).countP (fun z => decide (G.Adj y z)) ≤ (P ++ Q).length := by
  have hpairs : P.IsChain (fun u v =>
      ¬ (decide (G.Adj y u) = true ∧ decide (G.Adj x v) = true)) := by
    apply List.isChain_iff_forall_rel_of_append_cons_cons.mpr
    intro u v L R he hh
    have hsplit : P = (L ++ [u]) ++ (v :: R) := by simpa using he
    have hL := (List.isChain_append.mp (hsplit ▸ hP)).1
    have hR := (List.isChain_append.mp (hsplit ▸ hP)).2.1
    have hLx : (L ++ [u]).head? = some x := by
      rw [hsplit, List.head?_append_of_ne_nil _ (by simp)] at hPx
      exact hPx
    have hRb : (v :: R).getLast? = some b := by
      rw [hsplit, List.getLast?_append_of_ne_nil _ (by simp)] at hPb
      exact hPb
    apply hno
    rw [hsplit]
    exact reconnect_first hL hR hQ hLx (by simp) (by rfl) hRb hQy hQa
      (of_decide_eq_true hh.1) (of_decide_eq_true hh.2)
  have hqpairs : Q.IsChain (fun u v =>
      ¬ (decide (G.Adj x u) = true ∧ decide (G.Adj y v) = true)) := by
    apply List.isChain_iff_forall_rel_of_append_cons_cons.mpr
    intro u v L R he hh
    have hsplit : Q = (L ++ [u]) ++ (v :: R) := by simpa using he
    have hL := (List.isChain_append.mp (hsplit ▸ hQ)).1
    have hR := (List.isChain_append.mp (hsplit ▸ hQ)).2.1
    have hLy : (L ++ [u]).head? = some y := by
      rw [hsplit, List.head?_append_of_ne_nil _ (by simp)] at hQy
      exact hQy
    have hRa : (v :: R).getLast? = some a := by
      rw [hsplit, List.getLast?_append_of_ne_nil _ (by simp)] at hQa
      exact hQa
    apply hno
    rw [hsplit]
    exact reconnect_second hP hL hR hPx hPb hLy (by simp) (by rfl) hRa
      (of_decide_eq_true hh.1) (of_decide_eq_true hh.2)
  have hfirst := countP_add_countP_le
    (fun z => decide (G.Adj x z)) (fun z => decide (G.Adj y z)) P hpairs
  have hsecond := countP_add_countP_le
    (fun z => decide (G.Adj y z)) (fun z => decide (G.Adj x z)) Q hqpairs
  simp [hPx, hQy] at hfirst hsecond
  simp only [List.countP_append, List.length_append]
  omega

lemma countP_neighbors_eq_degree [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {c : List V} (hc : c.Nodup) (x : V)
    (hs : ∀ z, G.Adj x z → z ∈ c) :
    c.countP (fun z => decide (G.Adj x z)) = G.degree x := by
  have hset : G.neighborFinset x = c.toFinset.filter (G.Adj x) := by
    ext z
    simp only [mem_neighborFinset, Finset.mem_filter, List.mem_toFinset]
    exact ⟨fun hz => ⟨hs z hz, hz⟩, fun hz => hz.2⟩
  rw [← card_neighborFinset_eq_degree, hset, hc.card_eq_countP]

/-- The successor-degree lemma of the Erdős–Gallai cycle argument.
The lists are the two arcs, starting immediately after the specified ends. -/
lemma hamiltonEnds_of_degree_sum [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {P Q : List V} {a b x y : V}
    (hnd : (P ++ Q).Nodup) (hP : P.IsChain G.Adj) (hQ : Q.IsChain G.Adj)
    (hPx : P.head? = some x) (hPb : P.getLast? = some b)
    (hQy : Q.head? = some y) (hQa : Q.getLast? = some a)
    (hx : ∀ z, G.Adj x z → z ∈ P ++ Q)
    (hy : ∀ z, G.Adj y z → z ∈ P ++ Q)
    (hdeg : (P ++ Q).length < G.degree x + G.degree y) :
    HamiltonEnds G (P ++ Q) a b := by
  by_contra hno
  have h := arc_neighbor_count_le hP hQ hPx hPb hQy hQa hno
  rw [countP_neighbors_eq_degree hnd x hx, countP_neighbors_eq_degree hnd y hy] at h
  omega

lemma all_of_chain_imp {α : Type*} (R : α → Prop) :
    ∀ l : List α, l.IsChain (fun x y => R x → R y) →
      (∀ x ∈ l.head?, R x) → ∀ x ∈ l, R x := by
  intro l
  induction l with
  | nil => simp
  | cons a l ih =>
    intro hc ha x hx
    have hRa : R a := ha a rfl
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hRa
    · exact ih hc.tail (fun b hb => hc.rel_head? hb hRa) x hx

/-- A terminal cycle with large degrees has a Hamilton path from its attachment
vertex to every other vertex, provided all existing Hamilton endpoints have no
neighbors outside the cycle. This is the propagation step in the lollipop proof. -/
lemma all_cycle_ends [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {D : List V} {b x : V}
    (hD : D.head? = some x)
    (hnd : (D ++ [b]).Nodup) (hch : (D ++ [b]).IsChain G.Adj)
    (hclose : G.Adj b x)
    (hdeg : ∀ z ∈ D ++ [b], (D ++ [b]).length < 2 * G.degree z)
    (hclosed : ∀ z, HamiltonEnds G (D ++ [b]) b z →
      ∀ w, G.Adj z w → w ∈ D ++ [b]) :
    ∀ z ∈ D, HamiltonEnds G (D ++ [b]) b z := by
  let C := D ++ [b]
  let Good := fun z => HamiltonEnds G C b z
  change C.Nodup at hnd
  change C.IsChain G.Adj at hch
  have hDn : D ≠ [] := by intro h; simp [h] at hD
  have hx : Good x := by
    refine ⟨C.reverse, List.reverse_perm C, chain_reverse hch, ?_, ?_⟩
    · simp [C]
    · simp only [List.getLast?_reverse, C, List.head?_append_of_ne_nil _ hDn, hD]
  have hback : D.IsChain (fun u v => Good v → Good u) := by
    apply List.isChain_iff_forall_rel_of_append_cons_cons.mpr
    intro u v L R he hv
    have heC : C = (L ++ [u]) ++ ((v :: R) ++ [b]) := by simp [C, he]
    have hP := (List.isChain_append.mp (heC ▸ hch)).1
    have hQ := (List.isChain_append.mp (heC ▸ hch)).2.1
    have hPx : (L ++ [u]).head? = some x := by
      have hh : C.head? = some x := by
        simpa only [C, List.head?_append_of_ne_nil _ hDn] using hD
      rw [heC, List.head?_append_of_ne_nil _ (by simp)] at hh
      exact hh
    have hux : ∀ w, G.Adj x w → w ∈ (L ++ [u]) ++ ((v :: R) ++ [b]) := by
      simpa only [← heC] using hclosed x hx
    have hvx : ∀ w, G.Adj v w → w ∈ (L ++ [u]) ++ ((v :: R) ++ [b]) := by
      simpa only [← heC] using hclosed v hv
    have hxm : x ∈ C := by
      have hxD : x ∈ D := List.mem_of_mem_head? hD
      exact List.mem_append_left [b] hxD
    have hvm : v ∈ C := by simp [C, he]
    have hd := hdeg x hxm
    have hdv := hdeg v hvm
    have hsum : ((L ++ [u]) ++ ((v :: R) ++ [b])).length <
        G.degree x + G.degree v := by
      rw [← heC]
      change C.length < 2 * G.degree x at hd
      change C.length < 2 * G.degree v at hdv
      omega
    change HamiltonEnds G C b u
    rw [heC]
    exact hamiltonEnds_of_degree_sum (heC ▸ hnd) hP hQ hPx (by simp)
      (by simp) (by
        rw [List.getLast?_append_of_ne_nil _ (by simp)]
        rfl) hux hvx hsum
  have hstart : ∀ z ∈ D.reverse.head?, Good z := by
    intro z hz
    have hz' : D.getLast? = some z := by simpa using hz
    refine ⟨b :: D, ?_, ?_, by rfl, ?_⟩
    · exact List.perm_append_comm (l₁ := [b]) (l₂ := D)
    · apply (List.isChain_append.mp hch).1.cons
      intro v hv
      rw [hD] at hv
      have hv' : v = x := by simpa using hv.symm
      simpa [hv'] using hclose
    · simpa [List.getLast?_cons_of_ne_nil hDn] using hz'
  have hr : D.reverse.IsChain (fun u v => Good u → Good v) :=
    List.isChain_reverse.mpr hback
  intro z hz
  exact all_of_chain_imp Good D.reverse hr hstart z (List.mem_reverse.mpr hz)

lemma last_neighbors_mem {p : List V} (hp : LongestChain G p) {v : V}
    (hv : p.getLast? = some v) : ∀ w, G.Adj v w → w ∈ p := by
  intro w hw
  by_contra hwm
  have hnd : (p ++ [w]).Nodup := by
    rw [List.nodup_append]
    refine ⟨hp.1, by simp, ?_⟩
    intro a ha b hb
    have hb' : b = w := by simpa using hb
    subst b
    intro haw
    exact hwm (haw ▸ ha)
  have hch := chain_append hp.2.1 (List.isChain_singleton w) hv (by rfl) hw
  have hh := hp.2.2 (p ++ [w]) hnd hch
  simp only [List.length_append, List.length_singleton] at hh
  omega

/-- Replacing the cycle part by a Hamilton path preserves maximal path length.
Maximality of the terminal cycle then forces all endpoint neighbors into it. -/
lemma terminal_end_closed {stem C : List V} {b z : V}
    (ht : TerminalCycle G stem C) (hl : LongestChain G (stem ++ C))
    (hb : C.head? = some b)
    (hm : ∀ s c, TerminalCycle G s c →
      (s ++ c).length = (stem ++ C).length → c.length ≤ C.length)
    (hz : HamiltonEnds G C b z) :
    ∀ w, G.Adj z w → w ∈ C := by
  obtain ⟨p, hp, hpch, hpb, hpz⟩ := hz
  have hpn : p ≠ [] := by intro h; simp [h] at hpz
  have hperm : (stem ++ p).Perm (stem ++ C) := List.Perm.append_left stem hp
  have hnd : (stem ++ p).Nodup := hperm.nodup_iff.mpr ht.nodup
  have hch : (stem ++ p).IsChain G.Adj := by
    apply (List.isChain_append.mp ht.chain).1.append hpch
    intro a ha v hv
    have hv' : v = b := by rw [hpb] at hv; simpa using hv.symm
    subst v
    exact (List.isChain_append.mp ht.chain).2.2 a ha b hb
  have hlong : LongestChain G (stem ++ p) := by
    refine ⟨hnd, hch, ?_⟩
    intro q hq hqch
    rw [hperm.length_eq]
    exact hl.2.2 q hq hqch
  have hend : (stem ++ p).getLast? = some z := by
    simpa only [List.getLast?_append_of_ne_nil _ hpn] using hpz
  intro w hw
  have hmem := last_neighbors_mem hlong hend w hw
  rcases List.mem_append.mp hmem with hws | hwp
  · by_contra hwc
    obtain ⟨A, B, hstem⟩ := List.append_of_mem hws
    have heq : stem ++ p = A ++ ((w :: B) ++ p) := by simp [hstem]
    have hnew : TerminalCycle G A ((w :: B) ++ p) := by
      refine ⟨heq ▸ hnd, heq ▸ hch, ?_, ?_⟩
      · have hpLen := hp.length_eq
        have hc3 := ht.three_le
        simp only [List.length_append, List.length_cons]
        omega
      · intro a ha v hv
        rw [List.getLast?_append_of_ne_nil _ hpn, hpz] at ha
        have ha' : a = z := by simpa using ha.symm
        have hv' : v = w := by simpa using hv.symm
        simpa [ha', hv'] using hw
    have hlen : (A ++ ((w :: B) ++ p)).length = (stem ++ C).length := by
      rw [← heq]
      exact hperm.length_eq
    have hh := hm A ((w :: B) ++ p) hnew hlen
    simp only [List.length_append, List.length_cons, hp.length_eq] at hh
    omega
  · exact hp.mem_iff.mp hwp

lemma exists_longest_chain [Fintype V] [Nonempty V] (G : SimpleGraph V) :
    ∃ p : List V, LongestChain G p := by
  classical
  let v : V := Classical.choice inferInstance
  let PP : ℕ → Prop := fun n => ∃ p : List V,
    p.Nodup ∧ p.IsChain G.Adj ∧ p.length = n
  have h1 : PP 1 := ⟨[v], by simp, List.isChain_singleton v, by rfl⟩
  have hn : 1 ≤ Fintype.card V := Fintype.card_pos
  obtain ⟨p, hnd, hch, he⟩ := Nat.findGreatest_spec hn h1
  refine ⟨p, hnd, hch, ?_⟩
  intro q hq hqc
  rw [he]
  exact Nat.le_findGreatest hq.length_le_card ⟨q, hq, hqc, rfl⟩

lemma getD_last (p : List V) (hp : p ≠ []) (v : V) :
    p.getD (p.length - 1) v = p.getLast hp := by
  rw [List.getLast_eq_getElem, List.getD_eq_getElem]

lemma longest_chain_terminal [Fintype V] [DecidableEq V] [Nonempty V]
    [DecidableRel G.Adj] (hdeg : ∀ v, 2 ≤ G.degree v) :
    ∃ s c, TerminalCycle G s c ∧ LongestChain G (s ++ c) := by
  obtain ⟨p, hp⟩ := exists_longest_chain G
  have hpn : p ≠ [] := by
    intro h
    let v : V := Classical.choice inferInstance
    have hh := hp.2.2 [v] (by simp) (List.isChain_singleton v)
    simp [h] at hh
  let v := p.getLast hpn
  have hv : p.getLast? = some v := List.getLast?_eq_some_getLast hpn
  have hcard : 1 < (G.neighborFinset v).card := by
    rw [card_neighborFinset_eq_degree]
    exact hdeg v
  obtain ⟨w, hw, hwp⟩ := Finset.exists_mem_ne hcard (p.getD (p.length - 2) v)
  have haw := (mem_neighborFinset G v w).mp hw
  have hwm := last_neighbors_mem hp hv w haw
  obtain ⟨i, hi, hiw⟩ := List.getElem_of_mem hwm
  have hiD : p.getD i v = w := by rw [List.getD_eq_getElem _ _ hi]; exact hiw
  have hilast : i ≠ p.length - 1 := by
    intro he
    have hew : w = v := by rw [← hiD, he, getD_last]
    exact haw.ne hew.symm
  have hiprev : i ≠ p.length - 2 := by
    intro he
    exact hwp (by rw [← hiD, he])
  have hib : i + 3 ≤ p.length := by omega
  refine ⟨p.take i, p.drop i, ?_, ?_⟩
  · refine ⟨by simpa using hp.1, by simpa using hp.2.1, ?_, ?_⟩
    · simp only [List.length_drop]
      omega
    · intro a ha b hb
      have hdlast : (p.drop i).getLast? = some v := by
        rw [List.getLast?_drop, if_neg (by omega)]
        exact hv
      have hdhead : (p.drop i).head? = some w := by
        rw [List.head?_drop, List.getElem?_eq_getElem hi, hiw]
      rw [hdlast] at ha
      rw [hdhead] at hb
      have ha' : a = v := by simpa using ha.symm
      have hb' : b = w := by simpa using hb.symm
      simpa [ha', hb'] using haw
  · simpa using hp

/-- Choose a longest path whose terminal cycle is as long as possible. -/
lemma exists_maximal_terminal [Fintype V] [DecidableEq V] [Nonempty V]
    [DecidableRel G.Adj] (hdeg : ∀ v, 2 ≤ G.degree v) :
    ∃ s c, TerminalCycle G s c ∧ LongestChain G (s ++ c) ∧
      ∀ s' c', TerminalCycle G s' c' →
        (s' ++ c').length = (s ++ c).length → c'.length ≤ c.length := by
  classical
  let P : ℕ → Prop := fun n => ∃ s c : List V,
    TerminalCycle G s c ∧ LongestChain G (s ++ c) ∧ c.length = n
  obtain ⟨s₀, c₀, ht₀, hl₀⟩ := longest_chain_terminal hdeg
  have hb₀ : c₀.length ≤ Fintype.card V := by
    have hh := ht₀.nodup.length_le_card
    simp only [List.length_append] at hh
    omega
  have hp₀ : P c₀.length := ⟨s₀, c₀, ht₀, hl₀, rfl⟩
  obtain ⟨s, c, ht, hl, he⟩ := Nat.findGreatest_spec hb₀ hp₀
  refine ⟨s, c, ht, hl, ?_⟩
  intro s' c' ht' hlen
  have hl' : LongestChain G (s' ++ c') := by
    refine ⟨ht'.nodup, ht'.chain, ?_⟩
    intro q hq hqc
    rw [hlen]
    exact hl.2.2 q hq hqc
  have hb' : c'.length ≤ Fintype.card V := by
    have hh := ht'.nodup.length_le_card
    simp only [List.length_append] at hh
    omega
  rw [he]
  exact Nat.le_findGreatest hb' ⟨s', c', ht', hl', rfl⟩

lemma cycle_of_list {C : List V} (hnd : C.Nodup) (hch : C.IsChain G.Adj)
    (h3 : 3 ≤ C.length)
    (hclose : ∀ a ∈ C.getLast?, ∀ b ∈ C.head?, G.Adj a b) :
    ∃ v, ∃ p : G.Walk v v, p.IsCycle ∧ p.length = C.length := by
  have hne : C ≠ [] := by intro h; simp [h] at h3
  let p := Walk.ofSupport C hne hch
  have hplen : p.length = C.length - 1 := Walk.length_ofSupport hne hch
  have hp : p.IsPath := Walk.IsPath.mk' (by
    rw [Walk.support_ofSupport]
    exact hnd)
  have hadj : G.Adj (C.getLast hne) (C.head hne) :=
    hclose _ (List.getLast?_eq_some_getLast hne) _ (List.head?_eq_some_head hne)
  refine ⟨C.getLast hne, Walk.cons hadj p, ?_, ?_⟩
  · apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
    refine ⟨by simpa using hp, ?_⟩
    simp only [Walk.length_cons, hplen]
    omega
  · simp only [Walk.length_cons, hplen]
    omega

/-- The structural step: high minimum degree forces either a sufficiently long
cycle or a small vertex set attached to the remaining graph through one vertex. -/
lemma high_degree_long_cycle_or_block [Fintype V] [DecidableEq V] [Nonempty V]
    [DecidableRel G.Adj] (k : ℕ) (hk : 3 ≤ k)
    (hdeg : ∀ v, k - 1 < 2 * G.degree v) :
    (∃ v, ∃ p : G.Walk v v, p.IsCycle ∧ k ≤ p.length) ∨
      ∃ (b : V) (D : List V), (b :: D).Nodup ∧ 2 ≤ D.length ∧ D.length + 1 < k ∧
        ∀ z ∈ D, ∀ w, G.Adj z w → w ∈ b :: D := by
  have hd2 : ∀ v, 2 ≤ G.degree v := by
    intro v
    have hh := hdeg v
    omega
  obtain ⟨s, C, ht, hl, hm⟩ := exists_maximal_terminal hd2
  have hnd := (List.nodup_append.mp ht.nodup).2.1
  have hch := (List.isChain_append.mp ht.chain).2.1
  by_cases hc : k ≤ C.length
  · obtain ⟨v, p, hp, he⟩ := cycle_of_list hnd hch ht.three_le ht.close
    exact Or.inl ⟨v, p, hp, by omega⟩
  right
  cases C with
  | nil => have hh := ht.three_le; simp at hh
  | cons b D =>
    have hD2 : 2 ≤ D.length := by have hh := ht.three_le; simpa using hh
    have hDn : D ≠ [] := by intro h; simp [h] at hD2
    let x := D.getLast hDn
    have hDx : D.reverse.head? = some x := by
      rw [List.head?_reverse]
      exact List.getLast?_eq_some_getLast hDn
    have hp : (D.reverse ++ [b]).Perm (b :: D) := by
      simpa using List.reverse_perm (b :: D)
    have hrev : (D.reverse ++ [b]).IsChain G.Adj := by
      simpa using chain_reverse hch
    have hclose : G.Adj b x := by
      have hlast : (b :: D).getLast? = some x := by
        simpa [List.getLast?_cons_of_ne_nil hDn] using List.getLast?_eq_some_getLast hDn
      exact (ht.close x hlast b rfl).symm
    have hrd : ∀ z ∈ D.reverse ++ [b], (D.reverse ++ [b]).length < 2 * G.degree z := by
      intro z hz
      have hd := hdeg z
      rw [hp.length_eq]
      omega
    have hclosed : ∀ z, HamiltonEnds G (D.reverse ++ [b]) b z →
        ∀ w, G.Adj z w → w ∈ D.reverse ++ [b] := by
      intro z hz w hw
      obtain ⟨p, hpp, hpc, hph, hpl⟩ := hz
      have hz' : HamiltonEnds G (b :: D) b z := ⟨p, hpp.trans hp, hpc, hph, hpl⟩
      exact hp.mem_iff.mpr (terminal_end_closed ht hl rfl hm hz' w hw)
    have hall := all_cycle_ends hDx (hp.nodup_iff.mpr hnd) hrev hclose hrd hclosed
    refine ⟨b, D, hnd, hD2, by simpa only [List.length_cons] using Nat.lt_of_not_ge hc, ?_⟩
    intro z hz w hw
    exact hp.mem_iff.mp (hclosed z (hall z (List.mem_reverse.mpr hz)) w hw)

lemma edge_bound_of_attached_set [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (S : Finset V) (b : V)
    (hclosed : ∀ z ∈ S, ∀ w, G.Adj z w → w ∈ insert b S) :
    G.edgeFinset.card ≤ (G.induce (↑(Sᶜ) : Set V)).edgeFinset.card +
      (insert b S).card.choose 2 := by
  let T := Sᶜ
  let C := insert b S
  have hcover : G.edgeFinset ⊆
      (G.edgeFinset.filter fun e => e.toFinset ⊆ T) ∪
      (G.edgeFinset.filter fun e => e.toFinset ⊆ C) := by
    intro e he
    induction e using Sym2.ind with
    | _ u v =>
      have ha : G.Adj u v := by simpa using he
      by_cases hu : u ∈ S
      · apply Finset.mem_union_right
        apply Finset.mem_filter.mpr
        refine ⟨he, ?_⟩
        simp only [Sym2.toFinset_mk_eq, Finset.insert_subset_iff, Finset.singleton_subset_iff]
        exact ⟨Finset.mem_insert_of_mem hu, hclosed u hu v ha⟩
      · by_cases hv : v ∈ S
        · apply Finset.mem_union_right
          apply Finset.mem_filter.mpr
          refine ⟨he, ?_⟩
          simp only [Sym2.toFinset_mk_eq, Finset.insert_subset_iff, Finset.singleton_subset_iff]
          exact ⟨hclosed v hv u ha.symm, Finset.mem_insert_of_mem hv⟩
        · apply Finset.mem_union_left
          apply Finset.mem_filter.mpr
          refine ⟨he, ?_⟩
          simp [T, Sym2.toFinset_mk_eq, Finset.insert_subset_iff, hu, hv]
  have hcount := (Finset.card_le_card hcover).trans (Finset.card_union_le _ _)
  rw [G.card_filter_edgeFinset_toFinset_subset T,
    G.card_filter_edgeFinset_toFinset_subset C] at hcount
  have hcomplete : (G.induce (C : Set V)).edgeFinset.card ≤ C.card.choose 2 := by
    simpa using (G.induce (C : Set V)).card_edgeFinset_le_card_choose_two
  have hh := hcount.trans (Nat.add_le_add_left hcomplete _)
  exact hh

lemma two_mul_choose_two_le (n : ℕ) : 2 * n.choose 2 ≤ n * (n - 1) := by
  rw [Nat.choose_two_right, Nat.mul_comm]
  exact Nat.div_mul_le_self _ _

lemma card_ge_of_edge_density [Fintype V] [Nonempty V] [DecidableRel G.Adj]
    (k : ℕ) (hd : (k - 1) * Fintype.card V ≤ 2 * G.edgeFinset.card) :
    k ≤ Fintype.card V := by
  classical
  have hn : 0 < Fintype.card V := Fintype.card_pos
  have he := G.card_edgeFinset_le_card_choose_two
  have hc := two_mul_choose_two_le (Fintype.card V)
  by_contra h
  have hkn : Fintype.card V < k := Nat.lt_of_not_ge h
  have hk : 1 ≤ k := by omega
  have hn' : 1 ≤ Fintype.card V := hn
  have hsub : k - 1 + 1 = k := Nat.sub_add_cancel hk
  have hsubn : Fintype.card V - 1 + 1 = Fintype.card V := Nat.sub_add_cancel hn'
  nlinarith

lemma dense_cycle_induction (k : ℕ) (hk : 3 ≤ k) (n : ℕ) :
    ∀ (V : Type u) [Fintype V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj],
      Fintype.card V = n → (k - 1) * Fintype.card V ≤ 2 * G.edgeFinset.card →
      ∃ v, ∃ p : G.Walk v v, p.IsCycle ∧ k ≤ p.length := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V _ _ G _ hn hd
    have hkn := card_ge_of_edge_density k hd
    by_cases hlow : ∃ v, 2 * G.degree v ≤ k - 1
    · obtain ⟨v, hv⟩ := hlow
      let W := ({v} : Set V)ᶜ
      let F := G.induce W
      have hn3 : 3 ≤ Fintype.card V := hk.trans hkn
      obtain ⟨w, _, hw⟩ := (Finset.univ : Finset V).exists_mem_ne (by simpa using (show 1 < Fintype.card V by omega)) v
      let : Nonempty W := ⟨⟨w, by simpa [W] using hw⟩⟩
      have hcard : Fintype.card W + 1 = Fintype.card V := by
        change Fintype.card ↥(({v} : Set V)ᶜ) + 1 = Fintype.card V
        have hs : Fintype.card ({v} : Set V) = 1 := Fintype.card_unique
        rw [Fintype.card_compl_set, hs]
        omega
      have hsmall : Fintype.card W < n := by omega
      have hcount : F.edgeFinset.card + G.degree v = G.edgeFinset.card := by
        change (G.induce ({v} : Set V)ᶜ).edgeFinset.card + G.degree v = _
        rw [card_edgeFinset_induce_compl_singleton, card_edgeFinset_deleteIncidenceSet,
          Nat.sub_add_cancel (G.degree_le_card_edgeFinset v)]
      have hdf : (k - 1) * Fintype.card W ≤ 2 * F.edgeFinset.card := by
        nlinarith
      obtain ⟨x, p, hp, hlen⟩ := ih (Fintype.card W) hsmall W F rfl hdf
      let f : F →g G := ⟨Subtype.val, fun ha => ha⟩
      refine ⟨x.val, p.map f, ?_, ?_⟩
      · exact (Walk.isCycle_map_iff_of_injective Subtype.val_injective).mpr hp
      · simpa only [Walk.length_map] using hlen
    · have hmin : ∀ v, k - 1 < 2 * G.degree v := by
        intro v
        exact Nat.lt_of_not_ge (fun hv => hlow ⟨v, hv⟩)
      rcases high_degree_long_cycle_or_block k hk hmin with hcycle | ⟨b, D, hnd, hD2, hDk, hclosed⟩
      · exact hcycle
      let S := D.toFinset
      have hb : b ∉ S := by simpa [S] using (List.nodup_cons.mp hnd).1
      have hScard : S.card = D.length :=
        List.toFinset_card_of_nodup (List.nodup_cons.mp hnd).2
      have hS2 : 2 ≤ S.card := by omega
      have hSk : S.card + 1 ≤ k - 1 := by omega
      let W := (↑(Sᶜ) : Set V)
      let F := G.induce W
      let : Nonempty W := ⟨⟨b, by simpa [W] using hb⟩⟩
      have hcard : Fintype.card W + S.card = Fintype.card V := by
        have hs : Fintype.card W = (Sᶜ).card := Fintype.card_coe (Sᶜ)
        rw [hs]
        exact Finset.card_compl_add_card S
      have hsmall : Fintype.card W < n := by omega
      have hbound : G.edgeFinset.card ≤ F.edgeFinset.card + (S.card + 1).choose 2 := by
        have hh := edge_bound_of_attached_set (G := G) S b (by
          intro z hz w hw
          have hzD : z ∈ D := by simpa [S] using hz
          simpa [S] using hclosed z hzD w hw)
        simpa only [Finset.card_insert_of_notMem hb] using hh
      have hchoose : 2 * (S.card + 1).choose 2 ≤ (S.card + 1) * S.card := by
        simpa using two_mul_choose_two_le (S.card + 1)
      have hprod := Nat.mul_le_mul_right S.card hSk
      have hdf : (k - 1) * Fintype.card W ≤ 2 * F.edgeFinset.card := by
        nlinarith
      obtain ⟨x, p, hp, hlen⟩ := ih (Fintype.card W) hsmall W F rfl hdf
      let f : F →g G := ⟨Subtype.val, fun ha => ha⟩
      refine ⟨x.val, p.map f, ?_, ?_⟩
      · exact (Walk.isCycle_map_iff_of_injective Subtype.val_injective).mpr hp
      · simpa only [Walk.length_map] using hlen

/-- Exact mathematical statement of the published H1 component. -/
theorem long_cycle_of_edge_density (V : Type u) [Fintype V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (hk : 3 ≤ k)
    (hd : (k - 1) * Fintype.card V ≤ 2 * G.edgeFinset.card) :
    ∃ v, ∃ p : G.Walk v v, p.IsCycle ∧ k ≤ p.length :=
  dense_cycle_induction k hk (Fintype.card V) V G rfl hd


end UnsolvedMath.LongCycle

theorem OMA.solution : OMA.R_opg_forcing_a_2_regular_minor_R1.H1 :=
  UnsolvedMath.LongCycle.long_cycle_of_edge_density

