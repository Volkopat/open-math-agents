import OMAReductions.R_Erdos64_erdos_64_R3
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Interval.Finset.Nat

/-! Credit: @wispiANt. The single-edge degree bound and cycle lifting are
adapted from @JamesSlash (PR 466). The cut predicate comes from
@Hennyrick (PR 2088). The longest-path and two-bypass arguments adapt
@TheWaler (PR 5859) to subsets of high-degree vertices without a marked edge. -/

namespace OMA.R_Erdos64_erdos_64_R3_H1_R1

open SimpleGraph

-- The vertices of degree greater than three form an independent set.
def H1 : Prop :=
    ∀ (V : Type) (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj],
    3 ≤ G.minDegree →
    (∀ (z : V) (S : Set V), z ∈ S → (∃ x ∈ S, x ≠ z) → (∃ y : V, y ∉ S) →
      ∃ x ∈ S, x ≠ z ∧ ∃ y ∉ S, G.Adj x y) →
    (∀ a b, G.Adj a b → G.degree a = 3 ∨ G.degree b = 3) →
    ∃ (k : ℕ) (v : V) (c : G.Walk v v), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2 ^ k

-- Every edge between two high-degree vertices becomes the sole edge of
-- an explicit nontrivial cut upon removing a third vertex. In any subset of
-- high-degree vertices one can peel at degree two while retaining a prescribed vertex.
def H2 : Prop :=
    ∀ (V : Type) (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj],
    3 ≤ G.minDegree →
    (∀ (z : V) (S : Set V), z ∈ S → (∃ x ∈ S, x ≠ z) → (∃ y : V, y ∉ S) →
      ∃ x ∈ S, x ≠ z ∧ ∃ y ∉ S, G.Adj x y) →
    (∃ a b, G.Adj a b ∧ 3 < G.degree a ∧ 3 < G.degree b) →
    (∀ (T : Finset V) (r : V), (∃ x ∈ T, x ≠ r) → (∀ x ∈ T, 3 < G.degree x) →
      ∃ x ∈ T, x ≠ r ∧ (T.filter (G.Adj x)).card ≤ 2) →
    (∀ a b, G.Adj a b → 3 < G.degree a → 3 < G.degree b →
      ∃ z : V, ∃ S : Set V, z ∈ S ∧
        ((a ∈ S ∧ a ≠ z ∧ b ∉ S) ∨ (b ∈ S ∧ b ≠ z ∧ a ∉ S)) ∧
        ∀ x ∈ S, x ≠ z → ∀ y ∉ S, G.Adj x y → s(x, y) = s(a, b)) →
    ∃ (k : ℕ) (v : V) (c : G.Walk v v), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2 ^ k

theorem delete_edge_degree {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (a b : V) (minimum : 3 ≤ G.minDegree)
    (ha : 3 < G.degree a) (hb : 3 < G.degree b) (x : V) :
    3 ≤ (G.deleteEdges {s(a, b)}).degree x := by
  let H := G.deleteEdges {s(a, b)}
  change 3 ≤ H.degree x
  let removed : Finset V := if x = a then {b} else if x = b then {a} else ∅
  have inclusion : G.neighborFinset x ⊆ H.neighborFinset x ∪ removed := by
    intro y hy
    have adj := (G.mem_neighborFinset x y).mp hy
    apply Finset.mem_union.mpr
    by_cases h : s(x, y) = s(a, b)
    · right
      rcases (Sym2.mk_eq_mk_iff (p := (x, y)) (q := (a, b))).mp h with hd | hd
      · have hx : x = a := congrArg Prod.fst hd
        have hyb : y = b := congrArg Prod.snd hd
        simp [removed, hx, hyb]
      · have hx : x = b := congrArg Prod.fst hd
        have hya : y = a := congrArg Prod.snd hd
        by_cases hab : a = b <;> simp [removed, hx, hya, hab, eq_comm]
    · left
      apply (H.mem_neighborFinset x y).mpr
      exact SimpleGraph.deleteEdges_adj.mpr ⟨adj, by simpa using h⟩
  have cardinal : G.degree x ≤ H.degree x + removed.card := by
    simpa only [card_neighborFinset_eq_degree] using
      (Finset.card_le_card inclusion).trans (Finset.card_union_le _ _)
  have loss : removed.card ≤ 1 := by
    dsimp [removed]
    split
    · simp
    · split <;> simp
  by_cases endpoints : x = a ∨ x = b
  · have larger : 3 < G.degree x := endpoints.elim (fun hx => hx.symm ▸ ha)
      (fun hx => hx.symm ▸ hb)
    omega
  · have noLoss : removed.card = 0 := by simp [removed, (not_or.mp endpoints).1,
      (not_or.mp endpoints).2]
    have lower := minimum.trans (G.minDegree_le_degree x)
    omega

theorem critical_cut {V : Type} (G : SimpleGraph V) (a b : V)
    (block : (∀ (z : V) (S : Set V), z ∈ S → (∃ x ∈ S, x ≠ z) → (∃ y : V, y ∉ S) →
      ∃ x ∈ S, x ≠ z ∧ ∃ y ∉ S, G.Adj x y))
    (essential : ¬ (∀ (z : V) (S : Set V), z ∈ S → (∃ x ∈ S, x ≠ z) → (∃ y : V, y ∉ S) →
      ∃ x ∈ S, x ≠ z ∧ ∃ y ∉ S, (G.deleteEdges {s(a, b)}).Adj x y)) :
    ∃ z : V, ∃ S : Set V, z ∈ S ∧
        ((a ∈ S ∧ a ≠ z ∧ b ∉ S) ∨ (b ∈ S ∧ b ≠ z ∧ a ∉ S)) ∧
        ∀ x ∈ S, x ≠ z → ∀ y ∉ S, G.Adj x y → s(x, y) = s(a, b) := by
  classical
  push Not at essential
  obtain ⟨z, S, hz, inside, outside, noEdge⟩ := essential
  obtain ⟨x, hx, hxz, y, hy, xy⟩ := block z S hz inside outside
  have unique : ∀ u ∈ S, u ≠ z → ∀ v ∉ S, G.Adj u v → s(u, v) = s(a, b) := by
    intro u hu huz v hv uv
    by_contra ne
    exact noEdge u hu huz v hv (SimpleGraph.deleteEdges_adj.mpr ⟨uv, by simpa using ne⟩)
  refine ⟨z, S, hz, ?_, unique⟩
  rcases (Sym2.mk_eq_mk_iff (p := (x, y)) (q := (a, b))).mp (unique x hx hxz y hy xy) with e | e
  · have xa : x = a := congrArg Prod.fst e
    have yb : y = b := congrArg Prod.snd e
    exact Or.inl ⟨xa ▸ hx, xa ▸ hxz, yb ▸ hy⟩
  · have xb : x = b := congrArg Prod.fst e
    have ya : y = a := congrArg Prod.snd e
    exact Or.inr ⟨xb ▸ hx, xb ▸ hxz, ya ▸ hy⟩

section
variable {V : Type}

lemma interval_same (f : ℕ → V) (P : V → Prop) (i j : ℕ) (h : i ≤ j)
    (same : ∀ t, i ≤ t → t < j → (P (f t) ↔ P (f (t+1)))) : P (f i) ↔ P (f j) := by
  induction j, h using Nat.le_induction with
  | base => rfl
  | succ j h ih =>
    exact (ih (fun t ht hj => same t ht (by omega))).trans (same j h (by omega))

lemma chord_safe (G : SimpleGraph V) (cuts : (∀ (z : V) (S : Set V), z ∈ S → (∃ x ∈ S, x ≠ z) → (∃ y, y ∉ S) →
      ∃ x ∈ S, x ≠ z ∧ ∃ y ∉ S, (G).Adj x y)) (f : ℕ → V) (l m r : ℕ)
    (hl : 0 < l) (lm : l < m) (mr : m < r)
    (inj : ∀ i ≤ r, ∀ j ≤ r, f i = f j → i = j)
    (path : ∀ i < r, G.Adj (f i) (f (i+1)))
    (left : G.Adj (f 0) (f l)) (right : G.Adj (f 0) (f r)) :
    (∀ (z : V) (S : Set V), z ∈ S → (∃ x ∈ S, x ≠ z) → (∃ y, y ∉ S) →
      ∃ x ∈ S, x ≠ z ∧ ∃ y ∉ S, (G.deleteEdges {s(f 0,f m)}).Adj x y) := by
  classical
  let D := G.deleteEdges {s(f 0,f m)}
  intro z S hz hex hout
  by_contra! miss
  have eqside (x y : V) (hx : x ≠ z) (hy : y ≠ z) (e : D.Adj x y) : x ∈ S ↔ y ∈ S := by
    constructor
    · intro h; by_contra h'; exact miss x h hx y h' e
    · intro h; by_contra h'; exact miss y h hy x h' e.symm
  obtain ⟨x,hx,hxz,y,hy,edge⟩ := cuts z S hz hex hout
  have hmark : s(x,y) = s(f 0,f m) := by
    by_contra hn
    exact miss x hx hxz y hy (SimpleGraph.deleteEdges_adj.mpr ⟨edge,by simpa using hn⟩)
  have hyz : y ≠ z := fun e => hy (e ▸ hz)
  have ends : f 0 ≠ z ∧ f m ≠ z ∧ ¬(f 0 ∈ S ↔ f m ∈ S) := by
    rw [Sym2.eq,Sym2.rel_iff'] at hmark
    rcases hmark with ⟨h,h'⟩ | ⟨h,h'⟩ <;> grind
  have adjD (i j : ℕ) (hi : i ≤ r) (hj : j ≤ r) (avoid : ¬((i=0 ∧ j=m) ∨ (i=m ∧ j=0)))
      (e : G.Adj (f i) (f j)) : D.Adj (f i) (f j) := by
    apply SimpleGraph.deleteEdges_adj.mpr
    refine ⟨e,?_⟩
    simp only [Set.mem_singleton_iff,Sym2.eq,Sym2.rel_iff',Prod.mk.injEq,Prod.swap_prod_mk]
    intro h
    apply avoid
    rcases h with ⟨h,h'⟩ | ⟨h,h'⟩
    · exact Or.inl ⟨inj _ hi _ (by omega) h,inj _ hj _ (by omega) h'⟩
    · exact Or.inr ⟨inj _ hi _ (by omega) h,inj _ hj _ (by omega) h'⟩
  have step (i) (pos : 0 < i) (lim : i < r) : D.Adj (f i) (f (i+1)) :=
    adjD _ _ (by omega) (by omega) (by omega) (path i lim)
  apply ends.2.2
  by_cases first : ∀ i, l ≤ i → i ≤ m → f i ≠ z
  · apply (eqside _ _ ends.1 (first l le_rfl lm.le)
      (adjD 0 l (by omega) (by omega) (by omega) left)).trans
    exact interval_same f (· ∈ S) l m lm.le (fun t ht hm =>
      eqside _ _ (first _ ht (by omega)) (first _ (by omega) (by omega)) (step t (by omega) (by omega)))
  · push Not at first
    obtain ⟨i,hi,him,hz'⟩ := first
    have last (j) (hj : m ≤ j) (hjr : j ≤ r) : f j ≠ z := by
      intro e
      have := inj i (by omega) j hjr (hz'.trans e.symm)
      have : i = m := by omega
      exact ends.2.1 (this ▸ hz')
    apply (eqside _ _ ends.1 (last r mr.le le_rfl)
      (adjD 0 r (by omega) le_rfl (by omega) right)).trans
    exact (interval_same f (· ∈ S) m r mr.le (fun t ht hm =>
      eqside _ _ (last _ ht (by omega)) (last _ (by omega) (by omega)) (step t (by omega) hm))).symm

variable [Fintype V]

/-- Three neighbours of the starting vertex on a longest path yield an interior
chord with disjoint bypasses. The endpoint degrees are measured in the ambient
graph, whereas the neighbour count is measured within T. -/
lemma longest_endpoint (G : SimpleGraph V) [DecidableRel G.Adj]
    (cuts : (∀ (z : V) (S : Set V), z ∈ S → (∃ x ∈ S, x ≠ z) → (∃ y, y ∉ S) →
      ∃ x ∈ S, x ≠ z ∧ ∃ y ∉ S, (G).Adj x y))
    (minimal : ∀ a b, G.Adj a b → 3 < G.degree a → 3 < G.degree b → ¬ (∀ (z : V) (S : Set V), z ∈ S → (∃ x ∈ S, x ≠ z) → (∃ y, y ∉ S) →
      ∃ x ∈ S, x ≠ z ∧ ∃ y ∉ S, (G.deleteEdges {s(a,b)}).Adj x y))
    (T : Finset V) (high : ∀ x ∈ T, 3 < G.degree x) (u v : T)
    (p : (G.induce (T : Set V)).Walk u v) (hp : p.IsPath)
    (longest : ∀ (x y : T) (q : (G.induce (T : Set V)).Walk x y), q.IsPath → q.length ≤ p.length) :
    (T.filter (G.Adj u.val)).card ≤ 2 := by
  classical
  by_contra! three
  let H := G.induce (T : Set V)
  let f := fun i => (p.getVert i).val
  have inj (i) (hi : i ≤ p.length) (j) (hj : j ≤ p.length) (e : f i = f j) : i = j :=
    hp.getVert_injOn hi hj (Subtype.ext e)
  let I := (Finset.Icc 1 p.length).filter (fun i => G.Adj (f 0) (f i))
  have positions (y) (hy : y ∈ T.filter (G.Adj u.val)) :
      ∃ i ∈ I, f i = y := by
    obtain ⟨ys,uy⟩ := Finset.mem_filter.mp hy
    let w : T := ⟨y,ys⟩
    have ew : H.Adj u w := uy
    have inpath : w ∈ p.support := by
      by_contra hn
      have h := longest w v (.cons ew.symm p) (hp.cons hn)
      exact Nat.not_succ_le_self p.length h
    obtain ⟨i,hi,hiw⟩ := List.mem_iff_getElem.mp inpath
    have il : i ≤ p.length := by rw [p.length_support] at hi; omega
    have hit : p.getVert i = w := (p.getVert_eq_support_getElem il).trans hiw
    have ip : 0 < i := by
      by_contra! h
      have : i = 0 := by omega
      rw [this] at hit
      simp only [Walk.getVert_zero] at hit
      exact ew.ne hit
    refine ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨ip,il⟩,?_⟩,congrArg Subtype.val hit⟩
    simpa [f,hit] using uy
  have icard : 3 ≤ I.card := by
    have hsub : T.filter (G.Adj u.val) ⊆ I.image f := fun y hy =>
      Finset.mem_image.mpr (positions _ hy)
    have lower : 3 ≤ (T.filter (G.Adj u.val)).card := by omega
    exact lower.trans ((Finset.card_le_card hsub).trans Finset.card_image_le)
  let atI (j : Fin 3) := I.orderEmbOfFin rfl ⟨j.val,lt_of_lt_of_le j.isLt icard⟩
  have atmem (j : Fin 3) : atI j ∈ I := I.orderEmbOfFin_mem rfl _
  have mono : StrictMono atI := fun i j hij => (I.orderEmbOfFin rfl).strictMono hij
  have bounds (j : Fin 3) := Finset.mem_Icc.mp (Finset.mem_filter.mp (atmem j)).1
  have spokes (j : Fin 3) := (Finset.mem_filter.mp (atmem j)).2
  apply minimal (f 0) (f (atI 1)) (spokes 1) (high _ (p.getVert 0).property)
    (high _ (p.getVert (atI 1)).property)
  apply chord_safe G cuts f (atI 0) (atI 1) (atI 2) (bounds 0).1
    (mono (show (0 : Fin 3) < 1 by decide)) (mono (show (1 : Fin 3) < 2 by decide))
  · intro i hi j hj
    exact inj _ (hi.trans (bounds 2).2) _ (hj.trans (bounds 2).2)
  · intro i hi
    exact p.adj_getVert_succ (hi.trans_le (bounds 2).2)
  · exact spokes 0
  · exact spokes 2

/-- A longest path with a positive length has two distinct eligible endpoints.
An edgeless subset permits any choice other than the protected vertex. -/
lemma peel_away (G : SimpleGraph V) [DecidableRel G.Adj]
    (cuts : (∀ (z : V) (S : Set V), z ∈ S → (∃ x ∈ S, x ≠ z) → (∃ y, y ∉ S) →
      ∃ x ∈ S, x ≠ z ∧ ∃ y ∉ S, (G).Adj x y))
    (minimal : ∀ a b, G.Adj a b → 3 < G.degree a → 3 < G.degree b → ¬ (∀ (z : V) (S : Set V), z ∈ S → (∃ x ∈ S, x ≠ z) → (∃ y, y ∉ S) →
      ∃ x ∈ S, x ≠ z ∧ ∃ y ∉ S, (G.deleteEdges {s(a,b)}).Adj x y)) :
    (∀ (T : Finset V) (r : V), (∃ x ∈ T, x ≠ r) → (∀ x ∈ T, 3 < G.degree x) →
      ∃ x ∈ T, x ≠ r ∧ (T.filter (G.Adj x)).card ≤ 2) := by
  classical
  intro T r other high
  obtain ⟨w, hw, wr⟩ := other
  let H := G.induce (T : Set V)
  have : Nonempty T := ⟨⟨w, hw⟩⟩
  by_cases edge : ∃ a b : T, H.Adj a b
  · obtain ⟨a, b, ab⟩ := edge
    obtain ⟨u, v, p, hp, longest⟩ := Walk.exists_isPath_forall_isPath_length_le_length H
    have ne : u ≠ v := by
      rintro rfl
      have bound := longest a b ab.toWalk ab.isPath_toWalk
      rw [(Walk.isPath_iff_nil.mp hp).length_eq_zero, ab.length_toWalk] at bound
      omega
    by_cases ur : u.val = r
    · have vr : v.val ≠ r := fun e => ne (Subtype.ext (ur.trans e.symm))
      refine ⟨v.val, v.property, vr, longest_endpoint G cuts minimal T high v u p.reverse hp.reverse ?_⟩
      intro x y q hq
      simpa using longest x y q hq
    · exact ⟨u.val, u.property, ur, longest_endpoint G cuts minimal T high u v p hp longest⟩
  · have empty : T.filter (G.Adj w) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      obtain ⟨xt, wx⟩ := Finset.mem_filter.mp hx
      exact edge ⟨⟨w, hw⟩, ⟨x, xt⟩, wx⟩
    exact ⟨w, hw, wr, by simp [empty]⟩

end

theorem descend (independent : H1) (separated : H2) (n : ℕ) :
    ∀ (V : Type) (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj],
    G.edgeFinset.card = n → 3 ≤ G.minDegree →
    (∀ (z : V) (S : Set V), z ∈ S → (∃ x ∈ S, x ≠ z) → (∃ y : V, y ∉ S) →
      ∃ x ∈ S, x ≠ z ∧ ∃ y ∉ S, G.Adj x y) →
    ∃ (k : ℕ) (v : V) (c : G.Walk v v), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2 ^ k := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V G finite dec size low block
    classical
    let B (D : SimpleGraph V) : Prop := (∀ (z : V) (S : Set V), z ∈ S → (∃ x ∈ S, x ≠ z) → (∃ y : V, y ∉ S) →
      ∃ x ∈ S, x ≠ z ∧ ∃ y ∉ S, D.Adj x y)
    by_cases prune : ∃ a b, G.Adj a b ∧ 3 < G.degree a ∧ 3 < G.degree b ∧
        B (G.deleteEdges {s(a, b)})
    · obtain ⟨a, b, ab, ha, hb, remains⟩ := prune
      let D := G.deleteEdges {s(a, b)}
      have : Nonempty V := ⟨a⟩
      have lowD : 3 ≤ D.minDegree :=
        D.le_minDegree_of_forall_le_degree 3 (delete_edge_degree G a b low ha hb)
      have erased : D.edgeFinset = G.edgeFinset.erase s(a, b) := by
        ext e
        simp [D, edgeSet_deleteEdges, and_comm]
      have lt : D.edgeFinset.card < n := by
        rw [← size, erased]
        exact Finset.card_erase_lt_of_mem (G.mem_edgeFinset.mpr ab)
      obtain ⟨k, v, c, hk, hc, len⟩ := ih _ lt V D rfl lowD remains
      let incl : D ≤ G := G.deleteEdges_le _
      exact ⟨k, v, c.mapLe incl, hk, hc.mapLe incl, by simpa using len⟩
    · by_cases high : ∃ a b, G.Adj a b ∧ 3 < G.degree a ∧ 3 < G.degree b
      · apply separated V G low block high (peel_away G block
          (fun a b ab ha hb survives => prune ⟨a, b, ab, ha, hb, survives⟩))
        intro a b ab ha hb
        exact critical_cut G a b block (fun survives => prune ⟨a, b, ab, ha, hb, survives⟩)
      · apply independent V G low block
        intro a b ab
        have da := low.trans (G.minDegree_le_degree a)
        have db := low.trans (G.minDegree_le_degree b)
        by_contra! both
        exact high ⟨a, b, ab, by omega, by omega⟩

theorem main : H1 → H2 → OMA.R_Erdos64_erdos_64_R3.H1 := by
  intro independent separated V G finite dec low block
  exact descend independent separated _ V G rfl low block

end OMA.R_Erdos64_erdos_64_R3_H1_R1
