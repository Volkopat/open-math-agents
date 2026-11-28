import OMAReductions.R_Erdos64_erdos_64_R1
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Data.Set.Card

-- Reduction Erdos64.erdos_64.R1.H2.R1 of step Erdos64.erdos_64.R1.H2
-- Credit: @LeonC2009

/-! Split step H2 of reduction R1 into the cubic case and the critical bridgeless non-cubic
case: no nonempty proper vertex set induces minimum degree three, no edge joins two vertices of
degree above three, and no edge is a bridge (such graphs are connected, so they are
2-edge-connected). Step H2 of R1 contains every graph obtained by gluing two copies of a cubic
graph at a vertex, so it already contains the whole cubic case; the critical class excludes such
glued graphs, since each copy induces a cubic subgraph. Both new hypotheses follow from the
parent step: the cubic case through the gluing, and the critical bridgeless class is a subclass
(a vertex without a cubic neighbour could be deleted, leaving minimum degree three on a proper
subset). The descent is on the cube of the number of vertices plus the number of edges: delete
an edge between two vertices of degree above three (as in reduction R1 by JamesSlash), pass to an
induced subgraph of minimum degree three, or, at a bridge, glue two copies of its smaller side at
the end of the bridge; every cycle of the glued graph lies in one copy, so a cycle of length a
power of two in it gives one in the original graph. -/

namespace OMA.R_Erdos64_erdos_64_R1_H2_R1

open SimpleGraph

-- The cubic case (the same statement as step H1 of reduction R1).
def H1 : Prop :=
  ∀ (V : Type) (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj],
    Nonempty V → (∀ v, G.degree v = 3) →
    ∃ (k : ℕ) (v : V) (c : G.Walk v v), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2 ^ k

-- The critical bridgeless non-cubic case: some vertex has degree above three, every edge has an
-- endpoint of degree three, no nonempty proper vertex set induces minimum degree at least three,
-- and no edge is a bridge.
def H2 : Prop :=
  ∀ (V : Type) (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj],
    3 ≤ G.minDegree → (∃ v, 3 < G.degree v) →
    (∀ ⦃a b⦄, G.Adj a b → G.degree a = 3 ∨ G.degree b = 3) →
    (∀ S : Set V, S.Nonempty → S ≠ Set.univ → ∃ v ∈ S, (G.neighborSet v ∩ S).ncard < 3) →
    (∀ ⦃a b⦄, G.Adj a b → ¬ G.IsBridge s(a, b)) →
    ∃ (k : ℕ) (v : V) (c : G.Walk v v), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2 ^ k

/-! ### Two copies of one side of a bridge, glued at its end

Vertices `none` (standing for `a`) and `some (c, t)` (standing for `f t` in copy `c`). `K` is any
graph on these vertices in which two vertices are adjacent when their projections are adjacent
in `G` and they do not lie in different copies. The construction follows `research/oma-r1-glue`
(gluing two copies at a vertex), restated without definitions. -/

theorem glue_map_eq {V T : Type} (G : SimpleGraph V) (a : V) (f : T → V)
    (K : SimpleGraph (Option (Bool × T)))
    (hK : ∀ p q, K.Adj p q ↔ G.Adj (p.elim a (fun r => f r.2)) (q.elim a (fun r => f r.2)) ∧
      ∀ p' q', p = some p' → q = some q' → p'.1 = q'.1)
    {u v : Option (Bool × T)} (h : K.Adj u v) (hu : u ≠ none) (hv : v ≠ none) :
    u.map Prod.fst = v.map Prod.fst := by
  rcases u with _ | p
  · exact absurd rfl hu
  rcases v with _ | q
  · exact absurd rfl hv
  simp [((hK _ _).mp h).2 p q rfl rfl]

/-- A walk avoiding `none` stays in one copy. -/
theorem glue_support_of_none_notMem {V T : Type} (G : SimpleGraph V) (a : V) (f : T → V)
    (K : SimpleGraph (Option (Bool × T)))
    (hK : ∀ p q, K.Adj p q ↔ G.Adj (p.elim a (fun r => f r.2)) (q.elim a (fun r => f r.2)) ∧
      ∀ p' q', p = some p' → q = some q' → p'.1 = q'.1)
    {x y : Option (Bool × T)} (p : K.Walk x y) :
    none ∉ p.support → ∀ w ∈ p.support, w.map Prod.fst = x.map Prod.fst := by
  induction p with
  | nil =>
    intro _ w hw
    rw [Walk.support_nil, List.mem_singleton] at hw
    rw [hw]
  | @cons u v w h p ih =>
    intro hnone z hz
    rw [Walk.support_cons, List.mem_cons, not_or] at hnone
    rw [Walk.support_cons, List.mem_cons] at hz
    rcases hz with hz | hz
    · rw [hz]
    · have hvne : v ≠ none := fun e => hnone.2 (e ▸ p.start_mem_support)
      have hune : u ≠ none := fun e => hnone.1 e.symm
      rw [ih hnone.2 z hz]
      exact (glue_map_eq G a f K hK h hune hvne).symm

/-- A path ending at `none` and starting elsewhere stays, apart from `none`, in the copy of
its first vertex. -/
theorem glue_support_of_path_to_none {V T : Type} (G : SimpleGraph V) (a : V) (f : T → V)
    (K : SimpleGraph (Option (Bool × T)))
    (hK : ∀ p q, K.Adj p q ↔ G.Adj (p.elim a (fun r => f r.2)) (q.elim a (fun r => f r.2)) ∧
      ∀ p' q', p = some p' → q = some q' → p'.1 = q'.1)
    {x y : Option (Bool × T)} (p : K.Walk x y) :
    p.IsPath → y = none → x ≠ none →
      ∀ w ∈ p.support, w = none ∨ w.map Prod.fst = x.map Prod.fst := by
  induction p with
  | nil =>
    intro _ hc hx
    exact absurd hc hx
  | @cons u v w h p ih =>
    intro hpath hc hu z hz
    rw [Walk.cons_isPath_iff] at hpath
    rw [Walk.support_cons, List.mem_cons] at hz
    rcases hz with hz | hz
    · right
      rw [hz]
    · by_cases hv : v = none
      · subst hv
        subst hc
        have hnil : p = Walk.nil := Walk.eq_nil_iff_nil.mpr (Walk.isPath_iff_nil.mp hpath.1)
        subst hnil
        rw [Walk.support_nil, List.mem_singleton] at hz
        left
        exact hz
      · rcases ih hpath.1 hc hv z hz with h1 | h1
        · left
          exact h1
        · right
          rw [h1]
          exact (glue_map_eq G a f K hK h hu hv).symm

/-- A cycle through `none` lies in one copy together with `none`. -/
theorem glue_side_of_cycle_at_none {V T : Type} (G : SimpleGraph V) (a : V) (f : T → V)
    (K : SimpleGraph (Option (Bool × T)))
    (hK : ∀ p q, K.Adj p q ↔ G.Adj (p.elim a (fun r => f r.2)) (q.elim a (fun r => f r.2)) ∧
      ∀ p' q', p = some p' → q = some q' → p'.1 = q'.1)
    (c : K.Walk none none) (hc : c.IsCycle) :
    ∃ b : Bool, ∀ w ∈ c.support, w = none ∨ w.map Prod.fst = some b := by
  cases c with
  | nil => exact absurd hc Walk.not_isCycle_nil
  | @cons _ a1 _ h p =>
    rw [Walk.cons_isCycle_iff] at hc
    have ha1 : a1 ≠ none := by
      rintro rfl
      exact K.irrefl h
    obtain ⟨b, hb⟩ : ∃ b, a1.map Prod.fst = some b := by
      rcases a1 with _ | ⟨b, x⟩
      · exact absurd rfl ha1
      · exact ⟨b, rfl⟩
    refine ⟨b, fun w hw => ?_⟩
    rw [Walk.support_cons, List.mem_cons] at hw
    rcases hw with hw | hw
    · left
      exact hw
    · rcases glue_support_of_path_to_none G a f K hK p hc.1 rfl ha1 w hw with h1 | h1
      · left
        exact h1
      · right
        rw [h1, hb]

theorem glue_length_induce {T : Type} (K : SimpleGraph (Option (Bool × T)))
    {s : Set (Option (Bool × T))} {u v : Option (Bool × T)}
    (w : K.Walk u v) (hw : ∀ x ∈ w.support, x ∈ s) : (w.induce s hw).length = w.length := by
  induction w with
  | nil => rfl
  | cons h p ih => simp [Walk.induce_cons, ih]

/-- Every cycle of `K` gives a cycle of `G` of the same length. -/
theorem glue_cycle_transfer {V T : Type} (G : SimpleGraph V) (a : V) (f : T → V)
    (K : SimpleGraph (Option (Bool × T)))
    (hK : ∀ p q, K.Adj p q ↔ G.Adj (p.elim a (fun r => f r.2)) (q.elim a (fun r => f r.2)) ∧
      ∀ p' q', p = some p' → q = some q' → p'.1 = q'.1)
    (hf : Function.Injective f) (hfa : ∀ t, f t ≠ a)
    {x : Option (Bool × T)} (c : K.Walk x x) (hc : c.IsCycle) :
    ∃ (v : V) (c' : G.Walk v v), c'.IsCycle ∧ c'.length = c.length := by
  classical
  have key : ∃ (b : Bool) (x' : Option (Bool × T)) (c1 : K.Walk x' x'),
      c1.IsCycle ∧ c1.length = c.length ∧
        ∀ w ∈ c1.support, w ∈ {w : Option (Bool × T) | w = none ∨ w.map Prod.fst = some b} := by
    by_cases hn : none ∈ c.support
    · obtain ⟨b, hb⟩ := glue_side_of_cycle_at_none G a f K hK (c.rotate none hn) (hc.rotate hn)
      exact ⟨b, none, c.rotate none hn, hc.rotate hn, Walk.length_rotate _ _ _, hb⟩
    · have hx : x ≠ none := fun e => hn (e ▸ c.start_mem_support)
      obtain ⟨b, hb⟩ : ∃ b, x.map Prod.fst = some b := by
        rcases x with _ | ⟨b, t⟩
        · exact absurd rfl hx
        · exact ⟨b, rfl⟩
      refine ⟨b, x, c, hc, rfl, fun w hw => Or.inr ?_⟩
      rw [glue_support_of_none_notMem G a f K hK c hn w hw, hb]
  obtain ⟨b, x', c1, hc1, hlen, hsub⟩ := key
  let S : Set (Option (Bool × T)) := {w | w = none ∨ w.map Prod.fst = some b}
  let c2 := c1.induce S hsub
  have hc2 : c2.IsCycle := by
    apply Walk.IsCycle.of_map (f := (Embedding.induce _).toHom)
    rw [Walk.map_induce]
    exact hc1
  have hl2 : c2.length = c1.length := glue_length_induce K c1 hsub
  let φ : K.induce S →g G :=
    { toFun := fun w => w.1.elim a (fun r => f r.2)
      map_rel' := fun h => ((hK _ _).mp (induce_adj.mp h)).1 }
  have hφ : Function.Injective φ := by
    rintro ⟨w1, h1⟩ ⟨w2, h2⟩ he
    apply Subtype.ext
    change w1.elim a (fun r => f r.2) = w2.elim a (fun r => f r.2) at he
    rcases w1 with _ | ⟨b1, t1⟩ <;> rcases w2 with _ | ⟨b2, t2⟩
    · rfl
    · exact (hfa t2 he.symm).elim
    · exact (hfa t1 he).elim
    · simp only [S, Set.mem_ofPred_eq, reduceCtorEq, Option.map_some, Option.some.injEq,
        false_or] at h1 h2
      simp only [Option.elim_some] at he
      show some (b1, t1) = some (b2, t2)
      rw [h1, h2, hf he]
  exact ⟨_, c2.map φ, hc2.map hφ, by rw [Walk.length_map, hl2, hlen]⟩

/-- A copy vertex has at least the degree of the vertex it copies, provided every neighbour of
that vertex is `a` or in the range of `f`. -/
theorem glue_degree_some {V T : Type} (G : SimpleGraph V) (a : V) (f : T → V)
    (K : SimpleGraph (Option (Bool × T)))
    (hK : ∀ p q, K.Adj p q ↔ G.Adj (p.elim a (fun r => f r.2)) (q.elim a (fun r => f r.2)) ∧
      ∀ p' q', p = some p' → q = some q' → p'.1 = q'.1)
    [Fintype V] [DecidableRel G.Adj] [Fintype (Option (Bool × T))]
    [DecidableRel K.Adj]
    (hclosed : ∀ t y, G.Adj (f t) y → y = a ∨ ∃ t', f t' = y) (b : Bool) (t : T) :
    G.degree (f t) ≤ K.degree (some (b, t)) := by
  classical
  rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree]
  let g : V → Option (Bool × T) := fun y =>
    if h : ∃ t', f t' = y then some (b, h.choose) else none
  refine Finset.card_le_card_of_injOn g ?_ ?_
  · intro y hy
    rw [Finset.mem_coe, mem_neighborFinset] at hy
    rw [Finset.mem_coe, mem_neighborFinset, hK]
    by_cases h : ∃ t', f t' = y
    · have hg : g y = some (b, h.choose) := dif_pos h
      rw [hg]
      refine ⟨?_, fun p' q' e1 e2 => ?_⟩
      · simp only [Option.elim_some]
        rw [h.choose_spec]
        exact hy
      · cases e1
        cases e2
        rfl
    · have hg : g y = none := dif_neg h
      rw [hg]
      rcases hclosed t y hy with e | e
      · refine ⟨?_, fun p' q' _ e2 => absurd e2 (by simp)⟩
        simp only [Option.elim_some, Option.elim_none]
        rw [← e]
        exact hy
      · exact absurd e h
  · intro y1 hy1 y2 hy2 he
    rw [Finset.mem_coe, mem_neighborFinset] at hy1 hy2
    by_cases h1 : ∃ t', f t' = y1 <;> by_cases h2 : ∃ t', f t' = y2
    · have e1 : g y1 = some (b, h1.choose) := dif_pos h1
      have e2 : g y2 = some (b, h2.choose) := dif_pos h2
      rw [e1, e2] at he
      simp only [Option.some.injEq, Prod.mk.injEq, true_and] at he
      rw [← h1.choose_spec, ← h2.choose_spec, he]
    · have e1 : g y1 = some (b, h1.choose) := dif_pos h1
      have e2 : g y2 = none := dif_neg h2
      rw [e1, e2] at he
      exact absurd he (by simp)
    · have e1 : g y1 = none := dif_neg h1
      have e2 : g y2 = some (b, h2.choose) := dif_pos h2
      rw [e1, e2] at he
      exact absurd he (by simp)
    · rcases hclosed t y1 hy1 with e1 | e1
      · rcases hclosed t y2 hy2 with e2 | e2
        · rw [e1, e2]
        · exact absurd e2 h2
      · exact absurd e1 h1

/-- The glued vertex has degree at least 4 when `a` has two neighbours in the range of `f`. -/
theorem glue_degree_none {V T : Type} (G : SimpleGraph V) (a : V) (f : T → V)
    (K : SimpleGraph (Option (Bool × T)))
    (hK : ∀ p q, K.Adj p q ↔ G.Adj (p.elim a (fun r => f r.2)) (q.elim a (fun r => f r.2)) ∧
      ∀ p' q', p = some p' → q = some q' → p'.1 = q'.1)
    [Fintype (Option (Bool × T))] [DecidableRel K.Adj]
    {t1 t2 : T} (h12 : t1 ≠ t2) (h1 : G.Adj a (f t1)) (h2 : G.Adj a (f t2)) :
    4 ≤ K.degree none := by
  classical
  have hsub : ({some (true, t1), some (true, t2), some (false, t1), some (false, t2)} :
      Finset (Option (Bool × T))) ⊆ K.neighborFinset none := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rw [mem_neighborFinset, hK]
    rcases hw with rfl | rfl | rfl | rfl
    · exact ⟨h1, fun p' q' e _ => absurd e (by simp)⟩
    · exact ⟨h2, fun p' q' e _ => absurd e (by simp)⟩
    · exact ⟨h1, fun p' q' e _ => absurd e (by simp)⟩
    · exact ⟨h2, fun p' q' e _ => absurd e (by simp)⟩
  have hcard := Finset.card_le_card hsub
  rw [card_neighborFinset_eq_degree] at hcard
  rw [Finset.card_insert_of_notMem (by simp [h12]), Finset.card_insert_of_notMem (by simp),
    Finset.card_insert_of_notMem (by simp [h12]), Finset.card_singleton] at hcard
  exact hcard


/-- **Bridge gluing.** If `ab` is a bridge of a graph with minimum degree at least 3, there is a
graph with fewer vertices and minimum degree at least 3 whose cycles all map to cycles of the
same length in the original graph: two copies of the side of `a` glued at `a`, where the side of
`a` is chosen to be the smaller one. -/
theorem bridge_glue_side {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (minimum : 3 ≤ G.minDegree) {a b : V} (hab : G.Adj a b)
    (hbr : ¬ (G.deleteEdges {s(a, b)}).Reachable a b)
    (hside : Nat.card {x // (G.deleteEdges {s(a, b)}).Reachable a x} ≤
      Nat.card {x // (G.deleteEdges {s(a, b)}).Reachable b x}) :
    ∃ (W : Type) (_ : Fintype W) (K : SimpleGraph W) (_ : DecidableRel K.Adj),
      Fintype.card W < Fintype.card V ∧ 3 ≤ K.minDegree ∧
      ∀ (w : W) (c : K.Walk w w), c.IsCycle →
        ∃ (v : V) (c' : G.Walk v v), c'.IsCycle ∧ c'.length = c.length := by
  classical
  set H := G.deleteEdges {s(a, b)} with hH
  have hHadj : ∀ x y, H.Adj x y ↔ G.Adj x y ∧ ¬ (s(x, y) = s(a, b)) := by
    intro x y
    simp [H, deleteEdges_adj]
  let T := {x : V // H.Reachable a x ∧ x ≠ a}
  let f : T → V := Subtype.val
  have hf : Function.Injective f := Subtype.val_injective
  have hfa : ∀ t : T, f t ≠ a := fun t => t.2.2
  -- every neighbour of a vertex of `T` is `a` or in `T`
  have hclosed : ∀ t y, G.Adj (f t) y → y = a ∨ ∃ t', f t' = y := by
    intro t y hty
    by_cases hya : y = a
    · exact Or.inl hya
    right
    have hne : ¬ (s(f t, y) = s(a, b)) := by
      intro e
      rcases Sym2.eq_iff.mp e with ⟨e1, -⟩ | ⟨e1, -⟩
      · exact hfa t e1
      · exact hbr (e1 ▸ t.2.1)
    have hHty : H.Adj (f t) y := (hHadj _ _).mpr ⟨hty, hne⟩
    exact ⟨⟨y, t.2.1.trans hHty.reachable, hya⟩, rfl⟩
  -- `a` has two neighbours in `T`
  have hdeg_a : 3 ≤ G.degree a := minimum.trans (G.minDegree_le_degree a)
  obtain ⟨y1, y2, h12, hy1, hy2, hy1b, hy2b⟩ :
      ∃ y1 y2, y1 ≠ y2 ∧ G.Adj a y1 ∧ G.Adj a y2 ∧ y1 ≠ b ∧ y2 ≠ b := by
    have hc : 2 ≤ ((G.neighborFinset a).erase b).card := by
      have := Finset.pred_card_le_card_erase (s := G.neighborFinset a) (a := b)
      rw [card_neighborFinset_eq_degree] at this
      omega
    obtain ⟨y1, h1, y2, h2, h12⟩ :=
      Finset.one_lt_card.mp (show 1 < ((G.neighborFinset a).erase b).card by omega)
    rw [Finset.mem_erase, mem_neighborFinset] at h1 h2
    exact ⟨y1, y2, h12, h1.2, h2.2, h1.1, h2.1⟩
  have reach : ∀ y, G.Adj a y → y ≠ b → H.Reachable a y := by
    intro y hy hyb
    refine ((hHadj _ _).mpr ⟨hy, fun e => ?_⟩).reachable
    rcases Sym2.eq_iff.mp e with ⟨-, e2⟩ | ⟨e1, -⟩
    · exact hyb e2
    · exact G.ne_of_adj hab e1
  let t1 : T := ⟨y1, reach y1 hy1 hy1b, (G.ne_of_adj hy1).symm⟩
  let t2 : T := ⟨y2, reach y2 hy2 hy2b, (G.ne_of_adj hy2).symm⟩
  have ht12 : t1 ≠ t2 := fun e => h12 (congrArg Subtype.val e)
  -- the glued graph
  let K : SimpleGraph (Option (Bool × T)) :=
    { Adj := fun p q => G.Adj (p.elim a (fun r => f r.2)) (q.elim a (fun r => f r.2)) ∧
        ∀ p' q', p = some p' → q = some q' → p'.1 = q'.1
      symm := ⟨fun p q h => ⟨h.1.symm, fun p' q' e1 e2 => (h.2 q' p' e2 e1).symm⟩⟩
      loopless := ⟨fun p h => G.irrefl h.1⟩ }
  have hK : ∀ p q, K.Adj p q ↔ G.Adj (p.elim a (fun r => f r.2)) (q.elim a (fun r => f r.2)) ∧
      ∀ p' q', p = some p' → q = some q' → p'.1 = q'.1 := fun _ _ => Iff.rfl
  refine ⟨Option (Bool × T), inferInstance, K, inferInstance, ?_, ?_, ?_⟩
  · -- vertex count: 2 |T| + 1 < |V|
    have hX : Fintype.card {x // H.Reachable a x} = Fintype.card T + 1 := by
      have e : {x // H.Reachable a x} ≃ Option T :=
        { toFun := fun x => if h : x.1 = a then none else some ⟨x.1, x.2, h⟩
          invFun := fun o => o.elim ⟨a, Reachable.refl a⟩ (fun t => ⟨t.1, t.2.1⟩)
          left_inv := by
            rintro ⟨x, hx⟩
            by_cases h : x = a
            · subst h
              simp
            · simp [h]
          right_inv := by
            rintro (_ | ⟨x, hx, hxa⟩)
            · simp
            · simp [hxa] }
      rw [Fintype.card_congr e, Fintype.card_option]
    have hdisj : Fintype.card {x // H.Reachable a x} + Fintype.card {x // H.Reachable b x} ≤
        Fintype.card V := by
      rw [← Fintype.card_sum]
      refine Fintype.card_le_of_injective
        (fun s => Sum.elim (fun x => x.1) (fun x => x.1) s) ?_
      rintro (⟨x, hx⟩ | ⟨x, hx⟩) (⟨y, hy⟩ | ⟨y, hy⟩) he <;> simp only [Sum.elim_inl,
        Sum.elim_inr] at he
      · subst he
        rfl
      · subst he
        exact absurd (hx.trans hy.symm) hbr
      · subst he
        exact absurd (hy.trans hx.symm) hbr
      · subst he
        rfl
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at hside
    rw [Fintype.card_option, Fintype.card_prod, Fintype.card_bool]
    omega
  · -- minimum degree
    apply K.le_minDegree_of_forall_le_degree
    rintro (_ | ⟨c, t⟩)
    · exact (by omega : 3 ≤ 4).trans (glue_degree_none G a f K hK ht12 hy1 hy2)
    · have h3 : 3 ≤ G.degree (f t) := minimum.trans (G.minDegree_le_degree _)
      exact h3.trans (glue_degree_some G a f K hK hclosed c t)
  · intro w c hc
    exact glue_cycle_transfer G a f K hK hf hfa c hc

/-- Bridge gluing, either side. -/
theorem bridge_glue {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (minimum : 3 ≤ G.minDegree) {a b : V} (hab : G.Adj a b) (hbr : G.IsBridge s(a, b)) :
    ∃ (W : Type) (_ : Fintype W) (K : SimpleGraph W) (_ : DecidableRel K.Adj),
      Fintype.card W < Fintype.card V ∧ 3 ≤ K.minDegree ∧
      ∀ (w : W) (c : K.Walk w w), c.IsCycle →
        ∃ (v : V) (c' : G.Walk v v), c'.IsCycle ∧ c'.length = c.length := by
  classical
  rw [isBridge_iff] at hbr
  rcases le_total (Nat.card {x // (G.deleteEdges {s(a, b)}).Reachable a x})
      (Nat.card {x // (G.deleteEdges {s(a, b)}).Reachable b x}) with h | h
  · exact bridge_glue_side G minimum hab hbr h
  · have e : s(b, a) = s(a, b) := Sym2.eq_swap
    have hbr' : ¬ (G.deleteEdges {s(b, a)}).Reachable b a := by
      rw [e]
      exact fun h' => hbr h'.symm
    have h' : Nat.card {x // (G.deleteEdges {s(b, a)}).Reachable b x} ≤
        Nat.card {x // (G.deleteEdges {s(b, a)}).Reachable a x} := by
      rw [e]
      exact h
    exact bridge_glue_side G minimum hab.symm hbr' h'

theorem nonempty_of_three_le_minDegree {V : Type} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (minimum : 3 ≤ G.minDegree) : Nonempty V := by
  rcases isEmpty_or_nonempty V with hv | hv
  · have hz := G.minDegree_of_subsingleton
    omega
  · exact hv

theorem three_le_degree_delete {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (a b : V) (minimum : 3 ≤ G.minDegree)
    (ha : 3 < G.degree a) (hb : 3 < G.degree b) (x : V) :
    3 ≤ (G.deleteEdges {s(a, b)}).degree x := by
  let H := G.deleteEdges {s(a, b)}
  change 3 ≤ H.degree x
  have adjH : ∀ y, G.Adj x y → ¬ (x = a ∧ y = b) → ¬ (x = b ∧ y = a) → H.Adj x y := by
    intro y hxy h1 h2
    refine deleteEdges_adj.mpr ⟨hxy, ?_⟩
    rw [Set.mem_singleton_iff, Sym2.eq_iff]
    rintro (h | h)
    · exact h1 h
    · exact h2 h
  by_cases hxa : x = a
  · have sub : (G.neighborFinset x).erase b ⊆ H.neighborFinset x := by
      intro y hy
      rw [Finset.mem_erase, mem_neighborFinset] at hy
      rw [mem_neighborFinset]
      exact adjH y hy.2 (fun h => hy.1 h.2) (fun h => hy.2.ne (h.2.trans hxa.symm).symm)
    have c := Finset.card_le_card sub
    have e := Finset.pred_card_le_card_erase (s := G.neighborFinset x) (a := b)
    rw [card_neighborFinset_eq_degree] at c e
    have hx : 3 < G.degree x := hxa ▸ ha
    omega
  · by_cases hxb : x = b
    · have sub : (G.neighborFinset x).erase a ⊆ H.neighborFinset x := by
        intro y hy
        rw [Finset.mem_erase, mem_neighborFinset] at hy
        rw [mem_neighborFinset]
        exact adjH y hy.2 (fun h => hy.2.ne (h.2.trans hxb.symm).symm) (fun h => hy.1 h.2)
      have c := Finset.card_le_card sub
      have e := Finset.pred_card_le_card_erase (s := G.neighborFinset x) (a := a)
      rw [card_neighborFinset_eq_degree] at c e
      have hx : 3 < G.degree x := hxb ▸ hb
      omega
    · have same : H.neighborFinset x = G.neighborFinset x := by
        ext y
        rw [mem_neighborFinset, mem_neighborFinset]
        constructor
        · exact fun h => (deleteEdges_adj.mp h).1
        · exact fun h => adjH y h (fun h' => hxa h'.1) (fun h' => hxb h'.1)
      rw [← card_neighborFinset_eq_degree, same, card_neighborFinset_eq_degree]
      exact minimum.trans (G.minDegree_le_degree x)

theorem degree_induce_eq_ncard {V : Type} (G : SimpleGraph V) (S : Set V) (v : S)
    [Fintype ((G.induce S).neighborSet v)] :
    (G.induce S).degree v = (G.neighborSet v ∩ S).ncard := by
  rw [← card_neighborSet_eq_degree, Fintype.card_eq_nat_card, ← Nat.card_coe_set_eq]
  exact Nat.card_congr
    { toFun := fun w => ⟨w.1.1, Set.mem_inter (show G.Adj v.1 w.1.1 from w.2) w.1.2⟩
      invFun := fun y => ⟨⟨y.1, ((Set.mem_inter_iff _ _ _).mp y.2).2⟩,
        show G.Adj v.1 y.1 from ((Set.mem_inter_iff _ _ _).mp y.2).1⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem solve (cubic : H1) (critical : H2) (n : ℕ) :
    ∀ (V : Type) (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj],
      Fintype.card V ^ 3 + G.edgeFinset.card = n → 3 ≤ G.minDegree →
      ∃ (k : ℕ) (v : V) (c : G.Walk v v), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2 ^ k := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V G finite dec measure minimum
    classical
    have : Nonempty V := nonempty_of_three_le_minDegree G minimum
    by_cases uniform : ∀ v, G.degree v = 3
    · exact cubic V G inferInstance uniform
    have big : ∃ v, 3 < G.degree v := by
      rw [not_forall] at uniform
      obtain ⟨v, hv⟩ := uniform
      have lower := minimum.trans (G.minDegree_le_degree v)
      exact ⟨v, by omega⟩
    by_cases edges : ∀ ⦃a b⦄, G.Adj a b → G.degree a = 3 ∨ G.degree b = 3
    · by_cases sets : ∀ S : Set V, S.Nonempty → S ≠ Set.univ →
          ∃ v ∈ S, (G.neighborSet v ∩ S).ncard < 3
      · by_cases nobridge : ∀ ⦃a b⦄, G.Adj a b → ¬ G.IsBridge s(a, b)
        · exact critical V G minimum big edges sets nobridge
        · push Not at nobridge
          obtain ⟨a, b, hab, hbr⟩ := nobridge
          obtain ⟨W, hWf, K, hKd, hW, hK, transfer⟩ := bridge_glue G minimum hab hbr
          have hE : K.edgeFinset.card ≤ Fintype.card W ^ 2 :=
            K.card_edgeFinset_le_card_choose_two.trans (Nat.choose_le_pow _ _)
          have hcube : Fintype.card W ^ 3 + Fintype.card W ^ 2 < Fintype.card V ^ 3 := by
            have h2 : Fintype.card W ^ 2 < Fintype.card V ^ 2 := Nat.pow_lt_pow_left hW two_ne_zero
            have hv : 0 < Fintype.card V := by omega
            calc Fintype.card W ^ 3 + Fintype.card W ^ 2
                = Fintype.card W ^ 2 * (Fintype.card W + 1) := by ring
              _ ≤ Fintype.card W ^ 2 * Fintype.card V := Nat.mul_le_mul_left _ hW
              _ < Fintype.card V ^ 2 * Fintype.card V := Nat.mul_lt_mul_of_pos_right h2 hv
              _ = Fintype.card V ^ 3 := by ring
          have smaller : Fintype.card W ^ 3 + K.edgeFinset.card < n := by omega
          obtain ⟨k, v, c, hk, hc, hl⟩ := ih _ smaller W K rfl hK
          obtain ⟨v', c', hc', hl'⟩ := transfer v c hc
          exact ⟨k, v', c', hk, hc', hl'.trans hl⟩
      · push Not at sets
        obtain ⟨S, hne, hproper, hdeg⟩ := sets
        let H := G.induce S
        have minimumH : 3 ≤ H.minDegree := by
          obtain ⟨w, hw⟩ := hne
          have : Nonempty S := ⟨⟨w, hw⟩⟩
          apply H.le_minDegree_of_forall_le_degree
          intro x
          rw [degree_induce_eq_ncard G S x]
          exact hdeg x.1 x.2
        obtain ⟨a, ha⟩ : ∃ a, a ∉ S := by
          by_contra hall
          push Not at hall
          exact hproper (Set.eq_univ_of_forall hall)
        have hv : Fintype.card S < Fintype.card V :=
          Fintype.card_lt_of_injective_of_notMem Subtype.val Subtype.val_injective
            (b := a) (fun ⟨x, eq⟩ => ha (eq ▸ x.property))
        have he : H.edgeFinset.card ≤ G.edgeFinset.card := by
          have mapped := SimpleGraph.map_edgeFinset_induce (s := S) (G := G)
          rw [← Finset.card_map (f := (Function.Embedding.subtype (· ∈ S)).sym2Map), mapped]
          exact Finset.card_le_card Finset.inter_subset_left
        have hv3 : Fintype.card S ^ 3 < Fintype.card V ^ 3 := Nat.pow_lt_pow_left hv (by norm_num)
        have smaller : Fintype.card S ^ 3 + H.edgeFinset.card < n := by omega
        obtain ⟨k, v, c, hk, hc, hl⟩ := ih _ smaller S H rfl minimumH
        let lift : H →g G := ⟨Subtype.val, fun h => h⟩
        exact ⟨k, v.val, c.map lift, hk, hc.map Subtype.val_injective, by simpa using hl⟩
    · push Not at edges
      obtain ⟨a, b, hadj, ha, hb⟩ := edges
      have hda := minimum.trans (G.minDegree_le_degree a)
      have hdb := minimum.trans (G.minDegree_le_degree b)
      let H := G.deleteEdges {s(a, b)}
      have minimumH : 3 ≤ H.minDegree :=
        H.le_minDegree_of_forall_le_degree 3
          (three_le_degree_delete G a b minimum (by omega) (by omega))
      have reduced : H.edgeFinset = G.edgeFinset.erase s(a, b) := by
        ext e
        simp [H, edgeSet_deleteEdges, and_comm]
      have edgeOf : s(a, b) ∈ G.edgeFinset := G.mem_edgeFinset.mpr hadj
      have strict : H.edgeFinset.card < G.edgeFinset.card := by
        rw [reduced]
        exact Finset.card_erase_lt_of_mem edgeOf
      have smaller : Fintype.card V ^ 3 + H.edgeFinset.card < n := by omega
      obtain ⟨k, v, c, hk, hc, hl⟩ := ih _ smaller V H rfl minimumH
      let leG : H ≤ G := G.deleteEdges_le _
      exact ⟨k, v, c.mapLe leG, hk, hc.mapLe leG, by simpa using hl⟩

theorem main : H1 → H2 → OMA.R_Erdos64_erdos_64_R1.H2 := by
  intro cubic critical V G finite dec minimum _ _ _
  exact solve cubic critical _ V G rfl minimum

end OMA.R_Erdos64_erdos_64_R1_H2_R1
