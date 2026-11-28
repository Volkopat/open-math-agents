import OMAReductions.R_Erdos64_erdos_64_R3
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod
import Mathlib.Logic.Equiv.Option
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Combinatorics.SimpleGraph.Maps

-- Reduction Erdos64.erdos_64.R3.H2.R3 of step Erdos64.erdos_64.R3.H2
-- Credit: @LeonC2009

/-! Split step R3.H2 (2-connected, exactly one vertex r of degree 2, all others of degree at
least 3) by parity on two-terminal pieces. A two-terminal piece is a vertex set S avoiding r whose
only vertices with neighbours outside S are two vertices u, v, each with at least two neighbours
in S. If all u-v paths inside some piece have the same parity, take two copies of the subgraph
induced on S, identify the two copies of u and join the two copies of v by a new edge. The glued
graph has minimum degree at least 3 and is 2-connected in the sense of the separation hypothesis
of R3, so step R3.H1 gives it a cycle of length a power of two. A cycle avoiding the new edge lies
in one copy, so it is a cycle of G. A cycle through the new edge consists of two u-v paths of the
same parity plus one edge, so its length is odd, which is impossible. Otherwise every piece has
u-v paths of both parities; for the piece of all vertices but r (terminals the two neighbours of r)
this means cycles through r of both parities. So the hypotheses are R3.H1 and R3.H2 restricted to
graphs with cycles through r of both parities in which every piece has paths of both parities. -/

namespace OMA.R_Erdos64_erdos_64_R3_H2_R3

open SimpleGraph

/-- Step `Erdos64.erdos_64.R3.H1`, verbatim. -/
def H1 : Prop :=
  ∀ (V : Type) (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj],
    3 ≤ G.minDegree →
    (∀ (a : V) (S : Set V), a ∈ S → (∃ x ∈ S, x ≠ a) → (∃ y : V, y ∉ S) →
      ∃ x ∈ S, x ≠ a ∧ ∃ y ∉ S, G.Adj x y) →
    ∃ (k : ℕ) (v : V) (c : G.Walk v v), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2 ^ k

/-- Step `Erdos64.erdos_64.R3.H2` restricted to graphs with cycles through `r` of both
parities in which, moreover, every two-terminal piece avoiding `r` (a finset `S ∌ r` whose only
vertices with neighbours outside it are `u ≠ v`, each with at least two neighbours in `S`) has
`u`–`v` paths inside `S` of both parities. -/
def H2 : Prop :=
  ∀ (V : Type) (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj] (r : V),
    G.degree r = 2 → (∀ x, x ≠ r → 3 ≤ G.degree x) →
    (∀ (a : V) (S : Set V), a ∈ S → (∃ x ∈ S, x ≠ a) → (∃ y : V, y ∉ S) →
      ∃ x ∈ S, x ≠ a ∧ ∃ y ∉ S, G.Adj x y) →
    (∃ (c₁ c₂ : G.Walk r r), c₁.IsCycle ∧ c₂.IsCycle ∧ c₁.length % 2 ≠ c₂.length % 2) →
    (∀ (S : Finset V) (u v : V), r ∉ S → u ∈ S → v ∈ S → u ≠ v →
      (∀ a ∈ S, ∀ b, b ∉ S → G.Adj a b → a = u ∨ a = v) →
      2 ≤ (S.filter (G.Adj u)).card → 2 ≤ (S.filter (G.Adj v)).card →
      ∃ (p q : G.Walk u v), p.IsPath ∧ q.IsPath ∧ (∀ z ∈ p.support, z ∈ S) ∧
        (∀ z ∈ q.support, z ∈ S) ∧ p.length % 2 ≠ q.length % 2) →
    ∃ (k : ℕ) (v : V) (c : G.Walk v v), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2 ^ k

/- ### Two copies glued at one vertex (from R1.H2.R1) -/

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

/-- The projection of one copy together with the glued vertex is an injective homomorphism. -/
theorem glue_hom {V T : Type} (G : SimpleGraph V) (a : V) (f : T → V)
    (K : SimpleGraph (Option (Bool × T)))
    (hK : ∀ p q, K.Adj p q ↔ G.Adj (p.elim a (fun r => f r.2)) (q.elim a (fun r => f r.2)) ∧
      ∀ p' q', p = some p' → q = some q' → p'.1 = q'.1)
    (hf : Function.Injective f) (hfa : ∀ t, f t ≠ a) (b : Bool) :
    ∃ φ : K.induce {w : Option (Bool × T) | w = none ∨ w.map Prod.fst = some b} →g G,
      Function.Injective φ ∧ ∀ w, φ w = w.1.elim a (fun r => f r.2) := by
  let S : Set (Option (Bool × T)) := {w | w = none ∨ w.map Prod.fst = some b}
  let φ : K.induce S →g G :=
    { toFun := fun w => w.1.elim a (fun r => f r.2)
      map_rel' := fun h => ((hK _ _).mp (induce_adj.mp h)).1 }
  refine ⟨φ, ?_, fun _ => rfl⟩
  rintro ⟨w1, h1⟩ ⟨w2, h2⟩ he
  apply Subtype.ext
  change w1.elim a (fun r => f r.2) = w2.elim a (fun r => f r.2) at he
  rcases w1 with _ | ⟨b1, t1⟩ <;> rcases w2 with _ | ⟨b2, t2⟩
  · rfl
  · exact (hfa t2 he.symm).elim
  · exact (hfa t1 he).elim
  · simp only [Set.mem_ofPred_eq, reduceCtorEq, Option.map_some, Option.some.injEq,
      false_or] at h1 h2
    simp only [Option.elim_some] at he
    show some (b1, t1) = some (b2, t2)
    rw [h1, h2, hf he]

/-- A path that stays in one copy together with `none` projects to a path of `G` of the same
length. -/
theorem glue_path_transfer {V T : Type} (G : SimpleGraph V) (a : V) (f : T → V)
    (K : SimpleGraph (Option (Bool × T)))
    (hK : ∀ p q, K.Adj p q ↔ G.Adj (p.elim a (fun r => f r.2)) (q.elim a (fun r => f r.2)) ∧
      ∀ p' q', p = some p' → q = some q' → p'.1 = q'.1)
    (hf : Function.Injective f) (hfa : ∀ t, f t ≠ a) (b : Bool)
    {x y : Option (Bool × T)} (p : K.Walk x y) (hp : p.IsPath)
    (hs : ∀ w ∈ p.support, w ∈ {w : Option (Bool × T) | w = none ∨ w.map Prod.fst = some b}) :
    ∃ q : G.Walk (x.elim a (fun r => f r.2)) (y.elim a (fun r => f r.2)),
      q.IsPath ∧ q.length = p.length := by
  obtain ⟨φ, hφ, hφe⟩ := glue_hom G a f K hK hf hfa b
  let p' := p.induce _ hs
  have hp' : p'.IsPath := by
    apply Walk.IsPath.of_map (f := (Embedding.induce _).toHom)
    rw [Walk.map_induce]
    exact hp
  refine ⟨(p'.map φ).copy (hφe _) (hφe _), ?_, ?_⟩
  · rw [Walk.isPath_copy]
    exact hp'.map hφ
  · rw [Walk.length_copy, Walk.length_map]
    exact glue_length_induce K p hs

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
  obtain ⟨φ, hφ, -⟩ := glue_hom G a f K hK hf hfa b
  let c2 := c1.induce _ hsub
  have hc2 : c2.IsCycle := by
    apply Walk.IsCycle.of_map (f := (Embedding.induce _).toHom)
    rw [Walk.map_induce]
    exact hc1
  have hl2 : c2.length = c1.length := glue_length_induce K c1 hsub
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

/- ### Degrees under adding edges -/

theorem degree_le_of_adj_imp {W : Type} [Fintype W] {K0 K : SimpleGraph W}
    [DecidableRel K0.Adj] [DecidableRel K.Adj] (hle : ∀ p q, K0.Adj p q → K.Adj p q) (p : W) :
    K0.degree p ≤ K.degree p := by
  rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree]
  apply Finset.card_le_card
  intro q hq
  rw [mem_neighborFinset] at hq ⊢
  exact hle _ _ hq

theorem degree_succ_le_of_adj_imp {W : Type} [Fintype W] {K0 K : SimpleGraph W}
    [DecidableRel K0.Adj] [DecidableRel K.Adj] (hle : ∀ p q, K0.Adj p q → K.Adj p q)
    {p q : W} (hK : K.Adj p q) (hK0 : ¬ K0.Adj p q) : K0.degree p + 1 ≤ K.degree p := by
  classical
  rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree]
  have hsub : insert q (K0.neighborFinset p) ⊆ K.neighborFinset p := by
    intro w hw
    rw [Finset.mem_insert] at hw
    rw [mem_neighborFinset]
    rcases hw with rfl | hw
    · exact hK
    · rw [mem_neighborFinset] at hw
      exact hle _ _ hw
  have hc := Finset.card_le_card hsub
  rwa [Finset.card_insert_of_notMem (by rw [mem_neighborFinset]; exact hK0)] at hc

/- ### A general fact about cycles -/

/-- A cycle at `a` through the edge `ab` gives a path from `b` back to `a` that avoids this edge
and is one edge shorter. -/
theorem cycle_split_edge {V : Type} {G : SimpleGraph V} {a b : V} (c : G.Walk a a)
    (hc : c.IsCycle) (hab : s(a, b) ∈ c.edges) :
    ∃ p : G.Walk b a, p.IsPath ∧ s(a, b) ∉ p.edges ∧ p.length + 1 = c.length := by
  cases c with
  | nil => exact absurd hc Walk.not_isCycle_nil
  | @cons _ y _ h q =>
    rw [Walk.cons_isCycle_iff] at hc
    obtain ⟨hq, hqe⟩ := hc
    by_cases hy : y = b
    · subst hy
      exact ⟨q, hq, hqe, by simp⟩
    · have hin : s(a, b) ∈ q.edges := by
        rw [Walk.edges_cons, List.mem_cons] at hab
        rcases hab with e | e
        · exfalso
          rcases Sym2.eq_iff.mp e with ⟨-, e2⟩ | ⟨e1, -⟩
          · exact hy e2.symm
          · exact G.ne_of_adj h e1
        · exact e
      have hr : q.reverse.IsPath := hq.reverse
      have hin' : s(a, b) ∈ q.reverse.edges := by
        rw [Walk.edges_reverse, List.mem_reverse]
        exact hin
      have hlen : q.reverse.length = q.length := Walk.length_reverse q
      generalize q.reverse = r at hr hin' hlen
      cases r with
      | nil => simp at hin'
      | @cons _ z _ h2 r' =>
        rw [Walk.cons_isPath_iff] at hr
        obtain ⟨hr', ha⟩ := hr
        rw [Walk.edges_cons, List.mem_cons] at hin'
        have hz : z = b := by
          rcases hin' with e | e
          · rcases Sym2.eq_iff.mp e with ⟨-, e2⟩ | ⟨e1, -⟩
            · exact e2.symm
            · exact absurd e1 (G.ne_of_adj h2)
          · exact absurd (r'.fst_mem_support_of_mem_edges e) ha
        subst hz
        have ha' : a ∉ r'.reverse.support := by
          rw [Walk.support_reverse, List.mem_reverse]
          exact ha
        refine ⟨(Walk.cons h r'.reverse).reverse, ?_, ?_, ?_⟩
        · apply Walk.IsPath.reverse
          rw [Walk.cons_isPath_iff]
          exact ⟨hr'.reverse, ha'⟩
        · rw [Walk.edges_reverse, List.mem_reverse, Walk.edges_cons, List.mem_cons, not_or]
          refine ⟨fun e => ?_, fun e => ?_⟩
          · rcases Sym2.eq_iff.mp e with ⟨-, e2⟩ | ⟨e1, -⟩
            · exact hy e2.symm
            · exact G.ne_of_adj h e1
          · exact ha' (r'.reverse.fst_mem_support_of_mem_edges e)
        · simp only [Walk.length_reverse, Walk.length_cons] at hlen ⊢
          omega

/- ### Lemma N: the odd gluing is 2-connected (from NoCutGlue.lean) -/


/-- the separation hypothesis from a base vertex for each deleted vertex. -/
theorem noCut_of_base {W : Type} (K : SimpleGraph W)
    (h : ∀ a : W, ∃ c : W, ∀ p : W, p ≠ a → ∃ w : K.Walk p c, a ∉ w.support) :
    (∀ (a : W) (S : Set (W)), a ∈ S → (∃ p ∈ S, p ≠ a) → (∃ q : W, q ∉ S) →
      ∃ p ∈ S, p ≠ a ∧ ∃ q ∉ S, K.Adj p q) := by
  intro a S ha hx hy
  obtain ⟨x, hx, hxa⟩ := hx
  obtain ⟨y, hy⟩ := hy
  obtain ⟨c, hc⟩ := h a
  have hya : y ≠ a := fun e => hy (e ▸ ha)
  obtain ⟨w1, hw1⟩ := hc x hxa
  obtain ⟨w2, hw2⟩ := hc y hya
  have hw : a ∉ (w1.append w2.reverse).support := by
    rw [Walk.mem_support_append_iff, Walk.support_reverse, List.mem_reverse]
    rintro (h | h)
    · exact hw1 h
    · exact hw2 h
  obtain ⟨d, hd, hd1, hd2⟩ := (w1.append w2.reverse).exists_boundary_dart S hx hy
  refine ⟨d.fst, hd1, fun e => hw ?_, d.snd, hd2, d.adj⟩
  rw [← e]
  exact Walk.dart_fst_mem_support_of_mem_darts _ hd

/-- Walks avoiding a vertex, from the separation hypothesis. -/
theorem reach_of_noCut {W : Type} {K : SimpleGraph W} (hK : (∀ (a : W) (S : Set (W)), a ∈ S → (∃ p ∈ S, p ≠ a) → (∃ q : W, q ∉ S) →
      ∃ p ∈ S, p ≠ a ∧ ∃ q ∉ S, K.Adj p q)) {a x y : W}
    (hx : x ≠ a) (hy : y ≠ a) : ∃ w : K.Walk x y, a ∉ w.support := by
  classical
  by_contra hno
  let S : Set W := {z | z = a ∨ ∃ w : K.Walk x z, a ∉ w.support}
  have hxS : x ∈ S := Or.inr ⟨Walk.nil, by simp [hx.symm]⟩
  have hyS : y ∉ S := by
    rintro (e | h)
    · exact hy e
    · exact hno h
  obtain ⟨z, hz, hza, t, ht, hzt⟩ := hK a S (Or.inl rfl) ⟨x, hxS, hx⟩ ⟨y, hyS⟩
  rcases hz with e | ⟨w, hw⟩
  · exact hza e
  · apply ht
    have hta : t ≠ a := fun e => ht (Or.inl e)
    refine Or.inr ⟨w.append (Walk.cons hzt Walk.nil), ?_⟩
    rw [Walk.mem_support_append_iff]
    rintro (h | h)
    · exact hw h
    · simp [hza.symm, hta.symm] at h

set_option maxHeartbeats 1000000 in
/-- **Lemma N.** The odd gluing satisfies the separation hypothesis. -/
theorem glue_noCut {V T : Type} (H : SimpleGraph V) (u v : V) (f : T → V)
    (hf : Function.Injective f) (hfu : ∀ t, f t ≠ u) (hsurj : ∀ z, z ≠ u → ∃ t, f t = z)
    (tv : T) (htv : f tv = v)
    (K : SimpleGraph (Option (Bool × T)))
    (hK : ∀ p q, K.Adj p q ↔
      (H.Adj (p.elim u (fun r => f r.2)) (q.elim u (fun r => f r.2)) ∧
        ∀ p' q', p = some p' → q = some q' → p'.1 = q'.1) ∨
      (p = some (true, tv) ∧ q = some (false, tv)) ∨
      (p = some (false, tv) ∧ q = some (true, tv)))
    (Hu : ∀ z, z ≠ u → ∃ w : H.Walk z v, u ∉ w.support)
    (Hv : ∀ z, z ≠ v → ∃ w : H.Walk z u, v ∉ w.support)
    (Hw : ∀ x z, x ≠ u → x ≠ v → z ≠ x →
      (∃ w : H.Walk z u, x ∉ w.support) ∨ (∃ w : H.Walk z v, x ∉ w.support))
    (Hc : H.Reachable v u) : (∀ (a : (Option (Bool × T))) (S : Set ((Option (Bool × T)))), a ∈ S → (∃ p ∈ S, p ≠ a) → (∃ q : (Option (Bool × T)), q ∉ S) →
      ∃ p ∈ S, p ≠ a ∧ ∃ q ∉ S, K.Adj p q) := by
  classical
  -- the lift of `H` into copy `b`
  obtain ⟨lift, hl_u, hl_f⟩ : ∃ lift : Bool → V → Option (Bool × T),
      (∀ b, lift b u = none) ∧ (∀ b t, lift b (f t) = some (b, t)) := by
    refine ⟨fun b z => if h : z = u then none else some (b, (hsurj z h).choose),
      fun b => by simp, fun b t => ?_⟩
    have e : (hsurj (f t) (hfu t)).choose = t := hf (hsurj (f t) (hfu t)).choose_spec
    simp only [dif_neg (hfu t), e]
  have hrep : ∀ z, z = u ∨ ∃ t, f t = z := fun z => (em (z = u)).imp id (hsurj z)
  have hπ : ∀ b z, (lift b z).elim u (fun r => f r.2) = z := by
    intro b z
    rcases hrep z with rfl | ⟨t, rfl⟩
    · simp [hl_u]
    · simp [hl_f]
  have hfst : ∀ b z p', lift b z = some p' → p'.1 = b := by
    intro b z p' e
    rcases hrep z with rfl | ⟨t, rfl⟩
    · rw [hl_u] at e
      cases e
    · rw [hl_f] at e
      cases e
      rfl
  have hadj : ∀ b z z', H.Adj z z' → K.Adj (lift b z) (lift b z') := by
    intro b z z' h
    refine (hK _ _).mpr (Or.inl ⟨?_, fun p' q' e1 e2 =>
      (hfst b z p' e1).trans (hfst b z' q' e2).symm⟩)
    rw [hπ, hπ]
    exact h
  let φ : Bool → (H →g K) := fun b => ⟨lift b, fun h => hadj b _ _ h⟩
  have liftWalk : ∀ (b : Bool) {z z' : V} (w : H.Walk z z') (a : Option (Bool × T)),
      (∀ y ∈ w.support, lift b y ≠ a) → ∃ w' : K.Walk (lift b z) (lift b z'), a ∉ w'.support := by
    intro b z z' w a h
    refine ⟨w.map (φ b), ?_⟩
    rw [Walk.support_map, List.mem_map]
    rintro ⟨y, hy, e⟩
    exact h y hy e
  have join : ∀ {p q s a : Option (Bool × T)}, (∃ w : K.Walk p q, a ∉ w.support) →
      (∃ w : K.Walk q s, a ∉ w.support) → ∃ w : K.Walk p s, a ∉ w.support := by
    rintro p q s a ⟨w1, h1⟩ ⟨w2, h2⟩
    refine ⟨w1.append w2, ?_⟩
    rw [Walk.mem_support_append_iff]
    rintro (h | h)
    · exact h1 h
    · exact h2 h
  have edge : ∀ {p q a : Option (Bool × T)}, K.Adj p q → p ≠ a → q ≠ a →
      ∃ w : K.Walk p q, a ∉ w.support := by
    intro p q a h hp hq
    exact ⟨Walk.cons h Walk.nil, by simp [hp.symm, hq.symm]⟩
  have newEdge : ∀ b, K.Adj (some (b, tv)) (some (!b, tv)) := by
    intro b
    rw [hK]
    cases b
    · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  have Hany : ∀ z, H.Reachable z u := by
    intro z
    by_cases hz : z = v
    · rw [hz]
      exact Hc
    · obtain ⟨w, -⟩ := Hv z hz
      exact ⟨w⟩
  apply noCut_of_base
  rintro (_ | ⟨b, t⟩)
  · -- deleting the identified vertex: base = copy `true` of `v`
    refine ⟨some (true, tv), ?_⟩
    rintro (_ | ⟨b', t'⟩) hp
    · exact absurd rfl hp
    · obtain ⟨w, hw⟩ := Hu (f t') (hfu t')
      have h1 := liftWalk b' w none (fun y hy e => by
        rcases hrep y with rfl | ⟨s, rfl⟩
        · exact hw hy
        · rw [hl_f] at e
          cases e)
      rw [hl_f, ← htv, hl_f] at h1
      cases b'
      · exact join h1 (edge (newEdge false : K.Adj (some (false, tv)) (some (true, tv)))
          (by simp) (by simp))
      · exact h1
  · -- deleting a copy vertex: base = the identified vertex
    refine ⟨none, ?_⟩
    have other : ∀ (b' : Bool) {z : V} (w : H.Walk z u), b' ≠ b →
        ∃ w' : K.Walk (lift b' z) none, some (b, t) ∉ w'.support := by
      intro b' z w hb
      have h := liftWalk b' w (some (b, t)) (fun y _ e => hb (hfst b' y (b, t) e).symm)
      rwa [hl_u] at h
    rintro (_ | ⟨b', t'⟩) hp
    · exact ⟨Walk.nil, by simp⟩
    · by_cases hb : b' = b
      · rw [hb] at hp ⊢
        have hft : f t' ≠ f t := fun e => hp (by rw [hf e])
        have same : ∀ {z z' : V} (w : H.Walk z z'), f t ∉ w.support →
            ∀ y ∈ w.support, lift b y ≠ some (b, t) := by
          intro z z' w hw y hy e
          rcases hrep y with rfl | ⟨s, rfl⟩
          · rw [hl_u] at e
            cases e
          · rw [hl_f] at e
            cases e
            exact hw hy
        by_cases hv' : f t = v
        · obtain ⟨w, hw⟩ := Hv (f t') (by rw [← hv']; exact hft)
          have h := liftWalk b w _ (same w (by rw [hv']; exact hw))
          rwa [hl_f, hl_u] at h
        · rcases Hw (f t) (f t') (hfu t) hv' hft with ⟨w, hw⟩ | ⟨w, hw⟩
          · have h := liftWalk b w _ (same w hw)
            rwa [hl_f, hl_u] at h
          · have h1 := liftWalk b w _ (same w hw)
            rw [hl_f, ← htv, hl_f] at h1
            obtain ⟨w2⟩ := Hany (f tv)
            have h2 := other (!b) w2 (by cases b <;> simp)
            rw [hl_f] at h2
            refine join h1 (join (edge (newEdge b) ?_ ?_) h2)
            · intro e
              cases e
              exact hv' htv
            · cases b <;> simp
      · obtain ⟨w⟩ := Hany (f t')
        have h := other b' w hb
        rwa [hl_f] at h

/- ### The G-side: walk conditions for `H = G - r` from `(∀ (a : V) (S : Set (V)), a ∈ S → (∃ p ∈ S, p ≠ a) → (∃ q : V, q ∉ S) →
      ∃ p ∈ S, p ≠ a ∧ ∃ q ∉ S, G.Adj p q)` -/

/-- A walk avoiding `r` lifts to `G - r` with the same vertices. -/
theorem walk_to_induce {V : Type} {G : SimpleGraph V} {r : V} :
    ∀ {a b : V} (p : G.Walk a b) (ha : a ≠ r) (hb : b ≠ r), r ∉ p.support →
      ∃ q : (G.induce {z | z ≠ r}).Walk ⟨a, ha⟩ ⟨b, hb⟩, ∀ c ∈ q.support, c.1 ∈ p.support := by
  intro a b p
  induction p with
  | nil =>
    intro ha hb _
    refine ⟨Walk.nil, fun c hc => ?_⟩
    rw [Walk.support_nil, List.mem_singleton] at hc ⊢
    subst hc
    rfl
  | @cons a m b h p ih =>
    intro ha hb hp
    rw [Walk.support_cons, List.mem_cons, not_or] at hp
    have hm : m ≠ r := fun e => hp.2 (e ▸ p.start_mem_support)
    obtain ⟨q, hq⟩ := ih hm hb hp.2
    refine ⟨Walk.cons (induce_adj.mpr h) q, fun c hc => ?_⟩
    rw [Walk.support_cons, List.mem_cons] at hc ⊢
    rcases hc with hc | hc
    · subst hc
      exact Or.inl rfl
    · exact Or.inr (hq c hc)

/-- A walk from `a ≠ r` through `r` gives a walk from `a` to a neighbour of `r` that avoids `r`
and uses only vertices of the original walk. -/
theorem walk_last_before {V : Type} {G : SimpleGraph V} {r : V} :
    ∀ {a b : V} (p : G.Walk a b), a ≠ r → r ∈ p.support →
      ∃ m, G.Adj m r ∧ ∃ q : G.Walk a m, r ∉ q.support ∧ ∀ c ∈ q.support, c ∈ p.support := by
  intro a b p
  induction p with
  | nil =>
    intro ha hr
    rw [Walk.support_nil, List.mem_singleton] at hr
    exact absurd hr.symm ha
  | @cons a c b h p ih =>
    intro ha hr
    by_cases hc : c = r
    · refine ⟨a, hc ▸ h, Walk.nil, by simp [ha.symm], fun d hd => ?_⟩
      rw [Walk.support_nil, List.mem_singleton] at hd
      rw [hd, Walk.support_cons]
      simp
    · rw [Walk.support_cons, List.mem_cons] at hr
      have hr' : r ∈ p.support := hr.resolve_left (fun e => ha e.symm)
      obtain ⟨m, hm, q, hq, hsub⟩ := ih hc hr'
      refine ⟨m, hm, Walk.cons h q, ?_, fun d hd => ?_⟩
      · rw [Walk.support_cons, List.mem_cons, not_or]
        exact ⟨fun e => ha e.symm, hq⟩
      · rw [Walk.support_cons, List.mem_cons] at hd ⊢
        rcases hd with hd | hd
        · exact Or.inl hd
        · exact Or.inr (hsub d hd)

/-- The four walk conditions of `glue_noCut` for `H = G - r`, where `r` has neighbours `x ≠ y`
only, from `(∀ (a : V) (S : Set (V)), a ∈ S → (∃ p ∈ S, p ≠ a) → (∃ q : V, q ∉ S) →
      ∃ p ∈ S, p ≠ a ∧ ∃ q ∉ S, G.Adj p q)` (NOTES.md §3b). -/
theorem induce_conditions {V : Type} (G : SimpleGraph V) (hG : (∀ (a : V) (S : Set (V)), a ∈ S → (∃ p ∈ S, p ≠ a) → (∃ q : V, q ∉ S) →
      ∃ p ∈ S, p ≠ a ∧ ∃ q ∉ S, G.Adj p q)) {r x y : V}
    (hxr : x ≠ r) (hyr : y ≠ r) (hxy : x ≠ y) (hN : ∀ z, G.Adj z r → z = x ∨ z = y) :
    (∀ z : ({z | z ≠ r} : Set V), z ≠ ⟨x, hxr⟩ →
      ∃ w : (G.induce {z | z ≠ r}).Walk z ⟨y, hyr⟩, ⟨x, hxr⟩ ∉ w.support) ∧
    (∀ z : ({z | z ≠ r} : Set V), z ≠ ⟨y, hyr⟩ →
      ∃ w : (G.induce {z | z ≠ r}).Walk z ⟨x, hxr⟩, ⟨y, hyr⟩ ∉ w.support) ∧
    (∀ t z : ({z | z ≠ r} : Set V), t ≠ ⟨x, hxr⟩ → t ≠ ⟨y, hyr⟩ → z ≠ t →
      (∃ w : (G.induce {z | z ≠ r}).Walk z ⟨x, hxr⟩, t ∉ w.support) ∨
      (∃ w : (G.induce {z | z ≠ r}).Walk z ⟨y, hyr⟩, t ∉ w.support)) ∧
    (G.induce {z | z ≠ r}).Reachable ⟨y, hyr⟩ ⟨x, hxr⟩ := by
  have toH : ∀ {a b : V} (W : G.Walk a b) (ha : a ≠ r) (hb : b ≠ r), r ∉ W.support →
      ∀ t : ({z | z ≠ r} : Set V), t.1 ∉ W.support →
        ∃ q : (G.induce {z | z ≠ r}).Walk ⟨a, ha⟩ ⟨b, hb⟩, t ∉ q.support := by
    intro a b W ha hb hW t ht
    obtain ⟨q, hq⟩ := walk_to_induce W ha hb hW
    exact ⟨q, fun h => ht (hq t h)⟩
  have side : ∀ {p q : V} (hpr : p ≠ r) (hqr : q ≠ r), p ≠ q →
      (∀ z, G.Adj z r → z = p ∨ z = q) →
      ∀ z : ({z | z ≠ r} : Set V), z ≠ ⟨p, hpr⟩ →
        ∃ w : (G.induce {z | z ≠ r}).Walk z ⟨q, hqr⟩, ⟨p, hpr⟩ ∉ w.support := by
    intro p q hpr hqr hpq hN' z hz
    have hzp : z.1 ≠ p := fun e => hz (Subtype.ext e)
    obtain ⟨W, hW⟩ := reach_of_noCut hG hzp hpq.symm
    by_cases hrW : r ∈ W.support
    · obtain ⟨m, hm, W', hW'r, hsub⟩ := walk_last_before W z.2 hrW
      have hmq : m = q := by
        rcases hN' m hm with e | e
        · have hmW := hsub m W'.end_mem_support
          rw [e] at hmW
          exact absurd hmW hW
        · exact e
      subst hmq
      exact toH W' z.2 hqr hW'r ⟨p, hpr⟩ (fun h => hW (hsub p h))
    · exact toH W z.2 hqr hrW ⟨p, hpr⟩ hW
  refine ⟨side hxr hyr hxy hN, side hyr hxr hxy.symm (fun z hz => (hN z hz).symm), ?_, ?_⟩
  · intro t z _ _ hzt
    have htr : t.1 ≠ r := t.2
    have hzt' : z.1 ≠ t.1 := fun e => hzt (Subtype.ext e)
    obtain ⟨W, hW⟩ := reach_of_noCut hG hzt' (Ne.symm htr)
    obtain ⟨m, hm, W', hW'r, hsub⟩ := walk_last_before W z.2 W.end_mem_support
    have ht' : t.1 ∉ W'.support := fun h => hW (hsub _ h)
    rcases hN m hm with e | e
    · subst e
      exact Or.inl (toH W' z.2 hxr hW'r t ht')
    · subst e
      exact Or.inr (toH W' z.2 hyr hW'r t ht')
  · obtain ⟨W, hW⟩ := reach_of_noCut hG hyr hxr
    obtain ⟨q, -⟩ := walk_to_induce W hyr hxr hW
    exact ⟨q⟩

/-- **Lemma N, applied form.** For `G` with the separation hypothesis and a vertex `r` whose only neighbours are
`x ≠ y`, the odd gluing of `G - r` (identify the copies of `x`, join the copies of `y`; the
encoding of `odd_glue` with `T = {t // t ≠ x}`) satisfies the separation hypothesis. -/
theorem glue_noCut_of_noCut {V : Type} (G : SimpleGraph V) (hG : (∀ (a : V) (S : Set (V)), a ∈ S → (∃ p ∈ S, p ≠ a) → (∃ q : V, q ∉ S) →
      ∃ p ∈ S, p ≠ a ∧ ∃ q ∉ S, G.Adj p q)) {r x y : V}
    (hxr : x ≠ r) (hyr : y ≠ r) (hxy : x ≠ y) (hN : ∀ z, G.Adj z r → z = x ∨ z = y)
    (tv : {t : ({z | z ≠ r} : Set V) // t ≠ ⟨x, hxr⟩}) (htv : tv.1 = ⟨y, hyr⟩)
    (K : SimpleGraph (Option (Bool × {t : ({z | z ≠ r} : Set V) // t ≠ ⟨x, hxr⟩})))
    (hK : ∀ p q, K.Adj p q ↔
      ((G.induce {z | z ≠ r}).Adj (p.elim ⟨x, hxr⟩ (fun s => Subtype.val s.2))
          (q.elim ⟨x, hxr⟩ (fun s => Subtype.val s.2)) ∧
        ∀ p' q', p = some p' → q = some q' → p'.1 = q'.1) ∨
      (p = some (true, tv) ∧ q = some (false, tv)) ∨
      (p = some (false, tv) ∧ q = some (true, tv))) :
    (∀ (a : (Option (Bool × {t : ({z | z ≠ r} : Set V) // t ≠ ⟨x, hxr⟩}))) (S : Set ((Option (Bool × {t : ({z | z ≠ r} : Set V) // t ≠ ⟨x, hxr⟩})))), a ∈ S → (∃ p ∈ S, p ≠ a) → (∃ q : (Option (Bool × {t : ({z | z ≠ r} : Set V) // t ≠ ⟨x, hxr⟩})), q ∉ S) →
      ∃ p ∈ S, p ≠ a ∧ ∃ q ∉ S, K.Adj p q) := by
  obtain ⟨Hu, Hv, Hw, Hc⟩ := induce_conditions G hG hxr hyr hxy hN
  exact glue_noCut (G.induce {z | z ≠ r}) ⟨x, hxr⟩ ⟨y, hyr⟩ Subtype.val Subtype.val_injective
    (fun t => t.2) (fun z hz => ⟨⟨z, hz⟩, rfl⟩) tv htv K hK Hu Hv Hw Hc


/- ### Lemma A -/

set_option maxHeartbeats 1000000 in
/-- **Odd-crossing gluing.** Two copies of `H` with the copies of `u` identified and the copies
of `v` joined by an edge: `2 |V| - 1` vertices, minimum degree at least 3, and every cycle is a
cycle of `H` or two `u`–`v` paths of `H` plus one edge; and it satisfies the separation hypothesis when `H` satisfies the
four walk conditions of `glue_noCut`. -/
theorem odd_glue {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    {u v : V} (huv : u ≠ v) (hu : 2 ≤ H.degree u) (hv : 2 ≤ H.degree v)
    (hdeg : ∀ w, w ≠ u → w ≠ v → 3 ≤ H.degree w) :
    ∃ (W : Type) (_ : Fintype W) (K : SimpleGraph W) (_ : DecidableRel K.Adj),
      Fintype.card W + 1 = 2 * Fintype.card V ∧ 3 ≤ K.minDegree ∧
      (∀ (w : W) (c : K.Walk w w), c.IsCycle →
        (∃ (x : V) (c' : H.Walk x x), c'.IsCycle ∧ c'.length = c.length) ∨
        (∃ (p q : H.Walk u v), p.IsPath ∧ q.IsPath ∧ c.length = p.length + q.length + 1)) ∧
      ((∀ z, z ≠ u → ∃ w : H.Walk z v, u ∉ w.support) →
        (∀ z, z ≠ v → ∃ w : H.Walk z u, v ∉ w.support) →
        (∀ x z, x ≠ u → x ≠ v → z ≠ x →
          (∃ w : H.Walk z u, x ∉ w.support) ∨ (∃ w : H.Walk z v, x ∉ w.support)) →
        H.Reachable v u → (∀ (a : W) (S : Set (W)), a ∈ S → (∃ p ∈ S, p ≠ a) → (∃ q : W, q ∉ S) →
      ∃ p ∈ S, p ≠ a ∧ ∃ q ∉ S, K.Adj p q)) := by
  classical
  let T := {x : V // x ≠ u}
  let f : T → V := Subtype.val
  have hf : Function.Injective f := Subtype.val_injective
  have hfa : ∀ t : T, f t ≠ u := fun t => t.2
  have hclosed : ∀ t y, H.Adj (f t) y → y = u ∨ ∃ t', f t' = y := by
    intro t y _
    by_cases hy : y = u
    · exact Or.inl hy
    · exact Or.inr ⟨⟨y, hy⟩, rfl⟩
  let tv : T := ⟨v, huv.symm⟩
  -- two copies glued at `u`
  let K0 : SimpleGraph (Option (Bool × T)) :=
    { Adj := fun p q => H.Adj (p.elim u (fun r => f r.2)) (q.elim u (fun r => f r.2)) ∧
        ∀ p' q', p = some p' → q = some q' → p'.1 = q'.1
      symm := ⟨fun p q h => ⟨h.1.symm, fun p' q' e1 e2 => (h.2 q' p' e2 e1).symm⟩⟩
      loopless := ⟨fun p h => H.irrefl h.1⟩ }
  have hK0 : ∀ p q, K0.Adj p q ↔ H.Adj (p.elim u (fun r => f r.2)) (q.elim u (fun r => f r.2)) ∧
      ∀ p' q', p = some p' → q = some q' → p'.1 = q'.1 := fun _ _ => Iff.rfl
  -- the two copies of `v`, and the new edge between them
  let x1 : Option (Bool × T) := some (true, tv)
  let x2 : Option (Bool × T) := some (false, tv)
  have hx12 : x1 ≠ x2 := by simp [x1, x2]
  let K : SimpleGraph (Option (Bool × T)) :=
    { Adj := fun p q => K0.Adj p q ∨ (p = x1 ∧ q = x2) ∨ (p = x2 ∧ q = x1)
      symm := ⟨fun p q h => by
        rcases h with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl h.symm
        · exact Or.inr (Or.inr ⟨h2, h1⟩)
        · exact Or.inr (Or.inl ⟨h2, h1⟩)⟩
      loopless := ⟨fun p h => by
        rcases h with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact K0.irrefl h
        · exact hx12 (h1.symm.trans h2)
        · exact hx12 (h2.symm.trans h1)⟩ }
  have hK : ∀ p q, K.Adj p q ↔ K0.Adj p q ∨ (p = x1 ∧ q = x2) ∨ (p = x2 ∧ q = x1) :=
    fun _ _ => Iff.rfl
  have hle : ∀ p q, K0.Adj p q → K.Adj p q := fun _ _ h => Or.inl h
  refine ⟨Option (Bool × T), inferInstance, K, inferInstance, ?_, ?_, ?_, ?_⟩
  · -- vertex count
    have hT : Fintype.card T + 1 = Fintype.card V := by
      rw [← Fintype.card_option]
      exact Fintype.card_congr (Equiv.optionSubtypeNe u)
    rw [Fintype.card_option, Fintype.card_prod, Fintype.card_bool]
    omega
  · -- minimum degree
    apply K.le_minDegree_of_forall_le_degree
    rintro (_ | ⟨b, t⟩)
    · -- the glued copy of `u`
      obtain ⟨y1, h1, y2, h2, h12⟩ :=
        Finset.one_lt_card.mp (show 1 < (H.neighborFinset u).card by
          rw [card_neighborFinset_eq_degree]; omega)
      rw [mem_neighborFinset] at h1 h2
      let t1 : T := ⟨y1, (H.ne_of_adj h1).symm⟩
      let t2 : T := ⟨y2, (H.ne_of_adj h2).symm⟩
      have ht12 : t1 ≠ t2 := fun e => h12 (congrArg Subtype.val e)
      have hn := glue_degree_none H u f K0 hK0 ht12 h1 h2
      have hm := degree_le_of_adj_imp hle (none : Option (Bool × T))
      omega
    · by_cases ht : t = tv
      · -- a copy of `v`: its degree in `H` plus the new edge
        subst ht
        have hnew : K.Adj (some (b, tv)) (some (!b, tv)) := by
          cases b
          · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
          · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
        have hold : ¬ K0.Adj (some (b, tv)) (some (!b, tv)) := by
          intro h
          have := h.2 _ _ rfl rfl
          cases b <;> simp at this
        have hcard := degree_succ_le_of_adj_imp hle hnew hold
        have h0 := glue_degree_some H u f K0 hK0 hclosed b tv
        change 2 ≤ H.degree (f tv) at hv
        omega
      · -- any other copy vertex keeps its degree
        have hne : f t ≠ v := fun e => ht (Subtype.ext e)
        have h3 := hdeg (f t) (hfa t) hne
        have h0 := glue_degree_some H u f K0 hK0 hclosed b t
        have hm := degree_le_of_adj_imp hle (some (b, t))
        omega
  · -- cycles
    intro w c hc
    have hK0edge : ∀ (y z : Option (Bool × T)), K.Adj y z → s(y, z) ≠ s(x1, x2) → K0.Adj y z := by
      intro y z hyz hne
      rcases hyz with h0 | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact h0
      · exact absurd (show s(y, z) = s(x1, x2) by rw [h1, h2]) hne
      · exact absurd (show s(y, z) = s(x1, x2) by rw [h1, h2, Sym2.eq_swap]) hne
    have htransfer : ∀ {y z : Option (Bool × T)} (p : K.Walk y z), s(x1, x2) ∉ p.edges →
        ∀ e ∈ p.edges, e ∈ K0.edgeSet := by
      intro y z p hp e
      refine Sym2.ind (fun y' z' hep => ?_) e
      have heK : K.Adj y' z' := (mem_edgeSet K).mp (p.edges_subset_edgeSet hep)
      rw [mem_edgeSet]
      exact hK0edge y' z' heK (fun h => hp (h ▸ hep))
    by_cases he : s(x1, x2) ∈ c.edges
    · right
      have hx1 : x1 ∈ c.support := c.fst_mem_support_of_mem_edges he
      have he' : s(x1, x2) ∈ (c.rotate x1 hx1).edges :=
        (Walk.rotate_edges c x1 hx1).mem_iff.mpr he
      obtain ⟨p, hp, hpe, hpl⟩ := cycle_split_edge (c.rotate x1 hx1) (hc.rotate hx1) he'
      rw [Walk.length_rotate] at hpl
      let p0 := p.transfer K0 (htransfer p hpe)
      have hp0 : p0.IsPath := hp.transfer _
      have hp0l : p0.length = p.length := Walk.length_transfer _ _
      -- the path from the false copy of `v` to the true copy must pass through `none`
      have hnone : none ∈ p0.support := by
        by_contra hn
        have h := glue_support_of_none_notMem H u f K0 hK0 p0 hn x1 p0.end_mem_support
        simp [x1, x2] at h
      have hl12 : (p0.takeUntil none hnone).length + (p0.dropUntil none hnone).length =
          p0.length := by
        rw [← Walk.length_append, Walk.take_spec]
      set p1 := p0.takeUntil none hnone with hp1def
      set p2 := p0.dropUntil none hnone with hp2def
      have hp1 : p1.IsPath := hp0.takeUntil hnone
      have hp2 : p2.reverse.IsPath := (hp0.dropUntil hnone).reverse
      have hs1 : ∀ z ∈ p1.support,
          z ∈ {w : Option (Bool × T) | w = none ∨ w.map Prod.fst = some false} := by
        intro z hz
        exact glue_support_of_path_to_none H u f K0 hK0 p1 hp1 rfl (by simp [x2]) z hz
      have hs2 : ∀ z ∈ p2.reverse.support,
          z ∈ {w : Option (Bool × T) | w = none ∨ w.map Prod.fst = some true} := by
        intro z hz
        exact glue_support_of_path_to_none H u f K0 hK0 p2.reverse hp2 rfl (by simp [x1]) z hz
      obtain ⟨r1, hr1, hl1⟩ := glue_path_transfer H u f K0 hK0 hf hfa false p1 hp1 hs1
      obtain ⟨r2, hr2, hl2⟩ := glue_path_transfer H u f K0 hK0 hf hfa true p2.reverse hp2 hs2
      have ev2 : (x2 : Option (Bool × T)).elim u (fun r => f r.2) = v := rfl
      have ev1 : (x1 : Option (Bool × T)).elim u (fun r => f r.2) = v := rfl
      have eu : (none : Option (Bool × T)).elim u (fun r => f r.2) = u := rfl
      refine ⟨(r1.copy ev2 eu).reverse, (r2.copy ev1 eu).reverse,
        ((Walk.isPath_copy _ _ _).mpr hr1).reverse,
        ((Walk.isPath_copy _ _ _).mpr hr2).reverse, ?_⟩
      simp only [Walk.length_reverse, Walk.length_copy] at hl2 ⊢
      omega
    · left
      have hc0 := hc.transfer (htransfer c he)
      obtain ⟨x, c', hc', hl⟩ := glue_cycle_transfer H u f K0 hK0 hf hfa _ hc0
      exact ⟨x, c', hc', by rw [hl, Walk.length_transfer]⟩
  · -- 2-connectivity (Lemma N), from the four walk conditions on `H`
    intro Hu Hv Hw Hc
    exact glue_noCut H u v f hf hfa (fun z hz => ⟨⟨z, hz⟩, rfl⟩) tv rfl K (fun _ _ => Iff.rfl)
      Hu Hv Hw Hc

/-- **Lemma A (two-terminal parity).** In the setting of a minimum-order counterexample: if every
graph of minimum degree at least 3 on fewer than `n` vertices has a cycle of length `2^k`
(`k ≥ 2`), `H` has no such cycle, `2 |V(H)| ≤ n`, and `H` has minimum degree 3 except at `u ≠ v`
(degree at least 2 there), then two `u`–`v` paths of `H` have lengths adding up to `2^k - 1`. -/
theorem two_terminal_parity {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (n : ℕ)
    (hmin : ∀ (W : Type) (K : SimpleGraph W) [Fintype W] [DecidableRel K.Adj],
      Fintype.card W < n → 3 ≤ K.minDegree →
        ∃ (k : ℕ) (w : W) (c : K.Walk w w), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2 ^ k)
    (hfree : ∀ (k : ℕ) (x : V) (c : H.Walk x x), 2 ≤ k → c.IsCycle → c.length ≠ 2 ^ k)
    (hcard : 2 * Fintype.card V ≤ n)
    {u v : V} (huv : u ≠ v) (hu : 2 ≤ H.degree u) (hv : 2 ≤ H.degree v)
    (hdeg : ∀ w, w ≠ u → w ≠ v → 3 ≤ H.degree w) :
    ∃ (p q : H.Walk u v) (k : ℕ), p.IsPath ∧ q.IsPath ∧ 2 ≤ k ∧
      p.length + q.length + 1 = 2 ^ k := by
  obtain ⟨W, hW, K, hKd, hcardW, hmK, hcyc, -⟩ := odd_glue H huv hu hv hdeg
  obtain ⟨k, w, c, hk, hc, hcl⟩ := hmin W K (by omega) hmK
  rcases hcyc w c hc with ⟨x, c', hc', hl⟩ | ⟨p, q, hp, hq, hl⟩
  · exact absurd (hl.trans hcl) (hfree k x c' hk hc')
  · exact ⟨p, q, k, hp, hq, hk, by omega⟩

/-- **Lemma A, parity form.** Under the same hypotheses, `u` and `v` are joined in `H` by paths
of both parities. -/
theorem two_terminal_both_parities {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (n : ℕ)
    (hmin : ∀ (W : Type) (K : SimpleGraph W) [Fintype W] [DecidableRel K.Adj],
      Fintype.card W < n → 3 ≤ K.minDegree →
        ∃ (k : ℕ) (w : W) (c : K.Walk w w), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2 ^ k)
    (hfree : ∀ (k : ℕ) (x : V) (c : H.Walk x x), 2 ≤ k → c.IsCycle → c.length ≠ 2 ^ k)
    (hcard : 2 * Fintype.card V ≤ n)
    {u v : V} (huv : u ≠ v) (hu : 2 ≤ H.degree u) (hv : 2 ≤ H.degree v)
    (hdeg : ∀ w, w ≠ u → w ≠ v → 3 ≤ H.degree w) :
    ∃ (p q : H.Walk u v), p.IsPath ∧ q.IsPath ∧ p.length % 2 ≠ q.length % 2 := by
  obtain ⟨p, q, k, hp, hq, hk, he⟩ :=
    two_terminal_parity H n hmin hfree hcard huv hu hv hdeg
  refine ⟨p, q, hp, hq, ?_⟩
  obtain ⟨m, hm⟩ : 2 ∣ 2 ^ k := dvd_pow_self 2 (by omega)
  rw [hm] at he
  omega


/- ### The R3.H2 parity split -/

/-- Degrees in `G - r`: at most one neighbour is lost, none if `z` is not adjacent to `r`. -/
theorem induce_degree_ge {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : V)
    [Fintype ({z | z ≠ r} : Set V)] [DecidableRel (G.induce {z | z ≠ r}).Adj]
    (z : V) (hz : z ≠ r) :
    G.degree z ≤ (G.induce {z | z ≠ r}).degree ⟨z, hz⟩ + 1 ∧
      (¬ G.Adj z r → G.degree z ≤ (G.induce {z | z ≠ r}).degree ⟨z, hz⟩) := by
  classical
  have key : ∀ (extra : Finset V), (∀ w, G.Adj z w → w = r → w ∈ extra) →
      G.degree z ≤ (G.induce {z | z ≠ r}).degree ⟨z, hz⟩ + extra.card := by
    intro extra hex
    rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree]
    have hsub : G.neighborFinset z ⊆
        ((G.induce {z | z ≠ r}).neighborFinset ⟨z, hz⟩).map (Function.Embedding.subtype _) ∪
          extra := by
      intro w hw
      rw [mem_neighborFinset] at hw
      rw [Finset.mem_union]
      by_cases hwr : w = r
      · exact Or.inr (hex w hw hwr)
      · left
        rw [Finset.mem_map]
        refine ⟨⟨w, hwr⟩, ?_, rfl⟩
        rw [mem_neighborFinset]
        exact hw
    calc (G.neighborFinset z).card ≤ _ := Finset.card_le_card hsub
      _ ≤ _ := Finset.card_union_le _ _
      _ = _ := by rw [Finset.card_map]
  refine ⟨?_, fun hn => ?_⟩
  · have h := key {r} (fun w _ e => by simp [e])
    simpa using h
  · have h := key ∅ (fun w hw e => absurd (by subst e; exact hw) hn)
    simpa using h

/-- A path from `x` to `y` avoiding `r`, closed up through `r`, is a cycle at `r`. -/
theorem cycle_through {V : Type} (G : SimpleGraph V) {r x y : V} (hx : G.Adj r x)
    (hy : G.Adj y r) (hxy : x ≠ y) (P : G.Walk x y) (hP : P.IsPath) (hr : r ∉ P.support) :
    ∃ c : G.Walk r r, c.IsCycle ∧ c.length = P.length + 2 := by
  refine ⟨Walk.cons hx (P.concat hy), ?_, by rw [Walk.length_cons, Walk.length_concat]⟩
  rw [Walk.cons_isCycle_iff]
  refine ⟨hP.concat hr hy, ?_⟩
  rw [Walk.edges_concat, List.concat_eq_append, List.mem_append, List.mem_singleton, not_or]
  refine ⟨fun h => hr (P.fst_mem_support_of_mem_edges h), fun h => ?_⟩
  rcases Sym2.eq_iff.mp h with ⟨h1, -⟩ | ⟨-, h2⟩
  · exact G.ne_of_adj hy h1.symm
  · exact hxy h2


/- ### Pieces: the odd gluing of `G[S]` for a two-terminal piece `S` (NOTES.md §5) -/

/-- A walk from inside `S` to outside `S` has a first exit: a vertex `m ∈ S` with a neighbour
outside `S`, reached from the start by a walk inside `S` through vertices of the original walk. -/
theorem walk_exit {V : Type} {G : SimpleGraph V} {S : Set V} :
    ∀ {a b : V} (p : G.Walk a b) (ha : a ∈ S), b ∉ S →
      ∃ (m : V) (hm : m ∈ S), (∃ n, n ∉ S ∧ G.Adj m n) ∧
        ∃ q : (G.induce S).Walk ⟨a, ha⟩ ⟨m, hm⟩, ∀ c ∈ q.support, c.1 ∈ p.support := by
  intro a b p
  induction p with
  | nil =>
    intro ha hb
    exact absurd ha hb
  | @cons a c b h p ih =>
    intro ha hb
    by_cases hc : c ∈ S
    · obtain ⟨m, hm, hn, q, hq⟩ := ih hc hb
      refine ⟨m, hm, hn, Walk.cons (induce_adj.mpr h) q, fun d hd => ?_⟩
      rw [Walk.support_cons, List.mem_cons] at hd ⊢
      rcases hd with hd | hd
      · subst hd
        exact Or.inl rfl
      · exact Or.inr (hq d hd)
    · refine ⟨a, ha, ⟨c, hc, h⟩, Walk.nil, fun d hd => ?_⟩
      rw [Walk.support_nil, List.mem_singleton] at hd
      subst hd
      simp

/-- The four walk conditions of `glue_noCut` for `H = G[S]`, from `(∀ (a : V) (S : Set (V)), a ∈ S → (∃ p ∈ S, p ≠ a) → (∃ q : V, q ∉ S) →
      ∃ p ∈ S, p ≠ a ∧ ∃ q ∉ S, G.Adj p q)`, when some vertex `o`
lies outside `S` and every edge leaving `S` starts at `u` or `v` (NOTES.md §5). -/
theorem piece_conditions {V : Type} (G : SimpleGraph V) (hG : (∀ (a : V) (S : Set (V)), a ∈ S → (∃ p ∈ S, p ≠ a) → (∃ q : V, q ∉ S) →
      ∃ p ∈ S, p ≠ a ∧ ∃ q ∉ S, G.Adj p q)) {S : Set V} {u v o : V}
    (hu : u ∈ S) (hv : v ∈ S) (huv : u ≠ v) (ho : o ∉ S)
    (hbd : ∀ a ∈ S, ∀ b, b ∉ S → G.Adj a b → a = u ∨ a = v)
    (hnb : ∃ t ∈ S, G.Adj u t) :
    (∀ z : S, z ≠ ⟨u, hu⟩ → ∃ w : (G.induce S).Walk z ⟨v, hv⟩, ⟨u, hu⟩ ∉ w.support) ∧
    (∀ z : S, z ≠ ⟨v, hv⟩ → ∃ w : (G.induce S).Walk z ⟨u, hu⟩, ⟨v, hv⟩ ∉ w.support) ∧
    (∀ t z : S, t ≠ ⟨u, hu⟩ → t ≠ ⟨v, hv⟩ → z ≠ t →
      (∃ w : (G.induce S).Walk z ⟨u, hu⟩, t ∉ w.support) ∨
      (∃ w : (G.induce S).Walk z ⟨v, hv⟩, t ∉ w.support)) ∧
    (G.induce S).Reachable ⟨v, hv⟩ ⟨u, hu⟩ := by
  -- leave `S` from `z` while avoiding `x`: the exit vertex is `u` or `v`
  have exit : ∀ (z : S) (x : V), x ∈ S → z.1 ≠ x →
      ∃ (m : V) (hm : m ∈ S), (m = u ∨ m = v) ∧ m ≠ x ∧
        ∃ q : (G.induce S).Walk z ⟨m, hm⟩, ∀ c ∈ q.support, c.1 ≠ x := by
    intro z x hx hzx
    have hox : o ≠ x := fun e => ho (e ▸ hx)
    obtain ⟨W, hW⟩ := reach_of_noCut hG hzx hox
    obtain ⟨m, hm, ⟨n, hn, hmn⟩, q, hq⟩ := walk_exit W z.2 ho
    refine ⟨m, hm, hbd m hm n hn hmn, ?_, q, fun c hc e => hW (by rw [← e]; exact hq c hc)⟩
    intro e
    exact hW (by rw [← e]; exact hq _ q.end_mem_support)
  have side : ∀ {p q : V} (hp : p ∈ S) (hq : q ∈ S), (p = u ∧ q = v) ∨ (p = v ∧ q = u) →
      ∀ z : S, z ≠ ⟨p, hp⟩ → ∃ w : (G.induce S).Walk z ⟨q, hq⟩, ⟨p, hp⟩ ∉ w.support := by
    intro p q hp hq hpq z hz
    have hzp : z.1 ≠ p := fun e => hz (Subtype.ext e)
    obtain ⟨m, hm, hm2, hmp, w, hw⟩ := exit z p hp hzp
    have hmq : m = q := by
      rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hm2 with e | e <;>
        first | exact absurd e hmp | exact e
    subst hmq
    exact ⟨w, fun h => hw _ h rfl⟩
  have Hw : ∀ t z : S, t ≠ ⟨u, hu⟩ → t ≠ ⟨v, hv⟩ → z ≠ t →
      (∃ w : (G.induce S).Walk z ⟨u, hu⟩, t ∉ w.support) ∨
      (∃ w : (G.induce S).Walk z ⟨v, hv⟩, t ∉ w.support) := by
    intro t z _ _ hzt
    have hzt' : z.1 ≠ t.1 := fun e => hzt (Subtype.ext e)
    obtain ⟨m, hm, hm2, -, w, hw⟩ := exit z t.1 t.2 hzt'
    rcases hm2 with e | e
    · subst e
      exact Or.inl ⟨w, fun h => hw _ h rfl⟩
    · subst e
      exact Or.inr ⟨w, fun h => hw _ h rfl⟩
  have Hc : (G.induce S).Reachable ⟨v, hv⟩ ⟨u, hu⟩ := by
    obtain ⟨t, ht, hut⟩ := hnb
    have h1 : (G.induce S).Reachable ⟨u, hu⟩ ⟨t, ht⟩ :=
      (show (G.induce S).Adj ⟨u, hu⟩ ⟨t, ht⟩ from induce_adj.mpr hut).reachable
    have h2 : (G.induce S).Reachable ⟨t, ht⟩ ⟨v, hv⟩ := by
      by_cases htu : (⟨t, ht⟩ : S) = ⟨u, hu⟩
      · exact absurd (congrArg Subtype.val htu) (G.ne_of_adj hut).symm
      · obtain ⟨w, -⟩ := side hu hv (Or.inl ⟨rfl, rfl⟩) ⟨t, ht⟩ htu
        exact ⟨w⟩
    exact (h1.trans h2).symm
  exact ⟨side hu hv (Or.inl ⟨rfl, rfl⟩), side hv hu (Or.inr ⟨rfl, rfl⟩), Hw, Hc⟩

/-- Degrees in `G[S]` for a finset `S`: the neighbours of `z` that lie in `S`. -/
theorem induce_finset_degree {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) [Fintype (S : Set V)] [DecidableRel (G.induce (S : Set V)).Adj]
    (z : V) (hz : z ∈ (S : Set V)) :
    (G.induce (S : Set V)).degree ⟨z, hz⟩ = (S.filter (G.Adj z)).card := by
  rw [← card_neighborFinset_eq_degree, ← Finset.card_map (Function.Embedding.subtype _)]
  congr 1
  ext w
  simp only [Finset.mem_map, mem_neighborFinset, Function.Embedding.coe_subtype,
    Finset.mem_filter]
  constructor
  · rintro ⟨⟨w', hw'⟩, hadj, rfl⟩
    exact ⟨Finset.mem_coe.mp hw', induce_adj.mp hadj⟩
  · rintro ⟨hw, hadj⟩
    exact ⟨⟨w, Finset.mem_coe.mpr hw⟩, induce_adj.mpr hadj, rfl⟩

/-- A vertex whose neighbours all lie in `S` keeps its degree in `S`. -/
theorem filter_adj_card_of_closed {V : Type} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (S : Finset V) (z : V) (h : ∀ b, G.Adj z b → b ∈ S) :
    (S.filter (G.Adj z)).card = G.degree z := by
  rw [← card_neighborFinset_eq_degree]
  congr 1
  ext b
  simp only [Finset.mem_filter, mem_neighborFinset]
  exact ⟨fun h' => h'.2, fun h' => ⟨h b h', h'⟩⟩

/-- If `S` contains every vertex but `r`, a vertex loses at most one neighbour in `S`. -/
theorem degree_le_filter_succ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (S : Finset V) (x r : V) (hS : ∀ b, b ≠ r → b ∈ S) :
    G.degree x ≤ (S.filter (G.Adj x)).card + 1 := by
  rw [← card_neighborFinset_eq_degree]
  calc (G.neighborFinset x).card ≤ ((S.filter (G.Adj x)) ∪ {r}).card := by
        apply Finset.card_le_card
        intro b hb
        rw [mem_neighborFinset] at hb
        rw [Finset.mem_union, Finset.mem_filter, Finset.mem_singleton]
        by_cases hbr : b = r
        · exact Or.inr hbr
        · exact Or.inl ⟨hS b hbr, hb⟩
    _ ≤ (S.filter (G.Adj x)).card + ({r} : Finset V).card := Finset.card_union_le _ _
    _ = (S.filter (G.Adj x)).card + 1 := by rw [Finset.card_singleton]

set_option maxHeartbeats 1000000 in
/-- **Lemma Q (piece parity).** Assume every 2-connected graph of minimum degree at least 3 has
a cycle of length `2^k` (`k ≥ 2`). Let `G` be 2-connected and `S` a finset with a vertex `o`
outside it, such that `u ≠ v` are the only vertices of `S` with neighbours outside `S`, each has
at least two neighbours in `S`, and every other vertex of `S` has degree at least 3. If all
`u`–`v` paths inside `S` have the same parity, then `G` has a cycle of length `2^k`. -/
theorem piece_parity {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (h1 : ∀ (W : Type) (K : SimpleGraph W) [Fintype W] [DecidableRel K.Adj],
      3 ≤ K.minDegree → (∀ (a : W) (S : Set (W)), a ∈ S → (∃ p ∈ S, p ≠ a) → (∃ q : W, q ∉ S) →
      ∃ p ∈ S, p ≠ a ∧ ∃ q ∉ S, K.Adj p q) →
        ∃ (k : ℕ) (w : W) (c : K.Walk w w), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2 ^ k)
    (hG : (∀ (a : V) (S : Set (V)), a ∈ S → (∃ p ∈ S, p ≠ a) → (∃ q : V, q ∉ S) →
      ∃ p ∈ S, p ≠ a ∧ ∃ q ∉ S, G.Adj p q)) (S : Finset V) {u v o : V} (huS : u ∈ S) (hvS : v ∈ S) (huv : u ≠ v)
    (ho : o ∉ S) (hbd : ∀ a ∈ S, ∀ b, b ∉ S → G.Adj a b → a = u ∨ a = v)
    (hdu : 2 ≤ (S.filter (G.Adj u)).card) (hdv : 2 ≤ (S.filter (G.Adj v)).card)
    (hdeg : ∀ z ∈ S, z ≠ u → z ≠ v → 3 ≤ G.degree z)
    (hsame : ∀ p q : G.Walk u v, p.IsPath → q.IsPath → (∀ z ∈ p.support, z ∈ S) →
      (∀ z ∈ q.support, z ∈ S) → p.length % 2 = q.length % 2) :
    ∃ (k : ℕ) (w : V) (c : G.Walk w w), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2 ^ k := by
  classical
  have hu : u ∈ (S : Set V) := Finset.mem_coe.mpr huS
  have hv : v ∈ (S : Set V) := Finset.mem_coe.mpr hvS
  have huv' : (⟨u, hu⟩ : (S : Set V)) ≠ ⟨v, hv⟩ := fun e => huv (congrArg Subtype.val e)
  have hdu' : 2 ≤ (G.induce (S : Set V)).degree ⟨u, hu⟩ := by
    rw [induce_finset_degree]
    exact hdu
  have hdv' : 2 ≤ (G.induce (S : Set V)).degree ⟨v, hv⟩ := by
    rw [induce_finset_degree]
    exact hdv
  have hdegH : ∀ w : (S : Set V), w ≠ ⟨u, hu⟩ → w ≠ ⟨v, hv⟩ →
      3 ≤ (G.induce (S : Set V)).degree w := by
    rintro ⟨w, hw⟩ hwu hwv
    have hwu' : w ≠ u := fun e => hwu (Subtype.ext e)
    have hwv' : w ≠ v := fun e => hwv (Subtype.ext e)
    have hwS : w ∈ S := Finset.mem_coe.mp hw
    have hcl : ∀ b, G.Adj w b → b ∈ S := by
      intro b hb
      by_contra hbS
      rcases hbd w hwS b hbS hb with e | e
      · exact hwu' e
      · exact hwv' e
    rw [induce_finset_degree, filter_adj_card_of_closed G S w hcl]
    exact hdeg w hwS hwu' hwv'
  obtain ⟨W, hW, K, hKd, -, hmK, hcyc, hnc⟩ :=
    odd_glue (G.induce (S : Set V)) huv' hdu' hdv' hdegH
  have hnb : ∃ t ∈ (S : Set V), G.Adj u t := by
    obtain ⟨t, ht⟩ := Finset.card_pos.mp (by omega : 0 < (S.filter (G.Adj u)).card)
    rw [Finset.mem_filter] at ht
    exact ⟨t, Finset.mem_coe.mpr ht.1, ht.2⟩
  obtain ⟨Hu, Hv, Hw, Hc⟩ := piece_conditions G hG hu hv huv
    (fun h => ho (Finset.mem_coe.mp h))
    (fun a ha b hb hab => hbd a (Finset.mem_coe.mp ha) b (fun h => hb (Finset.mem_coe.mpr h)) hab)
    hnb
  obtain ⟨k, w, c, hk, hc, hcl⟩ := h1 W K hmK (hnc Hu Hv Hw Hc)
  have hinj := (Embedding.induce (S : Set V) (G := G)).injective
  rcases hcyc w c hc with ⟨z, c', hc', hl⟩ | ⟨p, q, hp, hq, hl⟩
  · refine ⟨k, _, c'.map (Embedding.induce (S : Set V) (G := G)).toHom, hk,
      Walk.IsCycle.map hinj hc', ?_⟩
    rw [Walk.length_map, hl, hcl]
  · exfalso
    have hin : ∀ {a b : (S : Set V)} (P : (G.induce (S : Set V)).Walk a b),
        ∀ z ∈ (P.map (Embedding.induce (S : Set V) (G := G)).toHom).support, z ∈ S := by
      intro a b P z hz
      rw [Walk.support_map, List.mem_map] at hz
      obtain ⟨t, -, rfl⟩ := hz
      exact Finset.mem_coe.mp t.2
    have e := hsame (p.map (Embedding.induce (S : Set V) (G := G)).toHom)
      (q.map (Embedding.induce (S : Set V) (G := G)).toHom)
      (Walk.IsPath.map hinj hp) (Walk.IsPath.map hinj hq) (hin p) (hin q)
    change (p.map (Embedding.induce (S : Set V) (G := G)).toHom).length % 2 =
      (q.map (Embedding.induce (S : Set V) (G := G)).toHom).length % 2 at e
    rw [Walk.length_map, Walk.length_map] at e
    obtain ⟨m, hm⟩ : 2 ∣ 2 ^ k := dvd_pow_self 2 (by omega)
    omega

set_option maxHeartbeats 1000000 in
/-- **The piece split.** If some two-terminal piece avoiding `r` has all its terminal-to-terminal
paths of one parity, Lemma Q (`piece_parity`) and `H1` give a cycle of length `2^k`. Otherwise the
piece `V - r` (terminals the two neighbours of `r`) gives cycles through `r` of both parities, and
`H2` applies. -/
theorem main : H1 → H2 → OMA.R_Erdos64_erdos_64_R3.H2 := by
  intro h1 h2 V G _ _ r hr hdeg hcut
  rcases Classical.em (∀ (S : Finset V) (u v : V), r ∉ S → u ∈ S → v ∈ S → u ≠ v →
      (∀ a ∈ S, ∀ b, b ∉ S → G.Adj a b → a = u ∨ a = v) →
      2 ≤ (S.filter (G.Adj u)).card → 2 ≤ (S.filter (G.Adj v)).card →
      ∃ (p q : G.Walk u v), p.IsPath ∧ q.IsPath ∧ (∀ z ∈ p.support, z ∈ S) ∧
        (∀ z ∈ q.support, z ∈ S) ∧ p.length % 2 ≠ q.length % 2) with hall | hnot
  · classical
    obtain ⟨x, y, hxy, hNr⟩ := Finset.card_eq_two.mp
      (show (G.neighborFinset r).card = 2 by rw [card_neighborFinset_eq_degree]; exact hr)
    have hrx : G.Adj r x := by
      rw [← mem_neighborFinset, hNr]
      simp
    have hry : G.Adj r y := by
      rw [← mem_neighborFinset, hNr]
      simp
    have hxr : x ≠ r := (G.ne_of_adj hrx).symm
    have hyr : y ≠ r := (G.ne_of_adj hry).symm
    have hN : ∀ z, G.Adj z r → z = x ∨ z = y := by
      intro z hz
      have hz' : z ∈ G.neighborFinset r := by
        rw [mem_neighborFinset]
        exact hz.symm
      rw [hNr] at hz'
      simpa using hz'
    have hS0 : ∀ b, b ≠ r → b ∈ Finset.univ.erase r :=
      fun b hb => Finset.mem_erase.mpr ⟨hb, Finset.mem_univ b⟩
    have hrS0 : r ∉ Finset.univ.erase r := fun h => (Finset.mem_erase.mp h).1 rfl
    have hbd0 : ∀ a ∈ Finset.univ.erase r, ∀ b, b ∉ Finset.univ.erase r → G.Adj a b →
        a = x ∨ a = y := by
      intro a _ b hb hab
      have hbr : b = r := by
        by_contra hne
        exact hb (hS0 b hne)
      subst hbr
      exact hN a hab
    have hdx := degree_le_filter_succ G (Finset.univ.erase r) x r hS0
    have hdy := degree_le_filter_succ G (Finset.univ.erase r) y r hS0
    have h3x := hdeg x hxr
    have h3y := hdeg y hyr
    obtain ⟨p, q, hp, hq, hps, hqs, hpq⟩ := hall (Finset.univ.erase r) x y hrS0 (hS0 x hxr)
      (hS0 y hyr) hxy hbd0 (by omega) (by omega)
    obtain ⟨c1, hc1, hl1⟩ := cycle_through G hrx hry.symm hxy p hp
      (fun h => hrS0 (hps r h))
    obtain ⟨c2, hc2, hl2⟩ := cycle_through G hrx hry.symm hxy q hq
      (fun h => hrS0 (hqs r h))
    refine h2 V G r hr hdeg hcut ⟨c1, c2, hc1, hc2, ?_⟩ hall
    rw [hl1, hl2]
    omega
  · push Not at hnot
    obtain ⟨S, u, v, hrS, huS, hvS, huv, hbd, hdu, hdv, hsame⟩ := hnot
    exact piece_parity G h1 hcut S huS hvS huv hrS hbd hdu hdv
      (fun z hz _ _ => hdeg z (fun e => hrS (e ▸ hz))) hsame

end OMA.R_Erdos64_erdos_64_R3_H2_R3
