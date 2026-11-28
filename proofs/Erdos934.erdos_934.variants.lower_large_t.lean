import FormalConjectures.ErdosProblems.«934»

/-!
# The lower bound along an unbounded sequence of degrees in Erdős Problem 934

Adapted from Asymptotically attaining the Moore bound, by Wouter Cames van
Batenburg and Samuel Korsky (arXiv:2608.03965), Proposition 3.1 and Corollary 1.2.
Lean source: https://github.com/woutercvb/wewantmoore
Revision: d59bd80ea93fabb9faf769e790ab47692645e022

This file reuses the Apache-2.0 port by GitHub contributor Ciphore, including
their bridge to the Formal Conjectures edge-distance definition:
https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/3048
(merge 42fde1599e71dce829956b900ca19e23de59a52d).
For the present, weaker conclusion we use the natural degree caps of the
halved-flag graphs themselves. The estimate at those degrees does not require
prime intervals, the prime number theorem, or interpolation between caps.
-/
/- DegreeDiameter.Framework -/
section PortFramework

/-
# Generic finite-graph framework for the degree--diameter preprint

This file contains only generic graph definitions and lemmas.  In particular, it does not assume
the flag-graph construction or any asymptotic input.

We use `SimpleGraph.ediam`, not `SimpleGraph.diam`: the latter is defined to be zero when the
extended diameter is infinite, and would therefore allow disconnected graphs accidentally.
-/

open Set

namespace DegreeDiameter

open SimpleGraph

universe u

/-- Every vertex of `G` has degree at most `d`, expressed without choosing a decidable adjacency
relation.  For a finite vertex type, `Set.ncard (G.neighborSet v)` is the ordinary vertex degree. -/
noncomputable def MaxDegreeLE {V : Type*} (G : SimpleGraph V) (d : ℕ) : Prop :=
  ∀ v, (G.neighborSet v).ncard ≤ d

/- ## A coarse breadth-first bound -/

/-- One legal breadth-first move: stay at the current vertex, or cross one edge. -/
def ClosedNeighbor {V : Type u} (G : SimpleGraph V) (x : V) :=
  {y : V // x = y ∨ G.Adj x y}

instance finite_closedNeighbor {V : Type u} [Finite V] (G : SimpleGraph V) (x : V) :
    Finite (ClosedNeighbor G x) :=
  Finite.of_injective Subtype.val Subtype.val_injective

lemma setOf_closedNeighbor_eq_insert {V : Type u} (G : SimpleGraph V) (x : V) :
    {y : V | x = y ∨ G.Adj x y} = insert x (G.neighborSet x) := by
  ext y
  simp [eq_comm]

lemma natCard_closedNeighbor_le {V : Type u} [Finite V] {G : SimpleGraph V} {d : ℕ}
    (hdegree : MaxDegreeLE G d) (x : V) : Nat.card (ClosedNeighbor G x) ≤ d + 1 := by
  change ({y : V | x = y ∨ G.Adj x y} : Set V).ncard ≤ d + 1
  rw [setOf_closedNeighbor_eq_insert, Set.ncard_insert_of_notMem]
  · exact Nat.add_le_add_right (hdegree x) 1
  · simp

/-- A uniform code space with `d + 1` choices at each of `n` stages. -/
def BFSCode (d : ℕ) : ℕ → Type
  | 0 => PUnit
  | n + 1 => Fin (d + 1) × BFSCode d n

instance finite_bfsCode (d n : ℕ) : Finite (BFSCode d n) := by
  induction n with
  | zero => exact inferInstanceAs (Finite PUnit)
  | succ n ih =>
      change Finite (Fin (d + 1) × BFSCode d n)
      letI : Finite (BFSCode d n) := ih
      infer_instance

@[simp] lemma natCard_bfsCode (d n : ℕ) : Nat.card (BFSCode d n) = (d + 1) ^ n := by
  induction n with
  | zero => simp [BFSCode]
  | succ n ih => simp [BFSCode, ih, pow_succ, mul_comm]

/-- Exact-length breadth-first routes.  Unlike graph walks, these permit stationary moves. -/
def BFSRouteCode {V : Type u} (G : SimpleGraph V) : V → ℕ → Type u
  | _, 0 => PUnit
  | x, n + 1 => Σ y : ClosedNeighbor G x, BFSRouteCode G y.1 n

/-- The endpoint of a breadth-first route code. -/
def BFSRouteCode.endpoint {V : Type u} (G : SimpleGraph V) :
    {x : V} → {n : ℕ} → BFSRouteCode G x n → V
  | x, 0, _ => x
  | _, _ + 1, c => endpoint G c.2

/-- A graph walk of length at most `n` can be padded by stationary moves to an exact-length
breadth-first route code with the same endpoint. -/
lemma exists_bfsRouteCode_endpoint_of_walk {V : Type u} {G : SimpleGraph V} {x y : V}
    (p : G.Walk x y) {n : ℕ} (hp : p.length ≤ n) :
    ∃ c : BFSRouteCode G x n, c.endpoint G = y := by
  induction n generalizing x y with
  | zero =>
      have hlen : p.length = 0 := Nat.eq_zero_of_le_zero hp
      have hxy : x = y := p.eq_of_length_eq_zero hlen
      subst y
      exact ⟨PUnit.unit, rfl⟩
  | succ n ih =>
      cases p with
      | nil =>
          obtain ⟨c, hc⟩ := ih (.nil : G.Walk x x) (Nat.zero_le n)
          exact ⟨⟨⟨x, Or.inl rfl⟩, c⟩, hc⟩
      | @cons x z y hxz tail =>
          have htail : tail.length ≤ n := Nat.succ_le_succ_iff.mp hp
          obtain ⟨c, hc⟩ := ih tail htail
          exact ⟨⟨⟨z, Or.inr hxz⟩, c⟩, hc⟩

/-- Each closed neighborhood embeds in the uniform alphabet of size `d + 1`. -/
noncomputable def closedNeighborEmbedding {V : Type u} [Finite V] {G : SimpleGraph V} {d : ℕ}
    (hdegree : MaxDegreeLE G d) (x : V) : ClosedNeighbor G x ↪ Fin (d + 1) :=
  (Finite.equivFin (ClosedNeighbor G x)).toEmbedding.trans
    (Fin.castLEEmb (natCard_closedNeighbor_le hdegree x))

/-- Encode a breadth-first route into a fixed-length word over `Fin (d + 1)`. -/
noncomputable def encodeBFSRoute {V : Type u} [Finite V] {G : SimpleGraph V} {d : ℕ}
    (hdegree : MaxDegreeLE G d) :
    (n : ℕ) → (x : V) → BFSRouteCode G x n → BFSCode d n
  | 0, _, _ => PUnit.unit
  | n + 1, x, c =>
      (closedNeighborEmbedding hdegree x c.1, encodeBFSRoute hdegree n c.1.1 c.2)

lemma encodeBFSRoute_injective {V : Type u} [Finite V] {G : SimpleGraph V} {d : ℕ}
    (hdegree : MaxDegreeLE G d) (n : ℕ) (x : V) :
    Function.Injective (encodeBFSRoute hdegree n x) := by
  induction n generalizing x with
  | zero =>
      intro a b _
      cases a
      cases b
      rfl
  | succ n ih =>
      rintro ⟨y, c⟩ ⟨z, c'⟩ h
      have hyz : y = z := (closedNeighborEmbedding hdegree x).injective
        (congrArg Prod.fst h)
      subst z
      have htail : encodeBFSRoute hdegree n y.1 c = encodeBFSRoute hdegree n y.1 c' := by
        simpa [encodeBFSRoute] using congrArg Prod.snd h
      have hcc' : c = c' := ih y.1 htail
      subst c'
      rfl

noncomputable def bfsRouteEmbedding {V : Type u} [Finite V]
    {G : SimpleGraph V} {d : ℕ} (hdegree : MaxDegreeLE G d) (n : ℕ) (x : V) :
    BFSRouteCode G x n ↪ BFSCode d n :=
  ⟨encodeBFSRoute hdegree n x, encodeBFSRoute_injective hdegree n x⟩

/-- Coarse breadth-first bound.  Its leading term is still `d^k`, so it is sufficient for the
upper asymptotic in Theorem 1.1. -/
lemma natCard_le_add_one_pow_of_ediam_le {V : Type u} [Finite V] [Nonempty V]
    {G : SimpleGraph V} {d k : ℕ} (hdegree : MaxDegreeLE G d)
    (hdiam : G.ediam ≤ (k : ℕ∞)) : Nat.card V ≤ (d + 1) ^ k := by
  let root : V := Classical.ofNonempty
  let e := bfsRouteEmbedding hdegree k root
  letI : Finite (BFSRouteCode G root k) := Finite.of_injective e e.injective
  have hsurj : Function.Surjective (BFSRouteCode.endpoint G (x := root) (n := k)) := by
    intro y
    have hdist : G.edist root y ≤ (k : ℕ∞) := SimpleGraph.edist_le_ediam.trans hdiam
    have hfinite : G.edist root y ≠ ⊤ := ne_top_of_le_ne_top (ENat.coe_ne_top k) hdist
    obtain ⟨p, hp⟩ := SimpleGraph.exists_walk_of_edist_ne_top hfinite
    have hlength : p.length ≤ k := by
      rw [← hp] at hdist
      exact_mod_cast hdist
    exact exists_bfsRouteCode_endpoint_of_walk p hlength
  calc
    Nat.card V ≤ Nat.card (BFSRouteCode G root k) :=
      Nat.card_le_card_of_surjective _ hsurj
    _ ≤ Nat.card (BFSCode d k) := Nat.card_le_card_of_injective e e.injective
    _ = (d + 1) ^ k := natCard_bfsCode d k

lemma natCard_le_add_one_pow_of_ediam_le' {V : Type u} [Finite V]
    {G : SimpleGraph V} {d k : ℕ} (hdegree : MaxDegreeLE G d)
    (hdiam : G.ediam ≤ (k : ℕ∞)) : Nat.card V ≤ (d + 1) ^ k := by
  cases isEmpty_or_nonempty V
  · simp
  · exact natCard_le_add_one_pow_of_ediam_le hdegree hdiam

/- ## A coarse degree bound for line graphs -/

noncomputable def lineGraphSharedVertex {V : Type u} {G : SimpleGraph V}
    (e : G.edgeSet) (f : G.lineGraph.neighborSet e) : V :=
  Classical.choose (SimpleGraph.lineGraph_adj_iff_exists.mp f.property).2

lemma lineGraphSharedVertex_mem_left {V : Type u} {G : SimpleGraph V}
    (e : G.edgeSet) (f : G.lineGraph.neighborSet e) : lineGraphSharedVertex e f ∈ e.1 :=
  (Classical.choose_spec (SimpleGraph.lineGraph_adj_iff_exists.mp f.property).2).1

lemma lineGraphSharedVertex_mem_right {V : Type u} {G : SimpleGraph V}
    (e : G.edgeSet) (f : G.lineGraph.neighborSet e) : lineGraphSharedVertex e f ∈ f.1.1 :=
  (Classical.choose_spec (SimpleGraph.lineGraph_adj_iff_exists.mp f.property).2).2

/-- Encode an edge neighboring `e` in the line graph by a shared endpoint of `e` and the other
endpoint of the neighboring edge. -/
noncomputable def lineGraphNeighborCode {V : Type u} {G : SimpleGraph V} (e : G.edgeSet) :
    G.lineGraph.neighborSet e → Σ v : {v : V // v ∈ e.1}, G.neighborSet v.1 :=
  fun f ↦
    let v := lineGraphSharedVertex e f
    let hvf : v ∈ f.1.1 := lineGraphSharedVertex_mem_right e f
    ⟨⟨v, lineGraphSharedVertex_mem_left e f⟩,
      ⟨Sym2.Mem.other hvf, by
        have hedge : s(v, Sym2.Mem.other hvf) ∈ G.edgeSet := by
          rw [Sym2.other_spec hvf]
          exact f.1.2
        exact G.mem_edgeSet.mp hedge⟩⟩

/-- Recover the encoded neighboring edge. -/
def edgeOfLineGraphNeighborCode {V : Type u} {G : SimpleGraph V} {e : G.edgeSet}
    (c : Σ v : {v : V // v ∈ e.1}, G.neighborSet v.1) : G.edgeSet :=
  ⟨s(c.1.1, c.2.1), G.mem_edgeSet.mpr c.2.2⟩

lemma edgeOfLineGraphNeighborCode_code {V : Type u} {G : SimpleGraph V}
    (e : G.edgeSet) (f : G.lineGraph.neighborSet e) :
    edgeOfLineGraphNeighborCode (lineGraphNeighborCode e f) = f.1 := by
  apply Subtype.ext
  exact Sym2.other_spec (lineGraphSharedVertex_mem_right e f)

lemma lineGraphNeighborCode_injective {V : Type u} {G : SimpleGraph V} (e : G.edgeSet) :
    Function.Injective (lineGraphNeighborCode e) := by
  intro f g hfg
  apply Subtype.ext
  rw [← edgeOfLineGraphNeighborCode_code e f, ← edgeOfLineGraphNeighborCode_code e g,
    hfg]

lemma natCard_endpoints_eq_two {V : Type u} {G : SimpleGraph V} (e : G.edgeSet) :
    Nat.card {v : V // v ∈ e.1} = 2 := by
  change (e.1 : Set V).ncard = 2
  let a := e.1.out.1
  let b := e.1.out.2
  have heq : s(a, b) = e.1 := e.1.out_eq
  have hab : a ≠ b := by
    have hadj : G.Adj a b := by
      rw [← G.mem_edgeSet, heq]
      exact e.2
    exact hadj.ne
  rw [← heq, Sym2.coe_mk, Set.ncard_pair hab]

/-- A coarse line-graph maximum-degree bound.  The sharper standard estimate is
`2 * (d - 1)`; `2 * d` is enough to establish finite boundedness of the edge extremum. -/
lemma maxDegreeLE_lineGraph {V : Type u} [Finite V] {G : SimpleGraph V} {d : ℕ}
    (hdegree : MaxDegreeLE G d) : MaxDegreeLE G.lineGraph (2 * d) := by
  intro e
  classical
  letI : Fintype V := Fintype.ofFinite V
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  have hcode : Nat.card (G.lineGraph.neighborSet e) ≤
      Nat.card (Σ v : {v : V // v ∈ e.1}, G.neighborSet v.1) :=
    Nat.card_le_card_of_injective (lineGraphNeighborCode e) (lineGraphNeighborCode_injective e)
  calc
    (G.lineGraph.neighborSet e).ncard = Nat.card (G.lineGraph.neighborSet e) :=
      (Nat.card_coe_set_eq _).symm
    _ ≤ Nat.card (Σ v : {v : V // v ∈ e.1}, G.neighborSet v.1) := hcode
    _ = ∑ v : {v : V // v ∈ e.1}, Nat.card (G.neighborSet v.1) := by
      rw [Nat.card_sigma]
    _ ≤ ∑ _v : {v : V // v ∈ e.1}, d := by
      apply Finset.sum_le_sum
      intro v _hv
      rw [Nat.card_coe_set_eq]
      exact hdegree v.1
    _ = Nat.card {v : V // v ∈ e.1} * d := by simp
    _ = 2 * d := by rw [natCard_endpoints_eq_two]

/-- A finite simple graph with `m` edges, maximum degree at most `d`, and line-graph diameter at
most `ell`. -/
noncomputable def EdgeAdmissible (ell d m : ℕ) : Prop :=
  ∃ (V : Type) (G : SimpleGraph V),
    Finite V ∧ G.edgeSet.ncard = m ∧ MaxDegreeLE G d ∧
      G.lineGraph.ediam ≤ (ell : ℕ∞)

lemma edgeAdmissible_le_coarseBound {ell d m : ℕ} (hm : EdgeAdmissible ell d m) :
    m ≤ (2 * d + 1) ^ ell := by
  rcases hm with ⟨V, G, hfinite, hcard, hdegree, hdiam⟩
  letI : Finite V := hfinite
  letI : Finite G.edgeSet := Finite.of_injective Subtype.val Subtype.val_injective
  rw [← hcard]
  calc
    G.edgeSet.ncard = Nat.card G.edgeSet := (Nat.card_coe_set_eq _).symm
    _ ≤ (2 * d + 1) ^ ell :=
      natCard_le_add_one_pow_of_ediam_le' (maxDegreeLE_lineGraph hdegree) hdiam

/-- The paper defines `h_ell(d) - 1` as the maximum admissible edge count, so we define `h` to be
one plus that maximum. -/
noncomputable def h (ell d : ℕ) : ℕ :=
  1 + sSup {m : ℕ | EdgeAdmissible ell d m}

/-- The exact Moore expression. -/
def mooreBound (k d : ℕ) : ℕ :=
  1 + d * ∑ j ∈ Finset.range k, (d - 1) ^ j

lemma maxDegreeLE_mono {V : Type*} {G : SimpleGraph V} {d d' : ℕ}
    (hdd' : d ≤ d') (hG : MaxDegreeLE G d) : MaxDegreeLE G d' :=
  fun v ↦ (hG v).trans hdd'

end DegreeDiameter

end PortFramework

/- DegreeDiameter.EdgeReduction -/
section PortEdgeReduction

/-
# The edge-reduction construction

This file formalizes the bipartite graph `B(H)` used in Lemma 4.1 of the draft.  An edge between
the two copies of the vertex set records either equality or adjacency in `H`.
-/

open Set

namespace DegreeDiameter

open SimpleGraph

universe u

variable {V : Type u}

/-- Equality or adjacency in a simple graph (the reflexive closure of adjacency). -/
def Linked (H : SimpleGraph V) (x y : V) : Prop :=
  x = y ∨ H.Adj x y

lemma linked_refl (H : SimpleGraph V) (x : V) : Linked H x x :=
  Or.inl rfl

lemma linked_symm {H : SimpleGraph V} {x y : V} : Linked H x y → Linked H y x := by
  rintro (rfl | h)
  · exact linked_refl H x
  · exact Or.inr h.symm

/-- The graph `B(H)` from the draft.  Its two parts are the two summands of `V ⊕ V`. -/
def bipartiteExpansion (H : SimpleGraph V) : SimpleGraph (V ⊕ V) where
  Adj
    | .inl x, .inr y => Linked H x y
    | .inr y, .inl x => Linked H x y
    | _, _ => False
  symm.symm _ _ := by
    grind [Linked, SimpleGraph.adj_comm]
  loopless.irrefl _ := by
    grind

@[simp] lemma bipartiteExpansion_adj_inl_inr (H : SimpleGraph V) (x y : V) :
    (bipartiteExpansion H).Adj (.inl x) (.inr y) ↔ Linked H x y :=
  Iff.rfl

@[simp] lemma bipartiteExpansion_adj_inr_inl (H : SimpleGraph V) (x y : V) :
    (bipartiteExpansion H).Adj (.inr y) (.inl x) ↔ Linked H x y :=
  Iff.rfl

@[simp] lemma bipartiteExpansion_not_adj_inl_inl (H : SimpleGraph V) (x y : V) :
    ¬ (bipartiteExpansion H).Adj (.inl x) (.inl y) := by
  simp [bipartiteExpansion]

@[simp] lemma bipartiteExpansion_not_adj_inr_inr (H : SimpleGraph V) (x y : V) :
    ¬ (bipartiteExpansion H).Adj (.inr x) (.inr y) := by
  simp [bipartiteExpansion]

/-- The edge of `B(H)` represented in the draft by `[x,y]`. -/
def bipartiteEdge (H : SimpleGraph V) (x y : V) (hxy : Linked H x y) :
    (bipartiteExpansion H).edgeSet :=
  ⟨s(.inl x, .inr y), by simpa [SimpleGraph.mem_edgeSet] using hxy⟩

@[simp] lemma bipartiteEdge_val (H : SimpleGraph V) (x y : V) (hxy : Linked H x y) :
    (bipartiteEdge H x y hxy : Sym2 (V ⊕ V)) = s(.inl x, .inr y) :=
  rfl

lemma neighborSet_bipartiteExpansion_inl (H : SimpleGraph V) (x : V) :
    (bipartiteExpansion H).neighborSet (.inl x) =
      Sum.inr '' insert x (H.neighborSet x) := by
  ext y
  cases y <;> simp [SimpleGraph.mem_neighborSet, bipartiteExpansion, Linked, eq_comm]

lemma neighborSet_bipartiteExpansion_inr (H : SimpleGraph V) (x : V) :
    (bipartiteExpansion H).neighborSet (.inr x) =
      Sum.inl '' insert x (H.neighborSet x) := by
  ext y
  cases y <;> simp [SimpleGraph.mem_neighborSet, bipartiteExpansion, Linked, eq_comm,
    SimpleGraph.adj_comm]

lemma ncard_neighborSet_bipartiteExpansion_inl [Finite V]
    (H : SimpleGraph V) (x : V) :
    ((bipartiteExpansion H).neighborSet (.inl x)).ncard =
      (H.neighborSet x).ncard + 1 := by
  rw [neighborSet_bipartiteExpansion_inl, Set.ncard_image_of_injective _ Sum.inr_injective,
    Set.ncard_insert_of_notMem]
  simp

lemma ncard_neighborSet_bipartiteExpansion_inr [Finite V]
    (H : SimpleGraph V) (x : V) :
    ((bipartiteExpansion H).neighborSet (.inr x)).ncard =
      (H.neighborSet x).ncard + 1 := by
  rw [neighborSet_bipartiteExpansion_inr, Set.ncard_image_of_injective _ Sum.inl_injective,
    Set.ncard_insert_of_notMem]
  simp

/-- `B(H)` raises the maximum-degree bound by exactly one. -/
lemma maxDegreeLE_bipartiteExpansion [Finite V] {H : SimpleGraph V} {d : ℕ}
    (hdegree : MaxDegreeLE H d) : MaxDegreeLE (bipartiteExpansion H) (d + 1) := by
  intro x
  cases x with
  | inl x =>
      rw [ncard_neighborSet_bipartiteExpansion_inl]
      exact Nat.add_le_add_right (hdegree x) 1
  | inr x =>
      rw [ncard_neighborSet_bipartiteExpansion_inr]
      exact Nat.add_le_add_right (hdegree x) 1

/-- If every vertex of `H` has degree `Delta`, then the paper's graph `B(H)` has exactly
`|V(H)| * (Delta + 1)` edges. -/
theorem ncard_edgeSet_bipartiteExpansion_of_regular [Finite V]
    (H : SimpleGraph V) (Delta : ℕ)
    (hregular : ∀ x, (H.neighborSet x).ncard = Delta) :
    (bipartiteExpansion H).edgeSet.ncard = Nat.card V * (Delta + 1) := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  let B := bipartiteExpansion H
  letI : DecidableRel B.Adj := Classical.decRel B.Adj
  have hBdegree : ∀ v, B.degree v = Delta + 1 := by
    intro v
    rw [← B.card_neighborSet_eq_degree, Set.fintypeCard_eq_ncard]
    cases v with
    | inl x => exact (ncard_neighborSet_bipartiteExpansion_inl H x).trans (congrArg (.+ 1) (hregular x))
    | inr x => exact (ncard_neighborSet_bipartiteExpansion_inr H x).trans (congrArg (.+ 1) (hregular x))
  have hsum : Fintype.card (V ⊕ V) * (Delta + 1) = 2 * B.edgeFinset.card := by
    simpa [hBdegree] using B.sum_degrees_eq_twice_card_edges
  have htwice : 2 * (Nat.card V * (Delta + 1)) = 2 * B.edgeFinset.card := by
    calc
      2 * (Nat.card V * (Delta + 1)) = Fintype.card (V ⊕ V) * (Delta + 1) := by
        rw [Nat.card_eq_fintype_card]
        simp [Fintype.card_sum, two_mul, add_mul]
      _ = 2 * B.edgeFinset.card := hsum
  have hedge : B.edgeFinset.card = Nat.card V * (Delta + 1) := by
    exact Nat.mul_left_cancel zero_lt_two htwice.symm
  calc
    B.edgeSet.ncard = Nat.card B.edgeSet := (Nat.card_coe_set_eq _).symm
    _ = B.edgeFinset.card := by
      rw [Nat.card_eq_fintype_card, ← B.edgeFinset_card]
    _ = Nat.card V * (Delta + 1) := hedge

/-- Every edge of `B(H)` has a unique orientation from the left part to the right part. -/
lemma exists_eq_bipartiteEdge (H : SimpleGraph V) (e : (bipartiteExpansion H).edgeSet) :
    ∃ x y, ∃ hxy : Linked H x y, e = bipartiteEdge H x y hxy := by
  rcases e with ⟨e, he⟩
  induction e with
  | _ u v =>
      cases u with
      | inl x =>
          cases v with
          | inl y => simp [SimpleGraph.mem_edgeSet, bipartiteExpansion] at he
          | inr y =>
              refine ⟨x, y, ?_, ?_⟩
              · simpa [SimpleGraph.mem_edgeSet, bipartiteExpansion] using he
              · rfl
      | inr y =>
          cases v with
          | inl x =>
              refine ⟨x, y, ?_, ?_⟩
              · simpa [SimpleGraph.mem_edgeSet, bipartiteExpansion] using he
              · apply Subtype.ext
                simp [bipartiteEdge]
          | inr x => simp [SimpleGraph.mem_edgeSet, bipartiteExpansion] at he

/-- Two represented edges with the same left endpoint have line-graph distance at most one. -/
lemma lineGraph_edist_bipartiteEdge_le_one_of_left
    (H : SimpleGraph V) (a b c : V) (hab : Linked H a b) (hac : Linked H a c) :
    (bipartiteExpansion H).lineGraph.edist
        (bipartiteEdge H a b hab) (bipartiteEdge H a c hac) ≤ 1 := by
  rw [SimpleGraph.edist_le_one_iff_adj_or_eq]
  by_cases hEq : bipartiteEdge H a b hab = bipartiteEdge H a c hac
  · exact Or.inr hEq
  · exact Or.inl <| SimpleGraph.lineGraph_adj_iff_exists.mpr
      ⟨hEq, .inl a, by simp [bipartiteEdge], by simp [bipartiteEdge]⟩

/-- Two represented edges with the same right endpoint have line-graph distance at most one. -/
lemma lineGraph_edist_bipartiteEdge_le_one_of_right
    (H : SimpleGraph V) (a b c : V) (hac : Linked H a c) (hbc : Linked H b c) :
    (bipartiteExpansion H).lineGraph.edist
        (bipartiteEdge H a c hac) (bipartiteEdge H b c hbc) ≤ 1 := by
  rw [SimpleGraph.edist_le_one_iff_adj_or_eq]
  by_cases hEq : bipartiteEdge H a c hac = bipartiteEdge H b c hbc
  · exact Or.inr hEq
  · exact Or.inl <| SimpleGraph.lineGraph_adj_iff_exists.mpr
      ⟨hEq, .inr c, by simp [bipartiteEdge], by simp [bipartiteEdge]⟩

/-- A route permits stationary steps as well as graph edges.  It is indexed by its exact length;
this is the formal counterpart of the padded sequences in the paper's proof of Lemma 4.1. -/
inductive Route (H : SimpleGraph V) : V → V → ℕ → Type u
  | nil (x : V) : Route H x x 0
  | cons {x y z : V} {n : ℕ} (hxy : Linked H x y) (tail : Route H y z n) :
      Route H x z n.succ

namespace Route

def ofWalk (H : SimpleGraph V) {x y : V} : (p : H.Walk x y) → Route H x y p.length
  | .nil => .nil x
  | .cons h p => .cons (Or.inr h) (ofWalk H p)

def stay (H : SimpleGraph V) (x : V) : (n : ℕ) → Route H x x n
  | 0 => .nil x
  | n + 1 => .cons (linked_refl H x) (stay H x n)

/-- Concatenate routes.  The length index is written in this order so the defining equations
reduce without arithmetic casts when recursing through the first route. -/
def append {H : SimpleGraph V} {x y z : V} {m n : ℕ} :
    Route H x y m → Route H y z n → Route H x z (n + m)
  | .nil _, q => q
  | .cons h p, q => .cons h (append p q)

/-- Pad an ordinary graph walk by stationary steps to any prescribed larger length. -/
def padWalk (H : SimpleGraph V) {x y : V} (p : H.Walk x y) (k : ℕ)
    (hp : p.length ≤ k) : Route H x y k := by
  have hlen : (k - p.length) + p.length = k := Nat.sub_add_cancel hp
  exact hlen ▸ append (ofWalk H p) (stay H y (k - p.length))

end Route

mutual

/-- Follow a route by first replacing the left coordinate of a represented bipartite edge. -/
def zigFirst (H : SimpleGraph V) {x y : V} {n : ℕ} (p : Route H x y n)
    (a : V) (ha : Linked H a x) : (bipartiteExpansion H).edgeSet :=
  match p with
  | .nil _ => bipartiteEdge H a x ha
  | .cons h tail => zigSecond H tail x (linked_symm h)

/-- Follow a route by first replacing the right coordinate of a represented bipartite edge. -/
def zigSecond (H : SimpleGraph V) {x y : V} {n : ℕ} (p : Route H x y n)
    (b : V) (hb : Linked H x b) : (bipartiteExpansion H).edgeSet :=
  match p with
  | .nil _ => bipartiteEdge H x b hb
  | .cons h tail => zigFirst H tail x h

end

theorem zig_terminal (H : SimpleGraph V) {x y : V} {n : ℕ} (p : Route H x y n) :
    (∀ a (ha : Linked H a x),
      (Even n → ∃ a', ∃ ha' : Linked H a' y,
        zigFirst H p a ha = bipartiteEdge H a' y ha') ∧
      (Odd n → ∃ b', ∃ hb' : Linked H y b',
        zigFirst H p a ha = bipartiteEdge H y b' hb')) ∧
    (∀ b (hb : Linked H x b),
      (Even n → ∃ b', ∃ hb' : Linked H y b',
        zigSecond H p b hb = bipartiteEdge H y b' hb') ∧
      (Odd n → ∃ a', ∃ ha' : Linked H a' y,
        zigSecond H p b hb = bipartiteEdge H a' y ha')) := by
  induction p with
  | nil x =>
      constructor
      · intro a ha
        constructor
        · intro _
          exact ⟨a, ha, rfl⟩
        · intro hn
          simp at hn
      · intro b hb
        constructor
        · intro _
          exact ⟨b, hb, rfl⟩
        · intro hn
          simp at hn
  | @cons x x' y n hxx' tail ih =>
      constructor
      · intro a ha
        constructor
        · intro hn
          have hn' : Odd n := Nat.not_even_iff_odd.mp (Nat.even_add_one.mp hn)
          simpa [zigFirst] using (ih.2 x (linked_symm hxx')).2 hn'
        · intro hn
          have hn' : Even n := Nat.not_odd_iff_even.mp (Nat.odd_add_one.mp hn)
          simpa [zigFirst] using (ih.2 x (linked_symm hxx')).1 hn'
      · intro b hb
        constructor
        · intro hn
          have hn' : Odd n := Nat.not_even_iff_odd.mp (Nat.even_add_one.mp hn)
          simpa [zigSecond] using (ih.1 x hxx').2 hn'
        · intro hn
          have hn' : Even n := Nat.not_odd_iff_even.mp (Nat.odd_add_one.mp hn)
          simpa [zigSecond] using (ih.1 x hxx').1 hn'

theorem zigFirst_of_even (H : SimpleGraph V) {x y : V} {n : ℕ}
    (p : Route H x y n) (a : V) (ha : Linked H a x) (hn : Even n) :
    ∃ a', ∃ ha' : Linked H a' y, zigFirst H p a ha = bipartiteEdge H a' y ha' :=
  ((zig_terminal H p).1 a ha).1 hn

theorem zigFirst_of_odd (H : SimpleGraph V) {x y : V} {n : ℕ}
    (p : Route H x y n) (a : V) (ha : Linked H a x) (hn : Odd n) :
    ∃ b', ∃ hb' : Linked H y b', zigFirst H p a ha = bipartiteEdge H y b' hb' :=
  ((zig_terminal H p).1 a ha).2 hn

/-- Both alternating coordinate routes cost no more than one line-graph step per route step. -/
theorem edist_zig_le (H : SimpleGraph V) {x y : V} {n : ℕ} (p : Route H x y n) :
    (∀ a (ha : Linked H a x),
      (bipartiteExpansion H).lineGraph.edist
        (bipartiteEdge H a x ha) (zigFirst H p a ha) ≤ (n : ℕ∞)) ∧
    (∀ b (hb : Linked H x b),
      (bipartiteExpansion H).lineGraph.edist
        (bipartiteEdge H x b hb) (zigSecond H p b hb) ≤ (n : ℕ∞)) := by
  induction p with
  | nil x =>
      constructor <;> intro z hz <;> simp [zigFirst, zigSecond]
  | @cons x x' y n hxx' tail ih =>
      constructor
      · intro a ha
        calc
          (bipartiteExpansion H).lineGraph.edist
              (bipartiteEdge H a x ha) (zigFirst H (.cons hxx' tail) a ha)
              ≤ (bipartiteExpansion H).lineGraph.edist
                  (bipartiteEdge H a x ha) (bipartiteEdge H x' x (linked_symm hxx')) +
                (bipartiteExpansion H).lineGraph.edist
                  (bipartiteEdge H x' x (linked_symm hxx'))
                  (zigSecond H tail x (linked_symm hxx')) :=
            SimpleGraph.edist_triangle
          _ ≤ 1 + (n : ℕ∞) := add_le_add
            (lineGraph_edist_bipartiteEdge_le_one_of_right H a x' x ha (linked_symm hxx'))
            (ih.2 x (linked_symm hxx'))
          _ = ((n + 1 : ℕ) : ℕ∞) := by simp [add_comm]
      · intro b hb
        calc
          (bipartiteExpansion H).lineGraph.edist
              (bipartiteEdge H x b hb) (zigSecond H (.cons hxx' tail) b hb)
              ≤ (bipartiteExpansion H).lineGraph.edist
                  (bipartiteEdge H x b hb) (bipartiteEdge H x x' hxx') +
                (bipartiteExpansion H).lineGraph.edist
                  (bipartiteEdge H x x' hxx') (zigFirst H tail x hxx') :=
            SimpleGraph.edist_triangle
          _ ≤ 1 + (n : ℕ∞) := add_le_add
            (lineGraph_edist_bipartiteEdge_le_one_of_left H x b x' hb hxx')
            (ih.1 x hxx')
          _ = ((n + 1 : ℕ) : ℕ∞) := by simp [add_comm]

theorem edist_zigFirst_le (H : SimpleGraph V) {x y : V} {n : ℕ}
    (p : Route H x y n) (a : V) (ha : Linked H a x) :
    (bipartiteExpansion H).lineGraph.edist
        (bipartiteEdge H a x ha) (zigFirst H p a ha) ≤ (n : ℕ∞) :=
  (edist_zig_le H p).1 a ha

/-- A diameter bound in `H` supplies an exact-length padded route between every two vertices. -/
lemma nonempty_route_of_ediam_le (H : SimpleGraph V) (k : ℕ)
    (hdiam : H.ediam ≤ (k : ℕ∞)) (x y : V) : Nonempty (Route H x y k) := by
  have hdist : H.edist x y ≤ (k : ℕ∞) := SimpleGraph.edist_le_ediam.trans hdiam
  have hfinite : H.edist x y ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.coe_ne_top k) hdist
  obtain ⟨p, hp⟩ := SimpleGraph.exists_walk_of_edist_ne_top hfinite
  have hlength : p.length ≤ k := by
    rw [← hp] at hdist
    exact_mod_cast hdist
  exact ⟨Route.padWalk H p k hlength⟩

/-- Pointwise distance form of Lemma 4.1. -/
lemma lineGraph_edist_bipartiteExpansion_le (H : SimpleGraph V) (k : ℕ)
    (hdiam : H.ediam ≤ (k : ℕ∞))
    (e f : (bipartiteExpansion H).edgeSet) :
    (bipartiteExpansion H).lineGraph.edist e f ≤ ((k + 1 : ℕ) : ℕ∞) := by
  obtain ⟨a, b, hab, rfl⟩ := exists_eq_bipartiteEdge H e
  obtain ⟨c, d, hcd, rfl⟩ := exists_eq_bipartiteEdge H f
  by_cases hk : Even k
  · obtain ⟨p⟩ := nonempty_route_of_ediam_le H k hdiam b d
    obtain ⟨u, hud, hterminal⟩ := zigFirst_of_even H p a hab hk
    calc
      (bipartiteExpansion H).lineGraph.edist
          (bipartiteEdge H a b hab) (bipartiteEdge H c d hcd)
          ≤ (bipartiteExpansion H).lineGraph.edist
              (bipartiteEdge H a b hab) (zigFirst H p a hab) +
            (bipartiteExpansion H).lineGraph.edist
              (zigFirst H p a hab) (bipartiteEdge H c d hcd) :=
        SimpleGraph.edist_triangle
      _ ≤ (k : ℕ∞) + 1 := add_le_add (edist_zigFirst_le H p a hab) <| by
        rw [hterminal]
        exact lineGraph_edist_bipartiteEdge_le_one_of_right H u c d hud hcd
      _ = ((k + 1 : ℕ) : ℕ∞) := by simp
  · have hk' : Odd k := Nat.not_even_iff_odd.mp hk
    obtain ⟨p⟩ := nonempty_route_of_ediam_le H k hdiam b c
    obtain ⟨u, hcu, hterminal⟩ := zigFirst_of_odd H p a hab hk'
    calc
      (bipartiteExpansion H).lineGraph.edist
          (bipartiteEdge H a b hab) (bipartiteEdge H c d hcd)
          ≤ (bipartiteExpansion H).lineGraph.edist
              (bipartiteEdge H a b hab) (zigFirst H p a hab) +
            (bipartiteExpansion H).lineGraph.edist
              (zigFirst H p a hab) (bipartiteEdge H c d hcd) :=
        SimpleGraph.edist_triangle
      _ ≤ (k : ℕ∞) + 1 := add_le_add (edist_zigFirst_le H p a hab) <| by
        rw [hterminal]
        exact lineGraph_edist_bipartiteEdge_le_one_of_left H c u d hcu hcd
      _ = ((k + 1 : ℕ) : ℕ∞) := by simp

/-- Lemma 4.1 in bounded-diameter form.  This formulation also handles empty vertex and edge
types without adding nonemptiness hypotheses. -/
theorem lemma_4_1_le (H : SimpleGraph V) (k : ℕ) (hdiam : H.ediam ≤ (k : ℕ∞)) :
    (bipartiteExpansion H).lineGraph.ediam ≤ ((k + 1 : ℕ) : ℕ∞) :=
  SimpleGraph.ediam_le_of_edist_le (lineGraph_edist_bipartiteExpansion_le H k hdiam)

end DegreeDiameter

end PortEdgeReduction

/- DegreeDiameter.MooreBound -/
section PortMooreBound

/-
# The exact Moore bound

This module proves the standard breadth-first (Moore) bound used in the
degree--diameter problem.  Starting from a root, a shortest route has at most
`d` choices for its first edge and at most `d - 1` choices for each later
edge: the edge just traversed cannot immediately be traversed backwards.

The route types below make that argument literal.  In particular, the proof
does not obtain the leading term indirectly from the coarser `(d + 1)^k`
bound in `Framework`.
-/

open Set

namespace DegreeDiameter

open SimpleGraph

universe u

/-- A possible next vertex after traversing `previous -- current`, excluding
the immediate reverse step. -/
def ForwardNeighbor {V : Type u} (G : SimpleGraph V) (previous current : V) :=
  {next : V // G.Adj current next ∧ next ≠ previous}

instance finite_forwardNeighbor {V : Type u} [Finite V] (G : SimpleGraph V)
    (previous current : V) : Finite (ForwardNeighbor G previous current) :=
  Finite.of_injective Subtype.val Subtype.val_injective

/-- An exact-length nonbacktracking continuation, after an initial directed
edge `previous -- current` has already been traversed. -/
def NBContinuation {V : Type u} (G : SimpleGraph V) : V → V → ℕ → Type u
  | _, _, 0 => PUnit
  | previous, current, n + 1 =>
      Σ next : ForwardNeighbor G previous current,
        NBContinuation G current next.1 n

instance finite_nbContinuation {V : Type u} [Finite V] (G : SimpleGraph V)
    (previous current : V) (n : ℕ) : Finite (NBContinuation G previous current n) := by
  classical
  induction n generalizing previous current with
  | zero => exact inferInstanceAs (Finite PUnit)
  | succ n ih =>
      change Finite
        (Σ next : ForwardNeighbor G previous current,
          NBContinuation G current next.1 n)
      letI (next : ForwardNeighbor G previous current) :
          Finite (NBContinuation G current next.1 n) := ih current next.1
      letI : Fintype (ForwardNeighbor G previous current) := Fintype.ofFinite _
      letI (next : ForwardNeighbor G previous current) :
          Fintype (NBContinuation G current next.1 n) := Fintype.ofFinite _
      infer_instance

/-- An exact-length nonbacktracking route beginning at `root`. -/
def ExactNBRoute {V : Type u} (G : SimpleGraph V) (root : V) : ℕ → Type u
  | 0 => PUnit
  | n + 1 => Σ first : G.neighborSet root, NBContinuation G root first.1 n

instance finite_exactNBRoute {V : Type u} [Finite V] (G : SimpleGraph V)
    (root : V) (n : ℕ) : Finite (ExactNBRoute G root n) := by
  classical
  cases n with
  | zero => exact inferInstanceAs (Finite PUnit)
  | succ n =>
      change Finite (Σ first : G.neighborSet root, NBContinuation G root first.1 n)
      letI (first : G.neighborSet root) :
          Finite (NBContinuation G root first.1 n) := finite_nbContinuation G root first.1 n
      letI : Fintype (G.neighborSet root) := Fintype.ofFinite _
      letI (first : G.neighborSet root) :
          Fintype (NBContinuation G root first.1 n) := Fintype.ofFinite _
      infer_instance

/-- The last vertex of a nonbacktracking continuation. -/
def NBContinuation.endpoint {V : Type u} (G : SimpleGraph V) :
    {previous current : V} → {n : ℕ} → NBContinuation G previous current n → V
  | _, current, 0, _ => current
  | _, _, _ + 1, route => endpoint G route.2

/-- The last vertex of an exact nonbacktracking route. -/
def ExactNBRoute.endpoint {V : Type u} (G : SimpleGraph V) (root : V) :
    {n : ℕ} → ExactNBRoute G root n → V
  | 0, _ => root
  | _ + 1, route => NBContinuation.endpoint G route.2

lemma ExactNBRoute.endpoint_cast {V : Type u} (G : SimpleGraph V) (root : V)
    {m n : ℕ} (h : m = n) (route : ExactNBRoute G root m) :
    ExactNBRoute.endpoint G root (h ▸ route) =
      ExactNBRoute.endpoint G root route := by
  cases h
  rfl

/-- Convert a path beginning at `current`, which avoids `previous`, into the
corresponding nonbacktracking continuation. -/
def NBContinuation.ofPath {V : Type u} {G : SimpleGraph V} :
    {previous current target : V} → (p : G.Walk current target) →
      p.IsPath → previous ∉ p.support → NBContinuation G previous current p.length
  | _, _, _, .nil, _, _ => PUnit.unit
  | previous, current, target, .cons hadj tail, hp, hprevious =>
      ⟨⟨_, hadj, fun h ↦ hprevious (by
          simp only [Walk.support_cons, List.mem_cons]
          exact Or.inr (by simpa [h] using tail.start_mem_support))⟩,
        ofPath tail hp.of_cons ((Walk.cons_isPath_iff hadj tail).mp hp).2⟩

lemma NBContinuation.endpoint_ofPath {V : Type u} {G : SimpleGraph V}
    {previous current target : V} (p : G.Walk current target) (hp : p.IsPath)
    (hprevious : previous ∉ p.support) :
    (NBContinuation.ofPath p hp hprevious).endpoint G = target := by
  induction p generalizing previous with
  | nil => rfl
  | @cons current next target hadj tail ih =>
      simp only [NBContinuation.ofPath]
      exact ih hp.of_cons ((Walk.cons_isPath_iff hadj tail).mp hp).2

/-- Every path gives an exact nonbacktracking route with the same endpoint. -/
def ExactNBRoute.ofPath {V : Type u} {G : SimpleGraph V} {root target : V}
    (p : G.Walk root target) (hp : p.IsPath) : ExactNBRoute G root p.length :=
  match p with
  | .nil => PUnit.unit
  | .cons hadj tail =>
      ⟨⟨_, hadj⟩,
        NBContinuation.ofPath tail hp.of_cons
          ((Walk.cons_isPath_iff hadj tail).mp hp).2⟩

lemma ExactNBRoute.endpoint_ofPath {V : Type u} {G : SimpleGraph V}
    {root target : V} (p : G.Walk root target) (hp : p.IsPath) :
    (ExactNBRoute.ofPath p hp).endpoint G root = target := by
  cases p with
  | nil => rfl
  | @cons root next target hadj tail =>
      exact NBContinuation.endpoint_ofPath tail hp.of_cons
        ((Walk.cons_isPath_iff hadj tail).mp hp).2

/-- Removing the vertex just left leaves at most `d - 1` choices. -/
lemma natCard_forwardNeighbor_le {V : Type u} [Finite V] {G : SimpleGraph V}
    {d : ℕ} (hdegree : MaxDegreeLE G d) {previous current : V}
    (hpc : G.Adj previous current) :
    Nat.card (ForwardNeighbor G previous current) ≤ d - 1 := by
  change ({next : V | G.Adj current next ∧ next ≠ previous} : Set V).ncard ≤ d - 1
  have hset : {next : V | G.Adj current next ∧ next ≠ previous} =
      G.neighborSet current \ {previous} := by
    ext next
    simp [and_comm]
  rw [hset, Set.ncard_sdiff_singleton_of_mem]
  · exact Nat.sub_le_sub_right (hdegree current) 1
  · exact hpc.symm

/-- There are at most `(d - 1)^n` nonbacktracking continuations of length
`n` after a directed edge. -/
lemma natCard_nbContinuation_le {V : Type u} [Finite V] {G : SimpleGraph V}
    {d : ℕ} (hdegree : MaxDegreeLE G d) {previous current : V}
    (hpc : G.Adj previous current) (n : ℕ) :
    Nat.card (NBContinuation G previous current n) ≤ (d - 1) ^ n := by
  classical
  induction n generalizing previous current with
  | zero => simp [NBContinuation]
  | succ n ih =>
      letI : Fintype (ForwardNeighbor G previous current) := Fintype.ofFinite _
      letI (next : ForwardNeighbor G previous current) :
          Fintype (NBContinuation G current next.1 n) := Fintype.ofFinite _
      rw [show Nat.card (NBContinuation G previous current (n + 1)) =
          ∑ next : ForwardNeighbor G previous current,
            Nat.card (NBContinuation G current next.1 n) by
        change Nat.card
            (Σ next : ForwardNeighbor G previous current,
              NBContinuation G current next.1 n) = _
        rw [Nat.card_sigma]]
      calc
        ∑ next : ForwardNeighbor G previous current,
            Nat.card (NBContinuation G current next.1 n)
            ≤ ∑ _next : ForwardNeighbor G previous current, (d - 1) ^ n := by
              apply Finset.sum_le_sum
              intro next _
              exact ih next.2.1
        _ = Nat.card (ForwardNeighbor G previous current) * (d - 1) ^ n := by
              simp
        _ ≤ (d - 1) * (d - 1) ^ n :=
              Nat.mul_le_mul_right ((d - 1) ^ n)
                (natCard_forwardNeighbor_le hdegree hpc)
        _ = (d - 1) ^ (n + 1) := by rw [pow_succ, Nat.mul_comm]

/-- The distance-`n+1` route layer has at most `d(d-1)^n` members. -/
lemma natCard_exactNBRoute_succ_le {V : Type u} [Finite V] {G : SimpleGraph V}
    {d : ℕ} (hdegree : MaxDegreeLE G d) (root : V) (n : ℕ) :
    Nat.card (ExactNBRoute G root (n + 1)) ≤ d * (d - 1) ^ n := by
  classical
  letI : Fintype (G.neighborSet root) := Fintype.ofFinite _
  letI (first : G.neighborSet root) :
      Fintype (NBContinuation G root first.1 n) := Fintype.ofFinite _
  rw [show Nat.card (ExactNBRoute G root (n + 1)) =
      ∑ first : G.neighborSet root,
        Nat.card (NBContinuation G root first.1 n) by
    change Nat.card
        (Σ first : G.neighborSet root, NBContinuation G root first.1 n) = _
    rw [Nat.card_sigma]]
  calc
    ∑ first : G.neighborSet root,
        Nat.card (NBContinuation G root first.1 n)
        ≤ ∑ _first : G.neighborSet root, (d - 1) ^ n := by
          apply Finset.sum_le_sum
          intro first _
          exact natCard_nbContinuation_le hdegree first.2 n
    _ = Nat.card (G.neighborSet root) * (d - 1) ^ n := by simp
    _ ≤ d * (d - 1) ^ n := by
          apply Nat.mul_le_mul_right
          simpa [Nat.card_coe_set_eq] using hdegree root

/-- Routes of length at most `k`, presented recursively as the disjoint union
of the earlier layers and the exact length-`k` layer. -/
def BoundedNBRoute {V : Type u} (G : SimpleGraph V) (root : V) : ℕ → Type u
  | 0 => PUnit
  | k + 1 => BoundedNBRoute G root k ⊕ ExactNBRoute G root (k + 1)

instance finite_boundedNBRoute {V : Type u} [Finite V] (G : SimpleGraph V)
    (root : V) (k : ℕ) : Finite (BoundedNBRoute G root k) := by
  classical
  induction k with
  | zero => exact inferInstanceAs (Finite PUnit)
  | succ k ih =>
      change Finite (BoundedNBRoute G root k ⊕ ExactNBRoute G root (k + 1))
      letI : Finite (BoundedNBRoute G root k) := ih
      letI : Fintype (BoundedNBRoute G root k) := Fintype.ofFinite _
      letI : Fintype (ExactNBRoute G root (k + 1)) := Fintype.ofFinite _
      infer_instance

/-- Endpoint of a route of length at most `k`. -/
def BoundedNBRoute.endpoint {V : Type u} (G : SimpleGraph V) (root : V) :
    {k : ℕ} → BoundedNBRoute G root k → V
  | 0, _ => root
  | _ + 1, .inl route => endpoint G root route
  | _ + 1, .inr route => route.endpoint G root

/-- A path of length at most `k` belongs to the bounded route type and keeps
its endpoint.  This is the formal shortest/nonbacktracking-route step in the
standard Moore-bound proof. -/
lemma exists_boundedNBRoute_endpoint_of_path {V : Type u} {G : SimpleGraph V}
    {root target : V} (p : G.Walk root target) (hp : p.IsPath) {k : ℕ}
    (hlength : p.length ≤ k) :
    ∃ route : BoundedNBRoute G root k, route.endpoint G root = target := by
  induction k with
  | zero =>
      have hz : p.length = 0 := Nat.eq_zero_of_le_zero hlength
      have hrt : root = target := p.eq_of_length_eq_zero hz
      subst target
      exact ⟨PUnit.unit, rfl⟩
  | succ k ih =>
      by_cases hle : p.length ≤ k
      · obtain ⟨route, hroute⟩ := ih hle
        exact ⟨Sum.inl route, hroute⟩
      · have heq : p.length = k + 1 := by omega
        let route : ExactNBRoute G root (k + 1) :=
          heq ▸ ExactNBRoute.ofPath p hp
        refine ⟨Sum.inr route, ?_⟩
        change ExactNBRoute.endpoint G root route = target
        rw [show ExactNBRoute.endpoint G root route =
            ExactNBRoute.endpoint G root (ExactNBRoute.ofPath p hp) by
          exact ExactNBRoute.endpoint_cast G root heq (ExactNBRoute.ofPath p hp)]
        exact ExactNBRoute.endpoint_ofPath p hp

/-- The recursive bounded-route type has exactly the cardinality estimate in
the Moore expression. -/
lemma natCard_boundedNBRoute_le {V : Type u} [Finite V] {G : SimpleGraph V}
    {d : ℕ} (hdegree : MaxDegreeLE G d) (root : V) (k : ℕ) :
    Nat.card (BoundedNBRoute G root k) ≤ mooreBound k d := by
  induction k with
  | zero => simp [BoundedNBRoute, mooreBound]
  | succ k ih =>
      change Nat.card
          (BoundedNBRoute G root k ⊕ ExactNBRoute G root (k + 1)) ≤
        mooreBound (k + 1) d
      rw [Nat.card_sum]
      calc
        Nat.card (BoundedNBRoute G root k) +
            Nat.card (ExactNBRoute G root (k + 1))
            ≤ mooreBound k d + d * (d - 1) ^ k :=
              Nat.add_le_add ih (natCard_exactNBRoute_succ_le hdegree root k)
        _ = mooreBound (k + 1) d := by
              simp [mooreBound, Finset.sum_range_succ, Nat.mul_add, Nat.add_assoc]

/-- The exact Moore expression is bounded by the convenient leading-term
comparison `(d + 1)^k`.  This lemma is used only after the exact graph bound
has been established. -/
lemma mooreBound_le_add_one_pow (k d : ℕ) : mooreBound k d ≤ (d + 1) ^ k := by
  induction k with
  | zero => simp [mooreBound]
  | succ k ih =>
      rw [show mooreBound (k + 1) d =
          mooreBound k d + d * (d - 1) ^ k by
        simp [mooreBound, Finset.sum_range_succ, Nat.mul_add, Nat.add_assoc]]
      calc
        mooreBound k d + d * (d - 1) ^ k ≤
            (d + 1) ^ k + d * (d + 1) ^ k := by
          exact Nat.add_le_add ih
            (Nat.mul_le_mul_left d (Nat.pow_le_pow_left (by omega) k))
        _ = (d + 1) ^ (k + 1) := by
          rw [pow_succ, Nat.mul_add, Nat.mul_one,
            Nat.mul_comm d ((d + 1) ^ k), Nat.add_comm]

/-- Exact Moore bound for every finite graph of maximum degree at most `d`
and extended diameter at most `k`. -/
theorem natCard_le_mooreBound_of_ediam_le {V : Type u} [Finite V] [Nonempty V]
    {G : SimpleGraph V} {d k : ℕ} (hdegree : MaxDegreeLE G d)
    (hdiam : G.ediam ≤ (k : ℕ∞)) : Nat.card V ≤ mooreBound k d := by
  let root : V := Classical.ofNonempty
  have hsurj : Function.Surjective
      (BoundedNBRoute.endpoint G root (k := k)) := by
    intro target
    have hdist : G.edist root target ≤ (k : ℕ∞) :=
      SimpleGraph.edist_le_ediam.trans hdiam
    have hfinite : G.edist root target ≠ ⊤ :=
      ne_top_of_le_ne_top (ENat.coe_ne_top k) hdist
    have hreachable : G.Reachable root target :=
      SimpleGraph.reachable_of_edist_ne_top hfinite
    obtain ⟨p, hp, hlengthDist⟩ := hreachable.exists_path_of_dist
    have hlength : p.length ≤ k := by
      rw [hlengthDist]
      exact_mod_cast hreachable.coe_dist_eq_edist.trans_le hdist
    exact exists_boundedNBRoute_endpoint_of_path p hp hlength
  calc
    Nat.card V ≤ Nat.card (BoundedNBRoute G root k) :=
      Nat.card_le_card_of_surjective _ hsurj
    _ ≤ mooreBound k d := natCard_boundedNBRoute_le hdegree root k

/-- The exact Moore bound, including the empty vertex type. -/
theorem natCard_le_mooreBound_of_ediam_le' {V : Type u} [Finite V]
    {G : SimpleGraph V} {d k : ℕ} (hdegree : MaxDegreeLE G d)
    (hdiam : G.ediam ≤ (k : ℕ∞)) : Nat.card V ≤ mooreBound k d := by
  cases isEmpty_or_nonempty V
  · simp
  · exact natCard_le_mooreBound_of_ediam_le hdegree hdiam

end DegreeDiameter

end PortMooreBound

/- DegreeDiameter.CommonBasis -/
section PortCommonBasis

/-
# A common ordered basis for two complete flags

This file isolates and proves the standard common-basis fact used as the first
step in the proof of Lemma 2.1 in Cames van Batenburg--Korsky.  It is not an
assumption: `common_apartment` constructs the basis and permutation, and
`common_basis_orderings` spells out the two prefix-span formulas
from the paper.
-/

open Module

namespace DegreeDiameter

variable (K V : Type*) [DivisionRing K] [AddCommGroup V] [Module K V]

/-- A complete flag in an `n`-dimensional vector space, indexed by its ranks
`0, ..., n`. Both strictness and the rank condition are recorded explicitly,
ruling out degenerate chains. -/
structure CompleteFlag (n : ℕ) where
  space : Fin (n + 1) → Submodule K V
  strictMono_space : StrictMono space
  finrank_space : ∀ i, Module.finrank K (space i) = i
  space_zero : space 0 = ⊥
  space_last : space (Fin.last n) = ⊤

namespace CompleteFlag

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
  {n : ℕ}

instance : CoeFun (CompleteFlag K V n) (fun _ ↦ Fin (n + 1) → Submodule K V) :=
  ⟨CompleteFlag.space⟩


theorem ext {F G : CompleteFlag K V n} (h : ∀ i, F i = G i) : F = G := by
  cases F with
  | mk spaceF strictF rankF zeroF lastF =>
    cases G with
    | mk spaceG strictG rankG zeroG lastG =>
      have hspace : spaceF = spaceG := funext h
      cases hspace
      rfl

/-- The complete flag of prefix spans of an ordered basis. -/
noncomputable def ofBasis (b : Basis (Fin n) K V) : CompleteFlag K V n where
  space := b.flag
  strictMono_space := b.flag_strictMono
  finrank_space := by
    intro i
    classical
    rw [Module.Basis.flag,
      finrank_span_set_eq_card ((b.linearIndependent.linearIndepOn _).id_image)]
    rw [Set.toFinset_image, Finset.card_image_of_injective _ b.injective]
    rw [Set.toFinset_setOf]
    change (Finset.filter (fun x : Fin n ↦ x.val < i.val) Finset.univ).card = i.val
    rw [Fin.card_filter_val_lt,
      Nat.min_eq_right (Nat.le_of_lt_succ i.isLt)]
  space_zero := b.flag_zero
  space_last := b.flag_last

end CompleteFlag

/-- The set of entries appearing before rank `i` in an ordering `σ`. -/
def PrefixSet {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : Fin (n + 1)) : Set (Fin n) :=
  σ '' {j | j.castSucc < i}

theorem ofBasis_reindex_apply {n : ℕ} (b : Basis (Fin n) K V)
    (σ : Equiv.Perm (Fin n)) (i : Fin (n + 1)) :
    CompleteFlag.ofBasis (b.reindex σ.symm) i =
      Submodule.span K (b '' PrefixSet σ i) := by
  change (b.reindex σ.symm).flag i = _
  simp [Module.Basis.flag, PrefixSet, Module.Basis.coe_reindex,
    Set.image_image]

/-- Any two complete flags lie in a common apartment: after choosing one
ordered basis, the second flag is obtained by permuting that same basis.
The inverse in `π.symm` compensates for Mathlib's convention for `Basis.reindex`. -/
theorem common_apartment {n : ℕ} (F F' : CompleteFlag K V n) :
    ∃ (b : Basis (Fin n) K V) (π : Equiv.Perm (Fin n)),
      F = CompleteFlag.ofBasis b ∧
      F' = CompleteFlag.ofBasis (b.reindex π.symm) := by
  classical
  cases n with
  | zero =>
      have htop_bot : (⊤ : Submodule K V) = ⊥ := by
        rw [← F.space_last]
        have hlast : (Fin.last 0 : Fin 1) = 0 := Fin.eq_zero _
        rw [hlast, F.space_zero]
      letI : Subsingleton V :=
        ⟨fun x y ↦ by
          have hx : x ∈ (⊥ : Submodule K V) := by
            rw [← htop_bot]
            exact Submodule.mem_top
          have hy : y ∈ (⊥ : Submodule K V) := by
            rw [← htop_bot]
            exact Submodule.mem_top
          exact ((Submodule.mem_bot K).mp hx).trans ((Submodule.mem_bot K).mp hy).symm⟩
      let b : Basis (Fin 0) K V := Basis.empty V
      refine ⟨b, 1, ?_, ?_⟩
      · apply CompleteFlag.ext
        intro i
        have hi : i = 0 := Fin.eq_zero _
        subst i
        rw [F.space_zero]
        exact (CompleteFlag.ofBasis b).space_zero.symm
      · apply CompleteFlag.ext
        intro i
        have hi : i = 0 := Fin.eq_zero _
        subst i
        rw [F'.space_zero]
        exact (CompleteFlag.ofBasis (b.reindex (1 : Equiv.Perm (Fin 0)).symm)).space_zero.symm
  | succ m =>
      have hfin : Module.finrank K V = m + 1 := by
        rw [← finrank_top K V, ← F.space_last]
        simpa using F.finrank_space (Fin.last (m + 1))
      letI : FiniteDimensional K V :=
        FiniteDimensional.of_finrank_pos (by omega)
      let P : Fin (m + 1) → Fin (m + 1) → Prop := fun i j ↦
        ∃ x : V, x ∈ F i.succ ∧ x ∈ F' j.succ ∧ x ∉ F i.castSucc
      have hP : ∀ i, ∃ j, P i j := by
        intro i
        obtain ⟨x, hxi, hxni⟩ :=
          SetLike.exists_of_lt (F.strictMono_space Fin.castSucc_lt_succ)
        refine ⟨Fin.last m, x, hxi, ?_, hxni⟩
        rw [show (Fin.last m).succ = Fin.last (m + 1) by
          ext
          simp, F'.space_last]
        exact Submodule.mem_top
      let σf : Fin (m + 1) → Fin (m + 1) := fun i ↦ Fin.find (P i) (hP i)
      have hσ_spec : ∀ i, P i (σf i) := fun i ↦ Fin.find_spec (hP i)
      have hP_iff (i j : Fin (m + 1)) : P i j ↔ σf i ≤ j := by
        constructor
        · exact Fin.find_le_of_pos (hP i)
        · intro hij
          obtain ⟨x, hxi, hxj, hxni⟩ := hσ_spec i
          refine ⟨x, hxi, ?_, hxni⟩
          exact F'.strictMono_space.monotone ((Fin.succ_le_succ_iff).2 hij) hxj
      let v : Fin (m + 1) → V := fun i ↦ Classical.choose (hσ_spec i)
      have hv_left (i) : v i ∈ F i.succ := (Classical.choose_spec (hσ_spec i)).1
      have hv_right (i) : v i ∈ F' (σf i).succ :=
        (Classical.choose_spec (hσ_spec i)).2.1
      have hv_not (i) : v i ∉ F i.castSucc :=
        (Classical.choose_spec (hσ_spec i)).2.2
      have hstep (i j : Fin (m + 1)) :
          Module.finrank K ↥(F i.succ ⊓ F' j.succ) =
            Module.finrank K ↥(F i.castSucc ⊓ F' j.succ) +
              if σf i ≤ j then 1 else 0 := by
        by_cases hij : σf i ≤ j
        · rw [if_pos hij]
          have hp : P i j := (hP_iff i j).2 hij
          obtain ⟨x, hxFi, hxFj, hxnot⟩ := hp
          let A : Submodule K V := F i.castSucc ⊓ F' j.succ
          let B : Submodule K V := F i.succ ⊓ F' j.succ
          have hABle : A ≤ B := inf_le_inf_right _ (F.strictMono_space.monotone
            (Fin.castSucc_lt_succ.le))
          have hABlt : A < B := lt_of_le_of_ne hABle (by
            intro hEq
            have hxA : x ∈ A := hEq ▸ show x ∈ B from ⟨hxFi, hxFj⟩
            exact hxnot hxA.1)
          have hrlt : Module.finrank K A < Module.finrank K B :=
            Submodule.finrank_lt_finrank_of_lt hABlt
          have hsup_le : F i.castSucc ⊔ B ≤ F i.succ :=
            sup_le (F.strictMono_space.monotone Fin.castSucc_lt_succ.le) inf_le_left
          have hinf : F i.castSucc ⊓ B = A := by
            apply le_antisymm
            · intro y hy
              exact ⟨hy.1, hy.2.2⟩
            · intro y hy
              exact ⟨hy.1, ⟨F.strictMono_space.monotone
                Fin.castSucc_lt_succ.le hy.1, hy.2⟩⟩
          have hdim := Submodule.finrank_sup_add_finrank_inf_eq (F i.castSucc) B
          rw [hinf] at hdim
          have hsupdim : Module.finrank K ↥(F i.castSucc ⊔ B) ≤ i.val + 1 := by
            calc
              Module.finrank K ↥(F i.castSucc ⊔ B) ≤ Module.finrank K ↥(F i.succ) :=
                Submodule.finrank_mono hsup_le
              _ = i.succ.val := F.finrank_space i.succ
              _ = i.val + 1 := rfl
          have hFidim : Module.finrank K (F i.castSucc) = i.val :=
            F.finrank_space i.castSucc
          change Module.finrank K B = Module.finrank K A + 1
          omega
        · rw [if_neg hij]
          have hnP : ¬P i j := fun hp ↦ hij ((hP_iff i j).1 hp)
          have heq : F i.succ ⊓ F' j.succ = F i.castSucc ⊓ F' j.succ := by
            apply le_antisymm
            · intro x hx
              refine ⟨?_, hx.2⟩
              by_contra hxnot
              exact hnP ⟨x, hx.1, hx.2, hxnot⟩
            · exact inf_le_inf_right _ (F.strictMono_space.monotone
                Fin.castSucc_lt_succ.le)
          rw [heq]
          omega
      let σN : ℕ → ℕ := fun a ↦
        if ha : a < m + 1 then (σf ⟨a, ha⟩).val else 0
      have hsum : ∀ (r : ℕ) (hr : r ≤ m + 1) (j : Fin (m + 1)),
          Module.finrank K ↥(F ⟨r, by omega⟩ ⊓ F' j.succ) =
            ∑ a ∈ Finset.range r, if σN a ≤ j.val then 1 else 0 := by
        intro r
        induction r with
        | zero =>
            intro hr j
            rw [show (⟨0, by omega⟩ : Fin (m + 2)) = 0 by rfl,
              F.space_zero]
            simp
        | succ r ih =>
            intro hr j
            have hrlt : r < m + 1 := hr
            let i : Fin (m + 1) := ⟨r, hrlt⟩
            have hprev := ih (Nat.le_of_succ_le hr) j
            change Module.finrank K ↥(F i.castSucc ⊓ F' j.succ) = _ at hprev
            change Module.finrank K ↥(F i.succ ⊓ F' j.succ) = _
            rw [hstep i j, hprev, Finset.sum_range_succ]
            congr 1
            change (if (σf ⟨r, hrlt⟩).val ≤ j.val then 1 else 0) = _
            have hrm : r ≤ m := by omega
            simp [σN, hrm]
      have hσ_surj : Function.Surjective σf := by
        have hcount (j : Fin (m + 1)) :
            (Finset.univ.filter (fun i : Fin (m + 1) ↦ σf i ≤ j)).card =
              j.val + 1 := by
          have hs := hsum (m + 1) le_rfl j
          have hlast : (⟨m + 1, by omega⟩ : Fin (m + 2)) = Fin.last (m + 1) := by
            apply Fin.ext
            rfl
          rw [hlast, F.space_last, top_inf_eq, F'.finrank_space] at hs
          rw [Finset.card_filter, Finset.sum_fin_eq_sum_range]
          calc
            (∑ i ∈ Finset.range (m + 1),
                if h : i < m + 1 then if σf ⟨i, h⟩ ≤ j then 1 else 0 else 0) =
                ∑ a ∈ Finset.range (m + 1), if σN a ≤ j.val then 1 else 0 := by
              apply Finset.sum_congr rfl
              intro a ha
              have halt : a < m + 1 := Finset.mem_range.mp ha
              have ham : a ≤ m := by omega
              rw [dif_pos halt]
              change (if (σf ⟨a, halt⟩).val ≤ j.val then 1 else 0) = _
              simp [σN, ham]
            _ = j.val + 1 := by simpa using hs.symm
        intro j
        by_contra hno
        have hno' : ∀ i, σf i ≠ j := by
          intro i hij
          exact hno ⟨i, hij⟩
        by_cases hj : j = 0
        · subst j
          have he : Finset.univ.filter (fun i : Fin (m + 1) ↦ σf i ≤ 0) = ∅ := by
            ext i
            simp only [Finset.mem_filter, Finset.mem_univ, true_and,
              Finset.notMem_empty, iff_false]
            intro hi
            exact hno' i (le_antisymm hi (Fin.zero_le _))
          have hc := hcount (0 : Fin (m + 1))
          rw [he] at hc
          simp at hc
        · let jp : Fin (m + 1) := ⟨j.val - 1, by omega⟩
          have he : Finset.univ.filter (fun i : Fin (m + 1) ↦ σf i ≤ j) =
              Finset.univ.filter (fun i : Fin (m + 1) ↦ σf i ≤ jp) := by
            ext i
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            constructor
            · intro hi
              have hne := hno' i
              change (σf i).val ≤ jp.val
              change (σf i).val ≤ j.val at hi
              change σf i ≠ j at hne
              dsimp [jp]
              omega
            · intro hi
              change (σf i).val ≤ j.val
              change (σf i).val ≤ jp.val at hi
              dsimp [jp] at hi
              omega
          have hcj := hcount j
          have hcp := hcount jp
          rw [he] at hcj
          change (Finset.univ.filter (fun i : Fin (m + 1) ↦ σf i ≤ jp)).card =
            j.val + 1 at hcj
          change (Finset.univ.filter (fun i : Fin (m + 1) ↦ σf i ≤ jp)).card =
            (j.val - 1) + 1 at hcp
          have hjpos : 0 < j.val := by
            by_contra hz
            have hzv : j.val = 0 := Nat.eq_zero_of_not_pos hz
            apply hj
            apply Fin.ext
            simpa using hzv
          omega
      have hσ_bij : Function.Bijective σf :=
        (Fintype.bijective_iff_surjective_and_card σf).2 ⟨hσ_surj, rfl⟩
      let e : Fin (m + 1) ≃ Fin (m + 1) := Equiv.ofBijective σf hσ_bij
      have he_apply (i) : e i = σf i := rfl
      let vr : (r : ℕ) → r ≤ m + 1 → Fin r → V := fun r hr i ↦
        v ⟨i.val, i.isLt.trans_le hr⟩
      have hLIprefix : ∀ (r : ℕ) (hr : r ≤ m + 1),
          LinearIndependent K (vr r hr) := by
        intro r
        induction r with
        | zero =>
            intro hr
            exact linearIndependent_empty_type
        | succ r ih =>
            intro hr
            rw [linearIndependent_finSucc']
            constructor
            · have heq : Fin.init (vr (r + 1) hr) =
                  vr r (Nat.le_of_succ_le hr) := by
                funext i
                apply congrArg v
                apply Fin.ext
                rfl
              rw [heq]
              exact ih (Nat.le_of_succ_le hr)
            · intro hmem
              have hspan_le : Submodule.span K (Set.range (Fin.init (vr (r + 1) hr))) ≤
                  F ⟨r, by omega⟩ := by
                rw [Submodule.span_le]
                intro x hx
                obtain ⟨i, rfl⟩ := hx
                have hvF := hv_left ⟨i.val, by omega⟩
                exact F.strictMono_space.monotone
                  (Fin.castSucc_lt_iff_succ_le.mp (show i.val < r from i.isLt)) hvF
              exact hv_not ⟨r, by omega⟩ (hspan_le hmem)
      have hLI : LinearIndependent K v := by
        simpa [vr] using hLIprefix (m + 1) le_rfl
      let b : Basis (Fin (m + 1)) K V :=
        basisOfLinearIndependentOfCardEqFinrank' v hLI (by simp [hfin])
      have hb : (b : Fin (m + 1) → V) = v :=
        coe_basisOfLinearIndependentOfCardEqFinrank' v hLI (by simp [hfin])
      have hFb : F = CompleteFlag.ofBasis b := by
        apply CompleteFlag.ext
        intro r
        apply (Submodule.eq_of_le_of_finrank_eq ?_ ?_).symm
        · change Submodule.span K (b '' {i | i.castSucc < r}) ≤ F r
          rw [Submodule.span_le]
          intro x hx
          obtain ⟨i, hi, rfl⟩ := hx
          rw [hb]
          exact F.strictMono_space.monotone
            (Fin.castSucc_lt_iff_succ_le.mp hi) (hv_left i)
        · rw [(CompleteFlag.ofBasis b).finrank_space, F.finrank_space]
      have hF'b : F' = CompleteFlag.ofBasis (b.reindex e) := by
        apply CompleteFlag.ext
        intro r
        apply (Submodule.eq_of_le_of_finrank_eq ?_ ?_).symm
        · rw [show CompleteFlag.ofBasis (b.reindex e) r =
              Submodule.span K (b '' PrefixSet e.symm r) by
                simpa using ofBasis_reindex_apply K V b e.symm r,
            Submodule.span_le]
          intro x hx
          obtain ⟨i, ⟨j, hj, hji⟩, rfl⟩ := hx
          subst i
          rw [hb]
          have hjσ : (σf (e.symm j)).succ ≤ r := by
            rw [← he_apply]
            simp only [Equiv.apply_symm_apply]
            exact Fin.castSucc_lt_iff_succ_le.mp hj
          exact F'.strictMono_space.monotone hjσ (hv_right (e.symm j))
        · rw [(CompleteFlag.ofBasis (b.reindex e)).finrank_space, F'.finrank_space]
      refine ⟨b, e.symm, hFb, ?_⟩
      simpa using hF'b

/-- The common-basis step in the paper, written literally as prefix spans.
For `i : Fin (n + 1)`, `{j | j.castSucc < i}` represents the first `i`
positions.  Thus `b` is the ordered basis `(v₁, ..., vₙ)`, while `π` gives
the second ordering `(v_{π(1)}, ..., v_{π(n)})`. -/
theorem common_basis_orderings {n : ℕ}
    (F F' : CompleteFlag K V n) :
    ∃ (b : Basis (Fin n) K V) (π : Equiv.Perm (Fin n)),
      (∀ i, F i = Submodule.span K (b '' {j | j.castSucc < i})) ∧
      (∀ i, F' i = Submodule.span K (b '' PrefixSet π i)) := by
  obtain ⟨b, π, hF, hF'⟩ := common_apartment K V F F'
  refine ⟨b, π, ?_, ?_⟩
  · intro i
    rw [hF]
    rfl
  · intro i
    rw [hF']
    exact ofBasis_reindex_apply K V b π i

end DegreeDiameter

end PortCommonBasis

/- DegreeDiameter.OddEvenRoute -/
section PortOddEvenRoute

namespace OddEvenSorting

def pairPhase {α : Type*} [LinearOrder α] : List α → List α
  | a :: b :: xs => min a b :: max a b :: pairPhase xs
  | xs => xs

def phase {α : Type*} [LinearOrder α] (shifted : Bool) (xs : List α) : List α :=
  if shifted then
    match xs with
    | [] => []
    | x :: xs => x :: pairPhase xs
  else
    pairPhase xs

@[simp] theorem pairPhase_nil {α : Type*} [LinearOrder α] :
    pairPhase ([] : List α) = [] := rfl

@[simp] theorem pairPhase_singleton {α : Type*} [LinearOrder α] (a : α) :
    pairPhase [a] = [a] := rfl

@[simp] theorem pairPhase_cons_cons {α : Type*} [LinearOrder α] (a b : α) (xs : List α) :
    pairPhase (a :: b :: xs) = min a b :: max a b :: pairPhase xs := rfl

@[simp] theorem phase_false {α : Type*} [LinearOrder α] (xs : List α) :
    phase false xs = pairPhase xs := rfl

@[simp] theorem phase_true_nil {α : Type*} [LinearOrder α] :
    phase true ([] : List α) = [] := rfl

@[simp] theorem phase_true_cons {α : Type*} [LinearOrder α] (a : α) (xs : List α) :
    phase true (a :: xs) = a :: pairPhase xs := rfl

@[simp] theorem length_pairPhase {α : Type*} [LinearOrder α] (xs : List α) :
    (pairPhase xs).length = xs.length := by
  induction xs using pairPhase.induct <;> simp_all [pairPhase]

@[simp] theorem length_phase {α : Type*} [LinearOrder α] (p : Bool) (xs : List α) :
    (phase p xs).length = xs.length := by
  cases p <;> cases xs <;> simp [phase]

def pref (xs : List Bool) (i : ℕ) : ℤ := ((xs.take i).count true : ℤ)

def bitInt (b : Bool) : ℤ := if b then 1 else 0

@[simp] theorem pref_nil (i : ℕ) : pref [] i = 0 := by simp [pref]

@[simp] theorem pref_zero (xs : List Bool) : pref xs 0 = 0 := by simp [pref]

@[simp] theorem pref_cons_succ (a : Bool) (xs : List Bool) (i : ℕ) :
    pref (a :: xs) (i + 1) = bitInt a + pref xs i := by
  cases a <;> simp [pref, bitInt, add_comm]

theorem pref_cons_cons_add (a b : Bool) (xs : List Bool) (i : ℕ) :
    pref (a :: b :: xs) (i + 2) = bitInt a + bitInt b + pref xs i := by
  rw [show i + 2 = (i + 1) + 1 by omega, pref_cons_succ, pref_cons_succ]
  omega

theorem bitInt_min_add_max (a b : Bool) :
    bitInt (min a b) + bitInt (max a b) = bitInt a + bitInt b := by
  cases a <;> cases b <;> decide

theorem pref_pairPhase_even (xs : List Bool) (k : ℕ) :
    pref (pairPhase xs) (2 * k) = pref xs (2 * k) := by
  induction k generalizing xs with
  | zero => simp
  | succ k ih =>
      cases xs with
      | nil => simp
      | cons a xs =>
          cases xs with
          | nil => simp [pairPhase, pref]
          | cons b xs =>
              rw [show 2 * (k + 1) = 2 * k + 2 by omega]
              rw [pairPhase_cons_cons, pref_cons_cons_add, pref_cons_cons_add,
                bitInt_min_add_max, ih]

theorem pref_pairPhase_odd (xs : List Bool) (k : ℕ)
    (hk : 2 * k + 1 < xs.length) :
    pref (pairPhase xs) (2 * k + 1) =
      max (pref xs (2 * k)) (pref xs (2 * k + 2) - 1) := by
  induction k generalizing xs with
  | zero =>
      cases xs with
      | nil => simp at hk
      | cons a xs =>
          cases xs with
          | nil => simp at hk
          | cons b xs => cases a <;> cases b <;> simp [pairPhase, pref]
  | succ k ih =>
      cases xs with
      | nil => simp at hk
      | cons a xs =>
          cases xs with
          | nil => simp at hk
          | cons b xs =>
              simp only [List.length_cons] at hk
              have hk' : 2 * k + 1 < xs.length := by omega
              have h := ih xs hk'
              rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by omega]
              rw [show 2 * (k + 1) = 2 * k + 2 by omega]
              rw [pairPhase_cons_cons, pref_cons_cons_add, pref_cons_cons_add,
                pref_cons_cons_add, bitInt_min_add_max, h]
              simp only [max_def]
              split <;> split <;> omega

theorem pref_phase_false_even (xs : List Bool) (k : ℕ) :
    pref (phase false xs) (2 * k) = pref xs (2 * k) := by
  exact pref_pairPhase_even xs k

theorem pref_phase_false_odd (xs : List Bool) (k : ℕ)
    (hk : 2 * k + 1 < xs.length) :
    pref (phase false xs) (2 * k + 1) =
      max (pref xs (2 * k)) (pref xs (2 * k + 2) - 1) := by
  exact pref_pairPhase_odd xs k hk

theorem pref_phase_true_odd (xs : List Bool) (k : ℕ) :
    pref (phase true xs) (2 * k + 1) = pref xs (2 * k + 1) := by
  cases xs with
  | nil => simp [phase, pref]
  | cons a xs =>
      rw [phase_true_cons]
      rw [show 2 * k + 1 = 2 * k + 1 by rfl, pref_cons_succ, pref_cons_succ,
        pref_pairPhase_even]

theorem pref_phase_true_even (xs : List Bool) (k : ℕ)
    (hk : 2 * k + 2 < xs.length) :
    pref (phase true xs) (2 * k + 2) =
      max (pref xs (2 * k + 1)) (pref xs (2 * k + 3) - 1) := by
  cases xs with
  | nil => simp at hk
  | cons a xs =>
      simp only [List.length_cons] at hk
      have hk' : 2 * k + 1 < xs.length := by omega
      rw [phase_true_cons]
      rw [show 2 * k + 2 = (2 * k + 1) + 1 by omega, pref_cons_succ]
      rw [show 2 * k + 1 = 2 * k + 1 by rfl, pref_pairPhase_odd xs k hk']
      rw [show 2 * k + 1 = 2 * k + 1 by rfl, pref_cons_succ]
      rw [show 2 * k + 3 = (2 * k + 2) + 1 by omega, pref_cons_succ]
      simp only [max_def]
      split <;> split <;> omega

def active (q i : ℕ) : Bool := decide (i % 2 = (q + 1) % 2)

def phaseN {α : Type*} [LinearOrder α] (q : ℕ) (xs : List α) : List α :=
  phase (decide (q % 2 = 1)) xs

theorem pref_phaseN (q : ℕ) (xs : List Bool) (i : ℕ)
    (hi0 : 0 < i) (hin : i < xs.length) :
    pref (phaseN q xs) i =
      if active q i then max (pref xs (i - 1)) (pref xs (i + 1) - 1)
      else pref xs i := by
  classical
  have hq : q % 2 = 0 ∨ q % 2 = 1 := by omega
  have hi : i % 2 = 0 ∨ i % 2 = 1 := by omega
  rcases hq with hq | hq <;> rcases hi with hi | hi
  · have hphase : phaseN q xs = phase false xs := by simp [phaseN, hq]
    have hactive : active q i = false := by simp [active]; omega
    have heq : i = 2 * (i / 2) := by omega
    rw [hphase, hactive]
    simp only [Bool.false_eq_true, if_false]
    rw [heq]
    exact pref_phase_false_even xs (i / 2)
  · have hphase : phaseN q xs = phase false xs := by simp [phaseN, hq]
    have hactive : active q i = true := by simp [active]; omega
    have heq : i = 2 * (i / 2) + 1 := by omega
    rw [hphase, hactive]
    simp only [if_true]
    rw [heq]
    rw [show 2 * (i / 2) + 1 - 1 = 2 * (i / 2) by omega]
    rw [show 2 * (i / 2) + 1 + 1 = 2 * (i / 2) + 2 by omega]
    exact pref_phase_false_odd xs (i / 2) (by omega)
  · have hphase : phaseN q xs = phase true xs := by simp [phaseN, hq]
    have hactive : active q i = true := by simp [active]; omega
    have heq : i = 2 * ((i - 2) / 2) + 2 := by omega
    rw [hphase, hactive]
    simp only [if_true]
    rw [heq]
    rw [show 2 * ((i - 2) / 2) + 2 - 1 = 2 * ((i - 2) / 2) + 1 by omega]
    rw [show 2 * ((i - 2) / 2) + 2 + 1 = 2 * ((i - 2) / 2) + 3 by omega]
    exact pref_phase_true_even xs ((i - 2) / 2) (by omega)
  · have hphase : phaseN q xs = phase true xs := by simp [phaseN, hq]
    have hactive : active q i = false := by simp [active]; omega
    have heq : i = 2 * (i / 2) + 1 := by omega
    rw [hphase, hactive]
    simp only [Bool.false_eq_true, if_false]
    rw [heq]
    exact pref_phase_true_odd xs (i / 2)

def countTrue (xs : List Bool) : ℕ := xs.count true

@[simp] theorem countTrue_pairPhase (xs : List Bool) :
    countTrue (pairPhase xs) = countTrue xs := by
  induction xs using pairPhase.induct with
  | case1 a b xs ih => cases a <;> cases b <;> simp_all [countTrue, pairPhase]
  | case2 xs h =>
      cases xs with
      | nil => rfl
      | cons a xs =>
          cases xs with
          | nil => rfl
          | cons b xs => exact (h a b xs rfl).elim

@[simp] theorem countTrue_phase (p : Bool) (xs : List Bool) :
    countTrue (phase p xs) = countTrue xs := by
  cases p with
  | false => exact countTrue_pairPhase xs
  | true =>
      cases xs with
      | nil => rfl
      | cons a xs =>
          change (a :: pairPhase xs).count true = (a :: xs).count true
          have h := countTrue_pairPhase xs
          unfold countTrue at h
          simp only [List.count_cons]
          rw [h]

@[simp] theorem countTrue_phaseN (q : ℕ) (xs : List Bool) :
    countTrue (phaseN q xs) = countTrue xs := by
  simp [phaseN]

def evolve {α : Type*} [LinearOrder α] (q : ℕ) (xs : List α) : ℕ → List α
  | 0 => xs
  | t + 1 => phaseN (q + t) (evolve q xs t)

@[simp] theorem evolve_zero {α : Type*} [LinearOrder α] (q : ℕ) (xs : List α) :
    evolve q xs 0 = xs := rfl

@[simp] theorem evolve_succ {α : Type*} [LinearOrder α] (q : ℕ) (xs : List α) (t : ℕ) :
    evolve q xs (t + 1) = phaseN (q + t) (evolve q xs t) := rfl

@[simp] theorem length_phaseN {α : Type*} [LinearOrder α] (q : ℕ) (xs : List α) :
    (phaseN q xs).length = xs.length := by simp [phaseN]

@[simp] theorem length_evolve {α : Type*} [LinearOrder α] (q : ℕ) (xs : List α) (t : ℕ) :
    (evolve q xs t).length = xs.length := by
  induction t with
  | zero => rfl
  | succ t ih => simp [evolve, ih]

@[simp] theorem countTrue_evolve (q : ℕ) (xs : List Bool) (t : ℕ) :
    countTrue (evolve q xs t) = countTrue xs := by
  induction t with
  | zero => rfl
  | succ t ih => simp [evolve, ih]

/-- Prefix count in the sorted Boolean word with `z` zeroes. -/
def low (z i : ℕ) : ℤ := max 0 ((i : ℤ) - (z : ℤ))

/-- The potential used to rule out a bad prefix surviving all layers. -/
def potential (z i : ℕ) (h : ℤ) : ℤ :=
  if i ≤ z then (i : ℤ) - 2 * h else 2 * (z : ℤ) - (i : ℤ) - 2 * h

def Bad (z : ℕ) (xs : List Bool) (i : ℕ) (h : ℤ) : Prop :=
  1 ≤ h ∧ low z i + h ≤ pref xs i

theorem pref_le_index (xs : List Bool) (i : ℕ) : pref xs i ≤ i := by
  unfold pref
  have h := List.count_le_length (a := true) (l := xs.take i)
  have ht := List.length_take_le i xs
  omega

theorem pref_le_total (xs : List Bool) (i : ℕ) : pref xs i ≤ countTrue xs := by
  unfold pref countTrue
  exact_mod_cast (List.take_sublist i xs).count_le true

theorem pref_at_length (xs : List Bool) : pref xs xs.length = countTrue xs := by
  simp [pref, countTrue]

theorem pref_lower (xs : List Bool) (z r i : ℕ)
    (hlen : xs.length = r + z) (hcount : countTrue xs = r) (hi : i ≤ xs.length) :
    low z i ≤ pref xs i := by
  have hsplit : xs.take i ++ xs.drop i = xs := List.take_append_drop i xs
  have hc : (xs.take i).count true + (xs.drop i).count true = xs.count true := by
    simpa only [List.count_append] using congrArg (List.count true) hsplit
  have hd := List.count_le_length (a := true) (l := xs.drop i)
  have hdl : (xs.drop i).length = xs.length - i := List.length_drop
  unfold low pref countTrue at *
  simp only [max_def]
  split <;> omega

theorem potential_upper (z i : ℕ) (h : ℤ) (hh : 1 ≤ h) :
    potential z i h ≤ (z : ℤ) - 2 := by
  unfold potential
  split <;> omega

theorem potential_lower_of_initial_bad (xs : List Bool) (z r i : ℕ) (h : ℤ)
    (hcount : countTrue xs = r) (hb : Bad z xs i h) :
    -(r : ℤ) ≤ potential z i h := by
  have hpi := pref_le_index xs i
  have hpr := pref_le_total xs i
  unfold Bad at hb
  unfold low at hb
  unfold potential
  rcases hb with ⟨hh, hb⟩
  simp only [max_def] at hb
  split at hb <;> split <;> omega

theorem potential_left (z i : ℕ) (h : ℤ) (hi : 0 < i) :
    potential z (i - 1) (h + low z i - low z (i - 1)) = potential z i h - 1 := by
  unfold potential low
  simp only [max_def]
  split <;> split <;> split <;> split <;> omega

theorem potential_right (z i : ℕ) (h : ℤ) :
    potential z (i + 1) (h + 1 + low z i - low z (i + 1)) = potential z i h - 1 := by
  unfold potential low
  simp only [max_def]
  split <;> split <;> split <;> split <;> omega

theorem not_bad_zero (z : ℕ) (xs : List Bool) (h : ℤ) : ¬Bad z xs 0 h := by
  unfold Bad low
  simp
  omega

theorem not_bad_length (z r : ℕ) (xs : List Bool) (h : ℤ)
    (hlen : xs.length = r + z) (hcount : countTrue xs = r) :
    ¬Bad z xs xs.length h := by
  intro hb
  have hp := pref_at_length xs
  unfold Bad low at hb
  rcases hb with ⟨hh, hb⟩
  simp only [max_def] at hb
  split at hb <;> omega

theorem bad_predecessor (z r q i : ℕ) (xs : List Bool) (h : ℤ)
    (hlen : xs.length = r + z) (hcount : countTrue xs = r)
    (hi0 : 0 < i) (hin : i < xs.length) (hact : active q i = true)
    (hb : Bad z (phaseN q xs) i h) :
    ∃ j : ℕ, ∃ h' : ℤ,
      (j = i - 1 ∨ j = i + 1) ∧ 0 < j ∧ j < xs.length ∧
      Bad z xs j h' ∧ potential z j h' = potential z i h - 1 := by
  have hp := pref_phaseN q xs i hi0 hin
  rw [hact] at hp
  simp only [if_true] at hp
  unfold Bad at hb
  rw [hp] at hb
  rcases hb with ⟨hh, hb⟩
  by_cases hc : pref xs (i - 1) ≤ pref xs (i + 1) - 1
  · have hbR : low z i + h ≤ pref xs (i + 1) - 1 := by
      simpa [max_eq_right hc] using hb
    let h' : ℤ := h + 1 + low z i - low z (i + 1)
    have hh' : 1 ≤ h' := by
      dsimp [h']
      unfold low
      simp only [max_def]
      split <;> split <;> omega
    have hbad : Bad z xs (i + 1) h' := by
      refine ⟨hh', ?_⟩
      dsimp [h']
      omega
    have hjlt : i + 1 < xs.length := by
      by_contra hn
      have heq : i + 1 = xs.length := by omega
      exact not_bad_length z r xs h' hlen hcount (heq ▸ hbad)
    exact ⟨i + 1, h', Or.inr rfl, by omega, hjlt, hbad, potential_right z i h⟩
  · have hbL : low z i + h ≤ pref xs (i - 1) := by
      simpa [max_eq_left (le_of_not_ge hc)] using hb
    let h' : ℤ := h + low z i - low z (i - 1)
    have hh' : 1 ≤ h' := by
      dsimp [h']
      unfold low
      simp only [max_def]
      split <;> split <;> omega
    have hbad : Bad z xs (i - 1) h' := by
      refine ⟨hh', ?_⟩
      dsimp [h']
      omega
    have hjpos : 0 < i - 1 := by
      by_contra hn
      have heq : i - 1 = 0 := by omega
      exact not_bad_zero z xs h' (heq ▸ hbad)
    exact ⟨i - 1, h', Or.inl rfl, hjpos, by omega, hbad, potential_left z i h hi0⟩

theorem active_previous_neighbor (q i j : ℕ) (hq : 0 < q) (hi0 : 0 < i)
    (hi : active q i = true) (hj : j = i - 1 ∨ j = i + 1) :
    active (q - 1) j = true := by
  unfold active at hi ⊢
  simp only [decide_eq_true_eq] at hi ⊢
  rw [show q - 1 + 1 = q by omega]
  rcases hj with rfl | rfl <;> omega

theorem active_previous_same (q i : ℕ) (hq : 0 < q)
    (hi : active q i = false) : active (q - 1) i = true := by
  unfold active at hi ⊢
  simp only [decide_eq_false_iff_not, decide_eq_true_eq] at hi ⊢
  rw [show q - 1 + 1 = q by omega]
  omega

theorem trace_bad_active (z r q : ℕ) (xs : List Bool) (t i : ℕ) (h : ℤ)
    (hlen : xs.length = r + z) (hcount : countTrue xs = r) (ht : 0 < t)
    (hact : active (q + t - 1) i = true)
    (hb : Bad z (evolve q xs t) i h) :
    ∃ j : ℕ, ∃ h' : ℤ,
      0 < j ∧ j < xs.length ∧ Bad z xs j h' ∧
      potential z j h' = potential z i h - t := by
  induction t generalizing i h with
  | zero => omega
  | succ t ih =>
      have hphase : q + (t + 1) - 1 = q + t := by omega
      rw [hphase] at hact
      have hi0 : 0 < i := by
        by_contra hn
        have hi : i = 0 := by omega
        have := not_bad_zero z (evolve q xs (t + 1)) h
        exact this (hi ▸ hb)
      have hin : i < (evolve q xs t).length := by
        by_contra hn
        have hle : (evolve q xs t).length ≤ i := by omega
        have hpref := pref_le_total (evolve q xs (t + 1)) i
        have hc : countTrue (evolve q xs (t + 1)) = r := by simpa using hcount
        have hl : (evolve q xs t).length = r + z := by simpa using hlen
        unfold Bad at hb
        unfold low at hb
        rcases hb with ⟨hh, hb⟩
        simp only [max_def] at hb
        split at hb <;> omega
      have hbPhase : Bad z (phaseN (q + t) (evolve q xs t)) i h := by
        simpa [evolve] using hb
      obtain ⟨j, h', hj, hj0, hjn, hb', hpot⟩ :=
        bad_predecessor z r (q + t) i (evolve q xs t) h
          (by simpa using hlen) (by simpa using hcount) hi0 hin hact hbPhase
      by_cases ht0 : t = 0
      · subst t
        refine ⟨j, h', ?_, ?_, ?_, ?_⟩
        · exact hj0
        · simpa using hjn
        · simpa using hb'
        · simpa using hpot
      · have htpos : 0 < t := by omega
        have hprev : active (q + t - 1) j = true := by
          exact active_previous_neighbor (q + t) i j (by omega) hi0 hact hj
        obtain ⟨j0, h0, hj00, hj0n, hb0, hpot0⟩ :=
          ih j h' htpos hprev hb'
        refine ⟨j0, h0, hj00, hj0n, hb0, ?_⟩
        rw [hpot0, hpot]
        push_cast
        omega

theorem pref_evolve_full (z r q : ℕ) (xs : List Bool)
    (hlen : xs.length = r + z) (hcount : countTrue xs = r)
    (i : ℕ) (hi : i ≤ xs.length) :
    pref (evolve q xs (r + z)) i = low z i := by
  have hlower : low z i ≤ pref (evolve q xs (r + z)) i :=
    pref_lower (evolve q xs (r + z)) z r i (by simpa using hlen) (by simpa using hcount) (by simpa)
  apply le_antisymm ?_ hlower
  by_contra hnle
  have hstrict : low z i < pref (evolve q xs (r + z)) i := by omega
  let h : ℤ := pref (evolve q xs (r + z)) i - low z i
  have hh : 1 ≤ h := by dsimp [h]; omega
  have hb : Bad z (evolve q xs (r + z)) i h := by
    refine ⟨hh, ?_⟩
    dsimp [h]
    omega
  have hi0 : 0 < i := by
    by_contra hz
    have : i = 0 := by omega
    exact not_bad_zero z (evolve q xs (r + z)) h (this ▸ hb)
  have hin : i < xs.length := by
    by_contra hni
    have : i = xs.length := by omega
    have heql : i = (evolve q xs (r + z)).length := by simpa using this
    exact not_bad_length z r (evolve q xs (r + z)) h
      (by simpa using hlen) (by simpa using hcount) (heql ▸ hb)
  have hnpos : 0 < r + z := by omega
  by_cases hact : active (q + (r + z) - 1) i = true
  · obtain ⟨j, h', hj0, hjn, hbad, hpot⟩ :=
      trace_bad_active z r q xs (r + z) i h hlen hcount hnpos hact hb
    have hlo := potential_lower_of_initial_bad xs z r j h' hcount hbad
    have hup := potential_upper z i h hh
    push_cast at hpot
    omega
  · have hactFalse : active (q + (r + z) - 1) i = false := by
      cases ha : active (q + (r + z) - 1) i <;> simp_all
    have htwo : 2 ≤ r + z := by omega
    have htpos : 0 < r + z - 1 := by omega
    have hevolve : evolve q xs (r + z) =
        phaseN (q + (r + z - 1)) (evolve q xs (r + z - 1)) := by
      rw [show r + z = (r + z - 1) + 1 by omega, evolve_succ]
      congr 2
    have hp := pref_phaseN (q + (r + z - 1)) (evolve q xs (r + z - 1)) i
      (by omega) (by simpa using hin)
    have hindex : q + (r + z - 1) = q + (r + z) - 1 := by omega
    have hactSmall : active (q + (r + z - 1)) i = false := by
      rw [hindex]
      exact hactFalse
    rw [hactSmall] at hp
    simp only [Bool.false_eq_true, if_false] at hp
    have hbPrev : Bad z (evolve q xs (r + z - 1)) i h := by
      rw [hevolve] at hb
      unfold Bad at hb ⊢
      rw [hp] at hb
      exact hb
    have hlastpos : 0 < q + (r + z) - 1 := by omega
    have hprev0 := active_previous_same (q + (r + z) - 1) i hlastpos hactFalse
    have hprev : active (q + (r + z - 1) - 1) i = true := by
      rw [show q + (r + z - 1) - 1 = (q + (r + z) - 1) - 1 by omega]
      exact hprev0
    obtain ⟨j, h', hj0, hjn, hbad, hpot⟩ :=
      trace_bad_active z r q xs (r + z - 1) i h hlen hcount htpos hprev hbPrev
    have hlo := potential_lower_of_initial_bad xs z r j h' hcount hbad
    have hup := potential_upper z i h hh
    omega

def threshold {α : Type*} [LinearOrder α] (a x : α) : Bool := decide (a ≤ x)

theorem threshold_min {α : Type*} [LinearOrder α] (a x y : α) :
    threshold a (min x y) = min (threshold a x) (threshold a y) := by
  rcases le_total x y with hxy | hyx
  · rw [min_eq_left hxy]
    by_cases hx : a ≤ x
    · have hy : a ≤ y := hx.trans hxy
      simp [threshold, hx, hy]
    · by_cases hy : a ≤ y <;> simp [threshold, hx, hy]
  · rw [min_eq_right hyx]
    by_cases hy : a ≤ y
    · have hx : a ≤ x := hy.trans hyx
      simp [threshold, hx, hy]
    · by_cases hx : a ≤ x <;> simp [threshold, hx, hy]

theorem threshold_max {α : Type*} [LinearOrder α] (a x y : α) :
    threshold a (max x y) = max (threshold a x) (threshold a y) := by
  rcases le_total x y with hxy | hyx
  · rw [max_eq_right hxy]
    by_cases hy : a ≤ y
    · by_cases hx : a ≤ x <;> simp [threshold, hx, hy]
    · have hx : ¬a ≤ x := fun hx ↦ hy (hx.trans hxy)
      simp [threshold, hx, hy]
  · rw [max_eq_left hyx]
    by_cases hx : a ≤ x
    · by_cases hy : a ≤ y <;> simp [threshold, hx, hy]
    · have hy : ¬a ≤ y := fun hy ↦ hx (hy.trans hyx)
      simp [threshold, hx, hy]

theorem map_threshold_pairPhase {α : Type*} [LinearOrder α] (a : α) (xs : List α) :
    (pairPhase xs).map (threshold a) = pairPhase (xs.map (threshold a)) := by
  induction xs using pairPhase.induct with
  | case1 x y xs ih => simp [pairPhase, ih, threshold_min, threshold_max]
  | case2 xs h =>
      cases xs with
      | nil => rfl
      | cons x xs =>
          cases xs with
          | nil => rfl
          | cons y xs => exact (h x y xs rfl).elim

theorem map_threshold_phase {α : Type*} [LinearOrder α]
    (a : α) (p : Bool) (xs : List α) :
    (phase p xs).map (threshold a) = phase p (xs.map (threshold a)) := by
  cases p with
  | false => exact map_threshold_pairPhase a xs
  | true =>
      cases xs with
      | nil => rfl
      | cons x xs => simp [phase, map_threshold_pairPhase]

theorem map_threshold_phaseN {α : Type*} [LinearOrder α]
    (a : α) (q : ℕ) (xs : List α) :
    (phaseN q xs).map (threshold a) = phaseN q (xs.map (threshold a)) := by
  exact map_threshold_phase a _ xs

theorem map_threshold_evolve {α : Type*} [LinearOrder α]
    (a : α) (q t : ℕ) (xs : List α) :
    (evolve q xs t).map (threshold a) = evolve q (xs.map (threshold a)) t := by
  induction t with
  | zero => rfl
  | succ t ih => simp [evolve, map_threshold_phaseN, ih]

theorem pref_succ (xs : List Bool) (i : ℕ) (hi : i < xs.length) :
    pref xs (i + 1) = pref xs i + bitInt xs[i] := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
      cases i with
      | zero => cases x <;> simp [pref, bitInt]
      | succ i =>
          have hi' : i < xs.length := by simpa using hi
          have h := ih i hi'
          rw [show i + 1 + 1 = (i + 1) + 1 by rfl, pref_cons_succ, pref_cons_succ]
          simpa [List.getElem_cons_succ, add_assoc] using congrArg (fun z : ℤ ↦ bitInt x + z) h

theorem bool_getElem_of_pref_full (z r q : ℕ) (xs : List Bool)
    (hlen : xs.length = r + z) (hcount : countTrue xs = r)
    (i : ℕ) (hi : i < xs.length) :
    (evolve q xs (r + z))[i]'(by simpa using hi) = decide (z ≤ i) := by
  let ys := evolve q xs (r + z)
  have hiy : i < ys.length := by simpa [ys] using hi
  have hp0 := pref_evolve_full z r q xs hlen hcount i (by omega)
  have hp1 := pref_evolve_full z r q xs hlen hcount (i + 1) (by omega)
  have hs := pref_succ ys i hiy
  have hbit : bitInt (ys[i]'hiy) = low z (i + 1) - low z i := by
    have hp0' : pref ys i = low z i := by simpa [ys] using hp0
    have hp1' : pref ys (i + 1) = low z (i + 1) := by simpa [ys] using hp1
    rw [hp0', hp1'] at hs
    omega
  by_cases hz : z ≤ i
  · have : bitInt (ys[i]'hiy) = 1 := by
      rw [hbit]
      unfold low
      simp only [max_def]
      split <;> split <;> omega
    cases hval : ys[i]'hiy <;> simp_all [bitInt, ys]
  · have : bitInt (ys[i]'hiy) = 0 := by
      rw [hbit]
      unfold low
      simp only [max_def]
      split <;> split <;> omega
    cases hval : ys[i]'hiy <;> simp_all [bitInt, ys]

theorem countTrue_map_threshold {α : Type*} [LinearOrder α] (a : α) (xs : List α) :
    countTrue (xs.map (threshold a)) = (xs.filter (threshold a)).length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      unfold countTrue at ih ⊢
      by_cases hx : a ≤ x <;> simp [threshold, hx, ih]

theorem countTrue_map_threshold_finRange {n : ℕ} (a : Fin n) :
    countTrue ((List.finRange n).map (threshold a)) = n - a.val := by
  rw [countTrue_map_threshold]
  have hn : ((List.finRange n).filter (threshold a)).Nodup :=
    (List.nodup_finRange n).filter _
  rw [← List.toFinset_card_of_nodup hn]
  rw [List.toFinset_filter, List.toFinset_finRange]
  have heq : ({x : Fin n | threshold a x = true} : Finset (Fin n)) = Finset.Ici a := by
    ext x
    simp [threshold]
  rw [heq, Fin.card_Ici]

theorem countTrue_map_threshold_of_perm_finRange {n : ℕ} (a : Fin n)
    (xs : List (Fin n)) (hp : xs.Perm (List.finRange n)) :
    countTrue (xs.map (threshold a)) = n - a.val := by
  rw [countTrue_map_threshold]
  rw [(hp.filter (threshold a)).length_eq]
  rw [← countTrue_map_threshold]
  exact countTrue_map_threshold_finRange a

theorem threshold_evolve_perm_finRange {n : ℕ} (xs : List (Fin n))
    (hp : xs.Perm (List.finRange n)) (q : ℕ) (a : Fin n) (i : ℕ)
    (hi : i < n) :
    threshold a ((evolve q xs n)[i]'(by
      have hl : xs.length = n := by simpa using hp.length_eq
      simpa [hl] using hi)) =
      decide (a.val ≤ i) := by
  let bs := xs.map (threshold a)
  have hlenxs : xs.length = n := by simpa using hp.length_eq
  have hlenbs : bs.length = n := by simp [bs, hlenxs]
  have hcountbs : countTrue bs = n - a.val := by
    dsimp [bs]
    exact countTrue_map_threshold_of_perm_finRange a xs hp
  have hsum : (n - a.val) + a.val = n := by omega
  have hb := bool_getElem_of_pref_full a.val (n - a.val) q bs
    (by omega) hcountbs i (by omega)
  rw [hsum] at hb
  dsimp [bs] at hb
  have hmap := map_threshold_evolve a q n xs
  have hie : i < (evolve q xs n).length := by simpa [hlenxs] using hi
  have hib : i < (evolve q (xs.map (threshold a)) n).length := by simp [hlenxs, hi]
  have hbOpt : (evolve q (xs.map (threshold a)) n)[i]? = some (decide (a.val ≤ i)) := by
    rw [List.getElem?_eq_getElem hib]
    exact congrArg some hb
  have hmapAt := congrArg (fun l : List Bool ↦ l[i]?) hmap
  have houtOpt : ((evolve q xs n).map (threshold a))[i]? =
      some (threshold a ((evolve q xs n)[i]'hie)) := by
    simp [List.getElem?_map, List.getElem?_eq_getElem hie]
  have hsome : some (threshold a ((evolve q xs n)[i]'hie)) =
      some (decide (a.val ≤ i)) := by
    rw [← houtOpt, hmapAt, hbOpt]
  exact Option.some.inj hsome

theorem evolve_perm_finRange_eq {n : ℕ} (xs : List (Fin n))
    (hp : xs.Perm (List.finRange n)) (q : ℕ) :
    evolve q xs n = List.finRange n := by
  apply List.ext_getElem (by simpa using hp.length_eq)
  intro i hi1 hi2
  have hi : i < n := by simpa using hi2
  let y : Fin n := (evolve q xs n)[i]'hi1
  have hy := threshold_evolve_perm_finRange xs hp q y i hi
  have hk := threshold_evolve_perm_finRange xs hp q (⟨i, hi⟩ : Fin n) i hi
  have hy_le : y.val ≤ i := by
    change threshold y y = decide (y.val ≤ i) at hy
    simpa [threshold] using hy
  have hi_le : i ≤ y.val := by
    change threshold (⟨i, hi⟩ : Fin n) y = decide (i ≤ i) at hk
    have hk' : (⟨i, hi⟩ : Fin n) ≤ y := by simpa [threshold] using hk
    change i ≤ y.val at hk'
    exact hk'
  have hyval : y = (⟨i, hi⟩ : Fin n) := Fin.ext (Nat.le_antisymm hy_le hi_le)
  change y = (List.finRange n)[i]
  rw [hyval]
  apply Fin.ext
  simp

theorem pair_minmax_perm {α : Type*} [LinearOrder α] (a b : α) (xs : List α) :
    (min a b :: max a b :: xs).Perm (a :: b :: xs) := by
  by_cases h : a ≤ b
  · simp [min_eq_left h, max_eq_right h]
  · have h' : b ≤ a := le_of_not_ge h
    simpa [min_eq_right h', max_eq_left h'] using List.Perm.swap a b xs

@[simp] theorem pairPhase_perm {α : Type*} [LinearOrder α] (xs : List α) :
    (pairPhase xs).Perm xs := by
  induction xs using pairPhase.induct with
  | case1 a b xs ih =>
      exact ((ih.cons (max a b)).cons (min a b)).trans (pair_minmax_perm a b xs)
  | case2 xs h =>
      cases xs with
      | nil => exact .refl _
      | cons a xs =>
          cases xs with
          | nil => exact .refl _
          | cons b xs => exact (h a b xs rfl).elim

@[simp] theorem phase_perm {α : Type*} [LinearOrder α] (p : Bool) (xs : List α) :
    (phase p xs).Perm xs := by
  cases p with
  | false => exact pairPhase_perm xs
  | true =>
      cases xs with
      | nil => exact .refl _
      | cons a xs => exact (pairPhase_perm xs).cons a

@[simp] theorem phaseN_perm {α : Type*} [LinearOrder α] (q : ℕ) (xs : List α) :
    (phaseN q xs).Perm xs := phase_perm _ xs

@[simp] theorem evolve_perm {α : Type*} [LinearOrder α] (q t : ℕ) (xs : List α) :
    (evolve q xs t).Perm xs := by
  induction t with
  | zero => exact .refl _
  | succ t ih => exact (phaseN_perm _ _).trans ih

theorem take_pairPhase_even_perm {α : Type*} [LinearOrder α]
    (xs : List α) (k : ℕ) :
    ((pairPhase xs).take (2 * k)).Perm (xs.take (2 * k)) := by
  induction k generalizing xs with
  | zero => exact .refl _
  | succ k ih =>
      cases xs with
      | nil => exact .refl _
      | cons a xs =>
          cases xs with
          | nil => exact .refl _
          | cons b xs =>
              simp only [pairPhase_cons_cons]
              rw [show 2 * (k + 1) = 2 * k + 2 by omega]
              simp only [List.take_succ_cons]
              exact (((ih xs).cons (max a b)).cons (min a b)).trans
                (pair_minmax_perm a b (xs.take (2 * k)))

theorem take_phase_false_even_perm {α : Type*} [LinearOrder α]
    (xs : List α) (k : ℕ) :
    ((phase false xs).take (2 * k)).Perm (xs.take (2 * k)) :=
  take_pairPhase_even_perm xs k

theorem take_phase_true_odd_perm {α : Type*} [LinearOrder α]
    (xs : List α) (k : ℕ) :
    ((phase true xs).take (2 * k + 1)).Perm (xs.take (2 * k + 1)) := by
  cases xs with
  | nil => exact .refl _
  | cons a xs =>
      rw [phase_true_cons]
      rw [show 2 * k + 1 = 2 * k + 1 by rfl]
      simp only [List.take_succ_cons]
      exact (take_pairPhase_even_perm xs k).cons a

theorem take_phaseN_perm_of_inactive {α : Type*} [LinearOrder α]
    (q : ℕ) (xs : List α) (i : ℕ) (hact : active q i = false) :
    ((phaseN q xs).take i).Perm (xs.take i) := by
  have hq : q % 2 = 0 ∨ q % 2 = 1 := by omega
  have hi : i % 2 = 0 ∨ i % 2 = 1 := by omega
  rcases hq with hq | hq <;> rcases hi with hi | hi
  · have hphase : phaseN q xs = phase false xs := by simp [phaseN, hq]
    have heq : i = 2 * (i / 2) := by omega
    rw [hphase, heq]
    exact take_phase_false_even_perm xs (i / 2)
  · exfalso
    unfold active at hact
    simp only [decide_eq_false_iff_not] at hact
    omega
  · exfalso
    unfold active at hact
    simp only [decide_eq_false_iff_not] at hact
    omega
  · have hphase : phaseN q xs = phase true xs := by simp [phaseN, hq]
    have heq : i = 2 * (i / 2) + 1 := by omega
    rw [hphase, heq]
    exact take_phase_true_odd_perm xs (i / 2)

/-- The permutation whose one-line notation is `l`. -/
noncomputable def permOfList {n : ℕ} (l : List (Fin n))
    (hp : l.Perm (List.finRange n)) : Equiv.Perm (Fin n) := by
  let hlen : l.length = n := by simpa using hp.length_eq
  exact (finCongr hlen.symm).trans
    (List.Nodup.getEquivOfForallMemList l
      (hp.nodup_iff.mpr (List.nodup_finRange n))
      (fun x ↦ (hp.mem_iff).2 (List.mem_finRange x)))

theorem permOfList_apply {n : ℕ} (l : List (Fin n))
    (hp : l.Perm (List.finRange n)) (i : Fin n) :
    permOfList l hp i = l[i.val]'(by
      have hlen : l.length = n := by simpa using hp.length_eq
      omega) := by
  simp [permOfList, List.Nodup.getEquivOfForallMemList_apply,
    List.get_eq_getElem]

def PrefixSet2 {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : Fin (n + 1)) : Set (Fin n) :=
  σ '' {j | j.castSucc < i}

def OrderingStep2 {n : ℕ} (s : Fin n)
    (σ τ : Equiv.Perm (Fin n)) : Prop :=
  ∀ i : Fin (n + 1), i.val % 2 ≠ (s.val + 1) % 2 → PrefixSet2 σ i = PrefixSet2 τ i

theorem mem_PrefixSet2_permOfList_iff {n : ℕ} (l : List (Fin n))
    (hp : l.Perm (List.finRange n)) (i : Fin (n + 1)) (x : Fin n) :
    x ∈ PrefixSet2 (permOfList l hp) i ↔ x ∈ l.take i.val := by
  have hlen : l.length = n := by simpa using hp.length_eq
  constructor
  · rintro ⟨j, hj, rfl⟩
    rw [List.mem_take_iff_getElem]
    refine ⟨j.val, ?_, ?_⟩
    · have hji : j.val < i.val := hj
      omega
    · exact permOfList_apply l hp j
  · intro hx
    rw [List.mem_take_iff_getElem] at hx
    obtain ⟨j, hj, hget⟩ := hx
    have hjn : j < n := by omega
    let jf : Fin n := ⟨j, hjn⟩
    refine ⟨jf, ?_, ?_⟩
    · change j < i.val
      omega
    · rw [permOfList_apply]
      exact hget

theorem mem_PrefixSet2_trans_permOfList_iff {n : ℕ} (l : List (Fin n))
    (hp : l.Perm (List.finRange n)) (π : Equiv.Perm (Fin n))
    (i : Fin (n + 1)) (x : Fin n) :
    x ∈ PrefixSet2 ((permOfList l hp).trans π) i ↔ π.symm x ∈ l.take i.val := by
  constructor
  · rintro ⟨j, hj, rfl⟩
    rw [← mem_PrefixSet2_permOfList_iff l hp]
    refine ⟨j, hj, ?_⟩
    simp
  · intro hx
    rw [← mem_PrefixSet2_permOfList_iff l hp] at hx
    obtain ⟨j, hj, hget⟩ := hx
    refine ⟨j, hj, ?_⟩
    simp only [Equiv.trans_apply]
    rw [hget]
    simp

theorem prefixSet2_trans_eq_of_take_perm {n : ℕ}
    (l m : List (Fin n))
    (hl : l.Perm (List.finRange n)) (hm : m.Perm (List.finRange n))
    (π : Equiv.Perm (Fin n)) (i : Fin (n + 1))
    (htake : (l.take i.val).Perm (m.take i.val)) :
    PrefixSet2 ((permOfList l hl).trans π) i =
      PrefixSet2 ((permOfList m hm).trans π) i := by
  ext x
  rw [mem_PrefixSet2_trans_permOfList_iff,
    mem_PrefixSet2_trans_permOfList_iff]
  exact htake.mem_iff

/-- Odd--even transposition routing, in the exact combinatorial form needed
for Lemma 2.1. -/
theorem oddEvenRoute2 {n : ℕ} (π : Equiv.Perm (Fin n)) :
    ∃ route : Fin (n + 1) → Equiv.Perm (Fin n),
      route 0 = Equiv.refl _ ∧
      route (Fin.last n) = π ∧
      ∀ s : Fin n, OrderingStep2 s (route s.castSucc) (route s.succ) := by
  classical
  let keys : List (Fin n) := (List.finRange n).map π.symm
  have hkeys : keys.Perm (List.finRange n) := by
    dsimp [keys]
    exact Equiv.Perm.map_finRange_perm π.symm
  have hstate : ∀ t : ℕ, (evolve 0 keys t).Perm (List.finRange n) :=
    fun t ↦ (evolve_perm 0 t keys).trans hkeys
  let route : Fin (n + 1) → Equiv.Perm (Fin n) := fun t ↦
    (permOfList (evolve 0 keys t.val) (hstate t.val)).trans π
  refine ⟨route, ?_, ?_, ?_⟩
  · have hkappa : permOfList (evolve 0 keys 0) (hstate 0) = π.symm := by
      ext i
      rw [permOfList_apply]
      simp [keys]
    change (permOfList (evolve 0 keys 0) (hstate 0)).trans π = Equiv.refl _
    rw [hkappa]
    exact π.symm_trans_self
  · have hsort : evolve 0 keys n = List.finRange n :=
      evolve_perm_finRange_eq keys hkeys 0
    have hkappa : permOfList (evolve 0 keys n) (hstate n) = Equiv.refl _ := by
      ext i
      rw [permOfList_apply]
      simp only [hsort]
      simp
    change (permOfList (evolve 0 keys n) (hstate n)).trans π = π
    rw [hkappa]
    exact Equiv.refl_trans π
  · intro s
    unfold OrderingStep2
    intro i hi
    have hinactive : active s.val i.val = false := by
      unfold active
      simp only [decide_eq_false_iff_not]
      exact hi
    have htake := (take_phaseN_perm_of_inactive s.val
      (evolve 0 keys s.val) i.val hinactive).symm
    change PrefixSet2
        ((permOfList (evolve 0 keys s.val) (hstate s.val)).trans π) i =
      PrefixSet2
        ((permOfList (evolve 0 keys (s.val + 1)) (hstate (s.val + 1))).trans π) i
    apply prefixSet2_trans_eq_of_take_perm
    simpa using htake
end OddEvenSorting

end PortOddEvenRoute

/- DegreeDiameter.Lemma21 -/
section PortLemma21

/-
# Alternating routes between complete flags

This file proves Lemma 2.1 in the same three visible stages as the paper:

1. invoke the separately proved common-basis theorem from `CommonBasis.lean`;
2. apply the separately proved `n`-round odd--even transposition route;
3. take prefix spans and verify that only ranks of the active parity change.

Indices are zero based in Lean: rank `i` is `space i`, while paper step
`s + 1` has Lean index `s`.
-/

open Module

namespace DegreeDiameter

variable (K V : Type*) [DivisionRing K] [AddCommGroup V] [Module K V]

/-- A purely combinatorial alternating layer. At layer `s + 1`, all prefix
sets of parity opposite to `s + 1` are unchanged. -/
def OrderingStep {n : ℕ} (s : Fin n)
    (σ τ : Equiv.Perm (Fin n)) : Prop :=
  ∀ i : Fin (n + 1), i.val % 2 ≠ (s.val + 1) % 2 → PrefixSet σ i = PrefixSet τ i

/-- Odd--even transposition routing, stated independently of linear algebra. -/
theorem oddEvenRoute {n : ℕ} (π : Equiv.Perm (Fin n)) :
    ∃ route : Fin (n + 1) → Equiv.Perm (Fin n),
      route 0 = 1 ∧
      route (Fin.last n) = π ∧
      ∀ s : Fin n, OrderingStep s (route s.castSucc) (route s.succ) := by
  obtain ⟨route, hzero, hlast, hstep⟩ := OddEvenSorting.oddEvenRoute2 π
  refine ⟨route, ?_, hlast, ?_⟩
  · change route 0 = Equiv.refl _
    exact hzero
  · simpa only [OrderingStep, PrefixSet, OddEvenSorting.OrderingStep2,
      OddEvenSorting.PrefixSet2] using hstep

theorem ofBasis_reindex_eq_at_of_prefixSet_eq {n : ℕ} (b : Basis (Fin n) K V)
    {σ τ : Equiv.Perm (Fin n)} {i : Fin (n + 1)} (h : PrefixSet σ i = PrefixSet τ i) :
    CompleteFlag.ofBasis (b.reindex σ.symm) i =
      CompleteFlag.ofBasis (b.reindex τ.symm) i := by
  rw [ofBasis_reindex_apply, ofBasis_reindex_apply, h]

/-- Step `s + 1` may change only ranks with the same parity as `s + 1`.
Equivalently, every rank of the other parity is frozen. -/
def AlternatingStep {n : ℕ} (s : Fin n)
    (F G : CompleteFlag K V n) : Prop :=
  ∀ i : Fin (n + 1), i.val % 2 ≠ (s.val + 1) % 2 → F i = G i

/-- Exact statement of Lemma 2.1: `route 0 = F`, `route n = F'`, and
the transition from `route s` to `route (s+1)` changes only ranks of the
parity prescribed by the one-based step number `s+1`. -/
theorem alternating_route {n : ℕ} (F F' : CompleteFlag K V n) :
    ∃ route : Fin (n + 1) → CompleteFlag K V n,
      route 0 = F ∧
      route (Fin.last n) = F' ∧
      ∀ s : Fin n, AlternatingStep K V s (route s.castSucc) (route s.succ) := by
  obtain ⟨b, π, hFspan, hF'span⟩ :=
    common_basis_orderings K V F F'
  have hF : F = CompleteFlag.ofBasis b := by
    apply CompleteFlag.ext
    intro i
    change F i = b.flag i
    simpa only [Module.Basis.flag] using hFspan i
  have hF' : F' = CompleteFlag.ofBasis (b.reindex π.symm) := by
    apply CompleteFlag.ext
    intro i
    rw [hF'span i]
    exact (ofBasis_reindex_apply K V b π i).symm
  obtain ⟨route, hroute0, hrouteLast, hrouteStep⟩ := oddEvenRoute π
  refine ⟨fun j ↦ CompleteFlag.ofBasis (b.reindex (route j).symm), ?_, ?_, ?_⟩
  · change CompleteFlag.ofBasis (b.reindex (route 0).symm) = F
    rw [hroute0]
    have hb : b.reindex (1 : Equiv.Perm (Fin n)).symm = b := by
      ext i
      simp
    rw [hb]
    exact hF.symm
  · change CompleteFlag.ofBasis (b.reindex (route (Fin.last n)).symm) = F'
    rw [hrouteLast]
    exact hF'.symm
  · intro s i hi
    exact ofBasis_reindex_eq_at_of_prefixSet_eq K V b (hrouteStep s i hi)

end DegreeDiameter

end PortLemma21

/- DegreeDiameter.HalvedFlags -/
section PortHalvedFlags

/-
# The halved flag graph

This file defines the two kinds of partial flags and their compatibility
relation exactly as in the paper.  A partial flag is represented by a full
rank-indexed family in which ranks of the other parity are replaced by `⊥`.
The fixed endpoint ranks are retained; this does not change the objects and
makes even and odd parts jointly determine a complete flag definitionally.
-/

open Module

namespace DegreeDiameter

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
  {n : ℕ}

/-- Keep the ranks congruent to `parity` modulo two and erase the others. -/
def flagPart (parity : ℕ) (F : CompleteFlag K V n) :
    Fin (n + 1) → Submodule K V :=
  fun i ↦ if i.val % 2 = parity % 2 then F i else ⊥

/-- Partial complete flags supported on one parity of ranks. -/
def PartialFlag (parity : ℕ) :=
  {P : Fin (n + 1) → Submodule K V //
    ∃ F : CompleteFlag K V n, flagPart parity F = P}

abbrev EvenPartialFlag := PartialFlag (K := K) (V := V) (n := n) 0
abbrev OddPartialFlag := PartialFlag (K := K) (V := V) (n := n) 1

namespace PartialFlag

instance {parity : ℕ} [Finite K] [Finite V] :
    Finite (PartialFlag (K := K) (V := V) (n := n) parity) := by
  letI : Finite (Submodule K V) :=
    Finite.of_injective (fun S : Submodule K V ↦ (S : Set V)) SetLike.coe_injective
  exact Finite.of_injective
    (fun P : PartialFlag (K := K) (V := V) (n := n) parity ↦ P.1)
    Subtype.val_injective


theorem ext {parity : ℕ}
    {P Q : PartialFlag (K := K) (V := V) (n := n) parity}
    (h : ∀ i, P.1 i = Q.1 i) : P = Q := by
  apply Subtype.ext
  exact funext h

/-- The partial flag of a complete flag at the selected parity. -/
def ofComplete (parity : ℕ) (F : CompleteFlag K V n) :
    PartialFlag (K := K) (V := V) (n := n) parity :=
  ⟨flagPart parity F, F, rfl⟩

@[simp]
theorem ofComplete_val (parity : ℕ) (F : CompleteFlag K V n) :
    (ofComplete parity F).1 = flagPart parity F := rfl

end PartialFlag

/-- An even and an odd partial flag are compatible when they are the two
parts of one complete flag. -/
def Compatible (P : EvenPartialFlag (K := K) (V := V) (n := n))
    (Q : OddPartialFlag (K := K) (V := V) (n := n)) : Prop :=
  ∃ F : CompleteFlag K V n,
    PartialFlag.ofComplete 0 F = P ∧ PartialFlag.ofComplete 1 F = Q

theorem compatible_parts (F : CompleteFlag K V n) :
    Compatible (PartialFlag.ofComplete 0 F) (PartialFlag.ofComplete 1 F) :=
  ⟨F, rfl, rfl⟩

/-- Even and odd parts determine their common complete flag uniquely. -/
theorem compatible_unique
    {P : EvenPartialFlag (K := K) (V := V) (n := n)}
    {Q : OddPartialFlag (K := K) (V := V) (n := n)}
    {F G : CompleteFlag K V n}
    (hF : PartialFlag.ofComplete 0 F = P)
    (hF' : PartialFlag.ofComplete 1 F = Q)
    (hG : PartialFlag.ofComplete 0 G = P)
    (hG' : PartialFlag.ofComplete 1 G = Q) : F = G := by
  apply CompleteFlag.ext
  intro i
  by_cases hi : i.val % 2 = 0
  · have h := congrFun (congrArg Subtype.val (hF.trans hG.symm)) i
    simpa [PartialFlag.ofComplete, flagPart, hi] using h
  · have hi' : i.val % 2 = 1 := by omega
    have h := congrFun (congrArg Subtype.val (hF'.trans hG'.symm)) i
    simpa [PartialFlag.ofComplete, flagPart, hi'] using h

/-- The graph on even partial flags in which distinct flags are adjacent when
they have a common compatible odd partial flag. -/
def halvedFlagGraph : SimpleGraph (EvenPartialFlag (K := K) (V := V) (n := n)) :=
  SimpleGraph.fromRel fun P P' ↦
    ∃ Q : OddPartialFlag (K := K) (V := V) (n := n),
      Compatible P Q ∧ Compatible P' Q

theorem halvedFlagGraph_adj_iff
    {P P' : EvenPartialFlag (K := K) (V := V) (n := n)} :
    (halvedFlagGraph (K := K) (V := V) (n := n)).Adj P P' ↔
      P ≠ P' ∧ ∃ Q : OddPartialFlag (K := K) (V := V) (n := n),
        Compatible P Q ∧ Compatible P' Q := by
  rw [halvedFlagGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hne, ⟨Q, hPQ, hP'Q⟩ | ⟨Q, hP'Q, hPQ⟩⟩
    · exact ⟨hne, Q, hPQ, hP'Q⟩
    · exact ⟨hne, Q, hPQ, hP'Q⟩
  · rintro ⟨hne, Q, hPQ, hP'Q⟩
    exact ⟨hne, Or.inl ⟨Q, hPQ, hP'Q⟩⟩

theorem evenPart_eq_of_alternatingStep {s : Fin n}
    {F G : CompleteFlag K V n} (h : AlternatingStep K V s F G)
    (hs : (s.val + 1) % 2 = 1) :
    PartialFlag.ofComplete 0 F = PartialFlag.ofComplete 0 G := by
  apply PartialFlag.ext
  intro i
  by_cases hi : i.val % 2 = 0
  · have hFG : F i = G i := h i (by omega)
    simpa [PartialFlag.ofComplete, flagPart, hi] using hFG
  · simp [PartialFlag.ofComplete, flagPart, hi]

theorem oddPart_eq_of_alternatingStep {s : Fin n}
    {F G : CompleteFlag K V n} (h : AlternatingStep K V s F G)
    (hs : (s.val + 1) % 2 = 0) :
    PartialFlag.ofComplete 1 F = PartialFlag.ofComplete 1 G := by
  apply PartialFlag.ext
  intro i
  by_cases hi : i.val % 2 = 1
  · have hFG : F i = G i := h i (by omega)
    simpa [PartialFlag.ofComplete, flagPart, hi] using hFG
  · have hi' : i.val % 2 ≠ 1 := hi
    simp [PartialFlag.ofComplete, flagPart, hi']

/-- Two even parts separated by an odd step and then an even step have
extended graph distance at most one. -/
theorem halved_edist_le_one_of_parts
    (F₀ F₁ F₂ : CompleteFlag K V n)
    (heven : PartialFlag.ofComplete 0 F₀ = PartialFlag.ofComplete 0 F₁)
    (hodd : PartialFlag.ofComplete 1 F₁ = PartialFlag.ofComplete 1 F₂) :
    (halvedFlagGraph (K := K) (V := V) (n := n)).edist
      (PartialFlag.ofComplete 0 F₀) (PartialFlag.ofComplete 0 F₂) ≤ 1 := by
  rw [SimpleGraph.edist_le_one_iff_adj_or_eq]
  by_cases heq : PartialFlag.ofComplete 0 F₀ = PartialFlag.ofComplete 0 F₂
  · exact Or.inr heq
  · apply Or.inl
    rw [halvedFlagGraph_adj_iff]
    refine ⟨heq, PartialFlag.ofComplete 1 F₁, ?_, ?_⟩
    · exact ⟨F₁, heven.symm, rfl⟩
    · exact ⟨F₂, rfl, hodd.symm⟩

/-- A chain with at most unit extended distance at every step has distance at
most its number of steps. -/
theorem edist_chain_le {W : Type*} (G : SimpleGraph W) (P : ℕ → W) :
    ∀ m : ℕ, (∀ j < m, G.edist (P j) (P (j + 1)) ≤ 1) →
      G.edist (P 0) (P m) ≤ m := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
      intro h
      calc
        G.edist (P 0) (P (m + 1)) ≤
            G.edist (P 0) (P m) + G.edist (P m) (P (m + 1)) :=
          G.edist_triangle
        _ ≤ (m : ℕ∞) + 1 :=
          add_le_add (ih fun j hj ↦ h j (Nat.lt_succ_of_lt hj)) (h m (Nat.lt_succ_self m))
        _ = (m + 1 : ℕ) := by simp

/-- The odd-first alternating route of Lemma 2.1 projects to a route of at
most `k` edges in the halved graph on a `(2*k+1)`-dimensional space. -/
theorem halvedFlagGraph_ediam_le (k : ℕ) :
    (halvedFlagGraph (K := K) (V := V) (n := 2 * k + 1)).ediam ≤ (k : ℕ∞) := by
  apply SimpleGraph.ediam_le_of_edist_le
  intro P P'
  obtain ⟨F, hF⟩ := P.property
  obtain ⟨F', hF'⟩ := P'.property
  have hPF : PartialFlag.ofComplete 0 F = P := by
    apply Subtype.ext
    exact hF
  have hPF' : PartialFlag.ofComplete 0 F' = P' := by
    apply Subtype.ext
    exact hF'
  obtain ⟨route, hroute₀, hrouteLast, hroute⟩ := alternating_route K V F F'
  let E : ℕ → EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1) := fun j ↦
    if hj : j ≤ k then
      PartialFlag.ofComplete 0 (route ⟨2 * j, by omega⟩)
    else P
  have hchain : ∀ j < k,
      (halvedFlagGraph (K := K) (V := V) (n := 2 * k + 1)).edist
        (E j) (E (j + 1)) ≤ 1 := by
    intro j hj
    have hj₀ : j ≤ k := Nat.le_of_lt hj
    have hj₁ : j + 1 ≤ k := by omega
    let sOdd : Fin (2 * k + 1) := ⟨2 * j, by omega⟩
    let sEven : Fin (2 * k + 1) := ⟨2 * j + 1, by omega⟩
    have heven :
        PartialFlag.ofComplete 0 (route sOdd.castSucc) =
          PartialFlag.ofComplete 0 (route sOdd.succ) :=
      evenPart_eq_of_alternatingStep (hroute sOdd) (by simp [sOdd])
    have hodd :
        PartialFlag.ofComplete 1 (route sEven.castSucc) =
          PartialFlag.ofComplete 1 (route sEven.succ) :=
      oddPart_eq_of_alternatingStep (hroute sEven) (by simp [sEven]; omega)
    have hdist := halved_edist_le_one_of_parts
      (route sOdd.castSucc) (route sOdd.succ) (route sEven.succ) heven (by
        simpa [sOdd, sEven] using hodd)
    have hstart : sOdd.castSucc = ⟨2 * j, by omega⟩ := by
      apply Fin.ext
      simp [sOdd]
    have hend : sEven.succ = ⟨2 * (j + 1), by omega⟩ := by
      apply Fin.ext
      simp [sEven]
      omega
    rw [hstart, hend] at hdist
    simpa [E, hj₀, hj₁] using hdist
  have hE₀ : E 0 = P := by
    simp [E, hroute₀, hPF]
  have hlastPart :
      PartialFlag.ofComplete 0 (route ⟨2 * k, by omega⟩) =
        PartialFlag.ofComplete 0 F' := by
    let sLast : Fin (2 * k + 1) := Fin.last (2 * k)
    have h := evenPart_eq_of_alternatingStep (hroute sLast) (by simp [sLast])
    have hstart : sLast.castSucc = ⟨2 * k, by omega⟩ := by
      apply Fin.ext
      simp [sLast]
    have hend : sLast.succ = Fin.last (2 * k + 1) := by
      apply Fin.ext
      simp [sLast]
    rw [hstart, hend, hrouteLast] at h
    exact h
  have hEk : E k = P' := by
    simp [E, hlastPart, hPF']
  simpa [hE₀, hEk] using
    (edist_chain_le (halvedFlagGraph (K := K) (V := V) (n := 2 * k + 1)) E k hchain)

end DegreeDiameter

end PortHalvedFlags

/- DegreeDiameter.ExactDiameter -/
section PortExactDiameter

/-
# The rank-potential lower bound for the halved flag graph

This file follows the reverse inequality in the diameter paragraph of
Proposition 3.1.  Relative to a fixed nonzero vector `e`, `evenEntryBlock`
records the first retained even rank containing `e` (with `k + 1` as the
sentinel when no retained even rank contains it).  The paper's potential is
exactly `2 * (evenEntryBlock - 1)`.

Compatibility with one odd partial flag lets the entry block move by at most
one.  The standard and reverse basis flags have entry blocks `1` and `k + 1`;
hence every walk between them has at least `k` edges.  Combined with the
odd--even route upper bound, this proves exact extended diameter `k`.
-/

open Module

namespace DegreeDiameter

variable {K : Type*} [DivisionRing K]

/-- The retained even rank `2*j` in dimension `2*k+1`. -/
def evenRank (k j : ℕ) (hj : j ≤ k) : Fin ((2 * k + 1) + 1) :=
  ⟨2 * j, by omega⟩

/-- A candidate entry block: either a positive retained even rank containing
`e`, or the sentinel `k+1`. -/
def EvenEntryCandidate {V : Type*} [AddCommGroup V] [Module K V]
    (k : ℕ) (e : V)
    (P : EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1))
    (j : ℕ) : Prop :=
  (1 ≤ j ∧ ∃ hj : j ≤ k, e ∈ P.1 (evenRank k j hj)) ∨ j = k + 1

theorem exists_evenEntryCandidate {V : Type*} [AddCommGroup V] [Module K V]
    (k : ℕ) (e : V)
    (P : EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1)) :
    ∃ j, EvenEntryCandidate k e P j :=
  ⟨k + 1, Or.inr rfl⟩

/-- The first positive retained even rank containing `e`, numbered in blocks;
the value is `k+1` if no retained even rank contains `e`. -/
noncomputable def evenEntryBlock {V : Type*} [AddCommGroup V] [Module K V]
    (k : ℕ) (e : V)
    (P : EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1)) : ℕ := by
  classical
  exact Nat.find (exists_evenEntryCandidate k e P)

theorem evenEntryBlock_spec {V : Type*} [AddCommGroup V] [Module K V]
    (k : ℕ) (e : V)
    (P : EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1)) :
    EvenEntryCandidate k e P (evenEntryBlock k e P) :=
  by
    classical
    exact Nat.find_spec (exists_evenEntryCandidate k e P)

theorem one_le_evenEntryBlock {V : Type*} [AddCommGroup V] [Module K V]
    (k : ℕ) (e : V)
    (P : EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1)) :
    1 ≤ evenEntryBlock k e P := by
  rcases evenEntryBlock_spec k e P with h | h
  · exact h.1
  · omega

theorem evenEntryBlock_le_sentinel {V : Type*} [AddCommGroup V] [Module K V]
    (k : ℕ) (e : V)
    (P : EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1)) :
    evenEntryBlock k e P ≤ k + 1 := by
  classical
  exact Nat.find_min' (exists_evenEntryCandidate k e P) (Or.inr rfl)

theorem evenEntryBlock_le_of_mem {V : Type*} [AddCommGroup V] [Module K V]
    (k : ℕ) (e : V)
    (P : EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1))
    (j : ℕ) (hj1 : 1 ≤ j) (hjk : j ≤ k)
    (hmem : e ∈ P.1 (evenRank k j hjk)) :
    evenEntryBlock k e P ≤ j := by
  classical
  exact Nat.find_min' (exists_evenEntryCandidate k e P)
    (Or.inl ⟨hj1, hjk, hmem⟩)

theorem evenEntryBlock_mem {V : Type*} [AddCommGroup V] [Module K V]
    (k : ℕ) (e : V)
    (P : EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1))
    (hblock : evenEntryBlock k e P ≤ k) :
    e ∈ P.1 (evenRank k (evenEntryBlock k e P) hblock) := by
  rcases evenEntryBlock_spec k e P with h | h
  · exact h.2.choose_spec
  · omega

theorem evenEntryBlock_ofComplete_le_of_mem
    {V : Type*} [AddCommGroup V] [Module K V]
    (k : ℕ) (e : V) (F : CompleteFlag K V (2 * k + 1))
    (j : ℕ) (hj1 : 1 ≤ j) (hjk : j ≤ k)
    (hmem : e ∈ F (evenRank k j hjk)) :
    evenEntryBlock k e (PartialFlag.ofComplete 0 F) ≤ j := by
  apply evenEntryBlock_le_of_mem k e (PartialFlag.ofComplete 0 F) j hj1 hjk
  simpa [PartialFlag.ofComplete, flagPart, evenRank] using hmem

/-- Compatibility with a common odd partial flag makes the first even entry
block move by at most one.  This is the paper's rank-potential estimate. -/
theorem evenEntryBlock_le_add_one_of_common_compatible
    {V : Type*} [AddCommGroup V] [Module K V]
    (k : ℕ) (e : V)
    {P P' : EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1)}
    {Q : OddPartialFlag (K := K) (V := V) (n := 2 * k + 1)}
    (hPQ : Compatible P Q) (hP'Q : Compatible P' Q) :
    evenEntryBlock k e P' ≤ evenEntryBlock k e P + 1 := by
  let a := evenEntryBlock k e P
  by_cases hak : a < k
  · have ha_le : a ≤ k := by omega
    have ha1 : 1 ≤ a := one_le_evenEntryBlock k e P
    have hmemP : e ∈ P.1 (evenRank k a ha_le) := evenEntryBlock_mem k e P ha_le
    obtain ⟨F, hFP, hFQ⟩ := hPQ
    obtain ⟨G, hGP', hGQ⟩ := hP'Q
    let ie : Fin ((2 * k + 1) + 1) := evenRank k a ha_le
    let io : Fin ((2 * k + 1) + 1) := ⟨2 * a + 1, by omega⟩
    let ie' : Fin ((2 * k + 1) + 1) := evenRank k (a + 1) (by omega)
    have heF : e ∈ F ie := by
      have hm : e ∈ (PartialFlag.ofComplete 0 F).1 ie := by
        rw [hFP]
        exact hmemP
      simpa [PartialFlag.ofComplete, flagPart, ie, evenRank] using hm
    have heFo : e ∈ F io := F.strictMono_space.monotone (by simp [ie, io, evenRank]) heF
    have heQ : e ∈ Q.1 io := by
      rw [← hFQ]
      simpa [PartialFlag.ofComplete, flagPart, io] using heFo
    have heGo : e ∈ G io := by
      have hm : e ∈ (PartialFlag.ofComplete 1 G).1 io := by
        rw [hGQ]
        exact heQ
      simpa [PartialFlag.ofComplete, flagPart, io] using hm
    have heGe : e ∈ G ie' :=
      G.strictMono_space.monotone (by simp [io, ie', evenRank]) heGo
    have heP' : e ∈ P'.1 ie' := by
      rw [← hGP']
      simpa [PartialFlag.ofComplete, flagPart, ie', evenRank] using heGe
    exact evenEntryBlock_le_of_mem k e P' (a + 1) (by omega) (by omega) heP'
  · have hka : k ≤ a := by omega
    exact (evenEntryBlock_le_sentinel k e P').trans (by omega)

theorem evenEntryBlock_adjacent
    {V : Type*} [AddCommGroup V] [Module K V]
    (k : ℕ) (e : V)
    {P P' : EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1)}
    (h : (halvedFlagGraph (K := K) (V := V) (n := 2 * k + 1)).Adj P P') :
    evenEntryBlock k e P' ≤ evenEntryBlock k e P + 1 := by
  obtain ⟨_, Q, hPQ, hP'Q⟩ := (halvedFlagGraph_adj_iff.mp h)
  exact evenEntryBlock_le_add_one_of_common_compatible k e hPQ hP'Q

/-- The rank potential `lambda` from the paper. -/
noncomputable def rankPotential {V : Type*} [AddCommGroup V] [Module K V]
    (k : ℕ) (e : V)
    (P : EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1)) : ℕ :=
  2 * (evenEntryBlock k e P - 1)

/-- Along a walk, the entry block changes by no more than its length. -/
theorem evenEntryBlock_walk_le
    {V : Type*} [AddCommGroup V] [Module K V]
    (k : ℕ) (e : V)
    {P P' : EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1)}
    (p : (halvedFlagGraph (K := K) (V := V) (n := 2 * k + 1)).Walk P P') :
    evenEntryBlock k e P' ≤ evenEntryBlock k e P + p.length := by
  induction p with
  | nil => simp
  | @cons P Q P' h p ih =>
      have hstep := evenEntryBlock_adjacent k e h
      calc
        evenEntryBlock k e P' ≤ evenEntryBlock k e Q + p.length := ih
        _ ≤ (evenEntryBlock k e P + 1) + p.length :=
          Nat.add_le_add_right hstep p.length
        _ = evenEntryBlock k e P + (SimpleGraph.Walk.cons h p).length := by
          simp
          omega

/-- The rank potential can increase by at most two per edge along a walk. -/
theorem rankPotential_walk_le
    {V : Type*} [AddCommGroup V] [Module K V]
    (k : ℕ) (e : V)
    {P P' : EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1)}
    (p : (halvedFlagGraph (K := K) (V := V) (n := 2 * k + 1)).Walk P P') :
    rankPotential k e P' ≤ rankPotential k e P + 2 * p.length := by
  have hblock := evenEntryBlock_walk_le k e p
  have hP := one_le_evenEntryBlock k e P
  have hP' := one_le_evenEntryBlock k e P'
  simp only [rankPotential]
  omega

section BasisEndpoints

variable {V : Type*} [AddCommGroup V] [Module K V]

theorem evenEntryBlock_standard_basis (k : ℕ) (hk : 1 ≤ k)
    (b : Basis (Fin (2 * k + 1)) K V) :
    evenEntryBlock k (b 0)
      (PartialFlag.ofComplete 0 (CompleteFlag.ofBasis b)) = 1 := by
  apply Nat.le_antisymm
  · apply evenEntryBlock_ofComplete_le_of_mem k (b 0)
      (CompleteFlag.ofBasis b) 1 (by omega) hk
    apply b.self_mem_flag
    change (0 : ℕ) < 2
    omega
  · exact one_le_evenEntryBlock k (b 0)
      (PartialFlag.ofComplete 0 (CompleteFlag.ofBasis b))

theorem evenEntryBlock_opposite_basis (k : ℕ)
    (b : Basis (Fin (2 * k + 1)) K V) :
    evenEntryBlock k (b 0)
      (PartialFlag.ofComplete 0
        (CompleteFlag.ofBasis (b.reindex Fin.revPerm))) = k + 1 := by
  apply Nat.le_antisymm (evenEntryBlock_le_sentinel k (b 0) _)
  let a := evenEntryBlock k (b 0)
    (PartialFlag.ofComplete 0
      (CompleteFlag.ofBasis (b.reindex Fin.revPerm)))
  have hspec : EvenEntryCandidate k (b 0)
      (PartialFlag.ofComplete 0
        (CompleteFlag.ofBasis (b.reindex Fin.revPerm))) a :=
    evenEntryBlock_spec k (b 0) _
  rcases hspec with hentry | hsentinel
  · obtain ⟨ha1, ha, hmem⟩ := hentry
    have hmemFlag : b 0 ∈
        (b.reindex Fin.revPerm).flag (evenRank k a ha) := by
      change b 0 ∈ flagPart 0
        (CompleteFlag.ofBasis (b.reindex Fin.revPerm)) (evenRank k a ha) at hmem
      rw [flagPart, if_pos (by simp [evenRank])] at hmem
      exact hmem
    have hb0 : b 0 = (b.reindex Fin.revPerm) (Fin.last (2 * k)) := by
      simp [Basis.reindex_apply]
    rw [hb0, (b.reindex Fin.revPerm).self_mem_flag_iff] at hmemFlag
    change 2 * k < 2 * a at hmemFlag
    omega
  · exact hsentinel.ge

theorem rankPotential_standard_basis (k : ℕ) (hk : 1 ≤ k)
    (b : Basis (Fin (2 * k + 1)) K V) :
    rankPotential k (b 0)
      (PartialFlag.ofComplete 0 (CompleteFlag.ofBasis b)) = 0 := by
  simp [rankPotential, evenEntryBlock_standard_basis k hk b]

theorem rankPotential_opposite_basis (k : ℕ)
    (b : Basis (Fin (2 * k + 1)) K V) :
    rankPotential k (b 0)
      (PartialFlag.ofComplete 0
        (CompleteFlag.ofBasis (b.reindex Fin.revPerm))) = 2 * k := by
  rw [rankPotential, evenEntryBlock_opposite_basis k b]
  omega

/-- Every walk from the standard flag to the opposite flag has at least `k`
edges, exactly as in the potential argument in Proposition 3.1. -/
theorem standard_to_opposite_walk_length (k : ℕ) (hk : 1 ≤ k)
    (b : Basis (Fin (2 * k + 1)) K V)
    (p : (halvedFlagGraph (K := K) (V := V) (n := 2 * k + 1)).Walk
      (PartialFlag.ofComplete 0 (CompleteFlag.ofBasis b))
      (PartialFlag.ofComplete 0
        (CompleteFlag.ofBasis (b.reindex Fin.revPerm)))) :
    k ≤ p.length := by
  have h := rankPotential_walk_le k (b 0) p
  rw [rankPotential_standard_basis k hk b,
    rankPotential_opposite_basis k b] at h
  omega

/-- The reverse inequality `k ≤ ediam`, witnessed by the standard and
opposite complete flags and proved with the paper's rank potential. -/
theorem halvedFlagGraph_ediam_ge_ofBasis (k : ℕ) (hk : 1 ≤ k)
    (b : Basis (Fin (2 * k + 1)) K V) :
    (k : ℕ∞) ≤
      (halvedFlagGraph (K := K) (V := V) (n := 2 * k + 1)).ediam := by
  let G := halvedFlagGraph (K := K) (V := V) (n := 2 * k + 1)
  let A := PartialFlag.ofComplete 0 (CompleteFlag.ofBasis b)
  let C := PartialFlag.ofComplete 0
    (CompleteFlag.ofBasis (b.reindex Fin.revPerm))
  have hupper : G.edist A C ≤ (k : ℕ∞) :=
    (SimpleGraph.edist_le_ediam (G := G)).trans
      (halvedFlagGraph_ediam_le (K := K) (V := V) k)
  have hfinite : G.edist A C ≠ ⊤ := by
    intro htop
    have : (⊤ : ℕ∞) ≤ (k : ℕ∞) := htop ▸ hupper
    simp at this
  obtain ⟨p, hp⟩ := SimpleGraph.exists_walk_of_edist_ne_top hfinite
  have hlength : k ≤ p.length := by
    exact standard_to_opposite_walk_length k hk b p
  have hdist : (k : ℕ∞) ≤ G.edist A C := by
    calc
      (k : ℕ∞) ≤ (p.length : ℕ∞) := by exact_mod_cast hlength
      _ = G.edist A C := hp
  exact hdist.trans SimpleGraph.edist_le_ediam

/-- The exact diameter assertion `diam H_{k,q}=k` from Proposition 3.1,
in extended-diameter form. -/
theorem halvedFlagGraph_ediam_eq_ofBasis (k : ℕ) (hk : 1 ≤ k)
    (b : Basis (Fin (2 * k + 1)) K V) :
    (halvedFlagGraph (K := K) (V := V) (n := 2 * k + 1)).ediam = (k : ℕ∞) :=
  le_antisymm (halvedFlagGraph_ediam_le (K := K) (V := V) k)
    (halvedFlagGraph_ediam_ge_ofBasis k hk b)

end BasisEndpoints

section CoordinateFlags

end CoordinateFlags

end DegreeDiameter

end PortExactDiameter

/- DegreeDiameter.CompletionCount -/
section PortCompletionCount

/-
# Exact counting of one-step refinements and parity completions

The interval between subspaces `U ⊆ W` whose ranks differ by two is
equivalent to the projective line of `W / U`.  We then prove that the choices
in the `k` disjoint rank-two intervals of a parity partial flag are genuinely
independent by constructing complete flags from arbitrary coordinate tuples.
The resulting equivalences give the exact completion multiplicity
`(|K| + 1)^k`; the neighbor-degree argument at the end deliberately remains
an injection, since a graph neighbor need not have a unique common odd part.
-/

open Module
open scoped LinearAlgebra.Projectivization

namespace DegreeDiameter

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Subspaces one rank above `U` and contained in `W`. -/
structure IntermediateSubspace (U W : Submodule K V) where
  space : Submodule K V
  lower : U ≤ space
  upper : space ≤ W
  finrank_space : finrank K space = finrank K U + 1

namespace IntermediateSubspace


theorem ext {U W : Submodule K V} {L L' : IntermediateSubspace U W}
    (h : L.space = L'.space) : L = L' := by
  cases L
  cases L'
  cases h
  rfl

instance {U W : Submodule K V} [Finite V] : Finite (IntermediateSubspace U W) := by
  letI : Finite (Submodule K V) :=
    Finite.of_injective (fun S : Submodule K V ↦ (S : Set V)) SetLike.coe_injective
  exact Finite.of_injective (fun L : IntermediateSubspace U W ↦ L.space) fun _ _ h ↦ ext h

end IntermediateSubspace

/-- Rank-nullity for the image of `L` in the quotient by a contained `U`. -/
theorem finrank_map_mkQ_add
    [FiniteDimensional K V] {U L : Submodule K V} (hUL : U ≤ L) :
    finrank K (L.map U.mkQ) + finrank K U = finrank K L := by
  have h := (U.mkQ.domRestrict L).finrank_range_add_finrank_ker
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict, Submodule.ker_mkQ] at h
  have hker : finrank K (U.comap L.subtype) = finrank K U :=
    (Submodule.comapSubtypeEquivOfLe hUL).finrank_eq
  simpa [hker] using h

section ProjectiveLine

variable [FiniteDimensional K V]

/-- The image of an intermediate subspace in `W / U`, regarded as a
one-dimensional subspace of the two-dimensional image of `W`. -/
noncomputable def intermediatePoint
    {U W : Submodule K V}
    (_hUW : U ≤ W) (_hW : finrank K W = finrank K U + 2)
    (L : IntermediateSubspace U W) : ℙ K (W.map U.mkQ) := by
  let qW : Submodule K (V ⧸ U) := W.map U.mkQ
  let qL : Submodule K (V ⧸ U) := L.space.map U.mkQ
  have hq : qL ≤ qW := Submodule.map_mono L.upper
  let inside : Submodule K qW := qL.comap qW.subtype
  have hqL := finrank_map_mkQ_add L.lower
  have hqL_one : finrank K qL = 1 := by
    dsimp [qL] at hqL ⊢
    rw [L.finrank_space] at hqL
    omega
  have hins : finrank K inside = finrank K qL :=
    (Submodule.comapSubtypeEquivOfLe hq).finrank_eq
  exact Projectivization.mk'' inside (hins.trans hqL_one)

theorem intermediatePoint_injective
    {U W : Submodule K V}
    (hUW : U ≤ W) (hW : finrank K W = finrank K U + 2) :
    Function.Injective (intermediatePoint hUW hW) := by
  intro L L' hpoint
  apply IntermediateSubspace.ext
  let qW : Submodule K (V ⧸ U) := W.map U.mkQ
  let qL : Submodule K (V ⧸ U) := L.space.map U.mkQ
  let qL' : Submodule K (V ⧸ U) := L'.space.map U.mkQ
  have hq : qL ≤ qW := Submodule.map_mono L.upper
  have hq' : qL' ≤ qW := Submodule.map_mono L'.upper
  have hins : qL.comap qW.subtype = qL'.comap qW.subtype := by
    have := congrArg Projectivization.submodule hpoint
    simpa [intermediatePoint, qW, qL, qL'] using this
  have hquot : qL = qL' := by
    have hm := congrArg (fun S : Submodule K qW ↦ S.map qW.subtype) hins
    simpa [Submodule.map_comap_subtype, inf_eq_right.mpr hq,
      inf_eq_right.mpr hq'] using hm
  have hrecover := congrArg (fun S : Submodule K (V ⧸ U) ↦ S.comap U.mkQ) hquot
  simpa [qL, qL', Submodule.comap_map_mkQ, sup_eq_right.mpr L.lower,
    sup_eq_right.mpr L'.lower] using hrecover

/-- Pull a projective point in `W / U` back to the unique intermediate
subspace of `V`. This explicit pullback is inverse to `intermediatePoint`. -/
noncomputable def intermediateSubspaceOfPoint
    {U W : Submodule K V}
    (hUW : U ≤ W) (p : ℙ K (W.map U.mkQ)) : IntermediateSubspace U W := by
  let qW : Submodule K (V ⧸ U) := W.map U.mkQ
  let T : Submodule K (V ⧸ U) := p.submodule.map qW.subtype
  let L : Submodule K V := T.comap U.mkQ
  have hTqW : T ≤ qW := by
    intro x hx
    rcases hx with ⟨y, hy, rfl⟩
    exact y.property
  have hUL : U ≤ L := by
    intro x hx
    change U.mkQ x ∈ T
    have hxker : x ∈ LinearMap.ker U.mkQ := by
      simpa [Submodule.ker_mkQ] using hx
    rw [LinearMap.mem_ker.mp hxker]
    exact T.zero_mem
  have hLW : L ≤ W := by
    intro x hx
    have hxqW : U.mkQ x ∈ qW := hTqW hx
    rcases hxqW with ⟨w, hwW, hw⟩
    have hdiff : x - w ∈ U :=
      (Submodule.Quotient.eq U).mp (by simpa [Submodule.mkQ_apply] using hw.symm)
    have hsum : x - w + w = x := sub_add_cancel x w
    rw [← hsum]
    exact W.add_mem (hUW hdiff) hwW
  have hcomap : T.comap qW.subtype = p.submodule := by
    ext x
    constructor
    · rintro ⟨y, hy, hxy⟩
      have : y = x := Subtype.ext hxy
      simpa [this] using hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hTfinrank : finrank K T = 1 := by
    have h := (Submodule.comapSubtypeEquivOfLe hTqW).finrank_eq
    rw [hcomap, Projectivization.finrank_submodule] at h
    exact h.symm
  have himage : L.map U.mkQ = T := by
    simpa [L] using
      (Submodule.map_comap_eq_of_surjective U.mkQ_surjective T)
  refine ⟨L, hUL, hLW, ?_⟩
  have hrank := finrank_map_mkQ_add hUL
  rw [himage, hTfinrank] at hrank
  omega

/-- The quotient-image construction and pullback construction are inverse:
rank-two subspace intervals are exactly projective lines. -/
theorem intermediatePoint_surjective
    {U W : Submodule K V}
    (hUW : U ≤ W) (hW : finrank K W = finrank K U + 2) :
    Function.Surjective (intermediatePoint hUW hW) := by
  intro p
  refine ⟨intermediateSubspaceOfPoint hUW p, ?_⟩
  apply Projectivization.submodule_injective
  let qW : Submodule K (V ⧸ U) := W.map U.mkQ
  let T : Submodule K (V ⧸ U) := p.submodule.map qW.subtype
  have hTqW : T ≤ qW := by
    intro x hx
    rcases hx with ⟨y, hy, rfl⟩
    exact y.property
  have hcomap : T.comap qW.subtype = p.submodule := by
    ext x
    constructor
    · rintro ⟨y, hy, hxy⟩
      have : y = x := Subtype.ext hxy
      simpa [this] using hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  have himage :
      (intermediateSubspaceOfPoint hUW p).space.map U.mkQ = T := by
    change (T.comap U.mkQ).map U.mkQ = T
    exact Submodule.map_comap_eq_of_surjective U.mkQ_surjective T
  simpa [intermediatePoint, qW, himage, hcomap]

/-- The genuine bijection between a rank-two interval and its projective
line. -/
noncomputable def intermediateSubspaceEquivProjectiveLine
    {U W : Submodule K V}
    (hUW : U ≤ W) (hW : finrank K W = finrank K U + 2) :
    IntermediateSubspace U W ≃ ℙ K (W.map U.mkQ) :=
  Equiv.ofBijective (intermediatePoint hUW hW)
    ⟨intermediatePoint_injective hUW hW,
      intermediatePoint_surjective hUW hW⟩

/-- Exactly `|K| + 1` subspaces occur in a rank-two interval. -/
theorem natCard_intermediate_eq
    [Finite K] [Finite V]
    {U W : Submodule K V}
    (hUW : U ≤ W) (hW : finrank K W = finrank K U + 2) :
    Nat.card (IntermediateSubspace U W) = Nat.card K + 1 := by
  letI : Fintype V := Fintype.ofFinite V
  let qW : Submodule K (V ⧸ U) := W.map U.mkQ
  have hqW := finrank_map_mkQ_add hUW
  have hqW_two : finrank K qW = 2 := by
    dsimp [qW] at hqW ⊢
    rw [hW] at hqW
    omega
  calc
    Nat.card (IntermediateSubspace U W) = Nat.card (ℙ K qW) :=
      Nat.card_congr (intermediateSubspaceEquivProjectiveLine hUW hW)
    _ = Nat.card K + 1 := Projectivization.card_of_finrank_two K qW hqW_two

end ProjectiveLine

section PartialFlagCompletions

variable [FiniteDimensional K V] [Finite K] [Finite V]

/-- Consecutive retained even ranks surrounding the `j`-th missing odd rank. -/
def evenLowerRank (k : ℕ) (j : Fin k) : Fin ((2 * k + 1) + 1) :=
  ⟨2 * j.val, by omega⟩

def oddMiddleRank (k : ℕ) (j : Fin k) : Fin ((2 * k + 1) + 1) :=
  ⟨2 * j.val + 1, by omega⟩

def evenUpperRank (k : ℕ) (j : Fin k) : Fin ((2 * k + 1) + 1) :=
  ⟨2 * j.val + 2, by omega⟩

/-- Consecutive retained odd ranks surrounding the `j`-th missing positive
even rank. -/
def oddLowerRank (k : ℕ) (j : Fin k) : Fin ((2 * k + 1) + 1) :=
  ⟨2 * j.val + 1, by omega⟩

def evenMiddleRank (k : ℕ) (j : Fin k) : Fin ((2 * k + 1) + 1) :=
  ⟨2 * j.val + 2, by omega⟩

def oddUpperRank (k : ℕ) (j : Fin k) : Fin ((2 * k + 1) + 1) :=
  ⟨2 * j.val + 3, by omega⟩

@[simp] theorem evenLowerRank_val (k : ℕ) (j : Fin k) :
    (evenLowerRank k j).val = 2 * j.val := rfl
@[simp] theorem oddMiddleRank_val (k : ℕ) (j : Fin k) :
    (oddMiddleRank k j).val = 2 * j.val + 1 := rfl
@[simp] theorem evenUpperRank_val (k : ℕ) (j : Fin k) :
    (evenUpperRank k j).val = 2 * j.val + 2 := rfl
@[simp] theorem oddLowerRank_val (k : ℕ) (j : Fin k) :
    (oddLowerRank k j).val = 2 * j.val + 1 := rfl
@[simp] theorem evenMiddleRank_val (k : ℕ) (j : Fin k) :
    (evenMiddleRank k j).val = 2 * j.val + 2 := rfl
@[simp] theorem oddUpperRank_val (k : ℕ) (j : Fin k) :
    (oddUpperRank k j).val = 2 * j.val + 3 := rfl

theorem ofComplete_space_eq_of_mod
    {n parity : ℕ} {F : CompleteFlag K V n}
    {P : PartialFlag (K := K) (V := V) (n := n) parity}
    (h : PartialFlag.ofComplete parity F = P) (i : Fin (n + 1))
    (hi : i.val % 2 = parity % 2) : F i = P.1 i := by
  have hi' := congrFun (congrArg Subtype.val h) i
  simpa [PartialFlag.ofComplete, flagPart, hi] using hi'

/-- A represented partial flag is bottom at every erased rank. -/
theorem partialFlag_space_eq_bot_of_mod_ne
    {n parity : ℕ}
    (P : PartialFlag (K := K) (V := V) (n := n) parity)
    (i : Fin (n + 1)) (hi : i.val % 2 ≠ parity % 2) : P.1 i = ⊥ := by
  obtain ⟨F, hF⟩ := P.property
  have hi' := congrFun hF i
  simpa [flagPart, hi] using hi'.symm

/-- At every retained rank a partial flag has the prescribed dimension. -/
theorem partialFlag_finrank_space_of_mod
    {n parity : ℕ}
    (P : PartialFlag (K := K) (V := V) (n := n) parity)
    (i : Fin (n + 1)) (hi : i.val % 2 = parity % 2) :
    finrank K (P.1 i) = i.val := by
  obtain ⟨F, hF⟩ := P.property
  have hPF : PartialFlag.ofComplete parity F = P := Subtype.ext hF
  rw [← ofComplete_space_eq_of_mod hPF i hi, F.finrank_space]

/-- The existence of a partial flag already fixes the dimension of the
ambient space. -/
theorem finrank_eq_of_partialFlag
    {n parity : ℕ}
    (P : PartialFlag (K := K) (V := V) (n := n) parity) :
    finrank K V = n := by
  obtain ⟨F, _hF⟩ := P.property
  rw [← finrank_top K V, ← F.space_last, F.finrank_space]
  rfl

/-- Package a ranked adjacent chain as a complete flag.  Strictness follows
from adjacent containment together with the one-rank dimension increase. -/
def completeFlagOfRankedSpaces {n : ℕ}
    (S : Fin (n + 1) → Submodule K V)
    (hrank : ∀ i, finrank K (S i) = i.val)
    (hstep : ∀ i : Fin n, S i.castSucc ≤ S i.succ)
    (hzero : S 0 = ⊥) (hlast : S (Fin.last n) = ⊤) :
    CompleteFlag K V n where
  space := S
  strictMono_space := Fin.strictMono_iff_lt_succ.2 fun i ↦ by
    have hle := hstep i
    exact lt_of_le_of_ne hle fun heq ↦ by
      have h := congrArg (fun T : Submodule K V ↦ finrank K T) heq
      rw [hrank, hrank] at h
      simp at h
  finrank_space := hrank
  space_zero := hzero
  space_last := hlast

@[simp]
theorem completeFlagOfRankedSpaces_apply {n : ℕ}
    (S : Fin (n + 1) → Submodule K V)
    (hrank : ∀ i, finrank K (S i) = i.val)
    (hstep : ∀ i : Fin n, S i.castSucc ≤ S i.succ)
    (hzero : S 0 = ⊥) (hlast : S (Fin.last n) = ⊤)
    (i : Fin (n + 1)) :
    completeFlagOfRankedSpaces S hrank hstep hzero hlast i = S i := rfl

/-- The product of the `k` projective-line intervals in which an even
partial flag can be completed. -/
abbrev EvenCompletionCoordinates (k : ℕ)
    (P : EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1)) :=
  ∀ j : Fin k,
    IntermediateSubspace (P.1 (evenLowerRank k j)) (P.1 (evenUpperRank k j))

/-- The common complete flag selected from a compatible pair.  Its
uniqueness was proved in `compatible_unique`; choice is used only to define
the counting injection. -/
noncomputable def completeOfEvenCompatibility (k : ℕ)
    (P : EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1))
    (x : {Q : OddPartialFlag (K := K) (V := V) (n := 2 * k + 1) // Compatible P Q}) :
    CompleteFlag K V (2 * k + 1) :=
  Classical.choose x.property

theorem completeOfEvenCompatibility_even (k : ℕ)
    (P : EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1))
    (x : {Q : OddPartialFlag (K := K) (V := V) (n := 2 * k + 1) // Compatible P Q}) :
    PartialFlag.ofComplete 0 (completeOfEvenCompatibility k P x) = P :=
  (Classical.choose_spec x.property).1

theorem completeOfEvenCompatibility_odd (k : ℕ)
    (P : EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1))
    (x : {Q : OddPartialFlag (K := K) (V := V) (n := 2 * k + 1) // Compatible P Q}) :
    PartialFlag.ofComplete 1 (completeOfEvenCompatibility k P x) = x.1 :=
  (Classical.choose_spec x.property).2

noncomputable def evenCompletionCoordinates (k : ℕ)
    (P : EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1)) :
    {Q : OddPartialFlag (K := K) (V := V) (n := 2 * k + 1) // Compatible P Q} →
      EvenCompletionCoordinates k P :=
  fun x j ↦ by
    let F := completeOfEvenCompatibility k P x
    have hEven := completeOfEvenCompatibility_even k P x
    have hlow : F (evenLowerRank k j) = P.1 (evenLowerRank k j) :=
      ofComplete_space_eq_of_mod hEven _ (by simp [evenLowerRank])
    have hhigh : F (evenUpperRank k j) = P.1 (evenUpperRank k j) :=
      ofComplete_space_eq_of_mod hEven _ (by simp [evenUpperRank])
    refine ⟨F (oddMiddleRank k j), ?_, ?_, ?_⟩
    · rw [← hlow]
      exact F.strictMono_space.monotone (by simp [evenLowerRank, oddMiddleRank])
    · rw [← hhigh]
      exact F.strictMono_space.monotone (by simp [oddMiddleRank, evenUpperRank])
    · rw [F.finrank_space]
      have hlowrank := F.finrank_space (evenLowerRank k j)
      rw [hlow] at hlowrank
      rw [hlowrank]
      simp [oddMiddleRank, evenLowerRank]

@[simp]
theorem evenCompletionCoordinates_space (k : ℕ)
    (P : EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1))
    (x : {Q : OddPartialFlag (K := K) (V := V) (n := 2 * k + 1) // Compatible P Q})
    (j : Fin k) :
    (evenCompletionCoordinates k P x j).space =
      completeOfEvenCompatibility k P x (oddMiddleRank k j) := rfl

theorem evenCompletionCoordinates_injective (k : ℕ)
    (P : EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1)) :
    Function.Injective (evenCompletionCoordinates k P) := by
  intro x y hxy
  let F := completeOfEvenCompatibility k P x
  let G := completeOfEvenCompatibility k P y
  have hEvenF := completeOfEvenCompatibility_even k P x
  have hEvenG := completeOfEvenCompatibility_even k P y
  have hFG : F = G := by
    apply CompleteFlag.ext
    intro i
    by_cases hi : i.val % 2 = 0
    · exact (ofComplete_space_eq_of_mod hEvenF i hi).trans
        (ofComplete_space_eq_of_mod hEvenG i hi).symm
    · have hiOdd : i.val % 2 = 1 := by omega
      by_cases hlast : i.val = 2 * k + 1
      · have hiLast : i = Fin.last (2 * k + 1) := by ext; simpa using hlast
        rw [hiLast, F.space_last, G.space_last]
      · have hiLt : i.val < 2 * k + 1 := by omega
        let j : Fin k := ⟨i.val / 2, by omega⟩
        have hij : i = oddMiddleRank k j := by
          apply Fin.ext
          simp [j, oddMiddleRank]
          omega
        have hs := congrArg (fun c ↦ (c j).space) hxy
        simpa [F, G, hij] using hs
  apply Subtype.ext
  calc
    x.1 = PartialFlag.ofComplete 1 F :=
      (completeOfEvenCompatibility_odd k P x).symm
    _ = PartialFlag.ofComplete 1 G := congrArg (PartialFlag.ofComplete 1) hFG
    _ = y.1 := completeOfEvenCompatibility_odd k P y

theorem evenBoundary_le (k : ℕ)
    (P : EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1)) (j : Fin k) :
    P.1 (evenLowerRank k j) ≤ P.1 (evenUpperRank k j) := by
  obtain ⟨F, hF⟩ := P.property
  have hPF : PartialFlag.ofComplete 0 F = P := Subtype.ext hF
  rw [← ofComplete_space_eq_of_mod hPF _ (by simp [evenLowerRank]),
    ← ofComplete_space_eq_of_mod hPF _ (by simp [evenUpperRank])]
  exact F.strictMono_space.monotone (by simp [evenLowerRank, evenUpperRank])

theorem evenBoundary_finrank (k : ℕ)
    (P : EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1)) (j : Fin k) :
    finrank K (P.1 (evenUpperRank k j)) =
      finrank K (P.1 (evenLowerRank k j)) + 2 := by
  obtain ⟨F, hF⟩ := P.property
  have hPF : PartialFlag.ofComplete 0 F = P := Subtype.ext hF
  rw [← ofComplete_space_eq_of_mod hPF _ (by simp),
    ← ofComplete_space_eq_of_mod hPF _ (by simp),
    F.finrank_space, F.finrank_space]
  simp [evenLowerRank, evenUpperRank]

/-- Interleave arbitrary rank-one choices in the rank-two intervals of an
even partial flag; the final odd rank is the ambient top space. -/
def evenCompletedSpace (k : ℕ)
    (P : EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1))
    (c : EvenCompletionCoordinates k P) :
    Fin ((2 * k + 1) + 1) → Submodule K V := fun i ↦
  if hi : i.val % 2 = 0 then P.1 i
  else if _hlast : i.val = 2 * k + 1 then ⊤
  else (c ⟨i.val / 2, by omega⟩).space

@[simp]
theorem evenCompletedSpace_of_even (k : ℕ)
    (P : EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1))
    (c : EvenCompletionCoordinates k P) (i : Fin ((2 * k + 1) + 1))
    (hi : i.val % 2 = 0) : evenCompletedSpace k P c i = P.1 i := by
  simp [evenCompletedSpace, hi]

@[simp]
theorem evenCompletedSpace_oddMiddle (k : ℕ)
    (P : EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1))
    (c : EvenCompletionCoordinates k P) (j : Fin k) :
    evenCompletedSpace k P c (oddMiddleRank k j) = (c j).space := by
  have hparity : (oddMiddleRank k j).val % 2 ≠ 0 := by
    simp [oddMiddleRank]
  have hlast : (oddMiddleRank k j).val ≠ 2 * k + 1 := by
    simp [oddMiddleRank]
    omega
  have hindex :
      (⟨(oddMiddleRank k j).val / 2, by omega⟩ : Fin k) = j := by
    apply Fin.ext
    change (2 * j.val + 1) / 2 = j.val
    rw [Nat.mul_add_div (by omega)]
    simp
  unfold evenCompletedSpace
  rw [dif_neg hparity, dif_neg hlast, hindex]

@[simp]
theorem evenCompletedSpace_last (k : ℕ)
    (P : EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1))
    (c : EvenCompletionCoordinates k P) :
    evenCompletedSpace k P c (Fin.last (2 * k + 1)) = ⊤ := by
  simp [evenCompletedSpace]

/-- Every coordinate tuple over an even partial flag assembles into a
complete flag.  This is the formal independence assertion for the missing
odd ranks. -/
noncomputable def completeFlagOfEvenCoordinates (k : ℕ)
    (P : EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1))
    (c : EvenCompletionCoordinates k P) : CompleteFlag K V (2 * k + 1) :=
  completeFlagOfRankedSpaces (evenCompletedSpace k P c) (by
    intro i
    by_cases hi : i.val % 2 = 0
    · rw [evenCompletedSpace_of_even k P c i hi]
      exact partialFlag_finrank_space_of_mod P i hi
    · have hiOdd : i.val % 2 = 1 := by omega
      by_cases hlast : i.val = 2 * k + 1
      · have hiLast : i = Fin.last (2 * k + 1) := by
          apply Fin.ext
          simpa using hlast
        rw [hiLast, evenCompletedSpace_last, finrank_top,
          finrank_eq_of_partialFlag P]
        simp
      · let j : Fin k := ⟨i.val / 2, by omega⟩
        have hij : i = oddMiddleRank k j := by
          apply Fin.ext
          simp [j, oddMiddleRank]
          omega
        rw [hij, evenCompletedSpace_oddMiddle,
          (c j).finrank_space,
          partialFlag_finrank_space_of_mod P (evenLowerRank k j) (by simp)]
        simp [evenLowerRank, oddMiddleRank]) (by
    intro i
    by_cases hi : i.val % 2 = 0
    · have hiNext : (i.val + 1) % 2 ≠ 0 := by omega
      by_cases hlast : i.val + 1 = 2 * k + 1
      · simp [evenCompletedSpace, hi, hiNext, hlast]
      · let j : Fin k := ⟨i.val / 2, by omega⟩
        have hsource : i.castSucc = evenLowerRank k j := by
          apply Fin.ext
          simp [j, evenLowerRank]
          omega
        have htarget : i.succ = oddMiddleRank k j := by
          apply Fin.ext
          simp [j, oddMiddleRank]
          omega
        rw [hsource, htarget, evenCompletedSpace_of_even,
          evenCompletedSpace_oddMiddle]
        · exact (c j).lower
        · simp [evenLowerRank]
    · have hiOdd : i.val % 2 = 1 := by omega
      let j : Fin k := ⟨i.val / 2, by omega⟩
      have hsource : i.castSucc = oddMiddleRank k j := by
        apply Fin.ext
        simp [j, oddMiddleRank]
        omega
      have htarget : i.succ = evenUpperRank k j := by
        apply Fin.ext
        simp [j, evenUpperRank]
        omega
      rw [hsource, htarget, evenCompletedSpace_oddMiddle,
        evenCompletedSpace_of_even]
      · exact (c j).upper
      · simp [evenUpperRank]) (by
    rw [evenCompletedSpace_of_even]
    · obtain ⟨F, hF⟩ := P.property
      have hPF : PartialFlag.ofComplete 0 F = P := Subtype.ext hF
      rw [← ofComplete_space_eq_of_mod hPF 0 (by simp), F.space_zero]
    · simp) (evenCompletedSpace_last k P c)

@[simp]
theorem completeFlagOfEvenCoordinates_apply (k : ℕ)
    (P : EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1))
    (c : EvenCompletionCoordinates k P) (i : Fin ((2 * k + 1) + 1)) :
    completeFlagOfEvenCoordinates k P c i = evenCompletedSpace k P c i := rfl

theorem completeFlagOfEvenCoordinates_evenPart (k : ℕ)
    (P : EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1))
    (c : EvenCompletionCoordinates k P) :
    PartialFlag.ofComplete 0 (completeFlagOfEvenCoordinates k P c) = P := by
  apply PartialFlag.ext
  intro i
  by_cases hi : i.val % 2 = 0
  · simp [PartialFlag.ofComplete, flagPart, hi]
  · rw [partialFlag_space_eq_bot_of_mod_ne P i (by simpa using hi)]
    simp [PartialFlag.ofComplete, flagPart, hi]

/-- The compatible odd part assembled from an arbitrary coordinate tuple. -/
noncomputable def oddCompatibleOfEvenCoordinates (k : ℕ)
    (P : EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1))
    (c : EvenCompletionCoordinates k P) :
    {Q : OddPartialFlag (K := K) (V := V) (n := 2 * k + 1) // Compatible P Q} :=
  ⟨PartialFlag.ofComplete 1 (completeFlagOfEvenCoordinates k P c),
    completeFlagOfEvenCoordinates k P c,
    completeFlagOfEvenCoordinates_evenPart k P c, rfl⟩

theorem evenCompletionCoordinates_rightInverse (k : ℕ)
    (P : EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1)) :
    Function.RightInverse (oddCompatibleOfEvenCoordinates k P)
      (evenCompletionCoordinates k P) := by
  intro c
  funext j
  apply IntermediateSubspace.ext
  let x := oddCompatibleOfEvenCoordinates k P c
  have hchosen : completeOfEvenCompatibility k P x =
      completeFlagOfEvenCoordinates k P c :=
    compatible_unique
      (completeOfEvenCompatibility_even k P x)
      (completeOfEvenCompatibility_odd k P x)
      (completeFlagOfEvenCoordinates_evenPart k P c) rfl
  simpa [x, hchosen] using
    (evenCompletionCoordinates_space k P x j)

/-- Compatible odd parts are exactly independent products of the `k`
rank-two intervals. -/
noncomputable def evenCompletionEquiv (k : ℕ)
    (P : EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1)) :
    {Q : OddPartialFlag (K := K) (V := V) (n := 2 * k + 1) // Compatible P Q} ≃
      EvenCompletionCoordinates k P where
  toFun := evenCompletionCoordinates k P
  invFun := oddCompatibleOfEvenCoordinates k P
  left_inv x := (evenCompletionCoordinates_injective k P)
    (evenCompletionCoordinates_rightInverse k P (evenCompletionCoordinates k P x))
  right_inv := evenCompletionCoordinates_rightInverse k P

/-- An even partial flag has exactly `(q+1)^k` compatible odd parts. -/
theorem natCard_odd_compatible_eq (k : ℕ)
    (P : EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1)) :
    Nat.card {Q : OddPartialFlag (K := K) (V := V) (n := 2 * k + 1) // Compatible P Q} =
      (Nat.card K + 1) ^ k := by
  calc
    Nat.card {Q : OddPartialFlag (K := K) (V := V) (n := 2 * k + 1) // Compatible P Q} =
        Nat.card (EvenCompletionCoordinates k P) :=
      Nat.card_congr (evenCompletionEquiv k P)
    _ = ∏ j : Fin k, Nat.card
          (IntermediateSubspace (P.1 (evenLowerRank k j)) (P.1 (evenUpperRank k j))) :=
      Nat.card_pi
    _ = ∏ _j : Fin k, (Nat.card K + 1) := by
      apply Finset.prod_congr rfl
      intro j _hj
      exact natCard_intermediate_eq
        (evenBoundary_le k P j) (evenBoundary_finrank k P j)
    _ = (Nat.card K + 1) ^ k := by simp

/-- The upper bound as a direct corollary of the exact completion count. -/
theorem natCard_odd_compatible_le (k : ℕ)
    (P : EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1)) :
    Nat.card {Q : OddPartialFlag (K := K) (V := V) (n := 2 * k + 1) // Compatible P Q} ≤
      (Nat.card K + 1) ^ k := by
  exact (natCard_odd_compatible_eq k P).le

/- The dual-parity completion count. -/

abbrev OddCompletionCoordinates (k : ℕ)
    (Q : OddPartialFlag (K := K) (V := V) (n := 2 * k + 1)) :=
  ∀ j : Fin k,
    IntermediateSubspace (Q.1 (oddLowerRank k j)) (Q.1 (oddUpperRank k j))

noncomputable def completeOfOddCompatibility (k : ℕ)
    (Q : OddPartialFlag (K := K) (V := V) (n := 2 * k + 1))
    (x : {P : EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1) // Compatible P Q}) :
    CompleteFlag K V (2 * k + 1) :=
  Classical.choose x.property

theorem completeOfOddCompatibility_even (k : ℕ)
    (Q : OddPartialFlag (K := K) (V := V) (n := 2 * k + 1))
    (x : {P : EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1) // Compatible P Q}) :
    PartialFlag.ofComplete 0 (completeOfOddCompatibility k Q x) = x.1 :=
  (Classical.choose_spec x.property).1

theorem completeOfOddCompatibility_odd (k : ℕ)
    (Q : OddPartialFlag (K := K) (V := V) (n := 2 * k + 1))
    (x : {P : EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1) // Compatible P Q}) :
    PartialFlag.ofComplete 1 (completeOfOddCompatibility k Q x) = Q :=
  (Classical.choose_spec x.property).2

noncomputable def oddCompletionCoordinates (k : ℕ)
    (Q : OddPartialFlag (K := K) (V := V) (n := 2 * k + 1)) :
    {P : EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1) // Compatible P Q} →
      OddCompletionCoordinates k Q :=
  fun x j ↦ by
    let F := completeOfOddCompatibility k Q x
    have hOdd := completeOfOddCompatibility_odd k Q x
    have hlow : F (oddLowerRank k j) = Q.1 (oddLowerRank k j) :=
      ofComplete_space_eq_of_mod hOdd _ (by simp [oddLowerRank])
    have hhigh : F (oddUpperRank k j) = Q.1 (oddUpperRank k j) :=
      ofComplete_space_eq_of_mod hOdd _ (by simp [oddUpperRank])
    refine ⟨F (evenMiddleRank k j), ?_, ?_, ?_⟩
    · rw [← hlow]
      exact F.strictMono_space.monotone (by simp [oddLowerRank, evenMiddleRank])
    · rw [← hhigh]
      exact F.strictMono_space.monotone (by simp [evenMiddleRank, oddUpperRank])
    · rw [F.finrank_space]
      have hlowrank := F.finrank_space (oddLowerRank k j)
      rw [hlow] at hlowrank
      rw [hlowrank]
      simp [evenMiddleRank, oddLowerRank]

@[simp]
theorem oddCompletionCoordinates_space (k : ℕ)
    (Q : OddPartialFlag (K := K) (V := V) (n := 2 * k + 1))
    (x : {P : EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1) // Compatible P Q})
    (j : Fin k) :
    (oddCompletionCoordinates k Q x j).space =
      completeOfOddCompatibility k Q x (evenMiddleRank k j) := rfl

theorem oddCompletionCoordinates_injective (k : ℕ)
    (Q : OddPartialFlag (K := K) (V := V) (n := 2 * k + 1)) :
    Function.Injective (oddCompletionCoordinates k Q) := by
  intro x y hxy
  let F := completeOfOddCompatibility k Q x
  let G := completeOfOddCompatibility k Q y
  have hOddF := completeOfOddCompatibility_odd k Q x
  have hOddG := completeOfOddCompatibility_odd k Q y
  have hFG : F = G := by
    apply CompleteFlag.ext
    intro i
    by_cases hi : i.val % 2 = 1
    · exact (ofComplete_space_eq_of_mod hOddF i hi).trans
        (ofComplete_space_eq_of_mod hOddG i hi).symm
    · have hiEven : i.val % 2 = 0 := by omega
      by_cases hzero : i.val = 0
      · have hiZero : i = 0 := by ext; simpa using hzero
        rw [hiZero, F.space_zero, G.space_zero]
      · let j : Fin k := ⟨i.val / 2 - 1, by omega⟩
        have hij : i = evenMiddleRank k j := by
          apply Fin.ext
          simp [j, evenMiddleRank]
          omega
        have hs := congrArg (fun c ↦ (c j).space) hxy
        simpa [F, G, hij] using hs
  apply Subtype.ext
  calc
    x.1 = PartialFlag.ofComplete 0 F :=
      (completeOfOddCompatibility_even k Q x).symm
    _ = PartialFlag.ofComplete 0 G := congrArg (PartialFlag.ofComplete 0) hFG
    _ = y.1 := completeOfOddCompatibility_even k Q y

theorem oddBoundary_le (k : ℕ)
    (Q : OddPartialFlag (K := K) (V := V) (n := 2 * k + 1)) (j : Fin k) :
    Q.1 (oddLowerRank k j) ≤ Q.1 (oddUpperRank k j) := by
  obtain ⟨F, hF⟩ := Q.property
  have hQF : PartialFlag.ofComplete 1 F = Q := Subtype.ext hF
  rw [← ofComplete_space_eq_of_mod hQF _ (by simp [oddLowerRank]),
    ← ofComplete_space_eq_of_mod hQF _ (by simp [oddUpperRank])]
  exact F.strictMono_space.monotone (by simp [oddLowerRank, oddUpperRank])

theorem oddBoundary_finrank (k : ℕ)
    (Q : OddPartialFlag (K := K) (V := V) (n := 2 * k + 1)) (j : Fin k) :
    finrank K (Q.1 (oddUpperRank k j)) =
      finrank K (Q.1 (oddLowerRank k j)) + 2 := by
  obtain ⟨F, hF⟩ := Q.property
  have hQF : PartialFlag.ofComplete 1 F = Q := Subtype.ext hF
  rw [← ofComplete_space_eq_of_mod hQF _ (by simp),
    ← ofComplete_space_eq_of_mod hQF _ (by simp),
    F.finrank_space, F.finrank_space]
  simp [oddLowerRank, oddUpperRank]

/-- Interleave arbitrary positive-even-rank choices in the rank-two
intervals of an odd partial flag; rank zero is the bottom space. -/
def oddCompletedSpace (k : ℕ)
    (Q : OddPartialFlag (K := K) (V := V) (n := 2 * k + 1))
    (c : OddCompletionCoordinates k Q) :
    Fin ((2 * k + 1) + 1) → Submodule K V := fun i ↦
  if hi : i.val % 2 = 1 then Q.1 i
  else if _hzero : i.val = 0 then ⊥
  else (c ⟨i.val / 2 - 1, by omega⟩).space

@[simp]
theorem oddCompletedSpace_of_odd (k : ℕ)
    (Q : OddPartialFlag (K := K) (V := V) (n := 2 * k + 1))
    (c : OddCompletionCoordinates k Q) (i : Fin ((2 * k + 1) + 1))
    (hi : i.val % 2 = 1) : oddCompletedSpace k Q c i = Q.1 i := by
  simp [oddCompletedSpace, hi]

@[simp]
theorem oddCompletedSpace_evenMiddle (k : ℕ)
    (Q : OddPartialFlag (K := K) (V := V) (n := 2 * k + 1))
    (c : OddCompletionCoordinates k Q) (j : Fin k) :
    oddCompletedSpace k Q c (evenMiddleRank k j) = (c j).space := by
  have hparity : (evenMiddleRank k j).val % 2 ≠ 1 := by
    simp [evenMiddleRank]
  have hzero : (evenMiddleRank k j).val ≠ 0 := by
    simp [evenMiddleRank]
  have hindex :
      (⟨(evenMiddleRank k j).val / 2 - 1, by omega⟩ : Fin k) = j := by
    apply Fin.ext
    change (2 * j.val + 2) / 2 - 1 = j.val
    rw [Nat.mul_add_div (by omega)]
    simp
  unfold oddCompletedSpace
  rw [dif_neg hparity, dif_neg hzero, hindex]

@[simp]
theorem oddCompletedSpace_zero (k : ℕ)
    (Q : OddPartialFlag (K := K) (V := V) (n := 2 * k + 1))
    (c : OddCompletionCoordinates k Q) : oddCompletedSpace k Q c 0 = ⊥ := by
  simp [oddCompletedSpace]

/-- Every coordinate tuple over an odd partial flag assembles into a
complete flag.  This is the dual formal independence assertion. -/
noncomputable def completeFlagOfOddCoordinates (k : ℕ)
    (Q : OddPartialFlag (K := K) (V := V) (n := 2 * k + 1))
    (c : OddCompletionCoordinates k Q) : CompleteFlag K V (2 * k + 1) :=
  completeFlagOfRankedSpaces (oddCompletedSpace k Q c) (by
    intro i
    by_cases hi : i.val % 2 = 1
    · rw [oddCompletedSpace_of_odd k Q c i hi]
      exact partialFlag_finrank_space_of_mod Q i hi
    · have hiEven : i.val % 2 = 0 := by omega
      by_cases hzero : i.val = 0
      · have hiZero : i = 0 := by
          apply Fin.ext
          simpa using hzero
        rw [hiZero, oddCompletedSpace_zero, finrank_bot]
        simp
      · let j : Fin k := ⟨i.val / 2 - 1, by omega⟩
        have hij : i = evenMiddleRank k j := by
          apply Fin.ext
          simp [j, evenMiddleRank]
          omega
        rw [hij, oddCompletedSpace_evenMiddle,
          (c j).finrank_space,
          partialFlag_finrank_space_of_mod Q (oddLowerRank k j) (by simp)]
        simp [oddLowerRank, evenMiddleRank]) (by
    intro i
    by_cases hi : i.val % 2 = 0
    · by_cases hzero : i.val = 0
      · have hsource : i.castSucc = 0 := by
          apply Fin.ext
          simpa using hzero
        rw [hsource, oddCompletedSpace_zero]
        exact bot_le
      · let j : Fin k := ⟨i.val / 2 - 1, by omega⟩
        have hsource : i.castSucc = evenMiddleRank k j := by
          apply Fin.ext
          simp [j, evenMiddleRank]
          omega
        have htarget : i.succ = oddUpperRank k j := by
          apply Fin.ext
          simp [j, oddUpperRank]
          omega
        rw [hsource, htarget, oddCompletedSpace_evenMiddle,
          oddCompletedSpace_of_odd]
        · exact (c j).upper
        · simp [oddUpperRank]
    · have hiOdd : i.val % 2 = 1 := by omega
      let j : Fin k := ⟨i.val / 2, by omega⟩
      have hsource : i.castSucc = oddLowerRank k j := by
        apply Fin.ext
        simp [j, oddLowerRank]
        omega
      have htarget : i.succ = evenMiddleRank k j := by
        apply Fin.ext
        simp [j, evenMiddleRank]
        omega
      rw [hsource, htarget, oddCompletedSpace_of_odd,
        oddCompletedSpace_evenMiddle]
      · exact (c j).lower
      · simp [oddLowerRank]) (oddCompletedSpace_zero k Q c) (by
    rw [oddCompletedSpace_of_odd]
    · obtain ⟨F, hF⟩ := Q.property
      have hQF : PartialFlag.ofComplete 1 F = Q := Subtype.ext hF
      rw [← ofComplete_space_eq_of_mod hQF (Fin.last (2 * k + 1)) (by simp),
        F.space_last]
    · simp)

@[simp]
theorem completeFlagOfOddCoordinates_apply (k : ℕ)
    (Q : OddPartialFlag (K := K) (V := V) (n := 2 * k + 1))
    (c : OddCompletionCoordinates k Q) (i : Fin ((2 * k + 1) + 1)) :
    completeFlagOfOddCoordinates k Q c i = oddCompletedSpace k Q c i := rfl

theorem completeFlagOfOddCoordinates_oddPart (k : ℕ)
    (Q : OddPartialFlag (K := K) (V := V) (n := 2 * k + 1))
    (c : OddCompletionCoordinates k Q) :
    PartialFlag.ofComplete 1 (completeFlagOfOddCoordinates k Q c) = Q := by
  apply PartialFlag.ext
  intro i
  by_cases hi : i.val % 2 = 1
  · simp [PartialFlag.ofComplete, flagPart, hi]
  · rw [partialFlag_space_eq_bot_of_mod_ne Q i (by simpa using hi)]
    simp [PartialFlag.ofComplete, flagPart, hi]

/-- The compatible even part assembled from an arbitrary coordinate tuple. -/
noncomputable def evenCompatibleOfOddCoordinates (k : ℕ)
    (Q : OddPartialFlag (K := K) (V := V) (n := 2 * k + 1))
    (c : OddCompletionCoordinates k Q) :
    {P : EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1) // Compatible P Q} :=
  ⟨PartialFlag.ofComplete 0 (completeFlagOfOddCoordinates k Q c),
    completeFlagOfOddCoordinates k Q c, rfl,
    completeFlagOfOddCoordinates_oddPart k Q c⟩

theorem oddCompletionCoordinates_rightInverse (k : ℕ)
    (Q : OddPartialFlag (K := K) (V := V) (n := 2 * k + 1)) :
    Function.RightInverse (evenCompatibleOfOddCoordinates k Q)
      (oddCompletionCoordinates k Q) := by
  intro c
  funext j
  apply IntermediateSubspace.ext
  let x := evenCompatibleOfOddCoordinates k Q c
  have hchosen : completeOfOddCompatibility k Q x =
      completeFlagOfOddCoordinates k Q c :=
    compatible_unique
      (completeOfOddCompatibility_even k Q x)
      (completeOfOddCompatibility_odd k Q x) rfl
      (completeFlagOfOddCoordinates_oddPart k Q c)
  simpa [x, hchosen] using
    (oddCompletionCoordinates_space k Q x j)

/-- Compatible even parts are exactly independent products of the `k`
rank-two intervals. -/
noncomputable def oddCompletionEquiv (k : ℕ)
    (Q : OddPartialFlag (K := K) (V := V) (n := 2 * k + 1)) :
    {P : EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1) // Compatible P Q} ≃
      OddCompletionCoordinates k Q where
  toFun := oddCompletionCoordinates k Q
  invFun := evenCompatibleOfOddCoordinates k Q
  left_inv x := (oddCompletionCoordinates_injective k Q)
    (oddCompletionCoordinates_rightInverse k Q (oddCompletionCoordinates k Q x))
  right_inv := oddCompletionCoordinates_rightInverse k Q

/-- An odd partial flag has exactly `(q+1)^k` compatible even parts. -/
theorem natCard_even_compatible_eq (k : ℕ)
    (Q : OddPartialFlag (K := K) (V := V) (n := 2 * k + 1)) :
    Nat.card {P : EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1) // Compatible P Q} =
      (Nat.card K + 1) ^ k := by
  calc
    Nat.card {P : EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1) // Compatible P Q} =
        Nat.card (OddCompletionCoordinates k Q) :=
      Nat.card_congr (oddCompletionEquiv k Q)
    _ = ∏ j : Fin k, Nat.card
          (IntermediateSubspace (Q.1 (oddLowerRank k j)) (Q.1 (oddUpperRank k j))) :=
      Nat.card_pi
    _ = ∏ _j : Fin k, (Nat.card K + 1) := by
      apply Finset.prod_congr rfl
      intro j _hj
      exact natCard_intermediate_eq
        (oddBoundary_le k Q j) (oddBoundary_finrank k Q j)
    _ = (Nat.card K + 1) ^ k := by simp

/-- The dual upper bound as a direct corollary of the exact completion count. -/
theorem natCard_even_compatible_le (k : ℕ)
    (Q : OddPartialFlag (K := K) (V := V) (n := 2 * k + 1)) :
    Nat.card {P : EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1) // Compatible P Q} ≤
      (Nat.card K + 1) ^ k := by
  exact (natCard_even_compatible_eq k Q).le

/-- A neighbor is encoded by a compatible odd part and then by an even part
compatible with that odd part.  We deliberately keep all such pairs, rather
than assuming that a neighbor has a unique common odd part. -/
abbrev NeighborEncoding (k : ℕ)
    (P : EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1)) :=
  Σ q : {Q : OddPartialFlag (K := K) (V := V) (n := 2 * k + 1) // Compatible P Q},
    {P' : EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1) //
      P' ∈ ({R | Compatible R q.1} \ {P} : Set _)}

noncomputable def encodeNeighbor (k : ℕ)
    (P : EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1)) :
    (halvedFlagGraph (K := K) (V := V) (n := 2 * k + 1)).neighborSet P →
      NeighborEncoding k P :=
  fun P' ↦ by
    have ha := (halvedFlagGraph_adj_iff (K := K) (V := V)).mp P'.property
    let Q := Classical.choose ha.2
    have hQ := Classical.choose_spec ha.2
    exact ⟨⟨Q, hQ.1⟩, ⟨P'.1, hQ.2, by simpa using ha.1.symm⟩⟩

theorem encodeNeighbor_injective (k : ℕ)
    (P : EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1)) :
    Function.Injective (encodeNeighbor k P) := by
  intro P' P'' h
  apply Subtype.ext
  have hs := congrArg (fun z : NeighborEncoding k P ↦ z.2.1) h
  simpa [encodeNeighbor] using hs

/-- The paper's neighbor-set cap `A(A-1)`, where `A = (q+1)^k`.  It does not
count a neighbor twice or posit uniqueness of its common odd flag: the
injection chooses one witness, and its second coordinate excludes the original
vertex from the at-most-`A` compatible even parts. -/
theorem halvedFlagGraph_natCard_neighborSet_le_sharp (k : ℕ)
    (P : EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1)) :
    Nat.card ((halvedFlagGraph (K := K) (V := V) (n := 2 * k + 1)).neighborSet P) ≤
      ((Nat.card K + 1) ^ k) * (((Nat.card K + 1) ^ k) - 1) := by
  let A := (Nat.card K + 1) ^ k
  let Base := {Q : OddPartialFlag (K := K) (V := V) (n := 2 * k + 1) // Compatible P Q}
  letI : Fintype Base := Fintype.ofFinite _
  calc
    Nat.card ((halvedFlagGraph (K := K) (V := V) (n := 2 * k + 1)).neighborSet P) ≤
        Nat.card (NeighborEncoding k P) :=
      Nat.card_le_card_of_injective (encodeNeighbor k P) (encodeNeighbor_injective k P)
    _ = ∑ q : Base, Nat.card
          {P' : EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1) //
            P' ∈ ({R | Compatible R q.1} \ {P} : Set _)} :=
      Nat.card_sigma
    _ ≤ ∑ _q : Base, (A - 1) := by
      exact Finset.sum_le_sum fun q _ ↦ by
        rw [Nat.card_coe_set_eq,
          Set.ncard_sdiff_singleton_of_mem
            (show P ∈ {R | Compatible R q.1} from q.2)]
        exact Nat.sub_le_sub_right (natCard_even_compatible_le k q.1) 1
    _ = Nat.card Base * (A - 1) := by
      simp [Nat.card_eq_fintype_card]
    _ ≤ A * (A - 1) := Nat.mul_le_mul_right (A - 1) (natCard_odd_compatible_le k P)
    _ = ((Nat.card K + 1) ^ k) * (((Nat.card K + 1) ^ k) - 1) := rfl

end PartialFlagCompletions

end DegreeDiameter

end PortCompletionCount

/- DegreeDiameter.FlagSpace -/
section PortFlagSpace

/-
# The recursively split flag space

This file contains only the neutral ambient vector-space model used by both
the exact flag-graph construction and the big-cell lower-bound argument.
Keeping it separate prevents the exact Proposition 3.1 chain from depending
on the lower-bound construction merely to obtain this coordinate model.
-/

open Module

namespace DegreeDiameter

universe u

/-- The recursively split `(2*k+1)`-dimensional coordinate space. -/
abbrev FlagSpace (K : Type u) : ℕ → Type u
  | 0 => Fin 1 → K
  | k + 1 => (Fin 2 → K) × FlagSpace K k

/-- The dimension of `FlagSpace`, kept recursive so adjoining its first two
coordinates remains definitionally transparent. -/
def flagDim : ℕ → ℕ
  | 0 => 1
  | k + 1 => flagDim k + 2

theorem flagDim_eq (k : ℕ) : flagDim k = 2 * k + 1 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [flagDim, ih]; omega

section LinearAlgebra

variable (K : Type u) [Field K]

instance flagSpaceAddCommGroup : ∀ k : ℕ, AddCommGroup (FlagSpace K k)
  | 0 => inferInstanceAs (AddCommGroup (Fin 1 → K))
  | k + 1 =>
      letI := flagSpaceAddCommGroup k
      inferInstanceAs (AddCommGroup ((Fin 2 → K) × FlagSpace K k))

instance flagSpaceModule : ∀ k : ℕ, Module K (FlagSpace K k)
  | 0 => inferInstanceAs (Module K (Fin 1 → K))
  | k + 1 =>
      letI := flagSpaceModule k
      inferInstanceAs (Module K ((Fin 2 → K) × FlagSpace K k))

noncomputable instance flagSpaceFiniteDimensional : ∀ k : ℕ,
    FiniteDimensional K (FlagSpace K k)
  | 0 => inferInstanceAs (FiniteDimensional K (Fin 1 → K))
  | k + 1 =>
      letI := flagSpaceFiniteDimensional k
      inferInstanceAs (FiniteDimensional K ((Fin 2 → K) × FlagSpace K k))

theorem finrank_flagSpace (k : ℕ) : finrank K (FlagSpace K k) = flagDim k := by
  induction k with
  | zero => simp [FlagSpace, flagDim]
  | succ k ih =>
      simp only [FlagSpace, flagDim, Module.finrank_prod]
      have htwo : finrank K (Fin 2 → K) = 2 := by simp
      rw [htwo, ih]
      omega

end LinearAlgebra

section Cardinality

variable (K : Type u)

instance flagSpaceFinite [Finite K] : ∀ k : ℕ, Finite (FlagSpace K k)
  | 0 => inferInstanceAs (Finite (Fin 1 → K))
  | k + 1 =>
      letI := flagSpaceFinite k
      inferInstanceAs (Finite ((Fin 2 → K) × FlagSpace K k))

end Cardinality

end DegreeDiameter

end PortFlagSpace

/- DegreeDiameter.FlagEnumeration -/
section PortFlagEnumeration

/-
# Exact enumeration of complete flags

For a natural number `q`, `qInteger q n` is the polynomial
`1 + q + ... + q^(n-1)`.  The product `qFactorial q n` is

`[n]_q [n-1]_q ... [1]_q`.

The order of the factors is reversed only to make the factorization used in
the proof definitionally transparent; multiplication in `ℕ` is commutative.

We prove the complete-flag formula by counting adapted ordered bases.  For a
complete flag `F`, an adapted vector at step `i` is a vector in
`F_(i+1) \ F_i`.  Choosing one at every step always gives a basis, and every
ordered basis is obtained exactly once after retaining its induced flag.
Mathlib's exact enumeration of linearly independent tuples then gives the
q-factorial formula.
-/

open Module
open scoped BigOperators

namespace DegreeDiameter

/-- The `q`-integer `[n]_q = 1 + q + ... + q^(n-1)`. -/
def qInteger (q n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range n, q ^ i

/-- The `q`-factorial `[n]_q! = [n]_q [n-1]_q ... [1]_q`.

Writing the factors in descending order agrees with the usual q-factorial
because multiplication in `ℕ` is commutative. -/
def qFactorial (q n : ℕ) : ℕ :=
  ∏ i : Fin n, qInteger q (n - i.val)

@[simp]
theorem qInteger_zero (q : ℕ) : qInteger q 0 = 0 := by
  simp [qInteger]

@[simp]
theorem qInteger_one (q : ℕ) : qInteger q 1 = 1 := by
  simp [qInteger]

@[simp]
theorem qFactorial_zero (q : ℕ) : qFactorial q 0 = 1 := by
  simp [qFactorial]

theorem qFactorial_succ (q n : ℕ) :
    qFactorial q (n + 1) = qInteger q (n + 1) * qFactorial q n := by
  rw [qFactorial, Fin.prod_univ_succ, qFactorial]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  congr 1
  simp

/-- The descending-product definition is the conventional ascending product
`[1]_q [2]_q ... [n]_q`. -/
theorem qFactorial_eq_prod_range (q n : ℕ) :
    qFactorial q n = ∏ j ∈ Finset.range n, qInteger q (j + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [qFactorial_succ, Finset.prod_range_succ, ih, Nat.mul_comm]

theorem qInteger_mul_sub_one (q n : ℕ) (hq : 1 ≤ q) :
    qInteger q n * (q - 1) = q ^ n - 1 := by
  simpa [qInteger] using (geom_sum_mul_of_one_le hq n)

section CompleteFlagFinite

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
  {n : ℕ}

/-- Complete flags form a finite type when the ambient vector space is
finite. -/
noncomputable instance CompleteFlag.instFinite [Finite V] :
    Finite (CompleteFlag K V n) := by
  letI : Finite (Submodule K V) :=
    Finite.of_injective (fun S : Submodule K V ↦ (S : Set V)) SetLike.coe_injective
  exact Finite.of_injective
    (fun F : CompleteFlag K V n ↦ F.space)
    (fun _ _ h ↦ CompleteFlag.ext (congrFun h))

end CompleteFlagFinite

section AdaptedBases

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  {n : ℕ}

/-- A vector which advances the complete flag `F` from rank `i` to rank
`i+1`. -/
def FlagStepVector (F : CompleteFlag K V n) (i : Fin n) :=
  {x : F i.succ // (x : V) ∉ F i.castSucc}

noncomputable instance flagStepVectorFinite [Finite V]
    (F : CompleteFlag K V n) (i : Fin n) : Finite (FlagStepVector F i) := by
  unfold FlagStepVector
  infer_instance

/-- One advancing vector at every rank of a complete flag. -/
def FlagStepChoices (F : CompleteFlag K V n) :=
  (i : Fin n) → FlagStepVector F i

noncomputable instance flagStepChoicesFinite [Finite V]
    (F : CompleteFlag K V n) : Finite (FlagStepChoices F) := by
  unfold FlagStepChoices
  infer_instance

/-- A complete flag together with a choice of one advancing vector at every
rank. -/
def AdaptedFlagBasis (K V : Type*) [Field K] [AddCommGroup V] [Module K V]
    (n : ℕ) :=
  Σ F : CompleteFlag K V n, FlagStepChoices F

/-- Forget the submodule-membership proofs in an adapted flag basis. -/
def adaptedVectors (d : AdaptedFlagBasis K V n) : Fin n → V :=
  fun i ↦ ((d.2 i).1 : V)

/-- Vectors in the preceding subspace, regarded as vectors in the next
subspace. -/
def previousStepEquiv (F : CompleteFlag K V n) (i : Fin n) :
    {x : F i.succ // (x : V) ∈ F i.castSucc} ≃ F i.castSucc where
  toFun x := ⟨x.1, x.2⟩
  invFun x :=
    ⟨⟨x.1, F.strictMono_space.monotone Fin.castSucc_lt_succ.le x.2⟩, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem natCard_flagStepVector [Finite K] [Finite V]
    (F : CompleteFlag K V n) (i : Fin n) :
    Nat.card (FlagStepVector F i) =
      Nat.card K ^ (i.val + 1) - Nat.card K ^ i.val := by
  classical
  letI := Fintype.ofFinite K
  letI := Fintype.ofFinite (F i.succ)
  letI := Fintype.ofFinite (F i.castSucc)
  letI := Fintype.ofFinite
    {x : F i.succ // (x : V) ∈ F i.castSucc}
  letI := Fintype.ofFinite (FlagStepVector F i)
  change Nat.card {x : F i.succ // ¬((x : V) ∈ F i.castSucc)} = _
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
  rw [Nat.card_congr (previousStepEquiv F i)]
  rw [Module.natCard_eq_pow_finrank (K := K) (V := F i.succ)]
  rw [Module.natCard_eq_pow_finrank (K := K) (V := F i.castSucc)]
  rw [F.finrank_space, F.finrank_space]
  rfl

theorem adaptedVectors_linearIndependent (d : AdaptedFlagBasis K V n) :
    LinearIndependent K (adaptedVectors d) := by
  let v := adaptedVectors d
  let F := d.1
  have hv_mem (i : Fin n) : v i ∈ F i.succ := (d.2 i).1.2
  have hv_not (i : Fin n) : v i ∉ F i.castSucc := (d.2 i).2
  let vr : (r : ℕ) → r ≤ n → Fin r → V := fun r hr i ↦
    v ⟨i.val, i.isLt.trans_le hr⟩
  have hLIprefix : ∀ (r : ℕ) (hr : r ≤ n), LinearIndependent K (vr r hr) := by
    intro r
    induction r with
    | zero =>
        intro _
        exact linearIndependent_empty_type
    | succ r ih =>
        intro hr
        rw [linearIndependent_finSucc']
        constructor
        · have heq : Fin.init (vr (r + 1) hr) = vr r (Nat.le_of_succ_le hr) := by
            funext i
            rfl
          rw [heq]
          exact ih (Nat.le_of_succ_le hr)
        · intro hmem
          have hspan_le :
              Submodule.span K (Set.range (Fin.init (vr (r + 1) hr))) ≤
                F ⟨r, by omega⟩ := by
            rw [Submodule.span_le]
            intro x hx
            obtain ⟨i, rfl⟩ := hx
            have hvi := hv_mem ⟨i.val, by omega⟩
            exact F.strictMono_space.monotone
              (Fin.castSucc_lt_iff_succ_le.mp (show i.val < r from i.isLt)) hvi
          exact hv_not ⟨r, by omega⟩ (hspan_le hmem)
  simpa [v, vr] using hLIprefix n le_rfl

/-- The span of the first `r` adapted vectors is exactly the rank-`r`
subspace of the flag. -/
theorem span_adaptedVectors_eq (d : AdaptedFlagBasis K V n)
    [FiniteDimensional K V]
    (r : Fin (n + 1)) :
    Submodule.span K
        (adaptedVectors d '' {i : Fin n | i.castSucc < r}) = d.1 r := by
  classical
  have hLI : LinearIndependent K (adaptedVectors d) :=
    adaptedVectors_linearIndependent d
  apply Submodule.eq_of_le_of_finrank_eq
  · rw [Submodule.span_le]
    intro x hx
    obtain ⟨i, hi, rfl⟩ := hx
    exact d.1.strictMono_space.monotone
      (Fin.castSucc_lt_iff_succ_le.mp hi) (d.2 i).1.2
  · calc
      finrank K (Submodule.span K
          (adaptedVectors d '' {i : Fin n | i.castSucc < r})) = r.val := by
            rw [finrank_span_set_eq_card
              ((hLI.linearIndepOn _).id_image)]
            rw [Set.toFinset_image,
              Finset.card_image_of_injective _ hLI.injective]
            rw [Set.toFinset_setOf]
            change
              (Finset.filter (fun x : Fin n ↦ x.val < r.val) Finset.univ).card =
                r.val
            rw [Fin.card_filter_val_lt,
              Nat.min_eq_right (Nat.le_of_lt_succ r.isLt)]
      _ = finrank K (d.1 r) := (d.1.finrank_space r).symm

/-- An adapted flag basis is exactly a linearly independent `n`-tuple. -/
noncomputable def adaptedFlagBasisEquivLinearIndependent
    [FiniteDimensional K V] (hV : finrank K V = n) :
    AdaptedFlagBasis K V n ≃
      {v : Fin n → V // LinearIndependent K v} := by
  let f : AdaptedFlagBasis K V n →
      {v : Fin n → V // LinearIndependent K v} := fun d ↦
    ⟨adaptedVectors d, adaptedVectors_linearIndependent d⟩
  apply Equiv.ofBijective f
  constructor
  · intro d e h
    have hv : adaptedVectors d = adaptedVectors e :=
      congrArg Subtype.val h
    have hflag : d.1 = e.1 := by
      apply CompleteFlag.ext
      intro r
      rw [← span_adaptedVectors_eq d r, ← span_adaptedVectors_eq e r, hv]
    cases d with
    | mk F a =>
      cases e with
      | mk G b =>
        dsimp only at hflag ⊢
        subst G
        have hab : a = b := by
          funext i
          apply Subtype.ext
          apply Subtype.ext
          exact congrFun hv i
        subst b
        rfl
  · intro s
    let b : Basis (Fin n) K V :=
      basisOfLinearIndependentOfCardEqFinrank' s.1 s.2 (by
        simp [hV])
    have hb : (b : Fin n → V) = s.1 :=
      coe_basisOfLinearIndependentOfCardEqFinrank' s.1 s.2 (by
        simp [hV])
    let F : CompleteFlag K V n := CompleteFlag.ofBasis b
    let a : FlagStepChoices F := fun i ↦
      ⟨⟨b i, b.self_mem_flag (by simp)⟩, by
        intro hmem
        exact (lt_irrefl i.castSucc) ((b.self_mem_flag_iff).mp hmem)⟩
    refine ⟨⟨F, a⟩, ?_⟩
    apply Subtype.ext
    funext i
    change b i = s.1 i
    exact congrFun hb i

end AdaptedBases

section Arithmetic

/-- The factor in the exact count of independent tuples splits into the
number of choices advancing a fixed flag and the corresponding q-integer. -/
theorem independentFactor_eq (q n : ℕ) (hq : 1 ≤ q) (i : Fin n) :
    q ^ n - q ^ i.val =
      (q ^ (i.val + 1) - q ^ i.val) * qInteger q (n - i.val) := by
  have hi : i.val ≤ n := Nat.le_of_lt i.isLt
  have hn : i.val + (n - i.val) = n := Nat.add_sub_of_le hi
  have hgeom := qInteger_mul_sub_one q (n - i.val) hq
  have hadvance :
      q ^ (i.val + 1) - q ^ i.val = q ^ i.val * (q - 1) := by
    rw [pow_succ]
    simpa using (Nat.mul_sub_left_distrib (q ^ i.val) q 1).symm
  calc
    q ^ n - q ^ i.val =
        q ^ i.val * q ^ (n - i.val) - q ^ i.val * 1 := by
          rw [← pow_add, hn, mul_one]
    _ = q ^ i.val * (q ^ (n - i.val) - 1) := by
          rw [Nat.mul_sub_left_distrib]
    _ = q ^ i.val * (qInteger q (n - i.val) * (q - 1)) := by
          rw [hgeom]
    _ = (q ^ i.val * (q - 1)) * qInteger q (n - i.val) := by
          ac_rfl
    _ = (q ^ (i.val + 1) - q ^ i.val) * qInteger q (n - i.val) := by
          rw [hadvance]

theorem independentProduct_eq (q n : ℕ) (hq : 1 ≤ q) :
    (∏ i : Fin n, (q ^ n - q ^ i.val)) =
      (∏ i : Fin n, (q ^ (i.val + 1) - q ^ i.val)) * qFactorial q n := by
  rw [qFactorial]
  calc
    (∏ i : Fin n, (q ^ n - q ^ i.val)) =
        ∏ i : Fin n,
          ((q ^ (i.val + 1) - q ^ i.val) * qInteger q (n - i.val)) := by
            apply Finset.prod_congr rfl
            intro i _
            exact independentFactor_eq q n hq i
    _ = (∏ i : Fin n, (q ^ (i.val + 1) - q ^ i.val)) *
          ∏ i : Fin n, qInteger q (n - i.val) := by
            exact Finset.prod_mul_distrib

end Arithmetic

section CompleteFlagCount

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [Finite V] [FiniteDimensional K V]

/-- The exact number of complete flags in an `n`-dimensional vector space
over a finite field is `[n]_q!`, where `q` is the cardinality of the field. -/
theorem natCard_completeFlag_of_finrank {n : ℕ}
    (hV : finrank K V = n) :
    Nat.card (CompleteFlag K V n) = qFactorial (Nat.card K) n := by
  classical
  letI := Fintype.ofFinite K
  letI := Fintype.ofFinite V
  letI := Fintype.ofFinite (CompleteFlag K V n)
  let q := Nat.card K
  let A := ∏ i : Fin n, (q ^ (i.val + 1) - q ^ i.val)
  have hq : 1 < q := by
    simpa [q, Nat.card_eq_fintype_card] using (Fintype.one_lt_card : 1 < Fintype.card K)
  have hA : 0 < A := by
    apply Finset.prod_pos
    intro i _
    rw [Nat.sub_pos_iff_lt]
    exact pow_lt_pow_right₀ hq (Nat.lt_succ_self i.val)
  have hdata :
      Nat.card (AdaptedFlagBasis K V n) =
        Nat.card (CompleteFlag K V n) * A := by
    change Nat.card (Σ F : CompleteFlag K V n, FlagStepChoices F) = _
    rw [Nat.card_sigma]
    simp_rw [FlagStepChoices, Nat.card_pi, natCard_flagStepVector]
    simp [A, q, Nat.card_eq_fintype_card]
  have hindependent :
      Nat.card {v : Fin n → V // LinearIndependent K v} =
        ∏ i : Fin n, (q ^ n - q ^ i.val) := by
    have h := card_linearIndependent (K := K) (V := V) (k := n) (by rw [hV])
    simpa [q, hV, Nat.card_eq_fintype_card] using h
  have hcount :
      Nat.card (CompleteFlag K V n) * A =
        ∏ i : Fin n, (q ^ n - q ^ i.val) := by
    rw [← hdata]
    rw [Nat.card_congr
      (adaptedFlagBasisEquivLinearIndependent (K := K) (V := V) (n := n) hV)]
    exact hindependent
  have hfactor :
      (∏ i : Fin n, (q ^ n - q ^ i.val)) = A * qFactorial q n :=
    independentProduct_eq q n hq.le
  apply Nat.eq_of_mul_eq_mul_right hA
  calc
    Nat.card (CompleteFlag K V n) * A =
        ∏ i : Fin n, (q ^ n - q ^ i.val) := hcount
    _ = A * qFactorial q n := hfactor
    _ = qFactorial q n * A := Nat.mul_comm _ _

end CompleteFlagCount

end DegreeDiameter

end PortFlagEnumeration

/- DegreeDiameter.ExactOrder -/
section PortExactOrder

/-
# Exact order of the halved flag graph

This file carries out the double count in Proposition 3.1.  A complete flag
is the same thing as an even partial flag together with a compatible odd
partial flag.  The equivalence is explicit, and the fibre over every even
partial flag has the exact cardinality `(q + 1)^k` proved in
`CompletionCount`.  Combining that equality with the exact q-factorial
enumeration of complete flags gives both the multiplication form and the
division form of the paper's vertex-count formula.
-/

open Module

namespace DegreeDiameter

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [Finite V] [FiniteDimensional K V]

/-- The dependent type of compatible even/odd partial-flag pairs. -/
abbrev CompatiblePartialFlagPair (k : ℕ) :=
  Σ P : EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1),
    {Q : OddPartialFlag (K := K) (V := V) (n := 2 * k + 1) // Compatible P Q}

/-- Splitting a complete flag into its parity parts is an equivalence onto
the type of compatible pairs.  This is the precise bijection used in the
double count. -/
noncomputable def completeFlagEquivCompatiblePartialFlagPair (k : ℕ) :
    CompleteFlag K V (2 * k + 1) ≃ CompatiblePartialFlagPair (K := K) (V := V) k where
  toFun F :=
    ⟨PartialFlag.ofComplete 0 F,
      ⟨PartialFlag.ofComplete 1 F, compatible_parts F⟩⟩
  invFun x := Classical.choose x.2.property
  left_inv F := by
    apply compatible_unique
      (P := PartialFlag.ofComplete 0 F)
      (Q := PartialFlag.ofComplete 1 F)
    · exact (Classical.choose_spec
        (show Compatible (PartialFlag.ofComplete 0 F)
          (PartialFlag.ofComplete 1 F) from compatible_parts F)).1
    · exact (Classical.choose_spec
        (show Compatible (PartialFlag.ofComplete 0 F)
          (PartialFlag.ofComplete 1 F) from compatible_parts F)).2
    · rfl
    · rfl
  right_inv x := by
    obtain ⟨P, Q, hPQ⟩ := x
    have hchosen := Classical.choose_spec hPQ
    change
      (⟨PartialFlag.ofComplete 0 (Classical.choose hPQ),
        ⟨PartialFlag.ofComplete 1 (Classical.choose hPQ),
          compatible_parts (Classical.choose hPQ)⟩⟩ :
        CompatiblePartialFlagPair (K := K) (V := V) k) =
      ⟨P, ⟨Q, hPQ⟩⟩
    have hpred : ∀ R : OddPartialFlag (K := K) (V := V) (n := 2 * k + 1),
        Compatible (PartialFlag.ofComplete 0 (Classical.choose hPQ)) R ↔
          Compatible P R := by
      intro R
      rw [hchosen.1]
    apply Sigma.ext hchosen.1
    apply (Subtype.heq_iff_coe_eq hpred).2
    exact hchosen.2

/-- Exact double-counting identity before inserting the q-factorial formula:
the number of complete flags is the number of even partial flags times the
constant compatible-completion multiplicity. -/
theorem natCard_completeFlag_eq_evenPartialFlag_mul_completion (k : ℕ) :
    Nat.card (CompleteFlag K V (2 * k + 1)) =
      Nat.card (EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1)) *
        (Nat.card K + 1) ^ k := by
  classical
  let X := EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1)
  letI : Fintype X := Fintype.ofFinite X
  calc
    Nat.card (CompleteFlag K V (2 * k + 1)) =
        Nat.card (CompatiblePartialFlagPair (K := K) (V := V) k) :=
      Nat.card_congr (completeFlagEquivCompatiblePartialFlagPair
        (K := K) (V := V) k)
    _ = ∑ P : X,
          Nat.card {Q : OddPartialFlag (K := K) (V := V) (n := 2 * k + 1) //
            Compatible P Q} := Nat.card_sigma
    _ = ∑ _P : X, (Nat.card K + 1) ^ k := by
      apply Finset.sum_congr rfl
      intro P _hP
      exact natCard_odd_compatible_eq k P
    _ = Nat.card X * (Nat.card K + 1) ^ k := by
      simp [Nat.card_eq_fintype_card]

/-- Equation (6) of the write-up in multiplication form.  This form records
the exact double count without relying on truncated natural-number division. -/
theorem natCard_evenPartialFlag_mul_completion_eq_qFactorial (k : ℕ)
    (hV : finrank K V = 2 * k + 1) :
    Nat.card (EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1)) *
        (Nat.card K + 1) ^ k =
      qFactorial (Nat.card K) (2 * k + 1) := by
  rw [← natCard_completeFlag_eq_evenPartialFlag_mul_completion (K := K) (V := V) k]
  exact natCard_completeFlag_of_finrank hV

/-- Equation (6) of the write-up in its displayed division form. -/
theorem natCard_evenPartialFlag_eq_qFactorial_div (k : ℕ)
    (hV : finrank K V = 2 * k + 1) :
    Nat.card (EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1)) =
      qFactorial (Nat.card K) (2 * k + 1) / (Nat.card K + 1) ^ k := by
  have hmul := natCard_evenPartialFlag_mul_completion_eq_qFactorial
    (K := K) (V := V) k hV
  have hcompletion : 0 < (Nat.card K + 1) ^ k :=
    pow_pos (Nat.succ_pos (Nat.card K)) k
  calc
    Nat.card (EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1)) =
        (Nat.card (EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1)) *
          (Nat.card K + 1) ^ k) / (Nat.card K + 1) ^ k := by
      rw [Nat.mul_div_left _ hcompletion]
    _ = qFactorial (Nat.card K) (2 * k + 1) / (Nat.card K + 1) ^ k := by
      rw [hmul]

/-- The same exact formula for the recursively split coordinate model used
by the big-cell construction. -/
theorem natCard_flagSpaceEvenPartialFlag_eq_qFactorial_div (k : ℕ) :
    Nat.card (EvenPartialFlag
      (K := K) (V := FlagSpace K k) (n := 2 * k + 1)) =
      qFactorial (Nat.card K) (2 * k + 1) / (Nat.card K + 1) ^ k := by
  apply natCard_evenPartialFlag_eq_qFactorial_div
  simpa [flagDim_eq] using finrank_flagSpace (K := K) k

end DegreeDiameter

end PortExactOrder

/- DegreeDiameter.FiniteFieldModels -/
section PortFiniteFieldModels

/-
# Finite fields of prime-power order

This file separates the finite-geometric construction from its numerical
prime-power indexing.  A `FiniteFieldModel` stores the carrier and the exact
field and finiteness structures that are used to compute its cardinality.

For every natural-number prime power `q`, `finiteFieldModelOfPrimePower`
chooses a Galois field of cardinality exactly `q`.  The subtype
`PrimePowerIndex` is ordered by its underlying natural number, so `atTop` on
this type is literally the filter “as `q` tends to infinity through prime
powers”.  The cofinality theorem below makes that interpretation explicit.
-/

open Filter

namespace DegreeDiameter

/-- A finite field together with the particular structures used on its
carrier.  Keeping the structures explicit makes existential prime-power
instantiation straightforward and avoids any hidden choice of instances. -/
structure FiniteFieldModel where
  carrier : Type
  field : Field carrier
  finite : Finite carrier

namespace FiniteFieldModel

/-- The cardinality of an explicitly packaged finite field. -/
noncomputable def card (M : FiniteFieldModel) : ℕ :=
  Nat.card M.carrier

end FiniteFieldModel

/-- Every natural-number prime power is the cardinality of an explicitly
packaged finite field.  The field is the Mathlib Galois field `GF(p^e)`. -/
theorem exists_finiteFieldModel_of_isPrimePow (q : ℕ) (hq : IsPrimePow q) :
    ∃ M : FiniteFieldModel, M.card = q := by
  rcases (isPrimePow_nat_iff q).mp hq with ⟨p, e, hp, he, rfl⟩
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  let M : FiniteFieldModel :=
    { carrier := GaloisField p e
      field := inferInstance
      finite := inferInstance }
  refine ⟨M, ?_⟩
  simpa only [FiniteFieldModel.card, M] using
    (GaloisField.card p e he.ne')

/-- Natural numbers that are positive powers of a prime.  Its inherited
order is the order of the underlying cardinalities. -/
abbrev PrimePowerIndex := {q : ℕ // IsPrimePow q}

/-- Prime powers are cofinal in the natural numbers.  Consequently `atTop`
on `PrimePowerIndex` is precisely “tending to infinity through prime
powers”. -/
theorem tendsto_primePowerIndex_val :
    Tendsto (fun q : PrimePowerIndex ↦ q.1) atTop atTop := by
  apply Monotone.tendsto_atTop_atTop
  · intro a b hab
    exact hab
  · intro n
    obtain ⟨p, hnp, hp⟩ := Nat.exists_infinite_primes n
    exact ⟨⟨p, hp.isPrimePow⟩, hnp⟩

/-- A chosen finite field model of order `q`, for each prime power `q`. -/
noncomputable def finiteFieldModelOfPrimePower (q : PrimePowerIndex) :
    FiniteFieldModel :=
  Classical.choose (exists_finiteFieldModel_of_isPrimePow q.1 q.2)

@[simp]
theorem finiteFieldModelOfPrimePower_card (q : PrimePowerIndex) :
    (finiteFieldModelOfPrimePower q).card = q.1 :=
  Classical.choose_spec (exists_finiteFieldModel_of_isPrimePow q.1 q.2)

/-- A chosen field of each prime-power cardinality.  The construction is
noncomputable only because a prime/exponent presentation of `q` is chosen. -/
noncomputable abbrev PrimePowerField (q : PrimePowerIndex) : Type :=
  (finiteFieldModelOfPrimePower q).carrier

noncomputable instance primePowerFieldField (q : PrimePowerIndex) :
    Field (PrimePowerField q) :=
  (finiteFieldModelOfPrimePower q).field

noncomputable instance primePowerFieldFinite (q : PrimePowerIndex) :
    Finite (PrimePowerField q) :=
  (finiteFieldModelOfPrimePower q).finite

/-- The chosen field really has the prime-power cardinality indexing it. -/
@[simp]
theorem natCard_primePowerField (q : PrimePowerIndex) :
    Nat.card (PrimePowerField q) = q.1 := by
  simpa only [FiniteFieldModel.card] using
    finiteFieldModelOfPrimePower_card q

end DegreeDiameter

end PortFiniteFieldModels

/- DegreeDiameter.Symmetry -/
section PortSymmetry

/-
# Symmetry and regularity of the halved flag graph

Linear automorphisms act on complete and partial flags.  The common-apartment
part of Lemma 2.1 supplies an automorphism taking any chosen completion of one
vertex to a chosen completion of another.  Consequently the action on even
partial flags is transitive and the halved graph is regular.
-/

open Module

namespace DegreeDiameter

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
  {n : ℕ}

@[simp]
theorem submodule_map_symm_map (e : V ≃ₗ[K] V) (S : Submodule K V) :
    (S.map e.toLinearMap).map e.symm.toLinearMap = S := by
  rw [Submodule.map_equiv_eq_comap_symm]
  exact Submodule.comap_map_eq_of_injective e.injective S

namespace CompleteFlag

/-- Transport every member of a complete flag along a linear equivalence. -/
noncomputable def map (e : V ≃ₗ[K] V) (F : CompleteFlag K V n) : CompleteFlag K V n where
  space i := (Submodule.orderIsoMapComap e) (F i)
  strictMono_space := (Submodule.orderIsoMapComap e).strictMono.comp F.strictMono_space
  finrank_space i := by
    change finrank K ((F i).map e.toLinearMap) = i
    exact (e.finrank_map_eq (F i)).trans (F.finrank_space i)
  space_zero := by simp [F.space_zero]
  space_last := by simp [F.space_last]

@[simp]
theorem map_apply (e : V ≃ₗ[K] V) (F : CompleteFlag K V n) (i : Fin (n + 1)) :
    F.map e i = (Submodule.orderIsoMapComap e) (F i) := rfl

@[simp]
theorem map_symm_map (e : V ≃ₗ[K] V) (F : CompleteFlag K V n) :
    (F.map e).map e.symm = F := by
  apply CompleteFlag.ext
  intro i
  exact submodule_map_symm_map e (F i)

@[simp]
theorem map_map_symm (e : V ≃ₗ[K] V) (F : CompleteFlag K V n) :
    (F.map e.symm).map e = F := by
  simpa using map_symm_map e.symm F

/-- Transporting a basis flag transports its basis. -/
theorem map_ofBasis (e : V ≃ₗ[K] V) (b : Basis (Fin n) K V) :
    (CompleteFlag.ofBasis b).map e = CompleteFlag.ofBasis (b.map e) := by
  apply CompleteFlag.ext
  intro i
  change (b.flag i).map e.toLinearMap = (b.map e).flag i
  simp only [Module.Basis.flag, Submodule.map_span, Set.image_image]
  rfl

end CompleteFlag

namespace PartialFlag

/-- Transport a partial flag along a linear equivalence. -/
noncomputable def map {parity : ℕ} (e : V ≃ₗ[K] V)
    (P : PartialFlag (K := K) (V := V) (n := n) parity) :
    PartialFlag (K := K) (V := V) (n := n) parity := by
  refine ⟨fun i ↦ (Submodule.orderIsoMapComap e) (P.1 i), ?_⟩
  obtain ⟨F, hF⟩ := P.property
  refine ⟨F.map e, ?_⟩
  funext i
  rw [← congrFun hF i]
  by_cases hi : i.val % 2 = parity % 2
  · simp [flagPart, hi]
  · simp [flagPart, hi]

@[simp]
theorem map_val {parity : ℕ} (e : V ≃ₗ[K] V)
    (P : PartialFlag (K := K) (V := V) (n := n) parity) (i : Fin (n + 1)) :
    (P.map e).1 i = (Submodule.orderIsoMapComap e) (P.1 i) := rfl

@[simp]
theorem map_symm_map {parity : ℕ} (e : V ≃ₗ[K] V)
    (P : PartialFlag (K := K) (V := V) (n := n) parity) :
    (P.map e).map e.symm = P := by
  apply PartialFlag.ext
  intro i
  exact submodule_map_symm_map e (P.1 i)

@[simp]
theorem map_map_symm {parity : ℕ} (e : V ≃ₗ[K] V)
    (P : PartialFlag (K := K) (V := V) (n := n) parity) :
    (P.map e.symm).map e = P := by
  simpa using map_symm_map e.symm P

/-- Linear transport is an equivalence on partial flags. -/
noncomputable def mapEquiv {parity : ℕ} (e : V ≃ₗ[K] V) :
    PartialFlag (K := K) (V := V) (n := n) parity ≃
      PartialFlag (K := K) (V := V) (n := n) parity where
  toFun := map e
  invFun := map e.symm
  left_inv := map_symm_map e
  right_inv := map_map_symm e

@[simp]
theorem mapEquiv_apply {parity : ℕ} (e : V ≃ₗ[K] V)
    (P : PartialFlag (K := K) (V := V) (n := n) parity) :
    mapEquiv e P = P.map e := rfl

@[simp]
theorem map_ofComplete {parity : ℕ} (e : V ≃ₗ[K] V)
    (F : CompleteFlag K V n) :
    (PartialFlag.ofComplete parity F).map e =
      PartialFlag.ofComplete parity (F.map e) := by
  apply PartialFlag.ext
  intro i
  by_cases hi : i.val % 2 = parity % 2
  · change (Submodule.orderIsoMapComap e) (flagPart parity F i) =
        flagPart parity (F.map e) i
    simp [flagPart, hi]
  · change (Submodule.orderIsoMapComap e) (flagPart parity F i) =
        flagPart parity (F.map e) i
    simp [flagPart, hi]

end PartialFlag

theorem Compatible.map
    {P : EvenPartialFlag (K := K) (V := V) (n := n)}
    {Q : OddPartialFlag (K := K) (V := V) (n := n)}
    (h : Compatible P Q) (e : V ≃ₗ[K] V) :
    Compatible (P.map e) (Q.map e) := by
  obtain ⟨F, hEven, hOdd⟩ := h
  refine ⟨F.map e, ?_, ?_⟩
  · exact (PartialFlag.map_ofComplete e F).symm.trans (congrArg (PartialFlag.map e) hEven)
  · exact (PartialFlag.map_ofComplete e F).symm.trans (congrArg (PartialFlag.map e) hOdd)

/-- Every linear equivalence acts by an automorphism of the halved graph. -/
noncomputable def halvedFlagGraphIso (e : V ≃ₗ[K] V) :
    halvedFlagGraph (K := K) (V := V) (n := n) ≃g
      halvedFlagGraph (K := K) (V := V) (n := n) where
  __ := PartialFlag.mapEquiv e
  map_rel_iff' := by
    intro P P'
    rw [halvedFlagGraph_adj_iff, halvedFlagGraph_adj_iff]
    constructor
    · rintro ⟨hne, Q, hPQ, hP'Q⟩
      refine ⟨fun h ↦ hne (congrArg (PartialFlag.map e) h), Q.map e.symm, ?_, ?_⟩
      · simpa using hPQ.map e.symm
      · simpa using hP'Q.map e.symm
    · rintro ⟨hne, Q, hPQ, hP'Q⟩
      refine ⟨fun h ↦ hne ((PartialFlag.mapEquiv e).injective h), Q.map e, ?_, ?_⟩
      · exact hPQ.map e
      · exact hP'Q.map e

@[simp]
theorem halvedFlagGraphIso_apply (e : V ≃ₗ[K] V)
    (P : EvenPartialFlag (K := K) (V := V) (n := n)) :
    halvedFlagGraphIso e P = P.map e := rfl

/-- Transitivity on even partial flags. -/
theorem exists_halvedFlagGraphIso_map_eq
    (P P' : EvenPartialFlag (K := K) (V := V) (n := n)) :
    ∃ φ : halvedFlagGraph (K := K) (V := V) (n := n) ≃g
        halvedFlagGraph (K := K) (V := V) (n := n), φ P = P' := by
  obtain ⟨F, hF⟩ := P.property
  obtain ⟨F', hF'⟩ := P'.property
  have hPF : PartialFlag.ofComplete 0 F = P := Subtype.ext hF
  have hPF' : PartialFlag.ofComplete 0 F' = P' := Subtype.ext hF'
  obtain ⟨b, π, hFb, hF'b⟩ := common_apartment K V F F'
  let b' : Basis (Fin n) K V := b.reindex π.symm
  let e : V ≃ₗ[K] V := b.equiv b' (Equiv.refl (Fin n))
  have hmapBasis : b.map e = b' := by
    dsimp [e]
    rw [Basis.map_equiv]
    simp
  have hmapFlag : F.map e = F' := by
    calc
      F.map e = (CompleteFlag.ofBasis b).map e := congrArg (fun H ↦ H.map e) hFb
      _ = CompleteFlag.ofBasis (b.map e) := CompleteFlag.map_ofBasis e b
      _ = CompleteFlag.ofBasis b' := congrArg CompleteFlag.ofBasis hmapBasis
      _ = F' := hF'b.symm
  refine ⟨halvedFlagGraphIso e, ?_⟩
  calc
    halvedFlagGraphIso e P = P.map e := rfl
    _ = (PartialFlag.ofComplete 0 F).map e := congrArg (PartialFlag.map e) hPF.symm
    _ = PartialFlag.ofComplete 0 (F.map e) := PartialFlag.map_ofComplete e F
    _ = PartialFlag.ofComplete 0 F' := congrArg (PartialFlag.ofComplete 0) hmapFlag
    _ = P' := hPF'

/-- All neighbor sets have the same finite cardinality. -/
theorem halvedFlagGraph_natCard_neighborSet_eq
    [Finite K] [Finite V]
    (P P' : EvenPartialFlag (K := K) (V := V) (n := n)) :
    Nat.card ((halvedFlagGraph (K := K) (V := V) (n := n)).neighborSet P) =
      Nat.card ((halvedFlagGraph (K := K) (V := V) (n := n)).neighborSet P') := by
  obtain ⟨φ, hφ⟩ := exists_halvedFlagGraphIso_map_eq P P'
  simpa [hφ] using Nat.card_congr (φ.mapNeighborSet P)

end DegreeDiameter

end PortSymmetry

/- DegreeDiameter.Proposition31 -/
section PortProposition31

/-
# Proposition 3.1 over arbitrary finite fields

The definitions below name the concrete graph in the write-up: its vertices
are the even partial flags in the recursively split `(2k+1)`-dimensional
coordinate model `FlagSpace K k`, and
adjacency means sharing a compatible odd partial flag.  The degree is the
cardinality of the neighbor set of the standard coordinate flag; transitivity
then proves that this is the degree of every vertex.

`proposition_3_1_over_finite_field` packages the exact order formula, the
sharp degree cap, regularity, and exact diameter for this one graph.  The
prime-power theorem is a genuine instance obtained from a finite field of
the requested cardinality, rather than a separate prime-only construction.
-/

namespace DegreeDiameter

open Module

/-- The vertex type of the graph `H_{k,K}` in Proposition 3.1. -/
abbrev Proposition31Vertex (K : Type*) [Field K] (k : ℕ) :=
  EvenPartialFlag (K := K) (V := FlagSpace K k) (n := 2 * k + 1)

/-- The concrete halved flag graph `H_{k,K}`. -/
abbrev Proposition31Graph (K : Type*) [Field K] (k : ℕ) :
    SimpleGraph (Proposition31Vertex K k) :=
  halvedFlagGraph (K := K) (V := FlagSpace K k) (n := 2 * k + 1)

/-- A coordinate basis of the recursively split model. -/
noncomputable def proposition31Basis (K : Type*) [Field K] (k : ℕ) :
    Basis (Fin (2 * k + 1)) K (FlagSpace K k) :=
  Module.finBasisOfFinrankEq K (FlagSpace K k) (by
    simpa only [flagDim_eq] using finrank_flagSpace (K := K) k)

/-- The standard vertex used to name the actual common degree. -/
noncomputable def proposition31StandardEven (K : Type*) [Field K] (k : ℕ) :
    Proposition31Vertex K k :=
  PartialFlag.ofComplete 0 (CompleteFlag.ofBasis (proposition31Basis K k))

/-- The actual degree of `H_{k,K}`, measured at the standard coordinate
flag.  Regularity below proves that this is independent of the vertex. -/
noncomputable def proposition31Degree (K : Type*) [Field K] [Finite K]
    (k : ℕ) : ℕ :=
  Nat.card ((Proposition31Graph K k).neighborSet
    (proposition31StandardEven K k))

/-- All vertices of the concrete graph have its named actual degree. -/
theorem proposition31_regular (K : Type*) [Field K] [Finite K] (k : ℕ) :
    ∀ P : Proposition31Vertex K k,
      Nat.card ((Proposition31Graph K k).neighborSet P) =
        proposition31Degree K k := by
  intro P
  exact halvedFlagGraph_natCard_neighborSet_eq P (proposition31StandardEven K k)

/-- **Proposition 3.1 (finite-field form).**  For every finite field `K` and
positive `k`, the same concrete graph is regular, has the exact q-factorial
order in both multiplication and division form, obeys the paper's sharp
degree cap, and has extended diameter exactly `k`. -/
theorem proposition_3_1_over_finite_field
    (K : Type*) [Field K] [Finite K] (k : ℕ) (hk : 0 < k) :
    (∀ P : Proposition31Vertex K k,
        Nat.card ((Proposition31Graph K k).neighborSet P) =
          proposition31Degree K k) ∧
    Nat.card (Proposition31Vertex K k) * (Nat.card K + 1) ^ k =
      qFactorial (Nat.card K) (2 * k + 1) ∧
    Nat.card (Proposition31Vertex K k) =
      qFactorial (Nat.card K) (2 * k + 1) / (Nat.card K + 1) ^ k ∧
    proposition31Degree K k ≤
      (Nat.card K + 1) ^ k * ((Nat.card K + 1) ^ k - 1) ∧
    (Proposition31Graph K k).ediam = (k : ℕ∞) := by
  refine ⟨proposition31_regular K k, ?_, ?_, ?_, ?_⟩
  · exact natCard_evenPartialFlag_mul_completion_eq_qFactorial
      (K := K) (V := FlagSpace K k) k (by
        simpa only [flagDim_eq] using finrank_flagSpace (K := K) k)
  · exact natCard_flagSpaceEvenPartialFlag_eq_qFactorial_div (K := K) k
  · exact halvedFlagGraph_natCard_neighborSet_le_sharp
      (K := K) (V := FlagSpace K k) k
      (proposition31StandardEven K k)
  · exact halvedFlagGraph_ediam_eq_ofBasis
      (K := K) (V := FlagSpace K k) k hk (proposition31Basis K k)

/-- **Proposition 3.1 (prime-power form).**  Every prime power `q` supplies
a finite field of cardinality exactly `q`, and hence the graph with exactly
the numerical parameters stated in the write-up. -/
theorem proposition_3_1_for_prime_power (q : PrimePowerIndex)
    (k : ℕ) (hk : 0 < k) :
    (∀ P : Proposition31Vertex (PrimePowerField q) k,
        Nat.card ((Proposition31Graph (PrimePowerField q) k).neighborSet P) =
          proposition31Degree (PrimePowerField q) k) ∧
    Nat.card (Proposition31Vertex (PrimePowerField q) k) * (q.1 + 1) ^ k =
      qFactorial q.1 (2 * k + 1) ∧
    Nat.card (Proposition31Vertex (PrimePowerField q) k) =
      qFactorial q.1 (2 * k + 1) / (q.1 + 1) ^ k ∧
    proposition31Degree (PrimePowerField q) k ≤
      (q.1 + 1) ^ k * ((q.1 + 1) ^ k - 1) ∧
    (Proposition31Graph (PrimePowerField q) k).ediam = (k : ℕ∞) := by
  simpa only [natCard_primePowerField] using
    (proposition_3_1_over_finite_field (PrimePowerField q) k hk)

end DegreeDiameter

end PortProposition31

/- DegreeDiameter.Proposition31Asymptotics -/
section PortProposition31Asymptotics

/-
# The graph-family asymptotics in Proposition 3.1

This file proves equation (9) for the actual halved flag graphs, indexed by
`PrimePowerIndex`.  Thus `atTop` means that the field cardinality tends to
infinity through all prime powers, as proved by
`tendsto_primePowerIndex_val`.

The proof follows the write-up.  Exact flag enumeration first shows that the
order divided by the `k`-th power of the displayed degree cap tends to one.
The Moore bound and regularity then squeeze the actual common degree against
that cap.  Substitution gives the second displayed asymptotic.
-/

open Filter Finset Polynomial Topology
open scoped BigOperators

namespace DegreeDiameter

noncomputable section

/-- The factor `A_q = (q+1)^k` in Proposition 3.1. -/
def proposition31Amplitude (q k : ℕ) : ℕ :=
  (q + 1) ^ k

/-- The sharp displayed degree cap
`K_q = (q+1)^k ((q+1)^k-1)`. -/
def proposition31DegreeCap (q k : ℕ) : ℕ :=
  proposition31Amplitude q k * (proposition31Amplitude q k - 1)

/-- The order of the concrete graph over the chosen field of order `q`. -/
abbrev proposition31PrimePowerOrder (k : ℕ) (q : PrimePowerIndex) : ℕ :=
  Nat.card (Proposition31Vertex (PrimePowerField q) k)

/-- The actual common degree of the concrete graph over the chosen field of
order `q`. -/
abbrev proposition31PrimePowerDegree (k : ℕ) (q : PrimePowerIndex) : ℕ :=
  proposition31Degree (PrimePowerField q) k

/- ## Polynomial form of exact flag enumeration -/

/-- The real polynomial `1 + X + ... + X^(n-1)`. -/
def proposition31QIntegerPolynomial (n : ℕ) : ℝ[X] :=
  ∑ i ∈ Finset.range n, X ^ i

/-- The real polynomial whose value at a natural number `q` is
`qFactorial q n`. -/
def proposition31QFactorialPolynomial (n : ℕ) : ℝ[X] :=
  ∏ i ∈ Finset.range n, proposition31QIntegerPolynomial (i + 1)

/-- The polynomial `(X+1)^k`. -/
def proposition31AmplitudePolynomial (k : ℕ) : ℝ[X] :=
  (X + 1) ^ k

/-- The polynomial version of the sharp degree cap. -/
def proposition31CapPolynomial (k : ℕ) : ℝ[X] :=
  proposition31AmplitudePolynomial k *
    (proposition31AmplitudePolynomial k - 1)

/-- The denominator polynomial `A_q K_q^k` occurring after the exact
multiplication count is substituted into `N_q / K_q^k`. -/
def proposition31DenominatorPolynomial (k : ℕ) : ℝ[X] :=
  proposition31AmplitudePolynomial k * proposition31CapPolynomial k ^ k

@[simp]
theorem proposition31_eval_qIntegerPolynomial (x : ℝ) (n : ℕ) :
    eval x (proposition31QIntegerPolynomial n) =
      ∑ i ∈ Finset.range n, x ^ i := by
  simp [proposition31QIntegerPolynomial]

@[simp]
theorem proposition31_eval_qIntegerPolynomial_nat (q n : ℕ) :
    eval (q : ℝ) (proposition31QIntegerPolynomial n) =
      (qInteger q n : ℝ) := by
  simp [proposition31QIntegerPolynomial, qInteger]

theorem proposition31_qIntegerPolynomial_monic {n : ℕ} (hn : n ≠ 0) :
    (proposition31QIntegerPolynomial n).Monic := by
  simpa only [proposition31QIntegerPolynomial] using
    (Polynomial.monic_geom_sum_X (R := ℝ) hn)

theorem proposition31_qIntegerPolynomial_natDegree_succ (n : ℕ) :
    (proposition31QIntegerPolynomial (n + 1)).natDegree = n := by
  induction n with
  | zero => simp [proposition31QIntegerPolynomial]
  | succ n ih =>
      change
        (∑ i ∈ Finset.range ((n + 1) + 1), (X : ℝ[X]) ^ i).natDegree = n + 1
      rw [Finset.sum_range_succ]
      change
        (proposition31QIntegerPolynomial (n + 1) + (X : ℝ[X]) ^ (n + 1)).natDegree =
          n + 1
      have hlt :
          (proposition31QIntegerPolynomial (n + 1)).natDegree <
            ((X : ℝ[X]) ^ (n + 1)).natDegree := by
        rw [ih, Polynomial.natDegree_X_pow]
        exact Nat.lt_succ_self n
      rw [Polynomial.natDegree_add_eq_right_of_natDegree_lt hlt,
        Polynomial.natDegree_X_pow]

@[simp]
theorem proposition31_eval_qFactorialPolynomial_nat (q n : ℕ) :
    eval (q : ℝ) (proposition31QFactorialPolynomial n) =
      (qFactorial q n : ℝ) := by
  rw [qFactorial_eq_prod_range, proposition31QFactorialPolynomial,
    Polynomial.eval_prod]
  simp_rw [proposition31_eval_qIntegerPolynomial_nat]
  push_cast
  rfl

theorem proposition31_qFactorialPolynomial_monic (n : ℕ) :
    (proposition31QFactorialPolynomial n).Monic := by
  apply Polynomial.monic_prod_of_monic
  intro i hi
  exact proposition31_qIntegerPolynomial_monic (by omega)

theorem proposition31_qFactorialPolynomial_natDegree_eq_sum (n : ℕ) :
    (proposition31QFactorialPolynomial n).natDegree =
      ∑ i ∈ Finset.range n, i := by
  rw [proposition31QFactorialPolynomial,
    Polynomial.natDegree_prod_of_monic]
  · exact Finset.sum_congr rfl fun i hi ↦
      proposition31_qIntegerPolynomial_natDegree_succ i
  · intro i hi
    exact proposition31_qIntegerPolynomial_monic (by omega)

theorem proposition31_qFactorialPolynomial_natDegree_odd (k : ℕ) :
    (proposition31QFactorialPolynomial (2 * k + 1)).natDegree =
      2 * k * k + k := by
  rw [proposition31_qFactorialPolynomial_natDegree_eq_sum]
  refine Nat.mul_right_cancel (m := 2) (by omega) ?_
  rw [Finset.sum_range_id_mul_two]
  have hsub : 2 * k + 1 - 1 = 2 * k := by omega
  rw [hsub]
  ring

theorem proposition31_amplitudePolynomial_monic (k : ℕ) :
    (proposition31AmplitudePolynomial k).Monic := by
  simpa only [proposition31AmplitudePolynomial, Polynomial.C_1] using
    (Polynomial.monic_X_add_C (1 : ℝ)).pow k

@[simp]
theorem proposition31_amplitudePolynomial_natDegree (k : ℕ) :
    (proposition31AmplitudePolynomial k).natDegree = k := by
  rw [proposition31AmplitudePolynomial, ← Polynomial.C_1,
    (Polynomial.monic_X_add_C (1 : ℝ)).natDegree_pow,
    Polynomial.natDegree_X_add_C, Nat.mul_one]

private theorem proposition31_degree_one_lt_amplitudePolynomial_degree
    {k : ℕ} (hk : 0 < k) :
    degree (1 : ℝ[X]) < degree (proposition31AmplitudePolynomial k) := by
  rw [Polynomial.degree_one,
    Polynomial.degree_eq_natDegree (proposition31_amplitudePolynomial_monic k).ne_zero,
    proposition31_amplitudePolynomial_natDegree]
  exact_mod_cast hk

theorem proposition31_amplitudePolynomial_sub_one_monic
    {k : ℕ} (hk : 0 < k) :
    (proposition31AmplitudePolynomial k - 1).Monic :=
  (proposition31_amplitudePolynomial_monic k).sub_of_left
    (proposition31_degree_one_lt_amplitudePolynomial_degree hk)

@[simp]
theorem proposition31_amplitudePolynomial_sub_one_natDegree
    {k : ℕ} (hk : 0 < k) :
    (proposition31AmplitudePolynomial k - 1).natDegree = k := by
  rw [Polynomial.natDegree_eq_of_degree_eq
    (Polynomial.degree_sub_eq_left_of_degree_lt
      (proposition31_degree_one_lt_amplitudePolynomial_degree hk)),
    proposition31_amplitudePolynomial_natDegree]

theorem proposition31_capPolynomial_monic {k : ℕ} (hk : 0 < k) :
    (proposition31CapPolynomial k).Monic := by
  exact (proposition31_amplitudePolynomial_monic k).mul
    (proposition31_amplitudePolynomial_sub_one_monic hk)

@[simp]
theorem proposition31_capPolynomial_natDegree {k : ℕ} (hk : 0 < k) :
    (proposition31CapPolynomial k).natDegree = 2 * k := by
  rw [proposition31CapPolynomial,
    (proposition31_amplitudePolynomial_monic k).natDegree_mul
      (proposition31_amplitudePolynomial_sub_one_monic hk),
    proposition31_amplitudePolynomial_natDegree,
    proposition31_amplitudePolynomial_sub_one_natDegree hk]
  omega

theorem proposition31_denominatorPolynomial_monic {k : ℕ} (hk : 0 < k) :
    (proposition31DenominatorPolynomial k).Monic := by
  exact (proposition31_amplitudePolynomial_monic k).mul
    ((proposition31_capPolynomial_monic hk).pow k)

@[simp]
theorem proposition31_denominatorPolynomial_natDegree {k : ℕ} (hk : 0 < k) :
    (proposition31DenominatorPolynomial k).natDegree = 2 * k * k + k := by
  rw [proposition31DenominatorPolynomial,
    (proposition31_amplitudePolynomial_monic k).natDegree_mul
      ((proposition31_capPolynomial_monic hk).pow k),
    (proposition31_capPolynomial_monic hk).natDegree_pow,
    proposition31_amplitudePolynomial_natDegree,
    proposition31_capPolynomial_natDegree hk]
  ring

@[simp]
theorem proposition31_eval_amplitudePolynomial_nat (q k : ℕ) :
    eval (q : ℝ) (proposition31AmplitudePolynomial k) =
      (proposition31Amplitude q k : ℝ) := by
  simp [proposition31AmplitudePolynomial, proposition31Amplitude]

@[simp]
theorem proposition31_eval_capPolynomial_nat (q k : ℕ) :
    eval (q : ℝ) (proposition31CapPolynomial k) =
      (proposition31DegreeCap q k : ℝ) := by
  have hA : 1 ≤ proposition31Amplitude q k := by
    exact Nat.one_le_pow' k q
  rw [proposition31CapPolynomial, eval_mul, eval_sub, eval_one,
    proposition31_eval_amplitudePolynomial_nat,
    proposition31DegreeCap, Nat.cast_mul, Nat.cast_sub hA, Nat.cast_one]

@[simp]
theorem proposition31_eval_denominatorPolynomial_nat (q k : ℕ) :
    eval (q : ℝ) (proposition31DenominatorPolynomial k) =
      (proposition31Amplitude q k * proposition31DegreeCap q k ^ k : ℕ) := by
  simp [proposition31DenominatorPolynomial]

/-- Exact q-factorial enumeration and the cap have the same monic leading
term after the multiplication count is substituted. -/
theorem proposition31_qFactorial_div_denominator_tendsto_one
    (k : ℕ) (hk : 0 < k) :
    Tendsto
      (fun x : ℝ ↦
        eval x (proposition31QFactorialPolynomial (2 * k + 1)) /
          eval x (proposition31DenominatorPolynomial k))
      atTop (nhds 1) := by
  have hdegree :
      (proposition31QFactorialPolynomial (2 * k + 1)).degree =
        (proposition31DenominatorPolynomial k).degree := by
    rw [Polynomial.degree_eq_natDegree
        (proposition31_qFactorialPolynomial_monic (2 * k + 1)).ne_zero,
      Polynomial.degree_eq_natDegree
        (proposition31_denominatorPolynomial_monic hk).ne_zero,
      proposition31_qFactorialPolynomial_natDegree_odd,
      proposition31_denominatorPolynomial_natDegree hk]
  have h := Polynomial.div_tendsto_atTop_leadingCoeff_div_of_degree_eq
    (proposition31QFactorialPolynomial (2 * k + 1))
    (proposition31DenominatorPolynomial k) hdegree
  simpa only [
      (proposition31_qFactorialPolynomial_monic (2 * k + 1)).leadingCoeff,
      (proposition31_denominatorPolynomial_monic hk).leadingCoeff,
      div_one] using h

/-- The purely algebraic ratio, restricted from all real `q` to prime-power
cardinalities. -/
theorem proposition31_qFactorial_div_capDenominator_tendsto_one
    (k : ℕ) (hk : 0 < k) :
    Tendsto
      (fun q : PrimePowerIndex ↦
        (qFactorial q.1 (2 * k + 1) : ℝ) /
          (proposition31Amplitude q.1 k *
            proposition31DegreeCap q.1 k ^ k : ℕ))
      atTop (nhds 1) := by
  have hreal := proposition31_qFactorial_div_denominator_tendsto_one k hk
  have hcast : Tendsto (fun q : PrimePowerIndex ↦ (q.1 : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp tendsto_primePowerIndex_val
  have hcomp := hreal.comp hcast
  change Tendsto
    (fun q : PrimePowerIndex ↦
      eval (q.1 : ℝ) (proposition31QFactorialPolynomial (2 * k + 1)) /
        eval (q.1 : ℝ) (proposition31DenominatorPolynomial k))
    atTop (nhds 1) at hcomp
  simpa only [
    proposition31_eval_qFactorialPolynomial_nat,
    proposition31_eval_denominatorPolynomial_nat] using hcomp

/- ## Exact order versus the cap -/

private theorem proposition31_amplitude_pos (q k : ℕ) :
    0 < proposition31Amplitude q k := by
  exact pow_pos (Nat.succ_pos q) k

private theorem proposition31_cap_pos (q : PrimePowerIndex)
    {k : ℕ} (hk : 0 < k) :
    0 < proposition31DegreeCap q.1 k := by
  have hbase : 1 < q.1 + 1 := by
    have hq := q.2.two_le
    omega
  have hpow : q.1 + 1 ≤ proposition31Amplitude q.1 k := by
    simpa only [proposition31Amplitude, pow_one] using
      (pow_le_pow_right₀ (a := q.1 + 1) (by omega) hk)
  have hA : 1 < proposition31Amplitude q.1 k := hbase.trans_le hpow
  exact Nat.mul_pos (Nat.zero_lt_of_lt hA) (Nat.sub_pos_of_lt hA)

private theorem proposition31_order_mul_amplitude
    (q : PrimePowerIndex) (k : ℕ) (hk : 0 < k) :
    proposition31PrimePowerOrder k q * proposition31Amplitude q.1 k =
      qFactorial q.1 (2 * k + 1) := by
  simpa only [proposition31Amplitude] using
    (proposition_3_1_for_prime_power q k hk).2.1

private theorem proposition31_degree_le_cap
    (q : PrimePowerIndex) (k : ℕ) (hk : 0 < k) :
    proposition31PrimePowerDegree k q ≤ proposition31DegreeCap q.1 k := by
  simpa only [proposition31DegreeCap, proposition31Amplitude] using
    (proposition_3_1_for_prime_power q k hk).2.2.2.1

private theorem proposition31_order_div_cap_pow_eq_qFactorial_ratio
    (q : PrimePowerIndex) (k : ℕ) (hk : 0 < k) :
    (proposition31PrimePowerOrder k q : ℝ) /
        (proposition31DegreeCap q.1 k : ℝ) ^ k =
      (qFactorial q.1 (2 * k + 1) : ℝ) /
        (proposition31Amplitude q.1 k *
          proposition31DegreeCap q.1 k ^ k : ℕ) := by
  have hmul :
      (proposition31PrimePowerOrder k q : ℝ) *
          proposition31Amplitude q.1 k =
        qFactorial q.1 (2 * k + 1) := by
    exact_mod_cast proposition31_order_mul_amplitude q k hk
  have hA : (proposition31Amplitude q.1 k : ℝ) ≠ 0 := by
    exact_mod_cast (proposition31_amplitude_pos q.1 k).ne'
  have hC : (proposition31DegreeCap q.1 k : ℝ) ≠ 0 := by
    exact_mod_cast (proposition31_cap_pos q hk).ne'
  push_cast
  rw [← hmul]
  field_simp [hA, hC]

/-- The exact graph order divided by the `k`-th power of the displayed cap
tends to one.  This is the algebraic input to the Moore squeeze. -/
theorem proposition31_order_div_cap_pow_tendsto_one
    (k : ℕ) (hk : 0 < k) :
    Tendsto
      (fun q : PrimePowerIndex ↦
        (proposition31PrimePowerOrder k q : ℝ) /
          (proposition31DegreeCap q.1 k : ℝ) ^ k)
      atTop (nhds 1) := by
  refine (proposition31_qFactorial_div_capDenominator_tendsto_one k hk).congr' ?_
  exact Eventually.of_forall fun q ↦
    (proposition31_order_div_cap_pow_eq_qFactorial_ratio q k hk).symm

/- ## The Moore squeeze for the actual common degree -/

private theorem proposition31_val_le_cap
    (q : PrimePowerIndex) {k : ℕ} (hk : 0 < k) :
    q.1 ≤ proposition31DegreeCap q.1 k := by
  have hAone : 1 ≤ proposition31Amplitude q.1 k := by
    exact Nat.one_le_pow' k q.1
  have hqA : q.1 + 1 ≤ proposition31Amplitude q.1 k := by
    simpa only [proposition31Amplitude, pow_one] using
      (pow_le_pow_right₀ (a := q.1 + 1) (by omega) hk)
  have hqsub : q.1 ≤ proposition31Amplitude q.1 k - 1 := by
    omega
  calc
    q.1 ≤ proposition31Amplitude q.1 k - 1 := hqsub
    _ = 1 * (proposition31Amplitude q.1 k - 1) := by simp
    _ ≤ proposition31Amplitude q.1 k *
          (proposition31Amplitude q.1 k - 1) :=
      Nat.mul_le_mul_right _ hAone
    _ = proposition31DegreeCap q.1 k := rfl

private theorem proposition31_cap_tendsto_atTop
    {k : ℕ} (hk : 0 < k) :
    Tendsto (fun q : PrimePowerIndex ↦ proposition31DegreeCap q.1 k)
      atTop atTop :=
  tendsto_atTop_mono (fun q ↦ proposition31_val_le_cap q hk)
    tendsto_primePowerIndex_val

private theorem proposition31_inv_cap_tendsto_zero
    {k : ℕ} (hk : 0 < k) :
    Tendsto
      (fun q : PrimePowerIndex ↦
        (proposition31DegreeCap q.1 k : ℝ)⁻¹)
      atTop (nhds 0) := by
  have hcast : Tendsto
      (fun q : PrimePowerIndex ↦ (proposition31DegreeCap q.1 k : ℝ))
      atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (proposition31_cap_tendsto_atTop hk)
  exact tendsto_inv_atTop_zero.comp hcast

private theorem proposition31_order_le_degree_add_one_pow
    (q : PrimePowerIndex) (k : ℕ) (hk : 0 < k) :
    proposition31PrimePowerOrder k q ≤
      (proposition31PrimePowerDegree k q + 1) ^ k := by
  let G := Proposition31Graph (PrimePowerField q) k
  have hp := proposition_3_1_for_prime_power q k hk
  have hregular : ∀ P,
      ((G.neighborSet P).ncard : ℕ) = proposition31PrimePowerDegree k q := by
    intro P
    simpa only [G, Nat.card_coe_set_eq] using hp.1 P
  have hdegree : MaxDegreeLE G (proposition31PrimePowerDegree k q) := by
    intro P
    exact (hregular P).le
  have hdiam : G.ediam ≤ (k : ℕ∞) := hp.2.2.2.2.le
  have hmoore := natCard_le_mooreBound_of_ediam_le' hdegree hdiam
  have hcoarse := mooreBound_le_add_one_pow k
    (proposition31PrimePowerDegree k q)
  simpa only [G] using hmoore.trans hcoarse

/-- **First asymptotic in Proposition 3.1, equation (9).**  For fixed
positive `k`, the actual common degree of the concrete graph is asymptotic
to the paper's sharp cap as `q` tends to infinity through prime powers. -/
theorem proposition31_degree_div_cap_tendsto_one
    (k : ℕ) (hk : 0 < k) :
    Tendsto
      (fun q : PrimePowerIndex ↦
        (proposition31Degree (PrimePowerField q) k : ℝ) /
          (proposition31DegreeCap q.1 k : ℝ))
      atTop (nhds 1) := by
  rw [tendsto_order]
  constructor
  · intro y hy
    by_cases hy0 : y < 0
    · exact Eventually.of_forall fun q ↦ hy0.trans_le (by positivity)
    · have hy_nonneg : 0 ≤ y := le_of_not_gt hy0
      let s : ℝ := (y + 1) / 2
      have hys : y < s := by
        dsimp only [s]
        linarith
      have hs1 : s < 1 := by
        dsimp only [s]
        linarith
      have hs0 : 0 ≤ s := by
        dsimp only [s]
        linarith
      have hspow : s ^ k < 1 := pow_lt_one₀ hs0 hs1 hk.ne'
      have horder := (proposition31_order_div_cap_pow_tendsto_one k hk).eventually
        (Ioi_mem_nhds hspow)
      have hinv := (proposition31_inv_cap_tendsto_zero hk).eventually
        (Iio_mem_nhds (sub_pos.mpr hys))
      filter_upwards [horder, hinv] with q horderq hinvq
      by_contra hnot
      have hratio_le :
          (proposition31PrimePowerDegree k q : ℝ) /
              (proposition31DegreeCap q.1 k : ℝ) ≤ y :=
        le_of_not_gt hnot
      have hcapPos : (0 : ℝ) < proposition31DegreeCap q.1 k := by
        exact_mod_cast proposition31_cap_pos q hk
      have hbase_lt :
          (proposition31PrimePowerDegree k q : ℝ) /
                (proposition31DegreeCap q.1 k : ℝ) +
              1 / (proposition31DegreeCap q.1 k : ℝ) < s := by
        rw [one_div]
        linarith
      have hbase_nonneg :
          0 ≤
            (proposition31PrimePowerDegree k q : ℝ) /
                (proposition31DegreeCap q.1 k : ℝ) +
              1 / (proposition31DegreeCap q.1 k : ℝ) := by
        positivity
      have hpow_lt :
          ((proposition31PrimePowerDegree k q : ℝ) /
                (proposition31DegreeCap q.1 k : ℝ) +
              1 / (proposition31DegreeCap q.1 k : ℝ)) ^ k < s ^ k :=
        pow_lt_pow_left₀ hbase_lt hbase_nonneg hk.ne'
      have hMoore :
          (proposition31PrimePowerOrder k q : ℝ) ≤
            ((proposition31PrimePowerDegree k q + 1) ^ k : ℕ) := by
        exact_mod_cast proposition31_order_le_degree_add_one_pow q k hk
      have hdenPos :
          0 < (proposition31DegreeCap q.1 k : ℝ) ^ k :=
        pow_pos hcapPos k
      have hMooreRatio :
          (proposition31PrimePowerOrder k q : ℝ) /
                (proposition31DegreeCap q.1 k : ℝ) ^ k ≤
            ((proposition31PrimePowerDegree k q : ℝ) /
                  (proposition31DegreeCap q.1 k : ℝ) +
                1 / (proposition31DegreeCap q.1 k : ℝ)) ^ k := by
        calc
          (proposition31PrimePowerOrder k q : ℝ) /
                (proposition31DegreeCap q.1 k : ℝ) ^ k ≤
              (((proposition31PrimePowerDegree k q + 1) ^ k : ℕ) : ℝ) /
                (proposition31DegreeCap q.1 k : ℝ) ^ k :=
            div_le_div_of_nonneg_right hMoore hdenPos.le
          _ = ((proposition31PrimePowerDegree k q : ℝ) /
                  (proposition31DegreeCap q.1 k : ℝ) +
                1 / (proposition31DegreeCap q.1 k : ℝ)) ^ k := by
            push_cast
            rw [← div_pow]
            congr 1
            field_simp [hcapPos.ne']
      have hcontr :
          (proposition31PrimePowerOrder k q : ℝ) /
              (proposition31DegreeCap q.1 k : ℝ) ^ k < s ^ k :=
        hMooreRatio.trans_lt hpow_lt
      exact lt_asymm horderq hcontr
  · intro z hz
    exact Eventually.of_forall fun q ↦ by
      have hcapPos : (0 : ℝ) < proposition31DegreeCap q.1 k := by
        exact_mod_cast proposition31_cap_pos q hk
      have hdegree :
          (proposition31PrimePowerDegree k q : ℝ) ≤
            proposition31DegreeCap q.1 k := by
        exact_mod_cast proposition31_degree_le_cap q k hk
      exact ((div_le_one hcapPos).2 hdegree).trans_lt hz

/-- **Second asymptotic in Proposition 3.1, equation (9).**  For fixed
positive `k`, the exact order of the concrete graph is asymptotic to the
`k`-th power of its actual common degree as `q` tends to infinity through
prime powers. -/
theorem proposition31_order_div_degree_pow_tendsto_one
    (k : ℕ) (hk : 0 < k) :
    Tendsto
      (fun q : PrimePowerIndex ↦
        (Nat.card (Proposition31Vertex (PrimePowerField q) k) : ℝ) /
          (proposition31Degree (PrimePowerField q) k : ℝ) ^ k)
      atTop (nhds 1) := by
  have horder := proposition31_order_div_cap_pow_tendsto_one k hk
  have hdegree := proposition31_degree_div_cap_tendsto_one k hk
  have hquot : Tendsto
      (fun q : PrimePowerIndex ↦
        ((proposition31PrimePowerOrder k q : ℝ) /
            (proposition31DegreeCap q.1 k : ℝ) ^ k) /
          (((proposition31PrimePowerDegree k q : ℝ) /
            (proposition31DegreeCap q.1 k : ℝ)) ^ k))
      atTop (nhds 1) := by
    simpa only [proposition31PrimePowerDegree, Pi.div_def, Pi.div_apply, Pi.pow_apply,
      one_pow, div_one] using
      horder.div (hdegree.pow k) (by simp)
  have hdegreePos : ∀ᶠ q : PrimePowerIndex in atTop,
      0 < (proposition31PrimePowerDegree k q : ℝ) /
        (proposition31DegreeCap q.1 k : ℝ) :=
    hdegree.eventually (Ioi_mem_nhds zero_lt_one)
  refine hquot.congr' ?_
  filter_upwards [hdegreePos] with q hdegreeq
  have hcap : (proposition31DegreeCap q.1 k : ℝ) ≠ 0 := by
    exact_mod_cast (proposition31_cap_pos q hk).ne'
  have hdegree_ne : (proposition31PrimePowerDegree k q : ℝ) ≠ 0 := by
    intro hzero
    simp [hzero] at hdegreeq
  rw [div_pow]
  field_simp [hcap, hdegree_ne]

end

end DegreeDiameter

end PortProposition31Asymptotics

/- DegreeDiameter.Proposition31Full -/
section PortProposition31Full

/-
# Complete form of Proposition 3.1

This module gives one declaration containing every finite and asymptotic
clause of Proposition 3.1.  The finite clauses retain the exact multiplication
identity as well as its natural-division consequence.  Both limits in equation
(9) concern the same concrete prime-power graph and use its actual common
degree, not merely the displayed upper bound.
-/

open Filter Topology

namespace DegreeDiameter

/-- The finite claims of Proposition 3.1 for the concrete graph over the
chosen field of cardinality `q`.

The named fields expose the five claims in the paper: regularity with the
actual common degree, the exact order in multiplication and division form
(equation (6)), the sharp degree cap (equation (7)), and exact extended
diameter (equation (8)). -/
structure Proposition31FiniteClaims (q : PrimePowerIndex) (k : ℕ) : Prop where
  /-- The graph is regular of its actual common degree. -/
  regularity : ∀ P : Proposition31Vertex (PrimePowerField q) k,
    Nat.card ((Proposition31Graph (PrimePowerField q) k).neighborSet P) =
      proposition31PrimePowerDegree k q
  /-- Equation (6), before taking natural-number division. -/
  order_mul : proposition31PrimePowerOrder k q * (q.1 + 1) ^ k =
    qFactorial q.1 (2 * k + 1)
  /-- Equation (6), in the displayed natural-division form. -/
  order_eq : proposition31PrimePowerOrder k q =
    qFactorial q.1 (2 * k + 1) / (q.1 + 1) ^ k
  /-- Equation (7), with the actual degree on the left. -/
  degree_le_cap :
    proposition31PrimePowerDegree k q ≤ proposition31DegreeCap q.1 k
  /-- Equation (8), as equality of extended diameters. -/
  ediam_eq :
    (Proposition31Graph (PrimePowerField q) k).ediam = (k : ℕ∞)

/-- The finite part of Proposition 3.1, repackaged under a named proposition. -/
theorem proposition31_finite_claims (q : PrimePowerIndex)
    (k : ℕ) (hk : 0 < k) : Proposition31FiniteClaims q k := by
  have hp := proposition_3_1_for_prime_power q k hk
  exact
    { regularity := hp.1
      order_mul := hp.2.1
      order_eq := hp.2.2.1
      degree_le_cap := by
        simpa only [proposition31DegreeCap, proposition31Amplitude] using
          hp.2.2.2.1
      ediam_eq := hp.2.2.2.2 }

/-- **Proposition 3.1 (complete formal statement).**

For every prime-power field order, the concrete halved-flag graph satisfies
all finite claims in equations (6)--(8).  As the field order tends to infinity
through all prime powers, its actual degree divided by the cap and its exact
order divided by the `k`-th power of that actual degree both tend to one, as in
equation (9). -/
theorem proposition_3_1 (k : ℕ) (hk : 0 < k) :
    (∀ q : PrimePowerIndex, Proposition31FiniteClaims q k) ∧
    Tendsto
      (fun q : PrimePowerIndex ↦
        (proposition31PrimePowerDegree k q : ℝ) /
          (proposition31DegreeCap q.1 k : ℝ))
      atTop (nhds 1) ∧
    Tendsto
      (fun q : PrimePowerIndex ↦
        (proposition31PrimePowerOrder k q : ℝ) /
          (proposition31PrimePowerDegree k q : ℝ) ^ k)
      atTop (nhds 1) := by
  exact ⟨fun q ↦ proposition31_finite_claims q k hk,
    proposition31_degree_div_cap_tendsto_one k hk,
    proposition31_order_div_degree_pow_tendsto_one k hk⟩

/-- Consequence of the two asymptotic clauses of Proposition 3.1.

This is the exact algebraic bridge used in the proof of Theorem 1.1.  It is
proved from the bundled declaration `proposition_3_1`, rather than by invoking
the independently available cap-normalized limit.  Pointwise, after the
nonzero denominators have been discharged, the identity is

`N / K^k = (N / Δ^k) * (Δ / K)^k`. -/
theorem proposition31_order_div_cap_pow_tendsto_one_from_proposition_3_1
    (k : ℕ) (hk : 0 < k) :
    Tendsto
      (fun q : PrimePowerIndex ↦
        (proposition31PrimePowerOrder k q : ℝ) /
          (proposition31DegreeCap q.1 k : ℝ) ^ k)
      atTop (nhds 1) := by
  have hP31 := proposition_3_1 k hk
  have hdegree := hP31.2.1
  have horder := hP31.2.2
  have hproduct :
      Tendsto
        (fun q : PrimePowerIndex ↦
          (proposition31PrimePowerOrder k q : ℝ) /
              (proposition31PrimePowerDegree k q : ℝ) ^ k *
            ((proposition31PrimePowerDegree k q : ℝ) /
              (proposition31DegreeCap q.1 k : ℝ)) ^ k)
        atTop (nhds 1) := by
    simpa only [one_pow, one_mul] using horder.mul (hdegree.pow k)
  have hdegreePos : ∀ᶠ q : PrimePowerIndex in atTop,
      0 < (proposition31PrimePowerDegree k q : ℝ) /
        (proposition31DegreeCap q.1 k : ℝ) :=
    hdegree.eventually (Ioi_mem_nhds zero_lt_one)
  refine hproduct.congr' ?_
  filter_upwards [hdegreePos] with q hratioPos
  have hcap : (proposition31DegreeCap q.1 k : ℝ) ≠ 0 := by
    intro hzero
    rw [hzero, div_zero] at hratioPos
    exact (lt_irrefl 0) hratioPos
  have hdegreeNe : (proposition31PrimePowerDegree k q : ℝ) ≠ 0 := by
    intro hzero
    rw [hzero, zero_div] at hratioPos
    exact (lt_irrefl 0) hratioPos
  rw [div_pow]
  field_simp [hcap, hdegreeNe]

end DegreeDiameter

end PortProposition31Full

namespace DegreeDiameter

open SimpleGraph

private lemma moore_shared_edge_edist {V : Type*} {G : SimpleGraph V} {a b : V}
    (e : G.edgeSet) (ha : a ∈ e.val) (hb : b ∈ e.val) : G.edist a b ≤ 1 := by
  by_cases hab : a = b
  · subst b
    simp
  · have he := (Sym2.mem_and_mem_iff hab).mp ⟨ha, hb⟩
    have hadj : G.Adj a b := by simpa [he] using e.property
    exact (edist_eq_one_iff_adj.mpr hadj).le

private lemma moore_walk_to_endpoint {V : Type*} {G : SimpleGraph V} {e f : G.edgeSet}
    (p : G.lineGraph.Walk e f) (a : V) (ha : a ∈ e.val) :
    ∃ b ∈ f.val, G.edist a b ≤ (p.length : ℕ∞) := by
  induction p generalizing a with
  | nil => exact ⟨a, ha, by simp⟩
  | @cons e e' f he p ih =>
      obtain ⟨c, hce, hce'⟩ := (lineGraph_adj_iff_exists.mp he).2
      obtain ⟨b, hbf, hcb⟩ := ih c hce'
      refine ⟨b, hbf, (G.edist_triangle (v := c)).trans ?_⟩
      simpa [Walk.length_cons, add_comm] using
        add_le_add (moore_shared_edge_edist e ha hce) hcb

private lemma moore_line_edist_of_shared {V : Type*} {G : SimpleGraph V}
    (e f : G.edgeSet) {x : V} (he : x ∈ e.val) (hf : x ∈ f.val) :
    G.lineGraph.edist e f ≤ 1 := by
  by_cases h : e = f
  · subst f
    simp
  · exact (edist_eq_one_iff_adj.mpr
      (lineGraph_adj_iff_exists.mpr ⟨h, x, he, hf⟩)).le

private lemma moore_line_edist_of_walk {V : Type*} {G : SimpleGraph V} {a b : V}
    (p : G.Walk a b) (e f : G.edgeSet) (ha : a ∈ e.val) (hb : b ∈ f.val) :
    G.lineGraph.edist e f ≤ ((p.length + 1 : ℕ) : ℕ∞) := by
  induction p generalizing e with
  | nil => simpa using moore_line_edist_of_shared e f ha hb
  | @cons x y z hxy p ih =>
      let e' : G.edgeSet := ⟨s(x, y), hxy⟩
      have hx : x ∈ e'.val := Sym2.mem_iff.mpr (Or.inl rfl)
      have hy : y ∈ e'.val := Sym2.mem_iff.mpr (Or.inr rfl)
      refine (G.lineGraph.edist_triangle (v := e')).trans ?_
      simpa [Walk.length_cons, add_comm, add_left_comm] using
        add_le_add (moore_line_edist_of_shared e e' ha hx) (ih e' hy hb)

private lemma moore_line_ediam_of_no_far {V : Type*} {G : SimpleGraph V} {t : ℕ}
    (h : ¬ Erdos934.HasFarEdges G t) : G.lineGraph.ediam ≤ (t : ℕ∞) := by
  apply ediam_le_iff.mpr
  rintro ⟨⟨u, v⟩, huv⟩ ⟨⟨w, x⟩, hwx⟩
  have hnear : ∃ a ∈ ({u, v} : Set V), ∃ b ∈ ({w, x} : Set V),
      G.edist a b < (t : ℕ∞) := by
    by_contra! hn
    exact h ⟨u, v, w, x, huv, hwx, hn⟩
  obtain ⟨a, ha, b, hb, hab⟩ := hnear
  have hreach := reachable_of_edist_ne_top (hab.trans_le le_top).ne
  obtain ⟨p, hp⟩ := hreach.exists_walk_length_eq_edist
  refine (moore_line_edist_of_walk p _ _ ?_ ?_).trans ?_
  · simpa only [Sym2.mem_iff, Set.mem_insert_iff, Set.mem_singleton_iff] using ha
  · simpa only [Sym2.mem_iff, Set.mem_insert_iff, Set.mem_singleton_iff] using hb
  · rw [← hp] at hab
    have hlen : p.length < t := by exact_mod_cast hab
    exact_mod_cast hlen

private lemma moore_no_far_of_line_ediam {V : Type*} {G : SimpleGraph V} {t : ℕ}
    (ht : 0 < t) (h : G.lineGraph.ediam ≤ (t : ℕ∞)) : ¬ Erdos934.HasFarEdges G t := by
  rintro ⟨u, v, w, x, huv, hwx, hfar⟩
  let e : G.edgeSet := ⟨s(u, v), huv⟩
  let f : G.edgeSet := ⟨s(w, x), hwx⟩
  have hle := ediam_le_iff.mp h e f
  have hreach := reachable_of_edist_ne_top (hle.trans_lt (ENat.natCast_lt_top t)).ne
  obtain ⟨p, hp⟩ := hreach.exists_walk_length_eq_edist
  have hlen : p.length ≤ t := by exact_mod_cast hp.trans_le hle
  have hfar' (e f : G.edgeSet) (he : e.val = s(u, v)) (hf : f.val = s(w, x))
      (a b : V) (ha : a ∈ e.val) (hb : b ∈ f.val) : (t : ℕ∞) ≤ G.edist a b := by
    refine hfar a ?_ b ?_
    · simpa only [he, Sym2.mem_iff, Set.mem_insert_iff, Set.mem_singleton_iff] using ha
    · simpa only [hf, Sym2.mem_iff, Set.mem_insert_iff, Set.mem_singleton_iff] using hb
  have hclose (e f : G.edgeSet) (p : G.lineGraph.Walk e f) (hl : p.length ≤ t) :
      ∃ a ∈ e.val, ∃ b ∈ f.val, G.edist a b < (t : ℕ∞) := by
    cases p with
    | nil =>
        obtain ⟨⟨a, b⟩, he⟩ := e
        have ha : a ∈ s(a, b) := Sym2.mem_iff.mpr (Or.inl rfl)
        refine ⟨a, ha, a, ha, ?_⟩
        simpa using ht
    | @cons e e' f he p =>
        obtain ⟨a, hae, hae'⟩ := (lineGraph_adj_iff_exists.mp he).2
        obtain ⟨b, hbf, hd⟩ := moore_walk_to_endpoint p a hae'
        have hlen' : p.length < t := Nat.lt_of_succ_le hl
        exact ⟨a, hae, b, hbf, hd.trans_lt (by exact_mod_cast hlen')⟩
  obtain ⟨a, ha, b, hb, hab⟩ := hclose e f p hlen
  exact hab.not_ge (hfar' e f rfl rfl a b ha hb)

private lemma moore_threshold_nonempty (t d : ℕ) :
    Set.Nonempty {m : ℕ | ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      (∀ v, (G.neighborSet v).ncard ≤ d) → m ≤ G.edgeSet.ncard → Erdos934.HasFarEdges G t} := by
  refine ⟨(2 * d + 1) ^ t + 1, ?_⟩
  intro n G hd hm
  by_contra hn
  have hadm : EdgeAdmissible t d G.edgeSet.ncard :=
    ⟨Fin n, G, inferInstance, rfl, hd, moore_line_ediam_of_no_far hn⟩
  have hbound := edgeAdmissible_le_coarseBound hadm
  omega

private lemma moore_le_formal_h {t d m : ℕ} (ht : 0 < t) (hm : EdgeAdmissible t d m) :
    m ≤ Erdos934.h t d := by
  classical
  obtain ⟨V, G, hV, he, hd, hl⟩ := hm
  letI : Fintype V := Fintype.ofFinite V
  let f := (Fintype.equivFin V).symm
  let H := G.comap f
  let i : H ≃g G := SimpleGraph.Iso.comap f G
  have hdeg (x : Fin (Fintype.card V)) : (H.neighborSet x).ncard ≤ d := by
    rw [← H.coe_neighborFinset, Set.ncard_coe_finset, H.card_neighborFinset_eq_degree,
      ← i.degree_eq, ← G.card_neighborFinset_eq_degree, ← Set.ncard_coe_finset,
      G.coe_neighborFinset]
    exact hd (i x)
  have hE : H.edgeSet.ncard = m := by
    rw [← he, ← H.coe_edgeFinset, ← G.coe_edgeFinset, Set.ncard_coe_finset,
      Set.ncard_coe_finset, i.card_edgeFinset_eq]
  have hdiam : H.lineGraph.ediam ≤ (t : ℕ∞) := by
    apply ediam_le_iff.mpr
    intro a b
    let j := i.lineGraph
    have hdist := ediam_le_iff.mp hl (j a) (j b)
    have hreach := reachable_of_edist_ne_top (hdist.trans_lt (ENat.natCast_lt_top t)).ne
    obtain ⟨p, hp⟩ := hreach.exists_walk_length_eq_edist
    have hmap := H.lineGraph.edist_le (p.map j.symm.toHom)
    rw [Walk.length_map, hp] at hmap
    change H.lineGraph.edist (j.symm (j a)) (j.symm (j b)) ≤
      G.lineGraph.edist (j a) (j b) at hmap
    simpa only [RelIso.symm_apply_apply] using hmap.trans hdist
  have hh := Nat.sInf_mem (moore_threshold_nonempty t d)
  change ∀ n (J : SimpleGraph (Fin n)), (∀ v, (J.neighborSet v).ncard ≤ d) →
    Erdos934.h t d ≤ J.edgeSet.ncard → Erdos934.HasFarEdges J t at hh
  exact (lt_of_not_ge fun hg ↦
    moore_no_far_of_line_ediam ht hdiam (hh _ H hdeg (hE.symm ▸ hg))).le

end DegreeDiameter


namespace DegreeDiameter
open Filter Set
noncomputable section
private theorem proposition31_bipartiteExpansion_edgeAdmissible
    (q : PrimePowerIndex) (k : ℕ) (hk : 0 < k)
    {ell d : ℕ} (hkell : k + 1 = ell)
    (hcap : proposition31DegreeCap q.1 k + 1 ≤ d) :
    EdgeAdmissible ell d
      (proposition31PrimePowerOrder k q *
        (proposition31PrimePowerDegree k q + 1)) := by
  let G := Proposition31Graph (PrimePowerField q) k
  have hP31 := proposition_3_1 k hk
  have hp : Proposition31FiniteClaims q k := hP31.1 q
  have hregular : ∀ P,
      (G.neighborSet P).ncard = proposition31PrimePowerDegree k q := by
    intro P
    simpa only [G, Nat.card_coe_set_eq] using hp.regularity P
  have hdegreeCap :
      proposition31PrimePowerDegree k q ≤
        proposition31DegreeCap q.1 k := by
    exact hp.degree_le_cap
  have hdegree : MaxDegreeLE (bipartiteExpansion G) d :=
    maxDegreeLE_mono
      ((Nat.add_le_add_right hdegreeCap 1).trans hcap)
      (maxDegreeLE_bipartiteExpansion
        (fun P ↦ (hregular P).le))
  have hedges :
      (bipartiteExpansion G).edgeSet.ncard =
        proposition31PrimePowerOrder k q *
          (proposition31PrimePowerDegree k q + 1) := by
    simpa only [G] using
      ncard_edgeSet_bipartiteExpansion_of_regular G
        (proposition31PrimePowerDegree k q) hregular
  have hdiamG : G.ediam ≤ (k : ℕ∞) := by
    simpa only [G] using hp.ediam_eq.le
  have hline :
      (bipartiteExpansion G).lineGraph.ediam ≤ (ell : ℕ∞) := by
    simpa only [hkell] using lemma_4_1_le G k hdiamG
  exact ⟨_, bipartiteExpansion G, inferInstance, hedges, hdegree, hline⟩

/-- Specialize the finite construction to its own degree cap plus one. -/
theorem cap_edge_lower {k : ℕ} (hk : 0 < k) (q : PrimePowerIndex) :
    proposition31PrimePowerOrder k q * (proposition31PrimePowerDegree k q + 1) ≤
      Erdos934.h (k+1) (proposition31DegreeCap q.val k + 1) :=
  moore_le_formal_h (by omega) (proposition31_bipartiteExpansion_edgeAdmissible q k hk rfl le_rfl)

theorem cap_unbounded {k : ℕ} (hk : 0 < k) :
    Tendsto (fun q : PrimePowerIndex => proposition31DegreeCap q.val k) atTop atTop :=
  proposition31_cap_tendsto_atTop hk

end
end DegreeDiameter

/-! The natural degree caps already furnish arbitrarily large degrees.
At those degrees it suffices to keep the order and degree ratios above 0.9. -/
namespace OMA.Caps934
open DegreeDiameter Filter Set
open scoped Topology

private theorem cap_estimate (k : ℕ) (hk : 0<k) :
    ∃ᶠ d : ℕ in atTop, ((629:ℝ)/1000)^(k+1)*(d:ℝ)^(k+1) ≤ (Erdos934.h (k+1) d : ℝ) := by
  have : Nonempty PrimePowerIndex := ⟨⟨2,Nat.prime_two.isPrimePow⟩⟩
  have ho := proposition31_order_div_cap_pow_tendsto_one_from_proposition_3_1 k hk
  have hD := proposition31_degree_div_cap_tendsto_one k hk
  have high := cap_unbounded hk
  rw [frequently_atTop]
  intro B
  obtain ⟨q,hN,hΔ,hB⟩ := ((ho.eventually (lt_mem_nhds (show (0.9:ℝ)<1 by norm_num))).and
    ((hD.eventually (lt_mem_nhds (show (0.9:ℝ)<1 by norm_num))).and
      (high.eventually (eventually_ge_atTop (max 10 B))))).exists
  let C := proposition31DegreeCap q.val k
  let D := proposition31PrimePowerDegree k q
  let V := proposition31PrimePowerOrder k q
  change 0.9 < (V:ℝ)/(C:ℝ)^k at hN
  change 0.9 < (D:ℝ)/(C:ℝ) at hΔ
  change max 10 B ≤ C at hB
  have cg : (10:ℝ) ≤ C := by exact_mod_cast (le_max_left 10 B).trans hB
  have cp : 0 < (C:ℝ) := by linarith
  have h1 := (lt_div_iff₀ (pow_pos cp k)).mp hN
  have h2 := (lt_div_iff₀ cp).mp hΔ
  refine ⟨C+1,by omega,?_⟩
  have hsmall : (629:ℝ)/1000*((C:ℝ)+1) ≤ 0.75*C := by linarith
  have hp : (0.75:ℝ)^(k+1) ≤ 0.75 := by
    rw [pow_succ]
    exact mul_le_of_le_one_left (by norm_num) (pow_le_one₀ (by norm_num) (by norm_num))
  have hedge : (V:ℝ)*((D:ℝ)+1) ≤ Erdos934.h (k+1) (C+1) := by
    exact_mod_cast cap_edge_lower hk q
  push_cast
  calc
    _ = ((629:ℝ)/1000*((C:ℝ)+1))^(k+1) := (mul_pow ..).symm
    _ ≤ (0.75*(C:ℝ))^(k+1) := pow_le_pow_left₀ (by positivity) hsmall _
    _ = (0.75:ℝ)^(k+1)*(C:ℝ)^(k+1) := mul_pow ..
    _ ≤ 0.75*(C:ℝ)^(k+1) := mul_le_mul_of_nonneg_right hp (by positivity)
    _ ≤ (0.9*(C:ℝ)^k)*(0.9*C) := by
      rw [pow_succ]; nlinarith [mul_nonneg (pow_nonneg cp.le k) cp.le]
    _ ≤ (V:ℝ)*((D:ℝ)+1) := mul_le_mul h1.le (by linarith) (by positivity) (by positivity)
    _ ≤ _ := hedge

theorem bound : type_of% @Erdos934.erdos_934.variants.lower_large_t := by
  refine ⟨2,fun t ht => ?_⟩
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show t ≠ 0 by omega)
  exact cap_estimate k (by omega)

end OMA.Caps934

theorem OMA.solution : type_of% @Erdos934.erdos_934.variants.lower_large_t := OMA.Caps934.bound

/-
                                 Apache License
                           Version 2.0, January 2004
                        http://www.apache.org/licenses/

   TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION

   1. Definitions.

      “License” shall mean the terms and conditions for use, reproduction,
      and distribution as defined by Sections 1 through 9 of this document.

      “Licensor” shall mean the copyright owner or entity authorized by
      the copyright owner that is granting the License.

      “Legal Entity” shall mean the union of the acting entity and all
      other entities that control, are controlled by, or are under common
      control with that entity. For the purposes of this definition,
      “control” means (i) the power, direct or indirect, to cause the
      direction or management of such entity, whether by contract or
      otherwise, or (ii) ownership of fifty percent (50%) or more of the
      outstanding shares, or (iii) beneficial ownership of such entity.

      “You” (or “Your”) shall mean an individual or Legal Entity
      exercising permissions granted by this License.

      “Source” form shall mean the preferred form for making modifications,
      including but not limited to software source code, documentation
      source, and configuration files.

      “Object” form shall mean any form resulting from mechanical
      transformation or translation of a Source form, including but
      not limited to compiled object code, generated documentation,
      and conversions to other media types.

      “Work” shall mean the work of authorship, whether in Source or
      Object form, made available under the License, as indicated by a
      copyright notice that is included in or attached to the work
      (an example is provided in the Appendix below).

      “Derivative Works” shall mean any work, whether in Source or Object
      form, that is based on (or derived from) the Work and for which the
      editorial revisions, annotations, elaborations, or other modifications
      represent, as a whole, an original work of authorship. For the purposes
      of this License, Derivative Works shall not include works that remain
      separable from, or merely link (or bind by name) to the interfaces of,
      the Work and Derivative Works thereof.

      “Contribution” shall mean any work of authorship, including
      the original version of the Work and any modifications or additions
      to that Work or Derivative Works thereof, that is intentionally
      submitted to Licensor for inclusion in the Work by the copyright owner
      or by an individual or Legal Entity authorized to submit on behalf of
      the copyright owner. For the purposes of this definition, “submitted”
      means any form of electronic, verbal, or written communication sent
      to the Licensor or its representatives, including but not limited to
      communication on electronic mailing lists, source code control systems,
      and issue tracking systems that are managed by, or on behalf of, the
      Licensor for the purpose of discussing and improving the Work, but
      excluding communication that is conspicuously marked or otherwise
      designated in writing by the copyright owner as “Not a Contribution.”

      “Contributor” shall mean Licensor and any individual or Legal Entity
      on behalf of whom a Contribution has been received by Licensor and
      subsequently incorporated within the Work.

   2. Grant of Copyright License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      copyright license to reproduce, prepare Derivative Works of,
      publicly display, publicly perform, sublicense, and distribute the
      Work and such Derivative Works in Source or Object form.

   3. Grant of Patent License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      (except as stated in this section) patent license to make, have made,
      use, offer to sell, sell, import, and otherwise transfer the Work,
      where such license applies only to those patent claims licensable
      by such Contributor that are necessarily infringed by their
      Contribution(s) alone or by combination of their Contribution(s)
      with the Work to which such Contribution(s) was submitted. If You
      institute patent litigation against any entity (including a
      cross-claim or counterclaim in a lawsuit) alleging that the Work
      or a Contribution incorporated within the Work constitutes direct
      or contributory patent infringement, then any patent licenses
      granted to You under this License for that Work shall terminate
      as of the date such litigation is filed.

   4. Redistribution. You may reproduce and distribute copies of the
      Work or Derivative Works thereof in any medium, with or without
      modifications, and in Source or Object form, provided that You
      meet the following conditions:

      (a) You must give any other recipients of the Work or
          Derivative Works a copy of this License; and

      (b) You must cause any modified files to carry prominent notices
          stating that You changed the files; and

      (c) You must retain, in the Source form of any Derivative Works
          that You distribute, all copyright, patent, trademark, and
          attribution notices from the Source form of the Work,
          excluding those notices that do not pertain to any part of
          the Derivative Works; and

      (d) If the Work includes a “NOTICE” text file as part of its
          distribution, then any Derivative Works that You distribute must
          include a readable copy of the attribution notices contained
          within such NOTICE file, excluding those notices that do not
          pertain to any part of the Derivative Works, in at least one
          of the following places: within a NOTICE text file distributed
          as part of the Derivative Works; within the Source form or
          documentation, if provided along with the Derivative Works; or,
          within a display generated by the Derivative Works, if and
          wherever such third-party notices normally appear. The contents
          of the NOTICE file are for informational purposes only and
          do not modify the License. You may add Your own attribution
          notices within Derivative Works that You distribute, alongside
          or as an addendum to the NOTICE text from the Work, provided
          that such additional attribution notices cannot be construed
          as modifying the License.

      You may add Your own copyright statement to Your modifications and
      may provide additional or different license terms and conditions
      for use, reproduction, or distribution of Your modifications, or
      for any such Derivative Works as a whole, provided Your use,
      reproduction, and distribution of the Work otherwise complies with
      the conditions stated in this License.

   5. Submission of Contributions. Unless You explicitly state otherwise,
      any Contribution intentionally submitted for inclusion in the Work
      by You to the Licensor shall be under the terms and conditions of
      this License, without any additional terms or conditions.
      Notwithstanding the above, nothing herein shall supersede or modify
      the terms of any separate license agreement you may have executed
      with Licensor regarding such Contributions.

   6. Trademarks. This License does not grant permission to use the trade
      names, trademarks, service marks, or product names of the Licensor,
      except as required for reasonable and customary use in describing the
      origin of the Work and reproducing the content of the NOTICE file.

   7. Disclaimer of Warranty. Unless required by applicable law or
      agreed to in writing, Licensor provides the Work (and each
      Contributor provides its Contributions) on an “AS IS” BASIS,
      WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
      implied, including, without limitation, any warranties or conditions
      of TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
      PARTICULAR PURPOSE. You are solely responsible for determining the
      appropriateness of using or redistributing the Work and assume any
      risks associated with Your exercise of permissions under this License.

   8. Limitation of Liability. In no event and under no legal theory,
      whether in tort (including negligence), contract, or otherwise,
      unless required by applicable law (such as deliberate and grossly
      negligent acts) or agreed to in writing, shall any Contributor be
      liable to You for damages, including any direct, indirect, special,
      incidental, or consequential damages of any character arising as a
      result of this License or out of the use or inability to use the
      Work (including but not limited to damages for loss of goodwill,
      work stoppage, computer failure or malfunction, or any and all
      other commercial damages or losses), even if such Contributor
      has been advised of the possibility of such damages.

   9. Accepting Warranty or Additional Liability. While redistributing
      the Work or Derivative Works thereof, You may choose to offer,
      and charge a fee for, acceptance of support, warranty, indemnity,
      or other liability obligations and/or rights consistent with this
      License. However, in accepting such obligations, You may act only
      on Your own behalf and on Your sole responsibility, not on behalf
      of any other Contributor, and only if You agree to indemnify,
      defend, and hold each Contributor harmless for any liability
      incurred by, or claims asserted against, such Contributor by reason
      of your accepting any such warranty or additional liability.

   END OF TERMS AND CONDITIONS

   APPENDIX: How to apply the Apache License to your work.

      To apply the Apache License to your work, attach the following
      boilerplate notice, with the fields enclosed by brackets “[]”
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same “printed page” as the copyright notice for easier
      identification within third-party archives.

   Copyright [yyyy] [name of copyright owner]

   Licensed under the Apache License, Version 2.0 (the “License”);
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an “AS IS” BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

-/
