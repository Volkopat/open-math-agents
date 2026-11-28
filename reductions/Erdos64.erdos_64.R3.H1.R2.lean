import OMAReductions.R_Erdos64_erdos_64_R3
import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Set.Card
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.IntervalCases

/-!
# Cycles through edges of a smallest biconnected counterexample to Erdős 64

This reduces H1 of project PR #2088. In a vertex-minimal counterexample within
the biconnected class, every edge whose endpoints do not separate the graph
lies on a cycle of length 2^k+1 with k ≥ 1. Such edges span a biconnected
subgraph with at least n+2 edges on n vertices. If an edge lies on no such
cycle, its endpoints form a separating pair.

Ducoffe and Dumitru, arXiv:2609.28594, Lemma 2.1, prove the all-edge statement
for counterexamples minimal among all graphs. Within a block, contracting an
adjacent separating pair can create a cut vertex. We keep track of this
condition under the quotient and delete edges of separating pairs to obtain
a biconnected spanning subgraph. The cycle lifting theorem applies at every
length, even for infinite input graphs. A bipartite block admits a smaller
block whose even cycle lengths all occur in the input, with one endpoint of
the contracted edge prescribed and another vertex excluded.

The spanning theorem for contractible edges is the finite graph theorem
recorded in Tsz Lung Chan, Electronic Journal of Combinatorics 22(2), 2015,
P2.47, Theorem 1. The cut proof below also covers the degenerate cases of
the parent cut predicate.

A descent inside regions attached along an adjacent pair finds a nonempty
subregion with every incident edge nonseparating. Minimum degree three gives
an internal edge. Repeating away from its endpoints yields four distinct
vertices with all incident edges nonseparating. Degree-sum gives the bound
n+2, attained for contractible edges in the complete graph on four vertices.

An uncovered edge yields two disjoint such regions. Absence of a square forces
at least seven vertices per region. Hence at least fourteen vertices have
degree at least three in the covered spanning graph, giving at least n+7 edges.

Retaining any union of components together with both adjacent terminals
preserves biconnectivity. Each proper nonempty side is connected
and, at an uncovered edge, each terminal has a unique neighbor there.
Every uncovered edge joins cubic vertices, and uncovered edges form a matching.
Two copies of a side of size m glued along both terminals have 2m+2 vertices. When this
is strictly less than n, minimality forces two terminal paths in that side
whose lengths sum to a power of two. Gluing along any disjoint side proves
that both lengths are exclusive to the first side. On every proper side, suppressing both
terminals produces a smaller block.
Deleting the virtual edge from its dyadic cycle and restoring the two
terminal edges gives a path in that side of length one more than a power of two.

For a proper side C, remove the unique attachment x of the first terminal and
the unique attachment y of the second. Each remaining component R meets both
ports. If at least three distinct vertices meet x or y, identifying the ports
on R yields a smaller block of minimum degree three. A dyadic cycle in this
block opens into an x-y path of the same length, yielding a terminal path of
length 2^k+2. If only two vertices meet the ports, either they are adjacent
and give a terminal path of length five, or a virtual edge between them
forces a terminal path of length 2^k+3 with k ≥ 3 and 2^k ≤ |R|.

Opposite terminal lengths six and ten therefore force every component of the
first kind to contain at least fifteen vertices. Opposite lengths five and
eleven force every component of the second kind to contain at least sixteen.
If the side has no dyadic-plus-two path, one attachment has neighbors in two
different components; the smaller component bounds the odd exponent by
2·2^k+2 ≤ |C|. In a bipartite induced side, trimming the first and last
edges shows that all proper terminal paths have the same parity. The forced
odd path rules out the even alternative. Removing x and y then disconnects C,
and opposite lengths five and eleven imply |C| ≥ 34. These restrictions hold
regardless of the order of the block.

The duplication of a region at a single cut vertex in Ducoffe--Dumitru,
Theorem 2.3, does not create cycles crossing the two copies. With two shared
terminals, such crossing cycles yield the path lengths used here.

Related Lean work includes the marked path decomposition in PR #2529, the
bipartite contraction in PR #31338, and the high-degree edge deletion in
PR #21911. PR #32185 duplicates a terminal piece to force both path parities.
PR #31004 treats degree-two terminals in cubic networks. The two remaining hypotheses are open cases of the block problem.
-/

namespace OMA.R_Erdos64_erdos_64_R3_H1_R2

open SimpleGraph
open scoped Classical

private theorem closeSame {V : Type*} {G : SimpleGraph V} {s u v : V}
    (p : G.Walk u v) (hp : p.IsPath) (hs : s ∉ p.support)
    (hu : G.Adj s u) (hv : G.Adj v s) (positive : 0 < p.length) :
    ∃ c : G.Walk s s, c.IsCycle ∧ c.length = p.length + 2 := by
  refine ⟨.cons hu (p.concat hv), ?_, by simp [Nat.add_assoc]⟩
  apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
  constructor
  · rw [Walk.tail_cons]
    exact (Walk.isPath_copy _ _ _).mpr (hp.concat hs hv)
  · simp only [Walk.length_cons, Walk.length_concat]
    omega

private theorem closeAcross {V : Type*} {G : SimpleGraph V} {s t u v : V}
    (p : G.Walk u v) (hp : p.IsPath) (hs : s ∉ p.support) (ht : t ∉ p.support)
    (hu : G.Adj s u) (hv : G.Adj v t) (hts : G.Adj t s) :
    ∃ c : G.Walk t t, c.IsCycle ∧ c.length = p.length + 3 ∧ s(t,s) ∈ c.edges := by
  refine ⟨.cons hts (.cons hu (p.concat hv)), ?_, by simp [Nat.add_assoc], by simp⟩
  apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
  constructor
  · have h : s ∉ (p.concat hv).support := by simp [hs, hts.ne.symm]
    rw [Walk.tail_cons]
    exact (Walk.isPath_copy _ _ _).mpr ((hp.concat ht hv).cons h (h := hu))
  · simp only [Walk.length_cons, Walk.length_concat]
    omega

/-- A single merged vertex can lengthen a simple cycle by exactly one edge.
The conclusion is valid at every cycle length and on infinite graphs. -/
theorem liftMergedCycle {V W : Type*} (G : SimpleGraph V) (K : SimpleGraph W)
    (f : W ↪ V) (z : W) {a : V} (link : G.Adj a (f z)) (miss : ∀ t, f t ≠ a)
    (interior : ∀ u v, u ≠ z → v ≠ z → K.Adj u v → G.Adj (f u) (f v))
    (star : ∀ u, K.Adj z u → G.Adj a (f u) ∨ G.Adj (f z) (f u))
    {w : W} (c : K.Walk w w) (hc : c.IsCycle) :
    ∃ v, ∃ d : G.Walk v v, d.IsCycle ∧
      (d.length = c.length ∨ (d.length = c.length + 1 ∧ s(a,f z) ∈ d.edges)) := by
  classical
  let F := G.comap f
  let hom : F →g G := ⟨f, fun h => h⟩
  have edges {u v : W} (p : K.Walk u v) (away : z ∉ p.support) :
      ∀ e ∈ p.edges, e ∈ F.edgeSet := by
    rintro ⟨i,j⟩ he
    exact interior i j (fun h => away (h ▸ p.fst_mem_support_of_mem_edges he))
      (fun h => away (h ▸ p.snd_mem_support_of_mem_edges he)) (p.edges_subset_edgeSet he)
  by_cases hz : z ∈ c.support
  · let rot := c.rotate z hz
    have rc : rot.IsCycle := hc.rotate hz
    have rl : rot.length = c.length := c.length_rotate _ _
    clear_value rot
    cases rot with
    | nil => exact (rc.not_nil .nil).elim
    | @cons _ u _ zu tail =>
      have tp : tail.IsPath := ((Walk.cons_isCycle_iff ..).mp rc).1
      have nz : ¬ tail.Nil := fun h => zu.ne.symm h.eq
      have vz := tail.adj_penultimate nz
      let p := tail.dropLast
      have eq : p.concat vz = tail := Walk.concat_dropLast vz
      obtain ⟨pp,away⟩ := (Walk.concat_isPath_iff vz).mp (eq ▸ tp)
      let q := (p.transfer F (edges p away)).map hom
      have qp : q.IsPath := (pp.transfer (edges p away)).map f.injective
      have qs : q.support = p.support.map f := by
        rw [show q.support = _ from Walk.support_map hom _, Walk.support_transfer]
        rfl
      have qa : a ∉ q.support := by
        rw [qs]
        rintro h
        obtain ⟨i,_,e⟩ := List.mem_map.mp h
        exact miss i e
      have qb : f z ∉ q.support := by
        rw [qs]
        rintro h
        obtain ⟨i,hi,e⟩ := List.mem_map.mp h
        exact away (f.injective e ▸ hi)
      have ql : q.length = p.length := by simp [q]
      have len : q.length + 2 = c.length := by
        rw [Walk.length_cons, ← eq, Walk.length_concat] at rl
        omega
      have minlen := hc.three_le_length
      have pos : 0 < q.length := by omega
      rcases star u zu with au | bu <;> rcases star _ vz.symm with av | bv
      · obtain ⟨d,hd,hl⟩ := closeSame q qp qa au av.symm pos
        exact ⟨_,d,hd,Or.inl (hl.trans len)⟩
      · obtain ⟨d,hd,hl,he⟩ := closeAcross q qp qa qb au bv.symm link.symm
        exact ⟨_,d,hd,Or.inr ⟨by omega, (Sym2.eq_swap ..) ▸ he⟩⟩
      · obtain ⟨d,hd,hl,he⟩ := closeAcross q qp qb qa bu av.symm link
        exact ⟨_,d,hd,Or.inr ⟨by omega,he⟩⟩
      · obtain ⟨d,hd,hl⟩ := closeSame q qp qb bu bv.symm pos
        exact ⟨_,d,hd,Or.inl (hl.trans len)⟩
  · let d := (c.transfer F (edges c hz)).map hom
    exact ⟨_,d,(hc.transfer (edges c hz)).map f.injective, Or.inl (by simp [d])⟩

/-- Push the one-vertex and two-vertex cut conditions through a contraction.
The fibers away from the marked vertex are singletons. -/
private theorem blockAfterFold {V W : Type*} (G : SimpleGraph V)
    (π : V → W) (rep : W → V) (z : W) (a b : V)
    (rightInv : ∀ t, π (rep t) = t)
    (single : ∀ {v t}, π v = t → t ≠ z → v = rep t)
    (fiber : ∀ v, π v = z ↔ v = a ∨ v = b)
    (block : ∀ (t : V) (S : Set V), t ∈ S → (∃ x ∈ S, x ≠ t) → (∃ y, y ∉ S) →
      ∃ x ∈ S, x ≠ t ∧ ∃ y ∉ S, G.Adj x y)
    (pair : ∀ S : Set V, a ∈ S → b ∈ S → (∃ x ∈ S, x ≠ a ∧ x ≠ b) → (∃ y, y ∉ S) →
      ∃ x ∈ S, x ≠ a ∧ x ≠ b ∧ ∃ y ∉ S, G.Adj x y) :
    ∀ (t : W) (S : Set W), t ∈ S → (∃ x ∈ S, x ≠ t) → (∃ y, y ∉ S) →
      ∃ x ∈ S, x ≠ t ∧ ∃ y ∉ S, (G.map π).Adj x y := by
  rintro t S ht ⟨u,hu,hut⟩ ⟨v,hv⟩
  let T := π ⁻¹' S
  have mem (w : W) : rep w ∈ T ↔ w ∈ S := by simp [T, rightInv]
  have out : ∃ y, y ∉ T := ⟨rep v,fun h => hv ((mem v).1 h)⟩
  have liftEdge {i j : V} (hi : i ∈ T) (hj : j ∉ T) (e : G.Adj i j) :
      (G.map π).Adj (π i) (π j) :=
    map_adj_apply' e (fun h => hj (show π j ∈ S from h ▸ (show π i ∈ S from hi)))
  by_cases tz : t = z
  · subst t
    have off : π (rep u) ≠ z := by rwa [rightInv]
    have outside := mt (fiber _).2 off
    obtain ⟨i,hi,hia,hib,j,hj,e⟩ := pair T
      (show π a ∈ S from ((fiber a).2 (Or.inl rfl)) ▸ ht)
      (show π b ∈ S from ((fiber b).2 (Or.inr rfl)) ▸ ht)
      ⟨rep u,(mem u).2 hu,fun h => outside (.inl h),fun h => outside (.inr h)⟩ out
    exact ⟨π i,hi,fun h => ((fiber i).1 h).elim hia hib,π j,hj,liftEdge hi hj e⟩
  · have ne : rep u ≠ rep t := fun h => hut (by simpa only [rightInv] using congrArg π h)
    obtain ⟨i,hi,hit,j,hj,e⟩ := block (rep t) T ((mem t).2 ht) ⟨rep u,(mem u).2 hu,ne⟩ out
    exact ⟨π i,hi,fun h => hit (single h tz),π j,hj,liftEdge hi hj e⟩

/-- Contract a triangle-free edge whose endpoints do not separate the block.
Every cycle of the smaller block has an equal-length lift or a lift one edge
longer through the contracted edge. -/
theorem contractInBlock {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {a b : V} (ab : G.Adj a b) (floor : ∀ t, 3 ≤ G.degree t)
    (common : ∀ t, G.Adj a t → G.Adj b t → False)
    (block : ∀ (t : V) (S : Set V), t ∈ S → (∃ x ∈ S, x ≠ t) → (∃ y, y ∉ S) →
      ∃ x ∈ S, x ≠ t ∧ ∃ y ∉ S, G.Adj x y)
    (pair : ∀ S : Set V, a ∈ S → b ∈ S → (∃ x ∈ S, x ≠ a ∧ x ≠ b) → (∃ y, y ∉ S) →
      ∃ x ∈ S, x ≠ a ∧ x ≠ b ∧ ∃ y ∉ S, G.Adj x y) :
    let W := {t : V // t ≠ a}
    ∃ (K : SimpleGraph W) (z : W), z.val = b ∧
      K = G.map (fun v => if h : v = a then z else ⟨v,h⟩) ∧ Fintype.card W < Fintype.card V ∧
      (∀ t, 3 ≤ K.degree t) ∧ 4 ≤ K.degree z ∧
      (∀ (t : W) (S : Set W), t ∈ S → (∃ x ∈ S, x ≠ t) → (∃ y, y ∉ S) →
        ∃ x ∈ S, x ≠ t ∧ ∃ y ∉ S, K.Adj x y) ∧
      ∀ w (c : K.Walk w w), c.IsCycle → ∃ v, ∃ d : G.Walk v v, d.IsCycle ∧
        (d.length = c.length ∨ (d.length = c.length + 1 ∧ s(a,b) ∈ d.edges)) := by
  classical
  let W := {t : V // t ≠ a}
  let z : W := ⟨b,ab.ne.symm⟩
  let π (v : V) : W := if h : v = a then z else ⟨v,h⟩
  let K := G.map π
  let : DecidableRel K.Adj := fun _ _ => Classical.propDecidable _
  let f : W ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
  have re (t : W) : π (f t) = t := by simp [π,f,t.property]
  have fiber (v : V) : π v = z ↔ v = a ∨ v = b := by
    by_cases h : v = a
    · simp [π,h]
    · unfold π
      rw [dif_neg h, or_iff_right h]
      exact ⟨fun e => congrArg Subtype.val e, fun e => Subtype.ext e⟩
  have single {v : V} {t : W} (h : π v = t) (ht : t ≠ z) : v = f t := by
    have ne : v ≠ a := fun e => ht (h.symm.trans ((fiber v).2 (Or.inl e)))
    simpa [π,ne,f] using congrArg Subtype.val h
  have pBlock := blockAfterFold G π f z a b re (fun h ht => single h ht) fiber block pair
  have off (t : W) (ht : t ≠ z) : 3 ≤ K.degree t := by
    have maps : Set.MapsTo π (G.neighborFinset (f t)) (K.neighborFinset t) := by
      intro v hv
      have e := (G.mem_neighborFinset ..).1 hv
      apply (K.mem_neighborFinset ..).2
      rw [← re t]
      exact map_adj_apply' e (fun h => e.ne (single (h.symm.trans (re t)) ht).symm)
    have inj : (↑(G.neighborFinset (f t)) : Set V).InjOn π := by
      intro v hv w hw eq
      by_cases h : π w = z
      · have avoid (x y : V) (hx : G.Adj (f t) x) (hy : G.Adj (f t) y)
            (ex : x = a ∨ x = b) (ey : y = a ∨ y = b) : x = y := by
          rcases ex with rfl | rfl <;> rcases ey with rfl | rfl
          · rfl
          · exact (common _ hx.symm hy.symm).elim
          · exact (common _ hy.symm hx.symm).elim
          · rfl
        exact avoid v w ((G.mem_neighborFinset ..).1 hv) ((G.mem_neighborFinset ..).1 hw)
          ((fiber v).1 (eq.trans h)) ((fiber w).1 h)
      · exact (single eq h).trans (single rfl h).symm
    have count := Finset.card_le_card_of_injOn π maps inj
    simpa only [card_neighborFinset_eq_degree] using (floor (f t)).trans count
  let A := (G.neighborFinset a).erase b
  let B := (G.neighborFinset b).erase a
  have memA (v) (hv : v ∈ A) : v ≠ b ∧ G.Adj a v := by simpa [A] using hv
  have memB (v) (hv : v ∈ B) : v ≠ a ∧ G.Adj b v := by simpa [B] using hv
  have fresh (v) (hv : v ∈ A ∪ B) : π v ≠ z := by
    rcases Finset.mem_union.mp hv with h | h
    · exact fun e => ((fiber _).1 e).elim (memA v h).2.ne.symm (memA v h).1
    · exact fun e => ((fiber _).1 e).elim (memB v h).1 (memB v h).2.ne.symm
  have disj : Disjoint A B := Finset.disjoint_left.mpr fun v hv hw => common v (memA v hv).2 (memB v hw).2
  have maps : Set.MapsTo π (↑(A ∪ B) : Set V) (K.neighborFinset z) := by
    intro v hv
    apply (K.mem_neighborFinset ..).2
    have ne := (fresh v hv).symm
    rcases Finset.mem_union.mp hv with h | h
    · exact ⟨ne,a,v,(memA v h).2,(fiber a).2 (.inl rfl),rfl⟩
    · exact ⟨ne,b,v,(memB v h).2,(fiber b).2 (.inr rfl),rfl⟩
  have inj : (↑(A ∪ B) : Set V).InjOn π := fun _ _ w hw eq =>
    (single eq (fresh w hw)).trans (single rfl (fresh w hw)).symm
  have count := Finset.card_le_card_of_injOn π maps inj
  have ac : A.card = G.degree a - 1 := by
    rw [show A = _ from rfl,Finset.card_erase_of_mem ((G.mem_neighborFinset ..).2 ab),card_neighborFinset_eq_degree]
  have bc : B.card = G.degree b - 1 := by
    rw [show B = _ from rfl,Finset.card_erase_of_mem ((G.mem_neighborFinset ..).2 ab.symm),card_neighborFinset_eq_degree]
  rw [Finset.card_union_of_disjoint disj,ac,bc,card_neighborFinset_eq_degree] at count
  have root : 4 ≤ K.degree z := by have := floor a; have := floor b; omega
  refine ⟨K,z,rfl,rfl,Fintype.card_lt_of_injective_of_notMem f f.injective (b := a)
    (by rintro ⟨v,h⟩; exact v.property h),fun t => ?_,root,pBlock,?_⟩
  · by_cases h : t = z
    · exact h ▸ (by omega : 3 ≤ K.degree z)
    · exact off t h
  · intro w c hc
    apply liftMergedCycle G K f z ab (fun t => t.property) _ _ c hc
    · rintro u v hu hv ⟨_,x,y,e,hx,hy⟩
      simpa only [← single hx hu, ← single hy hv] using e
    · rintro u e
      obtain ⟨ne,x,y,xy,hx,hy⟩ := e
      rw [single hy ne.symm] at xy
      rcases (fiber x).1 hx with he | he
      · exact Or.inl (he ▸ xy)
      · exact Or.inr (show G.Adj b (f u) from he ▸ xy)

/-- A nonempty region attached to the rest only at two terminals must join
their sides in every cut that is constant along each edge touching the region. -/
private theorem bankJoins {V : Type*} (G : SimpleGraph V) {a b : V} (C : Set V)
    (nonempty : C.Nonempty) (ca : a ∉ C) (cb : b ∉ C)
    (closed : ∀ x ∈ C, ∀ y, G.Adj x y → y ∈ C ∨ y = a ∨ y = b)
    (block : ∀ (z : V) (S : Set V), z ∈ S → (∃ x ∈ S, x ≠ z) → (∃ y, y ∉ S) →
      ∃ x ∈ S, x ≠ z ∧ ∃ y ∉ S, G.Adj x y)
    (P : Set V) (same : ∀ x ∈ C, ∀ y, G.Adj x y → (x ∈ P ↔ y ∈ P)) :
    a ∈ P ↔ b ∈ P := by
  have cut (Q : Set V) (u v : V) (q₁ : u ∈ Q) (q₂ : v ∉ Q) (hv : v ∉ C)
      (stable : ∀ x ∈ C, ∀ y, G.Adj x y → (x ∈ Q ↔ y ∈ Q))
      (near : ∀ x ∈ C, ∀ y, G.Adj x y → y ∈ C ∨ y = u ∨ y = v) :
      ∀ x ∈ C, x ∈ Q → x = u := by
    intro x hx hq
    by_contra xu
    let S := {y : V | y = u ∨ y ∈ C ∧ y ∈ Q}
    have vout : v ∉ S := by rintro (h | h); exact q₂ (h ▸ q₁); exact hv h.1
    obtain ⟨i,hi,ine,j,hj,e⟩ := block u S (Or.inl rfl) ⟨x,Or.inr ⟨hx,hq⟩,xu⟩ ⟨v,vout⟩
    have icq : i ∈ C ∧ i ∈ Q := hi.resolve_left ine
    have jq := (stable i icq.1 j e).1 icq.2
    rcases near i icq.1 j e with jc | ju | jv
    · exact hj (Or.inr ⟨jc,jq⟩)
    · exact hj (Or.inl ju)
    · exact q₂ (jv ▸ jq)
  obtain ⟨w,hw⟩ := nonempty
  have near' (x) (hx : x ∈ C) (y) (e : G.Adj x y) : y ∈ C ∨ y = b ∨ y = a :=
    (closed x hx y e).imp_right Or.symm
  have opp (x) (hx : x ∈ C) (y) (e : G.Adj x y) : x ∈ Pᶜ ↔ y ∈ Pᶜ := (same x hx y e).not
  constructor
  · intro ha
    by_contra hb
    by_cases h : w ∈ P
    · exact ca (cut P a b ha hb cb same closed w hw h ▸ hw)
    · exact cb (cut Pᶜ b a hb (fun q => q ha) ca opp near' w hw h ▸ hw)
  · intro hb
    by_contra ha
    by_cases h : w ∈ P
    · exact cb (cut P b a hb ha ca same near' w hw h ▸ hw)
    · exact ca (cut Pᶜ a b ha (fun q => q hb) cb opp closed w hw h ▸ hw)

/-- If the endpoints of an edge separate a block, deleting the edge itself
retains the one-vertex cut property. Finiteness and degree bounds are unnecessary. -/
theorem deleteSeparatingEdge {V : Type*} (G : SimpleGraph V) {a b : V}
    (block : ∀ (t : V) (S : Set V), t ∈ S → (∃ x ∈ S, x ≠ t) → (∃ y, y ∉ S) →
      ∃ x ∈ S, x ≠ t ∧ ∃ y ∉ S, G.Adj x y)
    (split : ¬ ∀ S : Set V, a ∈ S → b ∈ S → (∃ x ∈ S, x ≠ a ∧ x ≠ b) → (∃ y, y ∉ S) →
      ∃ x ∈ S, x ≠ a ∧ x ≠ b ∧ ∃ y ∉ S, G.Adj x y) :
    ∀ (t : V) (S : Set V), t ∈ S → (∃ x ∈ S, x ≠ t) → (∃ y, y ∉ S) →
      ∃ x ∈ S, x ≠ t ∧ ∃ y ∉ S, (G.deleteEdges {s(a,b)}).Adj x y := by
  classical
  push Not at split
  obtain ⟨T,ta,tb,⟨i,hi,ia,ib⟩,⟨j,hj⟩,gap⟩ := split
  intro z S hz inside outside
  by_contra! noCross
  obtain ⟨x,hx,hxz,y,hy,e⟩ := block z S hz inside outside
  have marked : s(x,y) = s(a,b) := by
    by_contra ne
    exact noCross x hx hxz y hy (deleteEdges_adj.mpr ⟨e,by simpa using ne⟩)
  have ends : a ≠ z ∧ b ≠ z ∧ ¬ (a ∈ S ↔ b ∈ S) := by
    have hyz : y ≠ z := fun h => hy (h ▸ hz)
    rw [Sym2.eq,Sym2.rel_iff'] at marked
    rcases marked with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact ⟨hxz,hyz,fun eq => hy (eq.mp hx)⟩
    · exact ⟨hyz,hxz,fun eq => hy (eq.mpr hx)⟩
  have bank : ∃ C : Set V, C.Nonempty ∧ a ∉ C ∧ b ∉ C ∧ z ∉ C ∧
      ∀ x ∈ C, ∀ y, G.Adj x y → y ∈ C ∨ y = a ∨ y = b := by
    by_cases zT : z ∈ T
    · refine ⟨Tᶜ,⟨j,hj⟩,fun h => h ta,fun h => h tb,fun h => h zT,?_⟩
      intro u hu v edge
      by_contra! bad
      exact gap v (by simpa using bad.1) bad.2.1 bad.2.2 u hu edge.symm
    · let C := {v : V | v ∈ T ∧ v ≠ a ∧ v ≠ b}
      refine ⟨C,⟨i,hi,ia,ib⟩,fun h => h.2.1 rfl,fun h => h.2.2 rfl,fun h => zT h.1,?_⟩
      intro u hu v edge
      by_contra! bad
      have vt : v ∉ T := fun h => bad.1 ⟨h,bad.2.1,bad.2.2⟩
      exact gap u hu.1 hu.2.1 hu.2.2 v vt edge
  obtain ⟨C,hC,ca,cb,cz,near⟩ := bank
  apply ends.2.2
  apply bankJoins G C hC ca cb near block S
  intro u hu v uv
  have uz : u ≠ z := fun h => cz (h ▸ hu)
  have vz : v ≠ z := by
    rcases near u hu v uv with h | h | h
    · exact fun eq => cz (eq ▸ h)
    · exact h ▸ ends.1
    · exact h ▸ ends.2.1
  have kept : (G.deleteEdges {s(a,b)}).Adj u v := by
    apply deleteEdges_adj.mpr
    refine ⟨uv,?_⟩
    simp only [Set.mem_singleton_iff,Sym2.eq,Sym2.rel_iff',Prod.mk.injEq,Prod.swap_prod_mk]
    rintro (⟨h,_⟩ | ⟨h,_⟩)
    · exact ca (h ▸ hu)
    · exact cb (h ▸ hu)
  constructor
  · intro h
    by_contra hv
    exact noCross u h uz v hv kept
  · intro h
    by_contra hu'
    exact noCross v h vz u hu' kept.symm

/-- Every finite block has a spanning block using only edges whose endpoints
can be deleted together without disconnecting the original graph. -/
theorem spanningNonseparatingEdges {V : Type*} [Fintype V] (G : SimpleGraph V)
    (block : ∀ (t : V) (S : Set V), t ∈ S → (∃ x ∈ S, x ≠ t) → (∃ y, y ∉ S) →
      ∃ x ∈ S, x ≠ t ∧ ∃ y ∉ S, G.Adj x y) :
    ∃ H : SimpleGraph V, H ≤ G ∧
      (∀ (t : V) (S : Set V), t ∈ S → (∃ x ∈ S, x ≠ t) → (∃ y, y ∉ S) →
        ∃ x ∈ S, x ≠ t ∧ ∃ y ∉ S, H.Adj x y) ∧
      ∀ a b, H.Adj a b → ∀ S : Set V, a ∈ S → b ∈ S →
        (∃ x ∈ S, x ≠ a ∧ x ≠ b) → (∃ y, y ∉ S) →
          ∃ x ∈ S, x ≠ a ∧ x ≠ b ∧ ∃ y ∉ S, G.Adj x y := by
  classical
  let B (D : SimpleGraph V) := ∀ (t : V) (S : Set V), t ∈ S → (∃ x ∈ S, x ≠ t) →
    (∃ y, y ∉ S) → ∃ x ∈ S, x ≠ t ∧ ∃ y ∉ S, D.Adj x y
  let good (a b : V) := ∀ S : Set V, a ∈ S → b ∈ S → (∃ x ∈ S, x ≠ a ∧ x ≠ b) →
    (∃ y, y ∉ S) → ∃ x ∈ S, x ≠ a ∧ x ≠ b ∧ ∃ y ∉ S, G.Adj x y
  have shrink (n : ℕ) (D : SimpleGraph V) (size : D.edgeFinset.card = n)
      (sub : D ≤ G) (bd : B D) : ∃ H : SimpleGraph V, H ≤ G ∧ B H ∧ ∀ a b, H.Adj a b → good a b := by
    induction n using Nat.strong_induction_on generalizing D with
    | h n ih =>
      by_cases keep : ∀ a b, D.Adj a b → good a b
      · exact ⟨D,sub,bd,keep⟩
      · push Not at keep
        obtain ⟨a,b,ab,bad⟩ := keep
        let E := D.deleteEdges {s(a,b)}
        let : DecidableRel E.Adj := fun _ _ => Classical.propDecidable _
        have be : B E := deleteSeparatingEdge D (a := a) (b := b) bd (by
          intro stuck
          apply bad
          intro S ha hb inside outside
          obtain ⟨i,hi,ia,ib,j,hj,edge⟩ := stuck S ha hb inside outside
          exact ⟨i,hi,ia,ib,j,hj,sub edge⟩)
        have removed : E.edgeFinset = D.edgeFinset.erase s(a,b) := by
          ext e
          simp [E,edgeSet_deleteEdges,and_comm]
        have lt : E.edgeFinset.card < n := by
          rw [← size,removed]
          exact Finset.card_erase_lt_of_mem (D.mem_edgeFinset.mpr ab)
        exact ih _ lt E rfl ((D.deleteEdges_le _).trans sub) be
  exact shrink _ G rfl le_rfl block

/-- A clique on two vertices cannot meet both sides of a vertex cut, except
at the deleted vertices. -/
private theorem sideAvoidingEdge {V : Type*} (G : SimpleGraph V) {a b u v : V}
    (ab : G.Adj a b)
    (split : ¬ ∀ S : Set V, u ∈ S → v ∈ S → (∃ x ∈ S, x ≠ u ∧ x ≠ v) → (∃ y, y ∉ S) →
      ∃ x ∈ S, x ≠ u ∧ x ≠ v ∧ ∃ y ∉ S, G.Adj x y) :
    ∃ R : Set V, R.Nonempty ∧ u ∉ R ∧ v ∉ R ∧ a ∉ R ∧ b ∉ R ∧
      ∀ x ∈ R, ∀ y, G.Adj x y → y ∈ R ∨ y = u ∨ y = v := by
  classical
  push Not at split
  obtain ⟨T,tu,tv,⟨i,hi,iu,iv⟩,⟨j,hj⟩,gap⟩ := split
  let X := {w : V | w ∈ T ∧ w ≠ u ∧ w ≠ v}
  have leftSide (p) (hp : p ∈ X) (q) (edge : G.Adj p q) : q ∈ X ∨ q = u ∨ q = v := by
    by_contra! miss
    exact gap p hp.1 hp.2.1 hp.2.2 q (fun h => miss.1 ⟨h,miss.2.1,miss.2.2⟩) edge
  have rightSide (p) (hp : p ∈ Tᶜ) (q) (edge : G.Adj p q) : q ∈ Tᶜ ∨ q = u ∨ q = v := by
    by_contra! miss
    exact gap q (by simpa using miss.1) miss.2.1 miss.2.2 p hp edge.symm
  have rightWitness (ha : a ∈ T) (hb : b ∈ T) := (show
      ∃ R : Set V, R.Nonempty ∧ u ∉ R ∧ v ∉ R ∧ a ∉ R ∧ b ∉ R ∧
        ∀ x ∈ R, ∀ y, G.Adj x y → y ∈ R ∨ y = u ∨ y = v from
    ⟨Tᶜ,⟨j,hj⟩,fun h => h tu,fun h => h tv,fun h => h ha,fun h => h hb,rightSide⟩)
  by_cases ax : a ∈ X
  · exact rightWitness ax.1 (by by_contra h; exact gap a ax.1 ax.2.1 ax.2.2 b h ab)
  by_cases bx : b ∈ X
  · exact rightWitness (by by_contra h; exact gap b bx.1 bx.2.1 bx.2.2 a h ab.symm) bx.1
  exact ⟨X,⟨i,hi,iu,iv⟩,fun h => h.2.1 rfl,fun h => h.2.2 rfl,ax,bx,leftSide⟩

/-- Each region attached along an adjacent pair has a nonempty subregion all
of whose vertices have only nonseparating incident edges in the entire graph.
The subregion is again attached along an adjacent pair. -/
theorem regionOfNonseparatingStars {V : Type*} [Finite V] (G : SimpleGraph V)
    (block : ∀ (t : V) (S : Set V), t ∈ S → (∃ x ∈ S, x ≠ t) → (∃ y, y ∉ S) →
      ∃ x ∈ S, x ≠ t ∧ ∃ y ∉ S, G.Adj x y)
    {a b : V} (ab : G.Adj a b) (C : Set V) (nonempty : C.Nonempty)
    (ca : a ∉ C) (cb : b ∉ C)
    (boundary : ∀ x ∈ C, ∀ y, G.Adj x y → y ∈ C ∨ y = a ∨ y = b) :
    ∃ (p q : V) (R : Set V), R ⊆ C ∧ R.Nonempty ∧ G.Adj p q ∧ p ∉ R ∧ q ∉ R ∧
      (∀ x ∈ R, ∀ y, G.Adj x y → y ∈ R ∨ y = p ∨ y = q) ∧
      ∀ u ∈ R, ∀ v, G.Adj u v → ∀ S : Set V, u ∈ S → v ∈ S →
        (∃ x ∈ S, x ≠ u ∧ x ≠ v) → (∃ y, y ∉ S) →
          ∃ x ∈ S, x ≠ u ∧ x ≠ v ∧ ∃ y ∉ S, G.Adj x y := by
  classical
  let good (u v : V) := ∀ S : Set V, u ∈ S → v ∈ S → (∃ x ∈ S, x ≠ u ∧ x ≠ v) →
    (∃ y, y ∉ S) → ∃ x ∈ S, x ≠ u ∧ x ≠ v ∧ ∃ y ∉ S, G.Adj x y
  have inside (n : ℕ) (A : Set V) (size : A.ncard = n) (p q : V) (pq : G.Adj p q)
      (live : A.Nonempty) (pa : p ∉ A) (qa : q ∉ A)
      (near : ∀ x ∈ A, ∀ y, G.Adj x y → y ∈ A ∨ y = p ∨ y = q) :
      ∃ (i j : V) (T : Set V), T ⊆ A ∧ T.Nonempty ∧ G.Adj i j ∧ i ∉ T ∧ j ∉ T ∧
        (∀ x ∈ T, ∀ y, G.Adj x y → y ∈ T ∨ y = i ∨ y = j) ∧
        ∀ u ∈ T, ∀ v, G.Adj u v → good u v := by
    induction n using Nat.strong_induction_on generalizing A p q with
    | h n ih =>
      by_cases safe : ∀ u ∈ A, ∀ v, G.Adj u v → good u v
      · exact ⟨p,q,A,(by intro x hx; exact hx),live,pq,pa,qa,near,safe⟩
      · push Not at safe
        obtain ⟨u,hu,v,uv,bad⟩ := safe
        obtain ⟨R,rne,ru,rv,rp,rq,closed⟩ := sideAvoidingEdge G pq bad
        have sub : R ⊆ A := by
          intro w hw
          by_contra wa
          let S := {t : V | t = v ∨ t ∈ R ∧ t ∉ A}
          have un : u ∉ S := by rintro (e | e); exact uv.ne e; exact ru e.1
          have wv : w ≠ v := fun e => rv (e ▸ hw)
          obtain ⟨i,hi,iv,j,hj,ij⟩ := block v S (Or.inl rfl) ⟨w,Or.inr ⟨hw,wa⟩,wv⟩ ⟨u,un⟩
          have ir := hi.resolve_left iv
          have ja : j ∉ A := by
            intro mem
            rcases near j mem i ij.symm with h | h | h
            · exact ir.2 h
            · exact rp (h ▸ ir.1)
            · exact rq (h ▸ ir.1)
          rcases closed i ir.1 j ij with h | h | h
          · exact hj (Or.inr ⟨h,ja⟩)
          · exact ja (h ▸ hu)
          · exact hj (Or.inl h)
        have lt : R.ncard < n := (Set.ncard_lt_ncard (show R ⊂ A from
          ⟨sub,fun back => ru (back hu)⟩)).trans_eq size
        obtain ⟨i,j,T,tSub,rest⟩ := ih R.ncard lt R rfl u v uv rne ru rv closed
        exact ⟨i,j,T,tSub.trans sub,rest⟩
  exact inside C.ncard C rfl a b ab nonempty ca cb boundary

/-- Any graph containing the nonseparating edges of a biconnected graph of
minimum degree three has at least n+2 edges on n vertices. Four vertices have degree at least three
in the covering graph: two disjoint edges have both whole stars preserved. -/
theorem card_of_nonseparating_edges {V : Type*} [Fintype V] [Nonempty V]
    (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (floor : ∀ t, 3 ≤ G.degree t)
    (block : ∀ (t : V) (S : Set V), t ∈ S → (∃ x ∈ S, x ≠ t) → (∃ y, y ∉ S) →
      ∃ x ∈ S, x ≠ t ∧ ∃ y ∉ S, G.Adj x y)
    (contains : ∀ a b, G.Adj a b →
      (∀ S : Set V, a ∈ S → b ∈ S → (∃ x ∈ S, x ≠ a ∧ x ≠ b) → (∃ y, y ∉ S) →
        ∃ x ∈ S, x ≠ a ∧ x ≠ b ∧ ∃ y ∉ S, G.Adj x y) → H.Adj a b) :
    Fintype.card V + 2 ≤ H.edgeFinset.card := by
  classical
  obtain ⟨J,sub,bJ,edges⟩ := spanningNonseparatingEdges G block
  have jh : J ≤ H := fun {u v} e => contains u v (sub e) (edges u v e)
  have many (t : V) : 1 < (G.neighborFinset t).card := by
    rw [card_neighborFinset_eq_degree]
    exact (by decide : 1 < 3).trans_le (floor t)
  have third (t r : V) : ∃ y, y ≠ t ∧ y ≠ r := by
    obtain ⟨y,hy,yr⟩ := Finset.exists_mem_ne (many t) r
    exact ⟨y,((G.mem_neighborFinset ..).1 hy).ne.symm,yr⟩
  have another (t r : V) (tr : t ≠ r) : ∃ b, H.Adj t b ∧ b ≠ r := by
    let S : Set V := {t,r}
    obtain ⟨y,yt,yr⟩ := third t r
    obtain ⟨x,hx,xr,b,hb,xb⟩ := bJ r S (by simp [S]) ⟨t,by simp [S],tr⟩ ⟨y,by simp [S,yt,yr]⟩
    have xt : x = t := by simpa [S,xr] using hx
    exact ⟨b,xt ▸ jh xb,fun e => hb (by simp [S,e])⟩
  have base (t : V) : 2 ≤ H.degree t := by
    obtain ⟨r,rt,_⟩ := third t t
    obtain ⟨y,ty,_⟩ := another t r rt.symm
    obtain ⟨z,tz,zy⟩ := another t y ty.ne
    rw [← card_neighborFinset_eq_degree]
    exact Finset.one_lt_card.mpr ⟨z,(H.mem_neighborFinset ..).2 tz,y,(H.mem_neighborFinset ..).2 ty,zy⟩
  have edgeAway (a b : V) (ab : G.Adj a b) :
      ∃ u v, u ≠ a ∧ u ≠ b ∧ v ≠ a ∧ v ≠ b ∧ G.Adj u v ∧ 3 ≤ H.degree u ∧ 3 ≤ H.degree v := by
    let C := {x : V | x ≠ a ∧ x ≠ b}
    obtain ⟨y,ya,yb⟩ := third a b
    obtain ⟨p,q,R,subR,⟨u,hu⟩,_,_,_,near,safe⟩ :=
      regionOfNonseparatingStars G block ab C ⟨y,ya,yb⟩
        (fun h => h.1 rfl) (fun h => h.2 rfl) (by
          intro x hx z _
          by_cases za : z = a
          · exact Or.inr (Or.inl za)
          by_cases zb : z = b
          · exact Or.inr (Or.inr zb)
          · exact Or.inl ⟨za,zb⟩)
    have cap : ({p,q} : Finset V).card ≤ 2 := by
      calc
        _ ≤ ({q} : Finset V).card + 1 := Finset.card_insert_le ..
        _ = 2 := by simp
    have outside : ¬ G.neighborFinset u ⊆ {p,q} := by
      intro h
      have upper := (Finset.card_le_card h).trans cap
      rw [card_neighborFinset_eq_degree] at upper
      have := floor u
      omega
    obtain ⟨v,hv,away⟩ := Finset.not_subset.mp outside
    have uv := (G.mem_neighborFinset ..).1 hv
    have vr : v ∈ R := (near u hu v uv).resolve_right (by simpa using away)
    have high (w) (hw : w ∈ R) : 3 ≤ H.degree w := by
      have incl : G.neighborFinset w ⊆ H.neighborFinset w := by
        intro t ht
        have e := (G.mem_neighborFinset ..).1 ht
        exact (H.mem_neighborFinset ..).2 (contains w t e (safe w hw t e))
      exact (floor w).trans (by simpa only [card_neighborFinset_eq_degree] using Finset.card_le_card incl)
    exact ⟨u,v,(subR hu).1,(subR hu).2,(subR vr).1,(subR vr).2,uv,high u hu,high v vr⟩
  let a := Classical.arbitrary V
  obtain ⟨b,hb,_⟩ := Finset.exists_mem_ne (many a) a
  obtain ⟨u,v,_,_,_,_,uv,hu,hv⟩ := edgeAway a b ((G.mem_neighborFinset ..).1 hb)
  obtain ⟨s,t,su,sv,tu,tv,st,hs,ht⟩ := edgeAway u v uv
  let Q : Finset V := {u,v,s,t}
  have qcard : Q.card = 4 := by simp [Q,uv.ne,su.symm,sv.symm,tu.symm,tv.symm,st.ne]
  have point (w : V) : 2 + (if w ∈ Q then 1 else 0) ≤ H.degree w := by
    by_cases hw : w ∈ Q
    · simp only [hw, if_true]
      simp only [Q,Finset.mem_insert,Finset.mem_singleton] at hw
      rcases hw with rfl | rfl | rfl | rfl <;> assumption
    · simpa [hw] using base w
  have total := Finset.sum_le_sum (s := Finset.univ) (fun w _ => point w)
  simp [Finset.sum_add_distrib,H.sum_degrees_eq_twice_card_edges,qcard] at total
  omega

/-- The obstruction works for an arbitrary set of forbidden cycle lengths.
A triangle is the sole exception where contraction can lower an outside degree. -/
theorem cycleThroughNonseparatingEdge {V : Type} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (lengths : Set ℕ)
    (floor : ∀ t, 3 ≤ G.degree t)
    (block : ∀ (t : V) (S : Set V), t ∈ S → (∃ x ∈ S, x ≠ t) → (∃ y, y ∉ S) →
      ∃ x ∈ S, x ≠ t ∧ ∃ y ∉ S, G.Adj x y)
    (avoid : ∀ w (c : G.Walk w w), c.IsCycle → c.length ∉ lengths)
    (smaller : ∀ (W : Type) [Fintype W] (K : SimpleGraph W) (z : W),
      Fintype.card W < Fintype.card V → (∀ t, 3 ≤ K.degree t) → 4 ≤ K.degree z →
      (∀ (t : W) (S : Set W), t ∈ S → (∃ x ∈ S, x ≠ t) → (∃ y, y ∉ S) →
        ∃ x ∈ S, x ≠ t ∧ ∃ y ∉ S, K.Adj x y) →
      ∃ w, ∃ c : K.Walk w w, c.IsCycle ∧ c.length ∈ lengths)
    {a b : V} (ab : G.Adj a b)
    (pair : ∀ S : Set V, a ∈ S → b ∈ S → (∃ x ∈ S, x ≠ a ∧ x ≠ b) → (∃ y, y ∉ S) →
      ∃ x ∈ S, x ≠ a ∧ x ≠ b ∧ ∃ y ∉ S, G.Adj x y) :
    ∃ w, ∃ c : G.Walk w w, c.IsCycle ∧ s(a,b) ∈ c.edges ∧
      (c.length = 3 ∨ ∃ n ∈ lengths, c.length = n + 1) := by
  classical
  by_cases triangle : ∃ t, G.Adj a t ∧ G.Adj b t
  · obtain ⟨t,at',bt⟩ := triangle
    let c : G.Walk a a := .cons ab (.cons bt (.cons at'.symm .nil))
    refine ⟨a,c,?_,by simp [c],Or.inl rfl⟩
    apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
    constructor
    · rw [show c = _ from rfl,Walk.tail_cons]
      apply (Walk.isPath_copy _ _ _).mpr
      simp [Walk.cons_isPath_iff,ab.ne.symm,bt.ne,at'.ne.symm]
    · exact le_rfl
  · obtain ⟨K,z,_,_,lt,degs,high,kept,lift⟩ := contractInBlock G ab floor
      (fun t ha hb => triangle ⟨t,ha,hb⟩) block pair
    obtain ⟨w,c,hc,len⟩ := smaller _ K z lt degs high kept
    obtain ⟨v,d,hd,same | ⟨long,edge⟩⟩ := lift w c hc
    · exact (avoid v d hd (same.symm ▸ len)).elim
    · exact ⟨v,d,hd,edge,Or.inr ⟨c.length,len,long⟩⟩

/-- A contracted edge can be chosen at any prescribed vertex, avoiding a
second prescribed vertex. Both degree and biconnectivity survive; in a
bipartite input every even cycle in the smaller block lifts at unchanged length. -/
theorem evenSpectrumOfBipartiteBlock {V : Type} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (color : G.Coloring Bool)
    (floor : ∀ x, 3 ≤ G.degree x)
    (block : ∀ (t : V) (S : Set V), t ∈ S → (∃ x ∈ S, x ≠ t) → (∃ y, y ∉ S) →
      ∃ x ∈ S, x ≠ t ∧ ∃ y ∉ S, G.Adj x y)
    (a r : V) (ar : a ≠ r) :
    ∃ b, G.Adj a b ∧ b ≠ r ∧
      let W := {t : V // t ≠ a}
      ∃ K : SimpleGraph W, ∃ z : W, z.val = b ∧
        K = G.map (fun v => if h : v = a then z else ⟨v,h⟩) ∧ Fintype.card W + 1 = Fintype.card V ∧
        (∀ t, 3 ≤ K.degree t) ∧ 4 ≤ K.degree z ∧
        (∀ (t : W) (S : Set W), t ∈ S → (∃ x ∈ S, x ≠ t) → (∃ y, y ∉ S) →
          ∃ x ∈ S, x ≠ t ∧ ∃ y ∉ S, K.Adj x y) ∧
        ∀ w (c : K.Walk w w), c.IsCycle → Even c.length →
          ∃ v, ∃ d : G.Walk v v, d.IsCycle ∧ d.length = c.length := by
  classical
  obtain ⟨H,sub,blockH,safe⟩ := spanningNonseparatingEdges G block
  have count : 1 < (G.neighborFinset a).card := by rw [card_neighborFinset_eq_degree]; have := floor a; omega
  obtain ⟨y,hy,yr⟩ := Finset.exists_mem_ne count r
  have ya := ((G.mem_neighborFinset ..).1 hy).ne.symm
  let S : Set V := {a,r}
  obtain ⟨x,hx,xr,b,hb,e⟩ := blockH r S (by simp [S]) ⟨a,by simp [S],ar⟩ ⟨y,by simp [S,ya,yr]⟩
  have xa : x = a := by simpa [S,xr] using hx
  subst x
  have common (v : V) (av : G.Adj a v) (bv : G.Adj b v) : False := by
    have h₁ := color.valid av
    have h₂ := color.valid bv
    have h₃ := color.valid (sub e)
    cases h : color a <;> cases j : color b <;> cases l : color v <;> simp [h,j,l] at h₁ h₂ h₃
  obtain ⟨K,z,hz,quotient,lt,degs,high,bK,lift⟩ := contractInBlock G (sub e) floor common block (safe a b e)
  have card : Fintype.card {v : V // v ≠ a} = Fintype.card V - 1 := by
    rw [Fintype.card_subtype_compl (fun x : V => x = a),Fintype.card_subtype_eq]
  refine ⟨b,sub e,fun eq => hb (by simp [S,eq]),K,z,hz,quotient,by omega,degs,high,bK,?_⟩
  intro w c hc even
  obtain ⟨v,d,hd,same | ⟨extra,_⟩⟩ := lift w c hc
  · exact ⟨v,d,hd,same⟩
  · have ed := (color.even_length_iff_congr d).2 Iff.rfl
    rw [extra,Nat.even_add_one] at ed
    exact (ed even).elim


/-- Two common neighbors display an explicit four-cycle through both terminals. -/
theorem squareOfCommonNeighbors {V : Type*} {G : SimpleGraph V} {x y p q : V}
    (xy : x ≠ y) (pq : p ≠ q) (xp : G.Adj x p) (yp : G.Adj y p)
    (xq : G.Adj x q) (yq : G.Adj y q) :
    ∃ c : G.Walk x x, c.IsCycle ∧ c.length = 4 := by
  let c : G.Walk x x := .cons xp (.cons yp.symm (.cons yq (.cons xq.symm .nil)))
  refine ⟨c,?_,rfl⟩
  apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
  constructor
  · rw [show c = _ from rfl,Walk.tail_cons]
    apply (Walk.isPath_copy _ _ _).mpr
    simp [Walk.cons_isPath_iff,yp.ne.symm,pq,xp.ne.symm,yq.ne,xy.symm,xq.ne.symm]
  · exact (by decide : 3 ≤ 4)

/-- Absence of dyadic cycles makes each pair of distinct vertices determine
at most one common neighbor, without a finiteness assumption. -/
theorem noDyadic_commonNeighbor_unique {V : Type*} {G : SimpleGraph V}
    (avoid : ¬ ∃ (k : ℕ) (w : V) (c : G.Walk w w), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2^k)
    {x y p q : V} (xy : x ≠ y)
    (xp : G.Adj x p) (yp : G.Adj y p) (xq : G.Adj x q) (yq : G.Adj y q) : p = q := by
  by_contra ne
  obtain ⟨c,hc,len⟩ := squareOfCommonNeighbors xy ne xp yp xq yq
  exact avoid ⟨2,x,c,le_rfl,hc,len⟩


/-- In a graph of minimum degree three with at most one common neighbor per
distinct pair, a region attached at the ends of an edge has at least seven
vertices. The argument counts a two-step neighborhood at an interior vertex. -/
theorem bankSeven {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (floor : ∀ x, 3 ≤ G.degree x)
    (unique : ∀ {x y p q : V}, x ≠ y → G.Adj x p → G.Adj y p →
      G.Adj x q → G.Adj y q → p = q)
    (p q : V) (pq : G.Adj p q) (R : Set V) (live : R.Nonempty)
    (rp : p ∉ R) (rq : q ∉ R)
    (near : ∀ x ∈ R, ∀ y, G.Adj x y → y ∈ R ∨ y = p ∨ y = q) :
    7 ≤ R.ncard := by
  classical
  have center : ∃ z ∈ R, ¬G.Adj z p ∧ ¬G.Adj z q := by
    by_contra! touch
    have small (a b : V) (ab : G.Adj a b) (bb : b ∉ R)
        (bound : ∀ x ∈ R, ∀ y, G.Adj x y → y ∈ R ∨ y = a ∨ y = b)
        (cover : ∀ x ∈ R, G.Adj x a ∨ G.Adj x b) (x : V) (hx : x ∈ R)
        (xa : G.Adj x a) : False := by
      have common (y : V) (hy : G.Adj x y) (ya : y ≠ a) : G.Adj a y := by
        rcases bound x hx y hy with hR | h | h
        · rcases cover y hR with h | h
          · exact h.symm
          · exact (ya (unique (show x ≠ b from fun e => bb (e ▸ hx)) hy h.symm xa ab.symm)).elim
        · exact (ya h).elim
        · exact h ▸ ab
      have one : ((G.neighborFinset x).erase a).card ≤ 1 := by
        apply Finset.card_le_one.mpr
        intro y hy z hz
        obtain ⟨ya,xy⟩ := Finset.mem_erase.mp hy
        obtain ⟨za,xz⟩ := Finset.mem_erase.mp hz
        have e := (G.mem_neighborFinset ..).1 xy
        have f := (G.mem_neighborFinset ..).1 xz
        exact unique xa.ne e (common y e ya) f (common z f za)
      rw [Finset.card_erase_of_mem ((G.mem_neighborFinset ..).2 xa),card_neighborFinset_eq_degree] at one
      have := floor x
      omega
    have cover (x : V) (hx : x ∈ R) : G.Adj x p ∨ G.Adj x q :=
      or_iff_not_imp_left.mpr (touch x hx)
    obtain ⟨x,hx⟩ := live
    rcases cover x hx with h | h
    · exact small p q pq rq near cover x hx h
    · exact small q p pq.symm rp (fun x hx y e => (near x hx y e).imp_right Or.symm)
        (fun x hx => (cover x hx).symm) x hx h
  obtain ⟨z,hz,zp,zq⟩ := center
  let N := G.neighborFinset z
  let F (v : V) := (G.neighborFinset v).erase z
  have neighbor {v : V} (hv : v ∈ N) : G.Adj z v := (G.mem_neighborFinset ..).1 hv
  have inner {v : V} (hv : v ∈ N) : v ∈ R := by
    rcases near z hz v (neighbor hv) with h | h | h
    · exact h
    · exact (zp (h ▸ neighbor hv)).elim
    · exact (zq (h ▸ neighbor hv)).elim
  have disj : (N : Set V).PairwiseDisjoint F := by
    intro v hv w hw vw
    apply Finset.disjoint_left.mpr
    intro t htv htw
    obtain ⟨tz,vt⟩ := Finset.mem_erase.mp htv
    have wt := (Finset.mem_erase.mp htw).2
    exact tz (unique vw ((G.mem_neighborFinset ..).1 vt) ((G.mem_neighborFinset ..).1 wt)
      (neighbor hv).symm (neighbor hw).symm)
  have point (v) (hv : v ∈ N) : 2 ≤ (F v).card := by
    rw [show F v = _ from rfl,Finset.card_erase_of_mem ((G.mem_neighborFinset ..).2 (neighbor hv).symm),
      card_neighborFinset_eq_degree]
    have := floor v
    omega
  have total : 2 * N.card ≤ (N.biUnion F).card := by
    rw [Finset.card_biUnion disj]
    simpa [Nat.mul_comm] using Finset.sum_le_sum point
  have znot : z ∉ N.biUnion F := by
    intro h
    obtain ⟨v,_,hv⟩ := Finset.mem_biUnion.mp h
    exact (Finset.mem_erase.mp hv).1 rfl
  have subset : insert z (N.biUnion F) ⊆ insert p (insert q R.toFinset) := by
    intro t ht
    rcases Finset.mem_insert.mp ht with rfl | ht
    · simp [hz]
    · obtain ⟨v,hv,vt⟩ := Finset.mem_biUnion.mp ht
      have e := (G.mem_neighborFinset ..).1 (Finset.mem_erase.mp vt).2
      rcases near v (inner hv) t e with h | h | h <;> simp [h]
  have count := Finset.card_le_card subset
  rw [Finset.card_insert_of_notMem znot] at count
  have cap₁ := Finset.card_insert_le p (insert q R.toFinset)
  have cap₂ := Finset.card_insert_le q R.toFinset
  have cardN : N.card = G.degree z := G.card_neighborFinset_eq_degree z
  rw [Set.ncard_eq_toFinset_card']
  have degree := floor z
  by_contra! tooSmall
  have three : N.card = 3 := by omega
  let K := insert p (insert q R.toFinset)
  let U := N.biUnion F
  have cap : K.card ≤ 8 := by dsimp [K]; omega
  have encl : N ⊆ K := by
    intro v hv
    simp [K,inner hv]
  have only {u v w : V} (hu : u ∈ N) (hv : v ∈ N) (hw : w ∈ N)
      (uv : G.Adj u v) (uw : G.Adj u w) : v = w :=
    unique (neighbor hu).ne (neighbor hv) uv (neighbor hw) uw
  have adjacent : ∃ a ∈ N, ∃ b ∈ N, G.Adj a b := by
    by_contra! ind
    have sep : Disjoint N (insert z U) := by
      apply Finset.disjoint_left.mpr
      intro t ht ht'
      rcases Finset.mem_insert.mp ht' with e | h
      · exact (neighbor ht).ne e.symm
      · obtain ⟨v,hv,vt⟩ := Finset.mem_biUnion.mp h
        exact ind v hv t ht ((G.mem_neighborFinset ..).1 (Finset.mem_erase.mp vt).2)
    have lt := Finset.card_le_card (Finset.union_subset encl subset)
    rw [Finset.card_union_of_disjoint sep,Finset.card_insert_of_notMem znot] at lt
    change N.card + ((N.biUnion F).card + 1) ≤ K.card at lt
    omega
  obtain ⟨a,ha,b,hb,ab⟩ := adjacent
  have third : ¬ N ⊆ {a,b} := by
    intro incl
    have bound := Finset.card_le_card incl
    simp [three,ab.ne] at bound
  obtain ⟨c,hc,fresh⟩ := Finset.not_subset.mp third
  have ca : c ≠ a := fun e => fresh (by simp [e])
  have cb : c ≠ b := fun e => fresh (by simp [e])
  have enum : N = {a,b,c} := by
    apply Eq.symm
    apply Finset.eq_of_subset_of_card_le
    · exact Finset.insert_subset ha (Finset.insert_subset hb (Finset.singleton_subset_iff.mpr hc))
    · simp [three,ab.ne,ca.symm,cb.symm]
  have noC (v) (hv : v ∈ N) : ¬ G.Adj c v := by
    have choice : v = a ∨ v = b ∨ v = c := by simpa [enum] using hv
    rintro e
    rcases choice with rfl | rfl | rfl
    · exact cb (only ha hc hb e.symm ab)
    · exact ca (only hb hc ha e.symm ab.symm)
    · exact e.ne rfl
  have cnot : c ∉ insert z U := by
    intro mem
    rcases Finset.mem_insert.mp mem with h | h
    · exact (neighbor hc).ne h.symm
    · obtain ⟨v,hv,vc⟩ := Finset.mem_biUnion.mp h
      exact noC v hv ((G.mem_neighborFinset ..).1 (Finset.mem_erase.mp vc).2).symm
  have wide : insert c (insert z U) ⊆ K :=
    Finset.insert_subset (encl hc) subset
  have eq : insert c (insert z U) = K := by
    apply Finset.eq_of_subset_of_card_le wide
    rw [Finset.card_insert_of_notMem cnot,Finset.card_insert_of_notMem znot]
    omega
  have sum3 := congrArg Finset.card eq
  rw [Finset.card_insert_of_notMem cnot,Finset.card_insert_of_notMem znot] at sum3
  change (N.biUnion F).card + 1 + 1 = K.card at sum3
  rw [Finset.card_biUnion disj,enum] at sum3
  simp [ab.ne,ca.symm,cb.symm] at sum3
  have a2 : (F a).card = 2 := by have := point a ha; have := point b hb; have := point c hc; omega
  have b2 : (F b).card = 2 := by have := point a ha; have := point b hb; have := point c hc; omega
  have baF : b ∈ F a := Finset.mem_erase.mpr ⟨(neighbor hb).ne.symm,(G.mem_neighborFinset ..).2 ab⟩
  have abF : a ∈ F b := Finset.mem_erase.mpr ⟨(neighbor ha).ne.symm,(G.mem_neighborFinset ..).2 ab.symm⟩
  obtain ⟨x,hx,xb⟩ := Finset.exists_mem_ne (a2 ▸ (by decide : 1 < 2) : 1 < (F a).card) b
  obtain ⟨y,hy,ya⟩ := Finset.exists_mem_ne (b2 ▸ (by decide : 1 < 2) : 1 < (F b).card) a
  have edgeF {u v : V} (h : v ∈ F u) : G.Adj u v := (G.mem_neighborFinset ..).1 (Finset.mem_erase.mp h).2
  have rangeF {u v w : V} (card : (F u).card = 2) (hv : v ∈ F u) (hw : w ∈ F u) (vw : v ≠ w) :
      F u = {v,w} := by
    apply Eq.symm
    apply Finset.eq_of_subset_of_card_le
    · exact Finset.insert_subset hv (Finset.singleton_subset_iff.mpr hw)
    · simp [card,vw]
  have fa := rangeF a2 baF hx xb.symm
  have fb := rangeF b2 abF hy ya.symm
  have xy : x ≠ y := fun h => (Finset.disjoint_left.mp (disj ha hb ab.ne)) hx (h ▸ hy)
  have nonedge : ¬G.Adj x y := by
    intro e
    exact ya (unique xb e (edgeF hy) (edgeF hx).symm ab.symm)
  have out (u v X Y : V) (hu : u ∈ N) (hv : v ∈ N) (uv : G.Adj u v)
      (hX : X ∈ F u) (Xv : X ≠ v) (noXY : ¬G.Adj X Y)
      (fu : F u = {v,X}) (fv : F v = {u,Y})
      (allN : ∀ w ∈ N, w = u ∨ w = v ∨ w = c) : X ∉ R := by
    intro XR
    have Xc : X ≠ c := fun e => noC u hu (e ▸ (edgeF hX).symm)
    have Xz : X ≠ z := (Finset.mem_erase.mp hX).1
    have notZ : ¬ G.Adj X z := fun e => Xv (only hu ((G.mem_neighborFinset ..).2 e.symm) hv (edgeF hX) uv)
    have notV : ¬ G.Adj X v := fun e => Xz (unique uv.ne (edgeF hX) e.symm (neighbor hu).symm (neighbor hv).symm)
    have atC (t : V) (xt : G.Adj X t) (tu : t ≠ u) : G.Adj c t := by
      have mem : t ∈ K := by
        rcases near X XR t xt with h | h | h <;> simp [K,h]
      rw [← eq] at mem
      rcases Finset.mem_insert.mp mem with e | mem
      · exact (Xz (unique (by intro h; exact noC v hv (h ▸ uv) : u ≠ c)
          (edgeF hX) (e ▸ xt.symm) (neighbor hu).symm (neighbor hc).symm)).elim
      rcases Finset.mem_insert.mp mem with e | mem
      · exact (notZ (e ▸ xt)).elim
      obtain ⟨w,hw,wt⟩ := Finset.mem_biUnion.mp mem
      rcases allN w hw with h | h | h
      · subst w
        have choice : t = v ∨ t = X := by simpa [fu] using wt
        rcases choice with h | h
        · exact (notV (h ▸ xt)).elim
        · exact (xt.ne h.symm).elim
      · subst w
        have choice : t = u ∨ t = Y := by simpa [fv] using wt
        rcases choice with h | h
        · exact (tu h).elim
        · exact (noXY (h ▸ xt)).elim
      · exact h ▸ edgeF wt
    have small : ((G.neighborFinset X).erase u).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro s hs t ht
      obtain ⟨su,xs⟩ := Finset.mem_erase.mp hs
      obtain ⟨tu,xt⟩ := Finset.mem_erase.mp ht
      have e := (G.mem_neighborFinset ..).1 xs
      have f := (G.mem_neighborFinset ..).1 xt
      exact unique Xc e (atC s e su) f (atC t f tu)
    rw [Finset.card_erase_of_mem ((G.mem_neighborFinset ..).2 (edgeF hX).symm),card_neighborFinset_eq_degree] at small
    have := floor X
    omega
  have allN (w) (hw : w ∈ N) : w = a ∨ w = b ∨ w = c := by simpa [enum] using hw
  have outX := out a b x y ha hb ab hx xb nonedge fa fb allN
  have outY := out b a y x hb ha ab.symm hy ya (fun e => nonedge e.symm) fb fa
    (by
      intro w hw
      rcases allN w hw with h | h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
      · exact Or.inr (Or.inr h))
  have term {u w : V} (hu : u ∈ N) (hw : w ∈ F u) (outside : w ∉ R) : w = p ∨ w = q :=
    (near u (inner hu) w (edgeF hw)).resolve_left outside
  rcases term ha hx outX with rfl | rfl <;> rcases term hb hy outY with rfl | rfl
  · exact xy rfl
  · exact nonedge pq
  · exact nonedge pq.symm
  · exact xy rfl


/-- A uniform lower bound on the size of every region attached at an edge
transfers to the excess of edges over vertices in any graph containing the
nonseparating edges of a biconnected graph of minimum degree three. -/
theorem twoBankCount {V : Type*} [Fintype V]
    (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (floor : ∀ t, 3 ≤ G.degree t)
    {k : ℕ}
    (size : ∀ p q, G.Adj p q → ∀ R : Set V, R.Nonempty → p ∉ R → q ∉ R →
      (∀ x ∈ R, ∀ y, G.Adj x y → y ∈ R ∨ y = p ∨ y = q) → k ≤ R.ncard)
    (block : ∀ (t : V) (S : Set V), t ∈ S → (∃ x ∈ S, x ≠ t) → (∃ y, y ∉ S) →
      ∃ x ∈ S, x ≠ t ∧ ∃ y ∉ S, G.Adj x y)
    (contains : ∀ a b, G.Adj a b →
      (∀ S : Set V, a ∈ S → b ∈ S → (∃ x ∈ S, x ≠ a ∧ x ≠ b) → (∃ y, y ∉ S) →
        ∃ x ∈ S, x ≠ a ∧ x ≠ b ∧ ∃ y ∉ S, G.Adj x y) → H.Adj a b)
    {a b : V} (ab : G.Adj a b) (S : Set V) (ha : a ∈ S) (hb : b ∈ S)
    (inside : ∃ x ∈ S, x ≠ a ∧ x ≠ b) (outside : ∃ y, y ∉ S)
    (gap : ∀ x ∈ S, x ≠ a → x ≠ b → ∀ y ∉ S, ¬ G.Adj x y) :
    2 * k ≤ (Finset.univ.filter (fun v => 3 ≤ H.degree v)).card ∧
      Fintype.card V + k ≤ H.edgeFinset.card := by
  classical
  let Q := Finset.univ.filter (fun v => 3 ≤ H.degree v)
  have bank (C : Set V) (live : C.Nonempty) (ca : a ∉ C) (cb : b ∉ C)
      (near : ∀ x ∈ C, ∀ y, G.Adj x y → y ∈ C ∨ y = a ∨ y = b) :
      ∃ R : Finset V, k ≤ R.card ∧ R ⊆ Q ∧ ∀ v ∈ R, v ∈ C := by
    obtain ⟨p,q,T,subT,neT,pq,tp,tq,bound,safe⟩ :=
      regionOfNonseparatingStars G block ab C live ca cb near
    refine ⟨T.toFinset,?_,?_,fun v hv => subT (Set.mem_toFinset.mp hv)⟩
    · simpa only [Set.ncard_eq_toFinset_card'] using size p q pq T neT tp tq bound
    · intro w hw
      have incl : G.neighborFinset w ⊆ H.neighborFinset w := by
        intro t ht
        have e := (G.mem_neighborFinset ..).1 ht
        exact (H.mem_neighborFinset ..).2 (contains w t e (safe w (Set.mem_toFinset.mp hw) t e))
      have deg : G.degree w ≤ H.degree w := by
        simpa only [card_neighborFinset_eq_degree] using Finset.card_le_card incl
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (floor w).trans deg⟩
  let X := {v : V | v ∈ S ∧ v ≠ a ∧ v ≠ b}
  obtain ⟨i,hi,ia,ib⟩ := inside
  obtain ⟨L,nL,qL,sideL⟩ := bank X ⟨i,hi,ia,ib⟩ (fun h => h.2.1 rfl) (fun h => h.2.2 rfl) (by
    intro x hx y xy
    by_contra! miss
    exact gap x hx.1 hx.2.1 hx.2.2 y (fun h => miss.1 ⟨h,miss.2⟩) xy)
  obtain ⟨R,nR,qR,sideR⟩ := bank Sᶜ outside (fun h => h ha) (fun h => h hb) (by
    intro x hx y xy
    by_contra! miss
    exact gap y (by simpa using miss.1) miss.2.1 miss.2.2 x hx xy.symm)
  have disj : Disjoint L R := Finset.disjoint_left.mpr fun _ hL hR => sideR _ hR (sideL _ hL).1
  have count := Finset.card_le_card (Finset.union_subset qL qR)
  rw [Finset.card_union_of_disjoint disj] at count
  have highCount : 2 * k ≤ Q.card := by omega
  obtain ⟨J,sub,bJ,edges⟩ := spanningNonseparatingEdges G block
  have another (t r : V) (tr : t ≠ r) : ∃ b, H.Adj t b ∧ b ≠ r := by
    have many : 1 < (G.neighborFinset t).card := by rw [card_neighborFinset_eq_degree]; have := floor t; omega
    obtain ⟨y,hy,yr⟩ := Finset.exists_mem_ne many r
    have yt := ((G.mem_neighborFinset ..).1 hy).ne.symm
    let P : Set V := {t,r}
    obtain ⟨x,hx,xr,u,hu,xu⟩ := bJ r P (by simp [P]) ⟨t,by simp [P],tr⟩ ⟨y,by simp [P,yt,yr]⟩
    have xt : x = t := by simpa [P,xr] using hx
    exact ⟨u,xt ▸ contains x u (sub xu) (edges x u xu),fun e => hu (by simp [P,e])⟩
  have base (t : V) : 2 ≤ H.degree t := by
    have r : ∃ r : V, t ≠ r := by
      by_cases h : t = a
      · exact ⟨b,h ▸ ab.ne⟩
      · exact ⟨a,h⟩
    obtain ⟨r,tr⟩ := r
    obtain ⟨u,tu,_⟩ := another t r tr
    obtain ⟨v,tv,vu⟩ := another t u tu.ne
    rw [← card_neighborFinset_eq_degree]
    exact Finset.one_lt_card.mpr
      ⟨v,(H.mem_neighborFinset ..).2 tv,u,(H.mem_neighborFinset ..).2 tu,vu⟩
  have point (w : V) : 2 + (if w ∈ Q then 1 else 0) ≤ H.degree w := by
    by_cases hw : w ∈ Q
    · simpa [hw] using (Finset.mem_filter.mp hw).2
    · simpa [hw] using base w
  have total := Finset.sum_le_sum (s := Finset.univ) (fun w _ => point w)
  simp [Finset.sum_add_distrib,H.sum_degrees_eq_twice_card_edges] at total
  exact ⟨highCount, by omega⟩

/-- An adjacent separating pair in a four-cycle-free block forces at least
fourteen vertices of degree at least three in any graph containing every
nonseparating edge, and at least seven more edges than vertices. -/
theorem twoBankCore {V : Type*} [Fintype V]
    (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (floor : ∀ t, 3 ≤ G.degree t)
    (unique : ∀ {x y p q : V}, x ≠ y → G.Adj x p → G.Adj y p →
      G.Adj x q → G.Adj y q → p = q)
    (block : ∀ (t : V) (S : Set V), t ∈ S → (∃ x ∈ S, x ≠ t) → (∃ y, y ∉ S) →
      ∃ x ∈ S, x ≠ t ∧ ∃ y ∉ S, G.Adj x y)
    (contains : ∀ a b, G.Adj a b →
      (∀ S : Set V, a ∈ S → b ∈ S → (∃ x ∈ S, x ≠ a ∧ x ≠ b) → (∃ y, y ∉ S) →
        ∃ x ∈ S, x ≠ a ∧ x ≠ b ∧ ∃ y ∉ S, G.Adj x y) → H.Adj a b)
    {a b : V} (ab : G.Adj a b) (S : Set V) (ha : a ∈ S) (hb : b ∈ S)
    (inside : ∃ x ∈ S, x ≠ a ∧ x ≠ b) (outside : ∃ y, y ∉ S)
    (gap : ∀ x ∈ S, x ≠ a → x ≠ b → ∀ y ∉ S, ¬ G.Adj x y) :
    14 ≤ (Finset.univ.filter (fun v => 3 ≤ H.degree v)).card ∧
      Fintype.card V + 7 ≤ H.edgeFinset.card :=
  twoBankCount G H floor (bankSeven G floor unique) block contains ab S ha hb inside outside gap


/-- Two simple terminal paths with disjoint interiors realize the sum of their
lengths as a simple cycle, subject only to the sharp minimum length three. -/
theorem joinTerminalPaths {V : Type*} {G : SimpleGraph V} {a b : V}
    (p q : G.Walk a b) (hp : p.IsPath) (hq : q.IsPath)
    (overlap : ∀ x, x ∈ p.support → x ∈ q.support → x = a ∨ x = b)
    (size : 3 ≤ p.length + q.length) :
    ∃ c : G.Walk a a, c.IsCycle ∧ c.length = p.length + q.length := by
  let r := q.reverse
  have hr : r.IsPath := hq.reverse
  have freshP : a ∉ p.support.tail := by
    have hn := hp.support_nodup
    rw [← p.cons_tail_support, List.nodup_cons] at hn
    exact hn.1
  have freshR : b ∉ r.support.tail := by
    have hn := hr.support_nodup
    rw [← r.cons_tail_support, List.nodup_cons] at hn
    exact hn.1
  have disj : p.support.tail.Disjoint r.support.tail := by
    intro x xp xr
    have pMem : x ∈ p.support := by rw [← p.cons_tail_support]; exact List.mem_cons_of_mem _ xp
    have rMem : x ∈ r.support := by rw [← r.cons_tail_support]; exact List.mem_cons_of_mem _ xr
    have qMem : x ∈ q.support := by simpa [r,Walk.support_reverse] using rMem
    rcases overlap x pMem qMem with h | h
    · exact freshP (h ▸ xp)
    · exact freshR (h ▸ xr)
  have l : r.length = q.length := q.length_reverse
  exact ⟨p.append r, hp.isCycle_append hr disj (by omega), by simp [l]⟩

/-- A component behind a separation pair has a neighbor at either terminal.
No degree or finiteness hypothesis is needed. -/
theorem componentSeesBoth {V : Type*} {G : SimpleGraph V}
    (block : ∀ (t : V) (S : Set V), t ∈ S → (∃ x ∈ S, x ≠ t) → (∃ y, y ∉ S) →
      ∃ x ∈ S, x ≠ t ∧ ∃ y ∉ S, G.Adj x y)
    {a b : V} (ab : a ≠ b) (C : Set V) (u : C) (ca : a ∉ C) (cb : b ∉ C)
    (boundary : ∀ x ∈ C, ∀ y, G.Adj x y → y ∈ C ∨ y = a ∨ y = b) :
    (∃ x : C, (G.induce C).Reachable u x ∧ G.Adj a x) ∧
    (∃ y : C, (G.induce C).Reachable u y ∧ G.Adj b y) := by
  classical
  let J := G.induce C
  let R := {v : V | ∃ hv : v ∈ C, J.Reachable u ⟨v,hv⟩}
  have ru : u.val ∈ R := ⟨u.property,Reachable.refl _⟩
  have sub : R ⊆ C := fun _ h => h.choose
  have closes {x y : V} (rx : x ∈ R) (yx : y ∈ C) (xy : G.Adj x y) : y ∈ R := by
    obtain ⟨xc,ux⟩ := rx
    have e : J.Adj ⟨x,xc⟩ ⟨y,yx⟩ := xy
    exact ⟨yx,ux.trans e.reachable⟩
  have see (s t : V) (st : s ≠ t) (cs : s ∉ C) (ct : t ∉ C)
      (ends : ∀ x ∈ C, ∀ y, G.Adj x y → y ∈ C ∨ y = s ∨ y = t) :
      ∃ x : C, J.Reachable u x ∧ G.Adj t x := by
    let S := {v : V | v = s ∨ v ∈ R}
    have out : t ∉ S := fun h => h.elim st.symm (fun tr => ct (sub tr))
    obtain ⟨x,hx,xs,y,hy,edge⟩ := block s S (Or.inl rfl)
      ⟨u.val, Or.inr ru, fun h => cs (h ▸ u.property)⟩ ⟨t,out⟩
    have rx : x ∈ R := hx.resolve_left xs
    obtain ⟨xc,ux⟩ := rx
    have et : y = t := by
      rcases ends x xc y edge with yc | ys | yt
      · exact (hy (Or.inr (closes ⟨xc,ux⟩ yc edge))).elim
      · exact (hy (Or.inl ys)).elim
      · exact yt
    exact ⟨⟨x,xc⟩,ux,et ▸ edge.symm⟩
  exact ⟨see b a ab.symm cb ca (fun x hx y e => (boundary x hx y e).imp_right Or.symm),
    see a b ab ca cb boundary⟩


/-- A proper region with a thin terminal in a block has connected interior:
every interior component must meet both terminal neighborhoods. -/
theorem thinBankConnected {V : Type*} {G : SimpleGraph V}
    (block : ∀ (t : V) (S : Set V), t ∈ S → (∃ x ∈ S, x ≠ t) → (∃ y, y ∉ S) →
      ∃ x ∈ S, x ≠ t ∧ ∃ y ∉ S, G.Adj x y)
    {a b : V} (ab : a ≠ b) (C : Set V) (live : C.Nonempty) (ca : a ∉ C) (cb : b ∉ C)
    (boundary : ∀ x ∈ C, ∀ y, G.Adj x y → y ∈ C ∨ y = a ∨ y = b)
    (thin : ¬ ((∃ x ∈ C, ∃ y ∈ C, x ≠ y ∧ G.Adj a x ∧ G.Adj a y) ∧
       (∃ x ∈ C, ∃ y ∈ C, x ≠ y ∧ G.Adj b x ∧ G.Adj b y))) :
    (G.induce C).Connected := by
  obtain ⟨v,hv⟩ := live
  apply (G.induce C).connected_iff_exists_forall_reachable.mpr
  refine ⟨⟨v,hv⟩,?_⟩
  intro w
  by_contra far
  obtain ⟨⟨x,vx,ax⟩,⟨s,vs,bs⟩⟩ := componentSeesBoth block ab C ⟨v,hv⟩ ca cb boundary
  obtain ⟨⟨y,wy,ay⟩,⟨t,wt,bt⟩⟩ := componentSeesBoth block ab C w ca cb boundary
  have different {u z : C} (vu : (G.induce C).Reachable ⟨v,hv⟩ u)
      (wz : (G.induce C).Reachable w z) : u.val ≠ z.val := by
    intro eq
    have h : u = z := Subtype.ext eq
    exact far ((h ▸ vu).trans wz.symm)
  exact thin ⟨⟨x,x.property,y,y.property,different vx wy,ax,ay⟩,
    ⟨s,s.property,t,t.property,different vs wt,bs,bt⟩⟩


private theorem noIsolatedRegion {V : Type*} {G : SimpleGraph V}
    (block : ∀ (z : V) (S : Set V), z ∈ S → (∃ x ∈ S, x ≠ z) → (∃ y, y ∉ S) →
      ∃ x ∈ S, x ≠ z ∧ ∃ y ∉ S, G.Adj x y)
    (r : V) (D : Set V) (outside : ∃ t ∉ D, t ≠ r)
    (avoids : r ∉ D) (closed : ∀ x ∈ D, ∀ y, G.Adj x y → y ∈ D ∨ y = r) :
    ∀ v, v ∉ D := by
  intro v hv
  let S : Set V := {x | x = r ∨ x ∈ D}
  obtain ⟨t,ht,tr⟩ := outside
  obtain ⟨x,hx,xr,y,hy,e⟩ := block r S (Or.inl rfl)
    ⟨v,Or.inr hv,fun eq => avoids (eq ▸ hv)⟩ ⟨t,fun h => h.elim tr ht⟩
  exact hy ((closed x (hx.resolve_left xr) y e).symm)

private theorem bankNeighbor {V : Type*} {G : SimpleGraph V}
    (block : ∀ (z : V) (S : Set V), z ∈ S → (∃ x ∈ S, x ≠ z) → (∃ y, y ∉ S) →
      ∃ x ∈ S, x ≠ z ∧ ∃ y ∉ S, G.Adj x y)
    {a b : V} (ab : a ≠ b) (C : Set V) (ne : C.Nonempty) (ca : a ∉ C) (cb : b ∉ C)
    (bound : ∀ x ∈ C, ∀ y, G.Adj x y → y ∈ C ∨ y = a ∨ y = b) :
    ∃ u : C, G.Adj a u.val := by
  obtain ⟨v,hv⟩ := ne
  by_contra! h
  apply noIsolatedRegion block b C ⟨a,ca,ab⟩ cb _ v hv
  intro x hx y xy
  rcases bound x hx y xy with hy | eq | eq
  · exact Or.inl hy
  · exact (h ⟨x,hx⟩ (eq ▸ xy.symm)).elim
  · exact Or.inr eq

theorem sheetQuiet {V W : Type*} {G : SimpleGraph V} {K : SimpleGraph W}
    (block : ∀ (z : V) (S : Set V), z ∈ S → (∃ x ∈ S, x ≠ z) → (∃ y, y ∉ S) →
      ∃ x ∈ S, x ≠ z ∧ ∃ y ∉ S, G.Adj x y)
    {a b : V} (ab : a ≠ b) (C : Set V) (ca : a ∉ C) (cb : b ∉ C)
    (bound : ∀ x ∈ C, ∀ y, G.Adj x y → y ∈ C ∨ y = a ∨ y = b)
    (A B z : W) (f : C → W) (r : V)
    (rf : ∀ u : C, f u = z ↔ u.val = r) (ra : A = z → a = r) (rb : B = z → b = r)
    (ef : ∀ u v : C, G.Adj u.val v.val → K.Adj (f u) (f v))
    (ea : ∀ u : C, G.Adj u.val a → K.Adj (f u) A)
    (eb : ∀ u : C, G.Adj u.val b → K.Adj (f u) B)
    (P : W → Prop) (same : ∀ u v, u ≠ z → v ≠ z → K.Adj u v → P u → P v)
    (pa : A ≠ z → ¬ P A) (pb : B ≠ z → ¬ P B) :
    ∀ u : C, f u ≠ z → ¬ P (f u) := by
  intro u uz bad
  let D := {v : V | ∃ hv : v ∈ C, f ⟨v,hv⟩ ≠ z ∧ P (f ⟨v,hv⟩)}
  have outside : ∃ t ∉ D, t ≠ r := by
    by_cases ar : a = r
    · exact ⟨b,fun ⟨h,_⟩ => cb h,ar ▸ ab.symm⟩
    · exact ⟨a,fun ⟨h,_⟩ => ca h,ar⟩
  apply noIsolatedRegion block r D outside _ _ u.val ⟨u.property,uz,bad⟩
  · exact fun ⟨h,hz,_⟩ => hz ((rf ⟨r,h⟩).2 rfl)
  · rintro x ⟨hx,hz,px⟩ y xy
    rcases bound x hx y xy with iy | rfl | rfl
    · by_cases yr : y = r
      · exact .inr yr
      · have ok := mt (rf ⟨y,iy⟩).1 yr
        exact .inl ⟨iy,ok,same _ _ hz ok (ef ⟨x,hx⟩ ⟨y,iy⟩ xy) px⟩
    · by_cases az : A = z
      · exact .inr (ra az)
      · exact (pa az (same _ _ hz az (ea ⟨x,hx⟩ xy) px)).elim
    · by_cases bz : B = z
      · exact .inr (rb bz)
      · exact (pb bz (same _ _ hz bz (eb ⟨x,hx⟩ xy) px)).elim

theorem doubleBank {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (block : ∀ (z : V) (S : Set V), z ∈ S → (∃ x ∈ S, x ≠ z) → (∃ y, y ∉ S) →
      ∃ x ∈ S, x ≠ z ∧ ∃ y ∉ S, G.Adj x y)
    {a b : V} (ab : G.Adj a b) (C : Set V) (ne : C.Nonempty) (ca : a ∉ C) (cb : b ∉ C)
    (bound : ∀ x ∈ C, ∀ y, G.Adj x y → y ∈ C ∨ y = a ∨ y = b)
    (deg : ∀ u : C, 3 ≤ G.degree u.val) :
    let W := Bool ⊕ (Bool × C)
    let π : W → V := Sum.elim (fun t : Bool => if t then b else a) (fun p : Bool × C => p.2.val)
    ∃ K : SimpleGraph W,
      (∀ u v, K.Adj u v → G.Adj (π u) (π v)) ∧
      (∀ i j x y, K.Adj (.inr (i,x)) (.inr (j,y)) → i = j) ∧
      (∀ u : W, 3 ≤ K.degree u) ∧
      (∀ (z : W) (S : Set W), z ∈ S → (∃ x ∈ S, x ≠ z) → (∃ y, y ∉ S) →
        ∃ x ∈ S, x ≠ z ∧ ∃ y ∉ S, K.Adj x y) ∧
      Fintype.card W = 2 + 2 * Fintype.card C := by
  classical
  let W := Bool ⊕ (Bool × C)
  let π : W → V := Sum.elim (fun t : Bool => if t then b else a) (fun p : Bool × C => p.2.val)
  let tag : W → Option Bool := Sum.elim (fun _ => none) (fun p => some p.1)
  let K : SimpleGraph W := {
    Adj := fun u v => G.Adj (π u) (π v) ∧ (tag u = none ∨ tag v = none ∨ tag u = tag v)
    symm := ⟨fun _ _ h => ⟨h.1.symm,h.2.elim (fun e => .inr (.inl e))
      (fun h' => h'.elim Or.inl (fun e => .inr (.inr e.symm)))⟩⟩
    loopless := ⟨fun _ h => h.1.ne rfl⟩ }
  let : DecidableRel K.Adj := fun _ _ => Classical.propDecidable _
  let A : W := .inl false
  let B : W := .inl true
  let f (i : Bool) (x : C) : W := .inr (i,x)
  have AB : K.Adj A B := ⟨ab,Or.inl rfl⟩
  have ef (i : Bool) (x y : C) (xy : G.Adj x.val y.val) : K.Adj (f i x) (f i y) :=
    ⟨xy,Or.inr (Or.inr rfl)⟩
  have ea (i : Bool) (x : C) (xa : G.Adj x.val a) : K.Adj (f i x) A := ⟨xa,Or.inr (Or.inl rfl)⟩
  have eb (i : Bool) (x : C) (xb : G.Adj x.val b) : K.Adj (f i x) B := ⟨xb,Or.inr (Or.inl rfl)⟩
  refine ⟨K,fun _ _ h => h.1,?_,?_,?_,?_⟩
  · intro i j x y e
    have h := e.2
    simpa [tag] using h
  · have three {v i j k : W} (vi : K.Adj v i) (vj : K.Adj v j) (vk : K.Adj v k)
        (ij : i ≠ j) (ik : i ≠ k) (jk : j ≠ k) : 3 ≤ K.degree v := by
      have sub : ({i,j,k} : Finset W) ⊆ K.neighborFinset v := by
        intro t ht
        simp only [Finset.mem_insert,Finset.mem_singleton] at ht
        rcases ht with rfl | rfl | rfl <;> simpa
      have h := Finset.card_le_card sub
      simpa [ij,ik,jk,card_neighborFinset_eq_degree] using h
    intro w
    rcases w with (u | ⟨i,x⟩)
    · cases u
      · obtain ⟨x,hx⟩ := bankNeighbor block ab.ne C ne ca cb bound
        exact three AB (ea false x hx.symm).symm (ea true x hx.symm).symm
          (by simp [B,f]) (by simp [B,f]) (fun e => Bool.noConfusion (congrArg Prod.fst (Sum.inr.inj e)))
      · obtain ⟨x,hx⟩ := bankNeighbor block ab.ne.symm C ne cb ca
          (fun v hv w vw => (bound v hv w vw).imp_right Or.symm)
        exact three AB.symm (eb false x hx.symm).symm (eb true x hx.symm).symm
          (by simp [A,f]) (by simp [A,f]) (fun e => Bool.noConfusion (congrArg Prod.fst (Sum.inr.inj e)))
    · let lift (v : V) : W := if h : v ∈ C then f i ⟨v,h⟩ else if v = a then A else B
      have maps (v : V) (hv : G.Adj x.val v) : K.Adj (f i x) (lift v) ∧ π (lift v) = v := by
        rcases bound x.val x.property v hv with h | rfl | rfl
        · simp only [lift,dif_pos h]
          exact ⟨ef i x ⟨v,h⟩ hv,rfl⟩
        · simp only [lift,dif_neg ca]
          exact ⟨ea i x hv,rfl⟩
        · simp only [lift,dif_neg cb,if_neg ab.ne.symm]
          exact ⟨eb i x hv,rfl⟩
      have h := Finset.card_le_card_of_injOn (s := G.neighborFinset x.val)
        (t := K.neighborFinset (f i x)) lift
        (fun v hv => (K.mem_neighborFinset ..).2 (maps v ((G.mem_neighborFinset ..).1 hv)).1)
        (fun v hv w hw e => (maps v ((G.mem_neighborFinset ..).1 hv)).2.symm.trans
          ((congrArg π e).trans (maps w ((G.mem_neighborFinset ..).1 hw)).2))
      exact (deg x).trans (by simpa only [card_neighborFinset_eq_degree] using h)
  · intro z S hz inside outside
    by_contra! none
    have agree (x y : W) (xz : x ≠ z) (yz : y ≠ z) (e : K.Adj x y) : x ∈ S ↔ y ∈ S := by
      constructor
      · intro hx
        by_contra hy
        exact none x hx xz y hy e
      · intro hy
        by_contra hx
        exact none y hy yz x hx e.symm
    let T : W := if A = z then B else A
    let P (w : W) := ¬ (w ∈ S ↔ T ∈ S)
    have pa (az : A ≠ z) : ¬ P A := by simp [P,T,az]
    have pb (bz : B ≠ z) : ¬ P B := by
      by_cases az : A = z
      · simp [P,T,az]
      · simpa [P,T,az] using (agree B A bz az AB.symm)
    have stable (u v : W) (hu : u ≠ z) (hv : v ≠ z) (uv : K.Adj u v) (h : P u) : P v :=
      fun e => h ((agree u v hu hv uv).trans e)
    have clear (w : W) (wz : w ≠ z) : ¬ P w := by
      rcases w with (t | ⟨i,x⟩)
      · cases t
        · exact pa wz
        · exact pb wz
      · let r : V := match z with
          | .inl t => if t then b else a
          | .inr (j,y) => if i = j then y.val else a
        have rf (u : C) : f i u = z ↔ u.val = r := by
          have ua : u.val ≠ a := fun e => ca (e ▸ u.property)
          have ub : u.val ≠ b := fun e => cb (e ▸ u.property)
          cases z with
          | inl t =>
            cases t
            · exact ⟨(fun e => nomatch e), fun e => (ua e).elim⟩
            · exact ⟨(fun e => nomatch e), fun e => (ub e).elim⟩
          | inr p =>
            rcases p with ⟨j,y⟩
            by_cases h : i = j
            · subst j
              change f i u = f i y ↔ u.val = (if i = i then y.val else a)
              rw [if_pos rfl]
              exact ⟨fun e => congrArg Subtype.val (congrArg Prod.snd (Sum.inr.inj e)),
                fun e => congrArg (f i) (Subtype.ext e)⟩
            · change f i u = f j y ↔ u.val = (if i = j then y.val else a)
              rw [if_neg h]
              exact ⟨fun e => (h (congrArg Prod.fst (Sum.inr.inj e))).elim, fun e => (ua e).elim⟩
        have ra (e : A = z) : a = r := by subst z; rfl
        have rb (e : B = z) : b = r := by subst z; rfl
        exact sheetQuiet block ab.ne C ca cb bound A B z (f i) r rf ra rb (ef i) (ea i) (eb i)
          P stable pa pb x wz
    obtain ⟨x,hx,xz⟩ := inside
    obtain ⟨y,hy⟩ := outside
    have yz : y ≠ z := fun e => hy (e ▸ hz)
    exact hy ((Classical.not_not.mp (clear y yz)).mpr ((Classical.not_not.mp (clear x xz)).mp hx))
  · simp [Fintype.card_sum,Fintype.card_prod]


/-- A walk avoiding both terminals stays on one sheet. -/
private theorem freeWalkOneSheet {X : Type*} {K : SimpleGraph (Bool ⊕ (Bool × X))}
    (separate : ∀ i j (x y : X), K.Adj (.inr (i,x)) (.inr (j,y)) → i = j)
    {u v} (p : K.Walk u v) (free : ∀ t, Sum.inl t ∉ p.support) :
    ∃ i, ∀ j (x : X), Sum.inr (j,x) ∈ p.support → j = i := by
  induction p with
  | @nil u =>
    cases u with
    | inl t => exact False.elim (free t (by simp))
    | inr z => exact ⟨z.1, fun j x h => by simpa using congrArg Prod.fst (Sum.inr.inj (List.mem_singleton.mp h))⟩
  | @cons u v w e q ih =>
    obtain ⟨i,qi⟩ := ih (fun t h => free t (List.mem_cons_of_mem _ h))
    cases u with
    | inl t => exact False.elim (free t (by simp))
    | inr u =>
      cases v with
      | inl t => exact False.elim (free t (List.mem_cons_of_mem _ q.start_mem_support))
      | inr v =>
        have vi := qi v.1 v.2 q.start_mem_support
        have ui := separate u.1 v.1 u.2 v.2 e
        refine ⟨i, fun j x h => ?_⟩
        rcases List.mem_cons.mp h with eq | hq
        · exact (congrArg Prod.fst (Sum.inr.inj eq)).trans (ui.trans vi)
        · exact qi j x hq

/-- A simple path ending at its only terminal stays on one sheet up to that terminal. -/
private theorem oneTerminalPathSheet {X : Type*} {K : SimpleGraph (Bool ⊕ (Bool × X))}
    (separate : ∀ i j (x y : X), K.Adj (.inr (i,x)) (.inr (j,y)) → i = j)
    {u t} (p : K.Walk u (.inl t)) (hp : p.IsPath)
    (only : ∀ k, k ≠ t → Sum.inl k ∉ p.support) :
    ∃ i, ∀ j (x : X), Sum.inr (j,x) ∈ p.support → j = i := by
  by_cases empty : p.Nil
  · cases empty
    exact ⟨false, by simp⟩
  let last := p.adj_penultimate empty
  have eq : p.dropLast.concat last = p := Walk.concat_dropLast last
  have ht := ((Walk.concat_isPath_iff last).mp (eq ▸ hp)).2
  have free (k : Bool) : Sum.inl k ∉ p.dropLast.support := by
    by_cases kt : k = t
    · simpa [kt] using ht
    · exact fun h => only k kt (eq ▸ p.dropLast.support_subset_support_concat last h)
  obtain ⟨i,hi⟩ := freeWalkOneSheet separate p.dropLast free
  refine ⟨i, fun j x hx => hi j x ?_⟩
  rw [← eq, Walk.support_concat] at hx
  simpa using hx

private theorem terminalPathSheet {X : Type*} {K : SimpleGraph (Bool ⊕ (Bool × X))}
    (separate : ∀ i j (x y : X), K.Adj (.inr (i,x)) (.inr (j,y)) → i = j)
    {s t : Bool} (st : s ≠ t) (p : K.Walk (.inl s) (.inl t)) (hp : p.IsPath) :
    ∃ i, ∀ j (x : X), Sum.inr (j,x) ∈ p.support → j = i := by
  cases p with
  | nil => exact False.elim (st rfl)
  | cons e q =>
    obtain ⟨hq,hs⟩ := (Walk.cons_isPath_iff e q).mp hp
    obtain ⟨i,hi⟩ := oneTerminalPathSheet separate q hq (fun k kt => by
      have eq : k = s := by cases k <;> cases s <;> cases t <;> simp_all
      simpa [eq] using hs)
    exact ⟨i, fun j x hx => hi j x (by simpa using hx)⟩

private theorem missedTerminalSheet {X : Type*} {K : SimpleGraph (Bool ⊕ (Bool × X))}
    (separate : ∀ i j (x y : X), K.Adj (.inr (i,x)) (.inr (j,y)) → i = j)
    {w} (c : K.Walk w w) (hc : c.IsCycle) {t : Bool} (miss : Sum.inl t ∉ c.support) :
    ∃ i, ∀ j (x : X), Sum.inr (j,x) ∈ c.support → j = i := by
  classical
  by_cases other : Sum.inl (!t) ∈ c.support
  · let d := c.rotate (.inl (!t)) other
    have hd : d.IsCycle := hc.rotate other
    have miss' : Sum.inl t ∉ d.support := by simpa [d] using miss
    suffices h : ∃ i, ∀ j (x : X), Sum.inr (j,x) ∈ d.support → j = i by simpa [d] using h
    generalize hD : d = r at hd miss' ⊢
    cases r with
    | nil => exact False.elim (hd.not_nil .nil)
    | cons e q =>
      have hq := (Walk.cons_isCycle_iff _ _).mp hd |>.1
      obtain ⟨i,hi⟩ := oneTerminalPathSheet separate q hq (fun k hk => by
        have eq : k = t := by cases k <;> cases t <;> simp_all
        exact fun h => miss' (List.mem_cons_of_mem _ (eq ▸ h)))
      exact ⟨i, fun j x hx => hi j x (by simpa using hx)⟩
  · apply freeWalkOneSheet separate c
    intro k
    have opt : k = t ∨ k = !t := by cases k <;> cases t <;> decide
    rcases opt with rfl | rfl <;> assumption

private theorem oneSheetInjective {V : Type*} {a b : V} (ab : a ≠ b) {S : Set V}
    (ha : a ∉ S) (hb : b ∉ S) (L : List (Bool ⊕ (Bool × S)))
    (one : ∃ i, ∀ j (x : S), Sum.inr (j,x) ∈ L → j = i) :
    Set.InjOn (Sum.elim (fun t : Bool => if t then b else a) (fun p : Bool × S => p.2.val))
      {z | z ∈ L} := by
  obtain ⟨i,hi⟩ := one
  intro u hu v hv eq
  rcases u with s | ⟨j,x⟩ <;> rcases v with t | ⟨k,y⟩
  · cases s <;> cases t <;> simp_all
  · cases s <;> simp_all [Subtype.coe_prop]
  · cases t
    · exact (ha ((show x.val = a from eq) ▸ x.property)).elim
    · exact (hb ((show x.val = b from eq) ▸ x.property)).elim
  · have jk := (hi j x hu).trans (hi k y hv).symm
    exact congrArg Sum.inr (Prod.ext jk (Subtype.ext eq))

private theorem pathMapOn {U V : Type*} {K : SimpleGraph U} {G : SimpleGraph V} (f : K →g G)
    {u v} (p : K.Walk u v) (hp : p.IsPath) (inj : Set.InjOn f {x | x ∈ p.support}) :
    (p.map f).IsPath := by
  apply Walk.IsPath.mk'
  rw [Walk.support_map]
  exact hp.support_nodup.map_on (fun a ha b hb => @inj a ha b hb)

private theorem cycleMapOn {U V : Type*} {K : SimpleGraph U} {G : SimpleGraph V} (f : K →g G)
    {u} (p : K.Walk u u) (hp : p.IsCycle) (inj : Set.InjOn f {x | x ∈ p.support}) :
    (p.map f).IsCycle := by
  rw [Walk.isCycle_iff_isPath_tail_and_le_length]
  refine ⟨?_,by simpa using hp.three_le_length⟩
  cases p with
  | nil => exact False.elim (hp.not_nil .nil)
  | cons e q =>
    have hq := ((Walk.cons_isCycle_iff _ _).mp hp).1
    simpa using pathMapOn f q hq (fun x hx y hy =>
      @inj x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy))

/-- A simple cycle in two copies of a bank glued at two terminals projects to a
cycle of the same length, or to two nontrivial terminal paths in the bank whose
lengths add to the cycle length. The projected paths may coincide. -/
theorem doubleCycle {V : Type*} (G : SimpleGraph V) {a b : V} (ab : a ≠ b)
    (S : Set V) (ha : a ∉ S) (hb : b ∉ S) (K : SimpleGraph (Bool ⊕ (Bool × S)))
    (project : ∀ u v, K.Adj u v → G.Adj
      (Sum.elim (fun t : Bool => if t then b else a) (fun p : Bool × S => p.2.val) u)
      (Sum.elim (fun t : Bool => if t then b else a) (fun p : Bool × S => p.2.val) v))
    (separate : ∀ i j (x y : S), K.Adj (.inr (i,x)) (.inr (j,y)) → i = j)
    {w} (c : K.Walk w w) (hc : c.IsCycle) :
    (∃ v, ∃ d : G.Walk v v, d.IsCycle ∧ d.length = c.length) ∨
    ∃ p q : G.Walk a b, p.IsPath ∧ q.IsPath ∧ 2 ≤ p.length ∧ 2 ≤ q.length ∧
      p.length + q.length = c.length ∧
      (∀ x ∈ p.support, x ≠ a → x ≠ b → x ∈ S) ∧
      (∀ x ∈ q.support, x ≠ a → x ≠ b → x ∈ S) := by
  classical
  let f : K →g G := ⟨Sum.elim (fun t : Bool => if t then b else a) (fun z : Bool × S => z.2.val),
    fun {u v} => project u v⟩
  by_cases one : ∃ i, ∀ j (x : S), Sum.inr (j,x) ∈ c.support → j = i
  · exact Or.inl ⟨f w,c.map f,cycleMapOn f c hc (oneSheetInjective ab ha hb _ one),by simp⟩
  have allTerm (t : Bool) : Sum.inl t ∈ c.support :=
    by_contra fun missing => one (missedTerminalSheet separate c hc missing)
  let d := c.rotate (.inl false) (allTerm false)
  have hd : d.IsCycle := hc.rotate (allTerm false)
  have bmem : Sum.inl true ∈ d.support := by simpa [d] using allTerm true
  let P := d.takeUntil (.inl true) bmem
  let Q := d.dropUntil (.inl true) bmem
  have decomp : P.append Q = d := Walk.take_spec d bmem
  have hp : P.IsPath := hd.isPath_takeUntil bmem
  have hq : Q.IsPath :=
    (show (P.append Q).IsCycle from decomp ▸ hd).isPath_of_append_right
      (Walk.not_nil_of_ne (by simp))
  let p : G.Walk a b := P.map f
  let q : G.Walk a b := (Q.map f).reverse
  have ip := oneSheetInjective ab ha hb _ (terminalPathSheet separate (by decide) P hp)
  have iq := oneSheetInjective ab ha hb _ (terminalPathSheet separate (by decide) Q hq)
  have ph : p.IsPath := pathMapOn f P hp ip
  have qh : q.IsPath := (pathMapOn f Q hq iq).reverse
  have sum : p.length + q.length = c.length := by
    have lp : p.length = P.length := Walk.length_map f P
    have lq : q.length = Q.length := (Walk.length_reverse (Q.map f)).trans (Walk.length_map f Q)
    calc
      p.length + q.length = (P.append Q).length := by rw [lp,lq,Walk.length_append]
      _ = c.length := by rw [decomp]; exact Walk.length_rotate _ _ _
  have nonzero (r : G.Walk a b) : r.length ≠ 0 :=
    fun h => ab (Walk.length_eq_zero_iff.mp h).eq
  have small (r s : G.Walk a b) (hs : s.IsPath) (one : r.length = 1)
      (sum : r.length + s.length = c.length) :
      ∃ v, ∃ e : G.Walk v v, e.IsCycle ∧ e.length = c.length := by
    let edge := Walk.adj_of_length_eq_one one
    let e := s.cons edge.symm
    have size : e.length = c.length := by simpa [e,one,Nat.add_comm] using sum
    refine ⟨b,e,Walk.isCycle_iff_isPath_tail_and_le_length.mpr ⟨?_,size ▸ hc.three_le_length⟩,size⟩
    simpa [e] using hs
  by_cases po : p.length = 1
  · exact Or.inl (small p q qh po sum)
  by_cases qo : q.length = 1
  · exact Or.inl (small q p ph qo (Nat.add_comm _ _ ▸ sum))
  have bank {u v} (r : K.Walk u v) :
      ∀ x ∈ (r.map f).support, x ≠ a → x ≠ b → x ∈ S := by
    intro x hx xa xb
    rw [Walk.support_map,List.mem_map] at hx
    obtain ⟨t,_,rfl⟩ := hx
    rcases t with t | ⟨j,y⟩
    · cases t
      · exact (xa rfl).elim
      · exact (xb rfl).elim
    · exact y.property
  refine Or.inr ⟨p,q,ph,qh,?_,?_,sum,bank P,?_⟩
  · have := nonzero p
    omega
  · have := nonzero q
    omega
  · intro x hx
    have eq : q.support = (Q.map f).support.reverse := Walk.support_reverse (Q.map f)
    exact bank Q x (List.mem_reverse.mp (eq ▸ hx))


/-- Doubling a bank strictly smaller than half the graph after removing the terminals
forces two proper detours of complementary lengths in a minimal counterexample. -/
theorem forcedBankDetours {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (block : ∀ (z : V) (S : Set V), z ∈ S → (∃ x ∈ S, x ≠ z) → (∃ y, y ∉ S) →
      ∃ x ∈ S, x ≠ z ∧ ∃ y ∉ S, G.Adj x y)
    {a b : V} (ab : G.Adj a b) (C : Set V) (ne : C.Nonempty) (ca : a ∉ C) (cb : b ∉ C)
    (bound : ∀ x ∈ C, ∀ y, G.Adj x y → y ∈ C ∨ y = a ∨ y = b)
    (deg : ∀ u : C, 3 ≤ G.degree u.val) (small : 2*C.ncard+2 < Fintype.card V)
    (absent : ¬ ∃ (k : ℕ) (w : V) (c : G.Walk w w), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2^k)
    (smaller : ∀ (W : Type) [Fintype W] (K : SimpleGraph W) [DecidableRel K.Adj],
      Fintype.card W < Fintype.card V → 3 ≤ K.minDegree →
      (∀ (z : W) (S : Set W), z ∈ S → (∃ x ∈ S, x ≠ z) → (∃ y, y ∉ S) →
        ∃ x ∈ S, x ≠ z ∧ ∃ y ∉ S, K.Adj x y) →
      ∃ (k : ℕ) (w : W) (c : K.Walk w w), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2^k) :
    ∃ (k : ℕ) (p q : G.Walk a b), 2 ≤ k ∧ p.IsPath ∧ q.IsPath ∧ 2 ≤ p.length ∧
      2 ≤ q.length ∧ p.length + q.length = 2^k ∧
      (∀ x ∈ p.support, x ≠ a → x ≠ b → x ∈ C) ∧
      (∀ x ∈ q.support, x ≠ a → x ≠ b → x ∈ C) := by
  classical
  obtain ⟨K,proj,sep,low,blk,order⟩ := doubleBank G block ab C ne ca cb bound deg
  have lt : Fintype.card (Bool ⊕ (Bool × C)) < Fintype.card V := by
    rw [order, Set.fintypeCard_eq_ncard, Nat.add_comm]
    exact small
  let : Nonempty (Bool ⊕ (Bool × C)) := ⟨Sum.inl false⟩
  obtain ⟨k,w,c,hk,hc,len⟩ := smaller _ K lt (K.le_minDegree_of_forall_le_degree 3 low) blk
  rcases doubleCycle G ab.ne C ca cb K proj sep c hc with
    ⟨v,d,hd,eq⟩ | ⟨p,q,hp,hq,lp,lq,sum,pc,qc⟩
  · exact (absent ⟨k,v,d,hk,hd,eq.trans len⟩).elim
  · exact ⟨k,p,q,hk,hp,hq,lp,lq,sum.trans len,pc,qc⟩


theorem closeMarkedDetour {V : Type*} {G : SimpleGraph V} {a b : V}
    (ab : G.Adj a b) (p : G.Walk a b) (hp : p.IsPath) (long : 2 ≤ p.length) :
    ∃ c : G.Walk b b, c.IsCycle ∧ c.length = p.length + 1 ∧ s(a,b) ∈ c.edges := by
  refine ⟨.cons ab.symm p, ?_, rfl, ?_⟩
  · apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
    constructor
    · rw [Walk.tail_cons]
      exact (Walk.isPath_copy _ _ _).mpr hp
    · simp only [Walk.length_cons]
      omega
  · rw [show s(a,b) = s(b,a) from Sym2.eq_swap]
    simp

/-- At an uncovered edge in a counterexample, a proper detour has length
neither a power of two nor one less than a power of two. -/
theorem markedDetourAvoids {V : Type*} {G : SimpleGraph V} {a b : V}
    (ab : G.Adj a b)
    (absent : ¬ ∃ (k : ℕ) (w : V) (c : G.Walk w w), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2^k)
    (uncov : ¬ ∃ (k : ℕ) (w : V) (c : G.Walk w w),
      1 ≤ k ∧ c.IsCycle ∧ c.length = 2^k+1 ∧ s(a,b) ∈ c.edges)
    (p : G.Walk a b) (hp : p.IsPath) (long : 2 ≤ p.length) :
    (∀ k : ℕ, 1 ≤ k → p.length ≠ 2^k) ∧
      (∀ k : ℕ, 2 ≤ k → p.length+1 ≠ 2^k) ∧ 5 ≤ p.length := by
  obtain ⟨c,cyc,len,mark⟩ := closeMarkedDetour ab p hp long
  have plain (k : ℕ) (hk : 1 ≤ k) (h : p.length = 2^k) : False :=
    uncov ⟨k,b,c,hk,cyc,by omega,mark⟩
  have succ (k : ℕ) (hk : 2 ≤ k) (h : p.length+1 = 2^k) : False :=
    absent ⟨k,b,c,hk,cyc,len.trans h⟩
  refine ⟨plain,succ,?_⟩
  have h₂ := plain 1 (by decide)
  have h₃ := succ 2 (by decide)
  have h₄ := plain 2 (by decide)
  norm_num at h₂ h₃ h₄
  omega

theorem separatedSumAvoids {V : Type*} {G : SimpleGraph V} {a b : V}
    (absent : ¬ ∃ (k : ℕ) (w : V) (c : G.Walk w w), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2^k)
    {C D : Set V} (dis : Disjoint C D) (p q : G.Walk a b) (hp : p.IsPath) (hq : q.IsPath)
    (pc : ∀ x ∈ p.support, x ≠ a → x ≠ b → x ∈ C)
    (qd : ∀ x ∈ q.support, x ≠ a → x ≠ b → x ∈ D)
    {k : ℕ} (hk : 2 ≤ k) : p.length + q.length ≠ 2^k := by
  intro eq
  have enough : 4 ≤ 2^k := (Nat.pow_le_pow_right (by decide : 0 < 2) hk : 2^2 ≤ 2^k)
  obtain ⟨c,hc,len⟩ := joinTerminalPaths p q hp hq (by
    intro x xp xq
    by_contra! h
    exact Set.disjoint_left.mp dis (pc x xp h.1 h.2) (qd x xq h.1 h.2)) (by omega)
  exact absent ⟨k,a,c,hk,hc,len.trans eq⟩

theorem detourLengthBound {V : Type*} [Finite V] {G : SimpleGraph V} {a b : V}
    {C : Set V} (p : G.Walk a b) (hp : p.IsPath)
    (pc : ∀ x ∈ p.support, x ≠ a → x ≠ b → x ∈ C) : p.length ≤ C.ncard + 1 := by
  classical
  have sub : (↑p.support.toFinset : Set V) ⊆ insert a (insert b C) := by
    intro x hx
    by_cases h : x = a
    · exact Or.inl h
    by_cases h' : x = b
    · exact Or.inr (Or.inl h')
    · exact Or.inr (Or.inr (pc x (by simpa using hx) h h'))
  have lower := Set.ncard_le_ncard sub
  have upper₁ := Set.ncard_insert_le a (insert b C)
  have upper₂ := Set.ncard_insert_le b C
  rw [Set.ncard_coe_finset,List.toFinset_card_of_nodup hp.support_nodup,p.length_support] at lower
  omega

/-- A dyadic sum of two admissible private path lengths first occurs
at scale sixteen. The two lengths straddle the preceding power of two,
and both miss that power by at least two. -/
theorem privatePairGap {p q k : ℕ} (hp : 5 ≤ p) (hq : 5 ≤ q) (hk : 2 ≤ k)
    (pDyadic : ∀ j : ℕ, 2 ≤ j → p ≠ 2^j)
    (pBefore : ∀ j : ℕ, 2 ≤ j → p+1 ≠ 2^j)
    (qBefore : ∀ j : ℕ, 2 ≤ j → q+1 ≠ 2^j)
    (sum : p+q = 2^k) :
    4 ≤ k ∧ min p q + 2 ≤ 2^(k-1) ∧ 2^(k-1)+2 ≤ max p q := by
  have scale : 4 ≤ k := by
    by_contra! h
    have e : k = 2 ∨ k = 3 := by omega
    rcases e with rfl | rfl <;> omega
  have next : 2^k = 2^(k-1) * 2 := by
    conv_lhs => rw [show k = (k-1)+1 by omega,pow_succ]
  have h1 := pDyadic (k-1) (by omega)
  have h2 := pBefore (k-1) (by omega)
  have h3 := qBefore (k-1) (by omega)
  refine ⟨scale,?_⟩
  rcases le_total p q with h | h
  · rw [min_eq_left h,max_eq_right h]
    omega
  · rw [min_eq_right h,max_eq_left h]
    omega


/-- The two lengths forced by a doubled bank are exclusive to that bank:
a realization of either length outside it would complete a dyadic cycle. -/
theorem exclusiveDetours {V : Type*} [Finite V] {G : SimpleGraph V} {a b : V}
    (ab : G.Adj a b)
    (absent : ¬ ∃ (k : ℕ) (w : V) (c : G.Walk w w), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2^k)
    (uncov : ¬ ∃ (k : ℕ) (w : V) (c : G.Walk w w),
      1 ≤ k ∧ c.IsCycle ∧ c.length = 2^k+1 ∧ s(a,b) ∈ c.edges)
    (C : Set V)
    (witness : ∃ (k : ℕ) (p q : G.Walk a b), 2 ≤ k ∧ p.IsPath ∧ q.IsPath ∧
      2 ≤ p.length ∧ 2 ≤ q.length ∧ p.length + q.length = 2^k ∧
      (∀ x ∈ p.support, x ≠ a → x ≠ b → x ∈ C) ∧
      (∀ x ∈ q.support, x ≠ a → x ≠ b → x ∈ C)) :
    let realizes (D : Set V) (l : ℕ) := ∃ p : G.Walk a b, p.IsPath ∧ p.length = l ∧
      ∀ x ∈ p.support, x ≠ a → x ≠ b → x ∈ D
    9 ≤ C.ncard ∧ ∃ (k s t : ℕ), 4 ≤ k ∧ 5 ≤ s ∧ s+2 ≤ 2^(k-1) ∧ 2^(k-1)+2 ≤ t ∧ s+t = 2^k ∧
      realizes C s ∧ realizes C t ∧
      ∀ D : Set V, Disjoint C D → ¬ realizes D s ∧ ¬ realizes D t := by
  classical
  dsimp only
  obtain ⟨k,p,q,hk,hp,hq,plen,qlen,sum,pc,qc⟩ := witness
  obtain ⟨pd,ps,p5⟩ := markedDetourAvoids ab absent uncov p hp plen
  obtain ⟨_,qs,q5⟩ := markedDetourAvoids ab absent uncov q hq qlen
  obtain ⟨k4,low,high⟩ := privatePairGap p5 q5 hk
    (fun j hj => pd j (by omega)) ps qs sum
  have mid : (2:ℕ)^3 ≤ 2^(k-1) := Nat.pow_le_pow_right (by decide) (by omega)
  have lp := detourLengthBound p hp pc
  have lq := detourLengthBound q hq qc
  have privateP (D : Set V) (dis : Disjoint C D) :
      ¬ ∃ r : G.Walk a b, r.IsPath ∧ r.length = p.length ∧
        ∀ x ∈ r.support, x ≠ a → x ≠ b → x ∈ D := by
    rintro ⟨r,hr,eq,rD⟩
    exact separatedSumAvoids absent dis q r hq hr qc rD hk (by omega)
  have privateQ (D : Set V) (dis : Disjoint C D) :
      ¬ ∃ r : G.Walk a b, r.IsPath ∧ r.length = q.length ∧
        ∀ x ∈ r.support, x ≠ a → x ≠ b → x ∈ D := by
    rintro ⟨r,hr,eq,rD⟩
    exact separatedSumAvoids absent dis p r hp hr pc rD hk (by omega)
  rcases le_total p.length q.length with lt | gt
  · rw [min_eq_left lt] at low
    rw [max_eq_right lt] at high
    exact ⟨by omega,k,p.length,q.length,k4,p5,low,high,sum,⟨p,hp,rfl,pc⟩,⟨q,hq,rfl,qc⟩,
      fun D dis => ⟨privateP D dis,privateQ D dis⟩⟩
  · rw [min_eq_right gt] at low
    rw [max_eq_left gt] at high
    exact ⟨by omega,k,q.length,p.length,k4,q5,low,high,by omega,⟨q,hq,rfl,qc⟩,⟨p,hp,rfl,pc⟩,
      fun D dis => ⟨privateQ D dis,privateP D dis⟩⟩


/-- Retaining an arbitrary collection of regions at an adjacent pair preserves
the no-cut-vertex property. No connectedness assumption on the interior is needed. -/
theorem inducedBankBlock {V : Type*} {G : SimpleGraph V}
    (block : ∀ (t : V) (S : Set V), t ∈ S → (∃ x ∈ S, x ≠ t) → (∃ y, y ∉ S) →
      ∃ x ∈ S, x ≠ t ∧ ∃ y ∉ S, G.Adj x y)
    {a b : V} (ab : G.Adj a b) (C : Set V)
    (boundary : ∀ x ∈ C, ∀ y, G.Adj x y → y ∈ C ∨ y = a ∨ y = b) :
    let U := insert a (insert b C)
    ∀ (z : U) (S : Set U), z ∈ S → (∃ x ∈ S, x ≠ z) → (∃ y, y ∉ S) →
      ∃ x ∈ S, x ≠ z ∧ ∃ y ∉ S, (G.induce U).Adj x y := by
  classical
  intro U
  let A : U := ⟨a, Set.mem_insert ..⟩
  let B : U := ⟨b, Set.mem_insert_of_mem a (Set.mem_insert ..)⟩
  intro z S zs xin yout
  obtain ⟨t,tz,term⟩ : ∃ t : U, t ≠ z ∧ (t = A ∨ t = B) := by
    by_cases az : A = z
    · exact ⟨B,fun h => ab.ne (congrArg Subtype.val (az.trans h.symm)),Or.inr rfl⟩
    · exact ⟨A,az,Or.inl rfl⟩
  let f (v : V) : U := if hv : v ∈ U then ⟨v,hv⟩ else t
  have ff (u : U) : f u.val = u := dif_pos u.property
  have fo {u : V} (h : u ∉ U) : f u = t := dif_neg h
  have stays {x : V} (h : x ≠ z.val) : f x ≠ z := by
    by_cases hx : x ∈ U
    · intro eq
      exact h (congrArg Subtype.val ((ff ⟨x,hx⟩).symm.trans eq))
    · exact (fo hx) ▸ tz
  have terminal {u v : V} (hu : u ∈ U) (hv : v ∉ U) (e : G.Adj u v) :
      (⟨u,hu⟩ : U) = A ∨ (⟨u,hu⟩ : U) = B := by
    have h : u = a ∨ u = b ∨ u ∈ C := by simpa [U] using hu
    rcases h with ha | hb | hc
    · exact Or.inl (Subtype.ext ha)
    · exact Or.inr (Subtype.ext hb)
    · rcases boundary u hc v e with vc | va | vb
      · exact (hv (Set.mem_insert_of_mem a (Set.mem_insert_of_mem b vc))).elim
      · exact (hv (va ▸ A.property)).elim
      · exact (hv (vb ▸ B.property)).elim
  have terminalEdge {u v : U} (hu : u = A ∨ u = B) (hv : v = A ∨ v = B)
      (ne : u ≠ v) : (G.induce U).Adj u v := by
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · exact (ne rfl).elim
    · exact ab
    · exact ab.symm
    · exact (ne rfl).elim
  have maps {x y : V} (xy : G.Adj x y) (ne : f x ≠ f y) : (G.induce U).Adj (f x) (f y) := by
    by_cases hx : x ∈ U <;> by_cases hy : y ∈ U
    · rw [ff ⟨x,hx⟩,ff ⟨y,hy⟩]
      exact xy
    · exact terminalEdge ((ff ⟨x,hx⟩).symm ▸ terminal hx hy xy) ((fo hy).symm ▸ term) ne
    · exact terminalEdge ((fo hx).symm ▸ term) ((ff ⟨y,hy⟩).symm ▸ terminal hy hx xy.symm) ne
    · exact (ne ((fo hx).trans (fo hy).symm)).elim
  obtain ⟨p,ps,pz⟩ := xin
  obtain ⟨q,qs⟩ := yout
  let T := {v : V | f v ∈ S}
  have inT {u : U} : u.val ∈ T ↔ u ∈ S := by simp only [T, Set.mem_ofPred_eq, ff]
  obtain ⟨x,hx,xz,y,hy,xy⟩ := block z.val T (inT.mpr zs)
    ⟨p.val,inT.mpr ps,fun eq => pz (Subtype.ext eq)⟩ ⟨q.val,fun h => qs (inT.mp h)⟩
  exact ⟨f x,hx,stays xz,f y,hy,maps xy (fun e => hy (e ▸ hx : f y ∈ S))⟩


/-- In a smallest counterexample among blocks, the terminals of a proper
closed side cannot both have two distinct neighbors in its interior. -/
theorem thinBankTerminal {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (small : ∀ (W : Type) [Fintype W] (K : SimpleGraph W) [DecidableRel K.Adj],
      Fintype.card W < Fintype.card V → 3 ≤ K.minDegree →
      (∀ (t : W) (S : Set W), t ∈ S → (∃ x ∈ S, x ≠ t) → (∃ y, y ∉ S) →
        ∃ x ∈ S, x ≠ t ∧ ∃ y ∉ S, K.Adj x y) →
      ∃ (k : ℕ) (v : W) (c : K.Walk v v), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2^k)
    (none : ¬ ∃ (k : ℕ) (v : V) (c : G.Walk v v), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2^k)
    (block : ∀ (t : V) (S : Set V), t ∈ S → (∃ x ∈ S, x ≠ t) → (∃ y, y ∉ S) →
      ∃ x ∈ S, x ≠ t ∧ ∃ y ∉ S, G.Adj x y)
    {a b : V} (ab : G.Adj a b) (C : Set V) (ca : a ∉ C) (cb : b ∉ C)
    (bound : ∀ x ∈ C, ∀ y, G.Adj x y → y ∈ C ∨ y = a ∨ y = b)
    (degree : ∀ u ∈ C, 3 ≤ G.degree u) (proper : C.ncard + 2 < Fintype.card V) :
    ¬ ((∃ x ∈ C, ∃ y ∈ C, x ≠ y ∧ G.Adj a x ∧ G.Adj a y) ∧
       (∃ x ∈ C, ∃ y ∈ C, x ≠ y ∧ G.Adj b x ∧ G.Adj b y)) := by
  classical
  let U : Set V := insert a (insert b C)
  let K := G.induce U
  have mem {x : V} (h : x ∈ C) : x ∈ U := by simp [U,h]
  let A : U := ⟨a,by simp [U]⟩
  let B : U := ⟨b,by simp [U]⟩
  have cardU : Fintype.card U < Fintype.card V := by
    rw [Set.fintypeCard_eq_ncard]
    exact lt_of_le_of_lt ((Set.ncard_insert_le a (insert b C)).trans
      (by have := Set.ncard_insert_le b C; omega)) proper
  have three {t u v w : U} (tu : K.Adj t u) (tv : K.Adj t v) (tw : K.Adj t w)
      (uv : u ≠ v) (uw : u ≠ w) (vw : v ≠ w) : 3 ≤ K.degree t := by
    have sub : ({u,v,w} : Finset U) ⊆ K.neighborFinset t := by
      intro x hx
      simp only [Finset.mem_insert,Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> simpa
    simpa [uv,uw,vw,card_neighborFinset_eq_degree] using Finset.card_le_card sub
  have atEnd (t u : U) (tu : K.Adj t u) (out : u.val ∉ C)
      (two : ∃ x ∈ C, ∃ y ∈ C, x ≠ y ∧ G.Adj t.val x ∧ G.Adj t.val y) : 3 ≤ K.degree t := by
    obtain ⟨x,cx,y,cy,xy,tx,ty⟩ := two
    let X : U := ⟨x,mem cx⟩
    let Y : U := ⟨y,mem cy⟩
    exact three (v := X) (w := Y) tu tx ty
      (fun e => out ((congrArg Subtype.val e : u.val = x) ▸ cx))
      (fun e => out ((congrArg Subtype.val e : u.val = y) ▸ cy))
      (fun e => xy (congrArg Subtype.val e))
  rintro ⟨atA,atB⟩
  have allDeg (t : U) : 3 ≤ K.degree t := by
    rcases show t.val = a ∨ t.val = b ∨ t.val ∈ C from t.property with ha | hb | hc
    · rw [show t = A from Subtype.ext ha]
      exact atEnd A B ab cb atA
    · rw [show t = B from Subtype.ext hb]
      exact atEnd B A ab.symm ca atB
    · have inside : G.neighborSet t.val ⊆ U := by
        intro v tv
        rcases bound _ hc _ tv with h | h | h <;> simp [U,h]
      let neighborLift (y : V) : U := if hy : y ∈ U then ⟨y,hy⟩ else A
      have project {v : V} (tv : G.Adj t.val v) : (neighborLift v).val = v := by
        simp [neighborLift,inside tv]
      have kept {v : V} (tv : G.Adj t.val v) : K.Adj t (neighborLift v) := by
        change G.Adj t.val (neighborLift v).val
        rwa [project tv]
      have count := Finset.card_le_card_of_injOn (s := G.neighborFinset t.val)
        (t := K.neighborFinset t) neighborLift
        (fun v h => (K.mem_neighborFinset ..).mpr (kept ((G.mem_neighborFinset ..).mp h)))
        (fun v hv w hw eq => (project ((G.mem_neighborFinset ..).mp hv)).symm.trans
          ((congrArg Subtype.val eq).trans (project ((G.mem_neighborFinset ..).mp hw))))
      exact (degree _ hc).trans (by simpa only [card_neighborFinset_eq_degree] using count)
  let : Nonempty U := ⟨A⟩
  obtain ⟨k,v,c,hk,hc,hl⟩ := small U K cardU (K.le_minDegree_of_forall_le_degree 3 allDeg) (inducedBankBlock block ab C bound)
  let lift := (Embedding.induce (G := G) U).toHom
  exact none ⟨k,v.val,c.map lift,hk,hc.map Subtype.val_injective,(c.length_map _).trans hl⟩


/-- At an adjacent two-vertex cut of a smallest block counterexample, each
proper nonempty region has connected interior and a terminal with exactly one
neighbor there. This includes equal-size sides. -/
theorem bankTopology {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (small : ∀ (W : Type) [Fintype W] (K : SimpleGraph W) [DecidableRel K.Adj],
      Fintype.card W < Fintype.card V → 3 ≤ K.minDegree →
      (∀ (t : W) (S : Set W), t ∈ S → (∃ x ∈ S, x ≠ t) → (∃ y, y ∉ S) →
        ∃ x ∈ S, x ≠ t ∧ ∃ y ∉ S, K.Adj x y) →
      ∃ (k : ℕ) (v : W) (c : K.Walk v v), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2^k)
    (none : ¬ ∃ (k : ℕ) (v : V) (c : G.Walk v v), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2^k)
    (block : ∀ (t : V) (S : Set V), t ∈ S → (∃ x ∈ S, x ≠ t) → (∃ y, y ∉ S) →
      ∃ x ∈ S, x ≠ t ∧ ∃ y ∉ S, G.Adj x y)
    {a b : V} (ab : G.Adj a b) (C : Set V) (live : C.Nonempty) (ca : a ∉ C) (cb : b ∉ C)
    (bound : ∀ x ∈ C, ∀ y, G.Adj x y → y ∈ C ∨ y = a ∨ y = b)
    (degree : ∀ u ∈ C, 3 ≤ G.degree u) (proper : C.ncard + 2 < Fintype.card V) :
    (G.induce C).Connected ∧ ((∃! x : C, G.Adj a x.val) ∨ (∃! x : C, G.Adj b x.val)) := by
  classical
  have thin := thinBankTerminal G small none block ab C ca cb bound degree proper
  refine ⟨thinBankConnected block ab.ne C live ca cb bound thin,?_⟩
  obtain ⟨v,hv⟩ := live
  obtain ⟨⟨x,_,ax⟩,⟨y,_,by'⟩⟩ := componentSeesBoth block ab.ne C ⟨v,hv⟩ ca cb bound
  have two {t : V} (u : C) (tu : G.Adj t u.val) (h : ¬ ∃! z : C, G.Adj t z.val) :
      ∃ i ∈ C, ∃ j ∈ C, i ≠ j ∧ G.Adj t i ∧ G.Adj t j := by
    by_contra missing
    apply h
    refine ⟨u,tu,?_⟩
    intro z tz
    by_contra ne
    exact missing ⟨z,z.property,u,u.property,fun e => ne (Subtype.ext e),tz,tu⟩
  by_contra! missing
  exact thin ⟨two x ax missing.1,two y by' missing.2⟩


/-- If a terminal has only one neighbor inside a bank, suppressing the
terminal induces a block with a virtual edge from that neighbor to the other
terminal. Every remaining interior vertex retains its minimum degree. -/
theorem suppressedBankStrong {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (block : ∀ (z : V) (S : Set V), z ∈ S → (∃ x ∈ S, x ≠ z) → (∃ y, y ∉ S) →
      ∃ x ∈ S, x ≠ z ∧ ∃ y ∉ S, G.Adj x y)
    {a b x : V} (C : Set V) (xc : x ∈ C) (bc : b ∉ C)
    (bound : ∀ u ∈ C, ∀ v, G.Adj u v → v ∈ C ∨ v = a ∨ v = b)
    (unique : ∀ y ∈ C, G.Adj a y → y = x) (deg : ∀ u : C, 3 ≤ G.degree u.val) :
    let W := {v : V // v ∈ insert b C}
    let X : W := ⟨x,Or.inr xc⟩
    let B : W := ⟨b,Or.inl rfl⟩
    let D : Set W := {w | w.val ∈ C ∧ w.val ≠ x}
    ∃ H : SimpleGraph W, H.Adj X B ∧
      (∀ u v, H.Adj u v → G.Adj u.val v.val ∨ (u = X ∧ v = B) ∨ (u = B ∧ v = X)) ∧
      (∀ u : D, 3 ≤ H.degree u.val) ∧
      (∀ (z : W) (S : Set W), z ∈ S → (∃ u ∈ S, u ≠ z) → (∃ v, v ∉ S) →
        ∃ u ∈ S, u ≠ z ∧ ∃ v ∉ S, H.Adj u v) ∧
      (∀ u ∈ D, ∀ v : W, H.Adj u v → v ∈ D ∨ v = X ∨ v = B) ∧
      D.ncard + 1 = C.ncard ∧ (∀ u v : W, G.Adj u.val v.val → H.Adj u v) := by
  classical
  let W := {v : V // v ∈ insert b C}
  let X : W := ⟨x,Or.inr xc⟩
  let B : W := ⟨b,Or.inl rfl⟩
  let D : Set W := {w | w.val ∈ C ∧ w.val ≠ x}
  let R := C \ {x}
  have xb : x ≠ b := fun e => bc (e ▸ xc)
  have border (u : V) (ur : u ∈ R) (v : V) (uv : G.Adj u v) : v ∈ R ∨ v = x ∨ v = b := by
    rcases bound u ur.1 v uv with vc | rfl | rfl
    · by_cases vx : v = x
      · exact .inr (.inl vx)
      · exact .inl ⟨vc,vx⟩
    · exact (ur.2 (unique u ur.1 uv.symm)).elim
    · exact .inr (.inr rfl)
  let H : SimpleGraph W := {
    Adj := fun u v => G.Adj u.val v.val ∨ (u = X ∧ v = B) ∨ (u = B ∧ v = X)
    symm := ⟨fun _ _ h => h.elim (fun e => .inl e.symm)
      (fun h => .inr (h.elim (fun e => .inr e.symm) (fun e => .inl e.symm)))⟩
    loopless := ⟨fun u h => h.elim (fun e => e.ne rfl) (fun h => h.elim
      (fun e => xb (congrArg Subtype.val (e.1.symm.trans e.2)))
      (fun e => xb (congrArg Subtype.val (e.2.symm.trans e.1))))⟩ }
  let : DecidableRel H.Adj := fun _ _ => Classical.propDecidable _
  have XB : H.Adj X B := Or.inr (Or.inl ⟨rfl,rfl⟩)
  have classify (v : W) : v ∈ D ∨ v = X ∨ v = B := by
    rcases v.property with vb | vc
    · exact .inr (.inr (Subtype.ext vb))
    · by_cases vx : v.val = x
      · exact .inr (.inl (Subtype.ext vx))
      · exact .inl ⟨vc,vx⟩
  refine ⟨H,XB,fun _ _ e => e,?_,?_,fun _ _ v _ => classify v,?_,fun _ _ e => Or.inl e⟩
  · intro u
    let lift (v : V) : W := if h : v ∈ insert b C then ⟨v,h⟩ else B
    have maps (v : V) (uv : G.Adj u.val.val v) : H.Adj u.val (lift v) ∧ (lift v).val = v := by
      have vr : v ∈ insert b C := by
        rcases border u.val.val u.property v uv with h | rfl | rfl
        · exact .inr h.1
        · exact .inr xc
        · exact .inl rfl
      simp only [lift,dif_pos vr]
      exact ⟨.inl uv,trivial⟩
    have count := Finset.card_le_card_of_injOn (s := G.neighborFinset u.val.val)
      (t := H.neighborFinset u.val) lift
      (fun v hv => (H.mem_neighborFinset ..).2 (maps v ((G.mem_neighborFinset ..).1 hv)).1)
      (fun v hv w hw e => (maps v ((G.mem_neighborFinset ..).1 hv)).2.symm.trans
        ((congrArg Subtype.val e).trans (maps w ((G.mem_neighborFinset ..).1 hw)).2))
    exact (deg ⟨u.val.val,u.property.1⟩).trans (by simpa only [card_neighborFinset_eq_degree] using count)
  · intro z S hz inner outer
    by_contra! none
    have agree (u v : W) (uz : u ≠ z) (vz : v ≠ z) (uv : H.Adj u v) : u ∈ S ↔ v ∈ S := by
      constructor
      · intro hu
        by_contra hv
        exact none u hu uz v hv uv
      · intro hv
        by_contra hu
        exact none v hv vz u hu uv.symm
    let anchor := if X = z then B else X
    let P (w : W) := ¬ (w ∈ S ↔ anchor ∈ S)
    have px (nz : X ≠ z) : ¬ P X := by simp [P,anchor,nz]
    have pb (nz : B ≠ z) : ¬ P B := by
      by_cases xz : X = z
      · simp [P,anchor,xz]
      · simpa [P,anchor,xz] using agree B X nz xz XB.symm
    let f (t : R) : W := ⟨t.val,Or.inr t.property.1⟩
    have quiet := sheetQuiet block xb R (fun h => h.2 rfl) (fun h => bc h.1) border X B z f z.val
      (fun _ => ⟨fun e => congrArg Subtype.val e, fun e => Subtype.ext e⟩)
      (fun e => congrArg Subtype.val e) (fun e => congrArg Subtype.val e)
      (fun _ _ e => Or.inl e) (fun _ e => Or.inl e) (fun _ e => Or.inl e) P
      (fun u v uz vz uv h eq => h ((agree u v uz vz uv).trans eq)) px pb
    have clear (w : W) (wz : w ≠ z) : ¬P w := by
      rcases classify w with mem | rfl | rfl
      · exact quiet ⟨w.val,mem⟩ wz
      · exact px wz
      · exact pb wz
    obtain ⟨u,hu,uz⟩ := inner
    obtain ⟨v,hv⟩ := outer
    have vz : v ≠ z := fun e => hv (e ▸ hz)
    exact hv ((Classical.not_not.mp (clear v vz)).mpr ((Classical.not_not.mp (clear u uz)).mp hu))
  · have im : Subtype.val '' D = R := by
      ext v
      exact ⟨fun ⟨w,hw,e⟩ => e ▸ hw,fun h => ⟨⟨v,Or.inr h.1⟩,h,rfl⟩⟩
    rw [← Set.ncard_image_of_injective D Subtype.val_injective,im]
    exact Set.ncard_sdiff_singleton_add_one xc


/-- A virtual edge between the marked endpoint and the unique bank neighbor can be
expanded to two edges. Any longer lift contains the original marked edge. -/
theorem suppressedBankCycle {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W)
    (f : W ↪ V) (x b : W) {a : V} (ab : G.Adj a (f b)) (ax : G.Adj a (f x))
    (miss : ∀ t, f t ≠ a)
    (real : ∀ u v, H.Adj u v → G.Adj (f u) (f v) ∨ (u = x ∧ v = b) ∨ (u = b ∧ v = x))
    {w : W} (c : H.Walk w w) (hc : c.IsCycle) :
    ∃ v, ∃ d : G.Walk v v, d.IsCycle ∧
      (d.length = c.length ∨ (d.length = c.length + 1 ∧ s(a,f b) ∈ d.edges)) := by
  apply liftMergedCycle G H f b ab miss _ _ c hc
  · intro u v ub vb edge
    rcases real u v edge with e | ⟨_,eq⟩ | ⟨eq,_⟩
    · exact e
    · exact (vb eq).elim
    · exact (ub eq).elim
  · intro u edge
    rcases real b u edge with e | ⟨_,eq⟩ | ⟨_,eq⟩
    · exact Or.inr e
    · exact (edge.ne eq.symm).elim
    · exact Or.inl (eq ▸ ax)


/-- At an uncovered edge of a smallest block counterexample, each end has
exactly one neighbor in every proper nonempty side. Suppressing a terminal
with a unique neighbor would otherwise leave a smaller minimum-degree-three
block, in which a dyadic cycle lifts unchanged or to a covered marked edge. -/
theorem bankTopologyUncovered {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (small : ∀ (W : Type) [Fintype W] (K : SimpleGraph W) [DecidableRel K.Adj],
      Fintype.card W < Fintype.card V → 3 ≤ K.minDegree →
      (∀ (t : W) (S : Set W), t ∈ S → (∃ x ∈ S, x ≠ t) → (∃ y, y ∉ S) →
        ∃ x ∈ S, x ≠ t ∧ ∃ y ∉ S, K.Adj x y) →
      ∃ (k : ℕ) (v : W) (c : K.Walk v v), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2^k)
    (none : ¬ ∃ (k : ℕ) (v : V) (c : G.Walk v v), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2^k)
    (block : ∀ (t : V) (S : Set V), t ∈ S → (∃ x ∈ S, x ≠ t) → (∃ y, y ∉ S) →
      ∃ x ∈ S, x ≠ t ∧ ∃ y ∉ S, G.Adj x y)
    {a b : V} (ab : G.Adj a b) (C : Set V) (live : C.Nonempty) (ca : a ∉ C) (cb : b ∉ C)
    (bound : ∀ x ∈ C, ∀ y, G.Adj x y → y ∈ C ∨ y = a ∨ y = b)
    (degree : ∀ u ∈ C, 3 ≤ G.degree u) (proper : C.ncard + 2 < Fintype.card V)
    (uncov : ¬ ∃ (k : ℕ) (v : V) (c : G.Walk v v), 1 ≤ k ∧ c.IsCycle ∧
      c.length = 2^k+1 ∧ s(a,b) ∈ c.edges) :
    (G.induce C).Connected ∧ (∃! x : C, G.Adj a x.val) ∧ (∃! x : C, G.Adj b x.val) := by
  classical
  obtain ⟨conn,thin⟩ := bankTopology G small none block ab C live ca cb bound degree proper
  have other {s t : V} (st : G.Adj s t) (cs : s ∉ C) (ct : t ∉ C)
      (ends : ∀ u ∈ C, ∀ v, G.Adj u v → v ∈ C ∨ v = s ∨ v = t)
      (unmarked : ¬ ∃ (k : ℕ) (v : V) (c : G.Walk v v), 1 ≤ k ∧ c.IsCycle ∧
        c.length = 2^k+1 ∧ s(s,t) ∈ c.edges)
      (atS : ∃! x : C, G.Adj s x.val) : ∃! y : C, G.Adj t y.val := by
    obtain ⟨x,sx,only⟩ := atS
    obtain ⟨_,y,_,ty⟩ := componentSeesBoth block st.ne C x cs ct ends
    refine ⟨y,ty,?_⟩
    intro v tv
    by_contra vy
    have xt : ¬ G.Adj x.val t := by
      intro e
      let c : G.Walk s s := .cons st (.cons e.symm (.cons sx.symm .nil))
      have hc : c.IsCycle := by
        apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
        constructor
        · simp [c,Walk.cons_isPath_iff,st.ne.symm,sx.ne.symm,e.ne.symm]
        · exact (by decide : 3 ≤ 3)
      exact unmarked ⟨1,s,c,by decide,hc,rfl,by simp [c]⟩
    let W := {i : V // i ∈ insert t C}
    let X : W := ⟨x.val,Or.inr x.property⟩
    let T : W := ⟨t,Or.inl rfl⟩
    let into (i : C) : W := ⟨i.val,Or.inr i.property⟩
    obtain ⟨H,XT,real,off,blockH,_,_,embed⟩ :=
      suppressedBankStrong G block C x.property ct ends
        (fun i hi si => congrArg Subtype.val (only ⟨i,hi⟩ si)) (fun i => degree i.val i.property)
    let : DecidableRel H.Adj := fun _ _ => Classical.propDecidable _
    have three {i j l m : W} (ij : H.Adj i j) (il : H.Adj i l) (im : H.Adj i m)
        (jl : j ≠ l) (jm : j ≠ m) (lm : l ≠ m) : 3 ≤ H.degree i := by
      have sub : ({j,l,m} : Finset W) ⊆ H.neighborFinset i := by
        intro w hw
        simp only [Finset.mem_insert,Finset.mem_singleton] at hw
        rcases hw with rfl | rfl | rfl <;> simpa
      simpa [jl,jm,lm,card_neighborFinset_eq_degree] using Finset.card_le_card sub
    have project {u w : W} (e : u = w) : u.val = w.val := congrArg (fun z : W => z.val) e
    have different {u : C} (tu : G.Adj t u.val) (e : X = into u) : False := by
      have eq : x.val = u.val := project e
      exact xt (eq.symm ▸ tu.symm)
    have out {u : C} (e : T = into u) : False := by
      have eq : t = u.val := project e
      exact ct (eq.symm ▸ u.property)
    have atT : 3 ≤ H.degree T := three (j := X) (l := into v) (m := into y)
      XT.symm (embed _ _ tv) (embed _ _ ty)
      (different tv) (different ty) (fun eq => vy (Subtype.ext (project eq)))
    have depth : 1 < ((G.neighborFinset x.val).erase s).card := by
      rw [Finset.card_erase_of_mem ((G.mem_neighborFinset ..).2 sx.symm),card_neighborFinset_eq_degree]
      have := degree x.val x.property
      omega
    obtain ⟨i,hi,j,hj,ij⟩ := Finset.one_lt_card.mp depth
    have inside {u : V} (hu : u ∈ (G.neighborFinset x.val).erase s) :
        u ∈ C ∧ G.Adj x.val u := by
      obtain ⟨us,hu⟩ := Finset.mem_erase.mp hu
      have edge := (G.mem_neighborFinset ..).1 hu
      exact ⟨(ends x.val x.property u edge).resolve_right (fun h =>
        h.elim us (fun eq => xt (eq ▸ edge))),edge⟩
    obtain ⟨ci,xi⟩ := inside hi
    obtain ⟨cj,xj⟩ := inside hj
    have atX : 3 ≤ H.degree X := three (j := T) (l := into ⟨i,ci⟩) (m := into ⟨j,cj⟩)
      XT (embed _ _ xi) (embed _ _ xj)
      out out (fun eq => ij (project eq))
    have allDeg (w : W) : 3 ≤ H.degree w := by
      rcases w.property with wt | wc
      · rw [show w = T from Subtype.ext wt]
        exact atT
      · by_cases h : w.val = x.val
        · rw [show w = X from Subtype.ext h]
          exact atX
        · exact off ⟨w,wc,h⟩
    have reduced : Fintype.card W < Fintype.card V := by
      change Fintype.card (insert t C : Set V) < _
      rw [Set.fintypeCard_eq_ncard]
      have := Set.ncard_insert_le t C
      omega
    let : Nonempty W := ⟨T⟩
    obtain ⟨k,w,c,hk,hc,hl⟩ := small W H reduced (H.le_minDegree_of_forall_le_degree 3 allDeg) blockH
    let f : W ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
    have miss (i : W) : f i ≠ s := fun h => i.property.elim
      (fun e => st.ne (h.symm.trans e)) (fun e => cs (h ▸ e))
    obtain ⟨u,d,hd,eq | ⟨eq,marked⟩⟩ := suppressedBankCycle G H f X T st sx miss real c hc
    · exact none ⟨k,u,d,hk,hd,eq.trans hl⟩
    · exact unmarked ⟨k,u,d,by omega,hd,by omega,marked⟩
  refine ⟨conn,?_⟩
  rcases thin with h | h
  · exact ⟨h,other ab ca cb bound uncov h⟩
  · have reverseUncov : ¬ ∃ (k : ℕ) (v : V) (c : G.Walk v v), 1 ≤ k ∧ c.IsCycle ∧
        c.length = 2^k+1 ∧ s(b,a) ∈ c.edges := by
      rintro ⟨k,v,c,hk,hc,hl,edge⟩
      exact uncov ⟨k,v,c,hk,hc,hl,(Sym2.eq_swap ..) ▸ edge⟩
    exact ⟨other ab.symm cb ca (fun u hu v uv => (bound u hu v uv).imp_right Or.symm) reverseUncov h,h⟩


/-- If each terminal has just one neighbor in each of its two complementary
regions, both ends of the separating edge have degree three. -/
theorem terminalDegrees {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {a b : V} (ab : G.Adj a b)
    (bank : ∀ C : Set V, C.Nonempty → a ∉ C → b ∉ C →
      (∀ x ∈ C, ∀ y, G.Adj x y → y ∈ C ∨ y = a ∨ y = b) →
      C.ncard + 2 < Fintype.card V →
      (∃! x : C, G.Adj a x.val) ∧ (∃! x : C, G.Adj b x.val))
    (S : Set V) (ha : a ∈ S) (hb : b ∈ S) (inside : ∃ x ∈ S, x ≠ a ∧ x ≠ b)
    (outside : ∃ y, y ∉ S)
    (gap : ∀ x ∈ S, x ≠ a → x ≠ b → ∀ y ∉ S, ¬ G.Adj x y) :
    G.degree a = 3 ∧ G.degree b = 3 := by
  classical
  let C := {v : V | v ∈ S ∧ v ≠ a ∧ v ≠ b}
  let D := Sᶜ
  obtain ⟨i,hi,ia,ib⟩ := inside
  obtain ⟨j,hj⟩ := outside
  have proper (T : Set V) (ta : a ∉ T) (tb : b ∉ T)
      (u : V) (ut : u ∉ T) (ua : u ≠ a) (ub : u ≠ b) :
      T.ncard + 2 < Fintype.card V := by
    have out : u ∉ insert a (insert b T) := by simp [ua,ub,ut]
    have lt := Set.ncard_lt_ncard (show insert a (insert b T) ⊂ Set.univ from
      ⟨Set.subset_univ _,fun back => out (back (Set.mem_univ u))⟩)
    rw [Set.ncard_insert_of_notMem (by simp [ab.ne,ta]),Set.ncard_insert_of_notMem tb,
      Set.ncard_univ,Nat.card_eq_fintype_card] at lt
    omega
  have ca : a ∉ C := fun h => h.2.1 rfl
  have cb : b ∉ C := fun h => h.2.2 rfl
  have da : a ∉ D := fun h => h ha
  have db : b ∉ D := fun h => h hb
  obtain ⟨auc,buc⟩ := bank C ⟨i,hi,ia,ib⟩ ca cb (by
    intro x hx y xy
    by_contra! miss
    exact gap x hx.1 hx.2.1 hx.2.2 y (fun h => miss.1 ⟨h,miss.2⟩) xy)
    (proper C ca cb j (fun h => hj h.1) (fun eq => hj (eq ▸ ha)) (fun eq => hj (eq ▸ hb)))
  obtain ⟨aud,bud⟩ := bank D ⟨j,hj⟩ da db (by
    intro x hx y xy
    by_contra! miss
    exact gap y (by simpa [D] using miss.1) miss.2.1 miss.2.2 x hx xy.symm)
    (proper D da db i (fun h => h hi) ia ib)
  have deg (t u : V) (tu : G.Adj t u) (uc : u ∉ C) (ud : u ∉ D)
      (parts : ∀ v, v ≠ t → v ≠ u → v ∈ C ∨ v ∈ D)
      (hc : ∃! x : C, G.Adj t x.val) (hd : ∃! y : D, G.Adj t y.val) : G.degree t = 3 := by
    obtain ⟨x,tx,ux⟩ := hc
    obtain ⟨y,ty,uy⟩ := hd
    have xy : x.val ≠ y.val := fun eq => y.property (eq ▸ x.property.1)
    rw [← G.card_neighborFinset_eq_degree]
    apply Finset.card_eq_three.mpr
    refine ⟨u,x.val,y.val,fun eq => uc (eq ▸ x.property),fun eq => ud (eq ▸ y.property),xy,?_⟩
    ext v
    simp only [mem_neighborFinset,Finset.mem_insert,Finset.mem_singleton]
    constructor
    · intro tv
      by_cases vu : v = u
      · exact .inl vu
      rcases parts v tv.ne.symm vu with cv | dv
      · exact .inr (.inl (congrArg Subtype.val (ux ⟨v,cv⟩ tv)))
      · exact .inr (.inr (congrArg Subtype.val (uy ⟨v,dv⟩ tv)))
    · rintro (rfl | rfl | rfl)
      · exact tu
      · exact tx
      · exact ty
  have parts (v : V) (va : v ≠ a) (vb : v ≠ b) : v ∈ C ∨ v ∈ D := by
    by_cases hs : v ∈ S
    · exact Or.inl ⟨hs,va,vb⟩
    · exact Or.inr hs
  exact ⟨deg a b ab cb db parts auc aud,
    deg b a ab.symm ca da (fun v vb va => parts v va vb) buc bud⟩


/-- When both attachments to a bank are unique, replace the outside
three-edge route by its virtual chord. All interior degrees are preserved
as lower bounds, and deleting any vertex keeps the bank connected. -/
theorem doubleSuppressedBank {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (block : ∀ (z : V) (S : Set V), z ∈ S → (∃ u ∈ S, u ≠ z) → (∃ v, v ∉ S) →
      ∃ u ∈ S, u ≠ z ∧ ∃ v ∉ S, G.Adj u v)
    {a b x y : V} (C : Set V) (ca : a ∉ C) (cb : b ∉ C) (cx : x ∈ C) (cy : y ∈ C)
    (xy : x ≠ y) (noChord : ¬ G.Adj x y)
    (bound : ∀ u ∈ C, ∀ v, G.Adj u v → v ∈ C ∨ v = a ∨ v = b)
    (left : ∀ u ∈ C, G.Adj a u → u = x) (right : ∀ u ∈ C, G.Adj b u → u = y)
    (ab : a ≠ b) (deg : ∀ u : C, 3 ≤ G.degree u.val) :
    let X : C := ⟨x,cx⟩
    let Y : C := ⟨y,cy⟩
    ∃ K : SimpleGraph C,
      (∀ u v, K.Adj u v → G.Adj u.val v.val ∨ (u = X ∧ v = Y) ∨ (u = Y ∧ v = X)) ∧
      (∀ u : C, 3 ≤ K.degree u) ∧
      (∀ (z : C) (S : Set C), z ∈ S → (∃ u ∈ S, u ≠ z) → (∃ v, v ∉ S) →
        ∃ u ∈ S, u ≠ z ∧ ∃ v ∉ S, K.Adj u v) := by
  classical
  let X : C := ⟨x,cx⟩
  let Y : C := ⟨y,cy⟩
  let J : SimpleGraph V := {
    Adj := fun u v => G.Adj u v ∨ (u = x ∧ v = y) ∨ (u = y ∧ v = x)
    symm := ⟨fun _ _ h => h.elim (fun e => .inl e.symm)
      (fun h => .inr (h.elim (fun e => .inr e.symm) (fun e => .inl e.symm)))⟩
    loopless := ⟨fun _ h => h.elim (fun e => e.ne rfl) (fun h => h.elim
      (fun e => xy (e.1.symm.trans e.2)) (fun e => xy (e.2.symm.trans e.1)))⟩ }
  let K := J.induce C
  let : DecidableRel K.Adj := fun _ _ => Classical.propDecidable _
  refine ⟨K,?_,?_,?_⟩
  · intro u v h
    rcases h with real | ⟨hx,hy⟩ | ⟨hy,hx⟩
    · exact .inl real
    · exact .inr (.inl ⟨Subtype.ext hx,Subtype.ext hy⟩)
    · exact .inr (.inr ⟨Subtype.ext hy,Subtype.ext hx⟩)
  · intro u
    let f (v : V) : C := if h : v ∈ C then ⟨v,h⟩ else if v = a then Y else X
    let g (w : C) : V :=
      if u.val = x ∧ w.val = y then a else if u.val = y ∧ w.val = x then b else w.val
    have maps (v : V) (uv : G.Adj u.val v) : K.Adj u (f v) ∧ g (f v) = v := by
      rcases bound u.val u.property v uv with vc | rfl | rfl
      · have n : ¬ (u.val = x ∧ v = y) := fun ⟨h,e⟩ => noChord (h ▸ e ▸ uv)
        have n' : ¬ (u.val = y ∧ v = x) := fun ⟨h,e⟩ => noChord (h ▸ e ▸ uv.symm)
        exact ⟨(by simpa only [f,dif_pos vc] using
          (show K.Adj u (⟨v,vc⟩ : C) from Or.inl uv)),by simp [f,g,vc,n,n']⟩
      · have ux := left u.val u.property uv.symm
        have e : K.Adj u Y := Or.inr (Or.inl ⟨ux,rfl⟩)
        exact ⟨by simpa [f,ca] using e,by simp [f,g,ca,Y,ux]⟩
      · have uy := right u.val u.property uv.symm
        have e : K.Adj u X := Or.inr (Or.inr ⟨uy,rfl⟩)
        exact ⟨by simpa [f,cb,ab.symm] using e,by simp [f,g,cb,ab.symm,X,uy,xy.symm]⟩
    have count := Finset.card_le_card_of_injOn (s := G.neighborFinset u.val)
      (t := K.neighborFinset u) f
      (fun v hv => (K.mem_neighborFinset ..).2 (maps v ((G.mem_neighborFinset ..).1 hv)).1)
      (fun v hv w hw e => (maps v ((G.mem_neighborFinset ..).1 hv)).2.symm.trans
        ((congrArg g e).trans (maps w ((G.mem_neighborFinset ..).1 hw)).2))
    exact (deg u).trans (by simpa only [card_neighborFinset_eq_degree] using count)
  · have blk (z : V) (S : Set V) (zs : z ∈ S) (i : ∃ u ∈ S, u ≠ z) (o : ∃ v, v ∉ S) :
        ∃ u ∈ S, u ≠ z ∧ ∃ v ∉ S, J.Adj u v := by
      obtain ⟨u,us,uz,v,vs,e⟩ := block z S zs i o
      exact ⟨u,us,uz,v,vs,Or.inl e⟩
    let R : Set V := {t | t ∈ C ∧ t ≠ x ∧ t ≠ y}
    have closed (u : V) (ur : u ∈ R) (v : V) (e : J.Adj u v) : v ∈ R ∨ v = x ∨ v = y := by
      rcases e with real | ⟨ux,_⟩ | ⟨uy,_⟩
      · rcases bound u ur.1 v real with vc | rfl | rfl
        · by_cases vx : v = x
          · exact .inr (.inl vx)
          by_cases vy : v = y
          · exact .inr (.inr vy)
          · exact .inl ⟨vc,vx,vy⟩
        · exact (ur.2.1 (left u ur.1 real.symm)).elim
        · exact (ur.2.2 (right u ur.1 real.symm)).elim
      · exact (ur.2.1 ux).elim
      · exact (ur.2.2 uy).elim
    have eq : insert x (insert y R) = C := by
      ext v
      constructor
      · rintro (rfl | rfl | h)
        · exact cx
        · exact cy
        · exact h.1
      · intro h
        by_cases vx : v = x
        · exact .inl vx
        by_cases vy : v = y
        · exact .inr (.inl vy)
        · exact .inr (.inr ⟨h,vx,vy⟩)
    have h := inducedBankBlock blk (show J.Adj x y from Or.inr (Or.inl ⟨rfl,rfl⟩)) R closed
    dsimp only at h
    rwa [eq] at h


/-- Removing a specified edge from a simple cycle gives a simple path between
its ends with exactly one fewer edge. -/
theorem deleteCycleEdge {W : Type*} {K : SimpleGraph W} {x y w : W}
    (c : K.Walk w w) (hc : c.IsCycle) (used : s(x,y) ∈ c.edges) :
    ∃ r : K.Walk x y, r.IsPath ∧ r.length + 1 = c.length ∧ s(x,y) ∉ r.edges := by
  classical
  have mx := c.fst_mem_support_of_mem_edges used
  have my := c.snd_mem_support_of_mem_edges used
  have xy := (c.adj_of_mem_edges used).ne
  let d := c.rotate x mx
  have hd : d.IsCycle := hc.rotate mx
  have edge : s(x,y) ∈ d.edges := (c.rotate_edges x mx).mem_iff.mpr used
  have ym : y ∈ d.support := by simpa [d] using my
  let P := d.takeUntil y ym
  let Q := d.dropUntil y ym
  have eq : P.append Q = d := Walk.take_spec d ym
  have hp : P.IsPath := hd.isPath_takeUntil ym
  have hq : Q.IsPath := (show (P.append Q).IsCycle from eq ▸ hd).isPath_of_append_right
    (Walk.not_nil_of_ne xy)
  have sum : P.length + Q.length = c.length := by
    rw [← Walk.length_append,eq]
    exact c.length_rotate x mx
  have lo := hc.three_le_length
  rw [← eq,Walk.edges_append,List.mem_append] at edge
  rcases edge with p | q
  · have lp := hp.length_eq_one_of_mem_edges p
    have reverse : Q.reverse.length = Q.length := Walk.length_reverse Q
    refine ⟨Q.reverse,hq.reverse,by omega,fun h => ?_⟩
    have := hq.reverse.length_eq_one_of_mem_edges h
    omega
  · have lq := hq.length_eq_one_of_mem_edges (Sym2.eq_swap ▸ q)
    refine ⟨P,hp,by omega,fun h => ?_⟩
    have := hp.length_eq_one_of_mem_edges h
    omega

/-- If a dyadic cycle becomes possible after inserting one virtual edge into
an embedded graph, deleting that edge and appending the two actual terminal
edges yields a successor-length terminal path in the original graph. -/
theorem detourFromVirtualCycle {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W)
    (f : W ↪ V) {a b : V} {x y : W} (ab : a ≠ b) (ax : G.Adj a (f x))
    (byEdge : G.Adj b (f y)) (missA : ∀ t, f t ≠ a) (missB : ∀ t, f t ≠ b)
    (real : ∀ u v, H.Adj u v → G.Adj (f u) (f v) ∨ (u = x ∧ v = y) ∨ (u = y ∧ v = x))
    (absent : ¬ ∃ (k : ℕ) (v : V) (c : G.Walk v v), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2^k)
    {w} (c : H.Walk w w) (hc : c.IsCycle) {k : ℕ} (len : c.length = 2^k) (hk : 2 ≤ k) :
    ∃ p : G.Walk a b, p.IsPath ∧ p.length = 2^k+1 ∧
      (∀ z ∈ p.support, z ≠ a → z ≠ b → z ∈ Set.range f) := by
  let F := G.comap f
  let hom : F →g G := ⟨f,fun e => e⟩
  have genuine {u v : W} (p : H.Walk u v) (avoid : s(x,y) ∉ p.edges) :
      ∀ e ∈ p.edges, e ∈ F.edgeSet := by
    rintro ⟨i,j⟩ mem
    rcases real i j (p.edges_subset_edgeSet mem) with e | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact e
    · exact (avoid mem).elim
    · exact (avoid (Sym2.eq_swap ▸ mem)).elim
  have used : s(x,y) ∈ c.edges := by
    by_contra avoid
    let d := (c.transfer F (genuine c avoid)).map hom
    exact absent ⟨k,f w,d,hk,(hc.transfer _).map f.injective,by simpa [d] using len⟩
  obtain ⟨r,hr,l,avoid⟩ := deleteCycleEdge c hc used
  let q := (r.transfer F (genuine r avoid)).map hom
  have hq : q.IsPath := (hr.transfer _).map f.injective
  have ql : q.length = r.length := by simp [q]
  have vertices : q.support = r.support.map f := by
    rw [show q.support = _ from Walk.support_map hom _, Walk.support_transfer]
    rfl
  have inside {z : V} (h : z ∈ q.support) : z ∈ Set.range f := by
    rw [vertices] at h
    obtain ⟨t,_,e⟩ := List.mem_map.mp h
    exact ⟨t,e⟩
  have qa : a ∉ q.support := fun h => (inside h).elim fun i e => missA i e
  have qb : b ∉ q.support := fun h => (inside h).elim fun i e => missB i e
  let p := (q.concat byEdge.symm).cons ax
  refine ⟨p,(hq.concat qb _).cons (by simp [qa,ab]),?_,?_⟩
  · simp only [p,Walk.length_cons,Walk.length_concat]
    omega
  · intro v hv va vb
    exact inside (by simpa [p,va,vb] using hv)


/-- Extend a simple path lying entirely in a region by one new edge at either end. -/
theorem extendRegionPath {V : Type*} {G : SimpleGraph V} {a b x y : V} (ab : a ≠ b)
    (C : Set V) (ca : a ∉ C) (cb : b ∉ C) (ax : G.Adj a x) (by' : G.Adj b y)
    (r : G.Walk x y) (hr : r.IsPath) (inside : ∀ v ∈ r.support, v ∈ C) :
    ∃ p : G.Walk a b, p.IsPath ∧ p.length = r.length+2 ∧
      ∀ v ∈ p.support, v ≠ a → v ≠ b → v ∈ C := by
  have na : a ∉ r.support := fun h => ca (inside a h)
  have nb : b ∉ r.support := fun h => cb (inside b h)
  let p := (r.concat by'.symm).cons ax
  refine ⟨p,(hr.concat nb _).cons (by simp [na,ab]),by simp [p,Nat.add_assoc],?_⟩
  intro v hv va vb
  exact inside v (by simpa [p,va,vb] using hv)

/-- Splitting a vertex with two sets of incident edges either preserves a
cycle or opens it into a simple path of precisely the same length. -/
theorem splitCycleAtPorts {V W : Type*} (G : SimpleGraph V) (K : SimpleGraph W)
    (f : W ↪ V) (z : W) {y : V} (miss : ∀ t, f t ≠ y) (R : Set V)
    (reps : ∀ t, t ≠ z → f t ∈ R)
    (interior : ∀ u v, u ≠ z → v ≠ z → K.Adj u v → G.Adj (f u) (f v))
    (star : ∀ u, K.Adj z u → G.Adj (f z) (f u) ∨ G.Adj y (f u))
    {w : W} (c : K.Walk w w) (hc : c.IsCycle) :
    (∃ v, ∃ d : G.Walk v v, d.IsCycle ∧ d.length = c.length) ∨
    ∃ r : G.Walk (f z) y, r.IsPath ∧ r.length = c.length ∧
      ∀ v ∈ r.support, v ≠ f z → v ≠ y → v ∈ R := by
  classical
  let F := G.comap f
  let hom : F →g G := ⟨f,fun h => h⟩
  have edges {u v : W} (p : K.Walk u v) (away : z ∉ p.support) :
      ∀ e ∈ p.edges, e ∈ F.edgeSet := by
    rintro ⟨i,j⟩ he
    exact interior i j (fun h => away (h ▸ p.fst_mem_support_of_mem_edges he))
      (fun h => away (h ▸ p.snd_mem_support_of_mem_edges he)) (p.edges_subset_edgeSet he)
  by_cases hz : z ∈ c.support
  · let rot := c.rotate z hz
    have rc : rot.IsCycle := hc.rotate hz
    have rl : rot.length = c.length := c.length_rotate _ _
    clear_value rot
    cases rot with
    | nil => exact (rc.not_nil .nil).elim
    | @cons _ u _ zu tail =>
      have tp : tail.IsPath := ((Walk.cons_isCycle_iff ..).mp rc).1
      have vz := tail.adj_penultimate (show ¬tail.Nil from fun h => zu.ne.symm h.eq)
      let s := tail.dropLast
      have eq : s.concat vz = tail := Walk.concat_dropLast vz
      obtain ⟨ps,away⟩ := (Walk.concat_isPath_iff vz).mp (eq ▸ tp)
      let q := (s.transfer F (edges s away)).map hom
      have hq : q.IsPath := (ps.transfer (edges s away)).map f.injective
      have qs : q.support = s.support.map f := by
        rw [show q.support = _ from Walk.support_map hom _,Walk.support_transfer]
        rfl
      have inside {v : V} (hv : v ∈ q.support) : v ∈ R ∧ v ≠ f z ∧ v ≠ y := by
        obtain ⟨i,hi,rfl⟩ := List.mem_map.mp (qs ▸ hv)
        have iz : i ≠ z := fun e => away (e ▸ hi)
        exact ⟨reps i iz,fun e => iz (f.injective e),miss i⟩
      have ql : q.length = s.length := by simp [q]
      have len : q.length+2 = c.length := by
        rw [Walk.length_cons,← eq,Walk.length_concat] at rl
        omega
      have pos : 0 < q.length := by have := hc.three_le_length; omega
      let T := {v | v ∈ R ∧ v ≠ f z ∧ v ≠ y}
      have nx : f z ∉ T := fun h => h.2.1 rfl
      have ny : y ∉ T := fun h => h.2.2 rfl
      have close {t : V} (nt : t ∉ q.support) (tu : G.Adj t (f u))
          (tv : G.Adj t (f tail.penultimate)) :
          ∃ d : G.Walk t t, d.IsCycle ∧ d.length = c.length := by
        refine ⟨.cons tu (q.concat tv.symm),?_,by simp [← len,Nat.add_assoc]⟩
        apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
        constructor
        · rw [Walk.tail_cons]
          exact (Walk.isPath_copy _ _ _).mpr (hq.concat nt _)
        · simp only [Walk.length_cons,Walk.length_concat]
          omega
      rcases star u zu with xu | yu <;> rcases star _ vz.symm with xv | yv
      · exact .inl ⟨_,close (fun h => (inside h).2.1 rfl) xu xv⟩
      · obtain ⟨r,hr,lr,rt⟩ := extendRegionPath (miss z) T nx ny xu yv q hq (fun _ h => inside h)
        exact .inr ⟨r,hr,lr.trans len,fun v h vx vy => (rt v h vx vy).1⟩
      · obtain ⟨r,hr,lr,rt⟩ := extendRegionPath (miss z) T nx ny xv yu q.reverse hq.reverse
          (fun _ h => inside (by simpa [Walk.support_reverse] using h))
        exact .inr ⟨r,hr,by simpa [Walk.length_reverse,len] using lr,
          fun v h vx vy => (rt v h vx vy).1⟩
      · exact .inl ⟨_,close (fun h => (inside h).2.2 rfl) yu yv⟩
  · let d := (c.transfer F (edges c hz)).map hom
    exact .inl ⟨_,d,(hc.transfer _).map f.injective,by simp [d]⟩

/-- In a side at an uncovered edge, the two attachment vertices are at
distance at least three along any simple path inside the side. -/
theorem uncoveredPortsSeparated {V : Type*} {G : SimpleGraph V} {a b x y : V}
    (ab : G.Adj a b) (C : Set V) (ca : a ∉ C) (cb : b ∉ C)
    (xc : x ∈ C) (yc : y ∈ C) (ax : G.Adj a x) (by' : G.Adj b y)
    (absent : ¬ ∃ (k : ℕ) (w : V) (c : G.Walk w w), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2^k)
    (uncov : ¬ ∃ (k : ℕ) (w : V) (c : G.Walk w w),
      1 ≤ k ∧ c.IsCycle ∧ c.length = 2^k+1 ∧ s(a,b) ∈ c.edges) :
    x ≠ y ∧ ¬G.Adj x y ∧ ∀ i ∈ C, G.Adj x i → ¬G.Adj y i := by
  have long (r : G.Walk x y) (hr : r.IsPath) (inc : ∀ i ∈ r.support, i ∈ C) : 3 ≤ r.length := by
    obtain ⟨p,hp,len,_⟩ := extendRegionPath ab.ne C ca cb ax by' r hr inc
    have five := (markedDetourAvoids ab absent uncov p hp (by omega)).2.2
    omega
  have xy : x ≠ y := by
    rintro rfl
    have h := long .nil (by simp) (by simpa using xc)
    exact (by decide : ¬ 3 ≤ 0) h
  refine ⟨xy,?_,?_⟩
  · intro e
    let r : G.Walk x y := .cons e .nil
    have h := long r (by simp [r,Walk.cons_isPath_iff,xy]) (by simpa [r] using And.intro xc yc)
    exact (by decide : ¬ 3 ≤ 1) h
  · intro i hi xi yi
    let r : G.Walk x y := .cons xi (.cons yi.symm .nil)
    have h := long r (by simp [r,Walk.cons_isPath_iff,xi.ne,xy,yi.ne.symm])
      (by simpa [r] using And.intro xc (And.intro hi yc))
    exact (by decide : ¬ 3 ≤ 2) h

/-- Every proper nonempty bank at an uncovered edge of a smallest block
counterexample contains a terminal path of length one more than a power of two. -/
theorem allBankDetour {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (block : ∀ (z : V) (S : Set V), z ∈ S → (∃ x ∈ S, x ≠ z) → (∃ y, y ∉ S) →
      ∃ x ∈ S, x ≠ z ∧ ∃ y ∉ S, G.Adj x y)
    {a b : V} (ab : G.Adj a b) (C : Set V) (ne : C.Nonempty) (ca : a ∉ C) (cb : b ∉ C)
    (bound : ∀ x ∈ C, ∀ y, G.Adj x y → y ∈ C ∨ y = a ∨ y = b)
    (deg : ∀ u : C, 3 ≤ G.degree u.val) (proper : C.ncard+2 < Fintype.card V)
    (absent : ¬ ∃ (k : ℕ) (w : V) (c : G.Walk w w), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2^k)
    (uncov : ¬ ∃ (k : ℕ) (w : V) (c : G.Walk w w),
      1 ≤ k ∧ c.IsCycle ∧ c.length = 2^k+1 ∧ s(a,b) ∈ c.edges)
    (smaller : ∀ (W : Type) [Fintype W] (K : SimpleGraph W) [DecidableRel K.Adj],
      Fintype.card W < Fintype.card V → 3 ≤ K.minDegree →
      (∀ (z : W) (S : Set W), z ∈ S → (∃ x ∈ S, x ≠ z) → (∃ y, y ∉ S) →
        ∃ x ∈ S, x ≠ z ∧ ∃ y ∉ S, K.Adj x y) →
      ∃ (k : ℕ) (w : W) (c : K.Walk w w), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2^k) :
    ∃ (k : ℕ) (p : G.Walk a b), 2 ≤ k ∧ p.IsPath ∧ p.length = 2^k+1 ∧
      (∀ i ∈ p.support, i ≠ a → i ≠ b → i ∈ C) := by
  classical
  obtain ⟨_,⟨x,ax,uniqueX⟩,y,byEdge,uniqueY⟩ :=
    bankTopologyUncovered G smaller absent block ab C ne ca cb bound
      (fun u hu => deg ⟨u,hu⟩) proper uncov
  obtain ⟨xy,noChord,_⟩ := uncoveredPortsSeparated ab C ca cb x.property y.property ax byEdge absent uncov
  obtain ⟨K,real,low,cut⟩ :=
    doubleSuppressedBank G block C ca cb x.property y.property xy noChord bound
      (fun u hu h => congrArg Subtype.val (uniqueX ⟨u,hu⟩ h))
      (fun u hu h => congrArg Subtype.val (uniqueY ⟨u,hu⟩ h)) ab.ne deg
  let : Nonempty C := ⟨x⟩
  let : DecidableRel K.Adj := fun _ _ => Classical.propDecidable _
  have lt : Fintype.card C < Fintype.card V := by rw [Set.fintypeCard_eq_ncard]; omega
  obtain ⟨k,w,c,hk,hc,len⟩ := smaller C K lt (K.le_minDegree_of_forall_le_degree 3 low) cut
  let f : C ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
  obtain ⟨p,hp,pl,within⟩ := detourFromVirtualCycle G K f (x := x) (y := y) ab.ne ax byEdge
    (fun z e => ca (e ▸ z.property)) (fun z e => cb (e ▸ z.property)) real absent c hc len hk
  refine ⟨k,p,hk,hp,pl,?_⟩
  intro i hi ia ib
  obtain ⟨z,e⟩ := within i hi ia ib
  exact e ▸ z.property


/-- If a spanning block uses covered edges and uncovered edges are incident
only to vertices of degree at most three, the uncovered edges form a matching. -/
theorem uncoveredMatching {V : Type*} [Fintype V] (G H : SimpleGraph V)
    [DecidableRel G.Adj] (covered : V → V → Prop) (sub : H ≤ G)
    (block : ∀ (t : V) (S : Set V), t ∈ S → (∃ x ∈ S, x ≠ t) → (∃ y, y ∉ S) →
      ∃ x ∈ S, x ≠ t ∧ ∃ y ∉ S, H.Adj x y)
    (cert : ∀ a b, H.Adj a b → covered a b)
    (cubic : ∀ a b, G.Adj a b → ¬ covered a b → G.degree a ≤ 3) :
    ∀ a b c, G.Adj a b → ¬ covered a b → G.Adj a c → ¬ covered a c → b = c := by
  classical
  intro a b c ab nb ac nc
  by_contra neq
  have extra (x y : V) (ax : a ≠ x) (ay : a ≠ y) (yx : y ≠ x) :
      ∃ t, H.Adj a t ∧ t ≠ x := by
    obtain ⟨v,hv,ne,t,ht,edge⟩ := block x {x,a} (by simp)
      ⟨a,by simp,ax⟩ ⟨y,by simp [yx,ay.symm]⟩
    have va : v = a := by simpa [ne] using hv
    subst v
    exact ⟨t,edge,fun h => ht (by simp [h])⟩
  obtain ⟨d,ad,db⟩ := extra b c ab.ne ac.ne (Ne.symm neq)
  obtain ⟨e,ae,ed⟩ := extra d b ad.ne ab.ne db.symm
  have bd : b ≠ d := db.symm
  have be : b ≠ e := fun h => nb (h ▸ cert a e ae)
  have cd : c ≠ d := fun h => nc (h ▸ cert a d ad)
  have ce : c ≠ e := fun h => nc (h ▸ cert a e ae)
  have de := ed.symm
  have four : ({b,c,d,e} : Finset V) ⊆ G.neighborFinset a := by
    intro v hv
    simp only [Finset.mem_insert,Finset.mem_singleton] at hv
    apply (G.mem_neighborFinset ..).2
    rcases hv with rfl | rfl | rfl | rfl
    · exact ab
    · exact ac
    · exact sub ad
    · exact sub ae
  have count : 4 ≤ G.degree a := by
    simpa [neq,bd,be,cd,ce,de,card_neighborFinset_eq_degree] using Finset.card_le_card four
  have := cubic a b ab nb
  omega

/-- A nonempty union of regions contains a connected region with the same two
possible exits. This form also applies after removing previous components. -/
theorem chooseConnectedRegion {V : Type*} (G : SimpleGraph V) {x y : V}
    (P : Set V) (live : P.Nonempty) (bound : ∀ u ∈ P, ∀ v, G.Adj u v → v ∈ P ∨ v = x ∨ v = y) :
    ∃ R : Set V, R.Nonempty ∧ R ⊆ P ∧ (G.induce R).Connected ∧
      ∀ u ∈ R, ∀ v, G.Adj u v → v ∈ R ∨ v = x ∨ v = y := by
  obtain ⟨t,ht⟩ := live
  let K := G.induce P
  let J := K.connectedComponentMk (⟨t,ht⟩ : P)
  let R := Subtype.val '' J.supp
  have sub : R ⊆ P := by rintro _ ⟨i,_,rfl⟩; exact i.property
  let f : J.toSimpleGraph →g G.induce R := ⟨fun i => ⟨i.val.val,i.val,i.property,rfl⟩,fun e => e⟩
  refine ⟨R,⟨t,⟨t,ht⟩,rfl,rfl⟩,sub,J.connected_toSimpleGraph.map f (by
    rintro ⟨v,i,hi,iv⟩
    exact ⟨⟨i,hi⟩,Subtype.ext iv⟩),?_⟩
  rintro u ⟨i,hi,iu⟩ v uv
  rcases bound u (iu ▸ i.property) v uv with hv | ends
  · let j : P := ⟨v,hv⟩
    have e : K.Adj j i := (iu ▸ uv.symm : G.Adj v i.val)
    exact Or.inl ⟨j,(ConnectedComponent.connectedComponentMk_eq_of_adj e).trans hi,rfl⟩
  · exact Or.inr ends

/-- Identify two ports on one connected region. Three distinct attachment
vertices give the identified vertex degree at least three. -/
theorem foldRegionDetour {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (block : ∀ (z : V) (S : Set V), z ∈ S → (∃ u ∈ S, u ≠ z) → (∃ v, v ∉ S) →
      ∃ u ∈ S, u ≠ z ∧ ∃ v ∉ S, G.Adj u v)
    {x y : V} (xy : x ≠ y) (R : Set V) (xr : x ∉ R) (yr : y ∉ R)
    (conn : (G.induce R).Connected)
    (bound : ∀ u ∈ R, ∀ v, G.Adj u v → v ∈ R ∨ v = x ∨ v = y)
    (split : ∀ u ∈ R, G.Adj x u → ¬ G.Adj y u)
    (deg : ∀ u ∈ R, 3 ≤ G.degree u)
    (many : 3 ≤ {u | u ∈ R ∧ (G.Adj x u ∨ G.Adj y u)}.ncard)
    (absent : ¬ ∃ (k : ℕ) (w : V) (c : G.Walk w w), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2^k)
    (smaller : ∀ (W : Type) [Fintype W] (K : SimpleGraph W) [DecidableRel K.Adj],
      Fintype.card W < Fintype.card V → 3 ≤ K.minDegree →
      (∀ (z : W) (S : Set W), z ∈ S → (∃ u ∈ S, u ≠ z) → (∃ v, v ∉ S) →
        ∃ u ∈ S, u ≠ z ∧ ∃ v ∉ S, K.Adj u v) →
      ∃ (k : ℕ) (w : W) (c : K.Walk w w), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2^k) :
    ∃ (k : ℕ) (r : G.Walk x y), 2 ≤ k ∧ r.IsPath ∧ r.length = 2^k ∧
      ∀ i ∈ r.support, i ≠ x → i ≠ y → i ∈ R := by
  classical
  let U := insert x R
  let z : U := ⟨x,Or.inl rfl⟩
  let π (v : V) : U := if h : v ∈ R then ⟨v,Or.inr h⟩ else z
  have inside (v : V) (hv : v ∈ R) : (π v).val = v := by simp [π,hv]
  have outside (v : V) (hv : v ∉ R) : π v = z := dif_neg hv
  have inv (t : U) : π t.val = t := by
    rcases t.property with e | h
    · exact (outside _ (e ▸ xr)).trans (Subtype.ext e.symm)
    · exact Subtype.ext (inside _ h)
  have isolated {u : V} {t : U} (eq : π u = t) (tz : t ≠ z) : u = t.val := by
    by_cases ur : u ∈ R
    · exact (inside u ur).symm.trans (congrArg Subtype.val eq)
    · exact (tz (eq.symm.trans (outside u ur))).elim
  have region {t : U} (tz : t ≠ z) : t.val ∈ R := t.property.resolve_left (fun e => tz (Subtype.ext e))
  let K := G.map π
  let : DecidableRel K.Adj := fun _ _ => Classical.propDecidable _
  have maps {u v : V} (e : G.Adj u v) (ne : π u ≠ π v) : K.Adj (π u) (π v) :=
    SimpleGraph.map_adj_apply' e ne
  have leaf (u : V) (m : u ∈ R) : π u ≠ z := by
    intro e
    have ux : u = x := (inside u m).symm.trans (congrArg Subtype.val e)
    exact xr (ux ▸ m)
  have bounds (t : U) : 3 ≤ K.degree t := by
    by_cases tz : t = z
    · subst t
      let A := {u | u ∈ R ∧ (G.Adj x u ∨ G.Adj y u)}
      have count := Finset.card_le_card_of_injOn (s := A.toFinset) (t := K.neighborFinset z) π (by
        intro u hu
        have mem := Set.mem_toFinset.mp hu
        have ne := (leaf u mem.1).symm
        apply (K.mem_neighborFinset ..).mpr
        rcases mem.2 with e | e
        · rw [← outside x xr] at ne ⊢
          exact maps e ne
        · rw [← outside y yr] at ne ⊢
          exact maps e ne) (by
        intro i hi j hj eq
        exact (inside i (Set.mem_toFinset.mp hi).1).symm.trans
          ((congrArg Subtype.val eq).trans (inside j (Set.mem_toFinset.mp hj).1)))
      rw [← Set.ncard_eq_toFinset_card',card_neighborFinset_eq_degree] at count
      exact many.trans count
    · have rt := region tz
      have border (v) (e : G.Adj t.val v) (vR : v ∉ R) : v = x ∨ v = y :=
        (bound _ rt v e).resolve_left vR
      have inj {i j : V} (ei : G.Adj t.val i) (ej : G.Adj t.val j) (eq : π i = π j) : i = j := by
        by_cases ir : i ∈ R
        · have jr : j ∈ R := by by_contra h; exact leaf i ir (eq.trans (outside j h))
          exact (inside i ir).symm.trans ((congrArg Subtype.val eq).trans (inside j jr))
        · have jr : j ∉ R := fun h => leaf j h (eq.symm.trans (outside i ir))
          rcases border i ei ir with rfl | rfl <;> rcases border j ej jr with rfl | rfl
          · rfl
          · exact (split _ rt ei.symm ej.symm).elim
          · exact (split _ rt ej.symm ei.symm).elim
          · rfl
      have count := Finset.card_le_card_of_injOn (s := G.neighborFinset t.val)
        (t := K.neighborFinset t) π (by
          intro u hu
          have e := (G.mem_neighborFinset ..).mp hu
          apply (K.mem_neighborFinset ..).mpr
          rw [← inv t]
          apply maps e
          intro eq
          exact e.ne (isolated (eq.symm.trans (inv t)) tz).symm) (by
          intro i hi j hj eq
          exact inj ((G.mem_neighborFinset ..).mp hi) ((G.mem_neighborFinset ..).mp hj) eq)
      exact (deg _ rt).trans (by simpa only [card_neighborFinset_eq_degree] using count)
  have blockK (t : U) (S : Set U) (ht : t ∈ S) (inn : ∃ u ∈ S, u ≠ t) (out : ∃ v, v ∉ S) :
      ∃ u ∈ S, u ≠ t ∧ ∃ v ∉ S, K.Adj u v := by
    obtain ⟨i,hi,it⟩ := inn
    obtain ⟨j,hj⟩ := out
    let T := {v : V | π v ∈ S}
    have mem (u : U) : u.val ∈ T ↔ u ∈ S := by simp [T,inv]
    by_cases tz : t = z
    · subst t
      have ir : i.val ∈ R := region it
      have jr : j.val ∈ R := region (fun e => hj (e ▸ ht))
      obtain ⟨p⟩ := conn.preconnected (⟨i.val,ir⟩ : R) ⟨j.val,jr⟩
      obtain ⟨d,_,h₁,h₂⟩ := p.exists_boundary_dart {u : R | u.val ∈ T} ((mem i).mpr hi) (fun h => hj ((mem j).mp h))
      exact ⟨π d.fst.val,h₁,leaf _ d.fst.property,π d.snd.val,h₂,
        maps d.adj (fun eq => h₂ (show π d.snd.val ∈ S from eq ▸ h₁))⟩
    · obtain ⟨u,hu,ut,v,hv,uv⟩ := block t.val T ((mem t).mpr ht)
        ⟨i.val,(mem i).mpr hi,fun e => it (Subtype.ext e)⟩ ⟨j.val,fun h => hj ((mem j).mp h)⟩
      exact ⟨π u,hu,fun eq => ut (isolated eq tz),π v,hv,maps uv (fun eq => hv (show π v ∈ S from eq ▸ (hu : π u ∈ S)))⟩
  have yu : y ∉ U := fun h => h.elim xy.symm yr
  have lt := Set.ncard_lt_ncard (show U ⊂ Set.univ from ⟨Set.subset_univ _,fun h => yu (h (Set.mem_univ y))⟩)
  let : Nonempty U := ⟨z⟩
  obtain ⟨k,w,c,hk,hc,len⟩ := smaller U K (by rw [Set.fintypeCard_eq_ncard]; simpa only [Set.ncard_univ,Nat.card_eq_fintype_card] using lt)
    (K.le_minDegree_of_forall_le_degree 3 bounds) blockK
  let f : U ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
  apply (splitCycleAtPorts G K f z (y := y) (fun t e => yu (e ▸ t.property)) R
    (fun t h => region h) (by
      rintro u v uz vz ⟨_,i,j,e,iu,jv⟩
      change G.Adj u.val v.val
      simpa only [isolated iu uz,isolated jv vz] using e) (by
      rintro u ⟨zu,i,j,e,iz,ju⟩
      have eq := isolated ju (Ne.symm zu)
      have ir : i ∉ R := fun h => leaf i h iz
      change G.Adj x u.val ∨ G.Adj y u.val
      rcases (bound u.val (region zu.symm) i (eq ▸ e.symm)).resolve_left ir with h | h
      · exact Or.inl (by simpa only [h,eq] using e)
      · exact Or.inr (by simpa only [h,eq] using e)) c hc).elim
  · rintro ⟨v,d,hd,ld⟩
    exact (absent ⟨k,v,d,hk,hd,ld.trans len⟩).elim
  · rintro ⟨r,hr,lr,inc⟩
    exact ⟨k,r,hk,hr,lr.trans len,inc⟩

/-- A region with just one neighbor at each port has either a three-edge
connection or a connection one longer than a power of two. -/
theorem thinRegionRoutes {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (block : ∀ (z : V) (S : Set V), z ∈ S → (∃ u ∈ S, u ≠ z) → (∃ v, v ∉ S) →
      ∃ u ∈ S, u ≠ z ∧ ∃ v ∉ S, G.Adj u v)
    {x y : V} (xy : x ≠ y) (R : Set V) (xr : x ∉ R) (yr : y ∉ R)
    (bound : ∀ u ∈ R, ∀ v, G.Adj u v → v ∈ R ∨ v = x ∨ v = y)
    (split : ∀ u ∈ R, G.Adj x u → ¬ G.Adj y u)
    (u v : R) (xu : G.Adj x u.val) (yv : G.Adj y v.val)
    (left : ∀ i ∈ R, G.Adj x i → i = u.val) (right : ∀ i ∈ R, G.Adj y i → i = v.val)
    (floor : ∀ i, 3 ≤ G.degree i)
    (absent : ¬ ∃ (k : ℕ) (w : V) (c : G.Walk w w), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2^k)
    (smaller : ∀ (W : Type) [Fintype W] (K : SimpleGraph W) [DecidableRel K.Adj],
      Fintype.card W < Fintype.card V → 3 ≤ K.minDegree →
      (∀ (z : W) (S : Set W), z ∈ S → (∃ i ∈ S, i ≠ z) → (∃ j, j ∉ S) →
        ∃ i ∈ S, i ≠ z ∧ ∃ j ∉ S, K.Adj i j) →
      ∃ (k : ℕ) (w : W) (c : K.Walk w w), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2^k) :
    let route (l : ℕ) := ∃ r : G.Walk x y, r.IsPath ∧ r.length = l ∧
      ∀ i ∈ r.support, i ≠ x → i ≠ y → i ∈ R
    (9 ≤ R.ncard ∧ route 3) ∨ ∃ k : ℕ, 2 ≤ k ∧ 2^k ≤ R.ncard ∧ route (2^k+1) := by
  classical
  dsimp only
  have uv : u.val ≠ v.val := fun e => split _ v.property (e ▸ xu) yv
  by_cases adj : G.Adj u.val v.val
  · let T := {i | i ∈ R ∧ i ≠ u.val ∧ i ≠ v.val}
    have sub : T ⊆ R := fun _ h => h.1
    have ut : u.val ∉ T := fun h => h.2.1 rfl
    have vt : v.val ∉ T := fun h => h.2.2 rfl
    have live : T.Nonempty := by
      by_contra missing
      have incl : G.neighborFinset u.val ⊆ {x,v.val} := by
        intro w hw
        have uw := (G.mem_neighborFinset ..).1 hw
        rcases bound u.val u.property w uw with wr | wx | wy
        · by_cases wv : w = v.val
          · simp [wv]
          · exact (missing ⟨w,wr,uw.ne.symm,wv⟩).elim
        · simp [wx]
        · exact (split _ u.property xu (wy ▸ uw.symm)).elim
      have hi := Finset.card_le_card incl
      have cap := Finset.card_insert_le x ({v.val} : Finset V)
      simp only [card_neighborFinset_eq_degree,Finset.card_singleton] at hi cap
      have := floor u.val
      omega
    have boundT (i : V) (hi : i ∈ T) (j : V) (ij : G.Adj i j) : j ∈ T ∨ j = u.val ∨ j = v.val := by
      rcases bound i hi.1 j ij with jr | rfl | rfl
      · by_cases ju : j = u.val
        · exact Or.inr (Or.inl ju)
        by_cases jv : j = v.val
        · exact Or.inr (Or.inr jv)
        · exact Or.inl ⟨jr,ju,jv⟩
      · exact (hi.2.1 (left _ hi.1 ij.symm)).elim
      · exact (hi.2.2 (right _ hi.1 ij.symm)).elim
    have seven := bankSeven G floor (noDyadic_commonNeighbor_unique absent) u.val v.val adj T live ut vt boundT
    have subset : insert u.val (insert v.val T) ⊆ R := Set.insert_subset u.property (Set.insert_subset v.property sub)
    have count := Set.ncard_le_ncard subset
    rw [Set.ncard_insert_of_notMem (by simp [uv,ut]),Set.ncard_insert_of_notMem vt] at count
    let r : G.Walk u.val v.val := .cons adj .nil
    have hr : r.IsPath := by simp [r,Walk.cons_isPath_iff,uv]
    obtain ⟨p,hp,len,inside⟩ := extendRegionPath xy R xr yr xu yv r hr (by
      intro w hw
      rcases (by simpa [r] using hw : w = u.val ∨ w = v.val) with rfl | rfl
      · exact u.property
      · exact v.property)
    exact .inl ⟨by omega,p,hp,len,inside⟩
  · obtain ⟨K,real,low,cut⟩ := doubleSuppressedBank G block R xr yr u.property v.property uv adj bound
      left right xy (fun i => floor i.val)
    let : Nonempty R := ⟨u⟩
    let : DecidableRel K.Adj := fun _ _ => Classical.propDecidable _
    have lt := Set.ncard_lt_ncard (show R ⊂ Set.univ from ⟨Set.subset_univ _,fun h => xr (h (Set.mem_univ x))⟩)
    obtain ⟨k,w,c,hk,hc,len⟩ := smaller R K
      (by rw [Set.fintypeCard_eq_ncard]; simpa only [Set.ncard_univ,Nat.card_eq_fintype_card] using lt)
      (K.le_minDegree_of_forall_le_degree 3 low) cut
    let f : R ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
    obtain ⟨p,hp,pl,pr⟩ := detourFromVirtualCycle G K f (x := u) (y := v) xy xu yv
      (fun i e => xr (e ▸ i.property)) (fun i e => yr (e ▸ i.property)) real absent c hc len hk
    have inside (i) (hi : i ∈ p.support) (ix : i ≠ x) (iy : i ≠ y) : i ∈ R := by
      obtain ⟨j,e⟩ := pr i hi ix iy
      exact e ▸ j.property
    have size := detourLengthBound p hp inside
    exact .inr ⟨k,hk,by omega,p,hp,pl,inside⟩

/-- Classify one component after removing the two attachment vertices of a side.
The dyadic-plus-three alternative gives a cardinality bound on that component. -/
theorem componentSpectrum {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (block : ∀ (z : V) (S : Set V), z ∈ S → (∃ u ∈ S, u ≠ z) → (∃ v, v ∉ S) →
      ∃ u ∈ S, u ≠ z ∧ ∃ v ∉ S, G.Adj u v)
    {a b x y : V} (ab : G.Adj a b) (C : Set V) (ca : a ∉ C) (cb : b ∉ C)
    (xc : x ∈ C) (yc : y ∈ C) (ax : G.Adj a x) (by' : G.Adj b y) (xy : x ≠ y)
    (R : Set V) (live : R.Nonempty) (sub : R ⊆ C) (xr : x ∉ R) (yr : y ∉ R)
    (conn : (G.induce R).Connected)
    (bound : ∀ u ∈ R, ∀ v, G.Adj u v → v ∈ R ∨ v = x ∨ v = y)
    (split : ∀ u ∈ R, G.Adj x u → ¬ G.Adj y u) (floor : ∀ i, 3 ≤ G.degree i)
    (absent : ¬ ∃ (k : ℕ) (w : V) (c : G.Walk w w), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2^k)
    (uncov : ¬ ∃ (k : ℕ) (w : V) (c : G.Walk w w),
      1 ≤ k ∧ c.IsCycle ∧ c.length = 2^k+1 ∧ s(a,b) ∈ c.edges)
    (smaller : ∀ (W : Type) [Fintype W] (K : SimpleGraph W) [DecidableRel K.Adj],
      Fintype.card W < Fintype.card V → 3 ≤ K.minDegree →
      (∀ (z : W) (S : Set W), z ∈ S → (∃ i ∈ S, i ≠ z) → (∃ j, j ∉ S) →
        ∃ i ∈ S, i ≠ z ∧ ∃ j ∉ S, K.Adj i j) →
      ∃ (k : ℕ) (w : W) (c : K.Walk w w), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2^k) :
    let route (l : ℕ) := ∃ p : G.Walk a b, p.IsPath ∧ p.length = l ∧
      ∀ i ∈ p.support, i ≠ a → i ≠ b → i ∈ insert x (insert y R)
    (3 ≤ {i | i ∈ R ∧ (G.Adj x i ∨ G.Adj y i)}.ncard ∧
      ∃ k : ℕ, 2 ≤ k ∧ route (2^k+2)) ∨
    ({i | i ∈ R ∧ (G.Adj x i ∨ G.Adj y i)}.ncard ≤ 2 ∧ (∃! i : R, G.Adj x i.val) ∧ (∃! i : R, G.Adj y i.val) ∧ 8 ≤ R.ncard ∧
      ((9 ≤ R.ncard ∧ route 5) ∨ ∃ k : ℕ, 3 ≤ k ∧ 2^k ≤ R.ncard ∧ route (2^k+3))) := by
  classical
  dsimp only
  let T := insert x (insert y R)
  have tc : T ⊆ C := Set.insert_subset xc (Set.insert_subset yc sub)
  have lift (r : G.Walk x y) (hr : r.IsPath)
      (inc : ∀ i ∈ r.support, i ≠ x → i ≠ y → i ∈ R) :=
    extendRegionPath ab.ne T (fun h => ca (tc h)) (fun h => cb (tc h)) ax by' r hr (by
      intro i hi
      by_cases ix : i = x
      · exact Or.inl ix
      by_cases iy : i = y
      · exact Or.inr (Or.inl iy)
      · exact Or.inr (Or.inr (inc i hi ix iy)))
  let A := {i | i ∈ R ∧ (G.Adj x i ∨ G.Adj y i)}
  by_cases many : 3 ≤ A.ncard
  · obtain ⟨k,r,hk,hr,len,inc⟩ := foldRegionDetour G block xy R xr yr conn bound split
      (fun i _ => floor i) many absent smaller
    obtain ⟨p,hp,lp,pc⟩ := lift r hr inc
    exact .inl ⟨many,k,hk,p,hp,by omega,pc⟩
  obtain ⟨t,ht⟩ := live
  obtain ⟨⟨u,_,xu⟩,v,_,yv⟩ := componentSeesBoth block xy R ⟨t,ht⟩ xr yr bound
  have apart {i j : V} (ir : i ∈ R) (xi : G.Adj x i) (yj : G.Adj y j) : i ≠ j :=
    fun h => split i ir xi (h ▸ yj)
  have uv := apart u.property xu yv
  have um : u.val ∈ A := ⟨u.property,Or.inl xu⟩
  have vm : v.val ∈ A := ⟨v.property,Or.inr yv⟩
  have left (w) (wr : w ∈ R) (xw : G.Adj x w) : w = u.val := by
    by_contra wu
    exact many ((Set.two_lt_ncard_iff (s := A)).mpr ⟨w,u.val,v.val,⟨wr,Or.inl xw⟩,um,vm,wu,apart wr xw yv,uv⟩)
  have right (w) (wr : w ∈ R) (yw : G.Adj y w) : w = v.val := by
    by_contra wv
    exact many ((Set.two_lt_ncard_iff (s := A)).mpr ⟨u.val,v.val,w,um,vm,⟨wr,Or.inr yw⟩,uv,apart u.property xu yw,Ne.symm wv⟩)
  refine .inr ⟨(by omega : A.ncard ≤ 2),⟨u,xu,fun i h => Subtype.ext (left i.val i.property h)⟩,
    ⟨v,yv,fun i h => Subtype.ext (right i.val i.property h)⟩,?_⟩
  rcases thinRegionRoutes G block xy R xr yr bound split u v xu yv left right floor absent smaller with
    ⟨size,r,hr,len,inc⟩ | ⟨k,hk,size,r,hr,len,inc⟩
  · obtain ⟨p,hp,lp,pc⟩ := lift r hr inc
    exact ⟨by omega,.inl ⟨size,p,hp,by omega,pc⟩⟩
  · obtain ⟨p,hp,lp,pc⟩ := lift r hr inc
    have range : 3 ≤ k := by
      by_contra h
      have eq : k = 2 := by omega
      subst k
      have avoids := (markedDetourAvoids ab absent uncov p hp (by omega)).2.1 3 (by decide)
      omega
    have eight : 2^3 ≤ 2^k := Nat.pow_le_pow_right (by decide) range
    exact ⟨by omega,.inr ⟨k,range,size,p,hp,by omega,pc⟩⟩

/-- Without a sixteen-cycle through the first terminal, two lengths on one
side rule out the first exponents in the indicated family on a disjoint side. -/
theorem shiftExclusionsAtSixteen {V : Type*} {G : SimpleGraph V} {a b : V}
    {C D : Set V} (dis : Disjoint C D)
    (no16 : ¬ ∃ c : G.Walk a a, c.IsCycle ∧ c.length = 16) :
    let path (S : Set V) (l : ℕ) := ∃ p : G.Walk a b, p.IsPath ∧ p.length = l ∧
      ∀ i ∈ p.support, i ≠ a → i ≠ b → i ∈ S
    (path C 6 → path C 10 → ∀ k : ℕ, 2 ≤ k → path D (2^k+2) → 4 ≤ k) ∧
    (path C 5 → path C 11 → ¬path D 5 ∧ ∀ k : ℕ, 3 ≤ k → path D (2^k+3) → 4 ≤ k) := by
  let path (S : Set V) (l : ℕ) := ∃ p : G.Walk a b, p.IsPath ∧ p.length = l ∧
    ∀ i ∈ p.support, i ≠ a → i ≠ b → i ∈ S
  have clash {s t : ℕ} (sum : s+t=16) (left : path C s) (right : path D t) : False := by
    obtain ⟨p,hp,lp,pc⟩ := left
    obtain ⟨q,hq,lq,qd⟩ := right
    obtain ⟨c,hc,lc⟩ := joinTerminalPaths p q hp hq (by
      intro i ip iq
      by_contra! h
      exact Set.disjoint_left.mp dis (pc i ip h.1 h.2) (qd i iq h.1 h.2)) (by omega)
    exact no16 ⟨c,hc,by omega⟩
  constructor
  · intro six ten k hk p
    by_contra h
    rcases (show k=2 ∨ k=3 by omega) with rfl | rfl
    · exact clash (s := 10) (t := 6) rfl ten p
    · exact clash (s := 6) (t := 10) rfl six p
  · intro five eleven
    refine ⟨fun p => clash (s := 11) (t := 5) rfl eleven p,?_⟩
    intro k hk p
    by_contra h
    have eq : k=3 := by omega
    subst k
    exact clash (s := 5) (t := 11) rfl five p

/-- At scale sixteen the opposite pair imposes a lower bound on one individual
component, independent of the total order of the graph or the side. -/
theorem componentAtSixteen {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (block : ∀ (z : V) (S : Set V), z ∈ S → (∃ u ∈ S, u ≠ z) → (∃ v, v ∉ S) →
      ∃ u ∈ S, u ≠ z ∧ ∃ v ∉ S, G.Adj u v)
    {a b x y : V} (ab : G.Adj a b) (C : Set V) (ca : a ∉ C) (cb : b ∉ C)
    (xc : x ∈ C) (yc : y ∈ C) (ax : G.Adj a x) (by' : G.Adj b y) (xy : x ≠ y)
    (R : Set V) (live : R.Nonempty) (sub : R ⊆ C) (xr : x ∉ R) (yr : y ∉ R)
    (conn : (G.induce R).Connected)
    (bound : ∀ u ∈ R, ∀ v, G.Adj u v → v ∈ R ∨ v = x ∨ v = y)
    (split : ∀ u ∈ R, G.Adj x u → ¬ G.Adj y u) (floor : ∀ i, 3 ≤ G.degree i)
    (absent : ¬ ∃ (k : ℕ) (w : V) (c : G.Walk w w), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2^k)
    (uncov : ¬ ∃ (k : ℕ) (w : V) (c : G.Walk w w),
      1 ≤ k ∧ c.IsCycle ∧ c.length = 2^k+1 ∧ s(a,b) ∈ c.edges)
    (smaller : ∀ (W : Type) [Fintype W] (K : SimpleGraph W) [DecidableRel K.Adj],
      Fintype.card W < Fintype.card V → 3 ≤ K.minDegree →
      (∀ (z : W) (S : Set W), z ∈ S → (∃ i ∈ S, i ≠ z) → (∃ j, j ∉ S) →
        ∃ i ∈ S, i ≠ z ∧ ∃ j ∉ S, K.Adj i j) →
      ∃ (k : ℕ) (w : W) (c : K.Walk w w), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2^k)
    {D : Set V} (dis : Disjoint D (insert x (insert y R))) :
    let path (S : Set V) (l : ℕ) := ∃ p : G.Walk a b, p.IsPath ∧ p.length = l ∧
      ∀ i ∈ p.support, i ≠ a → i ≠ b → i ∈ S
    let ports := {i | i ∈ R ∧ (G.Adj x i ∨ G.Adj y i)}.ncard
    (path D 6 → path D 10 → 3 ≤ ports → 15 ≤ R.ncard ∧
      ∃ k : ℕ, 4 ≤ k ∧ path (insert x (insert y R)) (2^k+2)) ∧
    (path D 5 → path D 11 → ports ≤ 2 → 16 ≤ R.ncard ∧
      ∃ k : ℕ, 4 ≤ k ∧ path (insert x (insert y R)) (2^k+3)) := by
  have no16 : ¬ ∃ c : G.Walk a a, c.IsCycle ∧ c.length = 16 := by
    rintro ⟨c,hc,len⟩
    exact absent ⟨4,a,c,by decide,hc,len⟩
  obtain ⟨evenCase,oddCase⟩ := shiftExclusionsAtSixteen (b := b) dis no16
  have data := componentSpectrum G block ab C ca cb xc yc ax by' xy R live sub xr yr conn bound split
    floor absent uncov smaller
  constructor
  · intro six ten many
    rcases data with ⟨_,k,hk,p⟩ | ⟨few,_⟩
    · have four := evenCase six ten k hk p
      have k16 : 2^4 ≤ 2^k := Nat.pow_le_pow_right (by decide) four
      obtain ⟨w,hw,wl,wi⟩ := p
      have cap := detourLengthBound w hw wi
      have a₁ := Set.ncard_insert_le x (insert y R)
      have a₂ := Set.ncard_insert_le y R
      exact ⟨by omega,k,four,w,hw,wl,wi⟩
    · exact (not_le_of_gt many few).elim
  · intro five eleven few
    obtain ⟨no5,big⟩ := oddCase five eleven
    rcases data with ⟨many,_⟩ | ⟨_,_,_,_,⟨_,f⟩ | ⟨k,hk,size,p⟩⟩
    · exact (not_le_of_gt many few).elim
    · exact (no5 f).elim
    · have four := big k hk p
      have k16 : 2^4 ≤ 2^k := Nat.pow_le_pow_right (by decide) four
      exact ⟨by omega,k,four,p⟩

/-- Every proper side forces a dyadic-plus-two path, or has two disjoint
interior components. In the latter case the smaller component gives a bound
on the exponent of the forced odd path. -/
theorem bankSpectrum {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (block : ∀ (z : V) (S : Set V), z ∈ S → (∃ x ∈ S, x ≠ z) → (∃ y, y ∉ S) →
      ∃ x ∈ S, x ≠ z ∧ ∃ y ∉ S, G.Adj x y)
    {a b : V} (ab : G.Adj a b) (C : Set V) (ne : C.Nonempty) (ca : a ∉ C) (cb : b ∉ C)
    (bound : ∀ x ∈ C, ∀ y, G.Adj x y → y ∈ C ∨ y = a ∨ y = b)
    (floor : ∀ i, 3 ≤ G.degree i) (proper : C.ncard+2 < Fintype.card V)
    (absent : ¬ ∃ (k : ℕ) (w : V) (c : G.Walk w w), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2^k)
    (uncov : ¬ ∃ (k : ℕ) (w : V) (c : G.Walk w w),
      1 ≤ k ∧ c.IsCycle ∧ c.length = 2^k+1 ∧ s(a,b) ∈ c.edges)
    (smaller : ∀ (W : Type) [Fintype W] (K : SimpleGraph W) [DecidableRel K.Adj],
      Fintype.card W < Fintype.card V → 3 ≤ K.minDegree →
      (∀ (z : W) (S : Set W), z ∈ S → (∃ x ∈ S, x ≠ z) → (∃ y, y ∉ S) →
        ∃ x ∈ S, x ≠ z ∧ ∃ y ∉ S, K.Adj x y) →
      ∃ (k : ℕ) (w : W) (c : K.Walk w w), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2^k) :
    let route (l : ℕ) := ∃ p : G.Walk a b, p.IsPath ∧ p.length = l ∧
      ∀ i ∈ p.support, i ≠ a → i ≠ b → i ∈ C
    (∃ k : ℕ, 2 ≤ k ∧ route (2^k+2)) ∨ (18 ≤ C.ncard ∧
      (∀ x y : C, G.Adj a x.val → G.Adj b y.val →
        ¬(G.induce {i | i ∈ C ∧ i ≠ x.val ∧ i ≠ y.val}).Connected) ∧
      (route 5 ∨ ∃ k : ℕ, 3 ≤ k ∧ 2*2^k+2 ≤ C.ncard ∧ route (2^k+3))) := by
  classical
  obtain ⟨_,⟨x,ax,uniqueX⟩,y,byEdge,uniqueY⟩ :=
    bankTopologyUncovered G smaller absent block ab C ne ca cb bound
      (fun u _ => floor u) proper uncov
  obtain ⟨xy,noChord,apart⟩ := uncoveredPortsSeparated ab C ca cb x.property y.property ax byEdge absent uncov
  let P := {i : V | i ∈ C ∧ i ≠ x.val ∧ i ≠ y.val}
  have boundP (i : V) (hi : i ∈ P) (j : V) (ij : G.Adj i j) : j ∈ P ∨ j = x.val ∨ j = y.val := by
    rcases bound i hi.1 j ij with jc | rfl | rfl
    · by_cases jx : j = x.val
      · exact Or.inr (Or.inl jx)
      by_cases jy : j = y.val
      · exact Or.inr (Or.inr jy)
      · exact Or.inl ⟨jc,jx,jy⟩
    · exact (hi.2.1 (congrArg Subtype.val (uniqueX ⟨i,hi.1⟩ ij.symm))).elim
    · exact (hi.2.2 (congrArg Subtype.val (uniqueY ⟨i,hi.1⟩ ij.symm))).elim
  let E := (G.neighborFinset x.val).erase a
  have count : 1 < E.card := by
    have d := floor x.val
    rw [show E.card = _ from Finset.card_erase_of_mem ((G.mem_neighborFinset ..).mpr ax.symm),
      card_neighborFinset_eq_degree]
    omega
  obtain ⟨m,hm,n,hn,mn⟩ := Finset.one_lt_card.mp count
  have port {w : V} (hw : w ∈ E) : w ∈ P ∧ G.Adj x.val w := by
    obtain ⟨wa,mem⟩ := Finset.mem_erase.mp hw
    have xw := (G.mem_neighborFinset ..).mp mem
    have wc : w ∈ C := by
      rcases bound x.val x.property w xw with wc | eq | wb
      · exact wc
      · exact (wa eq).elim
      · exact (xy (congrArg Subtype.val (uniqueY x (wb ▸ xw.symm)))).elim
    exact ⟨⟨wc,xw.ne.symm,fun e => noChord (e ▸ xw)⟩,xw⟩
  obtain ⟨mp,xm⟩ := port hm
  obtain ⟨np,xn⟩ := port hn
  let route (l : ℕ) := ∃ p : G.Walk a b, p.IsPath ∧ p.length = l ∧
    ∀ i ∈ p.support, i ≠ a → i ≠ b → i ∈ C
  change (∃ k : ℕ, 2 ≤ k ∧ route (2^k+2)) ∨ (18 ≤ C.ncard ∧
    (∀ x y : C, G.Adj a x.val → G.Adj b y.val →
      ¬(G.induce {i | i ∈ C ∧ i ≠ x.val ∧ i ≠ y.val}).Connected) ∧
    (route 5 ∨ ∃ k : ℕ, 3 ≤ k ∧ 2*2^k+2 ≤ C.ncard ∧ route (2^k+3)))
  by_cases even : ∃ k : ℕ, 2 ≤ k ∧ route (2^k+2)
  · exact .inl even
  have classify (R : Set V) (live : R.Nonempty) (rp : R ⊆ P) (conn : (G.induce R).Connected)
      (br : ∀ u ∈ R, ∀ v, G.Adj u v → v ∈ R ∨ v = x.val ∨ v = y.val) :
      (∃! i : R, G.Adj x.val i.val) ∧ 8 ≤ R.ncard ∧
        (route 5 ∨ ∃ k : ℕ, 3 ≤ k ∧ 2^k ≤ R.ncard ∧ route (2^k+3)) := by
    have sub : R ⊆ C := fun _ h => (rp h).1
    have inc : insert x.val (insert y.val R) ⊆ C := Set.insert_subset x.property (Set.insert_subset y.property sub)
    have widen {l : ℕ} {p : G.Walk a b} (hp : p.IsPath) (eq : p.length = l)
        (inside : ∀ i ∈ p.support, i ≠ a → i ≠ b → i ∈ insert x.val (insert y.val R)) : route l :=
      ⟨p,hp,eq,fun i hi ia ib => inc (inside i hi ia ib)⟩
    rcases componentSpectrum G block ab C ca cb x.property y.property ax byEdge xy R live sub
      (fun h => (rp h).2.1 rfl) (fun h => (rp h).2.2 rfl) conn br
      (fun i hi => apart i (rp hi).1) floor absent uncov smaller with
      ⟨_,k,hk,p,hp,len,inside⟩ | ⟨_,unique,_,size,alt⟩
    · exact (even ⟨k,hk,widen hp len inside⟩).elim
    refine ⟨unique,size,?_⟩
    rcases alt with ⟨_,p,hp,len,inside⟩ | ⟨k,hk,sk,p,hp,len,inside⟩
    · exact .inl (widen hp len inside)
    · exact .inr ⟨k,hk,sk,widen hp len inside⟩
  obtain ⟨R,rl,rp,rc,br⟩ := chooseConnectedRegion G P ⟨m,mp⟩ boundP
  obtain ⟨⟨u,_,unique⟩,rsize,rs⟩ := classify R rl rp rc br
  have rest : (P \ R).Nonempty := by
    by_cases mr : m ∈ R
    · refine ⟨n,np,fun nr => mn ?_⟩
      exact (congrArg Subtype.val (unique ⟨m,mr⟩ xm)).trans
        (congrArg Subtype.val (unique ⟨n,nr⟩ xn)).symm
    · exact ⟨m,mp,mr⟩
  have gap : ¬(G.induce P).Connected := by
    intro conn
    obtain ⟨i,ir⟩ := rl
    obtain ⟨j,jp,jr⟩ := rest
    obtain ⟨w⟩ := conn.preconnected (⟨i,rp ir⟩ : P) ⟨j,jp⟩
    obtain ⟨d,_,hin,hout⟩ := w.exists_boundary_dart {v : P | v.val ∈ R} ir jr
    rcases br d.fst.val hin d.snd.val d.adj with hit | eq | eq
    · exact hout hit
    · exact d.snd.property.2.1 eq
    · exact d.snd.property.2.2 eq
  obtain ⟨S,sl,srest,sc,bs⟩ := chooseConnectedRegion G (P \ R) rest (by
    intro i hi j ij
    rcases boundP i hi.1 j ij with jp | endpts
    · refine Or.inl ⟨jp,fun jr => ?_⟩
      rcases br j jr i ij.symm with ir | ix | iy
      · exact hi.2 ir
      · exact hi.1.2.1 ix
      · exact hi.1.2.2 iy
    · exact Or.inr endpts)
  have sp : S ⊆ P := fun _ h => (srest h).1
  obtain ⟨_,ssize,ss⟩ := classify S sl sp sc bs
  have dis : Disjoint R S := Set.disjoint_left.mpr fun _ hr hs => (srest hs).2 hr
  have both : R ∪ S ⊆ P := Set.union_subset rp sp
  have withoutX : x.val ∉ R ∪ S := fun h => (both h).2.1 rfl
  have withoutY : y.val ∉ R ∪ S := fun h => (both h).2.2 rfl
  have subset : insert x.val (insert y.val (R ∪ S)) ⊆ C :=
    Set.insert_subset x.property (Set.insert_subset y.property (fun _ h => (both h).1))
  have cap := Set.ncard_le_ncard subset
  rw [Set.ncard_insert_of_notMem (by simp [xy,withoutX]),Set.ncard_insert_of_notMem withoutY,
    Set.ncard_union_eq dis] at cap
  refine .inr ⟨by omega,?_,?_⟩
  · intro x' y' ax' by'
    rw [uniqueX x' ax',uniqueY y' by']
    exact gap
  by_cases five : route 5
  · exact .inl five
  have pick (T : Set V) (half : 2*T.ncard+2 ≤ C.ncard)
      (alt : route 5 ∨ ∃ k : ℕ, 3 ≤ k ∧ 2^k ≤ T.ncard ∧ route (2^k+3)) :
      ∃ k : ℕ, 3 ≤ k ∧ 2*2^k+2 ≤ C.ncard ∧ route (2^k+3) := by
    obtain ⟨k,hk,size,p⟩ := alt.resolve_left five
    exact ⟨k,hk,by omega,p⟩
  rcases le_total R.ncard S.ncard with h | h
  · exact .inr (pick R (by omega) rs)
  · exact .inr (pick S (by omega) ss)

/-- Apply the side spectrum to either pair summing to sixteen. The size
conditions count internal vertices and impose no bound on the whole graph. -/
theorem bankAtSixteen {V : Type*} [Finite V] {G : SimpleGraph V} {a b : V}
    {C D : Set V} (dis : Disjoint C D)
    (no16 : ¬ ∃ c : G.Walk a a, c.IsCycle ∧ c.length = 16) :
    let path (S : Set V) (l : ℕ) := ∃ p : G.Walk a b, p.IsPath ∧ p.length = l ∧
      ∀ i ∈ p.support, i ≠ a → i ≠ b → i ∈ S
    ((∃ k : ℕ, 2 ≤ k ∧ path D (2^k+2)) ∨ (18 ≤ D.ncard ∧
      (path D 5 ∨ ∃ k : ℕ, 3 ≤ k ∧ 2*2^k+2 ≤ D.ncard ∧ path D (2^k+3)))) →
    (path C 6 → path C 10 → 17 ≤ D.ncard ∧
      ((∃ k : ℕ, 4 ≤ k ∧ path D (2^k+2)) ∨ 18 ≤ D.ncard)) ∧
    (path C 5 → path C 11 → (∃ k : ℕ, 2 ≤ k ∧ path D (2^k+2)) ∨
      (34 ≤ D.ncard ∧ ∃ k : ℕ, 4 ≤ k ∧ 2*2^k+2 ≤ D.ncard ∧ path D (2^k+3))) := by
  dsimp only
  intro data
  obtain ⟨evenCase,oddCase⟩ := shiftExclusionsAtSixteen (b := b) dis no16
  constructor
  · intro six ten
    rcases data with ⟨k,hk,p⟩ | ⟨size,_⟩
    · have four := evenCase six ten k hk p
      have k16 : 2^4 ≤ 2^k := Nat.pow_le_pow_right (by decide) four
      obtain ⟨w,hw,wl,inside⟩ := p
      have cap := detourLengthBound w hw inside
      exact ⟨by omega,.inl ⟨k,four,w,hw,wl,inside⟩⟩
    · exact ⟨by omega,.inr size⟩
  · intro five eleven
    obtain ⟨no5,big⟩ := oddCase five eleven
    rcases data with even | ⟨_,alt⟩
    · exact .inl even
    obtain ⟨k,hk,half,p⟩ := alt.resolve_left no5
    have four := big k hk p
    have k16 : 2^4 ≤ 2^k := Nat.pow_le_pow_right (by decide) four
    exact .inr ⟨by omega,k,four,half,p⟩

/-- In a two-terminal side with one attachment at either end, deleting the
first and last edges of any proper terminal path gives a path in the induced
side. The two endpoints of the trimmed path are independent of the path. -/
theorem trimTerminalPath {V : Type*} {G : SimpleGraph V} {a b : V} (C : Set V) {x y : C}
    (first : ∀ i : C, G.Adj a i.val → i = x) (last : ∀ i : C, G.Adj b i.val → i = y)
    (p : G.Walk a b) (hp : p.IsPath) (long : 2 ≤ p.length)
    (inside : ∀ i ∈ p.support, i ≠ a → i ≠ b → i ∈ C) :
    ∃ r : (G.induce C).Walk x y, r.IsPath ∧ r.length+2 = p.length := by
  cases p with
  | nil => exact (by decide : ¬ 2 ≤ 0) long |>.elim
  | @cons _ u _ au q =>
    obtain ⟨hq,na⟩ := (Walk.cons_isPath_iff ..).mp hp
    have pos : ¬q.Nil := by
      rw [← Walk.length_eq_zero_iff]
      simp only [Walk.length_cons] at long
      omega
    have vb := q.adj_penultimate pos
    let r := q.dropLast
    have eq : r.concat vb = q := Walk.concat_dropLast vb
    obtain ⟨hr,nb⟩ := (Walk.concat_isPath_iff vb).mp (eq ▸ hq)
    have mem (i : V) (hi : i ∈ r.support) : i ∈ C := by
      have qi := eq ▸ r.support_subset_support_concat vb hi
      exact inside i (by simp [qi]) (fun e => na (e ▸ qi)) (fun e => nb (e ▸ hi))
    let t := r.induce C mem
    let inc := (Embedding.induce (G := G) C).toHom
    have mapEq : t.map inc = r := Walk.map_induce r mem
    have ht : t.IsPath := (show (t.map inc).IsPath by rw [mapEq]; exact hr).of_map
    have len : t.length = r.length := calc
      _ = (t.map inc).length := (Walk.length_map ..).symm
      _ = r.length := by rw [mapEq]; rfl
    have ux := first ⟨u,mem u r.start_mem_support⟩ au
    have vy := last ⟨q.penultimate,mem _ r.end_mem_support⟩ vb.symm
    rw [← ux,← vy]
    refine ⟨t,ht,?_⟩
    have lq : r.length+1 = q.length := by simpa only [Walk.length_concat] using congrArg Walk.length eq
    simp only [Walk.length_cons]
    omega

/-- In a bipartite induced interior, every proper terminal path has the same
length parity, even when the terminals themselves are outside the coloring. -/
theorem bipartiteSideParity {V : Type*} {G : SimpleGraph V} {a b : V} (C : Set V) {x y : C}
    (first : ∀ i : C, G.Adj a i.val → i = x) (last : ∀ i : C, G.Adj b i.val → i = y)
    (bip : (G.induce C).Colorable 2) (p q : G.Walk a b)
    (hp : p.IsPath) (lp : 2 ≤ p.length) (pc : ∀ i ∈ p.support, i ≠ a → i ≠ b → i ∈ C)
    (hq : q.IsPath) (lq : 2 ≤ q.length) (qc : ∀ i ∈ q.support, i ≠ a → i ≠ b → i ∈ C) :
    Even p.length ↔ Even q.length := by
  obtain ⟨r,_,lr⟩ := trimTerminalPath C first last p hp lp pc
  obtain ⟨s,_,ls⟩ := trimTerminalPath C first last q hq lq qc
  let c := recolorOfEquiv (G.induce C) finTwoEquiv bip.some
  have iff := (c.even_length_iff_congr r).trans (c.even_length_iff_congr s).symm
  simpa only [← lr,← ls,Nat.even_add,even_two,iff_true] using iff

/-- Bipartiteness of the interior alone forces a second separation. Opposite
lengths five and eleven then force at least thirty-four interior vertices. -/
theorem bipartiteBankAtSixteen {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (block : ∀ (z : V) (S : Set V), z ∈ S → (∃ x ∈ S, x ≠ z) → (∃ y, y ∉ S) →
      ∃ x ∈ S, x ≠ z ∧ ∃ y ∉ S, G.Adj x y)
    {a b : V} (ab : G.Adj a b) (C : Set V) (ne : C.Nonempty) (ca : a ∉ C) (cb : b ∉ C)
    (bound : ∀ x ∈ C, ∀ y, G.Adj x y → y ∈ C ∨ y = a ∨ y = b)
    (floor : ∀ i, 3 ≤ G.degree i) (proper : C.ncard+2 < Fintype.card V)
    (absent : ¬ ∃ (k : ℕ) (w : V) (c : G.Walk w w), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2^k)
    (uncov : ¬ ∃ (k : ℕ) (w : V) (c : G.Walk w w),
      1 ≤ k ∧ c.IsCycle ∧ c.length = 2^k+1 ∧ s(a,b) ∈ c.edges)
    (smaller : ∀ (W : Type) [Fintype W] (K : SimpleGraph W) [DecidableRel K.Adj],
      Fintype.card W < Fintype.card V → 3 ≤ K.minDegree →
      (∀ (z : W) (S : Set W), z ∈ S → (∃ x ∈ S, x ≠ z) → (∃ y, y ∉ S) →
        ∃ x ∈ S, x ≠ z ∧ ∃ y ∉ S, K.Adj x y) →
      ∃ (k : ℕ) (w : W) (c : K.Walk w w), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2^k)
    (bip : (G.induce C).Colorable 2) :
    let path (S : Set V) (l : ℕ) := ∃ p : G.Walk a b, p.IsPath ∧ p.length = l ∧
      ∀ i ∈ p.support, i ≠ a → i ≠ b → i ∈ S
    18 ≤ C.ncard ∧ (∀ x y : C, G.Adj a x.val → G.Adj b y.val →
      ¬(G.induce {i | i ∈ C ∧ i ≠ x.val ∧ i ≠ y.val}).Connected) ∧
    ∀ D, Disjoint D C → path D 5 → path D 11 →
      34 ≤ C.ncard ∧ ∃ k : ℕ, 4 ≤ k ∧ 2*2^k+2 ≤ C.ncard ∧ path C (2^k+3) := by
  obtain ⟨_,⟨x,_,first⟩,y,_,last⟩ := bankTopologyUncovered G smaller absent block ab C ne ca cb bound
    (fun i _ => floor i) proper uncov
  obtain ⟨j,p,hj,hp,lp,pc⟩ := allBankDetour G block ab C ne ca cb bound
    (fun i => floor i.val) proper absent uncov smaller
  have jpos : 2^2 ≤ 2^j := Nat.pow_le_pow_right (by decide) hj
  have je : Even (2^j : ℕ) := even_two.pow_of_ne_zero (by omega)
  have odd : ¬Even p.length := by simpa only [lp,Nat.even_add_one,not_not] using je
  rcases bankSpectrum G block ab C ne ca cb bound floor proper absent uncov smaller with
    ⟨k,hk,q,hq,lq,qc⟩ | ⟨size,gap,alt⟩
  · have kpos : 2^2 ≤ 2^k := Nat.pow_le_pow_right (by decide) hk
    have equiv := bipartiteSideParity C first last bip p q hp (by omega) pc hq (by omega) qc
    exact (odd (equiv.mpr (lq ▸ (even_two.pow_of_ne_zero (by omega)).add even_two))).elim
  refine ⟨size,gap,?_⟩
  intro D dis five eleven
  have no16 : ¬ ∃ c : G.Walk a a, c.IsCycle ∧ c.length = 16 := by
    rintro ⟨c,hc,len⟩
    exact absent ⟨4,a,c,by decide,hc,len⟩
  obtain ⟨no5,big⟩ := (shiftExclusionsAtSixteen (b := b) dis no16).2 five eleven
  obtain ⟨k,hk,half,q⟩ := alt.resolve_left no5
  have four := big k hk q
  have k16 : 2^4 ≤ 2^k := Nat.pow_le_pow_right (by decide) four
  exact ⟨by omega,k,four,half,q⟩

/-- Blocks in which every edge is on a cycle one longer than a power of two. -/
def H1 : Prop :=
  ∀ (V : Type) (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj],
    3 ≤ G.minDegree →
    (∀ (z : V) (S : Set V), z ∈ S → (∃ x ∈ S, x ≠ z) → (∃ y, y ∉ S) →
      ∃ x ∈ S, x ≠ z ∧ ∃ y ∉ S, G.Adj x y) →
    (∀ a b, G.Adj a b → ∃ (k : ℕ) (w : V) (c : G.Walk w w),
      1 ≤ k ∧ c.IsCycle ∧ c.length = 2 ^ k + 1 ∧ s(a,b) ∈ c.edges) →
    ∃ (k : ℕ) (w : V) (c : G.Walk w w), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2 ^ k

/-- At an uncovered edge the graph separates. The covered spanning block and
the shapes and path lengths of the separated regions constrain this case. -/
def H2 : Prop :=
  ∀ (V : Type) (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj],
    let n := Fintype.card V
    let covered (a b : V) := ∃ (k : ℕ) (w : V) (c : G.Walk w w),
      1 ≤ k ∧ c.IsCycle ∧ c.length = 2^k+1 ∧ s(a,b) ∈ c.edges
    let bad (a b : V) := G.Adj a b ∧ ¬ covered a b
    let bank (a b : V) (C : Set V) := C.Nonempty ∧ a ∉ C ∧ b ∉ C ∧ C.ncard+2 < n ∧
      ∀ x ∈ C, ∀ y, G.Adj x y → y ∈ C ∨ y = a ∨ y = b
    let path (a b : V) (C : Set V) (l : ℕ) := ∃ p : G.Walk a b, p.IsPath ∧ p.length = l ∧
      ∀ x ∈ p.support, x ≠ a → x ≠ b → x ∈ C
    3 ≤ G.minDegree → (∃ a b, bad a b) →
    (∀ a b, bad a b → G.degree a = 3 ∧ (∀ c, bad a c → b = c) ∧
      ∃ S : Set V, a ∈ S ∧ b ∈ S ∧ (∃ x ∈ S, x ≠ a ∧ x ≠ b) ∧ (∃ y, y ∉ S) ∧
        ∀ x ∈ S, x ≠ a → x ≠ b → ∀ y ∉ S, ¬ G.Adj x y) →
    (∃ H : SimpleGraph V, H ≤ G ∧ n+7 ≤ H.edgeFinset.card ∧
      14 ≤ (Finset.univ.filter (fun v => 3 ≤ H.degree v)).card ∧
      (∀ (z : V) (S : Set V), z ∈ S → (∃ x ∈ S, x ≠ z) → (∃ y, y ∉ S) →
        ∃ x ∈ S, x ≠ z ∧ ∃ y ∉ S, H.Adj x y) ∧ ∀ a b, H.Adj a b → covered a b) →
    (∀ a b, bad a b → ∀ C, bank a b C →
      let p := path a b
      (G.induce C).Connected ∧ (∃! x : C, G.Adj a x.val) ∧ (∃! x : C, G.Adj b x.val) ∧
      (∃ k : ℕ, 2 ≤ k ∧ p C (2^k+1)) ∧
      ((∃ k : ℕ, 2 ≤ k ∧ p C (2^k+2)) ∨ (18 ≤ C.ncard ∧
        (∀ x y : C, G.Adj a x.val → G.Adj b y.val →
          ¬(G.induce {i | i ∈ C ∧ i ≠ x.val ∧ i ≠ y.val}).Connected) ∧
        (p C 5 ∨ ∃ k : ℕ, 3 ≤ k ∧ 2*2^k+2 ≤ C.ncard ∧ p C (2^k+3)))) ∧
      (∀ D, Disjoint D C → (p D 6 → p D 10 → 17 ≤ C.ncard) ∧
        (p D 5 → p D 11 → (G.induce C).Colorable 2 → 34 ≤ C.ncard)) ∧
      (2*C.ncard+2 < n → 9 ≤ C.ncard ∧ ∃ (k s t : ℕ), 4 ≤ k ∧ 5 ≤ s ∧
        s+2 ≤ 2^(k-1) ∧ 2^(k-1)+2 ≤ t ∧ s+t = 2^k ∧ p C s ∧ p C t ∧
        ∀ D : Set V, Disjoint C D → ¬ p D s ∧ ¬ p D t)) →
    ∃ (k : ℕ) (w : V) (c : G.Walk w w), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2^k

theorem main : H1 → H2 → OMA.R_Erdos64_erdos_64_R3.H1 := by
  intro full separated
  have descend (n : ℕ) : ∀ (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
      Fintype.card V = n → 3 ≤ G.minDegree →
      (∀ (t : V) (S : Set V), t ∈ S → (∃ x ∈ S, x ≠ t) → (∃ y, y ∉ S) →
        ∃ x ∈ S, x ≠ t ∧ ∃ y ∉ S, G.Adj x y) →
      ∃ (k : ℕ) (w : V) (c : G.Walk w w), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2^k := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro V finite G dec size low block
      classical
      by_contra none
      let lengths : Set ℕ := {m | ∃ k : ℕ, 2 ≤ k ∧ m = 2^k}
      let covered (a b : V) := ∃ (k : ℕ) (w : V) (c : G.Walk w w),
        1 ≤ k ∧ c.IsCycle ∧ c.length = 2^k + 1 ∧ s(a,b) ∈ c.edges
      let good (a b : V) := ∀ S : Set V, a ∈ S → b ∈ S → (∃ x ∈ S, x ≠ a ∧ x ≠ b) →
        (∃ y, y ∉ S) → ∃ x ∈ S, x ≠ a ∧ x ≠ b ∧ ∃ y ∉ S, G.Adj x y
      have avoid (w) (c : G.Walk w w) (hc : c.IsCycle) : c.length ∉ lengths := by
        rintro ⟨k,hk,leq⟩
        exact none ⟨k,w,c,hk,hc,leq⟩
      have cert (a b : V) (ab : G.Adj a b) (safe : good a b) : covered a b := by
        obtain ⟨w,c,hc,edge,tri | ⟨m,⟨k,hk,hm⟩,hl⟩⟩ :=
          cycleThroughNonseparatingEdge G lengths (fun t => low.trans (G.minDegree_le_degree t))
            block avoid (by
              intro W inst K z lt degs _ smallerBlock
              have : Nonempty W := ⟨z⟩
              obtain ⟨k,w,c,hk,hc,hl⟩ := ih _ (lt.trans_eq size) W K rfl
                (K.le_minDegree_of_forall_le_degree 3 degs) smallerBlock
              exact ⟨w,c,hc,k,hk,hl⟩) ab safe
        · exact ⟨1,w,c,by decide,hc,tri,edge⟩
        · exact ⟨k,w,c,by omega,hc,hm ▸ hl,edge⟩
      by_cases allCovered : ∀ a b, G.Adj a b → covered a b
      · exact none (full V G low block allCovered)
      · push Not at allCovered
        have smaller (W : Type) [Fintype W] (K : SimpleGraph W) [DecidableRel K.Adj]
            (lt : Fintype.card W < Fintype.card V) (lowK : 3 ≤ K.minDegree)
            (blockK : ∀ (t : W) (S : Set W), t ∈ S → (∃ x ∈ S, x ≠ t) → (∃ y, y ∉ S) →
              ∃ x ∈ S, x ≠ t ∧ ∃ y ∉ S, K.Adj x y) :
            ∃ (k : ℕ) (w : W) (c : K.Walk w w), 2 ≤ k ∧ c.IsCycle ∧ c.length = 2^k :=
          ih _ (lt.trans_eq size) W K rfl lowK blockK
        have floor (u : V) := low.trans (G.minDegree_le_degree u)
        have cut (a b : V) (ab : G.Adj a b) (uncov : ¬ covered a b) :
            ∃ S : Set V, a ∈ S ∧ b ∈ S ∧ (∃ x ∈ S, x ≠ a ∧ x ≠ b) ∧ (∃ y, y ∉ S) ∧
              ∀ x ∈ S, x ≠ a → x ≠ b → ∀ y ∉ S, ¬ G.Adj x y := by
          have h : ¬ good a b := fun safe => uncov (cert a b ab safe)
          unfold good at h
          push Not at h
          exact h
        have cubic (a b : V) (ab : G.Adj a b) (uncov : ¬ covered a b) : G.degree a = 3 := by
          obtain ⟨S,ha,hb,ins,out,gap⟩ := cut a b ab uncov
          exact (terminalDegrees G ab (fun C live ca cb bound proper =>
            (bankTopologyUncovered G smaller none block ab C live ca cb bound
              (fun u _ => floor u) proper uncov).2) S ha hb ins out gap).1
        let D := SimpleGraph.fromRel (fun a b => G.Adj a b ∧ covered a b)
        let : DecidableRel D.Adj := fun _ _ => Classical.propDecidable _
        have inD (a b : V) (ab : G.Adj a b) (p : good a b) : D.Adj a b :=
          ⟨ab.ne, Or.inl ⟨ab,cert a b ab p⟩⟩
        have fromD (a b : V) (d : D.Adj a b) : G.Adj a b ∧ covered a b := by
          rcases d.2 with h | ⟨ba,k,w,c,hk,hc,hl,he⟩
          · exact h
          · exact ⟨ba.symm,k,w,c,hk,hc,hl,(Sym2.eq_swap ..) ▸ he⟩
        have subD : D ≤ G := fun {a b} e => (fromD a b e).1
        have certD (a b : V) (e : D.Adj a b) := (fromD a b e).2
        have blockD (t : V) (S : Set V) (ht : t ∈ S) (i : ∃ x ∈ S, x ≠ t) (o : ∃ y, y ∉ S) :
            ∃ a ∈ S, a ≠ t ∧ ∃ b ∉ S, D.Adj a b := by
          obtain ⟨J,sub,bJ,edges⟩ := spanningNonseparatingEdges G block
          obtain ⟨a,ha,at',b,hb,edge⟩ := bJ t S ht i o
          exact ⟨a,ha,at',b,hb,inD a b (sub edge) (edges a b edge)⟩
        apply none
        apply separated V G low allCovered
        · rintro a b ⟨ab,uncov⟩
          refine ⟨cubic a b ab uncov,?_,cut a b ab uncov⟩
          rintro c ⟨ac,noC⟩
          exact uncoveredMatching G D covered subD blockD certD
            (fun u v uv h => (cubic u v uv h).le) a b c ab uncov ac noC
        · obtain ⟨a,b,ab,uncov⟩ := allCovered
          obtain ⟨S,ha,hb,i,o,gap⟩ := cut a b ab uncov
          obtain ⟨high,count⟩ := twoBankCore G D floor
            (noDyadic_commonNeighbor_unique none) block inD ab S ha hb i o gap
          exact ⟨D,subD,count,high,blockD,certD⟩
        · rintro a b ⟨ab,uncov⟩ C ⟨live,ca,cb,proper,bound⟩
          have shape := bankTopologyUncovered G smaller none block ab C live ca cb bound
            (fun u _ => floor u) proper uncov
          obtain ⟨k,p,hk,hp,len,pc⟩ := allBankDetour G block ab C live ca cb bound
            (fun u => floor u.val) proper none uncov smaller
          have spectrum := bankSpectrum G block ab C live ca cb bound floor proper none uncov smaller
          refine ⟨shape.1,shape.2.1,shape.2.2,⟨k,hk,p,hp,len,pc⟩,spectrum,?_,?_⟩
          · intro D dis
            have no16 : ¬ ∃ c : G.Walk a a, c.IsCycle ∧ c.length = 16 := by
              rintro ⟨c,hc,hl⟩
              exact none ⟨4,a,c,by decide,hc,hl⟩
            have coarse := spectrum.imp id (fun h => And.intro h.1 h.2.2)
            obtain ⟨forEven,_⟩ := bankAtSixteen (b := b) dis no16 coarse
            refine ⟨fun six ten => (forEven six ten).1,?_⟩
            intro five eleven bip
            have bi := bipartiteBankAtSixteen G block ab C live ca cb bound floor proper none uncov smaller bip
            exact (bi.2.2 D dis five eleven).1
          intro small
          exact exclusiveDetours ab none uncov C
            (forcedBankDetours G block ab C live ca cb bound (fun u => floor u.val)
              small none smaller)
  intro V G finite dec
  exact descend _ V G rfl

end OMA.R_Erdos64_erdos_64_R3_H1_R2
