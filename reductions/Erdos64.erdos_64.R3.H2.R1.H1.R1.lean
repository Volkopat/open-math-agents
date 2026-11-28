import OMAReductions.R_Erdos64_erdos_64_R3_H2_R1
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

/-! Transfer a cycle away from a marked edge using graph automorphisms.
The two alternatives for the cycle length are those of @Hennyrick in PR 2529. -/
namespace OMA.R_Erdos64_erdos_64_R3_H2_R1_H1_R1

open SimpleGraph

-- The ordinary dyadic witness can be anywhere when the marked orbit branches.
def H1 : Prop :=
  ∀ (V : Type) (K : SimpleGraph V) [Fintype V] [DecidableRel K.Adj] (a b : V),
    K.Adj b a → 3 ≤ K.minDegree →
    (∀ (z : V) (S : Set V), z ∈ S → (∃ x ∈ S, x ≠ z) → (∃ y, y ∉ S) →
      ∃ x ∈ S, x ≠ z ∧ ∃ y ∉ S, K.Adj x y) →
    (¬ ∃ t, K.Adj a t ∧ K.Adj b t) →
    (∃ x, 2 < ({y : V | ∃ f : K ≃g K, s(f b, f a) = s(x, y)} : Set V).ncard) →
    ∃ (k : ℕ) (v : V) (c : K.Walk v v), 2 ≤ k ∧ c.IsCycle ∧
      (c.length = 2^k ∨ (c.length + 1 = 2^k ∧ s(b,a) ∈ c.edges))

-- Otherwise the orbit of the marked edge has maximum degree at most two.
def H2 : Prop :=
  ∀ (V : Type) (K : SimpleGraph V) [Fintype V] [DecidableRel K.Adj] (a b : V),
    K.Adj b a → 3 ≤ K.minDegree →
    (∀ (z : V) (S : Set V), z ∈ S → (∃ x ∈ S, x ≠ z) → (∃ y, y ∉ S) →
      ∃ x ∈ S, x ≠ z ∧ ∃ y ∉ S, K.Adj x y) →
    (¬ ∃ t, K.Adj a t ∧ K.Adj b t) →
    (∀ x, ({y : V | ∃ f : K ≃g K, s(f b, f a) = s(x, y)} : Set V).ncard ≤ 2) →
    ∃ (k : ℕ) (v : V) (c : K.Walk v v), 2 ≤ k ∧ c.IsCycle ∧
      ((c.length = 2^k ∧ s(b,a) ∉ c.edges) ∨ (c.length + 1 = 2^k ∧ s(b,a) ∈ c.edges))

/-- A proof of the existing relaxed sibling from PR 2529 discharges the whole
branching-orbit obligation. -/
theorem branching_of_relaxed_sibling (relaxed : OMA.R_Erdos64_erdos_64_R3_H2_R1.H2) : H1 := by
  intro V K finite dec a b ba low cuts _ _
  have floor (x : V) : 3 ≤ K.degree x := low.trans (K.minDegree_le_degree x)
  exact relaxed V K a b ba (fun x => (by decide : 2 ≤ 3).trans (floor x))
    (fun x _ _ => floor x) cuts

theorem triangle_at_mark {V : Type} {K : SimpleGraph V} {a b t : V}
    (ba : K.Adj b a) (at' : K.Adj a t) (bt : K.Adj b t) :
    ∃ c : K.Walk b b, c.IsCycle ∧ c.length = 3 ∧ s(b,a) ∈ c.edges := by
  let p : K.Walk b b := .cons ba (.cons at' (.cons bt.symm .nil))
  refine ⟨p, ?_, rfl, by simp [p]⟩
  simp [p, Walk.cons_isCycle_iff, Walk.isPath_def, ba.ne, ba.ne.symm,
    at'.ne, bt.ne, bt.ne.symm, Sym2.eq, Sym2.rel_iff']

/-- Map a cycle back after finding an image of the marked edge that it misses. -/
theorem transport_avoiding {V : Type} {K : SimpleGraph V} {a b v : V}
    (f : K ≃g K) (c : K.Walk v v) (hc : c.IsCycle)
    (miss : s(f b, f a) ∉ c.edges) :
    ∃ (w : V) (d : K.Walk w w), d.IsCycle ∧ d.length = c.length ∧ s(b,a) ∉ d.edges := by
  let d := c.map f.symm.toHom
  refine ⟨f.symm v, d, hc.map f.symm.injective, by simp [d], ?_⟩
  intro uses
  change s(b,a) ∈ (c.map f.symm.toHom).edges at uses
  rw [Walk.edges_map] at uses
  obtain ⟨e, he, eq⟩ := List.mem_map.mp uses
  apply miss
  have same : e = s(f b, f a) := by
    apply (Sym2.map.injective f.symm.injective)
    simpa using eq
  exact same ▸ he

/-- At a branching vertex of the marked edge orbit a cycle misses an orbit edge,
even when the vertex itself does not lie on the cycle. -/
theorem avoid_branching_mark {V : Type} [Fintype V] {K : SimpleGraph V} {a b v : V}
    (c : K.Walk v v) (hc : c.IsCycle)
    (branch : ∃ x, 2 < ({y : V | ∃ f : K ≃g K, s(f b, f a) = s(x, y)} : Set V).ncard) :
    ∃ (w : V) (d : K.Walk w w), d.IsCycle ∧ d.length = c.length ∧ s(b,a) ∉ d.edges := by
  classical
  obtain ⟨x, hx⟩ := branch
  let N : Set V := {y | ∃ f : K ≃g K, s(f b, f a) = s(x,y)}
  change 2 < N.ncard at hx
  have missing : ∃ f : K ≃g K, s(f b, f a) ∉ c.edges := by
    by_contra! allUsed
    have incl : N ⊆ c.toSubgraph.neighborSet x := by
      rintro y ⟨f, h⟩
      exact Walk.adj_toSubgraph_iff_mem_edges.mpr (h ▸ allUsed f)
    obtain ⟨y, hy⟩ := (Set.ncard_pos (Set.toFinite N)).mp (by omega : 0 < N.ncard)
    have adj : c.toSubgraph.Adj x y := incl hy
    have size := hc.ncard_neighborSet_toSubgraph_eq_two (Walk.mem_support_of_adj_toSubgraph adj)
    have bound := Set.ncard_le_ncard incl
    omega
  obtain ⟨f, hf⟩ := missing
  exact transport_avoiding f c hc hf

theorem main : H1 → H2 → OMA.R_Erdos64_erdos_64_R3_H2_R1.H1 := by
  intro branching sparse V K finite dec a b ba low cuts
  classical
  by_cases triangle : ∃ t, K.Adj a t ∧ K.Adj b t
  · obtain ⟨t, at', bt⟩ := triangle
    obtain ⟨c, hc, len, uses⟩ := triangle_at_mark ba at' bt
    exact ⟨2, b, c, by decide, hc, Or.inr ⟨by omega, uses⟩⟩
  by_cases branch : ∃ x, 2 < ({y : V | ∃ f : K ≃g K, s(f b, f a) = s(x, y)} : Set V).ncard
  · obtain ⟨k, v, c, hk, hc, len | short⟩ := branching V K a b ba low cuts triangle branch
    · obtain ⟨w, d, hd, equal, miss⟩ := avoid_branching_mark c hc branch
      exact ⟨k, w, d, hk, hd, Or.inl ⟨equal.trans len, miss⟩⟩
    · exact ⟨k, v, c, hk, hc, Or.inr short⟩
  · exact sparse V K a b ba low cuts triangle (fun x => Nat.le_of_not_gt (fun h => branch ⟨x,h⟩))

end OMA.R_Erdos64_erdos_64_R3_H2_R1_H1_R1
