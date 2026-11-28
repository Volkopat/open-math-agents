import OMAStatements.S_gillibert_geodesic_deletion

-- Problem: Geodesic deletion conjecture (vertex-transitive graphs)
-- Upstream: formal-conjectures statements/gillibert-geodesic-deletion.lean:0 (declaration OMA.S_gillibert_geodesic_deletion.main)
-- Credit: @amcolex (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-!
# Complete Proof of Gillibert's Geodesic Deletion Conjecture

Let `G` be a finite connected vertex-transitive graph with `3 ≤ |V(G)|`.
We prove that for every geodesic `P = (v_0, ..., v_L)` of `G`, the induced subgraph `G - V(P)`
is connected.

## Proof Structure
1. **Grand Antipode Block Theorem (`grand_antipode_block_theorem`)**:
   Assuming a minimal-length disconnecting geodesic `P = (v_0, ..., v_L)` with minimum-size
   component `A` of `G - P` and `B = V \ (A ∪ P)`, we show `3 ≤ L`, `d(v_m, x) < L` for all
   `x ∈ A ∪ P` (where `m = L / 2`), and via the discrete intermediate value theorem on
   `ψ(x) = d(x, v_0) - d(x, v_L)` over `G[A]` and excess domination, there exists `a ∈ A`
   sharing all spheres `S(a, r) = S(v_m, r)` for every `r ≥ L`.
   By vertex-transitivity, the `~_{≥ L}`-equivalence class `C_u` of `u = v_0` is nontrivial.
2. **Master Separation Lemma & Distance-Sum Contradiction (`contradiction_of_trapped_side`)**:
   - Since `v_1 ∉ C_u` (as `d(u, v) = L ≠ L - 1 = d(v_1, v)`), vertex-transitivity produces
     `w* ∈ W_r(v_1) \ W_r(u)` for some `r ≥ L`, lying in one side `O ∈ {A, B}` (`T` = other side).
   - For any `c ∈ C_u` on one side and `z` on the other side, any shortest path crosses `P` at
     some `v_k`, giving `d(c, z) ≥ min(d(c, u) + d(u, z), 1 + d(v_1, z))`.
   - This forces `C_u \ {u} ⊆ O`, which in turn forces every neighbor `t_0 ∈ N_T(u)` to satisfy
     `t_0 ∈ C_{v_1} \ {v_1}`.
   - Picking `φ ∈ Aut(G)` with `φ(v_1) = u` and setting `c := φ(t_0) ∈ C_u \ {u} ⊆ O`, every
     `z ∈ Z_<(t_0, v_1)` lies in `Z_<(u, c) \ {u}` with `d(v_1, z) - d(t_0, z) ≤ d(c, z) - d(u, z)`.
   - Summing over `Z_<(u, c) ⊇ {u} ⊔ Z_<(t_0, v_1)` and using the vertex-transitivity distance-sum
     identity `Φ(u, c) = Φ(c, u) = Φ(t_0, v_1)` yields `Φ(t_0, v_1) ≥ d(c, u) + Φ(t_0, v_1) ≥ 1 + Φ(t_0, v_1)`,
     contradiction!
-/

namespace GillibertGeodesicDeletionProof

open SimpleGraph
open scoped Classical

abbrev IsVertexTransitive {V : Type*} (G : SimpleGraph V) : Prop :=
  OMA.S_gillibert_geodesic_deletion.IsVertexTransitive G

section Helpers

variable {V : Type*}

/-! ### Part 1: Basic Induced Connectivity, Geodesics, and Non-Cut-Vertices -/

private lemma induce_connected_of_base {G : SimpleGraph V} {S : Set V} {r : V} (hr : r ∈ S)
    (hreach : ∀ x (hx : x ∈ S), (G.induce S).Reachable ⟨x, hx⟩ ⟨r, hr⟩) :
    (G.induce S).Connected := by
  have : Nonempty S := ⟨⟨r, hr⟩⟩
  exact ⟨fun ⟨x, hx⟩ ⟨y, hy⟩ => (hreach x hx).trans (hreach y hy).symm⟩

private lemma induce_connected_of_iso {G : SimpleGraph V} (φ : G ≃g G) {S T : Set V}
    (hST : ∀ x, x ∈ S ↔ φ x ∈ T) (hS : (G.induce S).Connected) :
    (G.induce T).Connected := by
  have e : G.induce S ≃g G.induce T :=
    { toFun := fun x => ⟨φ x.1, (hST x.1).1 x.2⟩
      invFun := fun y => ⟨φ.symm y.1, (hST (φ.symm y.1)).2 (by simp [y.2])⟩
      left_inv := fun x => Subtype.ext (φ.symm_apply_apply x.1)
      right_inv := fun y => Subtype.ext (φ.apply_symm_apply y.1)
      map_rel_iff' := by
        intro a b
        exact φ.map_rel_iff }
  have : Nonempty T := ⟨e hS.nonempty.some⟩
  refine ⟨fun x y => ?_⟩
  obtain ⟨w⟩ := hS.preconnected (e.symm x) (e.symm y)
  exact ⟨(w.map e.toHom).copy (e.apply_symm_apply x) (e.apply_symm_apply y)⟩

private lemma walk_induce_iff_exists_walk {G : SimpleGraph V} {S : Set V}
    {x y : V} (hx : x ∈ S) (hy : y ∈ S) :
    (G.induce S).Reachable ⟨x, hx⟩ ⟨y, hy⟩ ↔
      ∃ w : G.Walk x y, ∀ z ∈ w.support, z ∈ S := by
  constructor
  · rintro ⟨w⟩
    have hmem : ∀ {a b : S} (q : (G.induce S).Walk a b) (z : V),
        z ∈ (q.map (Embedding.induce S).toHom).support → z ∈ S := by
      intro a b q
      induction q with
      | @nil u =>
        intro z hz
        simp only [Walk.map_nil, Walk.support_nil, List.mem_singleton] at hz
        exact hz ▸ u.2
      | @cons a b c hab q' ih =>
        intro z hz
        simp only [Walk.map_cons, Walk.support_cons, List.mem_cons] at hz
        rcases hz with rfl | hz
        · exact a.2
        · exact ih z hz
    exact ⟨w.map (Embedding.induce S).toHom, fun z hz => hmem w z hz⟩
  · rintro ⟨w, hw⟩
    exact ⟨w.induce S hw⟩

private lemma walk_stay_in_part {G : SimpleGraph V} {A B : Finset V}
    (hnoAB : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b)
    {x y : V} (w : G.Walk x y) (hx : x ∈ A)
    (hpart : ∀ z ∈ w.support, z ∈ A ∨ z ∈ B) :
    ∀ z ∈ w.support, z ∈ A := by
  induction w with
  | nil =>
    intro z hz
    simp only [Walk.support_nil, List.mem_singleton] at hz
    exact hz ▸ hx
  | @cons a b c hab q ih =>
    intro z hz
    have hbA : b ∈ A := by
      rcases hpart b (by simp) with h | h
      · exact h
      · exact absurd hab (hnoAB a hx b h)
    rw [Walk.support_cons, List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact hx
    · exact ih hbA (fun t ht => hpart t (by simp [ht])) z hz

private lemma walk_enter_target_adj {G : SimpleGraph V} {A B : Finset V} {u : V}
    (hnoAB : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b) (huA : u ∉ A)
    {x : V} (q : G.Walk x u) (hx : x ∈ A)
    (hpart : ∀ t ∈ q.support, t ≠ u → t ∈ A ∨ t ∈ B) :
    ∃ a ∈ A, G.Adj u a := by
  induction q with
  | nil => exact absurd hx huA
  | @cons x₁ x₂ u' h12 q' ih =>
    by_cases h2u : x₂ = u'
    · exact ⟨x₁, hx, h2u ▸ h12.symm⟩
    · rcases hpart x₂ (by simp) h2u with h | h
      · exact ih huA h (fun t ht => hpart t (by simp [ht]))
      · exact absurd h12 (hnoAB x₁ hx x₂ h)

private lemma dist_triangle_of_reachable {G : SimpleGraph V} {x y z : V}
    (hxy : G.Reachable x y) (hyz : G.Reachable y z) :
    G.dist x z ≤ G.dist x y + G.dist y z := by
  obtain ⟨w1, hw1⟩ := hxy.exists_walk_length_eq_dist
  obtain ⟨w2, hw2⟩ := hyz.exists_walk_length_eq_dist
  have h := G.dist_le (w1.append w2)
  rw [Walk.length_append, hw1, hw2] at h
  exact h

private lemma iso_dist_eq {G : SimpleGraph V} (φ : G ≃g G) (hconn : G.Connected) (x y : V) :
    G.dist (φ x) (φ y) = G.dist x y := by
  apply le_antisymm
  · obtain ⟨w, hw⟩ := (hconn x y).exists_walk_length_eq_dist
    have h := G.dist_le (w.map φ.toHom)
    simpa [hw] using h
  · obtain ⟨w, hw⟩ := (hconn (φ x) (φ y)).exists_walk_length_eq_dist
    have h := G.dist_le ((w.map φ.symm.toHom).copy (φ.symm_apply_apply x) (φ.symm_apply_apply y))
    simpa [hw] using h

private lemma not_connected_induce_split [Fintype V] {G : SimpleGraph V} {S : Set V}
    (hSne : S.Nonempty) (hnot : ¬ (G.induce S).Connected) :
    ∃ A B : Finset V, A.Nonempty ∧ B.Nonempty ∧
      (G.induce (A : Set V)).Connected ∧
      (∀ x, x ∈ S ↔ x ∈ A ∨ x ∈ B) ∧
      Disjoint A B ∧
      (∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b) := by
  obtain ⟨a₀, ha₀⟩ := hSne
  let A : Finset V := Finset.univ.filter (fun x => ∃ hx : x ∈ S, (G.induce S).Reachable ⟨a₀, ha₀⟩ ⟨x, hx⟩)
  let B : Finset V := Finset.univ.filter (fun x => x ∈ S ∧ x ∉ A)
  have ha₀A : a₀ ∈ A := by
    simp [A, ha₀]
  have hAS : ∀ x ∈ A, x ∈ S := by
    intro x hx
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    exact hx.1
  have hBne : B.Nonempty := by
    by_contra hBe
    rw [Finset.not_nonempty_iff_eq_empty] at hBe
    apply hnot
    refine induce_connected_of_base ha₀ (fun x hx => ?_)
    have hxA : x ∈ A := by
      by_contra hxnA
      have : x ∈ B := by simp [B, hx, hxnA]
      rw [hBe] at this
      exact Finset.notMem_empty x this
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hxA
    exact hxA.2.symm
  have hAconn : (G.induce (A : Set V)).Connected := by
    refine induce_connected_of_base (show a₀ ∈ (A : Set V) from ha₀A) ?_
    intro x hx
    have hx' : x ∈ A := hx
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hx'
    obtain ⟨hxS, hr⟩ := hx'
    obtain ⟨w, hwS⟩ := (walk_induce_iff_exists_walk ha₀ hxS).1 hr
    have hwA : ∀ z ∈ w.support, z ∈ (A : Set V) := by
      intro z hz
      have hzS : z ∈ S := hwS z hz
      have hreach_z : (G.induce S).Reachable ⟨a₀, ha₀⟩ ⟨z, hzS⟩ := by
        rw [walk_induce_iff_exists_walk]
        refine ⟨w.takeUntil z hz, fun t ht => hwS t (Walk.support_takeUntil_subset_support w hz ht)⟩
      change z ∈ A
      simp [A, hzS, hreach_z]
    exact (walk_induce_iff_exists_walk hx (show a₀ ∈ (A : Set V) from ha₀A)).2
      ⟨w.reverse, fun z hz => hwA z (by simpa using hz)⟩
  have hpart : ∀ x, x ∈ S ↔ x ∈ A ∨ x ∈ B := by
    intro x
    constructor
    · intro hxS
      by_cases hxA : x ∈ A
      · exact Or.inl hxA
      · exact Or.inr (by simp [B, hxS, hxA])
    · rintro (hxA | hxB)
      · exact hAS x hxA
      · simp only [B, Finset.mem_filter, Finset.mem_univ, true_and] at hxB
        exact hxB.1
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro x hxA hxB
    simp only [B, Finset.mem_filter, Finset.mem_univ, true_and] at hxB
    exact hxB.2 hxA
  have hno : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b := by
    intro a haA b hbB hab
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at haA
    simp only [B, Finset.mem_filter, Finset.mem_univ, true_and] at hbB
    have hrb : (G.induce S).Reachable ⟨a₀, ha₀⟩ ⟨b, hbB.1⟩ :=
      haA.2.trans (Adj.reachable (show (G.induce S).Adj ⟨a, haA.1⟩ ⟨b, hbB.1⟩ from hab))
    exact hbB.2 (by simp [A, hbB.1, hrb])
  exact ⟨A, B, ⟨a₀, ha₀A⟩, hBne, hAconn, hpart, hdisj, hno⟩

private lemma exists_walk_last_before {G : SimpleGraph V} {S : Set V} {y t : V}
    (hy : y ∉ S) (ht : t ∈ S) (w : G.Walk y t) :
    ∃ (z : V) (hz : z ∉ S) (s : V), s ∈ S ∧ G.Adj z s ∧
      (G.induce {x | x ∉ S}).Reachable ⟨y, hy⟩ ⟨z, hz⟩ := by
  induction w with
  | nil => exact absurd ht hy
  | @cons a b c hab q ih =>
    by_cases hb : b ∈ S
    · exact ⟨a, hy, b, hb, hab, Reachable.refl _⟩
    · obtain ⟨z, hz, s, hs, hzs, hreach⟩ := ih hb ht
      exact ⟨z, hz, s, hs, hzs, (Adj.reachable (show (G.induce {x | x ∉ S}).Adj ⟨a, hy⟩ ⟨b, hb⟩ from hab)).trans hreach⟩

private lemma geodesic_dist_getVert {G : SimpleGraph V} {u v : V} (p : G.Walk u v)
    (hgeo : p.length = G.dist u v) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ p.length) :
    G.dist (p.getVert i) (p.getVert j) = j - i := by
  have hwalk_len : ∀ {a b : V} (q : G.Walk a b) (k : ℕ), k ≤ q.length →
      ∃ w : G.Walk a (q.getVert k), w.length = k := by
    intro a b q k hk
    induction q generalizing k with
    | nil =>
      have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
      subst hk0; exact ⟨Walk.nil, rfl⟩
    | @cons x y z hxy r ih =>
      cases k with
      | zero => exact ⟨Walk.nil, rfl⟩
      | succ k =>
        obtain ⟨w, hw⟩ := ih k (Nat.le_of_succ_le_succ hk)
        exact ⟨Walk.cons hxy w, by simp [hw]⟩
  have hseg : ∀ {a b : V} (q : G.Walk a b) (r s : ℕ), r ≤ s → s ≤ q.length →
      ∃ w : G.Walk (q.getVert r) (q.getVert s), w.length = s - r := by
    intro a b q r s hrs hs
    induction q generalizing r s with
    | nil =>
      have hs0 : s = 0 := Nat.eq_zero_of_le_zero hs
      have hr0 : r = 0 := Nat.eq_zero_of_le_zero (hrs.trans hs)
      subst hs0; subst hr0; exact ⟨Walk.nil, rfl⟩
    | @cons x y z hxy q' ih =>
      cases r with
      | zero =>
        exact hwalk_len (Walk.cons hxy q') s hs
      | succ r =>
        cases s with
        | zero => omega
        | succ s =>
          simpa [Nat.succ_sub_succ_eq_sub] using
            ih r s (Nat.le_of_succ_le_succ hrs) (Nat.le_of_succ_le_succ hs)
  obtain ⟨w1, hw1⟩ := hseg p 0 i (Nat.zero_le _) (hij.trans hj)
  obtain ⟨w2, hw2⟩ := hseg p i j hij hj
  obtain ⟨w3, hw3⟩ := hseg p j p.length hj le_rfl
  let w1' : G.Walk u (p.getVert i) := w1.copy (by simp) rfl
  let w3' : G.Walk (p.getVert j) v := w3.copy rfl (by simp)
  have h1 : G.dist u (p.getVert i) ≤ i := (G.dist_le w1').trans_eq (by simpa [w1'] using hw1)
  have h2 : G.dist (p.getVert i) (p.getVert j) ≤ j - i := (G.dist_le w2).trans_eq hw2
  have h3 : G.dist (p.getVert j) v ≤ p.length - j := (G.dist_le w3').trans_eq (by simpa [w3'] using hw3)
  have htri1 := dist_triangle_of_reachable ⟨w1'⟩ ⟨w2⟩
  have htri2 := dist_triangle_of_reachable ⟨w1'.append w2⟩ ⟨w3'⟩
  omega

private lemma geodesic_adj_getVert {G : SimpleGraph V} {u v : V} (p : G.Walk u v)
    (hgeo : p.length = G.dist u v) {i j : ℕ} (hi : i ≤ p.length) (hj : j ≤ p.length)
    (hadj : G.Adj (p.getVert i) (p.getVert j)) :
    i + 1 = j ∨ j + 1 = i := by
  have hd : G.dist (p.getVert i) (p.getVert j) = 1 :=
    SimpleGraph.dist_eq_one_iff_adj.2 hadj
  rcases le_total i j with hij | hji
  · have := geodesic_dist_getVert p hgeo hij hj
    omega
  · have := geodesic_dist_getVert p hgeo hji hi
    rw [SimpleGraph.dist_comm] at hd
    omega

private lemma mem_support_iff_getVert {G : SimpleGraph V} {u v : V} (p : G.Walk u v) (x : V) :
    x ∈ p.support ↔ ∃ i ≤ p.length, p.getVert i = x := by
  constructor
  · intro hx
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hx
    have hi' : i ≤ p.length := by
      have := p.length_support
      omega
    exact ⟨i, hi', (p.getVert_eq_support_getElem hi').trans rfl⟩
  · rintro ⟨i, _, rfl⟩
    exact p.getVert_mem_support i

private lemma exists_not_mem_geodesic [Fintype V] {G : SimpleGraph V}
    (hvt : IsVertexTransitive G)
    (hcard : 3 ≤ Fintype.card V) {u v : V} (p : G.Walk u v) (hp : p.IsPath)
    (hgeo : p.length = G.dist u v) :
    ∃ x : V, x ∉ p.support := by
  by_contra hall
  push Not at hall
  have hlen : p.length + 1 = Fintype.card V := by
    have hsub : Finset.univ ⊆ p.support.toFinset := fun x _ => List.mem_toFinset.2 (hall x)
    have hcard_eq : p.support.toFinset.card = Fintype.card V :=
      le_antisymm (Finset.card_le_univ _) (by simpa using Finset.card_le_card hsub)
    rw [List.toFinset_card_of_nodup hp.support_nodup, Walk.length_support] at hcard_eq
    exact hcard_eq
  have hp2 : 2 ≤ p.length := by omega
  have hdeg0 : G.degree (p.getVert 0) = 1 := by
    rw [SimpleGraph.degree_eq_one_iff_existsUnique_adj]
    refine ⟨p.getVert 1, p.adj_getVert_succ (by omega), ?_⟩
    intro w hw
    obtain ⟨j, hj, rfl⟩ := (mem_support_iff_getVert p w).1 (hall w)
    rcases geodesic_adj_getVert p hgeo (Nat.zero_le _) hj hw with h | h
    · simp [← h]
    · omega
  have hdeg1 : 2 ≤ G.degree (p.getVert 1) := by
    have h01 : G.Adj (p.getVert 1) (p.getVert 0) := (p.adj_getVert_succ (by omega)).symm
    have h12 : G.Adj (p.getVert 1) (p.getVert 2) := p.adj_getVert_succ (by omega)
    have hne : p.getVert 0 ≠ p.getVert 2 := by
      intro heq
      have h02 := geodesic_dist_getVert p hgeo (show 0 ≤ 2 by omega) hp2
      rw [heq, SimpleGraph.dist_self] at h02
      omega
    have hsub : ({p.getVert 0, p.getVert 2} : Finset V) ⊆ G.neighborFinset (p.getVert 1) := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rw [SimpleGraph.mem_neighborFinset]
      rcases hz with rfl | rfl <;> assumption
    have hc := Finset.card_le_card hsub
    rw [Finset.card_pair hne, SimpleGraph.card_neighborFinset_eq_degree] at hc
    exact hc
  obtain ⟨φ, hφ⟩ := hvt (p.getVert 0) (p.getVert 1)
  have hdeq : G.degree (p.getVert 0) = G.degree (p.getVert 1) := by
    rw [← hφ, φ.degree_eq]
  omega

private lemma exists_non_cut_vertex [Fintype V] (G : SimpleGraph V)
    (hconn : G.Connected) (hcard : 2 ≤ Fintype.card V) :
    ∃ m : V, (G.induce {x | x ≠ m}).Connected := by
  have : Nonempty V := Fintype.card_pos_iff.1 (by omega)
  let r : V := Classical.arbitrary V
  obtain ⟨m, _, hm_max⟩ := Finset.exists_max_image Finset.univ (fun x => G.dist r x) Finset.univ_nonempty
  have hmr : m ≠ r := by
    intro h
    rw [h] at hm_max
    have hall0 : ∀ x : V, G.dist r x = 0 := fun x =>
      Nat.eq_zero_of_le_zero (by simpa using hm_max x (Finset.mem_univ x))
    have hall : ∀ x : V, x = r := fun x =>
      (SimpleGraph.dist_eq_zero_iff_eq_or_not_reachable.1 (hall0 x)).resolve_right
        (not_not.2 (hconn r x)) |>.symm
    have hsub : Fintype.card V ≤ 1 := by
      have : (Finset.univ : Finset V) ⊆ {r} := fun x _ => Finset.mem_singleton.2 (hall x)
      simpa using Finset.card_le_card this
    omega
  refine ⟨m, induce_connected_of_base (show r ∈ {x | x ≠ m} from hmr.symm) ?_⟩
  intro x hx
  obtain ⟨w, hw⟩ := (hconn r x).exists_walk_length_eq_dist
  have hm_not : m ∉ w.support := by
    intro hm
    have hlen_split : (w.takeUntil m hm).length + (w.dropUntil m hm).length = w.length := by
      rw [← Walk.length_append, Walk.take_spec]
    have h1 : G.dist r m ≤ (w.takeUntil m hm).length := G.dist_le _
    have h2 : 1 ≤ (w.dropUntil m hm).length := by
      have hne : m ≠ x := hx.symm
      cases hd : w.dropUntil m hm with
      | nil => exact absurd rfl hne
      | cons _ _ => simp
    have hmax := hm_max x (Finset.mem_univ x)
    omega
  exact (walk_induce_iff_exists_walk hx hmr.symm).2
    ⟨w.reverse, fun z hz => fun hzm => hm_not (hzm ▸ (by simpa using hz))⟩

private lemma length_zero_connected [Fintype V] {G : SimpleGraph V}
    (hconn : G.Connected) (hvt : IsVertexTransitive G)
    (hcard : 2 ≤ Fintype.card V) (v : V) :
    (G.induce {x | x ≠ v}).Connected := by
  obtain ⟨m, hm⟩ := exists_non_cut_vertex G hconn hcard
  obtain ⟨φ, hφ⟩ := hvt m v
  refine induce_connected_of_iso φ (fun x => ?_) hm
  constructor <;> intro h h'
  · exact h (φ.injective (h'.trans hφ.symm))
  · exact h (by rw [h', hφ])

/-! ### Part 2: The Automorphism-Step Theorem (General Finite Connected Graphs) -/

private lemma automorphism_step_connected [Fintype V] {G : SimpleGraph V}
    (hconn : G.Connected) {u v : V} (p : G.Walk u v) (φ : G ≃g G)
    (hadj : ∀ x, G.Adj x (φ x)) (hdisj : ∀ x ∈ p.support, φ x ∉ p.support) :
    (G.induce {x | x ∉ p.support}).Connected := by
  let S : Set V := {x | x ∈ p.support}
  have huS : u ∈ S := p.start_mem_support
  have hsymm_not : ∀ x ∈ S, φ.symm x ∉ S := by
    intro x hx hmem
    have := hdisj (φ.symm x) hmem
    rw [φ.apply_symm_apply] at this
    exact this hx
  let r₀ : V := φ.symm u
  have hr₀ : r₀ ∉ S := hsymm_not u huS
  have hS_reach : ∀ x (hx : x ∈ S), (G.induce {z | z ∉ S}).Reachable ⟨φ.symm x, hsymm_not x hx⟩ ⟨r₀, hr₀⟩ := by
    intro x hx
    have htake : (G.induce S).Reachable ⟨x, hx⟩ ⟨u, huS⟩ := by
      rw [walk_induce_iff_exists_walk]
      exact ⟨(p.takeUntil x hx).reverse, fun z hz => Walk.support_takeUntil_subset_support p hx (by simpa using hz)⟩
    obtain ⟨w, hwS⟩ := (walk_induce_iff_exists_walk hx huS).1 htake
    rw [walk_induce_iff_exists_walk]
    refine ⟨w.map φ.symm.toHom, ?_⟩
    intro z hz
    rw [Walk.support_map] at hz
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hz
    exact hsymm_not t (hwS t ht)
  let ePerm : Equiv.Perm V := φ.toEquiv
  have hfin : IsOfFinOrder ePerm := isOfFinOrder_of_finite ePerm
  have hord_pos : 0 < orderOf ePerm := orderOf_pos_iff.2 hfin
  have hord_ge2 : 2 ≤ orderOf ePerm := by
    by_contra hlt
    have h1 : orderOf ePerm = 1 := by omega
    have he1 : ePerm = 1 := orderOf_eq_one_iff.1 h1
    have hfix : φ u = u := by
      have : ePerm u = u := by simp [he1]
      exact this
    have huu : G.Adj u u := by
      have h := hadj u
      rwa [hfix] at h
    exact G.loopless.irrefl u huu
  have hiter_reach : ∀ k (x : V) (hx : x ∉ S), (ePerm ^ k) x ∈ S →
      (G.induce {z | z ∉ S}).Reachable ⟨x, hx⟩ ⟨r₀, hr₀⟩ := by
    intro k
    induction k with
    | zero =>
      intro x hx hmem
      exact absurd hmem hx
    | succ k ih =>
      intro x hx hmem
      by_cases h1 : φ x ∈ S
      · have hxeq : x = φ.symm (φ x) := (φ.symm_apply_apply x).symm
        have hstep := hS_reach (φ x) h1
        have hsub : (⟨x, hx⟩ : {z | z ∉ S}) = ⟨φ.symm (φ x), hsymm_not (φ x) h1⟩ := Subtype.ext hxeq
        rw [hsub]
        exact hstep
      · have hmem' : (ePerm ^ k) (φ x) ∈ S := by
          have : (ePerm ^ (k + 1)) x = (ePerm ^ k) (ePerm x) := by
            rw [pow_succ, Equiv.Perm.mul_apply]
          simpa [ePerm, this] using hmem
        have hstep : (G.induce {z | z ∉ S}).Adj ⟨x, hx⟩ ⟨φ x, h1⟩ := hadj x
        exact (Adj.reachable hstep).trans (ih (φ x) h1 hmem')
  have hphiS_reach : ∀ s (hs : s ∈ S),
      (G.induce {z | z ∉ S}).Reachable ⟨φ s, hdisj s hs⟩ ⟨r₀, hr₀⟩ := by
    intro s hs
    refine hiter_reach (orderOf ePerm - 1) (φ s) (hdisj s hs) ?_
    have hpow : (ePerm ^ (orderOf ePerm - 1)) (ePerm s) = (ePerm ^ orderOf ePerm) s := by
      have hmul : ePerm ^ (orderOf ePerm - 1) * ePerm = ePerm ^ orderOf ePerm := by
        conv_rhs => rw [← Nat.sub_add_cancel (show 1 ≤ orderOf ePerm by omega)]
        rw [pow_succ]
      rw [← Equiv.Perm.mul_apply, hmul]
    rw [show φ s = ePerm s from rfl, hpow, pow_orderOf_eq_one]
    exact hs
  refine induce_connected_of_base hr₀ ?_
  intro y hy
  have hyS : y ∉ S := hy
  obtain ⟨w⟩ := hconn y u
  obtain ⟨z, hz, s, hs, hzs, hyz⟩ := exists_walk_last_before (S := S) hyS huS w
  by_cases hφz : φ z ∈ S
  · exact hyz.trans (hiter_reach 1 z hz (by simpa [ePerm] using hφz))
  · have hz1 : (G.induce {x | x ∉ S}).Adj ⟨z, hz⟩ ⟨φ z, hφz⟩ := hadj z
    have hz2 : (G.induce {x | x ∉ S}).Adj ⟨φ z, hφz⟩ ⟨φ s, hdisj s hs⟩ :=
      φ.map_rel_iff.2 hzs
    exact hyz.trans ((Adj.reachable hz1).trans ((Adj.reachable hz2).trans (hphiS_reach s hs)))

/-! ### Part 3: Watkins Connectivity Bound (kappa(G) >= min(deg, 4)) & Geodesics of Length <= 2 -/

private lemma card_boundary_union_inter_le [Fintype V] {G : SimpleGraph V}
    {A B S A' B' S' : Finset V}
    (hpart : ∀ x, x ∈ A ∨ x ∈ B ∨ x ∈ S)
    (hdAB : Disjoint A B) (hdAS : Disjoint A S) (hdBS : Disjoint B S)
    (hpart' : ∀ x, x ∈ A' ∨ x ∈ B' ∨ x ∈ S')
    (hdAB' : Disjoint A' B') (hdAS' : Disjoint A' S') (hdBS' : Disjoint B' S')
    (hnoAB : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b)
    (hnoAB' : ∀ a ∈ A', ∀ b ∈ B', ¬ G.Adj a b) :
    let N1 := Finset.univ.filter (fun x => x ∉ A ∩ A' ∧ ∃ a ∈ A ∩ A', G.Adj a x)
    let N2 := Finset.univ.filter (fun x => x ∉ B ∩ B' ∧ ∃ b ∈ B ∩ B', G.Adj b x)
    N1.card + N2.card ≤ S.card + S'.card ∧
    (∀ x ∈ N1, x ∈ (S ∩ A') ∪ (S ∩ S') ∪ (S' ∩ A)) ∧
    (∀ x ∈ N2, x ∈ (S ∩ B') ∪ (S ∩ S') ∪ (S' ∩ B)) := by
  intro N1 N2
  have h1 : N1 ⊆ (S ∩ A') ∪ (S ∩ S') ∪ (S' ∩ A) := by
    intro x hx
    simp only [N1, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    obtain ⟨hxn, a, ha, hax⟩ := hx
    rw [Finset.mem_inter] at ha
    have hx_notB : x ∉ B := fun hxB => hnoAB a ha.1 x hxB hax
    have hx_notB' : x ∉ B' := fun hxB' => hnoAB' a ha.2 x hxB' hax
    rcases hpart x with hxA | hxB | hxS
    · rcases hpart' x with hxA' | hxB' | hxS'
      · exact absurd (Finset.mem_inter.2 ⟨hxA, hxA'⟩) hxn
      · exact absurd hxB' hx_notB'
      · exact Finset.mem_union_right _ (Finset.mem_inter.2 ⟨hxS', hxA⟩)
    · exact absurd hxB hx_notB
    · rcases hpart' x with hxA' | hxB' | hxS'
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_inter.2 ⟨hxS, hxA'⟩))
      · exact absurd hxB' hx_notB'
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_inter.2 ⟨hxS, hxS'⟩))
  have h2 : N2 ⊆ (S ∩ B') ∪ (S ∩ S') ∪ (S' ∩ B) := by
    intro x hx
    simp only [N2, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    obtain ⟨hxn, b, hb, hbx⟩ := hx
    rw [Finset.mem_inter] at hb
    have hx_notA : x ∉ A := fun hxA => hnoAB x hxA b hb.1 hbx.symm
    have hx_notA' : x ∉ A' := fun hxA' => hnoAB' x hxA' b hb.2 hbx.symm
    rcases hpart x with hxA | hxB | hxS
    · exact absurd hxA hx_notA
    · rcases hpart' x with hxA' | hxB' | hxS'
      · exact absurd hxA' hx_notA'
      · exact absurd (Finset.mem_inter.2 ⟨hxB, hxB'⟩) hxn
      · exact Finset.mem_union_right _ (Finset.mem_inter.2 ⟨hxS', hxB⟩)
    · rcases hpart' x with hxA' | hxB' | hxS'
      · exact absurd hxA' hx_notA'
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_inter.2 ⟨hxS, hxB'⟩))
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_inter.2 ⟨hxS, hxS'⟩))
  have hS_decomp : (S ∩ A').card + (S ∩ S').card + (S ∩ B').card = S.card := by
    have hu : (S ∩ A') ∪ (S ∩ S') ∪ (S ∩ B') = S := by
      ext x; simp only [Finset.mem_union, Finset.mem_inter]
      constructor
      · rintro ((⟨h, _⟩ | ⟨h, _⟩) | ⟨h, _⟩) <;> exact h
      · intro hx
        rcases hpart' x with h | h | h
        · exact Or.inl (Or.inl ⟨hx, h⟩)
        · exact Or.inr ⟨hx, h⟩
        · exact Or.inl (Or.inr ⟨hx, h⟩)
    have hd1 : Disjoint (S ∩ A') (S ∩ S') :=
      Disjoint.mono Finset.inter_subset_right Finset.inter_subset_right hdAS'
    have hd2 : Disjoint ((S ∩ A') ∪ (S ∩ S')) (S ∩ B') := by
      rw [Finset.disjoint_union_left]
      exact ⟨Disjoint.mono Finset.inter_subset_right Finset.inter_subset_right hdAB',
             Disjoint.mono Finset.inter_subset_right Finset.inter_subset_right hdBS'.symm⟩
    calc (S ∩ A').card + (S ∩ S').card + (S ∩ B').card
        = ((S ∩ A') ∪ (S ∩ S') ∪ (S ∩ B')).card := by
          rw [Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd1]
      _ = S.card := by rw [hu]
  have hS'_decomp : (S' ∩ A).card + (S ∩ S').card + (S' ∩ B).card = S'.card := by
    have hu : (S' ∩ A) ∪ (S ∩ S') ∪ (S' ∩ B) = S' := by
      ext x; simp only [Finset.mem_union, Finset.mem_inter]
      constructor
      · rintro ((⟨h, _⟩ | ⟨_, h⟩) | ⟨h, _⟩) <;> exact h
      · intro hx
        rcases hpart x with h | h | h
        · exact Or.inl (Or.inl ⟨hx, h⟩)
        · exact Or.inr ⟨hx, h⟩
        · exact Or.inl (Or.inr ⟨h, hx⟩)
    have hd1 : Disjoint (S' ∩ A) (S ∩ S') :=
      Disjoint.mono Finset.inter_subset_right Finset.inter_subset_left hdAS
    have hd2 : Disjoint ((S' ∩ A) ∪ (S ∩ S')) (S' ∩ B) := by
      rw [Finset.disjoint_union_left]
      exact ⟨Disjoint.mono Finset.inter_subset_right Finset.inter_subset_right hdAB,
             Disjoint.mono Finset.inter_subset_left Finset.inter_subset_right hdBS.symm⟩
    calc (S' ∩ A).card + (S ∩ S').card + (S' ∩ B).card
        = ((S' ∩ A) ∪ (S ∩ S') ∪ (S' ∩ B)).card := by
          rw [Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd1]
      _ = S'.card := by rw [hu]
  have hc1 : N1.card ≤ (S ∩ A').card + (S ∩ S').card + (S' ∩ A).card :=
    (Finset.card_le_card h1).trans ((Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _))
  have hc2 : N2.card ≤ (S ∩ B').card + (S ∩ S').card + (S' ∩ B).card :=
    (Finset.card_le_card h2).trans ((Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _))
  exact ⟨by omega, fun x hx => h1 hx, fun x hx => h2 hx⟩

private lemma sep_of_boundary [Fintype V] {G : SimpleGraph V} {X Y : Finset V}
    (hX : X.Nonempty) (hY : Y.Nonempty) (hXY : Disjoint X Y)
    (hno : ∀ x ∈ X, ∀ y ∈ Y, ¬ G.Adj x y) :
    let N := Finset.univ.filter (fun z => z ∉ X ∧ ∃ x ∈ X, G.Adj x z)
    ¬ (G.induce {z | z ∉ (N : Set V)}).Connected := by
  intro N hconn
  obtain ⟨x, hx⟩ := hX
  obtain ⟨y, hy⟩ := hY
  have hxN : x ∉ (N : Set V) := by simp [N, hx]
  have hyN : y ∉ (N : Set V) := by
    simp only [N, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and, not_and, not_exists]
    intro _ a ha hax
    exact hno a ha y hy hax
  obtain ⟨w, hwN⟩ := (walk_induce_iff_exists_walk hxN hyN).1 (hconn.preconnected ⟨x, hxN⟩ ⟨y, hyN⟩)
  let Z : Finset V := Finset.univ.filter (fun z => z ∉ X ∧ z ∉ N)
  have hnoXZ : ∀ a ∈ X, ∀ b ∈ Z, ¬ G.Adj a b := fun a ha b hb hab => by
    simp only [Z, Finset.mem_filter, Finset.mem_univ, true_and] at hb
    exact hb.2 (by simp only [N, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hb.1, a, ha, hab⟩)
  have hmem := walk_stay_in_part hnoXZ w hx (fun z hz => by
    by_cases hzX : z ∈ X
    · exact Or.inl hzX
    · exact Or.inr (by simp [Z, hzX, show z ∉ N from hwN z hz]))
  exact Finset.disjoint_left.1 hXY (hmem y w.end_mem_support) hy

private lemma watkins_deg_le_cut_of_le_three [Fintype V] {G : SimpleGraph V}
    (hconn : G.Connected) (hvt : IsVertexTransitive G)
    (hcard : 3 ≤ Fintype.card V) {S₀ : Finset V} (hS₀_le : S₀.card ≤ 3)
    (hS₀_sep : ¬ (G.induce {x | x ∉ (S₀ : Set V)}).Connected) :
    ∀ v : V, G.degree v ≤ S₀.card := by
  by_cases hfull : Fintype.card V ≤ S₀.card
  · intro v
    have hlt : G.degree v < Fintype.card V := by
      rw [← SimpleGraph.card_neighborFinset_eq_degree, ← Finset.card_univ]
      refine Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨Finset.subset_univ _, fun heq => ?_⟩)
      have hv : v ∈ G.neighborFinset v := heq ▸ Finset.mem_univ v
      rw [SimpleGraph.mem_neighborFinset] at hv
      exact G.loopless.irrefl v hv
    omega
  have hdisj_img : ∀ {X Y : Finset V} (ψ : G ≃g G), Disjoint X Y → Disjoint (X.image ψ) (Y.image ψ) := by
    intro X Y ψ hd
    rw [Finset.disjoint_left]
    intro z hzX hzY
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hzX
    obtain ⟨y, hy, hyx⟩ := Finset.mem_image.1 hzY
    have hxy : y = x := ψ.injective hyx
    exact Finset.disjoint_left.1 hd hx (hxy ▸ hy)
  have hex_k : ∃ k, ∃ S : Finset V, S.card = k ∧
      ¬ (G.induce {x | x ∉ (S : Set V)}).Connected := ⟨S₀.card, S₀, rfl, hS₀_sep⟩
  set k := Nat.find hex_k
  have hk_spec : ∃ S : Finset V, S.card = k ∧ ¬ (G.induce {x | x ∉ (S : Set V)}).Connected :=
    Nat.find_spec hex_k
  have hk_min : ∀ S : Finset V, ¬ (G.induce {x | x ∉ (S : Set V)}).Connected → k ≤ S.card :=
    fun S hS => Nat.find_min' hex_k ⟨S, rfl, hS⟩
  have hk_le_S₀ : k ≤ S₀.card := hk_min S₀ hS₀_sep
  have hk_le3 : k ≤ 3 := hk_le_S₀.trans hS₀_le
  have hk_ge2 : 2 ≤ k := by
    by_contra hlt
    obtain ⟨S, hSc, hSsep⟩ := hk_spec
    have h01 : k = 0 ∨ k = 1 := by omega
    rcases h01 with h0 | h1
    · rw [h0] at hSc
      have hSe : S = ∅ := Finset.card_eq_zero.1 hSc
      apply hSsep
      rw [hSe]
      have hU : {x : V | x ∉ ((∅ : Finset V) : Set V)} = Set.univ := by ext x; simp
      rw [hU]
      have : Nonempty V := Fintype.card_pos_iff.1 (by omega)
      refine induce_connected_of_base (r := Classical.arbitrary V) (Set.mem_univ _) (fun x _ => ?_)
      obtain ⟨w⟩ := hconn x (Classical.arbitrary V)
      exact (walk_induce_iff_exists_walk (S := Set.univ) (Set.mem_univ x) (Set.mem_univ _)).2 ⟨w, fun _ _ => Set.mem_univ _⟩
    · rw [h1] at hSc
      obtain ⟨v, rfl⟩ := Finset.card_eq_one.1 hSc
      have hEq : {x : V | x ∉ (({v} : Finset V) : Set V)} = {x | x ≠ v} := by ext x; simp
      rw [hEq] at hSsep
      exact hSsep (length_zero_connected hconn hvt (by omega) v)
  have hex_frag : ∃ m, ∃ S A B : Finset V, S.card = k ∧ A.card = m ∧
      A.Nonempty ∧ B.Nonempty ∧ (G.induce (A : Set V)).Connected ∧
      (∀ x, x ∈ A ∨ x ∈ B ∨ x ∈ S) ∧
      Disjoint A B ∧ Disjoint A S ∧ Disjoint B S ∧
      (∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b) := by
    obtain ⟨S, hSc, hSsep⟩ := hk_spec
    have hSne : ({x : V | x ∉ (S : Set V)}).Nonempty := by
      by_contra he
      rw [Set.not_nonempty_iff_eq_empty] at he
      have hall : ∀ x : V, x ∈ S := fun x => by
        by_contra hx; exact Set.notMem_empty x (he ▸ hx)
      have hcardS : Fintype.card V ≤ S.card := by
        simpa using Finset.card_le_card (show (Finset.univ : Finset V) ⊆ S from fun x _ => hall x)
      omega
    obtain ⟨A, B, hA, hB, hAc, hpart, hdAB, hno⟩ := not_connected_induce_split hSne hSsep
    have hdAS : Disjoint A S := Finset.disjoint_left.2 fun x hxA hxS =>
      ((hpart x).2 (Or.inl hxA)) hxS
    have hdBS : Disjoint B S := Finset.disjoint_left.2 fun x hxB hxS =>
      ((hpart x).2 (Or.inr hxB)) hxS
    have hall : ∀ x, x ∈ A ∨ x ∈ B ∨ x ∈ S := fun x => by
      by_cases hxS : x ∈ S
      · exact Or.inr (Or.inr hxS)
      · rcases (hpart x).1 hxS with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
    exact ⟨A.card, S, A, B, hSc, rfl, hA, hB, hAc, hall, hdAB, hdAS, hdBS, hno⟩
  set a := Nat.find hex_frag
  obtain ⟨S, A, B, hSc, hAc, hAne, hBne, hAconn, hpart, hdAB, hdAS, hdBS, hnoAB⟩ :=
    Nat.find_spec hex_frag
  change A.card = a at hAc
  have ha_pos : 1 ≤ a := hAc ▸ Finset.card_pos.2 hAne
  have hmin_any : ∀ X Y : Finset V, X.Nonempty → Y.Nonempty → Disjoint X Y →
      (∀ x ∈ X, ∀ y ∈ Y, ¬ G.Adj x y) → X.card < a →
      k + 1 ≤ (Finset.univ.filter (fun z => z ∉ X ∧ ∃ x ∈ X, G.Adj x z)).card := by
    intro X Y hX hY hXY hnoX hXlt
    set N := Finset.univ.filter (fun z => z ∉ X ∧ ∃ x ∈ X, G.Adj x z)
    have hsepN : ¬ (G.induce {z | z ∉ (N : Set V)}).Connected := sep_of_boundary hX hY hXY hnoX
    have hge : k ≤ N.card := hk_min N hsepN
    by_contra hlt
    have hNeq : N.card = k := by omega
    have hXN : Disjoint X N := Finset.disjoint_left.2 fun z hzX hzN => by
      simp [N, hzX] at hzN
    have hYN : Disjoint Y N := Finset.disjoint_left.2 fun z hzY hzN => by
      simp only [N, Finset.mem_filter, Finset.mem_univ, true_and] at hzN
      obtain ⟨_, x, hxX, hxz⟩ := hzN
      exact hnoX x hxX z hzY hxz
    obtain ⟨x₀, hx₀⟩ := hX
    have hx₀N : x₀ ∉ (N : Set V) := fun h => Finset.disjoint_left.1 hXN hx₀ h
    have hx₀N' : x₀ ∉ N := fun h => hx₀N h
    obtain ⟨y₀, hy₀⟩ := hY
    have hy₀N : y₀ ∉ (N : Set V) := fun h => Finset.disjoint_left.1 hYN hy₀ h
    let C := Finset.univ.filter (fun z => ∃ hz : z ∉ (N : Set V),
      (G.induce {t | t ∉ (N : Set V)}).Reachable ⟨x₀, hx₀N⟩ ⟨z, hz⟩)
    let D := Finset.univ.filter (fun z => z ∉ N ∧ z ∉ C)
    have hCX : C ⊆ X := by
      intro z hz
      simp only [C, Finset.mem_filter, Finset.mem_univ, true_and] at hz
      obtain ⟨hzN, hrz⟩ := hz
      obtain ⟨w, hwN⟩ := (walk_induce_iff_exists_walk hx₀N hzN).1 hrz
      let Z : Finset V := Finset.univ.filter (fun t => t ∉ X ∧ t ∉ N)
      have hnoXZ : ∀ p ∈ X, ∀ q ∈ Z, ¬ G.Adj p q := fun p hp q hq hpq => by
        simp only [Z, Finset.mem_filter, Finset.mem_univ, true_and] at hq
        exact hq.2 (by simp only [N, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hq.1, p, hp, hpq⟩)
      have hmem := walk_stay_in_part hnoXZ w hx₀ (fun t ht => by
        by_cases htX : t ∈ X
        · exact Or.inl htX
        · exact Or.inr (by simp [Z, htX, show t ∉ N from hwN t ht]))
      exact hmem z w.end_mem_support
    have hx₀C : x₀ ∈ C := by simp [C, hx₀N']
    have hCne : C.Nonempty := ⟨x₀, hx₀C⟩
    have hDne : D.Nonempty := ⟨y₀, by
      refine Finset.mem_filter.2 ⟨Finset.mem_univ _, hy₀N, fun hyC => ?_⟩
      exact Finset.disjoint_left.1 hXY (hCX hyC) hy₀⟩
    have hCconn : (G.induce (C : Set V)).Connected := by
      refine induce_connected_of_base (show x₀ ∈ (C : Set V) from hx₀C) ?_
      intro z hz
      have hz' : z ∈ C := hz
      simp only [C, Finset.mem_filter, Finset.mem_univ, true_and] at hz'
      obtain ⟨hzN, hrz⟩ := hz'
      obtain ⟨w, hwN⟩ := (walk_induce_iff_exists_walk hx₀N hzN).1 hrz
      refine (walk_induce_iff_exists_walk hz (show x₀ ∈ (C : Set V) from hx₀C)).2
        ⟨w.reverse, fun t ht => ?_⟩
      have ht' : t ∈ w.support := by simpa using ht
      have htN : t ∉ (N : Set V) := hwN t ht'
      have htN' : t ∉ N := fun h => htN h
      have hrt : (G.induce {s | s ∉ (N : Set V)}).Reachable ⟨x₀, hx₀N⟩ ⟨t, htN⟩ :=
        (walk_induce_iff_exists_walk hx₀N htN).2
          ⟨w.takeUntil t ht', fun s hs => hwN s (Walk.support_takeUntil_subset_support w ht' hs)⟩
      change t ∈ C; simp [C, htN', hrt]
    have hClt : C.card < a := (Finset.card_le_card hCX).trans_lt hXlt
    have hpartCD : ∀ z, z ∈ C ∨ z ∈ D ∨ z ∈ N := fun z => by
      by_cases hzN : z ∈ N
      · exact Or.inr (Or.inr hzN)
      · by_cases hzC : z ∈ C
        · exact Or.inl hzC
        · exact Or.inr (Or.inl (by simp [D, hzN, hzC]))
    have hdCD : Disjoint C D := Finset.disjoint_left.2 fun z hzC hzD => (Finset.mem_filter.1 hzD).2.2 hzC
    have hdCN : Disjoint C N := Finset.disjoint_left.2 fun z hzC hzN => (Finset.mem_filter.1 hzC).2.1 hzN
    have hdDN : Disjoint D N := Finset.disjoint_left.2 fun z hzD hzN => (Finset.mem_filter.1 hzD).2.1 hzN
    have hnoCD : ∀ c ∈ C, ∀ d ∈ D, ¬ G.Adj c d := fun c hc d hd hcd => by
      simp only [C, Finset.mem_filter, Finset.mem_univ, true_and] at hc
      simp only [D, Finset.mem_filter, Finset.mem_univ, true_and] at hd
      have hrd : (G.induce {s | s ∉ (N : Set V)}).Reachable ⟨x₀, hx₀N⟩ ⟨d, hd.1⟩ :=
        hc.2.trans (Adj.reachable (show (G.induce {s | s ∉ (N : Set V)}).Adj ⟨c, hc.1⟩ ⟨d, hd.1⟩ from hcd))
      exact hd.2 (by simp [C, hd.1, hrd])
    exact Nat.find_min hex_frag hClt ⟨N, C, D, hNeq, rfl, hCne, hDne, hCconn, hpartCD, hdCD, hdCN, hdDN, hnoCD⟩
  have hAleB : a ≤ B.card := by
    by_contra hlt
    have hNle : (Finset.univ.filter (fun z => z ∉ B ∧ ∃ b ∈ B, G.Adj b z)).card ≤ S.card := by
      refine Finset.card_le_card (fun z hz => ?_)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
      obtain ⟨hzB, b, hb, hbz⟩ := hz
      rcases hpart z with hzA | hzB' | hzS
      · exact absurd hbz.symm (hnoAB z hzA b hb)
      · exact absurd hzB' hzB
      · exact hzS
    have hge := hmin_any B A hBne hAne hdAB.symm (fun b hb x hx h => hnoAB x hx b hb h.symm) (by omega)
    omega
  -- If a = 1, every vertex has degree = k ≤ S₀.card!
  by_cases ha1 : a = 1
  · rw [ha1] at hAc
    obtain ⟨v₀, rfl⟩ := Finset.card_eq_one.1 hAc
    have hdeg_v₀ : G.degree v₀ ≤ k := by
      rw [← SimpleGraph.card_neighborFinset_eq_degree, ← hSc]
      refine Finset.card_le_card (fun x hx => ?_)
      rw [SimpleGraph.mem_neighborFinset] at hx
      rcases hpart x with hxA | hxB | hxS
      · rw [Finset.mem_singleton] at hxA
        exact absurd (hxA ▸ hx) (G.loopless.irrefl v₀)
      · exact absurd hx (hnoAB v₀ (Finset.mem_singleton_self _) x hxB)
      · exact hxS
    intro v
    obtain ⟨φ, hφ⟩ := hvt v₀ v
    rw [← hφ, φ.degree_eq]
    exact hdeg_v₀.trans hk_le_S₀
  -- Otherwise a ≥ 2: derive contradiction via Watkins atom partition!
  exfalso
  have ha2 : 2 ≤ a := by omega
  -- Step 1: Atom disjointness: for every φ, either φ(A) = A or Disjoint A (φ(A))
  have hatom_disj : ∀ φ : G ≃g G, A.image φ = A ∨ Disjoint A (A.image φ) := by
    intro φ
    let A' := A.image φ
    let B' := B.image φ
    let S' := S.image φ
    by_cases hne : (A ∩ A').Nonempty
    · left
      by_contra hneq
      have hAA'_lt : (A ∩ A').card < a := by
        rw [← hAc]
        refine Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨Finset.inter_subset_left, ?_⟩)
        intro heq
        have hsub : A ⊆ A' := heq ▸ Finset.inter_subset_right
        have hcard_eq : A.card = A'.card := (Finset.card_image_of_injective A φ.injective).symm
        exact hneq (Finset.eq_of_subset_of_card_le hsub hcard_eq.ge).symm
      have hpart' : ∀ x, x ∈ A' ∨ x ∈ B' ∨ x ∈ S' := fun x => by
        rcases hpart (φ.symm x) with h | h | h
        · exact Or.inl (Finset.mem_image.2 ⟨φ.symm x, h, φ.apply_symm_apply x⟩)
        · exact Or.inr (Or.inl (Finset.mem_image.2 ⟨φ.symm x, h, φ.apply_symm_apply x⟩))
        · exact Or.inr (Or.inr (Finset.mem_image.2 ⟨φ.symm x, h, φ.apply_symm_apply x⟩))
      have hdAB' : Disjoint A' B' := hdisj_img φ hdAB
      have hdAS' : Disjoint A' S' := hdisj_img φ hdAS
      have hdBS' : Disjoint B' S' := hdisj_img φ hdBS
      have hnoAB' : ∀ x ∈ A', ∀ y ∈ B', ¬ G.Adj x y := by
        intro x hx y hy hxy
        obtain ⟨x₀, hx₀, rfl⟩ := Finset.mem_image.1 hx
        obtain ⟨y₀, hy₀, rfl⟩ := Finset.mem_image.1 hy
        exact hnoAB x₀ hx₀ y₀ hy₀ (φ.map_rel_iff.1 hxy)
      have hS'c : S'.card = k := (Finset.card_image_of_injective S φ.injective).trans hSc
      have hA'c : A'.card = a := (Finset.card_image_of_injective A φ.injective).trans hAc
      have hB'c : B'.card = B.card := Finset.card_image_of_injective B φ.injective
      have hAA'_ge := hmin_any (A ∩ A') B hne hBne
        (Disjoint.mono_left Finset.inter_subset_left hdAB)
        (fun x hx y hy => hnoAB x (Finset.mem_inter.1 hx).1 y hy) hAA'_lt
      have hsub1 := card_boundary_union_inter_le hpart hdAB hdAS hdBS hpart' hdAB' hdAS' hdBS' hnoAB hnoAB'
      have hN1_le : (Finset.univ.filter (fun x => x ∉ A ∩ A' ∧ ∃ a ∈ A ∩ A', G.Adj a x)).card ≤
          (S ∩ A').card + (S ∩ S').card + (S' ∩ A).card := by
        refine (Finset.card_le_card hsub1.2.1).trans ?_
        exact (Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _)
      have hBB'_empty : ¬ (B ∩ B').Nonempty := by
        intro hBB'
        have hsep := sep_of_boundary hBB' hAne
          (Disjoint.mono_left Finset.inter_subset_left hdAB.symm)
          (fun x hx y hy h => hnoAB y hy x (Finset.mem_inter.1 hx).1 h.symm)
        have hge := hk_min _ hsep
        omega
      rw [Finset.not_nonempty_iff_eq_empty] at hBB'_empty
      have hS_sum : (S ∩ A').card + (S ∩ S').card + (S ∩ B').card = k := by
        have hu : (S ∩ A') ∪ (S ∩ S') ∪ (S ∩ B') = S := by
          ext x; simp only [Finset.mem_union, Finset.mem_inter]
          constructor
          · rintro ((⟨h, _⟩ | ⟨h, _⟩) | ⟨h, _⟩) <;> exact h
          · intro hx; rcases hpart' x with h | h | h
            · exact Or.inl (Or.inl ⟨hx, h⟩)
            · exact Or.inr ⟨hx, h⟩
            · exact Or.inl (Or.inr ⟨hx, h⟩)
        have hd1 : Disjoint (S ∩ A') (S ∩ S') := Disjoint.mono Finset.inter_subset_right Finset.inter_subset_right hdAS'
        have hd2 : Disjoint ((S ∩ A') ∪ (S ∩ S')) (S ∩ B') := by
          rw [Finset.disjoint_union_left]
          exact ⟨Disjoint.mono Finset.inter_subset_right Finset.inter_subset_right hdAB',
                 Disjoint.mono Finset.inter_subset_right Finset.inter_subset_right hdBS'.symm⟩
        calc (S ∩ A').card + (S ∩ S').card + (S ∩ B').card
            = ((S ∩ A') ∪ (S ∩ S') ∪ (S ∩ B')).card := by
              rw [Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd1]
          _ = S.card := by rw [hu]
          _ = k := hSc
      have hS'_sum : (S' ∩ A).card + (S ∩ S').card + (S' ∩ B).card = k := by
        have hu : (S' ∩ A) ∪ (S ∩ S') ∪ (S' ∩ B) = S' := by
          ext x; simp only [Finset.mem_union, Finset.mem_inter]
          constructor
          · rintro ((⟨h, _⟩ | ⟨_, h⟩) | ⟨h, _⟩) <;> exact h
          · intro hx; rcases hpart x with h | h | h
            · exact Or.inl (Or.inl ⟨hx, h⟩)
            · exact Or.inr ⟨hx, h⟩
            · exact Or.inl (Or.inr ⟨h, hx⟩)
        have hd1 : Disjoint (S' ∩ A) (S ∩ S') := Disjoint.mono Finset.inter_subset_right Finset.inter_subset_left hdAS
        have hd2 : Disjoint ((S' ∩ A) ∪ (S ∩ S')) (S' ∩ B) := by
          rw [Finset.disjoint_union_left]
          exact ⟨Disjoint.mono Finset.inter_subset_right Finset.inter_subset_right hdAB,
                 Disjoint.mono Finset.inter_subset_left Finset.inter_subset_right hdBS.symm⟩
        calc (S' ∩ A).card + (S ∩ S').card + (S' ∩ B).card
            = ((S' ∩ A) ∪ (S ∩ S') ∪ (S' ∩ B)).card := by
              rw [Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd1]
          _ = S'.card := by rw [hu]
          _ = k := hS'c
      have hgt1 : (S ∩ B').card < (S' ∩ A).card := by omega
      have hgt2 : (S' ∩ B).card < (S ∩ A').card := by omega
      have hAB'_ne : (A ∩ B').Nonempty := by
        by_contra he
        rw [Finset.not_nonempty_iff_eq_empty] at he
        have hB'S : B' ⊆ S := fun x hx => by
          rcases hpart x with hxA | hxB | hxS
          · exact absurd (Finset.mem_inter.2 ⟨hxA, hx⟩) (by rw [he]; exact Finset.notMem_empty x)
          · exact absurd (Finset.mem_inter.2 ⟨hxB, hx⟩) (by rw [hBB'_empty]; exact Finset.notMem_empty x)
          · exact hxS
        have h1 : B'.card ≤ (S ∩ B').card := Finset.card_le_card (fun x hx => Finset.mem_inter.2 ⟨hB'S hx, hx⟩)
        have h2 : (S' ∩ A).card ≤ A.card := Finset.card_le_card Finset.inter_subset_right
        omega
      have hAB'_lt : (A ∩ B').card < a := by
        rw [← hAc]
        refine Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨Finset.inter_subset_left, ?_⟩)
        intro heq
        obtain ⟨x, hx⟩ := hne
        have hx1 : x ∈ A ∩ B' := by rw [heq]; exact (Finset.mem_inter.1 hx).1
        exact Finset.disjoint_left.1 hdAB' (Finset.mem_inter.1 hx).2 (Finset.mem_inter.1 hx1).2
      have hAB'_ge := hmin_any (A ∩ B') A' hAB'_ne (hAne.image φ)
        (Disjoint.mono_left Finset.inter_subset_right hdAB'.symm)
        (fun x hx y hy h => hnoAB' y hy x (Finset.mem_inter.1 hx).2 h.symm) hAB'_lt
      have hsub2 := card_boundary_union_inter_le hpart hdAB hdAS hdBS
        (fun x => by rcases hpart' x with h | h | h; exact Or.inr (Or.inl h); exact Or.inl h; exact Or.inr (Or.inr h))
        hdAB'.symm hdBS' hdAS' hnoAB (fun x hx y hy h => hnoAB' y hy x hx h.symm)
      have hBA'_empty : ¬ (B ∩ A').Nonempty := by
        intro hBA'
        have hsep := sep_of_boundary hBA' hAne
          (Disjoint.mono_left Finset.inter_subset_left hdAB.symm)
          (fun x hx y hy h => hnoAB y hy x (Finset.mem_inter.1 hx).1 h.symm)
        have hge := hk_min _ hsep
        omega
      rw [Finset.not_nonempty_iff_eq_empty] at hBA'_empty
      have hBS' : B ⊆ S' := fun x hx => by
        rcases hpart' x with hxA' | hxB' | hxS'
        · exact absurd (Finset.mem_inter.2 ⟨hx, hxA'⟩) (by rw [hBA'_empty]; exact Finset.notMem_empty x)
        · exact absurd (Finset.mem_inter.2 ⟨hx, hxB'⟩) (by rw [hBB'_empty]; exact Finset.notMem_empty x)
        · exact hxS'
      have h1 : B.card ≤ (S' ∩ B).card := Finset.card_le_card (fun x hx => Finset.mem_inter.2 ⟨hBS' hx, hx⟩)
      have h2 : (S ∩ A').card ≤ A'.card := Finset.card_le_card Finset.inter_subset_right
      omega
    · right
      exact Finset.disjoint_iff_inter_eq_empty.2 (Finset.not_nonempty_iff_eq_empty.1 hne)
  -- Step 2: Every atom A' meeting S is contained in S!
  have hatom_sub_S : ∀ φ : G ≃g G, (A.image φ ∩ S).Nonempty → A.image φ ⊆ S := by
    intro φ hmeet
    let A' := A.image φ
    let B' := B.image φ
    let S' := S.image φ
    have hdisjAA' : Disjoint A A' := by
      rcases hatom_disj φ with heq | hd
      · obtain ⟨u, hu⟩ := hmeet
        rw [Finset.mem_inter, heq] at hu
        exact absurd hu.2 (Finset.disjoint_left.1 hdAS hu.1)
      · exact hd
    have hpart' : ∀ x, x ∈ A' ∨ x ∈ B' ∨ x ∈ S' := fun x => by
      rcases hpart (φ.symm x) with h | h | h
      · exact Or.inl (Finset.mem_image.2 ⟨φ.symm x, h, φ.apply_symm_apply x⟩)
      · exact Or.inr (Or.inl (Finset.mem_image.2 ⟨φ.symm x, h, φ.apply_symm_apply x⟩))
      · exact Or.inr (Or.inr (Finset.mem_image.2 ⟨φ.symm x, h, φ.apply_symm_apply x⟩))
    have hdAB' : Disjoint A' B' := hdisj_img φ hdAB
    have hdAS' : Disjoint A' S' := hdisj_img φ hdAS
    have hdBS' : Disjoint B' S' := hdisj_img φ hdBS
    have hnoAB' : ∀ x ∈ A', ∀ y ∈ B', ¬ G.Adj x y := by
      intro x hx y hy hxy
      obtain ⟨x₀, hx₀, rfl⟩ := Finset.mem_image.1 hx
      obtain ⟨y₀, hy₀, rfl⟩ := Finset.mem_image.1 hy
      exact hnoAB x₀ hx₀ y₀ hy₀ (φ.map_rel_iff.1 hxy)
    have hS'c : S'.card = k := (Finset.card_image_of_injective S φ.injective).trans hSc
    have hA'c : A'.card = a := (Finset.card_image_of_injective A φ.injective).trans hAc
    intro x hxA'
    rcases hpart x with hxA | hxB | hxS
    · exact absurd hxA' (Finset.disjoint_left.1 hdisjAA' hxA)
    · exfalso
      have hA'B_ne : (A' ∩ B).Nonempty := ⟨x, Finset.mem_inter.2 ⟨hxA', hxB⟩⟩
      have hA'B_lt : (A' ∩ B).card < a := by
        rw [← hA'c]
        refine Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨Finset.inter_subset_left, ?_⟩)
        intro heq
        obtain ⟨u, hu⟩ := hmeet
        have huA' : u ∈ A' := (Finset.mem_inter.1 hu).1
        have huB : u ∈ A' ∩ B := by rw [heq]; exact huA'
        exact Finset.disjoint_left.1 hdBS (Finset.mem_inter.1 huB).2 (Finset.mem_inter.1 hu).2
      have hA'B_ge := hmin_any (A' ∩ B) A hA'B_ne hAne
        (Disjoint.mono_left Finset.inter_subset_right hdAB.symm)
        (fun z hz w hw h => hnoAB w hw z (Finset.mem_inter.1 hz).2 h.symm) hA'B_lt
      have hsub := card_boundary_union_inter_le
        (fun z => by rcases hpart' z with h | h | h; exact Or.inl h; exact Or.inr (Or.inl h); exact Or.inr (Or.inr h))
        hdAB' hdAS' hdBS'
        (fun z => by rcases hpart z with h | h | h; exact Or.inr (Or.inl h); exact Or.inl h; exact Or.inr (Or.inr h))
        hdAB.symm hdBS hdAS hnoAB' (fun z hz w hw h => hnoAB w hw z hz h.symm)
      have hB'A_empty : ¬ (B' ∩ A).Nonempty := by
        intro hB'A
        have hsep := sep_of_boundary hB'A (hAne.image φ)
          (Disjoint.mono_left Finset.inter_subset_left hdAB'.symm)
          (fun z hz w hw h => hnoAB' w hw z (Finset.mem_inter.1 hz).1 h.symm)
        have hge := hk_min _ hsep
        omega
      rw [Finset.not_nonempty_iff_eq_empty] at hB'A_empty
      have hAS' : A ⊆ S' := fun z hzA => by
        rcases hpart' z with hzA' | hzB' | hzS'
        · exact absurd hzA' (Finset.disjoint_left.1 hdisjAA' hzA)
        · exact absurd (Finset.mem_inter.2 ⟨hzB', hzA⟩) (by rw [hB'A_empty]; exact Finset.notMem_empty z)
        · exact hzS'
      have hN_le : (Finset.univ.filter (fun z => z ∉ A' ∩ B ∧ ∃ w ∈ A' ∩ B, G.Adj w z)).card ≤
          (S' \ A).card + (S ∩ A').card := by
        have hsubN : Finset.univ.filter (fun z => z ∉ A' ∩ B ∧ ∃ w ∈ A' ∩ B, G.Adj w z) ⊆
            (S' \ A) ∪ (S ∩ A') := by
          intro z hz
          have hz3 := hsub.2.1 z hz
          simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff] at hz3 ⊢
          rcases hz3 with (⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩
          · exact Or.inl ⟨h1, fun hzA => Finset.disjoint_left.1 hdAB hzA h2⟩
          · exact Or.inl ⟨h1, fun hzA => Finset.disjoint_left.1 hdAS hzA h2⟩
          · exact Or.inr ⟨h1, h2⟩
        exact (Finset.card_le_card hsubN).trans (Finset.card_union_le _ _)
      have hsdiff : (S' \ A).card = k - a := by
        rw [Finset.card_sdiff, Finset.inter_eq_left.2 hAS', hS'c, hAc]
      have hSA'_lt : (S ∩ A').card ≤ a - 1 := by
        have hss : S ∩ A' ⊂ A' := Finset.ssubset_iff_subset_ne.2 ⟨Finset.inter_subset_right, fun heq => by
          have hxA'' : x ∈ A' := hxA'
          have hxS : x ∈ S := (Finset.mem_inter.1 (heq ▸ hxA'')).1
          exact Finset.disjoint_left.1 hdBS hxB hxS⟩
        have := Finset.card_lt_card hss
        omega
      have ha_le_k : a ≤ k := by
        have := Finset.card_le_card hAS'
        omega
      omega
    · exact hxS
  -- Step 3: Since 2 ≤ a and k ≤ 3 and S is a disjoint union of atoms of size a, we get a = k and S is a SINGLE atom!
  obtain ⟨u₀, hu₀S⟩ : S.Nonempty := Finset.card_pos.1 (by omega)
  obtain ⟨a₀, ha₀A⟩ := hAne
  obtain ⟨φ₀, hφ₀⟩ := hvt a₀ u₀
  have hS_atom : A.image φ₀ = S := by
    have hsub : A.image φ₀ ⊆ S := hatom_sub_S φ₀ ⟨u₀, Finset.mem_inter.2 ⟨Finset.mem_image.2 ⟨a₀, ha₀A, hφ₀⟩, hu₀S⟩⟩
    have hc : (A.image φ₀).card = a := (Finset.card_image_of_injective A φ₀.injective).trans hAc
    have ha_le_k : a ≤ k := hc ▸ hSc ▸ Finset.card_le_card hsub
    by_cases hkeq : a = k
    · exact Finset.eq_of_subset_of_card_le hsub (by omega)
    · have hne_diff : (S \ A.image φ₀).Nonempty := Finset.card_pos.1 (by
        rw [Finset.card_sdiff, Finset.inter_eq_left.2 hsub, hSc, hc]; omega)
      obtain ⟨u₁, hu₁⟩ := hne_diff
      rw [Finset.mem_sdiff] at hu₁
      obtain ⟨φ₁, hφ₁⟩ := hvt a₀ u₁
      have hsub1 : A.image φ₁ ⊆ S := hatom_sub_S φ₁ ⟨u₁, Finset.mem_inter.2 ⟨Finset.mem_image.2 ⟨a₀, ha₀A, hφ₁⟩, hu₁.1⟩⟩
      have hd01 : Disjoint (A.image φ₀) (A.image φ₁) := by
        rcases hatom_disj (φ₁.trans φ₀.symm) with heq | hd
        · exfalso
          have hu₁in : u₁ ∈ A.image φ₀ := by
            have : φ₀.symm u₁ ∈ A := by
              rw [← heq]
              exact Finset.mem_image.2 ⟨a₀, ha₀A, by simp [RelIso.trans_apply, hφ₁]⟩
            exact Finset.mem_image.2 ⟨φ₀.symm u₁, this, φ₀.apply_symm_apply u₁⟩
          exact hu₁.2 hu₁in
        · rw [Finset.disjoint_left]
          intro z hz0 hz1
          obtain ⟨w0, hw0, rfl⟩ := Finset.mem_image.1 hz0
          obtain ⟨w1, hw1, hweq⟩ := Finset.mem_image.1 hz1
          have hw0' : w0 ∈ A.image (φ₁.trans φ₀.symm) :=
            Finset.mem_image.2 ⟨w1, hw1, by simp [RelIso.trans_apply, hweq]⟩
          exact Finset.disjoint_left.1 hd hw0 hw0'
      have hcard_u := Finset.card_le_card (Finset.union_subset hsub hsub1)
      rw [Finset.card_union_of_disjoint hd01, Finset.card_image_of_injective A φ₀.injective,
          Finset.card_image_of_injective A φ₁.injective, hAc, hSc] at hcard_u
      omega
  -- Step 4: Every atom disconnects G, yet the quotient graph on atoms has a non-cut-vertex!
  let Atoms : Finset (Finset V) := Finset.univ.filter (fun X => ∃ ψ : G ≃g G, A.image ψ = X)
  have hAt_ge2 : 2 ≤ Fintype.card {X : Finset V // X ∈ Atoms} := by
    have hA_in : A ∈ Atoms := by
      simp only [Atoms, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨RelIso.refl _, by ext z; simp⟩
    have hS_in : S ∈ Atoms := by
      simp only [Atoms, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨φ₀, hS_atom⟩
    have hne : (⟨A, hA_in⟩ : {X // X ∈ Atoms}) ≠ ⟨S, hS_in⟩ := by
      intro h
      have hASeq : A = S := congrArg Subtype.val h
      exact Finset.disjoint_left.1 hdAS ha₀A (hASeq ▸ ha₀A)
    have hsub : ({⟨A, hA_in⟩, ⟨S, hS_in⟩} : Finset {X // X ∈ Atoms}) ⊆ Finset.univ := Finset.subset_univ _
    have hc := Finset.card_le_card hsub
    rw [Finset.card_pair hne, Finset.card_univ] at hc
    exact hc
  let Q : SimpleGraph {X : Finset V // X ∈ Atoms} :=
    { Adj := fun X Y => X ≠ Y ∧ ∃ x ∈ X.1, ∃ y ∈ Y.1, G.Adj x y
      symm := ⟨fun X Y h => ⟨h.1.symm, let ⟨x, hx, y, hy, hxy⟩ := h.2; ⟨y, hy, x, hx, hxy.symm⟩⟩⟩
      loopless := ⟨fun X h => h.1 rfl⟩ }
  have hAtom_of_vert : ∀ v : V, ∃ X : {X // X ∈ Atoms}, v ∈ X.1 := by
    intro v
    obtain ⟨ψ, hψ⟩ := hvt a₀ v
    exact ⟨⟨A.image ψ, by simp only [Atoms, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨ψ, rfl⟩⟩,
           Finset.mem_image.2 ⟨a₀, ha₀A, hψ⟩⟩
  have hAtom_uniq : ∀ (X Y : {X // X ∈ Atoms}) (v : V), v ∈ X.1 → v ∈ Y.1 → X = Y := by
    intro X Y v hvX hvY
    apply Subtype.ext
    have hX := (Finset.mem_filter.1 X.2).2
    have hY := (Finset.mem_filter.1 Y.2).2
    obtain ⟨ψ₁, hψ₁⟩ := hX
    obtain ⟨ψ₂, hψ₂⟩ := hY
    rcases hatom_disj (ψ₂.trans ψ₁.symm) with heq | hd
    · rw [← hψ₁, ← hψ₂]
      ext z; simp only [Finset.mem_image]
      constructor
      · rintro ⟨w, hw, rfl⟩
        have hw' : w ∈ A.image (ψ₂.trans ψ₁.symm) := by rw [heq]; exact hw
        obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hw'
        exact ⟨u, hu, by simp [RelIso.trans_apply]⟩
      · rintro ⟨u, hu, rfl⟩
        have : ψ₁.symm (ψ₂ u) ∈ A := by
          rw [← heq]; exact Finset.mem_image.2 ⟨u, hu, rfl⟩
        exact ⟨ψ₁.symm (ψ₂ u), this, ψ₁.apply_symm_apply _⟩
    · exfalso
      rw [← hψ₁] at hvX; rw [← hψ₂] at hvY
      obtain ⟨w1, hw1, h1⟩ := Finset.mem_image.1 hvX
      obtain ⟨w2, hw2, h2⟩ := Finset.mem_image.1 hvY
      have hw1' : w1 ∈ A.image (ψ₂.trans ψ₁.symm) :=
        Finset.mem_image.2 ⟨w2, hw2, by simp [RelIso.trans_apply, h2, ← h1]⟩
      exact Finset.disjoint_left.1 hd hw1 hw1'
  have hQconn : Q.Connected := by
    have : Nonempty {X // X ∈ Atoms} := Fintype.card_pos_iff.1 (by omega)
    refine ⟨fun X Y => ?_⟩
    obtain ⟨ψX, hψX⟩ := (Finset.mem_filter.1 X.2).2
    obtain ⟨ψY, hψY⟩ := (Finset.mem_filter.1 Y.2).2
    have hx : ψX a₀ ∈ X.1 := hψX ▸ Finset.mem_image.2 ⟨a₀, ha₀A, rfl⟩
    have hy : ψY a₀ ∈ Y.1 := hψY ▸ Finset.mem_image.2 ⟨a₀, ha₀A, rfl⟩
    obtain ⟨w⟩ := hconn (ψX a₀) (ψY a₀)
    have hlift : ∀ {p q : V} (w' : G.Walk p q) (Xp Xq : {X // X ∈ Atoms}),
        p ∈ Xp.1 → q ∈ Xq.1 → Q.Reachable Xp Xq := by
      intro p q w'
      induction w' with
      | nil => intro Xp Xq hp hq; rw [hAtom_uniq Xp Xq _ hp hq]
      | @cons p r s hpr w'' ih =>
        intro Xp Xs hp hs
        obtain ⟨Xr, hr⟩ := hAtom_of_vert r
        have hstep : Q.Reachable Xp Xr := by
          by_cases heq : Xp = Xr
          · rw [heq]
          · exact Adj.reachable ⟨heq, p, hp, r, hr, hpr⟩
        exact hstep.trans (ih Xr Xs hr hs)
    exact hlift w X Y hx hy
  obtain ⟨M, hMconn⟩ := exists_non_cut_vertex Q hQconn hAt_ge2
  obtain ⟨ψM, hψM⟩ := (Finset.mem_filter.1 M.2).2
  have hGM_conn : (G.induce {x | x ∉ (M.1 : Set V)}).Connected := by
    obtain ⟨⟨R, hRM⟩⟩ := hMconn.nonempty
    obtain ⟨ψR, hψR⟩ := (Finset.mem_filter.1 R.2).2
    let r₀ := ψR a₀
    have hr₀R : r₀ ∈ R.1 := hψR ▸ Finset.mem_image.2 ⟨a₀, ha₀A, rfl⟩
    have hr₀M : r₀ ∉ (M.1 : Set V) := fun h => hRM (hAtom_uniq R M r₀ hr₀R h)
    have hX_conn : ∀ (X : {X // X ∈ Atoms}) (hXM : X ≠ M),
        ∀ x (hx : x ∈ X.1) y (hy : y ∈ X.1),
          (G.induce {z | z ∉ (M.1 : Set V)}).Reachable
            ⟨x, fun h => hXM (hAtom_uniq X M x hx h)⟩
            ⟨y, fun h => hXM (hAtom_uniq X M y hy h)⟩ := by
      intro X hXM x hx y hy
      obtain ⟨ψX, hψX⟩ := (Finset.mem_filter.1 X.2).2
      have hXc : (G.induce (X.1 : Set V)).Connected := by
        refine induce_connected_of_iso ψX (fun z => ?_) hAconn
        rw [← hψX]; simp
      obtain ⟨w, hwX⟩ := (walk_induce_iff_exists_walk (show x ∈ (X.1 : Set V) from hx)
        (show y ∈ (X.1 : Set V) from hy)).1 (hXc.preconnected ⟨x, hx⟩ ⟨y, hy⟩)
      exact (walk_induce_iff_exists_walk _ _).2 ⟨w, fun z hz hM => hXM (hAtom_uniq X M z (hwX z hz) hM)⟩
    refine induce_connected_of_base hr₀M ?_
    intro x hxM
    obtain ⟨X, hxX⟩ := hAtom_of_vert x
    have hXM : X ≠ M := fun h => hxM (h ▸ hxX)
    obtain ⟨wQ, hwQ⟩ := (walk_induce_iff_exists_walk (G := Q) hXM hRM).1
      (hMconn.preconnected ⟨X, hXM⟩ ⟨R, hRM⟩)
    have hliftQ : ∀ {X₁ X₂ : {X // X ∈ Atoms}} (wq : Q.Walk X₁ X₂)
        (hne : ∀ Z ∈ wq.support, Z ≠ M),
        ∀ x₁ (hx₁ : x₁ ∈ X₁.1) x₂ (hx₂ : x₂ ∈ X₂.1),
          (G.induce {z | z ∉ (M.1 : Set V)}).Reachable
            ⟨x₁, fun h => (hne X₁ wq.start_mem_support) (hAtom_uniq X₁ M x₁ hx₁ h)⟩
            ⟨x₂, fun h => (hne X₂ wq.end_mem_support) (hAtom_uniq X₂ M x₂ hx₂ h)⟩ := by
      intro X₁ X₂ wq
      induction wq with
      | @nil U =>
        intro hne x₁ hx₁ x₂ hx₂
        exact hX_conn U (hne U (by simp)) x₁ hx₁ x₂ hx₂
      | @cons U₁ U₂ U₃ h12 wq' ih =>
        intro hne x₁ hx₁ x₃ hx₃
        obtain ⟨_, u₁, hu₁, u₂, hu₂, hu12⟩ := h12
        have hU₁M : U₁ ≠ M := hne U₁ (by simp)
        have hU₂M : U₂ ≠ M := hne U₂ (by simp)
        have h1 := hX_conn U₁ hU₁M x₁ hx₁ u₁ hu₁
        have h2 : (G.induce {z | z ∉ (M.1 : Set V)}).Reachable
            ⟨u₁, fun h => hU₁M (hAtom_uniq U₁ M u₁ hu₁ h)⟩
            ⟨u₂, fun h => hU₂M (hAtom_uniq U₂ M u₂ hu₂ h)⟩ := Adj.reachable hu12
        have h3 := ih (fun Z hZ => hne Z (by simp [hZ])) u₂ hu₂ x₃ hx₃
        exact h1.trans (h2.trans h3)
    exact hliftQ wQ hwQ x hxX r₀ hr₀R
  have hGS_conn : (G.induce {x | x ∉ (S : Set V)}).Connected := by
    refine induce_connected_of_iso (ψM.symm.trans φ₀) (fun x => ?_) hGM_conn
    simp only [Set.mem_ofPred_eq, Finset.mem_coe, not_iff_not, RelIso.trans_apply]
    rw [← hψM, ← hS_atom]
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a, ha, by simp⟩
    · rintro ⟨a, ha, hfa⟩
      have haeq : a = ψM.symm x := φ₀.injective hfa
      exact ⟨a, ha, by rw [haeq, ψM.apply_symm_apply]⟩
  exact sep_of_boundary ⟨a₀, ha₀A⟩ hBne hdAB hnoAB (by
    have hNS : (Finset.univ.filter (fun z => z ∉ A ∧ ∃ x ∈ A, G.Adj x z)) ⊆ S := by
      intro z hz
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
      rcases hpart z with hzA | hzB | hzS
      · exact absurd hzA hz.1
      · obtain ⟨x, hxA, hxz⟩ := hz.2
        exact absurd hxz (hnoAB x hxA z hzB)
      · exact hzS
    have hNeqS : Finset.univ.filter (fun z => z ∉ A ∧ ∃ x ∈ A, G.Adj x z) = S := by
      have hge := hk_min _ (sep_of_boundary ⟨a₀, ha₀A⟩ hBne hdAB hnoAB)
      exact Finset.eq_of_subset_of_card_le hNS (hSc.symm ▸ hge)
    rwa [hNeqS])

private lemma length_le_two_connected [Fintype V] {G : SimpleGraph V}
    (hconn : G.Connected) (hvt : IsVertexTransitive G)
    (hcard : 3 ≤ Fintype.card V) {u v : V} (p : G.Walk u v) (hp : p.IsPath)
    (hgeo : p.length = G.dist u v) (hlen : p.length ≤ 2) :
    (G.induce {x | x ∉ p.support}).Connected := by
  by_contra hnot
  have hne : ({x : V | x ∉ p.support}).Nonempty := exists_not_mem_geodesic hvt hcard p hp hgeo
  have hsupp_eq : {x : V | x ∉ p.support} = {x : V | x ∉ (p.support.toFinset : Set V)} := by
    ext x; simp
  have hS_card : p.support.toFinset.card = p.length + 1 := by
    rw [List.toFinset_card_of_nodup hp.support_nodup, Walk.length_support]
  have hp0 : p.length ≠ 0 := by
    intro h0
    have hsupp : p.support = [u] := by
      cases p with
      | nil => rfl
      | cons _ _ => simp at h0
    have heq : {x : V | x ∉ p.support} = {x | x ≠ u} := by ext x; simp [hsupp]
    rw [heq] at hnot
    exact hnot (length_zero_connected hconn hvt (by omega) u)
  -- Case p.length = 1: p.support = [u, v]
  by_cases hp1 : p.length = 1
  · have hdeg_le2 : G.degree u ≤ 2 := by
      have h := watkins_deg_le_cut_of_le_three hconn hvt hcard (S₀ := p.support.toFinset)
        (by omega) (hsupp_eq ▸ hnot) u
      omega
    obtain ⟨A, B, hA, hB, _, hpart, hdAB, hnoAB⟩ := not_connected_induce_split hne hnot
    have huv : G.Adj u v := by
      have h := p.adj_getVert_succ (i := 0) (by omega)
      rw [Walk.getVert_zero, show (0 : ℕ) + 1 = p.length by omega, p.getVert_length] at h
      exact h
    have hv_conn := length_zero_connected hconn hvt (by omega) v
    obtain ⟨a₀, ha₀⟩ := hA
    obtain ⟨b₀, hb₀⟩ := hB
    have ha₀_ne : a₀ ≠ v := fun h => ((hpart a₀).2 (Or.inl ha₀)) (h ▸ p.end_mem_support)
    have hb₀_ne : b₀ ≠ v := fun h => ((hpart b₀).2 (Or.inr hb₀)) (h ▸ p.end_mem_support)
    obtain ⟨w, hwv⟩ := (walk_induce_iff_exists_walk ha₀_ne hb₀_ne).1
      (hv_conn.preconnected ⟨a₀, ha₀_ne⟩ ⟨b₀, hb₀_ne⟩)
    have hu_in : u ∈ w.support := by
      by_contra hun
      have hstay := walk_stay_in_part hnoAB w ha₀ (fun z hz => (hpart z).1 (fun hzp => by
        obtain ⟨i, hi, rfl⟩ := (mem_support_iff_getVert p z).1 hzp
        have hi01 : i = 0 ∨ i = 1 := by omega
        rcases hi01 with rfl | rfl
        · exact hun (by simpa using hz)
        · exact hwv (p.getVert 1) hz (by rw [← hp1, p.getVert_length])))
      exact Finset.disjoint_left.1 hdAB (hstay b₀ w.end_mem_support) hb₀
    have huA_not : u ∉ A := fun h => ((hpart u).2 (Or.inl h)) p.start_mem_support
    have huB_not : u ∉ B := fun h => ((hpart u).2 (Or.inr h)) p.start_mem_support
    have hnotp_of_ne : ∀ t, t ≠ u → t ≠ v → t ∈ A ∨ t ∈ B := fun t htu htv =>
      (hpart t).1 (fun htp => by
        obtain ⟨i, hi, rfl⟩ := (mem_support_iff_getVert p t).1 htp
        have hi01 : i = 0 ∨ i = 1 := by omega
        rcases hi01 with rfl | rfl
        · exact htu (by simp)
        · exact htv (by rw [← hp1, p.getVert_length]))
    have hu_A : ∃ a ∈ A, G.Adj u a :=
      walk_enter_target_adj hnoAB huA_not (w.takeUntil u hu_in) ha₀ (fun t ht htu =>
        hnotp_of_ne t htu (hwv t (Walk.support_takeUntil_subset_support w hu_in ht)))
    have hu_in_rev : u ∈ w.reverse.support := by simpa using hu_in
    have hu_B : ∃ b ∈ B, G.Adj u b :=
      walk_enter_target_adj (fun b hb a ha h => hnoAB a ha b hb h.symm) huB_not
        (w.reverse.takeUntil u hu_in_rev) hb₀ (fun t ht htu =>
          (hnotp_of_ne t htu (hwv t (by simpa using Walk.support_takeUntil_subset_support w.reverse hu_in_rev ht))).symm)
    obtain ⟨a, haA, hua⟩ := hu_A
    obtain ⟨b, hbB, hub⟩ := hu_B
    have hab : a ≠ b := fun h => Finset.disjoint_left.1 hdAB haA (h ▸ hbB)
    have hav : a ≠ v := fun h => ((hpart a).2 (Or.inl haA)) (h ▸ p.end_mem_support)
    have hbv : b ≠ v := fun h => ((hpart b).2 (Or.inr hbB)) (h ▸ p.end_mem_support)
    have hsub : ({a, b, v} : Finset V) ⊆ G.neighborFinset u := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rw [SimpleGraph.mem_neighborFinset]
      rcases hz with rfl | rfl | rfl <;> assumption
    have hc := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem (by simp [hab, hav]),
        Finset.card_pair hbv, SimpleGraph.card_neighborFinset_eq_degree] at hc
    omega
  -- Case p.length = 2: p = (v₀, v₁, v₂)
  have hp2 : p.length = 2 := by omega
  have hdeg_le3 : ∀ x : V, G.degree x ≤ 3 := by
    intro x
    have := watkins_deg_le_cut_of_le_three hconn hvt hcard (S₀ := p.support.toFinset)
      (by omega) (hsupp_eq ▸ hnot) x
    omega
  obtain ⟨A, B, hA, hB, _, hpart, hdAB, hnoAB⟩ := not_connected_induce_split hne hnot
  let v₁ := p.getVert 1
  have hv₁0 : G.Adj v₁ u := by
    have h := (p.adj_getVert_succ (i := 0) (by omega)).symm
    simpa [v₁] using h
  have hv₁2 : G.Adj v₁ v := by
    have h := p.adj_getVert_succ (i := 1) (by omega)
    rw [show (1 : ℕ) + 1 = p.length by omega, p.getVert_length] at h
    exact h
  have huv_ne : u ≠ v := by
    intro h
    have h02 := geodesic_dist_getVert p hgeo (show 0 ≤ 2 by omega) (by omega)
    simp only [Walk.getVert_zero, ← hp2, Walk.getVert_length, h, SimpleGraph.dist_self] at h02
    omega
  have hv₁_miss : (∀ a ∈ A, ¬ G.Adj v₁ a) ∨ (∀ b ∈ B, ¬ G.Adj v₁ b) := by
    by_contra hboth
    push Not at hboth
    obtain ⟨⟨a, ha, hva⟩, ⟨b, hb, hvb⟩⟩ := hboth
    have hab : a ≠ b := fun h => Finset.disjoint_left.1 hdAB ha (h ▸ hb)
    have hau : a ≠ u := fun h => ((hpart a).2 (Or.inl ha)) (h ▸ p.start_mem_support)
    have hav : a ≠ v := fun h => ((hpart a).2 (Or.inl ha)) (h ▸ p.end_mem_support)
    have hbu : b ≠ u := fun h => ((hpart b).2 (Or.inr hb)) (h ▸ p.start_mem_support)
    have hbv : b ≠ v := fun h => ((hpart b).2 (Or.inr hb)) (h ▸ p.end_mem_support)
    have hsub : ({a, b, u, v} : Finset V) ⊆ G.neighborFinset v₁ := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rw [SimpleGraph.mem_neighborFinset]
      rcases hz with rfl | rfl | rfl | rfl <;> assumption
    have hc := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem (by simp [hab, hau, hav]),
        Finset.card_insert_of_notMem (by simp [hbu, hbv]),
        Finset.card_pair huv_ne, SimpleGraph.card_neighborFinset_eq_degree] at hc
    have := hdeg_le3 v₁
    omega
  have hcut2 : ¬ (G.induce {x | x ∉ (({u, v} : Finset V) : Set V)}).Connected := by
    have hv₁_notA : v₁ ∉ A := fun h => ((hpart v₁).2 (Or.inl h)) (p.getVert_mem_support 1)
    have hv₁_notB : v₁ ∉ B := fun h => ((hpart v₁).2 (Or.inr h)) (p.getVert_mem_support 1)
    rcases hv₁_miss with hmissA | hmissB
    · have hsep := sep_of_boundary hA (Finset.insert_nonempty v₁ B)
        (Finset.disjoint_insert_right.2 ⟨hv₁_notA, hdAB⟩)
        (fun a ha x hx => by
          rw [Finset.mem_insert] at hx
          rcases hx with rfl | hxB
          · exact fun h => hmissA a ha h.symm
          · exact hnoAB a ha x hxB)
      have hNsub : Finset.univ.filter (fun z => z ∉ A ∧ ∃ a ∈ A, G.Adj a z) ⊆ ({u, v} : Finset V) := by
        intro z hz
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
        obtain ⟨hzA, a, ha, haz⟩ := hz
        by_cases hzp : z ∈ p.support
        · obtain ⟨i, hi, rfl⟩ := (mem_support_iff_getVert p z).1 hzp
          have : i = 0 ∨ i = 1 ∨ i = 2 := by omega
          rcases this with rfl | rfl | rfl
          · simp
          · exact absurd haz.symm (hmissA a ha)
          · simp [← hp2]
        · rcases (hpart z).1 hzp with h | h
          · exact absurd h hzA
          · exact absurd haz (hnoAB a ha z h)
      intro hconn2
      apply hsep
      obtain ⟨a₀, ha₀⟩ := hA
      have ha₀2 : a₀ ∉ (({u, v} : Finset V) : Set V) := by
        simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨fun h => ((hpart a₀).2 (Or.inl ha₀)) (h ▸ p.start_mem_support),
               fun h => ((hpart a₀).2 (Or.inl ha₀)) (h ▸ p.end_mem_support)⟩
      refine induce_connected_of_base (r := a₀) (fun h => ha₀2 (hNsub h)) ?_
      intro x hxN
      by_cases hx2 : x ∉ (({u, v} : Finset V) : Set V)
      · obtain ⟨w, hw2⟩ := (walk_induce_iff_exists_walk hx2 ha₀2).1 (hconn2.preconnected ⟨x, hx2⟩ ⟨a₀, ha₀2⟩)
        exact (walk_induce_iff_exists_walk hxN _).2 ⟨w, fun z hz h => hw2 z hz (hNsub h)⟩
      · push Not at hx2
        have hv₁_not2 : v₁ ∉ (({u, v} : Finset V) : Set V) := by
          simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨fun h => G.loopless.irrefl u (h ▸ hv₁0), fun h => G.loopless.irrefl v (h ▸ hv₁2)⟩
        have hxv₁ : G.Adj x v₁ := by
          simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hx2
          rcases hx2 with rfl | rfl
          · exact hv₁0.symm
          · exact hv₁2.symm
        obtain ⟨w, hw2⟩ := (walk_induce_iff_exists_walk hv₁_not2 ha₀2).1 (hconn2.preconnected ⟨v₁, hv₁_not2⟩ ⟨a₀, ha₀2⟩)
        exact (Adj.reachable (show (G.induce _).Adj ⟨x, hxN⟩ ⟨v₁, fun h => hv₁_not2 (hNsub h)⟩ from hxv₁)).trans
          ((walk_induce_iff_exists_walk _ _).2 ⟨w, fun z hz h => hw2 z hz (hNsub h)⟩)
    · have hsep := sep_of_boundary hB (Finset.insert_nonempty v₁ A)
        (Finset.disjoint_insert_right.2 ⟨hv₁_notB, hdAB.symm⟩)
        (fun b hb x hx => by
          rw [Finset.mem_insert] at hx
          rcases hx with rfl | hxA
          · exact fun h => hmissB b hb h.symm
          · exact fun h => hnoAB x hxA b hb h.symm)
      have hNsub : Finset.univ.filter (fun z => z ∉ B ∧ ∃ b ∈ B, G.Adj b z) ⊆ ({u, v} : Finset V) := by
        intro z hz
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
        obtain ⟨hzB, b, hb, hbz⟩ := hz
        by_cases hzp : z ∈ p.support
        · obtain ⟨i, hi, rfl⟩ := (mem_support_iff_getVert p z).1 hzp
          have : i = 0 ∨ i = 1 ∨ i = 2 := by omega
          rcases this with rfl | rfl | rfl
          · simp
          · exact absurd hbz.symm (hmissB b hb)
          · simp [← hp2]
        · rcases (hpart z).1 hzp with h | h
          · exact absurd hbz.symm (hnoAB z h b hb)
          · exact absurd h hzB
      intro hconn2
      apply hsep
      obtain ⟨b₀, hb₀⟩ := hB
      have hb₀2 : b₀ ∉ (({u, v} : Finset V) : Set V) := by
        simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨fun h => ((hpart b₀).2 (Or.inr hb₀)) (h ▸ p.start_mem_support),
               fun h => ((hpart b₀).2 (Or.inr hb₀)) (h ▸ p.end_mem_support)⟩
      refine induce_connected_of_base (r := b₀) (fun h => hb₀2 (hNsub h)) ?_
      intro x hxN
      by_cases hx2 : x ∉ (({u, v} : Finset V) : Set V)
      · obtain ⟨w, hw2⟩ := (walk_induce_iff_exists_walk hx2 hb₀2).1 (hconn2.preconnected ⟨x, hx2⟩ ⟨b₀, hb₀2⟩)
        exact (walk_induce_iff_exists_walk hxN _).2 ⟨w, fun z hz h => hw2 z hz (hNsub h)⟩
      · push Not at hx2
        have hv₁_not2 : v₁ ∉ (({u, v} : Finset V) : Set V) := by
          simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨fun h => G.loopless.irrefl u (h ▸ hv₁0), fun h => G.loopless.irrefl v (h ▸ hv₁2)⟩
        have hxv₁ : G.Adj x v₁ := by
          simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hx2
          rcases hx2 with rfl | rfl
          · exact hv₁0.symm
          · exact hv₁2.symm
        obtain ⟨w, hw2⟩ := (walk_induce_iff_exists_walk hv₁_not2 hb₀2).1 (hconn2.preconnected ⟨v₁, hv₁_not2⟩ ⟨b₀, hb₀2⟩)
        exact (Adj.reachable (show (G.induce _).Adj ⟨x, hxN⟩ ⟨v₁, fun h => hv₁_not2 (hNsub h)⟩ from hxv₁)).trans
          ((walk_induce_iff_exists_walk _ _).2 ⟨w, fun z hz h => hw2 z hz (hNsub h)⟩)
  have hdeg_le2 : ∀ x : V, G.degree x ≤ 2 := by
    intro x
    have := watkins_deg_le_cut_of_le_three hconn hvt hcard (S₀ := {u, v})
      (by rw [Finset.card_pair huv_ne]; omega) hcut2 x
    rw [Finset.card_pair huv_ne] at this
    exact this
  have hu_miss : (∀ a ∈ A, ¬ G.Adj u a) ∨ (∀ b ∈ B, ¬ G.Adj u b) := by
    by_contra hboth
    push Not at hboth
    obtain ⟨⟨a, ha, hua⟩, ⟨b, hb, hub⟩⟩ := hboth
    have hab : a ≠ b := fun h => Finset.disjoint_left.1 hdAB ha (h ▸ hb)
    have hav₁ : a ≠ v₁ := fun h => ((hpart a).2 (Or.inl ha)) (h ▸ p.getVert_mem_support 1)
    have hbv₁ : b ≠ v₁ := fun h => ((hpart b).2 (Or.inr hb)) (h ▸ p.getVert_mem_support 1)
    have hsub : ({a, b, v₁} : Finset V) ⊆ G.neighborFinset u := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rw [SimpleGraph.mem_neighborFinset]
      rcases hz with rfl | rfl | rfl
      · exact hua
      · exact hub
      · exact hv₁0.symm
    have hc := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem (by simp [hab, hav₁]),
        Finset.card_pair hbv₁, SimpleGraph.card_neighborFinset_eq_degree] at hc
    have := hdeg_le2 u
    omega
  have hv₁_only : ∀ z, G.Adj v₁ z → z = u ∨ z = v := by
    intro z hzv₁
    by_contra hne
    push Not at hne
    have hsub : ({z, u, v} : Finset V) ⊆ G.neighborFinset v₁ := by
      intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rw [SimpleGraph.mem_neighborFinset]
      rcases ht with rfl | rfl | rfl <;> assumption
    have hc := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem (by simp [hne.1, hne.2]),
        Finset.card_pair huv_ne, SimpleGraph.card_neighborFinset_eq_degree] at hc
    have := hdeg_le2 v₁
    omega
  have hv_conn := length_zero_connected hconn hvt (by omega) v
  obtain ⟨a₀, ha₀⟩ := hA
  obtain ⟨b₀, hb₀⟩ := hB
  have ha₀v : a₀ ≠ v := fun h => ((hpart a₀).2 (Or.inl ha₀)) (h ▸ p.end_mem_support)
  have hb₀v : b₀ ≠ v := fun h => ((hpart b₀).2 (Or.inr hb₀)) (h ▸ p.end_mem_support)
  obtain ⟨w, hwv⟩ := (walk_induce_iff_exists_walk ha₀v hb₀v).1 (hv_conn.preconnected ⟨a₀, ha₀v⟩ ⟨b₀, hb₀v⟩)
  have hnotv_split : ∀ z, z ≠ v → z ∈ A ∨ z ∈ B ∨ z = u ∨ z = v₁ := fun z hzv => by
    by_cases hzp : z ∈ p.support
    · obtain ⟨i, hi, rfl⟩ := (mem_support_iff_getVert p z).1 hzp
      have : i = 0 ∨ i = 1 ∨ i = 2 := by omega
      rcases this with rfl | rfl | rfl
      · exact Or.inr (Or.inr (Or.inl (by simp)))
      · exact Or.inr (Or.inr (Or.inr rfl))
      · exact absurd (by rw [← hp2, p.getVert_length]) hzv
    · rcases (hpart z).1 hzp with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
  rcases hu_miss with humA | humB
  · let B' : Finset V := insert u (insert v₁ B)
    have hnoAB' : ∀ a ∈ A, ∀ b ∈ B', ¬ G.Adj a b := fun a ha b hb hab => by
      simp only [B', Finset.mem_insert] at hb
      rcases hb with rfl | rfl | hbB
      · exact humA a ha hab.symm
      · rcases hv₁_only a hab.symm with hau | hav
        · exact ((hpart a).2 (Or.inl ha)) (hau ▸ p.start_mem_support)
        · exact ((hpart a).2 (Or.inl ha)) (hav ▸ p.end_mem_support)
      · exact hnoAB a ha b hbB hab
    have hstay := walk_stay_in_part hnoAB' w ha₀ (fun z hz => by
      rcases hnotv_split z (hwv z hz) with h | h | rfl | rfl
      · exact Or.inl h
      · exact Or.inr (by simp [B', h])
      · exact Or.inr (by simp [B'])
      · exact Or.inr (by simp [B']))
    exact Finset.disjoint_left.1 hdAB (hstay b₀ w.end_mem_support) hb₀
  · let A' : Finset V := insert u (insert v₁ A)
    have hnoBA' : ∀ b ∈ B, ∀ a ∈ A', ¬ G.Adj b a := fun b hb a ha hba => by
      simp only [A', Finset.mem_insert] at ha
      rcases ha with rfl | rfl | haA
      · exact humB b hb hba.symm
      · rcases hv₁_only b hba.symm with hbu | hbv
        · exact ((hpart b).2 (Or.inr hb)) (hbu ▸ p.start_mem_support)
        · exact ((hpart b).2 (Or.inr hb)) (hbv ▸ p.end_mem_support)
      · exact hnoAB a haA b hb hba.symm
    have hstay := walk_stay_in_part hnoBA' w.reverse hb₀ (fun z hz => by
      rcases hnotv_split z (hwv z (by simpa using hz)) with h | h | rfl | rfl
      · exact Or.inr (by simp [A', h])
      · exact Or.inl h
      · exact Or.inr (by simp [A'])
      · exact Or.inr (by simp [A']))
    exact Finset.disjoint_left.1 hdAB ha₀ (hstay a₀ w.reverse.end_mem_support)

/-! ### Part 4: Minimal Disconnecting Geodesic Endpoint Universality -/

private lemma minimal_endpoint_touches_both [Fintype V] {G : SimpleGraph V}
    {u v : V} (p : G.Walk u v) (hp : p.IsPath) (hgeo : p.length = G.dist u v)
    (hlen : 1 ≤ p.length)
    (hmin : ∀ (u' v' : V) (q : G.Walk u' v'), q.IsPath → q.length = G.dist u' v' →
      q.length < p.length → (G.induce {x | x ∉ q.support}).Connected)
    {A B : Finset V} (hA : A.Nonempty) (hB : B.Nonempty)
    (hpart : ∀ x, x ∉ p.support ↔ x ∈ A ∨ x ∈ B) (hdAB : Disjoint A B)
    (hnoAB : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b) :
    (∃ a ∈ A, G.Adj u a) ∧ (∃ b ∈ B, G.Adj u b) ∧
    (∃ a ∈ A, G.Adj v a) ∧ (∃ b ∈ B, G.Adj v b) := by
  have hstart_gen : ∀ {x y : V} (r : G.Walk x y), r.IsPath → r.length = G.dist x y →
      1 ≤ r.length → r.length = p.length →
      (∀ z, z ∉ r.support ↔ z ∈ A ∨ z ∈ B) →
      (∃ a ∈ A, G.Adj x a) ∧ (∃ b ∈ B, G.Adj x b) := by
    intro x y r hr hrgeo hrlen hrpeq hrpart
    cases r with
    | nil => simp at hrlen
    | @cons _ x₂ _ h12 q =>
      have hq_path : q.IsPath := hr.of_cons
      have hq_geo : q.length = G.dist x₂ y := by
        have h := geodesic_dist_getVert (Walk.cons h12 q) hrgeo
          (show 1 ≤ (Walk.cons h12 q).length by omega) le_rfl
        simpa using h.symm
      have hq_conn := hmin x₂ y q hq_path hq_geo (by simp [← hrpeq])
      obtain ⟨a₀, ha₀⟩ := hA
      obtain ⟨b₀, hb₀⟩ := hB
      have ha₀q : a₀ ∉ q.support := fun h => ((hrpart a₀).2 (Or.inl ha₀)) (by simp [h])
      have hb₀q : b₀ ∉ q.support := fun h => ((hrpart b₀).2 (Or.inr hb₀)) (by simp [h])
      obtain ⟨w, hwq⟩ := (walk_induce_iff_exists_walk ha₀q hb₀q).1
        (hq_conn.preconnected ⟨a₀, ha₀q⟩ ⟨b₀, hb₀q⟩)
      have hx₁_in : x ∈ w.support := by
        by_contra hxn
        have hstay := walk_stay_in_part hnoAB w ha₀ (fun z hz => (hrpart z).1 (fun hzp => by
          rw [Walk.support_cons, List.mem_cons] at hzp
          rcases hzp with rfl | hzq
          · exact hxn hz
          · exact hwq z hz hzq))
        exact Finset.disjoint_left.1 hdAB (hstay b₀ w.end_mem_support) hb₀
      have hx₁A : x ∉ A := fun h => ((hrpart x).2 (Or.inl h)) (by simp)
      have hx₁B : x ∉ B := fun h => ((hrpart x).2 (Or.inr h)) (by simp)
      constructor
      · exact walk_enter_target_adj hnoAB hx₁A (w.takeUntil x hx₁_in) ha₀ (fun t ht htx =>
          (hrpart t).1 (by
            rw [Walk.support_cons, List.mem_cons]
            rintro (rfl | h)
            · exact htx rfl
            · exact hwq t (Walk.support_takeUntil_subset_support w hx₁_in ht) h))
      · have hx₁_in_rev : x ∈ w.reverse.support := by simpa using hx₁_in
        exact walk_enter_target_adj (fun b hb a ha h => hnoAB a ha b hb h.symm) hx₁B
          (w.reverse.takeUntil x hx₁_in_rev) hb₀ (fun t ht htx =>
            ((hrpart t).1 (by
              rw [Walk.support_cons, List.mem_cons]
              rintro (rfl | h)
              · exact htx rfl
              · exact hwq t (by simpa using Walk.support_takeUntil_subset_support w.reverse hx₁_in_rev ht) h)).symm)
  have hstart := hstart_gen p hp hgeo hlen rfl hpart
  have hend := hstart_gen p.reverse hp.reverse
    (by rw [Walk.length_reverse, SimpleGraph.dist_comm]; exact hgeo)
    (by simpa using hlen) (Walk.length_reverse p)
    (fun z => by simpa using hpart z)
  exact ⟨hstart.1, hstart.2, hend.1, hend.2⟩

/-! ### Part 5: ALL Finite Abelian Cayley Graphs -/


/-! ### Part 5: The Grand Antipode Block Theorem & Kernel-Disjointness Theorem -/

/-- Diameter of a finite simple graph via `Finset.sup`. -/
noncomputable def graphDiam [Fintype V] (G : SimpleGraph V) : ℕ :=
  Finset.univ.sup (fun p : V × V => G.dist p.1 p.2)

/-- The distance-`r` sphere around a vertex `x`. -/
def sphere (G : SimpleGraph V) (x : V) (r : ℕ) : Set V :=
  {y : V | G.dist x y = r}

private lemma dist_le_graphDiam [Fintype V] (G : SimpleGraph V) (x y : V) :
    G.dist x y ≤ graphDiam G :=
  Finset.le_sup (f := fun p : V × V => G.dist p.1 p.2) (Finset.mem_univ (x, y))

private lemma exists_antipode [Fintype V] {G : SimpleGraph V}
    (hconn : G.Connected) (hvt : IsVertexTransitive G) (x : V) :
    ∃ w : V, G.dist x w = graphDiam G := by
  have hne : (Finset.univ : Finset (V × V)).Nonempty := ⟨(x, x), Finset.mem_univ _⟩
  obtain ⟨⟨u₀, v₀⟩, _, hmax⟩ := Finset.exists_mem_eq_sup Finset.univ hne
    (fun p : V × V => G.dist p.1 p.2)
  obtain ⟨φ, hφ⟩ := hvt u₀ x
  refine ⟨φ v₀, ?_⟩
  rw [← hφ, iso_dist_eq φ hconn u₀ v₀, ← hmax]
  rfl

private lemma card_sphere_eq_of_vt [Fintype V] {G : SimpleGraph V}
    (hconn : G.Connected) (hvt : IsVertexTransitive G) (x y : V) (r : ℕ) :
    (Finset.univ.filter (fun z => G.dist x z = r)).card =
    (Finset.univ.filter (fun z => G.dist y z = r)).card := by
  obtain ⟨φ, hφ⟩ := hvt x y
  refine Finset.card_bij (fun z _ => φ z) ?_ ?_ ?_
  · intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    rw [← hφ, iso_dist_eq φ hconn x z, hz]
  · intro a _ b _ hab
    exact φ.injective hab
  · intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
    refine ⟨φ.symm w, ?_, φ.apply_symm_apply w⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have := iso_dist_eq φ hconn x (φ.symm w)
    rw [hφ, φ.apply_symm_apply] at this
    omega

private lemma card_ge_sphere_eq_of_vt [Fintype V] {G : SimpleGraph V}
    (hconn : G.Connected) (hvt : IsVertexTransitive G) (x y : V) (r : ℕ) :
    (Finset.univ.filter (fun z => r ≤ G.dist x z)).card =
    (Finset.univ.filter (fun z => r ≤ G.dist y z)).card := by
  obtain ⟨φ, hφ⟩ := hvt x y
  refine Finset.card_bij (fun z _ => φ z) ?_ ?_ ?_
  · intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    rw [← hφ, iso_dist_eq φ hconn x z]
    exact hz
  · intro a _ b _ hab
    exact φ.injective hab
  · intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
    refine ⟨φ.symm w, ?_, φ.apply_symm_apply w⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have := iso_dist_eq φ hconn x (φ.symm w)
    rw [hφ, φ.apply_symm_apply] at this
    omega

private lemma exists_min_component_split [Fintype V] {G : SimpleGraph V} {S : Set V}
    (hSne : S.Nonempty) (hnot : ¬ (G.induce S).Connected) :
    ∃ A B : Finset V, A.Nonempty ∧ B.Nonempty ∧
      (G.induce (A : Set V)).Connected ∧
      (∀ x, x ∈ S ↔ x ∈ A ∨ x ∈ B) ∧
      Disjoint A B ∧
      (∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b) ∧
      (∀ K : Finset V, K.Nonempty → (∀ y ∈ K, y ∈ S) →
        (∀ y ∈ K, ∀ z, z ∈ S → G.Adj y z → z ∈ K) → A.card ≤ K.card) := by
  let Sfin : Finset V := Finset.univ.filter (· ∈ S)
  have hSfin_ne : Sfin.Nonempty := by
    obtain ⟨x, hx⟩ := hSne
    exact ⟨x, by simp [Sfin, hx]⟩
  let compOf : V → Finset V := fun x =>
    Finset.univ.filter (fun y => ∃ (hx : x ∈ S) (hy : y ∈ S), (G.induce S).Reachable ⟨x, hx⟩ ⟨y, hy⟩)
  obtain ⟨a₀, ha₀_mem, ha₀_min⟩ := Finset.exists_min_image Sfin (fun x => (compOf x).card) hSfin_ne
  have ha₀ : a₀ ∈ S := by simpa [Sfin] using ha₀_mem
  let A : Finset V := compOf a₀
  let B : Finset V := Finset.univ.filter (fun x => x ∈ S ∧ x ∉ A)
  have ha₀A : a₀ ∈ A := by
    simp [A, compOf, ha₀]
  have hAS : ∀ x ∈ A, x ∈ S := by
    intro x hx
    simp only [A, compOf, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    exact hx.2.1
  have hBne : B.Nonempty := by
    by_contra hBe
    rw [Finset.not_nonempty_iff_eq_empty] at hBe
    apply hnot
    refine induce_connected_of_base ha₀ (fun x hx => ?_)
    have hxA : x ∈ A := by
      by_contra hxnA
      have : x ∈ B := by simp [B, hx, hxnA]
      rw [hBe] at this
      exact Finset.notMem_empty x this
    simp only [A, compOf, Finset.mem_filter, Finset.mem_univ, true_and] at hxA
    exact hxA.2.2.symm
  have hAconn : (G.induce (A : Set V)).Connected := by
    refine induce_connected_of_base (show a₀ ∈ (A : Set V) from ha₀A) ?_
    intro x hx
    have hx' : x ∈ A := hx
    simp only [A, compOf, Finset.mem_filter, Finset.mem_univ, true_and] at hx'
    obtain ⟨_, hxS, hr⟩ := hx'
    obtain ⟨w, hwS⟩ := (walk_induce_iff_exists_walk ha₀ hxS).1 hr
    have hwA : ∀ z ∈ w.support, z ∈ (A : Set V) := by
      intro z hz
      have hzS : z ∈ S := hwS z hz
      have hreach_z : (G.induce S).Reachable ⟨a₀, ha₀⟩ ⟨z, hzS⟩ := by
        rw [walk_induce_iff_exists_walk]
        refine ⟨w.takeUntil z hz, fun t ht => hwS t (Walk.support_takeUntil_subset_support w hz ht)⟩
      change z ∈ A
      simp [A, compOf, ha₀, hzS, hreach_z]
    exact (walk_induce_iff_exists_walk hx (show a₀ ∈ (A : Set V) from ha₀A)).2
      ⟨w.reverse, fun z hz => hwA z (by simpa using hz)⟩
  have hpart : ∀ x, x ∈ S ↔ x ∈ A ∨ x ∈ B := by
    intro x
    constructor
    · intro hxS
      by_cases hxA : x ∈ A
      · exact Or.inl hxA
      · exact Or.inr (by simp [B, hxS, hxA])
    · rintro (hxA | hxB)
      · exact hAS x hxA
      · simp only [B, Finset.mem_filter, Finset.mem_univ, true_and] at hxB
        exact hxB.1
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro x hxA hxB
    simp only [B, Finset.mem_filter, Finset.mem_univ, true_and] at hxB
    exact hxB.2 hxA
  have hno : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b := by
    intro a haA b hbB hab
    simp only [A, compOf, Finset.mem_filter, Finset.mem_univ, true_and] at haA
    simp only [B, Finset.mem_filter, Finset.mem_univ, true_and] at hbB
    have hrb : (G.induce S).Reachable ⟨a₀, ha₀⟩ ⟨b, hbB.1⟩ :=
      haA.2.2.trans (Adj.reachable (show (G.induce S).Adj ⟨a, haA.2.1⟩ ⟨b, hbB.1⟩ from hab))
    exact hbB.2 (by simp [A, compOf, ha₀, hbB.1, hrb])
  have hminK : ∀ K : Finset V, K.Nonempty → (∀ y ∈ K, y ∈ S) →
      (∀ y ∈ K, ∀ z, z ∈ S → G.Adj y z → z ∈ K) → A.card ≤ K.card := by
    intro K hKne hKS hKclosed
    obtain ⟨y₀, hy₀K⟩ := hKne
    have hy₀S : y₀ ∈ S := hKS y₀ hy₀K
    have hsub : compOf y₀ ⊆ K := by
      intro z hz
      simp only [compOf, Finset.mem_filter, Finset.mem_univ, true_and] at hz
      obtain ⟨_, hzS, hr⟩ := hz
      obtain ⟨w, hwS⟩ := (walk_induce_iff_exists_walk hy₀S hzS).1 hr
      have hstay : ∀ {x₁ x₂ : V} (q : G.Walk x₁ x₂), x₁ ∈ K → (∀ t ∈ q.support, t ∈ S) → x₂ ∈ K := by
        intro x₁ x₂ q
        induction q with
        | nil => intro hx₁ _; exact hx₁
        | @cons a b c hab q' ih =>
          intro haK hqS
          have hbS : b ∈ S := hqS b (by simp)
          have hbK : b ∈ K := hKclosed a haK b hbS hab
          exact ih hbK (fun t ht => hqS t (by simp [ht]))
      exact hstay w hy₀K hwS
    exact (ha₀_min y₀ (by simp [Sfin, hy₀S])).trans (Finset.card_le_card hsub)
  exact ⟨A, B, ⟨a₀, ha₀A⟩, hBne, hAconn, hpart, hdisj, hno, hminK⟩

/-- If `G - φ(P)` has a nonempty connected subset `H` whose complement in `G - φ(P)` has
size `< A.card`, we contradict minimality of `A`. -/
private lemma absurd_of_large_connected_in_image [Fintype V] {G : SimpleGraph V}
    {S : Set V} (hnot : ¬ (G.induce S).Connected)
    {A : Finset V}
    (hminK : ∀ K : Finset V, K.Nonempty → (∀ y ∈ K, y ∈ S) →
      (∀ y ∈ K, ∀ z, z ∈ S → G.Adj y z → z ∈ K) → A.card ≤ K.card)
    (φ : G ≃g G) {T : Set V} (hST : ∀ x, x ∈ S ↔ φ x ∈ T)
    {r : V} (hrT : r ∈ T) {H : Finset V}
    (hHreach : ∀ x ∈ H, ∃ hx : x ∈ T, (G.induce T).Reachable ⟨r, hrT⟩ ⟨x, hx⟩)
    (hcomp_lt : (Finset.univ.filter (fun x => x ∈ T ∧ x ∉ H)).card < A.card) : False := by
  let K : Finset V := Finset.univ.filter (fun x =>
    ∃ hx : x ∈ T, ¬ (G.induce T).Reachable ⟨r, hrT⟩ ⟨x, hx⟩)
  have hKne : K.Nonempty := by
    by_contra hKe
    rw [Finset.not_nonempty_iff_eq_empty] at hKe
    have hTconn : (G.induce T).Connected := by
      refine induce_connected_of_base hrT (fun x hx => ?_)
      by_contra hnr
      have : x ∈ K := by
        simp only [K, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hx, fun h => hnr h.symm⟩
      rw [hKe] at this
      exact Finset.notMem_empty x this
    have hSconn : (G.induce S).Connected :=
      induce_connected_of_iso φ.symm (fun x => by
        have := hST (φ.symm x)
        rw [φ.apply_symm_apply] at this
        exact this.symm) hTconn
    exact hnot hSconn
  have hKsub : K ⊆ Finset.univ.filter (fun x => x ∈ T ∧ x ∉ H) := by
    intro x hx
    simp only [K, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    obtain ⟨hxT, hnr⟩ := hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨hxT, fun hxH => ?_⟩
    obtain ⟨_, hr⟩ := hHreach x hxH
    exact hnr hr
  let Kpre : Finset V := K.image φ.symm
  have hKpre_ne : Kpre.Nonempty := hKne.image _
  have hKpre_S : ∀ y ∈ Kpre, y ∈ S := by
    intro y hy
    obtain ⟨x, hxK, rfl⟩ := Finset.mem_image.1 hy
    simp only [K, Finset.mem_filter, Finset.mem_univ, true_and] at hxK
    exact (hST (φ.symm x)).2 (by simpa using hxK.1)
  have hKpre_closed : ∀ y ∈ Kpre, ∀ z, z ∈ S → G.Adj y z → z ∈ Kpre := by
    intro y hy z hzS hyz
    obtain ⟨x, hxK, rfl⟩ := Finset.mem_image.1 hy
    simp only [K, Finset.mem_filter, Finset.mem_univ, true_and] at hxK
    have hφzT : φ z ∈ T := (hST z).1 hzS
    have hφzK : φ z ∈ K := by
      simp only [K, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨hφzT, fun hrz => hxK.2 ?_⟩
      have hadj : G.Adj (φ z) x := by
        have := φ.map_rel_iff.2 hyz.symm
        simpa using this
      exact hrz.trans (Adj.reachable (show (G.induce T).Adj ⟨φ z, hφzT⟩ ⟨x, hxK.1⟩ from hadj))
    exact Finset.mem_image.2 ⟨φ z, hφzK, φ.symm_apply_apply z⟩
  have hcard_eq : Kpre.card = K.card := Finset.card_image_of_injective K φ.symm.injective
  have hge := hminK Kpre hKpre_ne hKpre_S hKpre_closed
  have hle := Finset.card_le_card hKsub
  omega

/-- Every finite connected VT graph with `3 ≤ |V|` and `3 ≤ deg` has connectivity `≥ 3`:
no cut of size `≤ 2` can separate two nonempty disjoint vertex sets with no edges between them. -/
private lemma vt_no_two_cut [Fintype V] {G : SimpleGraph V}
    (hconn : G.Connected) (hvt : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V)
    (hdeg3 : ∀ v : V, 3 ≤ G.degree v)
    {X Y S : Finset V} (hX : X.Nonempty) (hY : Y.Nonempty) (hXY : Disjoint X Y)
    (hXS : Disjoint X S) (hYS : Disjoint Y S)
    (hno : ∀ x ∈ X, ∀ y ∈ Y, ¬ G.Adj x y)
    (hbdry : ∀ x ∈ X, ∀ z, G.Adj x z → z ∈ X ∨ z ∈ S)
    (hSle : S.card ≤ 2) : False := by
  let N : Finset V := Finset.univ.filter (fun z => z ∉ X ∧ ∃ x ∈ X, G.Adj x z)
  have hNsub : N ⊆ S := by
    intro z hz
    simp only [N, Finset.mem_filter, Finset.mem_univ, true_and] at hz
    obtain ⟨hznX, x, hxX, hxz⟩ := hz
    exact (hbdry x hxX z hxz).resolve_left hznX
  have hNsep : ¬ (G.induce {z | z ∉ (N : Set V)}).Connected :=
    sep_of_boundary hX hY hXY hno
  have hNle : N.card ≤ 2 := (Finset.card_le_card hNsub).trans hSle
  have hdeg_le := watkins_deg_le_cut_of_le_three hconn hvt hcard (by omega) hNsep
  obtain ⟨x, _⟩ := hX
  have := hdeg3 x
  have := hdeg_le x
  omega

/-- Every connected component of `G - P` inside `B` touches both endpoints `u, v` and has
at least 3 neighbors in `P`. -/
private lemma comp_in_B_props [Fintype V] {G : SimpleGraph V}
    (hconn : G.Connected) (hvt : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V)
    (hdeg3 : ∀ v : V, 3 ≤ G.degree v)
    {u v : V} (p : G.Walk u v) (hp : p.IsPath) (hgeo : p.length = G.dist u v)
    (hlen : 2 ≤ p.length)
    (hmin : ∀ (u' v' : V) (q : G.Walk u' v'), q.IsPath → q.length = G.dist u' v' →
      q.length < p.length → (G.induce {x | x ∉ q.support}).Connected)
    {A B : Finset V} (hA : A.Nonempty)
    (hpart : ∀ x, x ∉ p.support ↔ x ∈ A ∨ x ∈ B) (hdAB : Disjoint A B)
    (hnoAB : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b)
    {C : Finset V} (hCne : C.Nonempty) (hCsub : C ⊆ B)
    (hCclosed : ∀ x ∈ C, ∀ y ∈ B, G.Adj x y → y ∈ C) :
    (∃ c ∈ C, G.Adj u c) ∧ (∃ c ∈ C, G.Adj v c) ∧
    3 ≤ (Finset.univ.filter (fun z => z ∈ p.support ∧ ∃ c ∈ C, G.Adj c z)).card := by
  let R : Finset V := Finset.univ.filter (fun x => x ∉ p.support ∧ x ∉ C)
  have hRne : R.Nonempty := by
    obtain ⟨a, ha⟩ := hA
    have haP : a ∉ p.support := (hpart a).2 (Or.inl ha)
    have haC : a ∉ C := fun h => Finset.disjoint_left.1 hdAB ha (hCsub h)
    exact ⟨a, by simp [R, haP, haC]⟩
  have hpartCR : ∀ x, x ∉ p.support ↔ x ∈ C ∨ x ∈ R := by
    intro x
    constructor
    · intro hxP
      by_cases hxC : x ∈ C
      · exact Or.inl hxC
      · exact Or.inr (by simp [R, hxP, hxC])
    · rintro (hxC | hxR)
      · exact (hpart x).2 (Or.inr (hCsub hxC))
      · simp only [R, Finset.mem_filter, Finset.mem_univ, true_and] at hxR
        exact hxR.1
  have hdCR : Disjoint C R := by
    rw [Finset.disjoint_left]
    intro x hxC hxR
    simp only [R, Finset.mem_filter, Finset.mem_univ, true_and] at hxR
    exact hxR.2 hxC
  have hnoCR : ∀ c ∈ C, ∀ r ∈ R, ¬ G.Adj c r := by
    intro c hcC r hrR hcr
    simp only [R, Finset.mem_filter, Finset.mem_univ, true_and] at hrR
    rcases (hpart r).1 hrR.1 with hrA | hrB
    · exact hnoAB r hrA c (hCsub hcC) hcr.symm
    · exact hrR.2 (hCclosed c hcC r hrB hcr)
  have ht := minimal_endpoint_touches_both p hp hgeo (by omega) hmin hCne hRne hpartCR hdCR hnoCR
  refine ⟨ht.1, ht.2.2.1, ?_⟩
  let N : Finset V := Finset.univ.filter (fun z => z ∈ p.support ∧ ∃ c ∈ C, G.Adj c z)
  by_contra hlt
  have hNle : N.card ≤ 2 := by dsimp only [N] at *; omega
  have hdisjCA : Disjoint C A := Disjoint.mono_left hCsub hdAB.symm
  have hdisjCN : Disjoint C N := by
    rw [Finset.disjoint_left]
    intro x hxC hxN
    simp only [N, Finset.mem_filter, Finset.mem_univ, true_and] at hxN
    exact ((hpart x).2 (Or.inr (hCsub hxC))) hxN.1
  have hdisjAN : Disjoint A N := by
    rw [Finset.disjoint_left]
    intro x hxA hxN
    simp only [N, Finset.mem_filter, Finset.mem_univ, true_and] at hxN
    exact ((hpart x).2 (Or.inl hxA)) hxN.1
  have hnoCA : ∀ c ∈ C, ∀ a ∈ A, ¬ G.Adj c a := fun c hc a ha h => hnoAB a ha c (hCsub hc) h.symm
  have hbdry : ∀ c ∈ C, ∀ z, G.Adj c z → z ∈ C ∨ z ∈ N := by
    intro c hc z hcz
    by_cases hzP : z ∈ p.support
    · exact Or.inr (by simp only [N, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hzP, c, hc, hcz⟩)
    · rcases (hpart z).1 hzP with hzA | hzB
      · exact absurd hcz (hnoCA c hc z hzA)
      · exact Or.inl (hCclosed c hc z hzB hcz)
  exact vt_no_two_cut hconn hvt hcard hdeg3 hCne hA hdisjCA hdisjCN hdisjAN hnoCA hbdry hNle

/-- Step 2 (Exact No-Nesting Small-Intersection Lemma):
If `φ(P) ⊆ A ∪ P`, then `|P ∩ φ(P)| ≥ 3`. -/
private lemma no_nesting_inter_ge_three [Fintype V] {G : SimpleGraph V}
    (hconn : G.Connected) (hvt : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V)
    (hdeg3 : ∀ v : V, 3 ≤ G.degree v)
    {u v : V} (p : G.Walk u v) (hp : p.IsPath) (hgeo : p.length = G.dist u v)
    (hlen : 2 ≤ p.length)
    (hnot : ¬ (G.induce {x | x ∉ p.support}).Connected)
    (hmin : ∀ (u' v' : V) (q : G.Walk u' v'), q.IsPath → q.length = G.dist u' v' →
      q.length < p.length → (G.induce {x | x ∉ q.support}).Connected)
    {A B : Finset V} (hA : A.Nonempty) (hB : B.Nonempty)
    (hpart : ∀ x, x ∉ p.support ↔ x ∈ A ∨ x ∈ B) (hdAB : Disjoint A B)
    (hnoAB : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b)
    (hminK : ∀ K : Finset V, K.Nonempty → (∀ y ∈ K, y ∉ p.support) →
      (∀ y ∈ K, ∀ z, z ∉ p.support → G.Adj y z → z ∈ K) → A.card ≤ K.card)
    (φ : G ≃g G)
    (hsub : ∀ x ∈ p.support, φ x ∈ A ∨ φ x ∈ p.support) :
    3 ≤ (Finset.univ.filter (fun z => z ∈ p.support ∧ φ.symm z ∈ p.support)).card := by
  by_contra hlt
  have hle2 : (Finset.univ.filter (fun z => z ∈ p.support ∧ φ.symm z ∈ p.support)).card ≤ 2 := by omega
  let T : Set V := {x | φ.symm x ∉ p.support}
  have hST : ∀ x, x ∉ p.support ↔ φ x ∈ T := fun x => by simp [T]
  have hB_in_T : ∀ b ∈ B, b ∈ T := by
    intro b hb hmem
    have := hsub (φ.symm b) hmem
    rw [φ.apply_symm_apply] at this
    rcases this with hbA | hbP
    · exact Finset.disjoint_left.1 hdAB hbA hb
    · exact ((hpart b).2 (Or.inr hb)) hbP
  have hB_comp_reach : ∀ b (hb : b ∈ B) w (hw : w ∈ B), (G.induce (B : Set V)).Reachable ⟨b, hb⟩ ⟨w, hw⟩ →
      (G.induce T).Reachable ⟨b, hB_in_T b hb⟩ ⟨w, hB_in_T w hw⟩ := by
    intro b hb w hw hr
    obtain ⟨q, hqB⟩ := (walk_induce_iff_exists_walk hb hw).1 hr
    exact (walk_induce_iff_exists_walk (hB_in_T b hb) (hB_in_T w hw)).2 ⟨q, fun z hz => hB_in_T z (hqB z hz)⟩
  -- Find a vertex v* ∈ P \ φ(P) such that every b ∈ B reaches v* in G[T].
  have hex_anchor : ∃ vstar : V, vstar ∈ p.support ∧ ∃ hvT : vstar ∈ T,
      ∀ b (hb : b ∈ B), (G.induce T).Reachable ⟨vstar, hvT⟩ ⟨b, hB_in_T b hb⟩ := by
    by_cases huT : u ∈ T
    · refine ⟨u, p.start_mem_support, huT, fun b hb => ?_⟩
      let C : Finset V := Finset.univ.filter (fun x => ∃ hx : x ∈ B, (G.induce (B : Set V)).Reachable ⟨b, hb⟩ ⟨x, hx⟩)
      have hCne : C.Nonempty := ⟨b, by simp [C, hb]⟩
      have hCsub : C ⊆ B := fun x hx => by
        simp only [C, Finset.mem_filter, Finset.mem_univ, true_and] at hx; exact hx.1
      have hCclosed : ∀ x ∈ C, ∀ y ∈ B, G.Adj x y → y ∈ C := by
        intro x hx y hy hxy
        simp only [C, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
        exact ⟨hy, hx.2.trans (Adj.reachable (show (G.induce (B : Set V)).Adj ⟨x, hx.1⟩ ⟨y, hy⟩ from hxy))⟩
      obtain ⟨⟨c, hcC, huc⟩, _, _⟩ := comp_in_B_props hconn hvt hcard hdeg3 p hp hgeo hlen hmin hA hpart hdAB hnoAB hCne hCsub hCclosed
      have hcB : c ∈ B := hCsub hcC
      simp only [C, Finset.mem_filter, Finset.mem_univ, true_and] at hcC
      have hrcb := hB_comp_reach b hb c hcB hcC.2
      exact (Adj.reachable (show (G.induce T).Adj ⟨u, huT⟩ ⟨c, hB_in_T c hcB⟩ from huc)).trans hrcb.symm
    · by_cases hvT : v ∈ T
      · refine ⟨v, p.end_mem_support, hvT, fun b hb => ?_⟩
        let C : Finset V := Finset.univ.filter (fun x => ∃ hx : x ∈ B, (G.induce (B : Set V)).Reachable ⟨b, hb⟩ ⟨x, hx⟩)
        have hCne : C.Nonempty := ⟨b, by simp [C, hb]⟩
        have hCsub : C ⊆ B := fun x hx => by
          simp only [C, Finset.mem_filter, Finset.mem_univ, true_and] at hx; exact hx.1
        have hCclosed : ∀ x ∈ C, ∀ y ∈ B, G.Adj x y → y ∈ C := by
          intro x hx y hy hxy
          simp only [C, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
          exact ⟨hy, hx.2.trans (Adj.reachable (show (G.induce (B : Set V)).Adj ⟨x, hx.1⟩ ⟨y, hy⟩ from hxy))⟩
        obtain ⟨_, ⟨c, hcC, hvc⟩, _⟩ := comp_in_B_props hconn hvt hcard hdeg3 p hp hgeo hlen hmin hA hpart hdAB hnoAB hCne hCsub hCclosed
        have hcB : c ∈ B := hCsub hcC
        simp only [C, Finset.mem_filter, Finset.mem_univ, true_and] at hcC
        have hrcb := hB_comp_reach b hb c hcB hcC.2
        exact (Adj.reachable (show (G.induce T).Adj ⟨v, hvT⟩ ⟨c, hB_in_T c hcB⟩ from hvc)).trans hrcb.symm
      · -- Both u and v lie in P ∩ φ(P). Since |P ∩ φ(P)| ≤ 2 and u ≠ v, P ∩ φ(P) = {u, v}!
        have huv : u ≠ v := by
          intro h
          have hd0 : G.dist u v = 0 := by rw [h, SimpleGraph.dist_self]
          omega
        have huI : u ∈ Finset.univ.filter (fun z => z ∈ p.support ∧ φ.symm z ∈ p.support) := by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨p.start_mem_support, not_not.1 huT⟩
        have hvI : v ∈ Finset.univ.filter (fun z => z ∈ p.support ∧ φ.symm z ∈ p.support) := by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨p.end_mem_support, not_not.1 hvT⟩
        have hIeq : Finset.univ.filter (fun z => z ∈ p.support ∧ φ.symm z ∈ p.support) = {u, v} := by
          have hsub_pair : ({u, v} : Finset V) ⊆ Finset.univ.filter (fun z => z ∈ p.support ∧ φ.symm z ∈ p.support) := by
            intro z hz
            simp only [Finset.mem_insert, Finset.mem_singleton] at hz
            rcases hz with rfl | rfl <;> assumption
          exact (Finset.eq_of_subset_of_card_le hsub_pair (by rw [Finset.card_pair huv]; exact hle2)).symm
        have hmid_in_T : ∀ i, 1 ≤ i → i ≤ p.length - 1 → p.getVert i ∈ T := by
          intro i hi1 hi2 hmem
          have hmemI : p.getVert i ∈ Finset.univ.filter (fun z => z ∈ p.support ∧ φ.symm z ∈ p.support) := by
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨p.getVert_mem_support i, hmem⟩
          rw [hIeq, Finset.mem_insert, Finset.mem_singleton] at hmemI
          rcases hmemI with hiu | hiv
          · have hd := geodesic_dist_getVert p hgeo (Nat.zero_le i) (by omega)
            rw [Walk.getVert_zero, hiu, SimpleGraph.dist_self] at hd
            omega
          · have hd := geodesic_dist_getVert p hgeo (show i ≤ p.length by omega) le_rfl
            rw [Walk.getVert_length, hiv, SimpleGraph.dist_self] at hd
            omega
        have hv1T : p.getVert 1 ∈ T := hmid_in_T 1 le_rfl (by omega)
        have hmid_reach : ∀ i (hi1 : 1 ≤ i) (hi2 : i ≤ p.length - 1),
            (G.induce T).Reachable ⟨p.getVert 1, hv1T⟩ ⟨p.getVert i, hmid_in_T i hi1 hi2⟩ := by
          intro i hi1 hi2
          induction i with
          | zero => omega
          | succ k ih =>
            by_cases hk0 : k = 0
            · subst hk0; exact Reachable.refl _
            · have hk1 : 1 ≤ k := by omega
              have hk2 : k ≤ p.length - 1 := by omega
              have hadj : G.Adj (p.getVert k) (p.getVert (k + 1)) := p.adj_getVert_succ (by omega)
              exact (ih hk1 hk2).trans (Adj.reachable (show (G.induce T).Adj ⟨p.getVert k, hmid_in_T k hk1 hk2⟩
                ⟨p.getVert (k + 1), hmid_in_T (k + 1) hi1 hi2⟩ from hadj))
        refine ⟨p.getVert 1, p.getVert_mem_support 1, hv1T, fun b hb => ?_⟩
        let C : Finset V := Finset.univ.filter (fun x => ∃ hx : x ∈ B, (G.induce (B : Set V)).Reachable ⟨b, hb⟩ ⟨x, hx⟩)
        have hCne : C.Nonempty := ⟨b, by simp [C, hb]⟩
        have hCsub : C ⊆ B := fun x hx => by
          simp only [C, Finset.mem_filter, Finset.mem_univ, true_and] at hx; exact hx.1
        have hCclosed : ∀ x ∈ C, ∀ y ∈ B, G.Adj x y → y ∈ C := by
          intro x hx y hy hxy
          simp only [C, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
          exact ⟨hy, hx.2.trans (Adj.reachable (show (G.induce (B : Set V)).Adj ⟨x, hx.1⟩ ⟨y, hy⟩ from hxy))⟩
        obtain ⟨_, _, hN3⟩ := comp_in_B_props hconn hvt hcard hdeg3 p hp hgeo hlen hmin hA hpart hdAB hnoAB hCne hCsub hCclosed
        -- Since |N_P(C)| ≥ 3 > 2 = |{u, v}|, ∃ z ∈ N_P(C) with z ∉ {u, v}
        have hex_z : ∃ z ∈ Finset.univ.filter (fun z => z ∈ p.support ∧ ∃ c ∈ C, G.Adj c z), z ∉ ({u, v} : Finset V) := by
          by_contra hall
          push Not at hall
          have hc := Finset.card_le_card hall
          rw [Finset.card_pair huv] at hc
          omega
        obtain ⟨z, hzN, hzuv⟩ := hex_z
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hzN
        obtain ⟨hzP, c, hcC, hcz⟩ := hzN
        obtain ⟨i, hiL, rfl⟩ := (mem_support_iff_getVert p z).1 hzP
        have hi1 : 1 ≤ i := by
          by_contra h0
          have hi0 : i = 0 := by omega
          subst hi0
          exact hzuv (by simp)
        have hi2 : i ≤ p.length - 1 := by
          by_contra hL
          have hiEq : i = p.length := by omega
          subst hiEq
          exact hzuv (by simp)
        have hcB : c ∈ B := hCsub hcC
        simp only [C, Finset.mem_filter, Finset.mem_univ, true_and] at hcC
        have hrcb := hB_comp_reach b hb c hcB hcC.2
        exact (hmid_reach i hi1 hi2).trans
          ((Adj.reachable (show (G.induce T).Adj ⟨p.getVert i, hmid_in_T i hi1 hi2⟩ ⟨c, hB_in_T c hcB⟩ from hcz.symm)).trans hrcb.symm)
  obtain ⟨vstar, hvstarP, hvstarT, hvstar_reach⟩ := hex_anchor
  let H : Finset V := insert vstar B
  have hvstar_notB : vstar ∉ B := fun h => ((hpart vstar).2 (Or.inr h)) hvstarP
  have hHcard : H.card = B.card + 1 := Finset.card_insert_of_notMem hvstar_notB
  have hHreach : ∀ x ∈ H, ∃ hx : x ∈ T, (G.induce T).Reachable ⟨vstar, hvstarT⟩ ⟨x, hx⟩ := by
    intro x hx
    rw [Finset.mem_insert] at hx
    rcases hx with rfl | hxB
    · exact ⟨hvstarT, Reachable.refl _⟩
    · exact ⟨hB_in_T x hxB, hvstar_reach x hxB⟩
  have hHsubT : H ⊆ Finset.univ.filter (· ∈ T) := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (hHreach x hx).1
  have hTcard : (Finset.univ.filter (· ∈ T)).card = A.card + B.card := by
    have h1 : (Finset.univ.filter (· ∈ T)).card = (Finset.univ.filter (fun x => x ∉ p.support)).card := by
      refine Finset.card_bij (fun x _ => φ.symm x) ?_ ?_ ?_
      · intro x hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, T] at hx ⊢
        exact hx
      · intro a _ b _ hab; exact φ.symm.injective hab
      · intro y hy
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
        exact ⟨φ y, by simp [T, hy], φ.symm_apply_apply y⟩
    have h2 : Finset.univ.filter (fun x => x ∉ p.support) = A ∪ B := by
      ext x; simp [hpart x]
    rw [h1, h2, Finset.card_union_of_disjoint hdAB]
  have hcomp_eq : Finset.univ.filter (fun x => x ∈ T ∧ x ∉ H) = (Finset.univ.filter (· ∈ T)) \ H := by
    ext x; simp
  have hcomp_lt : (Finset.univ.filter (fun x => x ∈ T ∧ x ∉ H)).card < A.card := by
    have hadd := Finset.card_sdiff_add_card_eq_card hHsubT
    rw [← hcomp_eq, hTcard, hHcard] at hadd
    omega
  exact absurd_of_large_connected_in_image hnot hminK φ hST hvstarT hHreach (by convert hcomp_lt)

/-- Any walk from `a ∈ A` to `b ∈ B` hits `P`, so `G.dist a b` passes through some `v_j ∈ P`. -/
private lemma exists_hit_P_on_geodesic [Fintype V] {G : SimpleGraph V}
    (hconn : G.Connected) {u v : V} (p : G.Walk u v)
    {A B : Finset V} (hpart : ∀ x, x ∉ p.support ↔ x ∈ A ∨ x ∈ B)
    (hdAB : Disjoint A B) (hnoAB : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b)
    {a z : V} (ha : a ∈ A) (hz : z ∉ A) :
    ∃ j ≤ p.length, G.dist a z = G.dist a (p.getVert j) + G.dist (p.getVert j) z := by
  obtain ⟨w, hw⟩ := (hconn a z).exists_walk_length_eq_dist
  have hhit : ∃ x ∈ w.support, x ∈ p.support := by
    by_contra hno
    push Not at hno
    have hstay := walk_stay_in_part hnoAB w ha (fun t ht => (hpart t).1 (hno t ht))
    exact hz (hstay z w.end_mem_support)
  obtain ⟨x, hxw, hxp⟩ := hhit
  obtain ⟨j, hjL, rfl⟩ := (mem_support_iff_getVert p x).1 hxp
  refine ⟨j, hjL, ?_⟩
  have hsplit : (w.takeUntil (p.getVert j) hxw).length + (w.dropUntil (p.getVert j) hxw).length = w.length := by
    rw [← Walk.length_append, Walk.take_spec]
  have h1 : G.dist a (p.getVert j) ≤ (w.takeUntil (p.getVert j) hxw).length := G.dist_le _
  have h2 : G.dist (p.getVert j) z ≤ (w.dropUntil (p.getVert j) hxw).length := G.dist_le _
  have htri := dist_triangle_of_reachable (hconn a (p.getVert j)) (hconn (p.getVert j) z)
  omega

/-- Step 3 (Midpoint Distance Bound):
For `m = L / 2`, EVERY `x ∈ A ∪ P` satisfies `G.dist (p.getVert m) x ≤ L - 1`. -/
private lemma midpoint_dist_lt_length [Fintype V] {G : SimpleGraph V}
    (hconn : G.Connected) (hvt : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V)
    (hdeg3 : ∀ v : V, 3 ≤ G.degree v)
    {u v : V} (p : G.Walk u v) (hp : p.IsPath) (hgeo : p.length = G.dist u v)
    (hlen : 2 ≤ p.length)
    (hnot : ¬ (G.induce {x | x ∉ p.support}).Connected)
    (hmin : ∀ (u' v' : V) (q : G.Walk u' v'), q.IsPath → q.length = G.dist u' v' →
      q.length < p.length → (G.induce {x | x ∉ q.support}).Connected)
    {A B : Finset V} (hA : A.Nonempty) (hB : B.Nonempty)
    (hpart : ∀ x, x ∉ p.support ↔ x ∈ A ∨ x ∈ B) (hdAB : Disjoint A B)
    (hnoAB : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b)
    (hminK : ∀ K : Finset V, K.Nonempty → (∀ y ∈ K, y ∉ p.support) →
      (∀ y ∈ K, ∀ z, z ∉ p.support → G.Adj y z → z ∈ K) → A.card ≤ K.card) :
    let m := p.length / 2
    ∀ x : V, (x ∈ A ∨ x ∈ p.support) → G.dist (p.getVert m) x < p.length := by
  intro m a hx
  rcases hx with ha | hxP
  · -- a ∈ A
    by_contra hge
    push Not at hge
    have hm_le : m ≤ p.length := Nat.div_le_self _ _
    have hdist_P : ∀ j ≤ p.length, p.length ≤ G.dist a (p.getVert j) + (if j ≤ m then m - j else j - m) := by
      intro j hjL
      have htri := dist_triangle_of_reachable (hconn (p.getVert m) (p.getVert j)) (hconn (p.getVert j) a)
      have hmj : G.dist (p.getVert m) (p.getVert j) = if j ≤ m then m - j else j - m := by
        split_ifs with hjm
        · rw [SimpleGraph.dist_comm]; exact geodesic_dist_getVert p hgeo hjm hm_le
        · exact geodesic_dist_getVert p hgeo (by omega) hjL
      rw [hmj, SimpleGraph.dist_comm (u := p.getVert j) (v := a)] at htri
      omega
    obtain ⟨φ, hφ⟩ := hvt (p.getVert m) a
    have hφ_dist : ∀ i ≤ p.length, G.dist a (φ (p.getVert i)) = if i ≤ m then m - i else i - m := by
      intro i hiL
      rw [← hφ, iso_dist_eq φ hconn]
      split_ifs with him
      · rw [SimpleGraph.dist_comm]; exact geodesic_dist_getVert p hgeo him hm_le
      · exact geodesic_dist_getVert p hgeo (by omega) hiL
    -- Distance from a to any vertex of B is strictly larger than min_{j} d(a, v_j)
    have hdist_B : ∀ b ∈ B, ∃ j ≤ p.length, G.dist a (p.getVert j) + 1 ≤ G.dist a b := by
      intro b hb
      have hb_notA : b ∉ A := fun h => Finset.disjoint_left.1 hdAB h hb
      obtain ⟨j, hjL, heq⟩ := exists_hit_P_on_geodesic hconn p hpart hdAB hnoAB ha hb_notA
      have hne : p.getVert j ≠ b := fun h => ((hpart b).2 (Or.inr hb)) (h ▸ p.getVert_mem_support j)
      have hpos : 1 ≤ G.dist (p.getVert j) b := by
        by_contra h0
        have h0' : G.dist (p.getVert j) b = 0 := by omega
        exact hne ((SimpleGraph.dist_eq_zero_iff_eq_or_not_reachable.1 h0').resolve_right (not_not.2 (hconn _ _)))
      exact ⟨j, hjL, by omega⟩
    by_cases heven : p.length % 2 = 0
    · -- Case 3a: L = 2*m is EVEN
      have hL2m : p.length = 2 * m := by omega
      have hdaP : ∀ j ≤ p.length, m ≤ G.dist a (p.getVert j) := by
        intro j hjL
        have := hdist_P j hjL
        split_ifs at this <;> omega
      have hφ_in_A : ∀ i, 1 ≤ i → i ≤ 2 * m - 1 → φ (p.getVert i) ∈ A := by
        intro i hi1 hi2
        have hd := hφ_dist i (by omega)
        have hdlt : G.dist a (φ (p.getVert i)) < m := by split_ifs at hd <;> omega
        have hnotP : φ (p.getVert i) ∉ p.support := by
          intro hP
          obtain ⟨j, hjL, hjEq⟩ := (mem_support_iff_getVert p _).1 hP
          have := hdaP j hjL
          rw [hjEq] at this
          omega
        rcases (hpart _).1 hnotP with hA' | hB'
        · exact hA'
        · obtain ⟨j, hjL, hjB⟩ := hdist_B _ hB'
          have := hdaP j hjL
          omega
      have hφ_sub : ∀ z ∈ p.support, φ z ∈ A ∨ φ z ∈ p.support := by
        intro z hz
        obtain ⟨i, hiL, rfl⟩ := (mem_support_iff_getVert p z).1 hz
        have hd := hφ_dist i hiL
        have hdle : G.dist a (φ (p.getVert i)) ≤ m := by split_ifs at hd <;> omega
        by_cases hP : φ (p.getVert i) ∈ p.support
        · exact Or.inr hP
        · rcases (hpart _).1 hP with hA' | hB'
          · exact Or.inl hA'
          · obtain ⟨j, hjL, hjB⟩ := hdist_B _ hB'
            have := hdaP j hjL
            omega
      have hinter_le2 : (Finset.univ.filter (fun z => z ∈ p.support ∧ φ.symm z ∈ p.support)).card ≤ 2 := by
        have hsub_pair : Finset.univ.filter (fun z => z ∈ p.support ∧ φ.symm z ∈ p.support) ⊆ {φ u, φ v} := by
          intro z hz
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
          obtain ⟨i, hiL, hiEq⟩ := (mem_support_iff_getVert p (φ.symm z)).1 hz.2
          have hz_eq : z = φ (p.getVert i) := by rw [hiEq, φ.apply_symm_apply]
          by_cases hi0 : i = 0
          · subst hi0; simp [hz_eq]
          · by_cases hiE : i = p.length
            · subst hiE; simp [hz_eq]
            · have hiA := hφ_in_A i (by omega) (by omega)
              rw [← hz_eq] at hiA
              exact absurd hz.1 ((hpart z).2 (Or.inl hiA))
        exact (Finset.card_le_card hsub_pair).trans (Finset.card_le_two)
      have hge3 := no_nesting_inter_ge_three hconn hvt hcard hdeg3 p hp hgeo hlen hnot hmin hA hB hpart hdAB hnoAB hminK φ hφ_sub
      omega
    · -- Case 3b/3c: L = 2*m + 1 is ODD
      have hL2m1 : p.length = 2 * m + 1 := by omega
      have hdaP_lt : ∀ j ≤ 2 * m, m + 1 ≤ G.dist a (p.getVert j) := by
        intro j hj
        have := hdist_P j (by omega)
        split_ifs at this <;> omega
      have hdaP_all : ∀ j ≤ p.length, m ≤ G.dist a (p.getVert j) := by
        intro j hj
        have := hdist_P j hj
        split_ifs at this <;> omega
      have hφ_in_A : ∀ i, 1 ≤ i → i ≤ 2 * m - 1 → φ (p.getVert i) ∈ A := by
        intro i hi1 hi2
        have hd := hφ_dist i (by omega)
        have hdlt : G.dist a (φ (p.getVert i)) < m := by split_ifs at hd <;> omega
        have hnotP : φ (p.getVert i) ∉ p.support := by
          intro hP
          obtain ⟨j, hjL, hjEq⟩ := (mem_support_iff_getVert p _).1 hP
          have := hdaP_all j hjL
          rw [hjEq] at this
          omega
        rcases (hpart _).1 hnotP with hA' | hB'
        · exact hA'
        · obtain ⟨j, hjL, hjB⟩ := hdist_B _ hB'
          have := hdaP_all j hjL
          omega
      have hφ_eq_v_if_P : ∀ i, (i = 0 ∨ i = 2 * m) → φ (p.getVert i) ∈ A ∨ φ (p.getVert i) = v := by
        intro i hi
        have hd := hφ_dist i (by omega)
        have hdle : G.dist a (φ (p.getVert i)) = m := by rcases hi with rfl | rfl <;> split_ifs at hd <;> omega
        by_cases hP : φ (p.getVert i) ∈ p.support
        · obtain ⟨j, hjL, hjEq⟩ := (mem_support_iff_getVert p _).1 hP
          by_cases hjE : j = p.length
          · subst hjE; exact Or.inr (by simpa using hjEq.symm)
          · have := hdaP_lt j (by omega)
            rw [hjEq] at this
            omega
        · rcases (hpart _).1 hP with hA' | hB'
          · exact Or.inl hA'
          · obtain ⟨j, hjL, hjB⟩ := hdist_B _ hB'
            have := hdaP_all j hjL
            omega
      by_cases hφvB : φ v ∈ B
      · -- Subcase 3c: φ v = b* ∈ B, forcing φ(p.getVert (2*m)) = v and φ(p.getVert 0) ∈ A!
        have hadj_2m : G.Adj (φ (p.getVert (2 * m))) (φ v) := by
          have h := p.adj_getVert_succ (show 2 * m < p.length by omega)
          have h' : p.getVert (2 * m + 1) = v := by rw [← hL2m1, Walk.getVert_length]
          rw [h'] at h
          exact φ.map_rel_iff.2 h
        have hφ2m_eq_v : φ (p.getVert (2 * m)) = v := by
          rcases hφ_eq_v_if_P (2 * m) (Or.inr rfl) with hA' | hv'
          · exact absurd hadj_2m (hnoAB _ hA' _ hφvB)
          · exact hv'
        have hφ0_in_A : φ (p.getVert 0) ∈ A := by
          rcases hφ_eq_v_if_P 0 (Or.inl rfl) with hA' | hv'
          · exact hA'
          · have h02m : p.getVert 0 = p.getVert (2 * m) := φ.injective (hv'.trans hφ2m_eq_v.symm)
            have hd0 := geodesic_dist_getVert p hgeo (Nat.zero_le (2 * m)) (by omega)
            rw [h02m, SimpleGraph.dist_self] at hd0
            omega
        let T : Set V := {z | φ.symm z ∉ p.support}
        have hST : ∀ z, z ∉ p.support ↔ φ z ∈ T := fun z => by simp [T]
        have hφP_cap_P : ∀ j ≤ 2 * m, p.getVert j ∈ T := by
          intro j hj hmem
          obtain ⟨i, hiL, hiEq⟩ := (mem_support_iff_getVert p (φ.symm (p.getVert j))).1 hmem
          have heq : p.getVert j = φ (p.getVert i) := by rw [hiEq, φ.apply_symm_apply]
          by_cases hi0 : i = 0
          · subst hi0; exact ((hpart _).2 (Or.inl hφ0_in_A)) (heq ▸ p.getVert_mem_support j)
          · by_cases hi2m : i = 2 * m
            · subst hi2m
              rw [hφ2m_eq_v] at heq
              have hd := geodesic_dist_getVert p hgeo (show j ≤ p.length by omega) le_rfl
              rw [Walk.getVert_length, heq, SimpleGraph.dist_self] at hd
              omega
            · by_cases hiL' : i = p.length
              · subst hiL'
                rw [Walk.getVert_length] at heq
                exact ((hpart _).2 (Or.inr hφvB)) (heq ▸ p.getVert_mem_support j)
              · exact ((hpart _).2 (Or.inl (hφ_in_A i (by omega) (by omega)))) (heq ▸ p.getVert_mem_support j)
        have hφP_cap_B : ∀ b ∈ B, b ≠ φ v → b ∈ T := by
          intro b hb hne hmem
          obtain ⟨i, hiL, hiEq⟩ := (mem_support_iff_getVert p (φ.symm b)).1 hmem
          have heq : b = φ (p.getVert i) := by rw [hiEq, φ.apply_symm_apply]
          by_cases hi0 : i = 0
          · subst hi0; exact Finset.disjoint_left.1 hdAB hφ0_in_A (heq ▸ hb)
          · by_cases hi2m : i = 2 * m
            · subst hi2m; rw [hφ2m_eq_v] at heq
              exact ((hpart b).2 (Or.inr hb)) (heq ▸ p.end_mem_support)
            · by_cases hiL' : i = p.length
              · subst hiL'; rw [Walk.getVert_length] at heq; exact hne heq
              · exact Finset.disjoint_left.1 hdAB (hφ_in_A i (by omega) (by omega)) (heq ▸ hb)
        have huT : u ∈ T := by simpa using hφP_cap_P 0 (Nat.zero_le _)
        have hP_reach : ∀ j (hj : j ≤ 2 * m), (G.induce T).Reachable ⟨u, huT⟩ ⟨p.getVert j, hφP_cap_P j hj⟩ := by
          intro j hj
          induction j with
          | zero =>
            have : (⟨p.getVert 0, hφP_cap_P 0 hj⟩ : T) = ⟨u, huT⟩ := Subtype.ext (Walk.getVert_zero p)
            rw [this]
          | succ k ih =>
            have hk : k ≤ 2 * m := by omega
            have hadj : G.Adj (p.getVert k) (p.getVert (k + 1)) := p.adj_getVert_succ (by omega)
            exact (ih hk).trans (Adj.reachable (show (G.induce T).Adj ⟨p.getVert k, hφP_cap_P k hk⟩
              ⟨p.getVert (k + 1), hφP_cap_P (k + 1) hj⟩ from hadj))
        -- Every b ∈ B \ {φ v} reaches u in G[T]!
        let B' : Finset V := B.erase (φ v)
        have hB'_reach : ∀ b (hb' : b ∈ B'), (G.induce T).Reachable ⟨u, huT⟩ ⟨b, hφP_cap_B b (Finset.mem_of_mem_erase hb') (Finset.ne_of_mem_erase hb')⟩ := by
          intro b hb'
          have hbB : b ∈ B := Finset.mem_of_mem_erase hb'
          have hbne : b ≠ φ v := Finset.ne_of_mem_erase hb'
          let C : Finset V := Finset.univ.filter (fun z =>
            ∃ hz : z ∈ B', (G.induce (B' : Set V)).Reachable ⟨b, hb'⟩ ⟨z, hz⟩)
          have hCne : C.Nonempty := ⟨b, by simp [C, hb']⟩
          have hCsub : C ⊆ B' := fun z hz => by
            simp only [C, Finset.mem_filter, Finset.mem_univ, true_and] at hz; exact hz.1
          have hCclosed : ∀ z ∈ C, ∀ y ∈ B', G.Adj z y → y ∈ C := by
            intro z hz y hy hzy
            simp only [C, Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
            exact ⟨hy, hz.2.trans (Adj.reachable (show (G.induce (B' : Set V)).Adj ⟨z, hz.1⟩ ⟨y, hy⟩ from hzy))⟩
          -- C must have an edge to P \ {v} (else {v, φ v} is a 2-cut separating C from A!)
          have hex_edge : ∃ c ∈ C, ∃ j ≤ 2 * m, G.Adj c (p.getVert j) := by
            by_contra hnoE
            push Not at hnoE
            let S2 : Finset V := {v, φ v}
            have hdisjCA : Disjoint C A := Disjoint.mono_left (hCsub.trans (Finset.erase_subset _ _)) hdAB.symm
            have hdisjCS2 : Disjoint C S2 := by
              rw [Finset.disjoint_left]
              intro z hzC hzS
              have hzB' : z ∈ B' := hCsub hzC
              simp only [S2, Finset.mem_insert, Finset.mem_singleton] at hzS
              rcases hzS with hzv | hzφ
              · rw [hzv] at hzB'
                exact ((hpart v).2 (Or.inr (Finset.mem_of_mem_erase hzB'))) p.end_mem_support
              · exact (Finset.ne_of_mem_erase hzB') hzφ
            have hdisjAS2 : Disjoint A S2 := by
              rw [Finset.disjoint_left]
              intro z hzA hzS
              simp only [S2, Finset.mem_insert, Finset.mem_singleton] at hzS
              rcases hzS with hzv | hzφ
              · rw [hzv] at hzA
                exact ((hpart v).2 (Or.inl hzA)) p.end_mem_support
              · rw [hzφ] at hzA
                exact Finset.disjoint_left.1 hdAB hzA hφvB
            have hnoCA : ∀ c ∈ C, ∀ a' ∈ A, ¬ G.Adj c a' :=
              fun c hc a' ha' h => hnoAB a' ha' c (Finset.mem_of_mem_erase (hCsub hc)) h.symm
            have hbdry : ∀ c ∈ C, ∀ z, G.Adj c z → z ∈ C ∨ z ∈ S2 := by
              intro c hc z hcz
              by_cases hzP : z ∈ p.support
              · obtain ⟨j, hjL, rfl⟩ := (mem_support_iff_getVert p z).1 hzP
                by_cases hjE : j = p.length
                · subst hjE; exact Or.inr (by simp [S2])
                · exact absurd hcz (hnoE c hc j (by omega))
              · rcases (hpart z).1 hzP with hzA | hzB
                · exact absurd hcz (hnoCA c hc z hzA)
                · by_cases hzφ : z = φ v
                  · subst hzφ; exact Or.inr (by simp [S2])
                  · exact Or.inl (hCclosed c hc z (Finset.mem_erase.2 ⟨hzφ, hzB⟩) hcz)
            exact vt_no_two_cut hconn hvt hcard hdeg3 hCne hA hdisjCA hdisjCS2 hdisjAS2 hnoCA hbdry Finset.card_le_two
          obtain ⟨c, hcC, j, hj, hcj⟩ := hex_edge
          have hcB' : c ∈ B' := hCsub hcC
          simp only [C, Finset.mem_filter, Finset.mem_univ, true_and] at hcC
          obtain ⟨q, hqB'⟩ := (walk_induce_iff_exists_walk hb' hcB').1 hcC.2
          have hbcT : (G.induce T).Reachable ⟨b, hφP_cap_B b hbB hbne⟩
              ⟨c, hφP_cap_B c (Finset.mem_of_mem_erase hcB') (Finset.ne_of_mem_erase hcB')⟩ :=
            (walk_induce_iff_exists_walk _ _).2 ⟨q, fun z hz =>
              hφP_cap_B z (Finset.mem_of_mem_erase (hqB' z hz)) (Finset.ne_of_mem_erase (hqB' z hz))⟩
          exact (hP_reach j hj).trans
            ((Adj.reachable (show (G.induce T).Adj ⟨p.getVert j, hφP_cap_P j hj⟩
              ⟨c, hφP_cap_B c (Finset.mem_of_mem_erase hcB') (Finset.ne_of_mem_erase hcB')⟩ from hcj.symm)).trans hbcT.symm)
        -- Now H = B' ∪ (P \ {v}) lies inside T, is connected, and its complement in T is ⊆ A \ {φ(p.getVert 0)}!
        let P' : Finset V := (Finset.range (2 * m + 1)).image (fun j => p.getVert j)
        let H : Finset V := B' ∪ P'
        have hHreach : ∀ z ∈ H, ∃ hz : z ∈ T, (G.induce T).Reachable ⟨u, huT⟩ ⟨z, hz⟩ := by
          intro z hz
          rw [Finset.mem_union] at hz
          rcases hz with hzB' | hzP'
          · exact ⟨hφP_cap_B z (Finset.mem_of_mem_erase hzB') (Finset.ne_of_mem_erase hzB'), hB'_reach z hzB'⟩
          · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hzP'
            have hj2m : j ≤ 2 * m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
            exact ⟨hφP_cap_P j hj2m, hP_reach j hj2m⟩
        have hcomp_sub : Finset.univ.filter (fun z => z ∈ T ∧ z ∉ H) ⊆ A.erase (φ (p.getVert 0)) := by
          intro z hz
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
          obtain ⟨hzT, hznH⟩ := hz
          have hz_notP' : z ∉ P' := fun h => hznH (Finset.mem_union_right _ h)
          have hz_notB' : z ∉ B' := fun h => hznH (Finset.mem_union_left _ h)
          have hz_ne_v : z ≠ v := by
            intro h
            have hEq : φ.symm z = p.getVert (2 * m) :=
              (congrArg φ.symm (h.trans hφ2m_eq_v.symm)).trans (φ.symm_apply_apply _)
            have hmem : φ.symm z ∈ p.support := by
              rw [hEq]; exact p.getVert_mem_support (2 * m)
            exact hzT hmem
          have hz_notP : z ∉ p.support := by
            intro hzP
            obtain ⟨j, hjL, rfl⟩ := (mem_support_iff_getVert p z).1 hzP
            by_cases hjE : j = p.length
            · subst hjE; exact hz_ne_v (Walk.getVert_length p)
            · exact hz_notP' (Finset.mem_image.2 ⟨j, Finset.mem_range.2 (by omega), rfl⟩)
          have hzA : z ∈ A := by
            rcases (hpart z).1 hz_notP with hA' | hB'
            · exact hA'
            · by_cases hzφ : z = φ v
              · subst hzφ
                exact absurd (by simp [p.end_mem_support]) hzT
              · exact absurd (Finset.mem_erase.2 ⟨hzφ, hB'⟩) hz_notB'
          have hz_ne_φ0 : z ≠ φ (p.getVert 0) := by
            intro h; subst h
            exact hzT (by simp [p.getVert_mem_support 0])
          exact Finset.mem_erase.2 ⟨hz_ne_φ0, hzA⟩
        have hcomp_lt : (Finset.univ.filter (fun z => z ∈ T ∧ z ∉ H)).card < A.card := by
          have h1 := Finset.card_le_card hcomp_sub
          have h2 : (A.erase (φ (p.getVert 0))).card = A.card - 1 := Finset.card_erase_of_mem hφ0_in_A
          have h3 : 1 ≤ A.card := Finset.card_pos.2 hA
          omega
        exact absurd_of_large_connected_in_image hnot hminK φ hST huT hHreach (by convert hcomp_lt)
      · -- Subcase 3b: φ v ∉ B, so φ(P) ⊆ A ∪ P and P ∩ φ(P) ⊆ {v, φ v} has card ≤ 2!
        have hφ_sub : ∀ z ∈ p.support, φ z ∈ A ∨ φ z ∈ p.support := by
          intro z hz
          obtain ⟨i, hiL, rfl⟩ := (mem_support_iff_getVert p z).1 hz
          by_cases hi0 : i = 0
          · subst hi0
            rcases hφ_eq_v_if_P 0 (Or.inl rfl) with hA' | hv'
            · exact Or.inl hA'
            · exact Or.inr (hv'.symm ▸ p.end_mem_support)
          · by_cases hi2m : i = 2 * m
            · subst hi2m
              rcases hφ_eq_v_if_P (2 * m) (Or.inr rfl) with hA' | hv'
              · exact Or.inl hA'
              · exact Or.inr (hv'.symm ▸ p.end_mem_support)
            · by_cases hiE : i = p.length
              · subst hiE; rw [Walk.getVert_length]
                by_cases hP : φ v ∈ p.support
                · exact Or.inr hP
                · rcases (hpart (φ v)).1 hP with hA' | hB'
                  · exact Or.inl hA'
                  · exact absurd hB' hφvB
              · exact Or.inl (hφ_in_A i (by omega) (by omega))
        have hinter_le2 : (Finset.univ.filter (fun z => z ∈ p.support ∧ φ.symm z ∈ p.support)).card ≤ 2 := by
          have hsub_pair : Finset.univ.filter (fun z => z ∈ p.support ∧ φ.symm z ∈ p.support) ⊆ {v, φ v} := by
            intro z hz
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
            obtain ⟨i, hiL, hiEq⟩ := (mem_support_iff_getVert p (φ.symm z)).1 hz.2
            have hz_eq : z = φ (p.getVert i) := by rw [hiEq, φ.apply_symm_apply]
            by_cases hi0 : i = 0
            · subst hi0
              rcases hφ_eq_v_if_P 0 (Or.inl rfl) with hA' | hv'
              · exact absurd hz.1 ((hpart z).2 (Or.inl (hz_eq ▸ hA')))
              · rw [hz_eq, hv']; exact Finset.mem_insert_self _ _
            · by_cases hi2m : i = 2 * m
              · subst hi2m
                rcases hφ_eq_v_if_P (2 * m) (Or.inr rfl) with hA' | hv'
                · exact absurd hz.1 ((hpart z).2 (Or.inl (hz_eq ▸ hA')))
                · rw [hz_eq, hv']; exact Finset.mem_insert_self _ _
              · by_cases hiE : i = p.length
                · subst hiE; simp [hz_eq]
                · exact absurd hz.1 ((hpart z).2 (Or.inl (hz_eq ▸ hφ_in_A i (by omega) (by omega))))
          exact (Finset.card_le_card hsub_pair).trans Finset.card_le_two
        have hge3 := no_nesting_inter_ge_three hconn hvt hcard hdeg3 p hp hgeo hlen hnot hmin hA hB hpart hdAB hnoAB hminK φ hφ_sub
        omega
  · -- a ∈ P
    obtain ⟨j, hjL, rfl⟩ := (mem_support_iff_getVert p a).1 hxP
    have hm_le : m ≤ p.length := Nat.div_le_self _ _
    rcases le_total m j with hmj | hjm
    · rw [geodesic_dist_getVert p hgeo hmj hjL]; omega
    · rw [SimpleGraph.dist_comm, geodesic_dist_getVert p hgeo hjm hm_le]; omega

/-- Step 4 (Discrete Intermediate Value Theorem on `ψ(a) = d(a, u) - d(a, v)` over `G[A]`):
There exists `a* ∈ A` with `ψ(a*) ∈ {2*m - L, 2*m - L + 1}`. -/
private lemma exists_middle_slice_vertex [Fintype V] {G : SimpleGraph V}
    (hconn : G.Connected) {u v : V} (p : G.Walk u v) (hp : p.IsPath)
    (hgeo : p.length = G.dist u v) (hlen : 2 ≤ p.length)
    (hmin : ∀ (u' v' : V) (q : G.Walk u' v'), q.IsPath → q.length = G.dist u' v' →
      q.length < p.length → (G.induce {x | x ∉ q.support}).Connected)
    {A B : Finset V} (hA : A.Nonempty) (hB : B.Nonempty)
    (hAconn : (G.induce (A : Set V)).Connected)
    (hpart : ∀ x, x ∉ p.support ↔ x ∈ A ∨ x ∈ B) (hdAB : Disjoint A B)
    (hnoAB : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b) :
    let m := p.length / 2
    ∃ a ∈ A,
      (G.dist a u : ℤ) - (G.dist a v : ℤ) = 2 * (m : ℤ) - (p.length : ℤ) ∨
      (G.dist a u : ℤ) - (G.dist a v : ℤ) = 2 * (m : ℤ) - (p.length : ℤ) + 1 := by
  intro m
  let ψ : V → ℤ := fun x => (G.dist x u : ℤ) - (G.dist x v : ℤ)
  let t : ℤ := 2 * (m : ℤ) - (p.length : ℤ)
  have hstep : ∀ x y : V, G.Adj x y → ψ y ≤ ψ x + 2 := by
    intro x y hxy
    have h1 : G.dist y u ≤ G.dist x u + 1 := by
      have := dist_triangle_of_reachable (Adj.reachable hxy.symm) (hconn x u)
      rw [SimpleGraph.dist_eq_one_iff_adj.2 hxy.symm] at this; omega
    have h2 : G.dist x v ≤ G.dist y v + 1 := by
      have := dist_triangle_of_reachable (Adj.reachable hxy) (hconn y v)
      rw [SimpleGraph.dist_eq_one_iff_adj.2 hxy] at this; omega
    simp only [ψ]; omega
  obtain ⟨⟨a0, ha0A, hua0⟩, _, ⟨aL, haLA, hvaL⟩, _⟩ :=
    minimal_endpoint_touches_both p hp hgeo (by omega) hmin hA hB hpart hdAB hnoAB
  have hψ0 : ψ a0 ≤ t := by
    have h1 : G.dist a0 u = 1 := SimpleGraph.dist_eq_one_iff_adj.2 hua0.symm
    have h2 : G.dist u v ≤ 1 + G.dist a0 v := by
      have := dist_triangle_of_reachable (Adj.reachable hua0) (hconn a0 v)
      rwa [SimpleGraph.dist_eq_one_iff_adj.2 hua0] at this
    simp only [ψ, t, h1]; omega
  have hψL : t ≤ ψ aL := by
    have h1 : G.dist aL v = 1 := SimpleGraph.dist_eq_one_iff_adj.2 hvaL.symm
    have h2 : G.dist u v ≤ G.dist aL u + 1 := by
      have := dist_triangle_of_reachable (hconn u aL) (Adj.reachable hvaL.symm)
      rw [SimpleGraph.dist_comm (u := u) (v := aL), SimpleGraph.dist_eq_one_iff_adj.2 hvaL.symm] at this
      exact this
    simp only [ψ, t, h1]; omega
  obtain ⟨w, hwA⟩ := (walk_induce_iff_exists_walk (show a0 ∈ (A : Set V) from ha0A)
    (show aL ∈ (A : Set V) from haLA)).1 (hAconn.preconnected ⟨a0, ha0A⟩ ⟨aL, haLA⟩)
  -- Walk induction: if ψ x ≤ t ≤ ψ y along a walk w in A, then some vertex on w has ψ z ∈ {t, t+1}.
  have hivt : ∀ {x y : V} (q : G.Walk x y), (∀ z ∈ q.support, z ∈ A) →
      ψ x ≤ t → t ≤ ψ y → ∃ z ∈ A, ψ z = t ∨ ψ z = t + 1 := by
    intro x y q
    induction q with
    | @nil x =>
      intro hq hx hy
      exact ⟨x, hq x (by simp), Or.inl (le_antisymm hx hy)⟩
    | @cons x y' z hxy' q' ih =>
      intro hq hx hy
      by_cases hy' : ψ y' ≤ t
      · exact ih (fun s hs => hq s (by simp [hs])) hy' hy
      · have hle := hstep x y' hxy'
        have hx' : ψ x ≤ t := hx
        by_cases h1 : ψ y' = t + 1
        · exact ⟨y', hq y' (by simp), Or.inr h1⟩
        · have hxt : ψ x = t := by omega
          exact ⟨x, hq x (by simp), Or.inl hxt⟩
  exact hivt w (fun z hz => hwA z hz) hψ0 hψL

/-- Step 5 (Excess Domination + Grand Antipode Block Theorem):
In ANY finite connected vertex-transitive graph `G` with `3 ≤ |V|` and a minimal-length
disconnecting geodesic `P = (v_0, ..., v_L)`, letting `A` be a minimum-size component of `G - P`
and `m = L / 2`, there exists `a* ∈ A` such that for EVERY `r ≥ L`:
  `sphere G a* r = sphere G (p.getVert m) r`!
In particular, `sphere G a* (graphDiam G) = sphere G (p.getVert m) (graphDiam G)` with `a* ≠ p.getVert m`! -/
theorem grand_antipode_block_theorem [Fintype V] {G : SimpleGraph V}
    (hconn : G.Connected) (hvt : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V)
    {u v : V} (p : G.Walk u v) (hp : p.IsPath) (hgeo : p.length = G.dist u v)
    (hnot : ¬ (G.induce {x | x ∉ p.support}).Connected)
    (hmin : ∀ (u' v' : V) (q : G.Walk u' v'), q.IsPath → q.length = G.dist u' v' →
      q.length < p.length → (G.induce {x | x ∉ q.support}).Connected) :
    ∃ A B : Finset V, A.Nonempty ∧ B.Nonempty ∧
      (G.induce (A : Set V)).Connected ∧
      (∀ x, x ∉ p.support ↔ x ∈ A ∨ x ∈ B) ∧
      Disjoint A B ∧
      (∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b) ∧
      (∀ K : Finset V, K.Nonempty → (∀ y ∈ K, y ∉ p.support) →
        (∀ y ∈ K, ∀ z, z ∉ p.support → G.Adj y z → z ∈ K) → A.card ≤ K.card) ∧
      (3 ≤ p.length) ∧
      (∀ x : V, (x ∈ A ∨ x ∈ p.support) → G.dist (p.getVert (p.length / 2)) x < p.length) ∧
      (∃ a ∈ A, ∀ r : ℕ, p.length ≤ r → sphere G a r = sphere G (p.getVert (p.length / 2)) r) := by
  have hlen3 : 3 ≤ p.length := by
    by_contra hlt
    exact hnot (length_le_two_connected hconn hvt hcard p hp hgeo (by omega))
  -- Prove degree ≥ 3 (if degree ≤ 2, length ≤ 2 or handshaking gives connectedness!)
  have hdeg3 : ∀ x : V, 3 ≤ G.degree x := by
    intro x
    by_contra hlt
    have hle2 : G.degree x ≤ 2 := by omega
    have hall_le2 : ∀ y : V, G.degree y ≤ 2 := by
      intro y
      obtain ⟨φ, hφ⟩ := hvt x y
      rw [← hφ, φ.degree_eq]; exact hle2
    -- Every vertex of G has degree 2 (if ≤ 1, connected with |V| ≥ 3 impossible!)
    have hall_eq2 : ∀ y : V, G.degree y = 2 := by
      intro y
      have hge2 : 2 ≤ G.degree y := by
        -- From p with length ≥ 3, p.getVert 1 has 2 distinct neighbors p.getVert 0 and p.getVert 2
        have h01 : G.Adj (p.getVert 1) (p.getVert 0) := (p.adj_getVert_succ (by omega)).symm
        have h12 : G.Adj (p.getVert 1) (p.getVert 2) := p.adj_getVert_succ (by omega)
        have hne : p.getVert 0 ≠ p.getVert 2 := by
          intro h
          have hd := geodesic_dist_getVert p hgeo (show 0 ≤ 2 by omega) (by omega)
          rw [h, SimpleGraph.dist_self] at hd; omega
        have hsub : ({p.getVert 0, p.getVert 2} : Finset V) ⊆ G.neighborFinset (p.getVert 1) := by
          intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rw [SimpleGraph.mem_neighborFinset]
          rcases hz with rfl | rfl <;> assumption
        have hc := Finset.card_le_card hsub
        rw [Finset.card_pair hne, SimpleGraph.card_neighborFinset_eq_degree] at hc
        obtain ⟨φ, hφ⟩ := hvt (p.getVert 1) y
        rw [← hφ, φ.degree_eq]; exact hc
      have := hall_le2 y
      omega
    -- In a 2-regular graph, u has only 1 neighbor outside P (since p.getVert 1 ∈ P) and v has 1,
    -- contradicting minimal_endpoint_touches_both which needs u to touch BOTH A and B!
    have hSne : {z : V | z ∉ p.support}.Nonempty := exists_not_mem_geodesic hvt hcard p hp hgeo
    obtain ⟨A, B, hA, hB, _, hpart, hdAB, hnoAB⟩ := not_connected_induce_split hSne hnot
    obtain ⟨⟨a0, ha0A, hua0⟩, ⟨b0, hb0B, hub0⟩, _, _⟩ :=
      minimal_endpoint_touches_both p hp hgeo (by omega) hmin hA hB hpart hdAB hnoAB
    have hu1 : G.Adj u (p.getVert 1) := by
      have := p.adj_getVert_succ (show 0 < p.length by omega)
      rwa [Walk.getVert_zero] at this
    have hab : a0 ≠ b0 := fun h => Finset.disjoint_left.1 hdAB ha0A (h ▸ hb0B)
    have ha1 : a0 ≠ p.getVert 1 := fun h => ((hpart a0).2 (Or.inl ha0A)) (h ▸ p.getVert_mem_support 1)
    have hb1 : b0 ≠ p.getVert 1 := fun h => ((hpart b0).2 (Or.inr hb0B)) (h ▸ p.getVert_mem_support 1)
    have hsub3 : ({a0, b0, p.getVert 1} : Finset V) ⊆ G.neighborFinset u := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rw [SimpleGraph.mem_neighborFinset]
      rcases hz with rfl | rfl | rfl <;> assumption
    have hc3 := Finset.card_le_card hsub3
    rw [Finset.card_insert_of_notMem (by simp [hab, ha1]),
        Finset.card_pair hb1, SimpleGraph.card_neighborFinset_eq_degree, hall_eq2 u] at hc3
    omega
  have hSne : {z : V | z ∉ p.support}.Nonempty := exists_not_mem_geodesic hvt hcard p hp hgeo
  obtain ⟨A, B, hA, hB, hAconn, hpart, hdAB, hnoAB, hminK⟩ := exists_min_component_split hSne hnot
  have hmid_lt := midpoint_dist_lt_length hconn hvt hcard hdeg3 p hp hgeo (by omega) hnot hmin hA hB hpart hdAB hnoAB hminK
  obtain ⟨a, haA, ha_psi⟩ := exists_middle_slice_vertex hconn p hp hgeo (by omega) hmin hA hB hAconn hpart hdAB hnoAB
  let m := p.length / 2
  have hm_le : m ≤ p.length := Nat.div_le_self _ _
  -- Step 5: Excess Domination on `a`!
  have hdom_P : ∀ j ≤ p.length, G.dist (p.getVert m) (p.getVert j) ≤ G.dist a (p.getVert j) := by
    intro j hjL
    have hmj : G.dist (p.getVert m) (p.getVert j) = if j ≤ m then m - j else j - m := by
      split_ifs with hjm
      · rw [SimpleGraph.dist_comm]; exact geodesic_dist_getVert p hgeo hjm hm_le
      · exact geodesic_dist_getVert p hgeo (by omega) hjL
    have htri0 := dist_triangle_of_reachable (hconn a (p.getVert j)) (hconn (p.getVert j) u)
    have hj0 : G.dist (p.getVert j) u = j := by
      have h := geodesic_dist_getVert p hgeo (Nat.zero_le j) hjL
      rw [Walk.getVert_zero, SimpleGraph.dist_comm] at h
      simpa using h
    have htriL := dist_triangle_of_reachable (hconn a (p.getVert j)) (hconn (p.getVert j) v)
    have hjL' : G.dist (p.getVert j) v = p.length - j := by
      have h := geodesic_dist_getVert p hgeo hjL le_rfl
      rw [Walk.getVert_length] at h
      exact h
    have htri_uv := dist_triangle_of_reachable (hconn u a) (hconn a v)
    rw [SimpleGraph.dist_comm (u := u) (v := a), ← hgeo] at htri_uv
    rw [hj0] at htri0; rw [hjL'] at htriL; rw [hmj]
    rcases ha_psi with hψ | hψ <;> split_ifs <;> omega
  have hdom_BP : ∀ z : V, z ∉ A → G.dist (p.getVert m) z ≤ G.dist a z := by
    intro z hznA
    obtain ⟨j, hjL, heq⟩ := exists_hit_P_on_geodesic hconn p hpart hdAB hnoAB haA hznA
    have htri := dist_triangle_of_reachable (hconn (p.getVert m) (p.getVert j)) (hconn (p.getVert j) z)
    have hdj := hdom_P j hjL
    omega
  -- Hence for EVERY r ≥ p.length, {z | r ≤ d(v_m, z)} = {z | r ≤ d(a, z)}!
  have hge_eq : ∀ r : ℕ, p.length ≤ r →
      Finset.univ.filter (fun z => r ≤ G.dist (p.getVert m) z) =
      Finset.univ.filter (fun z => r ≤ G.dist a z) := by
    intro r hrL
    have hsub_ge : Finset.univ.filter (fun z => r ≤ G.dist (p.getVert m) z) ⊆
        Finset.univ.filter (fun z => r ≤ G.dist a z) := by
      intro z hz
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
      have hznA : z ∉ A := fun hzA => by
        have := hmid_lt z (Or.inl hzA)
        dsimp only [m] at hz ⊢
        omega
      exact hz.trans (hdom_BP z hznA)
    exact Finset.eq_of_subset_of_card_le hsub_ge (le_of_eq (card_ge_sphere_eq_of_vt hconn hvt a (p.getVert m) r))
  have hsphere_eq : ∀ r : ℕ, p.length ≤ r → sphere G a r = sphere G (p.getVert m) r := by
    intro r hrL
    ext z
    simp only [sphere, Set.mem_setOf_eq]
    have h1 := Finset.ext_iff.1 (hge_eq r hrL) z
    have h2 := Finset.ext_iff.1 (hge_eq (r + 1) (by omega)) z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    omega
  exact ⟨A, B, hA, hB, hAconn, hpart, hdAB, hnoAB, hminK, hlen3, hmid_lt, a, haA, hsphere_eq⟩

/-- Existence of a minimal-length disconnecting geodesic if any disconnecting geodesic exists. -/
private lemma exists_min_disconnecting_geodesic [Fintype V] {G : SimpleGraph V}
    (hnot_all : ¬ ∀ (u v : V) (p : G.Walk u v), p.IsPath → p.length = G.dist u v →
      (G.induce {x | x ∉ p.support}).Connected) :
    ∃ (u v : V) (p : G.Walk u v), p.IsPath ∧ p.length = G.dist u v ∧
      ¬ (G.induce {x | x ∉ p.support}).Connected ∧
      (∀ (u' v' : V) (q : G.Walk u' v'), q.IsPath → q.length = G.dist u' v' →
        q.length < p.length → (G.induce {x | x ∉ q.support}).Connected) := by
  let P : ℕ → Prop := fun k => ∃ (u v : V) (p : G.Walk u v),
    p.IsPath ∧ p.length = G.dist u v ∧ p.length = k ∧ ¬ (G.induce {x | x ∉ p.support}).Connected
  have hex : ∃ k, P k := by
    push Not at hnot_all
    obtain ⟨u, v, p, hp, hgeo, hnot⟩ := hnot_all
    exact ⟨p.length, u, v, p, hp, hgeo, rfl, hnot⟩
  let k₀ := Nat.find hex
  obtain ⟨u, v, p, hp, hgeo, hk, hnot⟩ := Nat.find_spec hex
  refine ⟨u, v, p, hp, hgeo, hnot, fun u' v' q hq hqgeo hqlt => ?_⟩
  by_contra hqn
  exact Nat.find_min hex (hk ▸ hqlt) ⟨u', v', q, hq, hqgeo, rfl, hqn⟩


/-- Core finale: given a minimal-length disconnecting geodesic `p : G.Walk u v` (`3 ≤ p.length`),
a partition `V \ p.support = T ⊔ O` with no edges between `T` and `O`,
a neighbor `t0 ∈ T` of `u`, a nontrivial `~_{≥ L}`-equivalent `c_any ≠ u` of `u`,
and a vertex `wstar ∈ O` with `p.length ≤ d(v1, wstar)` and `d(u, wstar) ≤ d(v1, wstar)`,
we derive `False` via the Master Separation Lemma and the VT Distance-Sum Identity. -/
private lemma contradiction_of_trapped_side [Fintype V] {G : SimpleGraph V}
    (hconn : G.Connected) (hvt : IsVertexTransitive G)
    {u v : V} (p : G.Walk u v) (hgeo : p.length = G.dist u v) (hlen3 : 3 ≤ p.length)
    {T O : Finset V} (hpart : ∀ x, x ∉ p.support ↔ x ∈ T ∨ x ∈ O)
    (hdTO : Disjoint T O) (hnoTO : ∀ a ∈ T, ∀ b ∈ O, ¬ G.Adj a b)
    {t0 : V} (ht0T : t0 ∈ T) (hut0 : G.Adj u t0)
    {c_any : V} (hc_ne : c_any ≠ u) (hc_eq : ∀ r, p.length ≤ r → sphere G c_any r = sphere G u r)
    {wstar : V} (hwstarO : wstar ∈ O)
    (hwstar_ge : p.length ≤ G.dist (p.getVert 1) wstar)
    (hwstar_le : G.dist u wstar ≤ G.dist (p.getVert 1) wstar) : False := by
  let L := p.length
  let v1 := p.getVert 1
  have huv1 : G.Adj u v1 := by
    have h := p.adj_getVert_succ (show 0 < p.length by omega)
    rwa [Walk.getVert_zero] at h
  have hduv1 : G.dist u v1 = 1 := SimpleGraph.dist_eq_one_iff_adj.2 huv1
  have hdut0 : G.dist u t0 = 1 := SimpleGraph.dist_eq_one_iff_adj.2 hut0
  have hc_dist_v : ∀ c : V, (∀ r, L ≤ r → sphere G c r = sphere G u r) → G.dist c v = L := by
    intro c hc
    have hv_in : v ∈ sphere G u L := by
      simp only [sphere, Set.mem_setOf_eq]; exact hgeo.symm
    rw [← hc L le_rfl] at hv_in
    exact hv_in
  have hc_not_P : ∀ c : V, c ≠ u → (∀ r, L ≤ r → sphere G c r = sphere G u r) → c ∉ p.support := by
    intro c hcne hc hcP
    obtain ⟨j, hjL, hjEq⟩ := (mem_support_iff_getVert p c).1 hcP
    have hj_pos : 1 ≤ j := by
      by_contra h0
      have hj0 : j = 0 := by omega
      subst hj0; rw [Walk.getVert_zero] at hjEq; exact hcne hjEq.symm
    have hdv : G.dist (p.getVert j) v = L - j := by
      have h := geodesic_dist_getVert p hgeo hjL le_rfl
      rwa [Walk.getVert_length] at h
    have hcv := hc_dist_v c hc
    rw [← hjEq] at hcv
    omega
  -- Master Separation Lemma: if `c ∈ C_u ∩ S1` and `z ∈ S2`, then
  -- `d(c, u) + d(u, z) ≤ d(c, z) ∨ 1 + d(v1, z) ≤ d(c, z)`.
  have hmaster : ∀ {S1 S2 : Finset V},
      (∀ x, x ∉ p.support ↔ x ∈ S1 ∨ x ∈ S2) → Disjoint S1 S2 →
      (∀ a ∈ S1, ∀ b ∈ S2, ¬ G.Adj a b) →
      ∀ {c z : V}, c ∈ S1 → (∀ r, L ≤ r → sphere G c r = sphere G u r) → z ∈ S2 →
      G.dist c u + G.dist u z ≤ G.dist c z ∨ 1 + G.dist v1 z ≤ G.dist c z := by
    intro S1 S2 hpt hd hno c z hcS1 hceq hzS2
    have hznS1 : z ∉ S1 := Finset.disjoint_right.1 hd hzS2
    obtain ⟨k, hkL, hckz⟩ := exists_hit_P_on_geodesic hconn p hpt hd hno hcS1 hznS1
    by_cases hk0 : k = 0
    · left
      subst hk0
      rw [Walk.getVert_zero] at hckz
      omega
    · right
      have hk1 : 1 ≤ k := by omega
      have hcv := hc_dist_v c hceq
      have htri_cv := dist_triangle_of_reachable (hconn c (p.getVert k)) (hconn (p.getVert k) v)
      have hkv : G.dist (p.getVert k) v = L - k := by
        have h := geodesic_dist_getVert p hgeo hkL le_rfl
        rwa [Walk.getVert_length] at h
      have hck : k ≤ G.dist c (p.getVert k) := by omega
      have hv1k : G.dist v1 (p.getVert k) = k - 1 :=
        geodesic_dist_getVert p hgeo hk1 hkL
      have htri_v1z := dist_triangle_of_reachable (hconn v1 (p.getVert k)) (hconn (p.getVert k) z)
      omega
  -- Domino 1: if `c ∈ (C_u \ {u}) ∩ S1`, no `z ∈ S2` satisfies `L ≤ d(v1, z)` and `d(u, z) ≤ d(v1, z)`.
  have hdomino1 : ∀ {S1 S2 : Finset V},
      (∀ x, x ∉ p.support ↔ x ∈ S1 ∨ x ∈ S2) → Disjoint S1 S2 →
      (∀ a ∈ S1, ∀ b ∈ S2, ¬ G.Adj a b) →
      ∀ {c z : V}, c ∈ S1 → c ≠ u → (∀ r, L ≤ r → sphere G c r = sphere G u r) →
      z ∈ S2 → L ≤ G.dist v1 z → G.dist u z ≤ G.dist v1 z → False := by
    intro S1 S2 hpt hd hno c z hcS1 hcne hceq hzS2 hgeL hle
    have hcu_pos : 1 ≤ G.dist c u := by
      by_contra h0
      have h0' : G.dist c u = 0 := by omega
      exact hcne ((SimpleGraph.dist_eq_zero_iff_eq_or_not_reachable.1 h0').resolve_right (not_not.2 (hconn _ _)))
    have htri_uv1 := dist_triangle_of_reachable (hconn v1 u) (hconn u z)
    rw [SimpleGraph.dist_comm (u := v1) (v := u), hduv1] at htri_uv1
    have hstep : 1 + G.dist u z ≤ G.dist c z := by
      rcases hmaster hpt hd hno hcS1 hceq hzS2 with h1 | h2 <;> omega
    have hcz_geL : L ≤ G.dist c z := by omega
    have hcz_eq : G.dist c z = G.dist u z := by
      have hz_in : z ∈ sphere G c (G.dist c z) := rfl
      rw [hceq (G.dist c z) hcz_geL] at hz_in
      exact hz_in.symm
    omega
  -- Domino 2: every `c ∈ C_u \ {u}` lies in `O`.
  have hC_in_O : ∀ c : V, c ≠ u → (∀ r, L ≤ r → sphere G c r = sphere G u r) → c ∈ O := by
    intro c hcne hceq
    have hc_notP := hc_not_P c hcne hceq
    rcases (hpart c).1 hc_notP with hcT | hcO
    · exact False.elim (hdomino1 hpart hdTO hnoTO hcT hcne hceq hwstarO hwstar_ge hwstar_le)
    · exact hcO
  -- Half-space containment: `Z_<(t0, v1) ⊆ T`.
  have hZ_t0_sub_T : ∀ z : V, G.dist t0 z < G.dist v1 z → z ∈ T := by
    intro z hz
    by_contra hznT
    obtain ⟨j, hjL, ht0jz⟩ := exists_hit_P_on_geodesic hconn p hpart hdTO hnoTO ht0T hznT
    have hdv1j : G.dist v1 (p.getVert j) ≤ G.dist t0 (p.getVert j) := by
      by_cases hj0 : j = 0
      · subst hj0; rw [Walk.getVert_zero]
        rw [SimpleGraph.dist_comm (u := v1) (v := u), hduv1,
            SimpleGraph.dist_comm (u := t0) (v := u), hdut0]
      · have hj1 : 1 ≤ j := by omega
        have hv1j : G.dist v1 (p.getVert j) = j - 1 := geodesic_dist_getVert p hgeo hj1 hjL
        have hjv : G.dist (p.getVert j) v = L - j := by
          have h := geodesic_dist_getVert p hgeo hjL le_rfl
          rwa [Walk.getVert_length] at h
        have htri1 := dist_triangle_of_reachable (hconn u t0) (hconn t0 v)
        have htri2 := dist_triangle_of_reachable (hconn t0 (p.getVert j)) (hconn (p.getVert j) v)
        have huv : G.dist u v = L := hgeo.symm
        omega
    have htri := dist_triangle_of_reachable (hconn v1 (p.getVert j)) (hconn (p.getVert j) z)
    omega
  -- Domino 3: `t0 ∈ C_{v1} \ {v1}`.
  have ht0_ge_eq : ∀ r : ℕ, L ≤ r →
      Finset.univ.filter (fun z => r ≤ G.dist v1 z) =
      Finset.univ.filter (fun z => r ≤ G.dist t0 z) := by
    intro r hrL
    have hc0O : c_any ∈ O := hC_in_O c_any hc_ne hc_eq
    have hsub : Finset.univ.filter (fun z => r ≤ G.dist v1 z) ⊆
        Finset.univ.filter (fun z => r ≤ G.dist t0 z) := by
      intro z hz
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
      by_contra hlt
      have ht0_lt : G.dist t0 z < G.dist v1 z := by omega
      have hzT : z ∈ T := hZ_t0_sub_T z ht0_lt
      have htri_uz := dist_triangle_of_reachable (hconn u t0) (hconn t0 z)
      have huz_le : G.dist u z ≤ G.dist v1 z := by omega
      exact hdomino1 (fun x => (hpart x).trans or_comm) hdTO.symm
        (fun a ha b hb => fun hab => hnoTO b hb a ha hab.symm)
        hc0O hc_ne hc_eq hzT (hrL.trans hz) huz_le
    exact Finset.eq_of_subset_of_card_le hsub (le_of_eq (card_ge_sphere_eq_of_vt hconn hvt t0 v1 r))
  have ht0_eq : ∀ r : ℕ, L ≤ r → sphere G t0 r = sphere G v1 r := by
    intro r hrL
    ext z
    simp only [sphere, Set.mem_setOf_eq]
    have h1 := Finset.ext_iff.1 (ht0_ge_eq r hrL) z
    have h2 := Finset.ext_iff.1 (ht0_ge_eq (r + 1) (by omega)) z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    omega
  -- Domino 4: Map `v1 ↦ u` via `φ ∈ Aut(G)`, set `c := φ(t0) ∈ O`, and derive `Φ(t0, v1) ≥ 1 + Φ(t0, v1)`.
  obtain ⟨φ, hφ⟩ := hvt v1 u
  let c := φ t0
  have ht0_ne_v1 : t0 ≠ v1 := fun h => ((hpart t0).2 (Or.inl ht0T)) (h ▸ p.getVert_mem_support 1)
  have hc_ne_u : c ≠ u := fun h => ht0_ne_v1 (φ.injective (h.trans hφ.symm))
  have hceq : ∀ r : ℕ, L ≤ r → sphere G c r = sphere G u r := by
    intro r hrL
    ext z
    simp only [sphere, Set.mem_setOf_eq]
    have h1 := iso_dist_eq φ hconn t0 (φ.symm z)
    have h2 := iso_dist_eq φ hconn v1 (φ.symm z)
    rw [φ.apply_symm_apply] at h1 h2
    rw [hφ] at h2
    have h3 := Set.ext_iff.1 (ht0_eq r hrL) (φ.symm z)
    simp only [sphere, Set.mem_setOf_eq] at h3
    change G.dist (φ t0) z = r ↔ G.dist u z = r
    rw [h1, h2]; exact h3
  have hcO : c ∈ O := hC_in_O c hc_ne_u hceq
  have hdcu_eq : G.dist c u = G.dist t0 v1 := by
    change G.dist (φ t0) u = G.dist t0 v1
    rw [← hφ, iso_dist_eq φ hconn]
  have hdcu_pos : 1 ≤ G.dist c u := by
    by_contra h0
    have h0' : G.dist c u = 0 := by omega
    exact hc_ne_u ((SimpleGraph.dist_eq_zero_iff_eq_or_not_reachable.1 h0').resolve_right (not_not.2 (hconn _ _)))
  have hptwise : ∀ z : V, G.dist t0 z < G.dist v1 z →
      z ≠ u ∧ G.dist u z < G.dist c z ∧ G.dist v1 z - G.dist t0 z ≤ G.dist c z - G.dist u z := by
    intro z hz
    have hzT : z ∈ T := hZ_t0_sub_T z hz
    have hzne : z ≠ u := fun h => ((hpart z).2 (Or.inl hzT)) (h ▸ p.start_mem_support)
    have hms := hmaster (fun x => (hpart x).trans or_comm) hdTO.symm
      (fun a ha b hb => fun hab => hnoTO b hb a ha hab.symm)
      hcO hceq hzT
    have htri_v1z := dist_triangle_of_reachable (hconn v1 t0) (hconn t0 z)
    rw [SimpleGraph.dist_comm (u := v1) (v := t0)] at htri_v1z
    have htri_uz := dist_triangle_of_reachable (hconn u t0) (hconn t0 z)
    rcases hms with h1 | h2
    · refine ⟨hzne, by omega, by omega⟩
    · refine ⟨hzne, by omega, by omega⟩
  let Zu := Finset.univ.filter (fun z : V => G.dist u z < G.dist c z)
  let Zc := Finset.univ.filter (fun z : V => G.dist c z < G.dist u z)
  let Zt := Finset.univ.filter (fun z : V => G.dist t0 z < G.dist v1 z)
  have hsum_bal : (∑ z ∈ Zu, (G.dist c z - G.dist u z)) = ∑ z ∈ Zc, (G.dist u z - G.dist c z) := by
    obtain ⟨τ, hτ⟩ := hvt u c
    have htot : (∑ z : V, (G.dist u z : ℤ)) = ∑ z : V, (G.dist c z : ℤ) := by
      refine Fintype.sum_equiv τ.toEquiv _ _ (fun z => ?_)
      simp only [RelIso.coe_fn_toEquiv]
      rw [← hτ, iso_dist_eq τ hconn]
    have hdiff : (∑ z : V, ((G.dist c z : ℤ) - (G.dist u z : ℤ))) = 0 := by
      rw [Finset.sum_sub_distrib, htot, sub_self]
    have hsplit : (∑ z : V, ((G.dist c z : ℤ) - (G.dist u z : ℤ))) =
        (∑ z ∈ Zu, ((G.dist c z - G.dist u z : ℕ) : ℤ)) -
        (∑ z ∈ Zc, ((G.dist u z - G.dist c z : ℕ) : ℤ)) := by
      have h1 : (∑ z ∈ Zu, ((G.dist c z - G.dist u z : ℕ) : ℤ)) =
          ∑ z : V, if G.dist u z < G.dist c z then ((G.dist c z : ℤ) - (G.dist u z : ℤ)) else 0 := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl (fun z _ => ?_)
        split_ifs with h
        · exact Nat.cast_sub (le_of_lt h)
        · rfl
      have h2 : (∑ z ∈ Zc, ((G.dist u z - G.dist c z : ℕ) : ℤ)) =
          ∑ z : V, if G.dist c z < G.dist u z then ((G.dist u z : ℤ) - (G.dist c z : ℤ)) else 0 := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl (fun z _ => ?_)
        split_ifs with h
        · exact Nat.cast_sub (le_of_lt h)
        · rfl
      rw [h1, h2, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun z _ => ?_)
      rcases lt_trichotomy (G.dist u z) (G.dist c z) with hlt | heq | hgt
      · have hnot : ¬ G.dist c z < G.dist u z := not_lt_of_gt hlt
        simp [hlt, hnot]
      · simp [heq]
      · have hnot : ¬ G.dist u z < G.dist c z := not_lt_of_gt hgt
        simp [hgt, hnot]
    have hZeq : ((∑ z ∈ Zu, (G.dist c z - G.dist u z) : ℕ) : ℤ) =
        ((∑ z ∈ Zc, (G.dist u z - G.dist c z) : ℕ) : ℤ) := by
      push_cast
      omega
    exact Nat.cast_injective hZeq
  have hsum_iso : (∑ z ∈ Zc, (G.dist u z - G.dist c z)) = ∑ z ∈ Zt, (G.dist v1 z - G.dist t0 z) := by
    refine Finset.sum_bij (fun z _ => φ.symm z) ?_ ?_ ?_ ?_
    · intro z hz
      simp only [Zc, Zt, Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
      have h1 := iso_dist_eq φ.symm hconn c z
      have h2 := iso_dist_eq φ.symm hconn u z
      have hφc : φ.symm c = t0 := φ.symm_apply_apply t0
      have hφu : φ.symm u = v1 := by rw [← hφ, φ.symm_apply_apply]
      rw [hφc] at h1; rw [hφu] at h2
      omega
    · intro z1 _ z2 _ h; exact φ.symm.injective h
    · intro y hy
      refine ⟨φ y, ?_, φ.symm_apply_apply y⟩
      simp only [Zc, Zt, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
      have h1 := iso_dist_eq φ hconn t0 y
      have h2 := iso_dist_eq φ hconn v1 y
      rw [hφ] at h2
      change G.dist (φ t0) (φ y) < G.dist u (φ y)
      omega
    · intro z _
      have h1 := iso_dist_eq φ.symm hconn c z
      have h2 := iso_dist_eq φ.symm hconn u z
      have hφc : φ.symm c = t0 := φ.symm_apply_apply t0
      have hφu : φ.symm u = v1 := by rw [← hφ, φ.symm_apply_apply]
      rw [hφc] at h1; rw [hφu] at h2
      rw [← h1, ← h2]
  have hsub_ins : insert u Zt ⊆ Zu := by
    intro z hz
    simp only [Finset.mem_insert] at hz
    simp only [Zu, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hz with rfl | hz
    · rw [SimpleGraph.dist_self]; omega
    · simp only [Zt, Finset.mem_filter, Finset.mem_univ, true_and] at hz
      exact (hptwise z hz).2.1
  have hu_not_Zt : u ∉ Zt := by
    simp only [Zt, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [SimpleGraph.dist_comm (u := t0) (v := u), hdut0,
        SimpleGraph.dist_comm (u := v1) (v := u), hduv1]
    omega
  have hge1 : (∑ z ∈ insert u Zt, (G.dist c z - G.dist u z)) ≤ ∑ z ∈ Zu, (G.dist c z - G.dist u z) :=
    Finset.sum_le_sum_of_subset hsub_ins
  rw [Finset.sum_insert hu_not_Zt, SimpleGraph.dist_self, Nat.sub_zero] at hge1
  have hge2 : (∑ z ∈ Zt, (G.dist v1 z - G.dist t0 z)) ≤ ∑ z ∈ Zt, (G.dist c z - G.dist u z) :=
    Finset.sum_le_sum (fun z hz => by
      simp only [Zt, Finset.mem_filter, Finset.mem_univ, true_and] at hz
      exact (hptwise z hz).2.2)
  omega

/-- Full Gillibert Geodesic Deletion Theorem for all finite connected vertex-transitive graphs
with `3 ≤ |V|`. -/
theorem gillibert_geodesic_deletion [Fintype V] (G : SimpleGraph V)
    (hconn : G.Connected) (hvt : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V) :
    ∀ (u v : V) (p : G.Walk u v), p.IsPath → p.length = G.dist u v →
      (G.induce {x | x ∉ p.support}).Connected := by
  by_contra hnot_all
  obtain ⟨u, v, p, hp, hgeo, hnot, hmin⟩ := exists_min_disconnecting_geodesic hnot_all
  obtain ⟨A, B, hA, hB, _, hpart, hdAB, hnoAB, _, hlen3, _, a, haA, hsp⟩ :=
    grand_antipode_block_theorem hconn hvt hcard p hp hgeo hnot hmin
  let m := p.length / 2
  let L := p.length
  let v1 := p.getVert 1
  obtain ⟨ψ, hψ⟩ := hvt (p.getVert m) u
  have ha_ne_vm : a ≠ p.getVert m := fun h =>
    ((hpart a).2 (Or.inl haA)) (h ▸ p.getVert_mem_support m)
  have hc_ne : ψ a ≠ u := fun h => ha_ne_vm (ψ.injective (h.trans hψ.symm))
  have hc_eq : ∀ r, L ≤ r → sphere G (ψ a) r = sphere G u r := by
    intro r hrL
    ext z; simp only [sphere, Set.mem_setOf_eq]
    have h1 := iso_dist_eq ψ hconn a (ψ.symm z)
    have h2 := iso_dist_eq ψ hconn (p.getVert m) (ψ.symm z)
    rw [ψ.apply_symm_apply] at h1 h2; rw [hψ] at h2
    have h3 := Set.ext_iff.1 (hsp r hrL) (ψ.symm z)
    simp only [sphere, Set.mem_setOf_eq] at h3
    rw [h1, h2]; exact h3
  have hex_r : ∃ r : ℕ, L ≤ r ∧
      Finset.univ.filter (fun z => r ≤ G.dist v1 z) ≠
      Finset.univ.filter (fun z => r ≤ G.dist u z) := by
    by_contra hall
    push Not at hall
    have hv_in : v ∈ Finset.univ.filter (fun z => L ≤ G.dist u z) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact le_of_eq hgeo
    rw [← hall L le_rfl] at hv_in
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv_in
    have hv1v : G.dist v1 v = L - 1 := by
      have h := geodesic_dist_getVert p hgeo (show 1 ≤ L by omega) le_rfl
      rwa [Walk.getVert_length] at h
    omega
  obtain ⟨r, hrL, hne_filt⟩ := hex_r
  have hex_wstar : ∃ wstar : V, r ≤ G.dist v1 wstar ∧ G.dist u wstar < r := by
    by_contra hall
    push Not at hall
    have hsub : Finset.univ.filter (fun z => r ≤ G.dist v1 z) ⊆
        Finset.univ.filter (fun z => r ≤ G.dist u z) := by
      intro z hz
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
      have := hall z hz; omega
    exact hne_filt (Finset.eq_of_subset_of_card_le hsub (le_of_eq (card_ge_sphere_eq_of_vt hconn hvt u v1 r)))
  obtain ⟨wstar, hw1, hw2⟩ := hex_wstar
  have hwstar_notP : wstar ∉ p.support := by
    intro hwP
    obtain ⟨j, hjL, hjEq⟩ := (mem_support_iff_getVert p wstar).1 hwP
    by_cases hj0 : j = 0
    · subst hj0; rw [Walk.getVert_zero] at hjEq
      have huv1 : G.Adj u v1 := by
        have h := p.adj_getVert_succ (show 0 < p.length by omega)
        rwa [Walk.getVert_zero] at h
      have hduv1 : G.dist v1 u = 1 := by
        rw [SimpleGraph.dist_comm]; exact SimpleGraph.dist_eq_one_iff_adj.2 huv1
      rw [hjEq] at hduv1; omega
    · have hj1 : 1 ≤ j := by omega
      have hv1j : G.dist v1 (p.getVert j) = j - 1 := geodesic_dist_getVert p hgeo hj1 hjL
      have huj : G.dist u (p.getVert j) = j := by
        have h := geodesic_dist_getVert p hgeo (Nat.zero_le j) hjL
        rwa [Walk.getVert_zero] at h
      rw [hjEq] at hv1j huj; omega
  obtain ⟨⟨a0, ha0A, hua0⟩, ⟨b0, hb0B, hub0⟩, _, _⟩ :=
    minimal_endpoint_touches_both p hp hgeo (by omega) hmin hA hB hpart hdAB hnoAB
  have hw_le : G.dist u wstar ≤ G.dist (p.getVert 1) wstar := by
    dsimp only [v1] at hw1; omega
  rcases (hpart wstar).1 hwstar_notP with hwA | hwB
  · exact contradiction_of_trapped_side hconn hvt p hgeo hlen3
      (fun x => (hpart x).trans or_comm) hdAB.symm
      (fun x hx y hy hxy => hnoAB y hy x hx hxy.symm)
      hb0B hub0 hc_ne hc_eq hwA (hrL.trans hw1) hw_le
  · exact contradiction_of_trapped_side hconn hvt p hgeo hlen3
      hpart hdAB hnoAB ha0A hua0 hc_ne hc_eq hwB (hrL.trans hw1) hw_le

end Helpers

end GillibertGeodesicDeletionProof

theorem OMA.solution : type_of% @OMA.S_gillibert_geodesic_deletion.main :=
  fun {_} _ G hconn hvt hcard =>
    GillibertGeodesicDeletionProof.gillibert_geodesic_deletion G hconn hvt hcard
