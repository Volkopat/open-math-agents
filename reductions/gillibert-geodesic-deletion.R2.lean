import OMAStatements.S_gillibert_geodesic_deletion

-- Reduction gillibert-geodesic-deletion.R2 of Geodesic deletion conjecture (vertex-transitive graphs)
-- Credit: @amcolex
-- Proved in full here (zero sorry):
--   1. Automorphism-Step Theorem (general finite connected graphs): any automorphism moving every
--      vertex to an adjacent vertex and mapping V(P) disjointly from V(P) implies G - V(P) connected.
--   2. Watkins atom theorem & connectivity bound kappa(G) >= min(deg(G), 4) for connected VT graphs,
--      settling ALL geodesics of length L <= 2 (and all connected VT graphs of diameter <= 2).
--   3. ALL finite Abelian Cayley graphs (every finite AddCommGroup of order >= 3 and symmetric S).
--   4. Minimal-length disconnecting geodesic reduction splitting the remaining core cleanly into
--      H1 (non-Abelian Cayley graphs, L >= 3) and H2 (non-Cayley VT graphs, L >= 3).

namespace OMA.R_gillibert_geodesic_deletion_R2

open SimpleGraph
open scoped Classical

def H1 : Prop :=
  ∀ {V : Type} [Fintype V] (G : SimpleGraph V),
    G.Connected → OMA.S_gillibert_geodesic_deletion.IsVertexTransitive G → 3 ≤ Fintype.card V →
    (∃ (_ : Group V) (S : Set V), ∀ x y : V, G.Adj x y ↔ x⁻¹ * y ∈ S) →
    (¬ ∃ (_ : AddCommGroup V) (S : Set V), ∀ x y : V, G.Adj x y ↔ y - x ∈ S) →
    ∀ (u v : V) (p : G.Walk u v), p.IsPath → p.length = G.dist u v → 3 ≤ p.length →
      (¬ ∃ φ : G ≃g G, (∀ x, G.Adj x (φ x)) ∧ (∀ x ∈ p.support, φ x ∉ p.support)) →
      (∀ (u' v' : V) (q : G.Walk u' v'), q.IsPath → q.length = G.dist u' v' → q.length < p.length →
        (G.induce {x | x ∉ q.support}).Connected) →
      (G.induce {x | x ∉ p.support}).Connected

def H2 : Prop :=
  ∀ {V : Type} [Fintype V] (G : SimpleGraph V),
    G.Connected → OMA.S_gillibert_geodesic_deletion.IsVertexTransitive G → 3 ≤ Fintype.card V →
    (¬ ∃ (_ : Group V) (S : Set V), ∀ x y : V, G.Adj x y ↔ x⁻¹ * y ∈ S) →
    ∀ (u v : V) (p : G.Walk u v), p.IsPath → p.length = G.dist u v → 3 ≤ p.length →
      (¬ ∃ φ : G ≃g G, (∀ x, G.Adj x (φ x)) ∧ (∀ x ∈ p.support, φ x ∉ p.support)) →
      (∀ (u' v' : V) (q : G.Walk u' v'), q.IsPath → q.length = G.dist u' v' → q.length < p.length →
        (G.induce {x | x ∉ q.support}).Connected) →
      (G.induce {x | x ∉ p.support}).Connected

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
    (hvt : OMA.S_gillibert_geodesic_deletion.IsVertexTransitive G)
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
    (hconn : G.Connected) (hvt : OMA.S_gillibert_geodesic_deletion.IsVertexTransitive G)
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
    (hconn : G.Connected) (hvt : OMA.S_gillibert_geodesic_deletion.IsVertexTransitive G)
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
    (hconn : G.Connected) (hvt : OMA.S_gillibert_geodesic_deletion.IsVertexTransitive G)
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

private lemma abelian_walk_from_list {A : Type*} [AddCommGroup A] {G : SimpleGraph A}
    {S : Set A} (hS : ∀ x y : A, G.Adj x y ↔ y - x ∈ S) :
    ∀ (x : A) (l : List A), (∀ s ∈ l, s ∈ S) →
      ∃ w : G.Walk x (x + l.sum), w.length = l.length := by
  intro x l
  induction l generalizing x with
  | nil =>
    intro _; exact ⟨Walk.nil.copy rfl (by simp), by rw [Walk.length_copy]; rfl⟩
  | cons s t ih =>
    intro hl
    have hs : s ∈ S := hl s (by simp)
    have hxs : G.Adj x (x + s) := (hS x (x + s)).2 (by simpa using hs)
    obtain ⟨w, hw⟩ := ih (x + s) (fun z hz => hl z (by simp [hz]))
    refine ⟨(Walk.cons hxs w).copy rfl (by simp [add_assoc]), by simp [hw]⟩

private lemma abelian_dist_le_sum {A : Type*} [AddCommGroup A] {G : SimpleGraph A}
    {S : Set A} (hS : ∀ x y : A, G.Adj x y ↔ y - x ∈ S)
    {x : A} {l : List A} (hl : ∀ s ∈ l, s ∈ S) :
    G.dist x (x + l.sum) ≤ l.length := by
  obtain ⟨w, hw⟩ := abelian_walk_from_list hS x l hl
  exact hw ▸ G.dist_le w

private lemma abelian_dist_le_finset_sum {A : Type*} [AddCommGroup A] {G : SimpleGraph A}
    {S : Set A} (hS : ∀ x y : A, G.Adj x y ↔ y - x ∈ S)
    {ι : Type*} (I : Finset ι) (f : ι → A) (hf : ∀ i ∈ I, f i ∈ S) :
    G.dist (0 : A) (∑ i ∈ I, f i) ≤ I.card := by
  have h1 : ∀ (l : List ι), (∀ i ∈ l, f i ∈ S) →
      G.dist (0 : A) (l.map f).sum ≤ l.length := by
    intro l hl
    have := abelian_dist_le_sum hS (x := (0 : A)) (l := l.map f) (by
      intro z hz; obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hz; exact hl i hi)
    simpa using this
  obtain ⟨l, hl_eq⟩ := Quotient.exists_rep I.1
  have hmem : ∀ i, i ∈ l ↔ i ∈ I := fun i => by
    change i ∈ l ↔ i ∈ I.1
    rw [← hl_eq]; rfl
  have hlen : l.length = I.card := by
    change l.length = Multiset.card I.1
    rw [← hl_eq]; rfl
  have hsum : (l.map f).sum = ∑ i ∈ I, f i := by
    change (l.map f).sum = (I.1.map f).sum
    rw [← hl_eq]; rfl
  rw [← hsum, ← hlen]
  exact h1 l (fun i hi => hf i ((hmem i).1 hi))

private lemma abelian_cayley_connected [Fintype V] [AddCommGroup V] {G : SimpleGraph V}
    {S : Set V} (hS : ∀ x y : V, G.Adj x y ↔ y - x ∈ S)
    (hconn : G.Connected) (hcard : 3 ≤ Fintype.card V) :
    ∀ (u v : V) (p : G.Walk u v), p.IsPath → p.length = G.dist u v →
      (G.induce {x | x ∉ p.support}).Connected := by
  have hS0 : (0 : V) ∉ S := fun h0 => G.loopless.irrefl (0 : V) ((hS 0 0).2 (by simpa using h0))
  have hSneg : ∀ s ∈ S, -s ∈ S := fun s hs => by
    have h1 : G.Adj (0 : V) s := (hS 0 s).2 (by simpa using hs)
    simpa using (hS s 0).1 h1.symm
  let htrans_iso : V → G ≃g G := fun c =>
    { toFun := fun x => x + c
      invFun := fun x => x - c
      left_inv := fun x => add_sub_cancel_right x c
      right_inv := fun x => sub_add_cancel x c
      map_rel_iff' := by
        intro x y
        show G.Adj (x + c) (y + c) ↔ G.Adj x y
        simp only [hS, add_sub_add_right_eq_sub] }
  have hvt : OMA.S_gillibert_geodesic_deletion.IsVertexTransitive G := fun u v =>
    ⟨htrans_iso (v - u), by show u + (v - u) = v; abel⟩
  by_contra hbad
  push Not at hbad
  have hex : ∃ L, ∃ (u v : V) (p : G.Walk u v), p.IsPath ∧ p.length = G.dist u v ∧
      p.length = L ∧ ¬ (G.induce {x | x ∉ p.support}).Connected := by
    obtain ⟨u, v, p, hp, hgeo, hnot⟩ := hbad
    exact ⟨p.length, u, v, p, hp, hgeo, rfl, hnot⟩
  set L := Nat.find hex
  obtain ⟨u₀, v₀, p₀, hp₀, hgeo₀, hL₀, hnot₀⟩ := Nat.find_spec hex
  change p₀.length = L at hL₀
  have hmin_all : ∀ (u' v' : V) (q : G.Walk u' v'), q.IsPath → q.length = G.dist u' v' →
      q.length < L → (G.induce {x | x ∉ q.support}).Connected := by
    intro u' v' q hq hqg hqlt
    by_contra hqn
    exact Nat.find_min hex hqlt ⟨u', v', q, hq, hqg, rfl, hqn⟩
  -- Shift p₀ by -u₀ so it starts at 0!
  let φ0 := htrans_iso (-u₀)
  let v : V := v₀ + -u₀
  let p : G.Walk (0 : V) v := (p₀.map φ0.toHom).copy (by show u₀ + -u₀ = 0; abel) rfl
  have hp : p.IsPath := by
    rw [Walk.isPath_def]
    have : p.support = p₀.support.map φ0 := by
      simp [p, Walk.support_copy, Walk.support_map]
    rw [this]
    exact hp₀.support_nodup.map φ0.injective
  have hplen : p.length = L := by simp [p, hL₀]
  have hgeo : p.length = G.dist (0 : V) v := by
    have h0 : φ0 u₀ = 0 := by show u₀ + -u₀ = 0; abel
    have hv' : φ0 v₀ = v := rfl
    calc p.length = p₀.length := by simp [p]
      _ = G.dist u₀ v₀ := hgeo₀
      _ = G.dist (φ0 u₀) (φ0 v₀) := (iso_dist_eq φ0 hconn u₀ v₀).symm
      _ = G.dist (0 : V) v := by rw [h0, hv']
  have hnot : ¬ (G.induce {x | x ∉ p.support}).Connected := by
    intro hc
    apply hnot₀
    refine induce_connected_of_iso φ0.symm (fun x => ?_) hc
    simp only [Set.mem_ofPred_eq, not_iff_not]
    have hsp : p.support = p₀.support.map φ0 := by
      simp [p, Walk.support_copy, Walk.support_map]
    rw [hsp, List.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
    · intro hx
      exact ⟨φ0.symm x, hx, φ0.apply_symm_apply x⟩
  have hL3 : 3 ≤ L := by
    by_contra hlt
    exact hnot (length_le_two_connected hconn hvt hcard p hp hgeo (by omega))
  -- Split G - V(p) into A ⊔ B
  have hne : ({x : V | x ∉ p.support}).Nonempty := exists_not_mem_geodesic hvt hcard p hp hgeo
  obtain ⟨A, B, hA, hB, _, hpart, hdAB, hnoAB⟩ := not_connected_induce_split hne hnot
  have hends := minimal_endpoint_touches_both p hp hgeo (by omega)
    (fun u' v' q hq hqg hqlt => hmin_all u' v' q hq hqg (by omega)) hA hB hpart hdAB hnoAB
  -- Define steps of p: step i = p.getVert (i+1) - p.getVert i
  let step : Fin L → V := fun i => p.getVert (i.1 + 1) - p.getVert i.1
  have hstep_S : ∀ i : Fin L, step i ∈ S := fun i =>
    (hS _ _).1 (p.adj_getVert_succ (by omega))
  have hgetVert_sum : ∀ k ≤ L, p.getVert k = ∑ i : Fin L with i.1 < k, step i := by
    intro k hk
    induction k with
    | zero => simp
    | succ k ih =>
      have hk' : k ≤ L := by omega
      have hfilt : (Finset.univ.filter (fun i : Fin L => i.1 < k + 1)) =
          insert ⟨k, by omega⟩ (Finset.univ.filter (fun i : Fin L => i.1 < k)) := by
        ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
        omega
      rw [hfilt, Finset.sum_insert (by simp), ← ih hk']
      simp [step, sub_add_cancel]
  have hv_sum : v = ∑ i : Fin L, step i := by
    have h1 := hgetVert_sum L le_rfl
    have h2 : p.getVert L = v := by rw [← hplen, p.getVert_length]
    rw [h2] at h1
    simpa using h1
  -- Abelian Subsum Lemma: for any I ⊆ Fin L with 2 ≤ I.card, ∑ i ∈ I, step i ≠ 0 and ∉ S!
  have hsubsum : ∀ (I : Finset (Fin L)), 2 ≤ I.card →
      (∑ i ∈ I, step i) ≠ 0 ∧ (∑ i ∈ I, step i) ∉ S := by
    intro I hI
    have hdecomp : (∑ i ∈ I, step i) + (∑ i ∈ Iᶜ, step i) = v := by
      rw [hv_sum, Finset.sum_add_sum_compl]
    constructor
    · intro h0
      rw [h0, zero_add] at hdecomp
      have hd := abelian_dist_le_finset_sum hS Iᶜ step (fun i _ => hstep_S i)
      rw [hdecomp, Finset.card_compl, Fintype.card_fin] at hd
      omega
    · intro hmem
      have hd1 := abelian_dist_le_finset_sum hS Iᶜ step (fun i _ => hstep_S i)
      have hadj : G.Adj (∑ i ∈ Iᶜ, step i) v := by
        rw [hS, ← hdecomp, add_sub_cancel_right]
        exact hmem
      have hd2 : G.dist (∑ i ∈ Iᶜ, step i) v ≤ 1 := G.dist_le (Walk.cons hadj Walk.nil)
      have htri := dist_triangle_of_reachable (hconn (0 : V) (∑ i ∈ Iᶜ, step i)) (hconn _ v)
      rw [Finset.card_compl, Fintype.card_fin] at hd1
      omega
  -- Corollary C1: for i ≠ j, step i + step j ≠ 0 and ∉ S
  have hC1 : ∀ i j : Fin L, i ≠ j → step i + step j ≠ 0 ∧ step i + step j ∉ S := by
    intro i j hij
    have h := hsubsum {i, j} (by rw [Finset.card_pair hij])
    rwa [Finset.sum_pair hij] at h
  -- Corollary C2: for pairwise distinct i, j, k, step i + step j + step k ≠ 0 and ∉ S
  have hC2 : ∀ i j k : Fin L, i ≠ j → i ≠ k → j ≠ k →
      step i + step j + step k ≠ 0 ∧ step i + step j + step k ∉ S := by
    intro i j k hij hik hjk
    have h := hsubsum {i, j, k} (by
      rw [Finset.card_insert_of_notMem (by simp [hij, hik]), Finset.card_pair hjk]; omega)
    rw [Finset.sum_insert (by simp [hij, hik]), Finset.sum_pair hjk, ← add_assoc] at h
    exact h
  -- Step 1: Every generator w ∈ S must be ± step i (W = ∅), else automorphism_step_connected!
  have hW_empty : ∀ w ∈ S, ∃ i : Fin L, w = step i ∨ w = -(step i) := by
    intro w hwS
    by_contra hno
    push Not at hno
    apply hnot
    refine automorphism_step_connected hconn p (htrans_iso w) (fun x => (hS x (x + w)).2 (by simpa using hwS)) ?_
    intro x hx hxw
    obtain ⟨i, hi, rfl⟩ := (mem_support_iff_getVert p x).1 hx
    obtain ⟨j, hj, hjeq⟩ := (mem_support_iff_getVert p (p.getVert i + w)).1 hxw
    have hadj : G.Adj (p.getVert i) (p.getVert j) := by
      rw [hjeq]; exact (hS _ _).2 (by simpa using hwS)
    rcases geodesic_adj_getVert p hgeo hi hj hadj with h | h
    · have hiL : i < L := by omega
      have hw_eq : w = step ⟨i, hiL⟩ := by
        simp only [step]
        have : p.getVert (i + 1) = p.getVert i + w := by rw [h, hjeq]
        rw [this, add_sub_cancel_left]
      exact (hno ⟨i, hiL⟩).1 hw_eq
    · have hjL : j < L := by omega
      have hw_eq : w = -(step ⟨j, hjL⟩) := by
        simp only [step]
        have : p.getVert (j + 1) + w = p.getVert j := by rw [h]; exact hjeq.symm
        exact eq_neg_of_add_eq_zero_left (by
          calc w + (p.getVert (j + 1) - p.getVert j)
              = (p.getVert (j + 1) + w) - p.getVert j := by abel
            _ = 0 := by rw [this, sub_self])
      exact (hno ⟨j, hjL⟩).2 hw_eq
  -- Helpers for steps 0, 1, 2
  let i0 : Fin L := ⟨0, by omega⟩
  let i1 : Fin L := ⟨1, by omega⟩
  let i2 : Fin L := ⟨2, by omega⟩
  let s0 : V := step i0
  let s1 : V := step i1
  let s2 : V := step i2
  have hstep0 : step i0 = s0 := rfl
  have hstep1 : step i1 = s1 := rfl
  have hstep2 : step i2 = s2 := rfl
  have hs0S : s0 ∈ S := hstep_S i0
  have hs1S : s1 ∈ S := hstep_S i1
  have hs0_eq : p.getVert 1 = s0 := by
    have := hgetVert_sum 1 (by omega)
    have hfilt : (Finset.univ.filter (fun i : Fin L => i.1 < 1)) = {i0} := by
      ext i; simp [i0, Fin.ext_iff]
    rw [hfilt, Finset.sum_singleton] at this
    exact this
  have hs01_eq : p.getVert 2 = s0 + s1 := by
    have := hgetVert_sum 2 (by omega)
    have hfilt : (Finset.univ.filter (fun i : Fin L => i.1 < 2)) = {i0, i1} := by
      ext i; simp [i0, i1, Fin.ext_iff]; omega
    have hne01 : i0 ≠ i1 := by simp [i0, i1]
    rw [hfilt, Finset.sum_pair hne01] at this
    exact this
  -- Every neighbor of 0 outside V(p) lies in A or B, and s0 is the ONLY neighbor of 0 in V(p)!
  have hS_split : ∀ x ∈ S, x ≠ s0 → x ∈ A ∨ x ∈ B := by
    intro x hxS hxne
    refine (hpart x).1 ?_
    intro hxp
    obtain ⟨j, hj, rfl⟩ := (mem_support_iff_getVert p x).1 hxp
    have hadj : G.Adj (p.getVert 0) (p.getVert j) := by
      simpa [hS] using hxS
    rcases geodesic_adj_getVert p hgeo (Nat.zero_le _) hj hadj with h | h
    · exact hxne (by rw [← h, hs0_eq])
    · omega
  -- Key 4-cycle equation at v₀ = 0: for all a ∈ S ∩ A and b ∈ S ∩ B, a + b ∈ {0, s0, s0 + s1}!
  have hsum_AB : ∀ a ∈ S, a ∈ A → ∀ b ∈ S, b ∈ B →
      a + b = 0 ∨ a + b = s0 ∨ a + b = s0 + s1 := by
    intro a haS haA b hbS hbB
    have h1 : G.Adj a (a + b) := (hS _ _).2 (by simpa using hbS)
    have h2 : G.Adj b (a + b) := (hS _ _).2 (by
      have : a + b - b = a := by abel
      rw [this]; exact haS)
    have hmem : a + b ∈ p.support := by
      by_contra hnotp
      rcases (hpart (a + b)).1 hnotp with h | h
      · exact hnoAB (a + b) h b hbB h2.symm
      · exact hnoAB a haA (a + b) h h1
    obtain ⟨j, hj, hjeq⟩ := (mem_support_iff_getVert p (a + b)).1 hmem
    have hd : G.dist (0 : V) (a + b) ≤ 2 := by
      have := abelian_dist_le_sum hS (x := (0 : V)) (l := [a, b]) (by simp [haS, hbS])
      simpa using this
    have hdj : G.dist (0 : V) (p.getVert j) = j := by
      simpa using geodesic_dist_getVert p hgeo (Nat.zero_le _) hj
    have hjle : j ≤ 2 := by rw [← hjeq] at hd; omega
    have hj_cases : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases hj_cases with rfl | rfl | rfl
    · left; simpa using hjeq.symm
    · right; left; rw [← hjeq, hs0_eq]
    · right; right; rw [← hjeq, hs01_eq]
  -- Also note: any neighbor of v outside V(p) lies in A or B, and endpoints have neighbors in both A and B!
  have hA0 : ∃ a ∈ S, a ∈ A := by
    obtain ⟨a, haA, h0a⟩ := hends.1
    exact ⟨a, by simpa [hS] using h0a, haA⟩
  have hB0 : ∃ b ∈ S, b ∈ B := by
    obtain ⟨b, hbB, h0b⟩ := hends.2.1
    exact ⟨b, by simpa [hS] using h0b, hbB⟩
  -- Helper: if all neighbors of v outside V(p) are connected in G - V(p) to a single vertex z₀ ∉ V(p), contradiction!
  have hv_same_comp : ∀ (z₀ : V) (hz₀ : z₀ ∉ p.support),
      (∀ t ∈ S, ∀ (ht : v + t ∉ p.support),
        (G.induce {x | x ∉ p.support}).Reachable ⟨v + t, ht⟩ ⟨z₀, hz₀⟩) → False := by
    intro z₀ hz₀ hall
    obtain ⟨a, haA, hva⟩ := hends.2.2.1
    obtain ⟨b, hbB, hvb⟩ := hends.2.2.2
    have haS : a - v ∈ S := (hS v a).1 hva
    have hbS : b - v ∈ S := (hS v b).1 hvb
    have ha_eq : v + (a - v) = a := add_sub_cancel v a
    have hb_eq : v + (b - v) = b := add_sub_cancel v b
    have ha_notp : v + (a - v) ∉ p.support := by rw [ha_eq]; exact (hpart a).2 (Or.inl haA)
    have hb_notp : v + (b - v) ∉ p.support := by rw [hb_eq]; exact (hpart b).2 (Or.inr hbB)
    have hreach := (hall (a - v) haS ha_notp).trans (hall (b - v) hbS hb_notp).symm
    obtain ⟨w, hwp⟩ := (walk_induce_iff_exists_walk ha_notp hb_notp).1 hreach
    have hstay := walk_stay_in_part hnoAB w (by rw [ha_eq]; exact haA) (fun z hz => (hpart z).1 (hwp z hz))
    exact Finset.disjoint_left.1 hdAB (hstay _ w.end_mem_support) (by rw [hb_eq]; exact hbB)
  -- Helper: check if v + x ∈ p.support when dist v (v + x) ≤ 2!
  have hv_mem_p_of_dist2 : ∀ x : V, G.dist v (v + x) ≤ 2 → v + x ∈ p.support →
      x = 0 ∨ x = -(step ⟨L - 1, by omega⟩) ∨
      x = -(step ⟨L - 2, by omega⟩ + step ⟨L - 1, by omega⟩) := by
    intro x hdx hxmem
    obtain ⟨j, hj, hjeq⟩ := (mem_support_iff_getVert p (v + x)).1 hxmem
    have hdj : G.dist (p.getVert j) v = L - j := by
      have h := geodesic_dist_getVert p hgeo hj le_rfl
      rw [p.getVert_length, hplen] at h
      exact h
    rw [SimpleGraph.dist_comm, hjeq] at hdj
    have hj_cases : j = L ∨ j = L - 1 ∨ j = L - 2 := by omega
    have htail1 : p.getVert (L - 1) = v - step ⟨L - 1, by omega⟩ := by
      have h1 : p.getVert L = v := by rw [← hplen, p.getVert_length]
      have hL1 : L - 1 + 1 = L := by omega
      have h2 : step ⟨L - 1, by omega⟩ = p.getVert L - p.getVert (L - 1) := by
        simp only [step, hL1]
      rw [h1] at h2; rw [h2]; abel
    have htail2 : p.getVert (L - 2) = v - (step ⟨L - 2, by omega⟩ + step ⟨L - 1, by omega⟩) := by
      have hL2 : L - 2 + 1 = L - 1 := by omega
      have h1 : step ⟨L - 2, by omega⟩ = p.getVert (L - 1) - p.getVert (L - 2) := by
        simp only [step, hL2]
      rw [htail1] at h1
      have : p.getVert (L - 2) = v - step ⟨L - 1, by omega⟩ - step ⟨L - 2, by omega⟩ := by
        rw [h1]; abel
      rw [this]; abel
    rcases hj_cases with rfl | rfl | rfl
    · left
      have h1 : p.getVert L = v := by rw [← hplen, p.getVert_length]
      rw [h1] at hjeq
      exact add_left_cancel (hjeq.symm.trans (add_zero v).symm)
    · right; left
      rw [htail1] at hjeq
      have : v + x = v + -step ⟨L - 1, by omega⟩ := by rw [← hjeq]; abel
      exact add_left_cancel this
    · right; right
      rw [htail2] at hjeq
      have : v + x = v + -(step ⟨L - 2, by omega⟩ + step ⟨L - 1, by omega⟩) := by rw [← hjeq]; abel
      exact add_left_cancel this
  -- Symmetrized Case A (2 * s0 ≠ 0) helper: assumes -s0 ∈ B (swap A/B at call site if -s0 ∈ A)
  have hCaseA : s0 + s0 ≠ 0 →
      ∀ (X Y : Finset V), (∀ x, x ∉ p.support ↔ x ∈ X ∨ x ∈ Y) → Disjoint X Y →
        (∀ x ∈ X, ∀ y ∈ Y, ¬ G.Adj x y) →
        (∃ a ∈ S, a ∈ X) → (-s0 ∈ Y) →
        (∀ a ∈ S, a ∈ X → ∀ b ∈ S, b ∈ Y → a + b = 0 ∨ a + b = s0 ∨ a + b = s0 + s1) → False := by
    intro h2s0 X Y hpartXY hdXY hnoXY hX0 hnegY hsumXY
    have hXsub : ∀ u ∈ S, u ∈ X → u = s0 + s0 ∨ u = s0 + s0 + s1 := by
      intro u huS huX
      have hns0 : -s0 ∈ S := hSneg s0 (hstep_S i0)
      rcases hsumXY u huS huX (-s0) hns0 hnegY with h | h | h
      · exfalso
        have hus0 : u = s0 := eq_of_sub_eq_zero (by simpa [sub_eq_add_neg] using h)
        exact ((hpartXY u).2 (Or.inl huX)) (hus0 ▸ hs0_eq ▸ p.getVert_mem_support 1)
      · left
        calc u = (u + -s0) + s0 := by abel
          _ = s0 + s0 := by rw [h]
      · right
        calc u = (u + -s0) + s0 := by abel
          _ = (s0 + s1) + s0 := by rw [h]
          _ = s0 + s0 + s1 := by abel
    -- Subcase A1: s1 = s0
    by_cases hs10 : s1 = s0
    · obtain ⟨u, huS, huX⟩ := hX0
      have hu_eq : u = s0 + s0 + s0 := by
        rcases hXsub u huS huX with h | h
        · exfalso
          have : u = p.getVert 2 := by rw [hs01_eq, hs10, h]
          exact ((hpartXY u).2 (Or.inl huX)) (this ▸ p.getVert_mem_support 2)
        · rw [hs10] at h; exact h
      subst hu_eq
      have h3s0_S : s0 + s0 + s0 ∈ S := huS
      -- 3*s0 must be +step k for some k ≥ 2
      have h3s0_step : ∃ k : Fin L, step k = s0 + s0 + s0 := by
        obtain ⟨k, hk | hk⟩ := hW_empty _ h3s0_S
        · exact ⟨k, hk.symm⟩
        · exfalso
          have hkne0 : k ≠ i0 := by
            intro h; subst h
            have h4 : s0 + s0 + s0 + s0 = 0 := by
              have : s0 + s0 + s0 + s0 = (-s0) + s0 := by rw [← hk]
              simpa using this
            have h3eq : s0 + s0 + s0 = -s0 := eq_neg_of_add_eq_zero_left h4
            exact Finset.disjoint_left.1 hdXY huX (h3eq ▸ hnegY)
          have hkne1 : k ≠ i1 := by
            intro h; subst h
            have : s0 + s0 + s0 = -s0 := by rw [hk, hstep1, hs10]
            exact Finset.disjoint_left.1 hdXY huX (this ▸ hnegY)
          have hc2 := (hC2 i0 i1 k (by simp [i0, i1]) hkne0.symm hkne1.symm).2
          have hsum_eq : step i0 + step i1 + step k = -s0 := by
            have hk' : step k = -(s0 + s0 + s0) := by rw [hk, neg_neg]
            rw [hstep0, hstep1, hs10, hk']; abel
          exact hc2 (hsum_eq ▸ hSneg s0 hs0S)
      -- Every element of S is in {s0, -s0, 3s0, -3s0}
      have hS_sub : ∀ y ∈ S, y = s0 ∨ y = -s0 ∨ y = s0 + s0 + s0 ∨ y = -(s0 + s0 + s0) := by
        intro y hyS
        by_cases hys0 : y = s0
        · exact Or.inl hys0
        · have hyXY : y ∈ X ∨ y ∈ Y := (hpartXY y).1 (by
            intro hyp
            obtain ⟨j, hj, rfl⟩ := (mem_support_iff_getVert p y).1 hyp
            have hadj : G.Adj (p.getVert 0) (p.getVert j) := by simpa [hS] using hyS
            rcases geodesic_adj_getVert p hgeo (Nat.zero_le _) hj hadj with h | h
            · exact hys0 (by rw [← h, hs0_eq])
            · omega)
          rcases hyXY with hyX | hyY
          · rcases hXsub y hyS hyX with h | h
            · exfalso
              have : y = p.getVert 2 := by rw [hs01_eq, hs10, h]
              exact ((hpartXY y).2 (Or.inl hyX)) (this ▸ p.getVert_mem_support 2)
            · rw [hs10] at h; exact Or.inr (Or.inr (Or.inl h))
          · rcases hsumXY _ h3s0_S huX y hyS hyY with h | h | h
            · right; right; right; exact eq_neg_of_add_eq_zero_right h
            · exfalso
              have hy2 : y = -(s0 + s0) := by
                have : (s0 + s0 + s0) + y - s0 = 0 := by rw [h, sub_self]
                exact eq_neg_of_add_eq_zero_right (by
                  calc (s0 + s0) + y = (s0 + s0 + s0) + y - s0 := by abel
                    _ = 0 := this)
              have h2S : s0 + s0 ∈ S := by
                have := hSneg y hyS; rw [hy2, neg_neg] at this; exact this
              exact (hC1 i0 i1 (by simp [i0, i1])).2 (by rw [hstep0, hstep1, hs10]; exact h2S)
            · right; left
              rw [hs10] at h
              exact eq_neg_of_add_eq_zero_right (by
                calc s0 + y = (s0 + s0 + s0) + y - (s0 + s0) := by abel
                  _ = 0 := by rw [h, sub_self])
      -- Every step i for i ≥ 2 equals 3*s0!
      have hstep_ge2 : ∀ i : Fin L, 2 ≤ i.1 → step i = s0 + s0 + s0 := by
        intro i hi
        obtain ⟨k, hk⟩ := h3s0_step
        rcases hS_sub (step i) (hstep_S i) with h | h | h | h
        · exfalso
          have hne0 : i0 ≠ i := by intro e; rw [← e] at hi; simp [i0] at hi
          have hne1 : i1 ≠ i := by intro e; rw [← e] at hi; simp [i1] at hi
          have hc2 := (hC2 i0 i1 i (by simp [i0, i1]) hne0 hne1).2
          have : step i0 + step i1 + step i = s0 + s0 + s0 := by rw [hstep0, hstep1, hs10, h]
          exact hc2 (this ▸ h3s0_S)
        · exfalso
          have hne0 : i0 ≠ i := by intro e; rw [← e] at hi; simp [i0] at hi
          exact (hC1 i0 i hne0).1 (by rw [hstep0, h, add_neg_cancel])
        · exact h
        · exfalso
          have hnek : k ≠ i := by
            intro e; subst e
            have h6 : (s0 + s0 + s0) + (s0 + s0 + s0) = 0 := by
              calc (s0 + s0 + s0) + (s0 + s0 + s0)
                  = step k + (s0 + s0 + s0) := by rw [hk]
                _ = -(s0 + s0 + s0) + (s0 + s0 + s0) := by rw [h]
                _ = 0 := neg_add_cancel _
            have hstep_k : step i0 + step i1 + step k = s0 + s0 + s0 + s0 + s0 := by
              rw [hstep0, hstep1, hs10, hk]; abel
            have hne0k : i0 ≠ k := by
              intro e; subst e
              exact h2s0 (by
                calc s0 + s0 = (s0 + s0 + s0) - s0 := by abel
                  _ = step i0 - s0 := by rw [← hk]
                  _ = 0 := by rw [hstep0, sub_self])
            have hne1k : i1 ≠ k := by
              intro e; subst e
              exact h2s0 (by
                calc s0 + s0 = (s0 + s0 + s0) - s0 := by abel
                  _ = step i1 - s0 := by rw [← hk]
                  _ = 0 := by rw [hstep1, hs10, sub_self])
            have hc2 := (hC2 i0 i1 k (by simp [i0, i1]) hne0k hne1k).2
            have h5eq : step i0 + step i1 + step k = -s0 := eq_neg_of_add_eq_zero_left (by
              calc (step i0 + step i1 + step k) + s0
                  = (s0 + s0 + s0) + (s0 + s0 + s0) := by rw [hstep_k]; abel
                _ = 0 := h6)
            exact hc2 (h5eq ▸ hSneg s0 hs0S)
          exact (hC1 k i hnek).1 (by rw [hk, h, add_neg_cancel])
      -- Now at v = p.getVert L, all neighbors of v outside V(p) connect to v + 3*s0!
      have hlast : step ⟨L - 1, by omega⟩ = s0 + s0 + s0 := hstep_ge2 ⟨L - 1, by omega⟩ (by dsimp; omega)
      have hv_3s0_notp : v + (s0 + s0 + s0) ∉ p.support := by
        intro hmem
        have hd1 : G.dist v (v + (s0 + s0 + s0)) ≤ 2 := by
          have hd := G.dist_le (Walk.cons ((hS v (v + (s0 + s0 + s0))).2 (by simpa using h3s0_S)) Walk.nil)
          simp only [Walk.length_cons, Walk.length_nil] at hd
          omega
        rcases hv_mem_p_of_dist2 (s0 + s0 + s0) hd1 hmem with h | h | h
        · exact hS0 (h ▸ h3s0_S)
        · -- 6*s0 = 0 => s0 + s0 + 3*s0 = -s0 ∈ S
          rw [hlast] at h
          have h6 : (s0 + s0 + s0) + (s0 + s0 + s0) = 0 := by
            calc (s0 + s0 + s0) + (s0 + s0 + s0)
                = -(s0 + s0 + s0) + (s0 + s0 + s0) := congrArg (· + (s0 + s0 + s0)) h
              _ = 0 := neg_add_cancel _
          have h2 : step i2 = s0 + s0 + s0 := hstep_ge2 i2 (by simp [i2])
          have hc2 := (hC2 i0 i1 i2 (by simp [i0, i1]) (by simp [i0, i2]) (by simp [i1, i2])).2
          have h5 : step i0 + step i1 + step i2 = -s0 := eq_neg_of_add_eq_zero_left (by
            calc step i0 + step i1 + step i2 + s0
                = (s0 + s0 + s0) + (s0 + s0 + s0) := by rw [hstep0, hstep1, hs10, h2]; abel
              _ = 0 := h6)
          exact hc2 (h5 ▸ hSneg s0 hs0S)
        · -- s0+s0+s0 = -(step (L-2) + 3s0)
          rw [hlast] at h
          by_cases hL3eq : L = 3
          · have hL2 : step ⟨L - 2, by omega⟩ = s0 := by
              have : (⟨L - 2, by omega⟩ : Fin L) = i1 := Fin.ext (by simp [i1, hL3eq])
              rw [this, hstep1]; exact hs10
            rw [hL2] at h
            have h7 : s0 + s0 + s0 + s0 + s0 + s0 + s0 = 0 := by
              calc s0 + s0 + s0 + s0 + s0 + s0 + s0
                  = (s0 + s0 + s0) + (s0 + (s0 + s0 + s0)) := by abel
                _ = -(s0 + (s0 + s0 + s0)) + (s0 + (s0 + s0 + s0)) := congrArg (· + (s0 + (s0 + s0 + s0))) h
                _ = 0 := neg_add_cancel _
            have hv5 : v = s0 + s0 + (s0 + s0 + s0) := by
              rw [hv_sum]
              have hu : (Finset.univ : Finset (Fin L)) = {i0, i1, i2} := by
                ext x
                simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff, i0, i1, i2, true_iff]
                have hxL := x.2; omega
              rw [hu, Finset.sum_insert (by simp [i0, i1, i2]), Finset.sum_pair (by simp [i1, i2])]
              rw [hstep0, hstep1, hs10, hstep_ge2 i2 (by simp [i2])]; abel
            have hv_neg2 : v = (-s0) + (-s0) := by
              have : v + (s0 + s0) = 0 := by rw [hv5]; convert h7 using 1; abel
              have := eq_neg_of_add_eq_zero_left this
              rw [this]; abel
            have hd2 := abelian_dist_le_sum hS (x := (0 : V)) (l := [-s0, -s0]) (by simp [hSneg s0 hs0S])
            simp only [List.sum_cons, List.sum_nil, add_zero, zero_add, List.length_cons, List.length_nil] at hd2
            rw [← hv_neg2] at hd2
            omega
          · have hL4 : 4 ≤ L := by omega
            have hL2 : step ⟨L - 2, by omega⟩ = s0 + s0 + s0 := hstep_ge2 ⟨L - 2, by omega⟩ (by dsimp; omega)
            rw [hL2] at h
            have h9 : (s0 + s0 + s0) + (s0 + s0 + s0) + (s0 + s0 + s0) = 0 := by
              calc (s0 + s0 + s0) + (s0 + s0 + s0) + (s0 + s0 + s0)
                  = (s0 + s0 + s0) + ((s0 + s0 + s0) + (s0 + s0 + s0)) := by abel
                _ = -((s0 + s0 + s0) + (s0 + s0 + s0)) + ((s0 + s0 + s0) + (s0 + s0 + s0)) :=
                    congrArg (· + ((s0 + s0 + s0) + (s0 + s0 + s0))) h
                _ = 0 := neg_add_cancel _
            have h2 := hstep_ge2 i2 (by simp [i2])
            let i3 : Fin L := ⟨3, by omega⟩
            have h3 := hstep_ge2 i3 (by simp [i3])
            have hsub3 := (hsubsum {i0, i1, i2, i3} (by
              rw [Finset.card_insert_of_notMem (by simp [i0, i1, i2, i3]),
                  Finset.card_insert_of_notMem (by simp [i1, i2, i3]),
                  Finset.card_pair (by simp [i2, i3])]; omega)).2
            rw [Finset.sum_insert (by simp [i0, i1, i2, i3]),
                Finset.sum_insert (by simp [i1, i2, i3]),
                Finset.sum_pair (by simp [i2, i3])] at hsub3
            have h8eq : step i0 + (step i1 + (step i2 + step i3)) = -s0 := eq_neg_of_add_eq_zero_left (by
              calc step i0 + (step i1 + (step i2 + step i3)) + s0
                  = (s0 + s0 + s0) + (s0 + s0 + s0) + (s0 + s0 + s0) := by rw [hstep0, hstep1, hs10, h2, h3]; abel
                _ = 0 := h9)
            exact hsub3 (h8eq ▸ hSneg s0 hs0S)
      have hv_2s0_notp : v + (s0 + s0) ∉ p.support := by
        intro hmem
        have hd2 : G.dist v (v + (s0 + s0)) ≤ 2 := by
          have := abelian_dist_le_sum hS (x := v) (l := [s0 + s0 + s0, -s0])
            (by simp [h3s0_S, hSneg s0 hs0S])
          have heq : v + ((s0 + s0 + s0) + (-s0 + 0)) = v + (s0 + s0) := by abel
          simpa [heq] using this
        rcases hv_mem_p_of_dist2 (s0 + s0) hd2 hmem with h | h | h
        · exact h2s0 h
        · rw [hlast] at h
          have h5 : step i0 + step i1 + step i2 = 0 := by
            rw [hstep0, hstep1, hs10, hstep_ge2 i2 (by simp [i2])]
            calc s0 + s0 + (s0 + s0 + s0)
                = (s0 + s0) + (s0 + s0 + s0) := by abel
              _ = -(s0 + s0 + s0) + (s0 + s0 + s0) := congrArg (· + (s0 + s0 + s0)) h
              _ = 0 := neg_add_cancel _
          exact (hC2 i0 i1 i2 (by simp [i0, i1]) (by simp [i0, i2]) (by simp [i1, i2])).1 h5
        · rw [hlast] at h
          by_cases hL3eq : L = 3
          · have hL2 : step ⟨L - 2, by omega⟩ = s0 := by
              have : (⟨L - 2, by omega⟩ : Fin L) = i1 := Fin.ext (by simp [i1, hL3eq])
              rw [this, hstep1]; exact hs10
            rw [hL2] at h
            have h6 : (s0 + s0 + s0) + (s0 + s0 + s0) = 0 := by
              calc (s0 + s0 + s0) + (s0 + s0 + s0)
                  = (s0 + s0) + (s0 + (s0 + s0 + s0)) := by abel
                _ = -(s0 + (s0 + s0 + s0)) + (s0 + (s0 + s0 + s0)) := congrArg (· + (s0 + (s0 + s0 + s0))) h
                _ = 0 := neg_add_cancel _
            have hc2 := (hC2 i0 i1 i2 (by simp [i0, i1]) (by simp [i0, i2]) (by simp [i1, i2])).2
            have h5 : step i0 + step i1 + step i2 = -s0 := eq_neg_of_add_eq_zero_left (by
              calc step i0 + step i1 + step i2 + s0
                  = (s0 + s0 + s0) + (s0 + s0 + s0) := by rw [hstep0, hstep1, hs10, hstep_ge2 i2 (by simp [i2])]; abel
                _ = 0 := h6)
            exact hc2 (h5 ▸ hSneg s0 hs0S)
          · have hL4 : 4 ≤ L := by omega
            have hL2 : step ⟨L - 2, by omega⟩ = s0 + s0 + s0 := hstep_ge2 ⟨L - 2, by omega⟩ (by dsimp; omega)
            rw [hL2] at h
            let i3 : Fin L := ⟨3, by omega⟩
            have hsub4 := (hsubsum {i0, i1, i2, i3} (by
              rw [Finset.card_insert_of_notMem (by simp [i0, i1, i2, i3]),
                  Finset.card_insert_of_notMem (by simp [i1, i2, i3]),
                  Finset.card_pair (by simp [i2, i3])]; omega)).1
            rw [Finset.sum_insert (by simp [i0, i1, i2, i3]),
                Finset.sum_insert (by simp [i1, i2, i3]),
                Finset.sum_pair (by simp [i2, i3])] at hsub4
            apply hsub4
            rw [hstep0, hstep1, hs10, hstep_ge2 i2 (by simp [i2]), hstep_ge2 i3 (by simp [i3])]
            calc s0 + (s0 + ((s0 + s0 + s0) + (s0 + s0 + s0)))
                = (s0 + s0) + ((s0 + s0 + s0) + (s0 + s0 + s0)) := by abel
              _ = -((s0 + s0 + s0) + (s0 + s0 + s0)) + ((s0 + s0 + s0) + (s0 + s0 + s0)) :=
                  congrArg (· + ((s0 + s0 + s0) + (s0 + s0 + s0))) h
              _ = 0 := neg_add_cancel _
      have hv_4s0_notp : v + (s0 + s0 + s0 + s0) ∉ p.support := by
        intro hmem
        have hd2 : G.dist v (v + (s0 + s0 + s0 + s0)) ≤ 2 := by
          have := abelian_dist_le_sum hS (x := v) (l := [s0 + s0 + s0, s0])
            (by simp [h3s0_S, hs0S])
          have heq : v + ((s0 + s0 + s0) + (s0 + 0)) = v + (s0 + s0 + s0 + s0) := by abel
          simpa [heq] using this
        rcases hv_mem_p_of_dist2 (s0 + s0 + s0 + s0) hd2 hmem with h | h | h
        · have h3eq : s0 + s0 + s0 = -s0 := eq_neg_of_add_eq_zero_left h
          exact Finset.disjoint_left.1 hdXY huX (h3eq ▸ hnegY)
        · rw [hlast] at h
          have h7 : s0 + s0 + s0 + s0 + s0 + s0 + s0 = 0 := by
            calc s0 + s0 + s0 + s0 + s0 + s0 + s0
                = (s0 + s0 + s0 + s0) + (s0 + s0 + s0) := by abel
              _ = -(s0 + s0 + s0) + (s0 + s0 + s0) := congrArg (· + (s0 + s0 + s0)) h
              _ = 0 := neg_add_cancel _
          by_cases hL3eq : L = 3
          · have hv5 : v = s0 + s0 + (s0 + s0 + s0) := by
              rw [hv_sum]
              have hu : (Finset.univ : Finset (Fin L)) = {i0, i1, i2} := by
                ext x
                simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff, i0, i1, i2, true_iff]
                have hxL := x.2; omega
              rw [hu, Finset.sum_insert (by simp [i0, i1, i2]), Finset.sum_pair (by simp [i1, i2])]
              rw [hstep0, hstep1, hs10, hstep_ge2 i2 (by simp [i2])]; abel
            have hv_neg2 : v = (-s0) + (-s0) := by
              have : v + (s0 + s0) = 0 := by rw [hv5]; convert h7 using 1; abel
              have := eq_neg_of_add_eq_zero_left this
              rw [this]; abel
            have hd2' := abelian_dist_le_sum hS (x := (0 : V)) (l := [-s0, -s0]) (by simp [hSneg s0 hs0S])
            simp only [List.sum_cons, List.sum_nil, add_zero, zero_add, List.length_cons, List.length_nil] at hd2'
            rw [← hv_neg2] at hd2'
            omega
          · have hL4 : 4 ≤ L := by omega
            let i3 : Fin L := ⟨3, by omega⟩
            have hc1 := (hC1 i2 i3 (by simp [i2, i3])).2
            have h6eq : step i2 + step i3 = -s0 := eq_neg_of_add_eq_zero_left (by
              rw [hstep_ge2 i2 (by simp [i2]), hstep_ge2 i3 (by simp [i3])]
              convert h7 using 1; abel)
            exact hc1 (h6eq ▸ hSneg s0 hs0S)
        · rw [hlast] at h
          by_cases hL3eq : L = 3
          · have hL2 : step ⟨L - 2, by omega⟩ = s0 := by
              have : (⟨L - 2, by omega⟩ : Fin L) = i1 := Fin.ext (by simp [i1, hL3eq])
              rw [this, hstep1]; exact hs10
            rw [hL2] at h
            have h8 : s0 + s0 + s0 + s0 + s0 + s0 + s0 + s0 = 0 := by
              calc s0 + s0 + s0 + s0 + s0 + s0 + s0 + s0
                  = (s0 + s0 + s0 + s0) + (s0 + (s0 + s0 + s0)) := by abel
                _ = -(s0 + (s0 + s0 + s0)) + (s0 + (s0 + s0 + s0)) := by rw [h]
                _ = 0 := neg_add_cancel _
            have hc2 := (hC2 i0 i1 i2 (by simp [i0, i1]) (by simp [i0, i2]) (by simp [i1, i2])).2
            have h5eq : step i0 + step i1 + step i2 = -(s0 + s0 + s0) := eq_neg_of_add_eq_zero_left (by
              rw [hstep0, hstep1, hs10, hstep_ge2 i2 (by simp [i2])]
              convert h8 using 1; abel)
            exact hc2 (h5eq ▸ hSneg _ h3s0_S)
          · have hL4 : 4 ≤ L := by omega
            have hL2 : step ⟨L - 2, by omega⟩ = s0 + s0 + s0 := hstep_ge2 ⟨L - 2, by omega⟩ (by dsimp; omega)
            rw [hL2] at h
            have h10 : (s0 + s0 + s0 + s0) + ((s0 + s0 + s0) + (s0 + s0 + s0)) = 0 := by
              calc (s0 + s0 + s0 + s0) + ((s0 + s0 + s0) + (s0 + s0 + s0))
                  = -((s0 + s0 + s0) + (s0 + s0 + s0)) + ((s0 + s0 + s0) + (s0 + s0 + s0)) := by rw [h]
                _ = 0 := neg_add_cancel _
            let i3 : Fin L := ⟨3, by omega⟩
            have h4sum : p.getVert 4 = (-s0) + (-s0) := by
              have hg := hgetVert_sum 4 hL4
              have hfilt : (Finset.univ.filter (fun i : Fin L => i.1 < 4)) = {i0, i1, i2, i3} := by
                ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and,
                  Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff, i0, i1, i2, i3]
                omega
              rw [hfilt, Finset.sum_insert (by simp [i0, i1, i2, i3]),
                  Finset.sum_insert (by simp [i1, i2, i3]),
                  Finset.sum_pair (by simp [i2, i3]), hstep0, hstep1, hs10,
                  hstep_ge2 i2 (by simp [i2]), hstep_ge2 i3 (by simp [i3])] at hg
              have : p.getVert 4 + (s0 + s0) = 0 := by rw [hg]; convert h10 using 1; abel
              have := eq_neg_of_add_eq_zero_left this
              rw [this]; abel
            have hd4 := geodesic_dist_getVert p hgeo (Nat.zero_le 4) (by omega)
            simp only [Walk.getVert_zero, Nat.sub_zero] at hd4
            have hd2' := abelian_dist_le_sum hS (x := (0 : V)) (l := [-s0, -s0]) (by simp [hSneg s0 hs0S])
            simp only [List.sum_cons, List.sum_nil, add_zero, zero_add, List.length_cons, List.length_nil] at hd2'
            rw [← h4sum, hd4] at hd2'
            omega
      -- Every neighbor v + t (∉ V(p)) reaches v + 3*s0 in G - V(p)!
      refine hv_same_comp (v + (s0 + s0 + s0)) hv_3s0_notp (fun t htS ht_notp => ?_)
      rcases hS_sub t htS with rfl | rfl | rfl | rfl
      · -- t = s0: v + s0 ~ v + 4s0 ~ v + 3s0
        have h1 : G.Adj (v + s0) (v + (s0 + s0 + s0 + s0)) := (hS _ _).2 (by
          have : v + (s0 + s0 + s0 + s0) - (v + s0) = s0 + s0 + s0 := by abel
          rw [this]; exact h3s0_S)
        have h2 : G.Adj (v + (s0 + s0 + s0 + s0)) (v + (s0 + s0 + s0)) := (hS _ _).2 (by
          have : v + (s0 + s0 + s0) - (v + (s0 + s0 + s0 + s0)) = -s0 := by abel
          rw [this]; exact hSneg s0 (hstep_S i0))
        exact (Adj.reachable (show (G.induce _).Adj ⟨v + s0, ht_notp⟩ ⟨v + (s0 + s0 + s0 + s0), hv_4s0_notp⟩ from h1)).trans
          (Adj.reachable (show (G.induce _).Adj ⟨v + (s0 + s0 + s0 + s0), hv_4s0_notp⟩ ⟨v + (s0 + s0 + s0), hv_3s0_notp⟩ from h2))
      · -- t = -s0: v + (-s0) ~ v + 2s0 ~ v + 3s0
        have h1 : G.Adj (v + -s0) (v + (s0 + s0)) := (hS _ _).2 (by
          have : v + (s0 + s0) - (v + -s0) = s0 + s0 + s0 := by abel
          rw [this]; exact h3s0_S)
        have h2 : G.Adj (v + (s0 + s0)) (v + (s0 + s0 + s0)) := (hS _ _).2 (by
          have : v + (s0 + s0 + s0) - (v + (s0 + s0)) = s0 := by abel
          rw [this]; exact hstep_S i0)
        exact (Adj.reachable (show (G.induce _).Adj ⟨v + -s0, ht_notp⟩ ⟨v + (s0 + s0), hv_2s0_notp⟩ from h1)).trans
          (Adj.reachable (show (G.induce _).Adj ⟨v + (s0 + s0), hv_2s0_notp⟩ ⟨v + (s0 + s0 + s0), hv_3s0_notp⟩ from h2))
      · exact Reachable.refl _
      · -- t = -(3s0): v - 3s0 = p.getVert (L - 1) ∈ p.support!
        exfalso
        apply ht_notp
        have h1 : p.getVert L = v := by rw [← hplen, p.getVert_length]
        have hL1 : L - 1 + 1 = L := by omega
        have h2 : step ⟨L - 1, by omega⟩ = p.getVert L - p.getVert (L - 1) := by
          simp only [step, hL1]
        rw [h1, hlast] at h2
        have : v + -(s0 + s0 + s0) = p.getVert (L - 1) := by rw [h2]; abel
        rw [this]
        exact p.getVert_mem_support (L - 1)
    -- Subcase A2: s1 ≠ s0
    · have hs1XY : s1 ∈ X ∨ s1 ∈ Y := (hpartXY s1).1 (by
        intro hmem
        obtain ⟨j, hj, hjeq⟩ := (mem_support_iff_getVert p s1).1 hmem
        have hadj : G.Adj (p.getVert 0) (p.getVert j) := by rw [hjeq]; simpa [hS] using hs1S
        rcases geodesic_adj_getVert p hgeo (Nat.zero_le _) hj hadj with h | h
        · exact hs10 (by rw [← hjeq, ← h, hs0_eq])
        · omega)
      rcases hs1XY with hs1X | hs1Y
      · -- Subcase A2a: s1 ∈ X => s1 = 2*s0!
        have hs1_eq : s1 = s0 + s0 := by
          rcases hXsub s1 hs1S hs1X with h | h
          · exact h
          · exfalso
            have : s0 + s0 = 0 := by
              have := congrArg (· - s1) h
              simpa [add_sub_cancel_right] using this.symm
            exact h2s0 this
        have h2s0_S : s0 + s0 ∈ S := hs1_eq ▸ hs1S
        -- Every y ∈ Y satisfies y ∈ {-s0, -2s0}
        have hYsub : ∀ y ∈ S, y ∈ Y → y = -s0 ∨ y = -(s0 + s0) := by
          intro y hyS hyY
          rcases hsumXY s1 hs1S hs1X y hyS hyY with h | h | h
          · right; rw [hs1_eq] at h; exact eq_neg_of_add_eq_zero_right h
          · left; rw [hs1_eq] at h
            exact eq_neg_of_add_eq_zero_right (by
              calc s0 + y = (s0 + s0) + y - s0 := by abel
                _ = 0 := by rw [h, sub_self])
          · exfalso
            rw [hs1_eq] at h
            have hys0 : y = s0 := by
              calc y = (s0 + s0 + y) - (s0 + s0) := by abel
                _ = (s0 + (s0 + s0)) - (s0 + s0) := by rw [h]
                _ = s0 := by abel
            exact ((hpartXY y).2 (Or.inr hyY)) (hys0 ▸ hs0_eq ▸ p.getVert_mem_support 1)
        have hS_sub : ∀ y ∈ S, y = s0 ∨ y = -s0 ∨ y = s0 + s0 ∨ y = -(s0 + s0) := by
          intro y hyS
          by_cases hys0 : y = s0
          · exact Or.inl hys0
          · have hyXY : y ∈ X ∨ y ∈ Y := (hpartXY y).1 (by
              intro hyp
              obtain ⟨j, hj, rfl⟩ := (mem_support_iff_getVert p y).1 hyp
              have hadj : G.Adj (p.getVert 0) (p.getVert j) := by simpa [hS] using hyS
              rcases geodesic_adj_getVert p hgeo (Nat.zero_le _) hj hadj with h | h
              · exact hys0 (by rw [← h, hs0_eq])
              · omega)
            rcases hyXY with hyX | hyY
            · rcases hXsub y hyS hyX with h | h
              · exact Or.inr (Or.inr (Or.inl h))
              · rw [hs1_eq] at h
                have hnyS : -y ∈ S := hSneg y hyS
                by_cases hnys0 : -y = s0
                · exfalso
                  have h3eq : s0 + s1 = -(s0 + s0) := eq_neg_of_add_eq_zero_left (by
                    rw [hs1_eq]; calc s0 + (s0 + s0) + (s0 + s0) = y + s0 := by rw [h]; abel
                      _ = 0 := by rw [← hnys0, add_neg_cancel])
                  exact (hC1 i0 i1 (by simp [i0, i1])).2 (h3eq ▸ hSneg _ h2s0_S)
                · have hnyXY : -y ∈ X ∨ -y ∈ Y := (hpartXY (-y)).1 (by
                    intro hyp
                    obtain ⟨j, hj, hjeq⟩ := (mem_support_iff_getVert p (-y)).1 hyp
                    have hadj : G.Adj (p.getVert 0) (p.getVert j) := by rw [hjeq]; simpa [hS] using hnyS
                    rcases geodesic_adj_getVert p hgeo (Nat.zero_le _) hj hadj with hh | hh
                    · exact hnys0 (by rw [← hjeq, ← hh, hs0_eq])
                    · omega)
                  rcases hnyXY with hnyX | hnyY
                  · rcases hXsub (-y) hnyS hnyX with h' | h'
                    · exact Or.inr (Or.inr (Or.inr (by rw [← neg_neg y, h'])))
                    · exfalso
                      rw [hs1_eq] at h'
                      have h8 : y + y = 0 := by
                        have h0 : y + (-y) = 0 := add_neg_cancel y
                        rw [h', ← h] at h0; exact h0
                      obtain ⟨k, hk | hk⟩ := hW_empty y hyS
                      · have hkne0 : k ≠ i0 := by
                          intro e; subst e
                          have : step i0 + step i1 = 0 := by
                            rw [hstep0, hstep1, hs1_eq]
                            calc s0 + (s0 + s0) = (s0 + s0 + (s0 + s0)) - s0 := by abel
                              _ = y - s0 := by rw [← h]
                              _ = step i0 - s0 := by rw [hk]
                              _ = 0 := by rw [hstep0, sub_self]
                          exact (hC1 i0 i1 (by simp [i0, i1])).1 this
                        have hkne1 : k ≠ i1 := by
                          intro e; subst e
                          exact h2s0 (by
                            calc s0 + s0 = (s0 + s0 + (s0 + s0)) - (s0 + s0) := by abel
                              _ = y - (s0 + s0) := by rw [← h]
                              _ = step i1 - (s0 + s0) := by rw [hk]
                              _ = 0 := by rw [hstep1, hs1_eq, sub_self])
                        have hc2 := (hC2 i0 i1 k (by simp [i0, i1]) hkne0.symm hkne1.symm).2
                        have h7 : step i0 + step i1 + step k = -s0 := eq_neg_of_add_eq_zero_left (by
                          calc step i0 + step i1 + step k + s0
                              = y + y := by rw [hstep0, hstep1, hs1_eq, ← hk, h]; abel
                            _ = 0 := h8)
                        exact hc2 (h7 ▸ hSneg s0 hs0S)
                      · have hky : step k = y := by
                          have hstep_neg : step k = -y := by rw [hk, neg_neg]
                          rw [hstep_neg, h', ← h]
                        have hkne0 : k ≠ i0 := by
                          intro e; subst e
                          have : step i0 + step i1 = 0 := by
                            rw [hstep0, hstep1, hs1_eq]
                            calc s0 + (s0 + s0) = (s0 + s0 + (s0 + s0)) - s0 := by abel
                              _ = y - s0 := by rw [← h]
                              _ = step i0 - s0 := by rw [← hky]
                              _ = 0 := by rw [hstep0, sub_self]
                          exact (hC1 i0 i1 (by simp [i0, i1])).1 this
                        have hkne1 : k ≠ i1 := by
                          intro e; subst e
                          exact h2s0 (by
                            calc s0 + s0 = (s0 + s0 + (s0 + s0)) - (s0 + s0) := by abel
                              _ = y - (s0 + s0) := by rw [← h]
                              _ = step i1 - (s0 + s0) := by rw [← hky]
                              _ = 0 := by rw [hstep1, hs1_eq, sub_self])
                        have hc2 := (hC2 i0 i1 k (by simp [i0, i1]) hkne0.symm hkne1.symm).2
                        have h7 : step i0 + step i1 + step k = -s0 := eq_neg_of_add_eq_zero_left (by
                          calc step i0 + step i1 + step k + s0
                              = y + y := by rw [hstep0, hstep1, hs1_eq, hky, h]; abel
                            _ = 0 := h8)
                        exact hc2 (h7 ▸ hSneg s0 hs0S)
                  · exfalso
                    rcases hYsub (-y) hnyS hnyY with h' | h'
                    · have h3 : s0 + s0 + s0 = 0 := by
                        calc s0 + s0 + s0 = (s0 + s0 + (s0 + s0)) + -s0 := by abel
                          _ = y + (-y) := by rw [← h, h']
                          _ = 0 := add_neg_cancel y
                      have : s1 = -s0 := eq_neg_of_add_eq_zero_left (by rw [hs1_eq]; exact h3)
                      exact Finset.disjoint_left.1 hdXY hs1X (this ▸ hnegY)
                    · have : s0 + s0 = 0 := by
                        calc s0 + s0 = (s0 + s0 + (s0 + s0)) + -(s0 + s0) := by abel
                          _ = y + (-y) := by rw [← h, h']
                          _ = 0 := add_neg_cancel y
                      exact h2s0 this
            · rcases hYsub y hyS hyY with h | h
              · exact Or.inr (Or.inl h)
              · exact Or.inr (Or.inr (Or.inr h))
        -- Every step i ≥ 1 must equal 2*s0!
        have hstep_ge1 : ∀ i : Fin L, 1 ≤ i.1 → step i = s0 + s0 := by
          intro i hi
          rcases hS_sub (step i) (hstep_S i) with h | h | h | h
          · exfalso
            have hne0 : i0 ≠ i := by intro e; rw [← e] at hi; simp [i0] at hi
            exact (hC1 i0 i hne0).2 (by rw [hstep0, h]; exact h2s0_S)
          · exfalso
            have hne0 : i0 ≠ i := by intro e; rw [← e] at hi; simp [i0] at hi
            exact (hC1 i0 i hne0).1 (by rw [hstep0, h, add_neg_cancel])
          · exact h
          · exfalso
            by_cases hi1 : i = i1
            · rw [hi1, hstep1, hs1_eq] at h
              have h4 : (s0 + s0) + (s0 + s0) = 0 := by
                calc (s0 + s0) + (s0 + s0)
                    = -(s0 + s0) + (s0 + s0) := congrArg (· + (s0 + s0)) h
                  _ = 0 := neg_add_cancel _
              rcases hS_sub (step i2) (hstep_S i2) with h2 | h2 | h2 | h2
              · exact (hC1 i0 i2 (by simp [i0, i2])).2 (by rw [hstep0, h2]; exact h2s0_S)
              · exact (hC1 i0 i2 (by simp [i0, i2])).1 (by rw [hstep0, h2, add_neg_cancel])
              · exact (hC1 i1 i2 (by simp [i1, i2])).1 (by rw [hstep1, hs1_eq, h2]; exact h4)
              · exact (hC1 i1 i2 (by simp [i1, i2])).1 (by rw [hstep1, hs1_eq, h2, add_neg_cancel])
            · exact (hC1 i1 i (Ne.symm hi1)).1 (by rw [hstep1, hs1_eq, h, add_neg_cancel])
        -- Now at v, s_{L-1} = 2*s0! Check v + s0 ∉ p.support and connects to v - s0 and v + 2*s0 directly!
        have hlast : step ⟨L - 1, by omega⟩ = s0 + s0 := hstep_ge1 ⟨L - 1, by omega⟩ (by dsimp; omega)
        have hv_s0_notp : v + s0 ∉ p.support := by
          intro hmem
          obtain ⟨j, hj, hjeq⟩ := (mem_support_iff_getVert p (v + s0)).1 hmem
          have hadj : G.Adj (p.getVert L) (p.getVert j) := by
            rw [← hplen, p.getVert_length, hjeq]; exact (hS _ _).2 (by simpa using hs0S)
          rcases geodesic_adj_getVert p hgeo (by omega) hj hadj with hh | hh
          · omega
          · have hjL : j = L - 1 := by omega
            subst hjL
            have h1 : p.getVert L = v := by rw [← hplen, p.getVert_length]
            have hL1 : L - 1 + 1 = L := by omega
            have h2 : step ⟨L - 1, by omega⟩ = p.getVert L - p.getVert (L - 1) := by
              simp only [step, hL1]
            rw [h1, hlast, hjeq] at h2
            have h3 : s0 + s0 + s0 = 0 := by
              calc s0 + s0 + s0 = (s0 + s0) + (v + s0) - v := by abel
                _ = (v - (v + s0)) + (v + s0) - v := by rw [h2]
                _ = 0 := by abel
            have : s1 = -s0 := eq_neg_of_add_eq_zero_left (by rw [hs1_eq]; exact h3)
            exact Finset.disjoint_left.1 hdXY hs1X (this ▸ hnegY)
        refine hv_same_comp (v + s0) hv_s0_notp (fun t htS ht_notp => ?_)
        rcases hS_sub t htS with rfl | rfl | rfl | rfl
        · exact Reachable.refl _
        · have h1 : G.Adj (v + -s0) (v + s0) := (hS _ _).2 (by
            have : v + s0 - (v + -s0) = s0 + s0 := by abel
            rw [this]; exact h2s0_S)
          exact Adj.reachable (show (G.induce _).Adj ⟨v + -s0, ht_notp⟩ ⟨v + s0, hv_s0_notp⟩ from h1)
        · have h1 : G.Adj (v + (s0 + s0)) (v + s0) := (hS _ _).2 (by
            have : v + s0 - (v + (s0 + s0)) = -s0 := by abel
            rw [this]; exact hSneg s0 (hstep_S i0))
          exact Adj.reachable (show (G.induce _).Adj ⟨v + (s0 + s0), ht_notp⟩ ⟨v + s0, hv_s0_notp⟩ from h1)
        · exfalso
          apply ht_notp
          have h1 : p.getVert L = v := by rw [← hplen, p.getVert_length]
          have hL1 : L - 1 + 1 = L := by omega
          have h2 : step ⟨L - 1, by omega⟩ = p.getVert L - p.getVert (L - 1) := by
            simp only [step, hL1]
          rw [h1, hlast] at h2
          have : v + -(s0 + s0) = p.getVert (L - 1) := by rw [h2]; abel
          rw [this]; exact p.getVert_mem_support (L - 1)
      · -- Subcase A2b: s1 ∈ Y!
        obtain ⟨u, huS, huX⟩ := hX0
        rcases hXsub u huS huX with hu2 | hu21
        · rcases hsumXY u huS huX s1 (hstep_S i1) hs1Y with h | h | h
          · rw [hu2] at h
            have : s0 + s1 = -s0 := eq_neg_of_add_eq_zero_left (by convert h using 1; abel)
            exact (hC1 i0 i1 (by simp [i0, i1])).2 (this ▸ hSneg s0 (hstep_S i0))
          · rw [hu2] at h
            have : s0 + s1 = 0 := by
              have := congrArg (· - s0) h; convert this using 1 <;> abel
            exact (hC1 i0 i1 (by simp [i0, i1])).1 this
          · rw [hu2] at h
            have : s0 = 0 := by
              have := congrArg (· - (s0 + s1)) h; convert this using 1 <;> abel
            exact hS0 (this ▸ hstep_S i0)
        · rcases hsumXY u huS huX s1 (hstep_S i1) hs1Y with h | h | h
          · -- 2*s0 + 2*s1 = 0!
            rw [hu21] at h
            have h201 : s0 + s0 + (s1 + s1) = 0 := by convert h using 1; abel
            have hu_eq : u = -s1 := eq_neg_of_add_eq_zero_left (by rw [hu21]; convert h201 using 1; abel)
            have hS_sub : ∀ y ∈ S, y = s0 ∨ y = -s0 ∨ y = s1 ∨ y = -s1 := by
              intro y hyS
              by_cases hys0 : y = s0
              · exact Or.inl hys0
              · have hyXY : y ∈ X ∨ y ∈ Y := (hpartXY y).1 (by
                  intro hyp
                  obtain ⟨j, hj, rfl⟩ := (mem_support_iff_getVert p y).1 hyp
                  have hadj : G.Adj (p.getVert 0) (p.getVert j) := by simpa [hS] using hyS
                  rcases geodesic_adj_getVert p hgeo (Nat.zero_le _) hj hadj with hh | hh
                  · exact hys0 (by rw [← hh, hs0_eq])
                  · omega)
                rcases hyXY with hyX | hyY
                · rcases hXsub y hyS hyX with hh | hh
                  · exfalso
                    rcases hsumXY y hyS hyX s1 (hstep_S i1) hs1Y with h' | h' | h'
                    · rw [hh] at h'
                      have : s0 + s1 = -s0 := eq_neg_of_add_eq_zero_left (by convert h' using 1; abel)
                      exact (hC1 i0 i1 (by simp [i0, i1])).2 (this ▸ hSneg s0 (hstep_S i0))
                    · rw [hh] at h'
                      have : s0 + s1 = 0 := by have := congrArg (· - s0) h'; convert this using 1 <;> abel
                      exact (hC1 i0 i1 (by simp [i0, i1])).1 this
                    · rw [hh] at h'
                      have : s0 = 0 := by have := congrArg (· - (s0 + s1)) h'; convert this using 1 <;> abel
                      exact hS0 (this ▸ hstep_S i0)
                  · right; right; right; rw [hh, ← hu21]; exact hu_eq
                · rcases hsumXY u huS huX y hyS hyY with h' | h' | h'
                  · right; right; left; rw [hu_eq] at h'; exact eq_of_sub_eq_zero (by convert h' using 1; abel)
                  · exfalso
                    rw [hu_eq] at h'
                    have : y = s0 + s1 := by
                      have := congrArg (· + s1) h'; convert this using 1; abel
                    exact (hC1 i0 i1 (by simp [i0, i1])).2 (this ▸ hyS)
                  · right; left
                    rw [hu_eq] at h'
                    have hy' : y = s0 + s1 + s1 := by
                      have := congrArg (· + s1) h'; convert this using 1; abel
                    exact eq_neg_of_add_eq_zero_left (by rw [hy']; convert h201 using 1; abel)
            -- Now L ≥ 3 gives step i2 ∈ {s0, -s0, s1, -s1}, all 4 impossible!
            rcases hS_sub s2 (hstep_S i2) with hs2 | hs2 | hs2 | hs2
            · have hc2 := (hC2 i0 i1 i2 (by simp [i0, i1]) (by simp [i0, i2]) (by simp [i1, i2])).2
              have : step i0 + step i1 + step i2 = -s1 := eq_neg_of_add_eq_zero_left (by
                change s0 + s1 + s2 + s1 = 0; rw [hs2]; convert h201 using 1; abel)
              exact hc2 (this ▸ hSneg s1 (hstep_S i1))
            · exact (hC1 i0 i2 (by simp [i0, i2])).1 (by change s0 + s2 = 0; rw [hs2, add_neg_cancel])
            · have hc2 := (hC2 i0 i1 i2 (by simp [i0, i1]) (by simp [i0, i2]) (by simp [i1, i2])).2
              have : step i0 + step i1 + step i2 = -s0 := eq_neg_of_add_eq_zero_left (by
                change s0 + s1 + s2 + s0 = 0; rw [hs2]; convert h201 using 1; abel)
              exact hc2 (this ▸ hSneg s0 (hstep_S i0))
            · exact (hC1 i1 i2 (by simp [i1, i2])).1 (by change s1 + s2 = 0; rw [hs2, add_neg_cancel])
          · rw [hu21] at h
            have : s0 + s1 = -s1 := eq_neg_of_add_eq_zero_left (by
              have := congrArg (· - s0) h; convert this using 1 <;> abel)
            exact (hC1 i0 i1 (by simp [i0, i1])).2 (this ▸ hSneg s1 (hstep_S i1))
          · rw [hu21] at h
            have : s0 + s1 = 0 := by
              have := congrArg (· - (s0 + s1)) h; convert this using 1 <;> abel
            exact (hC1 i0 i1 (by simp [i0, i1])).1 this
  -- Symmetrized Case B (2 * s0 = 0) helper: assumes s1 ∈ X
  have hCaseB : s0 + s0 = 0 →
      ∀ (X Y : Finset V), (∀ x, x ∉ p.support ↔ x ∈ X ∨ x ∈ Y) → Disjoint X Y →
        (∀ x ∈ X, ∀ y ∈ Y, ¬ G.Adj x y) →
        (∃ b ∈ S, b ∈ Y) → (s1 ∈ X) →
        (∀ a ∈ S, a ∈ X → ∀ b ∈ S, b ∈ Y → a + b = 0 ∨ a + b = s0 ∨ a + b = s0 + s1) → False := by
    intro h2s0 X Y hpartXY hdXY hnoXY hY0 hs1X hsumXY
    have hs0_neg : -s0 = s0 := (eq_neg_of_add_eq_zero_left h2s0).symm
    have hYsub : ∀ y ∈ S, y ∈ Y → y = -s1 := by
      intro y hyS hyY
      rcases hsumXY s1 (hstep_S i1) hs1X y hyS hyY with h | h | h
      · exact eq_neg_of_add_eq_zero_right h
      · exfalso
        have hy_eq : y = s0 - s1 := by
          have := congrArg (· - s1) h; convert this using 1; abel
        obtain ⟨k, hk | hk⟩ := hW_empty y hyS
        · have hkne0 : k ≠ i0 := by
            intro e; subst e
            have : s1 = 0 := by
              calc s1 = s0 - (s0 - s1) := by abel
                _ = s0 - y := by rw [← hy_eq]
                _ = s0 - step i0 := by rw [hk]
                _ = 0 := by rw [hstep0, sub_self]
            exact hS0 (this ▸ hs1S)
          by_cases hk1 : k = i1
          · subst hk1
            have hs02 : s0 = s1 + s1 := by
              calc s0 = (s0 - s1) + s1 := by abel
                _ = y + s1 := by rw [← hy_eq]
                _ = step i1 + s1 := by rw [hk]
                _ = s1 + s1 := by rw [hstep1]
            have h4 : s1 + s1 + (s1 + s1) = 0 := by rw [← hs02]; exact h2s0
            have h3eq : s0 + s1 = -s1 := eq_neg_of_add_eq_zero_left (by rw [hs02]; convert h4 using 1; abel)
            exact (hC1 i0 i1 (by simp [i0, i1])).2 (h3eq ▸ hSneg s1 hs1S)
          · exact (hC1 i1 k (Ne.symm hk1)).2 (by
              have : step i1 + step k = s0 := by rw [hstep1, ← hk, hy_eq]; abel
              rw [this]; exact hs0S)
        · have hsk : step k = s0 + s1 := by
            have hneg : step k = -y := by rw [hk, neg_neg]
            rw [hneg, hy_eq]; calc -(s0 - s1) = -s0 + s1 := by abel
              _ = s0 + s1 := by rw [hs0_neg]
          exact (hC1 i0 i1 (by simp [i0, i1])).2 (hsk ▸ hstep_S k)
      · exfalso
        have hys0 : y = s0 := by
          have := congrArg (· - s1) h; convert this using 1 <;> abel
        exact ((hpartXY y).2 (Or.inr hyY)) (hys0 ▸ hs0_eq ▸ p.getVert_mem_support 1)
    obtain ⟨b, hbS, hbY⟩ := hY0
    have hns1Y : -s1 ∈ Y := hYsub b hbS hbY ▸ hbY
    have h2s1 : s1 + s1 ≠ 0 := by
      intro h0
      have : -s1 = s1 := (eq_neg_of_add_eq_zero_left h0).symm
      exact Finset.disjoint_left.1 hdXY hs1X (this ▸ hns1Y)
    have hXsub : ∀ u ∈ S, u ∈ X → u = s1 ∨ u = s0 + s1 + s1 := by
      intro u huS huX
      rcases hsumXY u huS huX (-s1) (hSneg s1 hs1S) hns1Y with h | h | h
      · left; exact eq_of_sub_eq_zero (by simpa [sub_eq_add_neg] using h)
      · exfalso
        have hu01 : u = s0 + s1 := by
          have := congrArg (· + s1) h; convert this using 1; abel
        exact (hC1 i0 i1 (by simp [i0, i1])).2 (hu01 ▸ huS)
      · right
        have := congrArg (· + s1) h; convert this using 1; abel
    have hS_sub : ∀ y ∈ S, y = s0 ∨ y = s1 ∨ y = -s1 := by
      intro y hyS
      by_cases hys0 : y = s0
      · exact Or.inl hys0
      · have hyXY : y ∈ X ∨ y ∈ Y := (hpartXY y).1 (by
          intro hyp
          obtain ⟨j, hj, rfl⟩ := (mem_support_iff_getVert p y).1 hyp
          have hadj : G.Adj (p.getVert 0) (p.getVert j) := by simpa [hS] using hyS
          rcases geodesic_adj_getVert p hgeo (Nat.zero_le _) hj hadj with hh | hh
          · exact hys0 (by rw [← hh, hs0_eq])
          · omega)
        rcases hyXY with hyX | hyY
        · rcases hXsub y hyS hyX with h | h
          · exact Or.inr (Or.inl h)
          · exfalso
            have hnyS : -y ∈ S := hSneg y hyS
            have hny_eq : -y = s0 - (s1 + s1) := by
              rw [h]; calc -(s0 + s1 + s1) = -s0 - (s1 + s1) := by abel
                _ = s0 - (s1 + s1) := by rw [hs0_neg]
            by_cases hnys0 : -y = s0
            · exact h2s1 (by
                calc s1 + s1 = s0 - (s0 - (s1 + s1)) := by abel
                  _ = s0 - (-y) := by rw [← hny_eq]
                  _ = s0 - s0 := by rw [hnys0]
                  _ = 0 := sub_self s0)
            · have hnyXY : -y ∈ X ∨ -y ∈ Y := (hpartXY (-y)).1 (by
                intro hyp
                obtain ⟨j, hj, hjeq⟩ := (mem_support_iff_getVert p (-y)).1 hyp
                have hadj : G.Adj (p.getVert 0) (p.getVert j) := by rw [hjeq]; simpa [hS] using hnyS
                rcases geodesic_adj_getVert p hgeo (Nat.zero_le _) hj hadj with hh | hh
                · exact hnys0 (by rw [← hjeq, ← hh, hs0_eq])
                · omega)
              rcases hnyXY with hnyX | hnyY
              · rcases hXsub (-y) hnyS hnyX with h' | h'
                · have : y = -s1 := by rw [← neg_neg y, h']
                  exact Finset.disjoint_left.1 hdXY hyX (this ▸ hns1Y)
                · have h4s1 : s1 + s1 + (s1 + s1) = 0 := by
                    have hsum0 : y + (-y) = 0 := add_neg_cancel y
                    rw [h'] at hsum0; rw [h] at hsum0
                    calc s1 + s1 + (s1 + s1) = (s0 + s0) + (s1 + s1 + (s1 + s1)) := by rw [h2s0, zero_add]
                      _ = (s0 + s1 + s1) + (s0 + s1 + s1) := by abel
                      _ = 0 := hsum0
                  obtain ⟨k, hk | hk⟩ := hW_empty y hyS
                  · have hky : step k = y := hk.symm
                    have hkne0 : k ≠ i0 := by
                      intro e; subst e
                      exact h2s1 (by
                        calc s1 + s1 = (s0 + s1 + s1) - s0 := by abel
                          _ = y - s0 := by rw [← h]
                          _ = step i0 - s0 := by rw [← hky]
                          _ = 0 := by rw [hstep0, sub_self])
                    have hkne1 : k ≠ i1 := by
                      intro e; subst e
                      exact (hC1 i0 i1 (by simp [i0, i1])).1 (by
                        rw [hstep0, hstep1]
                        calc s0 + s1 = (s0 + s1 + s1) - s1 := by abel
                          _ = y - s1 := by rw [← h]
                          _ = step i1 - s1 := by rw [← hky]
                          _ = 0 := by rw [hstep1, sub_self])
                    have hc2 := (hC2 i0 i1 k (by simp [i0, i1]) hkne0.symm hkne1.symm).2
                    have hsum3 : step i0 + step i1 + step k = -s1 := eq_neg_of_add_eq_zero_left (by
                      rw [hstep0, hstep1, hky, h]
                      calc s0 + s1 + (s0 + s1 + s1) + s1 = (s0 + s0) + (s1 + s1 + (s1 + s1)) := by abel
                        _ = 0 := by rw [h2s0, h4s1, add_zero])
                    exact hc2 (hsum3 ▸ hSneg s1 hs1S)
                  · have hky : step k = y := by
                      have hneg : step k = -y := by rw [hk, neg_neg]
                      rw [hneg, h', ← h]
                    have hkne0 : k ≠ i0 := by
                      intro e; subst e
                      exact h2s1 (by
                        calc s1 + s1 = (s0 + s1 + s1) - s0 := by abel
                          _ = y - s0 := by rw [← h]
                          _ = step i0 - s0 := by rw [← hky]
                          _ = 0 := by rw [hstep0, sub_self])
                    have hkne1 : k ≠ i1 := by
                      intro e; subst e
                      exact (hC1 i0 i1 (by simp [i0, i1])).1 (by
                        rw [hstep0, hstep1]
                        calc s0 + s1 = (s0 + s1 + s1) - s1 := by abel
                          _ = y - s1 := by rw [← h]
                          _ = step i1 - s1 := by rw [← hky]
                          _ = 0 := by rw [hstep1, sub_self])
                    have hc2 := (hC2 i0 i1 k (by simp [i0, i1]) hkne0.symm hkne1.symm).2
                    have hsum3 : step i0 + step i1 + step k = -s1 := eq_neg_of_add_eq_zero_left (by
                      rw [hstep0, hstep1, hky, h]
                      calc s0 + s1 + (s0 + s1 + s1) + s1 = (s0 + s0) + (s1 + s1 + (s1 + s1)) := by abel
                        _ = 0 := by rw [h2s0, h4s1, add_zero])
                    exact hc2 (hsum3 ▸ hSneg s1 hs1S)
              · have hny_eq1 : -y = -s1 := hYsub (-y) hnyS hnyY
                have hys1 : y = s1 := neg_inj.1 hny_eq1
                exact (hC1 i0 i1 (by simp [i0, i1])).1 (by
                  rw [hstep0, hstep1]
                  calc s0 + s1 = (s0 + s1 + s1) - s1 := by abel
                    _ = y - s1 := by rw [← h]
                    _ = 0 := by rw [hys1, sub_self])
        · exact Or.inr (Or.inr (hYsub y hyS hyY))
    -- Every step i ≥ 1 equals s1!
    have hstep_ge1 : ∀ i : Fin L, 1 ≤ i.1 → step i = s1 := by
      intro i hi
      rcases hS_sub (step i) (hstep_S i) with h | h | h
      · exfalso
        have hne0 : i0 ≠ i := by intro e; rw [← e] at hi; simp [i0] at hi
        exact (hC1 i0 i hne0).1 (by rw [hstep0, h]; exact h2s0)
      · exact h
      · exfalso
        by_cases hi1 : i = i1
        · rw [hi1, hstep1] at h
          exact h2s1 (calc s1 + s1 = -s1 + s1 := congrArg (· + s1) h
            _ = 0 := neg_add_cancel s1)
        · exact (hC1 i1 i (Ne.symm hi1)).1 (by rw [hstep1, h, add_neg_cancel])
    -- At v, the last two steps are s1 and s1, and v + s0 + s1 ∉ p.support connects v + s0 and v + s1!
    have hlast1 : step ⟨L - 1, by omega⟩ = s1 := hstep_ge1 ⟨L - 1, by omega⟩ (by dsimp; omega)
    have hlast2 : step ⟨L - 2, by omega⟩ = s1 := hstep_ge1 ⟨L - 2, by omega⟩ (by dsimp; omega)
    have hv_01_notp : v + (s0 + s1) ∉ p.support := by
      intro hmem
      have hd2 : G.dist v (v + (s0 + s1)) ≤ 2 := by
        have := abelian_dist_le_sum hS (x := v) (l := [s0, s1]) (by simp [hs0S, hs1S])
        simpa [add_assoc] using this
      rcases hv_mem_p_of_dist2 (s0 + s1) hd2 hmem with h | h | h
      · exact (hC1 i0 i1 (by simp [i0, i1])).1 h
      · rw [hlast1] at h
        exact (hC1 i0 i1 (by simp [i0, i1])).2 (h ▸ hSneg s1 hs1S)
      · rw [hlast1, hlast2] at h
        have hc2 := (hC2 i0 i1 i2 (by simp [i0, i1]) (by simp [i0, i2]) (by simp [i1, i2])).2
        have hsum3 : step i0 + step i1 + step i2 = -s1 := eq_neg_of_add_eq_zero_left (by
          rw [hstep0, hstep1, hstep_ge1 i2 (by simp [i2])]
          calc s0 + s1 + s1 + s1 = (s0 + s1) + (s1 + s1) := by abel
            _ = -(s1 + s1) + (s1 + s1) := by rw [h]
            _ = 0 := neg_add_cancel _)
        exact hc2 (hsum3 ▸ hSneg s1 hs1S)
    refine hv_same_comp (v + (s0 + s1)) hv_01_notp (fun t htS ht_notp => ?_)
    rcases hS_sub t htS with rfl | rfl | rfl
    · have h1 : G.Adj (v + s0) (v + (s0 + s1)) := (hS _ _).2 (by
        have : v + (s0 + s1) - (v + s0) = s1 := by abel
        rw [this]; exact hs1S)
      exact Adj.reachable (show (G.induce _).Adj ⟨v + s0, ht_notp⟩ ⟨v + (s0 + s1), hv_01_notp⟩ from h1)
    · have h1 : G.Adj (v + s1) (v + (s0 + s1)) := (hS _ _).2 (by
        have : v + (s0 + s1) - (v + s1) = s0 := by abel
        rw [this]; exact hs0S)
      exact Adj.reachable (show (G.induce _).Adj ⟨v + s1, ht_notp⟩ ⟨v + (s0 + s1), hv_01_notp⟩ from h1)
    · exfalso
      apply ht_notp
      have h1 : p.getVert L = v := by rw [← hplen, p.getVert_length]
      have hL1 : L - 1 + 1 = L := by omega
      have h2 : step ⟨L - 1, by omega⟩ = p.getVert L - p.getVert (L - 1) := by
        simp only [step, hL1]
      rw [h1, hlast1] at h2
      have : v + -s1 = p.getVert (L - 1) := by rw [h2]; abel
      rw [this]; exact p.getVert_mem_support (L - 1)
  -- Dispatch Case A vs Case B!
  by_cases h2s0 : s0 + s0 = 0
  · have hs1ne : s1 ≠ s0 := fun h => (hC1 i0 i1 (by simp [i0, i1])).1 (by rw [hstep0, hstep1, h]; exact h2s0)
    rcases hS_split s1 hs1S hs1ne with hs1A | hs1B
    · exact hCaseB h2s0 A B hpart hdAB hnoAB hB0 hs1A hsum_AB
    · exact hCaseB h2s0 B A (fun x => (hpart x).trans or_comm) hdAB.symm
        (fun b hb a ha h => hnoAB a ha b hb h.symm) hA0 hs1B
        (fun b hbS hbB a haS haA => by rw [add_comm]; exact hsum_AB a haS haA b hbS hbB)
  · have hns0_ne : -s0 ≠ s0 := fun h => h2s0 (calc s0 + s0 = -s0 + s0 := congrArg (· + s0) h.symm
      _ = 0 := neg_add_cancel s0)
    rcases hS_split (-s0) (hSneg s0 hs0S) hns0_ne with hns0A | hns0B
    · exact hCaseA h2s0 B A (fun x => (hpart x).trans or_comm) hdAB.symm
        (fun b hb a ha h => hnoAB a ha b hb h.symm) hB0 hns0A
        (fun b hbS hbB a haS haA => by rw [add_comm]; exact hsum_AB a haS haA b hbS hbB)
    · exact hCaseA h2s0 A B hpart hdAB hnoAB hA0 hns0B hsum_AB

end Helpers

theorem main : H1 → H2 → type_of% @OMA.S_gillibert_geodesic_deletion.main := by
  intro hH1 hH2 V _ G hconn hvt hcard u v p hp hgeo
  by_contra hnot
  have hex : ∃ L, ∃ (u' v' : V) (q : G.Walk u' v'), q.IsPath ∧ q.length = G.dist u' v' ∧
      q.length = L ∧ ¬ (G.induce {x | x ∉ q.support}).Connected :=
    ⟨p.length, u, v, p, hp, hgeo, rfl, hnot⟩
  let L := Nat.find hex
  obtain ⟨u', v', q, hq, hqg, hqL, hqnot⟩ := Nat.find_spec hex
  have hmin : ∀ (u'' v'' : V) (r : G.Walk u'' v''), r.IsPath → r.length = G.dist u'' v'' →
      r.length < q.length → (G.induce {x | x ∉ r.support}).Connected := by
    intro u'' v'' r hr hrg hrlt
    by_contra hrnot
    exact Nat.find_min hex (hqL ▸ hrlt) ⟨u'', v'', r, hr, hrg, rfl, hrnot⟩
  have hq3 : 3 ≤ q.length := by
    by_contra hlt
    exact hqnot (length_le_two_connected hconn hvt hcard q hq hqg (by omega))
  have hno_step : ¬ ∃ φ : G ≃g G, (∀ x, G.Adj x (φ x)) ∧ (∀ x ∈ q.support, φ x ∉ q.support) := by
    rintro ⟨φ, hadj, hdisj⟩
    exact hqnot (automorphism_step_connected hconn q φ hadj hdisj)
  by_cases hCay : ∃ (_ : Group V) (S : Set V), ∀ x y : V, G.Adj x y ↔ x⁻¹ * y ∈ S
  · by_cases hAb : ∃ (_ : AddCommGroup V) (S : Set V), ∀ x y : V, G.Adj x y ↔ y - x ∈ S
    · obtain ⟨inst, S, hS⟩ := hAb
      exact hqnot (@abelian_cayley_connected V _ inst G S hS hconn hcard u' v' q hq hqg)
    · exact hqnot (hH1 G hconn hvt hcard hCay hAb u' v' q hq hqg hq3 hno_step hmin)
  · exact hqnot (hH2 G hconn hvt hcard hCay u' v' q hq hqg hq3 hno_step hmin)

end OMA.R_gillibert_geodesic_deletion_R2
