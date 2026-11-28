import OMAReductions.R_Erdos64_erdos_64_R4
import Mathlib

/-!
# Structural reduction of the vertex-transitive cubic branch of Erdős Problem 64

Step H2 of Erdos64.erdos_64.R4 reduces vertex-transitive graphs to connected cubic
vertex-transitive C4-free C8-free graphs of order different from 2^k and 2p (p prime).
This reduction proves four structural theorems in Lean 4 and splits the remaining
vertex-transitive cubic branch into bipartite (H1) and non-bipartite (H2) subproblems:

1. Bridgelessness: every connected cubic vertex-transitive graph is bridgeless, proved
   by taking a bridge minimizing one component size and transporting it into that
   component by vertex-transitivity.
2. Triangle elimination (girth ≥ 5): in a connected cubic vertex-transitive C4-free
   graph with a triangle, the triangles partition the vertex set into disjoint triples
   with at most one edge between any two triples; contracting each triangle produces a
   smaller connected cubic vertex-transitive quotient whose 2^k-cycle lifts to a
   2^(k+1)-cycle.
3. Transitive-commuting involution elimination (2-cover descent): if a connected cubic
   vertex-transitive C4-free graph admits a nontrivial involution σ commuting with a
   transitive family of automorphisms, then σ is automatically fixed-point-free and
   non-adjacent; quotienting by σ gives a connected cubic vertex-transitive graph on
   half as many vertices whose 2^k-cycle lifts via R4.lift_two to a 2^k- or 2^(k+1)-cycle.
   (This eliminates all prisms, antipodal 2-covers, and cubic Cayley graphs of groups
   with even-order center, including all finite nilpotent groups.)
4. Order lower bound (|V| ≥ 18 and even): handshaking forces |V| even, girth ≥ 5 gives
   the Moore bound |V| ≥ 10, every cubic girth ≥ 5 graph on 12 vertices contains a C8,
   and 10 = 2·5, 14 = 2·7, 16 = 2^4 are excluded by R4.
-/

namespace OMA.R_Erdos64_erdos_64_R4_H2_R1

open SimpleGraph Finset Function
open scoped Classical

/-- Connected bridgeless cubic vertex-transitive bipartite C4-free C8-free graphs of even
order at least 18 (not 2^k or 2p) admitting no transitive-commuting involution. -/
def H1 : Prop :=
  ∀ (V : Type) (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj],
    G.Connected →
    (∀ ⦃a b⦄, G.Adj a b → ¬ G.IsBridge s(a, b)) →
    (∀ x, G.degree x = 3) →
    (∀ x y, ∃ g : G ≃g G, g x = y) →
    G.IsBipartite →
    (¬ cycleGraph 4 ⊑ G) →
    (¬ cycleGraph 8 ⊑ G) →
    Even (Fintype.card V) →
    18 ≤ Fintype.card V →
    (∀ k : ℕ, Fintype.card V ≠ 2 ^ k) →
    (∀ p : ℕ, p.Prime → Fintype.card V ≠ 2 * p) →
    (¬ ∃ σ : G ≃g G, σ ≠ 1 ∧ (∀ x, σ (σ x) = x) ∧
      (∀ x y, ∃ g : G ≃g G, g x = y ∧ ∀ z, g (σ z) = σ (g z))) →
    ∃ k : ℕ, 2 ≤ k ∧ cycleGraph (2 ^ k) ⊑ G

/-- Connected bridgeless cubic vertex-transitive non-bipartite triangle-free C4-free C8-free
graphs of even order at least 18 (not 2^k or 2p) admitting no transitive-commuting involution. -/
def H2 : Prop :=
  ∀ (V : Type) (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj],
    G.Connected →
    (∀ ⦃a b⦄, G.Adj a b → ¬ G.IsBridge s(a, b)) →
    (∀ x, G.degree x = 3) →
    (∀ x y, ∃ g : G ≃g G, g x = y) →
    ¬ G.IsBipartite →
    (∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a) →
    (¬ cycleGraph 4 ⊑ G) →
    (¬ cycleGraph 8 ⊑ G) →
    Even (Fintype.card V) →
    18 ≤ Fintype.card V →
    (∀ k : ℕ, Fintype.card V ≠ 2 ^ k) →
    (∀ p : ℕ, p.Prime → Fintype.card V ≠ 2 * p) →
    (¬ ∃ σ : G ≃g G, σ ≠ 1 ∧ (∀ x, σ (σ x) = x) ∧
      (∀ x y, ∃ g : G ≃g G, g x = y ∧ ∀ z, g (σ z) = σ (g z))) →
    ∃ k : ℕ, 2 ≤ k ∧ cycleGraph (2 ^ k) ⊑ G

section Helpers

private lemma no_c4_of_not_copy {V : Type} {G : SimpleGraph V} (hc4 : ¬ cycleGraph 4 ⊑ G)
    {a b c d : V} (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) (hda : G.Adj d a) :
    a = c ∨ b = d := by
  by_contra h
  push Not at h
  exact hc4 (OMA.R_Erdos64_erdos_64_R4.square_of_four hab hbc hcd hda h.1 h.2)

private lemma copy_eight {V : Type} (G : SimpleGraph V)
    (v0 v1 v2 v3 v4 v5 v6 v7 : V)
    (e01 : G.Adj v0 v1) (e12 : G.Adj v1 v2) (e23 : G.Adj v2 v3) (e34 : G.Adj v3 v4)
    (e45 : G.Adj v4 v5) (e56 : G.Adj v5 v6) (e67 : G.Adj v6 v7) (e70 : G.Adj v7 v0)
    (hnd : ([v0, v1, v2, v3, v4, v5, v6, v7] : List V).Nodup) :
    cycleGraph 8 ⊑ G := by
  have hring := OMA.R_Erdos64_erdos_64_R4.cycle_of_ring G [v0, v1, v2, v3, v4, v5, v6, v7]
    (by simp) hnd (by simp [e01, e12, e23, e34, e45, e56, e67]) (by simpa using e70)
  simpa using hring

/- ### Part 1: Bridgelessness of connected cubic vertex-transitive graphs -/

private lemma iso_preserves_bridge {V : Type} {G : SimpleGraph V} (g : G ≃g G)
    {x y : V} (hbr : G.IsBridge s(x, y)) : G.IsBridge s(g x, g y) := by
  rw [SimpleGraph.isBridge_iff] at hbr ⊢
  intro hreach
  apply hbr
  rcases hreach with ⟨p⟩
  refine ⟨(p.map ⟨g.symm, ?_⟩).copy (g.symm_apply_apply x) (g.symm_apply_apply y)⟩
  intro u v huv
  rw [SimpleGraph.deleteEdges_adj] at huv ⊢
  refine ⟨g.symm.map_rel_iff.mpr huv.1, ?_⟩
  intro heq
  apply huv.2
  simp only [Set.mem_singleton_iff, Sym2.eq_iff] at heq ⊢
  rcases heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left; exact ⟨by rw [← h1, g.apply_symm_apply], by rw [← h2, g.apply_symm_apply]⟩
  · right; exact ⟨by rw [← h1, g.apply_symm_apply], by rw [← h2, g.apply_symm_apply]⟩

private lemma vt_cubic_bridgeless {V : Type} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hdeg : ∀ x, G.degree x = 3)
    (hvt : ∀ x y, ∃ g : G ≃g G, g x = y)
    ⦃a b : V⦄ (hab : G.Adj a b) : ¬ G.IsBridge s(a, b) := by
  intro hbr0
  let P : ℕ → Prop := fun k =>
    ∃ x y : V, G.Adj x y ∧ G.IsBridge s(x, y) ∧
      (Finset.univ.filter (fun z => (G.deleteEdges {s(x, y)}).Reachable x z)).card = k
  have hex : ∃ k, P k := ⟨_, a, b, hab, hbr0, rfl⟩
  obtain ⟨k, ⟨x, y, hxy, hbr, hcard⟩, hmin⟩ :
      ∃ k, (∃ x y : V, G.Adj x y ∧ G.IsBridge s(x, y) ∧
        (Finset.univ.filter (fun z => (G.deleteEdges {s(x, y)}).Reachable x z)).card = k) ∧
        ∀ m < k, ¬ P m :=
    ⟨Nat.find hex, Nat.find_spec hex, fun m hm => Nat.find_min hex hm⟩
  let H := G.deleteEdges {s(x, y)}
  let C := Finset.univ.filter (fun z => H.Reachable x z)
  have hxC : x ∈ C := Finset.mem_filter.mpr ⟨Finset.mem_univ _, SimpleGraph.Reachable.refl x⟩
  have hnot_xy : ¬ H.Reachable x y := SimpleGraph.isBridge_iff.mp hbr
  have hyC : y ∉ C := fun h => hnot_xy (Finset.mem_filter.mp h).2
  -- x has at least one neighbor w ≠ y, hence w ∈ C and w ≠ x
  have hex_w : ∃ w : V, G.Adj x w ∧ w ≠ y := by
    by_contra hno
    push Not at hno
    have hsub : G.neighborFinset x ⊆ {y} := fun z hz =>
      Finset.mem_singleton.mpr (hno z ((G.mem_neighborFinset x z).mp hz))
    have hc := Finset.card_le_card hsub
    rw [card_neighborFinset_eq_degree, hdeg x, Finset.card_singleton] at hc
    omega
  obtain ⟨w, hxw, hwy⟩ := hex_w
  have hwx : w ≠ x := (G.ne_of_adj hxw).symm
  have hxw_H : H.Adj x w := by
    rw [SimpleGraph.deleteEdges_adj]
    refine ⟨hxw, ?_⟩
    simp only [Set.mem_singleton_iff, Sym2.eq_iff]
    rintro (⟨_, h2⟩ | ⟨h1, _⟩)
    · exact hwy h2
    · exact G.loopless.irrefl x (h1 ▸ hxy)
  have hwC : w ∈ C := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxw_H.reachable⟩
  -- Transport bridge s(x, y) to w via vertex-transitivity
  obtain ⟨g, hgx⟩ := hvt x w
  let w' := g y
  have hww' : G.Adj w w' := hgx ▸ g.map_rel_iff.mpr hxy
  have hbr' : G.IsBridge s(w, w') := hgx ▸ iso_preserves_bridge g hbr
  have hw'C : w' ∈ C := by
    have hww'_H : H.Adj w w' := by
      rw [SimpleGraph.deleteEdges_adj]
      refine ⟨hww', ?_⟩
      simp only [Set.mem_singleton_iff, Sym2.eq_iff]
      rintro (⟨h1, _⟩ | ⟨h1, _⟩)
      · exact hwx h1
      · exact hyC (h1 ▸ hwC)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hwC).2.trans hww'_H.reachable⟩
  -- Whichever side of G \ {s(w, w')} avoids x is strictly contained in C \ {x}
  let H2 := G.deleteEdges {s(w, w')}
  have hnot_ww' : ¬ H2.Reachable w w' := SimpleGraph.isBridge_iff.mp hbr'
  have hside : ∀ (u v : V), G.Adj u v → G.IsBridge s(u, v) → u ∈ C →
      ¬ (G.deleteEdges {s(u, v)}).Reachable u x → False := by
    intro u v huv hbruv huC hno_x
    let Hu := G.deleteEdges {s(u, v)}
    let D := Finset.univ.filter (fun z => Hu.Reachable u z)
    have hsub : D ⊆ C.erase x := by
      intro z hz
      have hrz : Hu.Reachable u z := (Finset.mem_filter.mp hz).2
      have hzx : z ≠ x := fun h => hno_x (h ▸ hrz)
      refine Finset.mem_erase.mpr ⟨hzx, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
      rcases hrz with ⟨p⟩
      have hwalk_H : H.Reachable u z := by
        have hrec : ∀ {a' b' : V} (q : Hu.Walk a' b'),
            (∀ t ∈ q.support, Hu.Reachable u t) → H.Reachable a' b' := by
          intro a' b' q hq
          induction q with
          | nil => exact SimpleGraph.Reachable.refl _
          | @cons a1 a2 a3 hadj q' ih =>
            have ha1x : a1 ≠ x := fun h => hno_x (h ▸ hq a1 (by simp))
            have ha2x : a2 ≠ x := fun h => hno_x (h ▸ hq a2 (by simp))
            have hadj_H : H.Adj a1 a2 := by
              rw [SimpleGraph.deleteEdges_adj] at hadj ⊢
              refine ⟨hadj.1, ?_⟩
              simp only [Set.mem_singleton_iff, Sym2.eq_iff]
              rintro (⟨h1, _⟩ | ⟨_, h2⟩)
              · exact ha1x h1
              · exact ha2x h2
            exact hadj_H.reachable.trans (ih (fun t ht => hq t (by simp [ht])))
        exact hrec p (fun t ht => ⟨p.takeUntil t ht⟩)
      exact (Finset.mem_filter.mp huC).2.trans hwalk_H
    have hlt : D.card < k := by
      have hc1 := Finset.card_le_card hsub
      rw [Finset.card_erase_of_mem hxC, hcard] at hc1
      have hpos : 0 < k := hcard ▸ Finset.card_pos.mpr ⟨x, hxC⟩
      omega
    exact hmin D.card hlt ⟨u, v, huv, hbruv, rfl⟩
  by_cases hx1 : H2.Reachable w x
  · have hx2 : ¬ H2.Reachable w' x := fun h => hnot_ww' (hx1.trans h.symm)
    have hbr_symm : G.IsBridge s(w', w) := by rwa [Sym2.eq_swap]
    have hx2' : ¬ (G.deleteEdges {s(w', w)}).Reachable w' x := by
      simpa [H2, Sym2.eq_swap] using hx2
    exact hside w' w hww'.symm hbr_symm hw'C hx2'
  · exact hside w w' hww' hbr' hwC hx1

/- ### Part 2: Triangle contraction for connected cubic vertex-transitive C4-free graphs -/

private lemma vt_cubic_triangle_contraction {V : Type} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hconn : G.Connected) (hdeg : ∀ x, G.degree x = 3)
    (hvt : ∀ x y, ∃ g : G ≃g G, g x = y) (hc4 : ¬ cycleGraph 4 ⊑ G)
    (htri : ∃ a b c : V, G.Adj a b ∧ G.Adj b c ∧ G.Adj c a)
    (ih : ∀ (Q : Type) (GQ : SimpleGraph Q) [Fintype Q] [DecidableRel GQ.Adj],
      Fintype.card Q < Fintype.card V → GQ.Connected → (∀ q, GQ.degree q = 3) →
      (∀ q1 q2, ∃ g : GQ ≃g GQ, g q1 = q2) →
      ∃ k : ℕ, 2 ≤ k ∧ cycleGraph (2 ^ k) ⊑ GQ) :
    ∃ k : ℕ, 2 ≤ k ∧ cycleGraph (2 ^ k) ⊑ G := by
  -- Every vertex lies in a triangle by vertex-transitivity
  have hall_tri : ∀ x : V, ∃ y z : V, G.Adj x y ∧ G.Adj y z ∧ G.Adj z x := by
    obtain ⟨a0, b0, c0, hab, hbc, hca⟩ := htri
    intro x
    obtain ⟨g, hga⟩ := hvt a0 x
    exact ⟨g b0, g c0, hga ▸ g.map_rel_iff.mpr hab, g.map_rel_iff.mpr hbc,
      hga ▸ g.map_rel_iff.mpr hca⟩
  -- Uniqueness of the triangle at every vertex (cubic + C4-free)
  have htri_uniq : ∀ x y1 z1 y2 z2 : V,
      G.Adj x y1 → G.Adj y1 z1 → G.Adj z1 x →
      G.Adj x y2 → G.Adj y2 z2 → G.Adj z2 x →
      y2 = y1 ∨ y2 = z1 := by
    intro x y1 z1 y2 z2 hxy1 hyz1 hzx1 hxy2 hyz2 hzx2
    by_contra hno
    push Not at hno
    have hy1z1 : y1 ≠ z1 := G.ne_of_adj hyz1
    have hsub : ({y1, z1, y2} : Finset V) ⊆ G.neighborFinset x := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with h | h | h
      · rw [h]; exact (G.mem_neighborFinset x y1).mpr hxy1
      · rw [h]; exact (G.mem_neighborFinset x z1).mpr hzx1.symm
      · rw [h]; exact (G.mem_neighborFinset x y2).mpr hxy2
    have hcard3 : ({y1, z1, y2} : Finset V).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [hy1z1, hno.1.symm]),
        Finset.card_pair hno.2.symm]
    have heq_N : ({y1, z1, y2} : Finset V) = G.neighborFinset x :=
      Finset.eq_of_subset_of_card_le hsub (by rw [card_neighborFinset_eq_degree, hdeg x, hcard3])
    have hz2_mem : z2 ∈ ({y1, z1, y2} : Finset V) :=
      heq_N ▸ (G.mem_neighborFinset x z2).mpr hzx2.symm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz2_mem
    rcases hz2_mem with h | h | h
    · -- z2 = y1 gives C4: x - z1 - y1 - y2 - x
      rw [h] at hyz2
      rcases no_c4_of_not_copy hc4 hzx1.symm hyz1.symm hyz2.symm hxy2.symm with h1 | h1
      · exact G.ne_of_adj hxy1 h1
      · exact hno.2 h1.symm
    · -- z2 = z1 gives C4: x - y1 - z1 - y2 - x
      rw [h] at hyz2
      rcases no_c4_of_not_copy hc4 hxy1 hyz1 hyz2.symm hxy2.symm with h1 | h1
      · exact G.ne_of_adj hzx1 h1.symm
      · exact hno.1 h1.symm
    · exact G.loopless.irrefl y2 (h ▸ hyz2)
  -- Equivalence relation: same triangle
  let R : V → V → Prop := fun x y => x = y ∨ ∃ z : V, G.Adj x y ∧ G.Adj y z ∧ G.Adj z x
  have hR_refl : ∀ x, R x x := fun _ => Or.inl rfl
  have hR_symm : ∀ {x y}, R x y → R y x := by
    rintro x y (rfl | ⟨z, h1, h2, h3⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨z, h1.symm, h3.symm, h2.symm⟩
  have hR_trans : ∀ {x y w}, R x y → R y w → R x w := by
    rintro x y w (rfl | ⟨z1, hxy, hyz1, hz1x⟩) (rfl | ⟨z2, hyw, hwz2, hz2y⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨z2, hyw, hwz2, hz2y⟩
    · exact Or.inr ⟨z1, hxy, hyz1, hz1x⟩
    · rcases htri_uniq y x z1 w z2 hxy.symm hz1x.symm hyz1.symm hyw hwz2 hz2y with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr ⟨y, hz1x.symm, hyz1.symm, hxy.symm⟩
  let S : Setoid V := ⟨R, ⟨hR_refl, hR_symm, hR_trans⟩⟩
  let Q := Quotient S
  have : Finite Q := Finite.of_surjective (Quotient.mk S) Quotient.mk_surjective
  let : Fintype Q := Fintype.ofFinite Q
  -- Every equivalence class has size 3 and is a triangle
  have hclass_adj : ∀ x y : V, Quotient.mk S x = Quotient.mk S y → x ≠ y → G.Adj x y := by
    intro x y heq hne
    rcases Quotient.exact heq with h | ⟨_, h, _, _⟩
    · exact absurd h hne
    · exact h
  have hclass_tri : ∀ x : V, ∃ y z : V, G.Adj x y ∧ G.Adj y z ∧ G.Adj z x ∧
      Finset.univ.filter (fun w : V => Quotient.mk S w = Quotient.mk S x) = {x, y, z} := by
    intro x
    obtain ⟨y, z, hxy, hyz, hzx⟩ := hall_tri x
    refine ⟨y, z, hxy, hyz, hzx, ?_⟩
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, Quotient.eq]
    constructor
    · intro hwx
      rcases hwx with rfl | ⟨u, hwx', hxu, huw⟩
      · exact Or.inl rfl
      · rcases htri_uniq x y z w u hxy hyz hzx hwx'.symm huw.symm hxu.symm with rfl | rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr rfl)
    · rintro (rfl | rfl | rfl)
      · exact Or.inl rfl
      · exact Or.inr ⟨z, hxy.symm, hzx.symm, hyz.symm⟩
      · exact Or.inr ⟨y, hzx, hxy, hyz⟩
  have hfib_card : ∀ q : Q, (Finset.univ.filter (fun w : V => Quotient.mk S w = q)).card = 3 := by
    intro q
    induction q using Quotient.inductionOn with | h x =>
    obtain ⟨y, z, hxy, hyz, hzx, heq⟩ := hclass_tri x
    rw [heq, Finset.card_insert_of_notMem (by simp [G.ne_of_adj hxy, (G.ne_of_adj hzx).symm]),
      Finset.card_pair (G.ne_of_adj hyz)]
  have hcard_lt : Fintype.card Q < Fintype.card V := by
    have hsum := Finset.card_eq_sum_card_fiberwise (f := Quotient.mk S) (s := Finset.univ)
      (t := Finset.univ) (fun _ _ => Finset.mem_univ _)
    have h3 : Fintype.card V = 3 * Fintype.card Q := by
      calc Fintype.card V = (Finset.univ : Finset V).card := rfl
        _ = ∑ q ∈ (Finset.univ : Finset Q), (Finset.univ.filter (fun x => Quotient.mk S x = q)).card := hsum
        _ = ∑ _q ∈ (Finset.univ : Finset Q), 3 := Finset.sum_congr rfl (fun q _ => hfib_card q)
        _ = 3 * Fintype.card Q := by rw [Finset.sum_const, smul_eq_mul, Finset.card_univ]; ring
    have hpos : 0 < Fintype.card Q := by
      obtain ⟨v0⟩ := hconn.nonempty
      exact Fintype.card_pos_iff.mpr ⟨Quotient.mk S v0⟩
    omega
  -- Each vertex has a unique neighbor outside its triangle class
  have hout_uniq : ∀ x : V, ∃! y : V, G.Adj x y ∧ Quotient.mk S y ≠ Quotient.mk S x := by
    intro x
    obtain ⟨a, b, hxa, hab, hbx, hfilt⟩ := hclass_tri x
    have ha_ne_b : a ≠ b := G.ne_of_adj hab
    have hsub : ({a, b} : Finset V) ⊆ G.neighborFinset x := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with h | h
      · rw [h]; exact (G.mem_neighborFinset x a).mpr hxa
      · rw [h]; exact (G.mem_neighborFinset x b).mpr hbx.symm
    have hcard_diff : (G.neighborFinset x \ {a, b}).card = 1 := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub, card_neighborFinset_eq_degree, hdeg x,
        Finset.card_pair ha_ne_b]
    obtain ⟨y, hy_eq⟩ := Finset.card_eq_one.mp hcard_diff
    have hy_mem : y ∈ G.neighborFinset x \ {a, b} := by rw [hy_eq]; simp
    have ⟨hyN, hyab⟩ := Finset.mem_sdiff.mp hy_mem
    have hxy : G.Adj x y := (G.mem_neighborFinset x y).mp hyN
    have hyq : Quotient.mk S y ≠ Quotient.mk S x := by
      intro hq
      have hy_in : y ∈ Finset.univ.filter (fun w => Quotient.mk S w = Quotient.mk S x) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq⟩
      rw [hfilt] at hy_in
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy_in hyab
      rcases hy_in with rfl | rfl | rfl
      · exact G.loopless.irrefl y hxy
      · exact hyab (Or.inl rfl)
      · exact hyab (Or.inr rfl)
    refine ⟨y, ⟨hxy, hyq⟩, ?_⟩
    intro z ⟨hxz, hzq⟩
    have hz_diff : z ∈ G.neighborFinset x \ {a, b} := by
      refine Finset.mem_sdiff.mpr ⟨(G.mem_neighborFinset x z).mpr hxz, ?_⟩
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rintro (rfl | rfl)
      · exact hzq (Quotient.sound (Or.inr ⟨b, hxa.symm, hbx.symm, hab.symm⟩))
      · exact hzq (Quotient.sound (Or.inr ⟨a, hbx, hxa, hab⟩))
    rw [hy_eq, Finset.mem_singleton] at hz_diff
    exact hz_diff
  -- Between any two distinct classes, there is at most one edge
  have hbetween_uniq : ∀ {x1 x2 y1 y2 : V},
      Quotient.mk S x1 = Quotient.mk S x2 → Quotient.mk S y1 = Quotient.mk S y2 →
      Quotient.mk S x1 ≠ Quotient.mk S y1 →
      G.Adj x1 y1 → G.Adj x2 y2 → x1 = x2 ∧ y1 = y2 := by
    intro x1 x2 y1 y2 hqx hqy hqne h1 h2
    by_cases hx : x1 = x2
    · subst hx
      exact ⟨rfl, (hout_uniq x1).unique ⟨h1, hqne.symm⟩ ⟨h2, (hqy ▸ hqne).symm⟩⟩
    · by_cases hy : y1 = y2
      · subst hy
        exact ⟨(hout_uniq y1).unique ⟨h1.symm, hqne⟩ ⟨h2.symm, hqx ▸ hqne⟩, rfl⟩
      · have hx12 : G.Adj x1 x2 := hclass_adj x1 x2 hqx hx
        have hy12 : G.Adj y1 y2 := hclass_adj y1 y2 hqy hy
        rcases no_c4_of_not_copy hc4 hx12 h2 hy12.symm h1.symm with h | h
        · exact absurd (congrArg (Quotient.mk S) h) (hqy ▸ hqne)
        · exact absurd (congrArg (Quotient.mk S) h) (hqx ▸ hqne)
  -- Quotient simple graph GQ
  let GQ : SimpleGraph Q := {
    Adj := fun q1 q2 => q1 ≠ q2 ∧ ∃ x y : V, Quotient.mk S x = q1 ∧ Quotient.mk S y = q2 ∧ G.Adj x y
    symm := ⟨fun _ _ ⟨hne, x, y, hx, hy, hadj⟩ => ⟨hne.symm, y, x, hy, hx, hadj.symm⟩⟩
    loopless := ⟨fun _ ⟨hne, _⟩ => hne rfl⟩
  }
  have hGQ_conn : GQ.Connected := by
    obtain ⟨v0⟩ := hconn.nonempty
    refine { preconnected := ?_, nonempty := ⟨Quotient.mk S v0⟩ }
    intro q1 q2
    induction q1 using Quotient.inductionOn with | h x1 =>
    induction q2 using Quotient.inductionOn with | h x2 =>
    rcases hconn x1 x2 with ⟨p⟩
    induction p with
    | nil => exact SimpleGraph.Reachable.refl _
    | @cons u v w huv p' ih =>
      by_cases hq : Quotient.mk S u = Quotient.mk S v
      · rw [hq]; exact ih
      · exact SimpleGraph.Reachable.trans
          (SimpleGraph.Adj.reachable ⟨hq, u, v, rfl, rfl, huv⟩) ih
  have hGQ_deg : ∀ q : Q, GQ.degree q = 3 := by
    intro q
    rw [← card_neighborFinset_eq_degree, ← hfib_card q]
    symm
    let outV : V → V := fun x => (hout_uniq x).choose
    have hout_spec : ∀ x, G.Adj x (outV x) ∧ Quotient.mk S (outV x) ≠ Quotient.mk S x :=
      fun x => (hout_uniq x).choose_spec.1
    refine Finset.card_bij (fun x _ => Quotient.mk S (outV x)) ?_ ?_ ?_
    · intro x hx
      have hxq : Quotient.mk S x = q := (Finset.mem_filter.mp hx).2
      exact (GQ.mem_neighborFinset _ _).mpr
        ⟨(hxq ▸ (hout_spec x).2).symm, x, outV x, hxq, rfl, (hout_spec x).1⟩
    · intro x1 hx1 x2 hx2 heq
      have h1 : Quotient.mk S x1 = q := (Finset.mem_filter.mp hx1).2
      have h2 : Quotient.mk S x2 = q := (Finset.mem_filter.mp hx2).2
      exact (hbetween_uniq (h1.trans h2.symm) heq (hout_spec x1).2.symm
        (hout_spec x1).1 (hout_spec x2).1).1
    · intro q' hq'
      obtain ⟨hne, x, y, hxq, hyq', hxy⟩ := (GQ.mem_neighborFinset _ _).mp hq'
      have hy_eq : outV x = y := (hout_uniq x).unique (hout_spec x) ⟨hxy, by rw [hxq, hyq']; exact hne.symm⟩
      exact ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxq⟩, by rw [hy_eq, hyq']⟩
  have hGQ_vt : ∀ q1 q2 : Q, ∃ g : GQ ≃g GQ, g q1 = q2 := by
    intro q1 q2
    induction q1 using Quotient.inductionOn with | h x1 =>
    induction q2 using Quotient.inductionOn with | h x2 =>
    obtain ⟨g, hgx⟩ := hvt x1 x2
    have hR_map : ∀ {u v : V}, R u v → R (g u) (g v) := by
      rintro u v (rfl | ⟨z, h1, h2, h3⟩)
      · exact Or.inl rfl
      · exact Or.inr ⟨g z, g.map_rel_iff.mpr h1, g.map_rel_iff.mpr h2, g.map_rel_iff.mpr h3⟩
    have hR_inv : ∀ {u v : V}, R u v → R (g.symm u) (g.symm v) := by
      rintro u v (rfl | ⟨z, h1, h2, h3⟩)
      · exact Or.inl rfl
      · exact Or.inr ⟨g.symm z, g.symm.map_rel_iff.mpr h1, g.symm.map_rel_iff.mpr h2,
          g.symm.map_rel_iff.mpr h3⟩
    let toF : Q → Q := Quotient.map g (fun _ _ h => hR_map h)
    let invF : Q → Q := Quotient.map g.symm (fun _ _ h => hR_inv h)
    have hleft : LeftInverse invF toF := by
      intro q; induction q using Quotient.inductionOn with | h x =>
      exact congrArg (Quotient.mk S) (g.symm_apply_apply x)
    have hright : RightInverse invF toF := by
      intro q; induction q using Quotient.inductionOn with | h x =>
      exact congrArg (Quotient.mk S) (g.apply_symm_apply x)
    let e : Q ≃ Q := ⟨toF, invF, hleft, hright⟩
    have hmap : ∀ {a b : Q}, GQ.Adj (e a) (e b) ↔ GQ.Adj a b := by
      intro a b
      constructor
      · rintro ⟨hne, x, y, hx, hy, hxy⟩
        refine ⟨fun h => hne (congrArg e h), g.symm x, g.symm y, ?_, ?_, g.symm.map_rel_iff.mpr hxy⟩
        · have : invF (toF a) = invF (Quotient.mk S x) := congrArg invF hx.symm
          exact this.symm.trans (hleft a)
        · have : invF (toF b) = invF (Quotient.mk S y) := congrArg invF hy.symm
          exact this.symm.trans (hleft b)
      · rintro ⟨hne, x, y, hx, hy, hxy⟩
        refine ⟨fun h => hne (e.injective h), g x, g y, ?_, ?_, g.map_rel_iff.mpr hxy⟩
        · exact congrArg toF hx
        · exact congrArg toF hy
    exact ⟨⟨e, hmap⟩, congrArg (Quotient.mk S) hgx⟩
  -- Apply IH on GQ and lift a 2^k-cycle in GQ to a 2^(k+1)-cycle in G
  obtain ⟨k, hk, ⟨c⟩⟩ := ih Q GQ hcard_lt hGQ_conn hGQ_deg hGQ_vt
  obtain ⟨m, hm_eq, hm4⟩ : ∃ m : ℕ, m = 2 ^ k ∧ 4 ≤ m :=
    ⟨2 ^ k, rfl, calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk⟩
  rw [← hm_eq] at c
  let : NeZero m := ⟨by omega⟩
  have hstep_adj : ∀ i : Fin m, GQ.Adj (c i) (c (i + 1)) := by
    intro i
    apply c.toHom.map_rel'
    apply cycleGraph_adj'.mpr
    right
    simp [Nat.mod_eq_of_lt (show 1 < m by omega)]
  -- For each i : Fin m, choose the unique edge (outV i, inV (i + 1)) from c i to c (i + 1)
  have hedge : ∀ i : Fin m, ∃ xy : V × V,
      Quotient.mk S xy.1 = c i ∧ Quotient.mk S xy.2 = c (i + 1) ∧ G.Adj xy.1 xy.2 := by
    intro i
    obtain ⟨_, x, y, hx, hy, hxy⟩ := hstep_adj i
    exact ⟨(x, y), hx, hy, hxy⟩
  let outV : Fin m → V := fun i => (Classical.choose (hedge i)).1
  let inV : Fin m → V := fun i => (Classical.choose (hedge (i - 1))).2
  have hout_q : ∀ i : Fin m, Quotient.mk S (outV i) = c i :=
    fun i => (Classical.choose_spec (hedge i)).1
  have hin_q : ∀ i : Fin m, Quotient.mk S (inV i) = c i := by
    intro i
    have h := (Classical.choose_spec (hedge (i - 1))).2.1
    simpa [inV, sub_add_cancel] using h
  have hbridge_adj : ∀ i : Fin m, G.Adj (outV i) (inV (i + 1)) := by
    intro i
    have h := (Classical.choose_spec (hedge i)).2.2
    simpa [inV, add_sub_cancel_right] using h
  have hin_ne_out : ∀ i : Fin m, inV i ≠ outV i := by
    intro i heq
    have h1 : G.Adj (inV i) (outV (i - 1)) := by
      have h := hbridge_adj (i - 1)
      simpa [sub_add_cancel] using h.symm
    have h2 : G.Adj (inV i) (inV (i + 1)) := heq ▸ hbridge_adj i
    have hq1 : Quotient.mk S (outV (i - 1)) ≠ Quotient.mk S (inV i) := by
      rw [hout_q, hin_q]
      intro h
      have hi := c.injective h
      have h10 : (1 : Fin m) = 0 := by
        simpa [sub_eq_add_neg] using congrArg (· - i) hi.symm
      have : (1 : Fin m).val = 0 := congrArg Fin.val h10
      rw [Fin.val_one', Nat.mod_eq_of_lt (by omega)] at this
      omega
    have hq2 : Quotient.mk S (inV (i + 1)) ≠ Quotient.mk S (inV i) := by
      rw [hin_q, hin_q]
      intro h
      have hi := c.injective h
      have h10 : (1 : Fin m) = 0 := by simpa using congrArg (· - i) hi
      have : (1 : Fin m).val = 0 := congrArg Fin.val h10
      rw [Fin.val_one', Nat.mod_eq_of_lt (by omega)] at this
      omega
    have heq_nb : outV (i - 1) = inV (i + 1) :=
      (hout_uniq (inV i)).unique ⟨h1, hq1⟩ ⟨h2, hq2⟩
    have hc_eq : c (i - 1) = c (i + 1) := by
      rw [← hout_q, heq_nb, hin_q]
    have hi_eq : i - 1 = i + 1 := c.injective hc_eq
    have h20 : (1 : Fin m) + 1 = 0 := by
      have h1 : i + (1 + 1) = i + 0 := by
        rw [← add_assoc, ← hi_eq, sub_add_cancel, add_zero]
      exact add_left_cancel h1
    have hv : ((1 : Fin m) + 1).val = 0 := congrArg Fin.val h20
    rw [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (show 1 < m by omega),
      Nat.mod_eq_of_lt (show 1 + 1 < m by omega)] at hv
    omega
  have htri_adj : ∀ i : Fin m, G.Adj (inV i) (outV i) :=
    fun i => hclass_adj _ _ ((hin_q i).trans (hout_q i).symm) (hin_ne_out i)
  -- Build the 2^(k+1)-cycle in G: [inV 0, outV 0, inV 1, outV 1, ...]
  let seq : ℕ → V := fun j =>
    let idx : Fin m := ⟨(j / 2) % m, Nat.mod_lt _ (by omega)⟩
    if j % 2 = 0 then inV idx else outV idx
  let L : List V := (List.range (2 * m)).map seq
  have hL_len : L.length = 2 ^ (k + 1) := by
    simp [L, hm_eq, pow_succ, mul_comm]
  have hseq_inj : ∀ a b : ℕ, a < 2 * m → b < 2 * m → seq a = seq b → a = b := by
    intro a b ha hb hab
    have hqa : Quotient.mk S (seq a) = c ⟨a / 2, by omega⟩ := by
      simp only [seq, Nat.mod_eq_of_lt (show a / 2 < m by omega)]
      split_ifs <;> simp [hin_q, hout_q]
    have hqb : Quotient.mk S (seq b) = c ⟨b / 2, by omega⟩ := by
      simp only [seq, Nat.mod_eq_of_lt (show b / 2 < m by omega)]
      split_ifs <;> simp [hin_q, hout_q]
    have hdiv : a / 2 = b / 2 :=
      congrArg Fin.val (c.injective (hqa.symm.trans ((congrArg (Quotient.mk S) hab).trans hqb)))
    have hmod : a % 2 = b % 2 := by
      by_contra hne_m
      have hidx : (⟨(a / 2) % m, Nat.mod_lt _ (by omega)⟩ : Fin m) =
          ⟨(b / 2) % m, Nat.mod_lt _ (by omega)⟩ := by simp [hdiv]
      simp only [seq, hidx] at hab
      split_ifs at hab with h1 h2
      · omega
      · exact hin_ne_out _ hab
      · exact hin_ne_out _ hab.symm
      · omega
    omega
  have hL_nodup : L.Nodup := by
    rw [List.nodup_map_iff_inj_on List.nodup_range]
    intro a ha b hb hab
    exact hseq_inj a b (List.mem_range.mp ha) (List.mem_range.mp hb) hab
  have hseq_step : ∀ j : ℕ, j + 1 < 2 * m → G.Adj (seq j) (seq (j + 1)) := by
    intro j hj
    by_cases heven : j % 2 = 0
    · have hodd : (j + 1) % 2 ≠ 0 := by omega
      have hdiv : (j + 1) / 2 = j / 2 := by omega
      simp only [seq, heven, ↓reduceIte, hodd, hdiv]
      exact htri_adj _
    · have hnext : (j + 1) % 2 = 0 := by omega
      have hdiv : (j + 1) / 2 = j / 2 + 1 := by omega
      have hlt1 : j / 2 < m := by omega
      have hlt2 : j / 2 + 1 < m := by omega
      have hidx_eq : (⟨(j / 2 + 1) % m, Nat.mod_lt _ (by omega)⟩ : Fin m) =
          (⟨(j / 2) % m, Nat.mod_lt _ (by omega)⟩ : Fin m) + 1 := by
        apply Fin.ext
        simp only [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt hlt1, Nat.mod_eq_of_lt hlt2,
          Nat.mod_eq_of_lt (show 1 < m by omega)]
      simp only [seq, heven, ↓reduceIte, hnext, hdiv, hidx_eq]
      exact hbridge_adj _
  have hL_chain : L.IsChain G.Adj := by
    rw [List.isChain_iff_getElem]
    intro j hj
    have hj' : j + 1 < 2 * m := by simpa [L] using hj
    simpa [L] using hseq_step j hj'
  have hL_close : ∀ h : L ≠ [], G.Adj (L.getLast h) (L.head h) := by
    intro h
    have hlast : L.getLast h = seq (2 * m - 1) := by
      rw [List.getLast_eq_getElem]
      simp [L]
    have hhead : L.head h = seq 0 := by
      rw [List.head_eq_getElem]
      simp [L]
    rw [hlast, hhead]
    have hodd : (2 * m - 1) % 2 ≠ 0 := by omega
    have hdiv : (2 * m - 1) / 2 = m - 1 := by omega
    have hidx0 : (⟨0, by omega⟩ : Fin m) =
        (⟨(m - 1) % m, Nat.mod_lt _ (by omega)⟩ : Fin m) + 1 := by
      apply Fin.ext
      simp only [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (show m - 1 < m by omega),
        Nat.mod_eq_of_lt (show 1 < m by omega), show m - 1 + 1 = m by omega, Nat.mod_self]
    simp only [seq, hodd, ↓reduceIte, hdiv, Nat.zero_div, Nat.zero_mod]
    rw [hidx0]
    exact hbridge_adj _
  have hcyc := OMA.R_Erdos64_erdos_64_R4.cycle_of_ring G L (by rw [hL_len]; omega)
    hL_nodup hL_chain hL_close
  exact ⟨k + 1, by omega, hL_len ▸ hcyc⟩

/- ### Part 3: Transitive-commuting involution elimination (2-cover descent) -/

private lemma vt_cubic_central_involution {V : Type} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hconn : G.Connected) (hdeg : ∀ x, G.degree x = 3)
    (hc4 : ¬ cycleGraph 4 ⊑ G)
    (σ : G ≃g G) (hσ_ne : σ ≠ 1) (hinv : ∀ x, σ (σ x) = x)
    (hvt_comm : ∀ x y : V, ∃ g : G ≃g G, g x = y ∧ ∀ z, g (σ z) = σ (g z))
    (ih : ∀ (Q : Type) (GQ : SimpleGraph Q) [Fintype Q] [DecidableRel GQ.Adj],
      Fintype.card Q < Fintype.card V → GQ.Connected → (∀ q, GQ.degree q = 3) →
      (∀ q1 q2, ∃ g : GQ ≃g GQ, g q1 = q2) →
      ∃ k : ℕ, 2 ≤ k ∧ cycleGraph (2 ^ k) ⊑ GQ) :
    ∃ k : ℕ, 2 ≤ k ∧ cycleGraph (2 ^ k) ⊑ G := by
  -- 1. σ is fixed-point-free
  have hfree : ∀ x : V, σ x ≠ x := by
    intro x hfix
    apply hσ_ne
    ext y
    obtain ⟨g, hgx, hcomm⟩ := hvt_comm x y
    rw [← hgx, ← hcomm x, hfix]
    rfl
  -- 2. σ is non-adjacent everywhere (else C4!)
  have hnadj : ∀ x : V, ¬ G.Adj x (σ x) := by
    intro x hloop
    have hall_loop : ∀ y : V, G.Adj y (σ y) := by
      intro y
      obtain ⟨g, hgx, hcomm⟩ := hvt_comm x y
      rw [← hgx, ← hcomm x]
      exact g.map_rel_iff.mpr hloop
    have hex_y : ∃ y : V, G.Adj x y ∧ y ≠ σ x := by
      by_contra hno
      push Not at hno
      have hsub : G.neighborFinset x ⊆ {σ x} := fun z hz =>
        Finset.mem_singleton.mpr (hno z ((G.mem_neighborFinset x z).mp hz))
      have hc := Finset.card_le_card hsub
      rw [card_neighborFinset_eq_degree, hdeg x, Finset.card_singleton] at hc
      omega
    obtain ⟨y, hxy, hne⟩ := hex_y
    have hdiff : x ≠ σ y := fun h => hne ((hinv y).symm.trans (congrArg σ h.symm))
    exact hc4 (OMA.R_Erdos64_erdos_64_R4.square_of_four hxy (hall_loop y)
      (σ.map_rel_iff.mpr hxy).symm hloop.symm hdiff hne)
  -- 3. Quotient by {x, σ x} via R4.pair_projection
  obtain ⟨W, fw, q, honto, hpair, hcard_eq, hfib⟩ :=
    OMA.R_Erdos64_erdos_64_R4.pair_projection (fun x => σ x) hinv hfree
  let : Fintype W := fw
  have hqσ : ∀ x, q (σ x) = q x := fun x => (hpair _ _).mpr (Or.inr rfl)
  have hcard_lt : Fintype.card W < Fintype.card V := by
    have hpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr hconn.nonempty
    omega
  have hedge_distinct : ∀ {x y : V}, G.Adj x y → q x ≠ q y := by
    intro x y hxy hq
    rcases (hpair _ _).mp hq with rfl | rfl
    · exact G.loopless.irrefl x hxy
    · exact hnadj y hxy.symm
  have hnb_inj : ∀ {x y z : V}, G.Adj x y → G.Adj x z → q y = q z → y = z := by
    intro x y z hxy hxz hq
    rcases (hpair _ _).mp hq with rfl | rfl
    · rfl
    · have hacross : G.Adj z (σ x) := by
        have h := σ.map_rel_iff.mpr hxy
        rw [hinv z] at h
        exact h.symm
      exact (hc4 (OMA.R_Erdos64_erdos_64_R4.square_of_four hxz hacross
        (σ.map_rel_iff.mpr hxz) hxy.symm (hfree x).symm (hfree z).symm)).elim
  let B : SimpleGraph W := G.map q
  have hlift : ∀ (x : V) (w : W), B.Adj (q x) w → ∃! y : V, G.Adj x y ∧ q y = w := by
    intro x w hbw
    obtain ⟨_, a, b, hab, ha, hb⟩ := (SimpleGraph.map_adj' q G _ _).mp hbw
    rcases (hpair a x).mp ha with rfl | rfl
    · exact ⟨b, ⟨hab, hb⟩, fun y ⟨hxy, hqy⟩ => hnb_inj hxy hab (hqy.trans hb.symm)⟩
    · refine ⟨σ b, ⟨?_, (hqσ b).trans hb⟩, fun y ⟨hxy, hqy⟩ => ?_⟩
      · have h := σ.map_rel_iff.mpr hab
        rwa [hinv x] at h
      · have h := σ.map_rel_iff.mpr hab
        rw [hinv x] at h
        exact hnb_inj hxy h (hqy.trans ((hqσ b).trans hb).symm)
  have hB_conn : B.Connected := by
    obtain ⟨v0⟩ := hconn.nonempty
    refine { preconnected := ?_, nonempty := ⟨q v0⟩ }
    intro w1 w2
    obtain ⟨x1, rfl⟩ := honto w1
    obtain ⟨x2, rfl⟩ := honto w2
    rcases hconn x1 x2 with ⟨p⟩
    induction p with
    | nil => exact SimpleGraph.Reachable.refl _
    | @cons u v z huv _ ih =>
      have hadj : B.Adj (q u) (q v) := (SimpleGraph.map_adj' q G _ _).mpr
        ⟨hedge_distinct huv, u, v, huv, rfl, rfl⟩
      exact hadj.reachable.trans ih
  have hB_deg : ∀ w : W, B.degree w = 3 := by
    intro w
    obtain ⟨x, rfl⟩ := honto w
    rw [← card_neighborFinset_eq_degree, ← hdeg x, ← card_neighborFinset_eq_degree]
    symm
    refine Finset.card_bij (fun y _ => q y) ?_ ?_ ?_
    · intro y hy
      have hxy := (G.mem_neighborFinset x y).mp hy
      exact (B.mem_neighborFinset _ _).mpr ((SimpleGraph.map_adj' q G _ _).mpr
        ⟨hedge_distinct hxy, x, y, hxy, rfl, rfl⟩)
    · intro y1 hy1 y2 hy2 heq
      exact hnb_inj ((G.mem_neighborFinset x y1).mp hy1) ((G.mem_neighborFinset x y2).mp hy2) heq
    · intro w' hw'
      obtain ⟨y, ⟨hxy, hqy⟩, _⟩ := hlift x w' ((B.mem_neighborFinset _ _).mp hw')
      exact ⟨y, (G.mem_neighborFinset x y).mpr hxy, hqy⟩
  have hB_vt : ∀ w1 w2 : W, ∃ g : B ≃g B, g w1 = w2 := by
    intro w1 w2
    obtain ⟨x1, rfl⟩ := honto w1
    obtain ⟨x2, rfl⟩ := honto w2
    obtain ⟨g, hgx, hcomm⟩ := hvt_comm x1 x2
    have hcomm_inv : ∀ z : V, g.symm (σ z) = σ (g.symm z) := by
      intro z
      apply g.injective
      rw [g.apply_symm_apply, hcomm, g.apply_symm_apply]
    let toF : W → W := fun w => q (g (Classical.choose (honto w)))
    let invF : W → W := fun w => q (g.symm (Classical.choose (honto w)))
    have hto_eq : ∀ x : V, toF (q x) = q (g x) := by
      intro x
      have hx := Classical.choose_spec (honto (q x))
      rcases (hpair _ _).mp hx with h | h
      · simp [toF, h]
      · simp only [toF, h, hcomm, hqσ]
    have hinv_eq : ∀ x : V, invF (q x) = q (g.symm x) := by
      intro x
      have hx := Classical.choose_spec (honto (q x))
      rcases (hpair _ _).mp hx with h | h
      · simp [invF, h]
      · simp only [invF, h, hcomm_inv, hqσ]
    have hleft : LeftInverse invF toF := by
      intro w; obtain ⟨x, rfl⟩ := honto w
      rw [hto_eq, hinv_eq, g.symm_apply_apply]
    have hright : RightInverse invF toF := by
      intro w; obtain ⟨x, rfl⟩ := honto w
      rw [hinv_eq, hto_eq, g.apply_symm_apply]
    let e : W ≃ W := ⟨toF, invF, hleft, hright⟩
    have hmap : ∀ {a b : W}, B.Adj (e a) (e b) ↔ B.Adj a b := by
      intro a b
      obtain ⟨x, rfl⟩ := honto a
      obtain ⟨y, rfl⟩ := honto b
      change B.Adj (toF (q x)) (toF (q y)) ↔ B.Adj (q x) (q y)
      rw [hto_eq, hto_eq]
      constructor
      · intro hadj
        obtain ⟨hne, u, v, huv, hu, hv⟩ := (SimpleGraph.map_adj' q G _ _).mp hadj
        refine (SimpleGraph.map_adj' q G _ _).mpr
          ⟨fun h => hne (by rw [← hto_eq, ← hto_eq, h]), g.symm u, g.symm v,
            g.symm.map_rel_iff.mpr huv, ?_, ?_⟩
        · have : invF (q u) = invF (q (g x)) := congrArg invF hu
          simpa [hinv_eq] using this
        · have : invF (q v) = invF (q (g y)) := congrArg invF hv
          simpa [hinv_eq] using this
      · intro hadj
        obtain ⟨hne, u, v, huv, hu, hv⟩ := (SimpleGraph.map_adj' q G _ _).mp hadj
        refine (SimpleGraph.map_adj' q G _ _).mpr
          ⟨fun h => hne (by have := congrArg invF h; simpa [hinv_eq] using this), g u, g v,
            g.map_rel_iff.mpr huv, ?_, ?_⟩
        · have : toF (q u) = toF (q x) := congrArg toF hu
          simpa [hto_eq] using this
        · have : toF (q v) = toF (q y) := congrArg toF hv
          simpa [hto_eq] using this
    exact ⟨⟨e, hmap⟩, by change toF (q x1) = q x2; rw [hto_eq, hgx]⟩
  -- Apply IH on B and lift via R4.lift_two
  obtain ⟨k, hk, ⟨c⟩⟩ := ih W B hcard_lt hB_conn hB_deg hB_vt
  have hge3 : 3 ≤ 2 ^ k := by
    calc (3 : ℕ) ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  rcases OMA.R_Erdos64_erdos_64_R4.lift_two q honto (fun w => (hfib w).le) hge3 c hlift with h1 | h2
  · exact ⟨k, hk, h1⟩
  · exact ⟨k + 1, by omega, by rw [pow_succ, mul_comm]; exact h2⟩

/- ### Part 4: Order bounds (even, Moore ≥ 10, and |V| ≠ 12) -/

private lemma even_card_of_cubic {V : Type} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hdeg : ∀ x, G.degree x = 3) : Even (Fintype.card V) := by
  have hsum := G.sum_degrees_eq_twice_card_edges
  have h3 : ∑ v : V, G.degree v = 3 * Fintype.card V := by
    calc ∑ v : V, G.degree v = ∑ _v : V, 3 := Finset.sum_congr rfl (fun v _ => hdeg v)
      _ = 3 * Fintype.card V := by rw [Finset.sum_const, smul_eq_mul, Finset.card_univ]; ring
  rw [h3] at hsum
  exact ⟨G.edgeFinset.card - Fintype.card V, by omega⟩

private lemma pair_adj_ne {V : Type} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (hdeg : ∀ x, G.degree x = 3) {u v a b : V}
    (huv : G.Adj u v) (hA : (G.neighborFinset v).erase u = {a, b}) :
    G.Adj v a ∧ G.Adj v b ∧ a ≠ u ∧ b ≠ u ∧ a ≠ b := by
  have ha := Finset.mem_erase.mp (show a ∈ (G.neighborFinset v).erase u by rw [hA]; simp)
  have hb := Finset.mem_erase.mp (show b ∈ (G.neighborFinset v).erase u by rw [hA]; simp)
  have hne : a ≠ b := by
    have hc : ({a, b} : Finset V).card = 2 := by
      rw [← hA, Finset.card_erase_of_mem ((G.mem_neighborFinset v u).mpr huv.symm),
        card_neighborFinset_eq_degree, hdeg v]
    intro h; subst h; simp at hc
  exact ⟨(G.mem_neighborFinset v a).mp ha.2, (G.mem_neighborFinset v b).mp hb.2, ha.1, hb.1, hne⟩

private lemma n1_ne_n2 {V : Type} {G : SimpleGraph V}
    (htf : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    {u x y v : V} (hux : G.Adj u x) (huv : G.Adj u v) (hvy : G.Adj v y) : x ≠ y := by
  intro h; rw [← h] at hvy; exact htf u v x huv hvy hux.symm

private lemma n2_disj {V : Type} {G : SimpleGraph V} (hc4 : ¬ cycleGraph 4 ⊑ G)
    {u vi vj x y : V} (huvi : G.Adj u vi) (huvj : G.Adj u vj) (hvne : vi ≠ vj)
    (hvix : G.Adj vi x) (hxu : x ≠ u) (hvjy : G.Adj vj y) : x ≠ y := by
  intro h; rw [← h] at hvjy
  rcases no_c4_of_not_copy hc4 huvi hvix hvjy.symm huvj.symm with h1 | h1
  · exact hxu h1.symm
  · exact hvne h1

private lemma no_both_nb {V : Type} {G : SimpleGraph V} (hc4 : ¬ cycleGraph 4 ⊑ G)
    {v x y z : V} (hvx : G.Adj v x) (hvy : G.Adj v y) (hxy : x ≠ y) (hzv : z ≠ v)
    (hzx : G.Adj z x) : ¬ G.Adj z y := by
  intro hzy
  rcases no_c4_of_not_copy hc4 hvx hzx.symm hzy hvy.symm with h | h
  · exact hzv h.symm
  · exact hxy h

private lemma far_ne_n1 {V : Type} {G : SimpleGraph V} {u v w : V}
    (hw : w ≠ u ∧ ¬ G.Adj u w ∧ ∀ x, G.Adj u x → ¬ G.Adj x w) (huv : G.Adj u v) : w ≠ v := by
  intro e; rw [e] at hw; exact hw.2.1 huv

private lemma far_ne_n2 {V : Type} {G : SimpleGraph V} {u v x w : V}
    (hw : w ≠ u ∧ ¬ G.Adj u w ∧ ∀ t, G.Adj u t → ¬ G.Adj t w) (huv : G.Adj u v)
    (hvx : G.Adj v x) : w ≠ x := by
  intro e; rw [e] at hw; exact hw.2.2 v huv hvx

private lemma bfs10_nodup {V : Type} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (hdeg : ∀ x, G.degree x = 3)
    (htf : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    (hc4 : ¬ cycleGraph 4 ⊑ G)
    {u vp vq vr p1 p2 q1 q2 r1 r2 : V}
    (huvp : G.Adj u vp) (huvq : G.Adj u vq) (huvr : G.Adj u vr)
    (hpq : vp ≠ vq) (hpr : vp ≠ vr) (hqr : vq ≠ vr)
    (hAp : (G.neighborFinset vp).erase u = {p1, p2})
    (hAq : (G.neighborFinset vq).erase u = {q1, q2})
    (hAr : (G.neighborFinset vr).erase u = {r1, r2}) :
    ([u, vp, vq, vr, p1, p2, q1, q2, r1, r2] : List V).Nodup := by
  obtain ⟨hvpp1, hvpp2, hp1u, hp2u, hp12⟩ := pair_adj_ne hdeg huvp hAp
  obtain ⟨hvqq1, hvqq2, hq1u, hq2u, hq12⟩ := pair_adj_ne hdeg huvq hAq
  obtain ⟨hvrr1, hvrr2, hr1u, hr2u, hr12⟩ := pair_adj_ne hdeg huvr hAr
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil,
    not_false_eq_true, and_true]
  refine ⟨⟨G.ne_of_adj huvp, G.ne_of_adj huvq, G.ne_of_adj huvr, hp1u.symm, hp2u.symm,
      hq1u.symm, hq2u.symm, hr1u.symm, hr2u.symm⟩,
    ⟨hpq, hpr, n1_ne_n2 htf huvp huvp hvpp1, n1_ne_n2 htf huvp huvp hvpp2,
      n1_ne_n2 htf huvp huvq hvqq1, n1_ne_n2 htf huvp huvq hvqq2,
      n1_ne_n2 htf huvp huvr hvrr1, n1_ne_n2 htf huvp huvr hvrr2⟩,
    ⟨hqr, n1_ne_n2 htf huvq huvp hvpp1, n1_ne_n2 htf huvq huvp hvpp2,
      n1_ne_n2 htf huvq huvq hvqq1, n1_ne_n2 htf huvq huvq hvqq2,
      n1_ne_n2 htf huvq huvr hvrr1, n1_ne_n2 htf huvq huvr hvrr2⟩,
    ⟨n1_ne_n2 htf huvr huvp hvpp1, n1_ne_n2 htf huvr huvp hvpp2,
      n1_ne_n2 htf huvr huvq hvqq1, n1_ne_n2 htf huvr huvq hvqq2,
      n1_ne_n2 htf huvr huvr hvrr1, n1_ne_n2 htf huvr huvr hvrr2⟩,
    ⟨hp12, n2_disj hc4 huvp huvq hpq hvpp1 hp1u hvqq1,
      n2_disj hc4 huvp huvq hpq hvpp1 hp1u hvqq2,
      n2_disj hc4 huvp huvr hpr hvpp1 hp1u hvrr1,
      n2_disj hc4 huvp huvr hpr hvpp1 hp1u hvrr2⟩,
    ⟨n2_disj hc4 huvp huvq hpq hvpp2 hp2u hvqq1,
      n2_disj hc4 huvp huvq hpq hvpp2 hp2u hvqq2,
      n2_disj hc4 huvp huvr hpr hvpp2 hp2u hvrr1,
      n2_disj hc4 huvp huvr hpr hvpp2 hp2u hvrr2⟩,
    ⟨hq12, n2_disj hc4 huvq huvr hqr hvqq1 hq1u hvrr1,
      n2_disj hc4 huvq huvr hqr hvqq1 hq1u hvrr2⟩,
    ⟨n2_disj hc4 huvq huvr hqr hvqq2 hq2u hvrr1,
      n2_disj hc4 huvq huvr hqr hvqq2 hq2u hvrr2⟩,
    hr12⟩

private lemma bfs12_cover {V : Type} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (hcard12 : Fintype.card V = 12) (hdeg : ∀ x, G.degree x = 3)
    (htf : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    (hc4 : ¬ cycleGraph 4 ⊑ G)
    {u vp vq vr p1 p2 q1 q2 r1 r2 w1 w2 : V}
    (huvp : G.Adj u vp) (huvq : G.Adj u vq) (huvr : G.Adj u vr)
    (hpq : vp ≠ vq) (hpr : vp ≠ vr) (hqr : vq ≠ vr)
    (hAp : (G.neighborFinset vp).erase u = {p1, p2})
    (hAq : (G.neighborFinset vq).erase u = {q1, q2})
    (hAr : (G.neighborFinset vr).erase u = {r1, r2})
    (hw12 : w1 ≠ w2)
    (hw1 : w1 ≠ u ∧ ¬ G.Adj u w1 ∧ ∀ v, G.Adj u v → ¬ G.Adj v w1)
    (hw2 : w2 ≠ u ∧ ¬ G.Adj u w2 ∧ ∀ v, G.Adj u v → ¬ G.Adj v w2) :
    ∀ z : V, z = u ∨ z = vp ∨ z = vq ∨ z = vr ∨
      z = p1 ∨ z = p2 ∨ z = q1 ∨ z = q2 ∨ z = r1 ∨ z = r2 ∨ z = w1 ∨ z = w2 := by
  obtain ⟨hvpp1, hvpp2, _, _, _⟩ := pair_adj_ne hdeg huvp hAp
  obtain ⟨hvqq1, hvqq2, _, _, _⟩ := pair_adj_ne hdeg huvq hAq
  obtain ⟨hvrr1, hvrr2, _, _, _⟩ := pair_adj_ne hdeg huvr hAr
  have h10 := bfs10_nodup hdeg htf hc4 huvp huvq huvr hpq hpr hqr hAp hAq hAr
  have hfar_not : ∀ w : V, (w ≠ u ∧ ¬ G.Adj u w ∧ ∀ v, G.Adj u v → ¬ G.Adj v w) →
      w ∉ ([u, vp, vq, vr, p1, p2, q1, q2, r1, r2] : List V) := by
    intro w hw hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with h | h | h | h | h | h | h | h | h | h
    · exact hw.1 h
    · exact far_ne_n1 hw huvp h
    · exact far_ne_n1 hw huvq h
    · exact far_ne_n1 hw huvr h
    · exact far_ne_n2 hw huvp hvpp1 h
    · exact far_ne_n2 hw huvp hvpp2 h
    · exact far_ne_n2 hw huvq hvqq1 h
    · exact far_ne_n2 hw huvq hvqq2 h
    · exact far_ne_n2 hw huvr hvrr1 h
    · exact far_ne_n2 hw huvr hvrr2 h
  let L12 : List V := [u, vp, vq, vr, p1, p2, q1, q2, r1, r2, w1, w2]
  have hL12_nd : L12.Nodup := by
    change ([u, vp, vq, vr, p1, p2, q1, q2, r1, r2] ++ [w1, w2]).Nodup
    refine List.nodup_append.mpr ⟨h10, by simp [hw12], ?_⟩
    intro x hx y hy hxy
    rw [hxy] at hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with h | h
    · rw [h] at hx; exact hfar_not w1 hw1 hx
    · rw [h] at hx; exact hfar_not w2 hw2 hx
  have hL12_univ : L12.toFinset = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [List.toFinset_card_of_nodup hL12_nd, hcard12]
    rfl
  intro z
  have hz : z ∈ L12 := List.mem_toFinset.mp (by rw [hL12_univ]; exact Finset.mem_univ z)
  simpa only [L12, List.mem_cons, List.not_mem_nil, or_false] using hz

private lemma n2_nb_of_nadj_w {V : Type} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (hcard12 : Fintype.card V = 12) (hdeg : ∀ x, G.degree x = 3)
    (htf : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    (hc4 : ¬ cycleGraph 4 ⊑ G)
    {u vp vq vr p1 p2 q1 q2 r1 r2 w1 w2 : V}
    (huvp : G.Adj u vp) (huvq : G.Adj u vq) (huvr : G.Adj u vr)
    (hpq : vp ≠ vq) (hpr : vp ≠ vr) (hqr : vq ≠ vr)
    (hAp : (G.neighborFinset vp).erase u = {p1, p2})
    (hAq : (G.neighborFinset vq).erase u = {q1, q2})
    (hAr : (G.neighborFinset vr).erase u = {r1, r2})
    (hw12 : w1 ≠ w2)
    (hw1 : w1 ≠ u ∧ ¬ G.Adj u w1 ∧ ∀ v, G.Adj u v → ¬ G.Adj v w1)
    (hw2 : w2 ≠ u ∧ ¬ G.Adj u w2 ∧ ∀ v, G.Adj u v → ¬ G.Adj v w2)
    (hnw1 : ¬ G.Adj p1 w1) (hnw2 : ¬ G.Adj p1 w2) :
    (G.Adj p1 q1 ∨ G.Adj p1 q2) ∧ (G.Adj p1 r1 ∨ G.Adj p1 r2) := by
  obtain ⟨hvpp1, hvpp2, hp1u, _, _⟩ := pair_adj_ne hdeg huvp hAp
  obtain ⟨hvqq1, hvqq2, _, _, hq12⟩ := pair_adj_ne hdeg huvq hAq
  obtain ⟨hvrr1, hvrr2, _, _, hr12⟩ := pair_adj_ne hdeg huvr hAr
  have hp1_sub : (G.neighborFinset p1).erase vp ⊆ {q1, q2, r1, r2} := by
    intro z hz
    have ⟨hzv, hzp1⟩ := Finset.mem_erase.mp hz
    have hpz : G.Adj p1 z := (G.mem_neighborFinset p1 z).mp hzp1
    rcases bfs12_cover hcard12 hdeg htf hc4 huvp huvq huvr hpq hpr hqr hAp hAq hAr hw12 hw1 hw2 z with
      h | h | h | h | h | h | h | h | h | h | h | h
    · rw [h] at hpz; exact absurd hpz.symm (fun h' => htf u vp p1 huvp hvpp1 h'.symm)
    · exact absurd h hzv
    · rw [h] at hpz
      rcases no_c4_of_not_copy hc4 huvp hvpp1 hpz huvq.symm with h1 | h1
      · exact absurd h1.symm hp1u
      · exact absurd h1 hpq
    · rw [h] at hpz
      rcases no_c4_of_not_copy hc4 huvp hvpp1 hpz huvr.symm with h1 | h1
      · exact absurd h1.symm hp1u
      · exact absurd h1 hpr
    · rw [h] at hpz; exact absurd hpz (G.loopless.irrefl p1)
    · rw [h] at hpz; exact absurd hpz (fun h' => htf vp p1 p2 hvpp1 h' hvpp2.symm)
    · rw [h]; simp
    · rw [h]; simp
    · rw [h]; simp
    · rw [h]; simp
    · rw [h] at hpz; exact absurd hpz hnw1
    · rw [h] at hpz; exact absurd hpz hnw2
  have hcard2 : ((G.neighborFinset p1).erase vp).card = 2 := by
    rw [Finset.card_erase_of_mem ((G.mem_neighborFinset p1 vp).mpr hvpp1.symm),
      card_neighborFinset_eq_degree, hdeg p1]
  have hp1_ne_vq : p1 ≠ vq := (n1_ne_n2 htf huvq huvp hvpp1).symm
  have hp1_ne_vr : p1 ≠ vr := (n1_ne_n2 htf huvr huvp hvpp1).symm
  have hmax1_q : (((G.neighborFinset p1).erase vp) ∩ {q1, q2}).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro x hx y hy
    have hx' := Finset.mem_inter.mp hx
    have hy' := Finset.mem_inter.mp hy
    have hpx : G.Adj p1 x := (G.mem_neighborFinset p1 x).mp (Finset.mem_of_mem_erase hx'.1)
    have hpy : G.Adj p1 y := (G.mem_neighborFinset p1 y).mp (Finset.mem_of_mem_erase hy'.1)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx' hy'
    rcases hx'.2 with h1 | h1 <;> rcases hy'.2 with h2 | h2
    · rw [h1, h2]
    · rw [h1] at hpx; rw [h2] at hpy
      exact absurd hpy (no_both_nb hc4 hvqq1 hvqq2 hq12 hp1_ne_vq hpx)
    · rw [h1] at hpx; rw [h2] at hpy
      exact absurd hpx (no_both_nb hc4 hvqq1 hvqq2 hq12 hp1_ne_vq hpy)
    · rw [h1, h2]
  have hmax1_r : (((G.neighborFinset p1).erase vp) ∩ {r1, r2}).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro x hx y hy
    have hx' := Finset.mem_inter.mp hx
    have hy' := Finset.mem_inter.mp hy
    have hpx : G.Adj p1 x := (G.mem_neighborFinset p1 x).mp (Finset.mem_of_mem_erase hx'.1)
    have hpy : G.Adj p1 y := (G.mem_neighborFinset p1 y).mp (Finset.mem_of_mem_erase hy'.1)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx' hy'
    rcases hx'.2 with h1 | h1 <;> rcases hy'.2 with h2 | h2
    · rw [h1, h2]
    · rw [h1] at hpx; rw [h2] at hpy
      exact absurd hpy (no_both_nb hc4 hvrr1 hvrr2 hr12 hp1_ne_vr hpx)
    · rw [h1] at hpx; rw [h2] at hpy
      exact absurd hpx (no_both_nb hc4 hvrr1 hvrr2 hr12 hp1_ne_vr hpy)
    · rw [h1, h2]
  have hcov : (G.neighborFinset p1).erase vp ⊆
      (((G.neighborFinset p1).erase vp) ∩ {q1, q2}) ∪ (((G.neighborFinset p1).erase vp) ∩ {r1, r2}) := by
    intro z hz
    have h4 := hp1_sub hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at h4
    rcases h4 with h | h | h | h
    · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hz, by simp [h]⟩)
    · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hz, by simp [h]⟩)
    · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hz, by simp [h]⟩)
    · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hz, by simp [h]⟩)
  have hle := (Finset.card_le_card hcov).trans (Finset.card_union_le _ _)
  have hpos_q : 0 < (((G.neighborFinset p1).erase vp) ∩ {q1, q2}).card := by omega
  have hpos_r : 0 < (((G.neighborFinset p1).erase vp) ∩ {r1, r2}).card := by omega
  obtain ⟨zq, hzq⟩ := Finset.card_pos.mp hpos_q
  obtain ⟨zr, hzr⟩ := Finset.card_pos.mp hpos_r
  have hzq' := Finset.mem_inter.mp hzq
  have hzr' := Finset.mem_inter.mp hzr
  have h1 : G.Adj p1 q1 ∨ G.Adj p1 q2 := by
    have hadj := (G.mem_neighborFinset p1 zq).mp (Finset.mem_of_mem_erase hzq'.1)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hzq'
    rcases hzq'.2 with h | h
    · rw [h] at hadj; exact Or.inl hadj
    · rw [h] at hadj; exact Or.inr hadj
  have h2 : G.Adj p1 r1 ∨ G.Adj p1 r2 := by
    have hadj := (G.mem_neighborFinset p1 zr).mp (Finset.mem_of_mem_erase hzr'.1)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hzr'
    rcases hzr'.2 with h | h
    · rw [h] at hadj; exact Or.inl hadj
    · rw [h] at hadj; exact Or.inr hadj
  exact ⟨h1, h2⟩

private lemma kill_12_B1 {V : Type} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (hcard12 : Fintype.card V = 12) (hdeg : ∀ x, G.degree x = 3)
    (htf : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    (hc4 : ¬ cycleGraph 4 ⊑ G) (hc8 : ¬ cycleGraph 8 ⊑ G)
    {u vp vq vr p1 p2 q1 q2 r1 r2 w1 w2 : V}
    (huvp : G.Adj u vp) (huvq : G.Adj u vq) (huvr : G.Adj u vr)
    (hpq : vp ≠ vq) (hpr : vp ≠ vr) (hqr : vq ≠ vr)
    (hAp : (G.neighborFinset vp).erase u = {p1, p2})
    (hAq : (G.neighborFinset vq).erase u = {q1, q2})
    (hAr : (G.neighborFinset vr).erase u = {r1, r2})
    (hw12 : w1 ≠ w2)
    (hw1 : w1 ≠ u ∧ ¬ G.Adj u w1 ∧ ∀ v, G.Adj u v → ¬ G.Adj v w1)
    (hw2 : w2 ≠ u ∧ ¬ G.Adj u w2 ∧ ∀ v, G.Adj u v → ¬ G.Adj v w2)
    (hw_adj : G.Adj w1 w2)
    (hw1p1 : G.Adj w1 p1) (hw1q1 : G.Adj w1 q1)
    (hw2p2 : G.Adj w2 p2) (hw2r1 : G.Adj w2 r1) : False := by
  obtain ⟨hvpp1, hvpp2, hp1u, hp2u, _⟩ := pair_adj_ne hdeg huvp hAp
  obtain ⟨hvqq1, hvqq2, hq1u, hq2u, hq12⟩ := pair_adj_ne hdeg huvq hAq
  obtain ⟨hvrr1, hvrr2, hr1u, hr2u, hr12⟩ := pair_adj_ne hdeg huvr hAr
  have hw1r2 : ¬ G.Adj r2 w1 := by
    intro h
    have hsub : ({w2, p1, q1, r2} : Finset V) ⊆ G.neighborFinset w1 := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with hz' | hz' | hz' | hz'
      · rw [hz']; exact (G.mem_neighborFinset w1 w2).mpr hw_adj
      · rw [hz']; exact (G.mem_neighborFinset w1 p1).mpr hw1p1
      · rw [hz']; exact (G.mem_neighborFinset w1 q1).mpr hw1q1
      · rw [hz']; exact (G.mem_neighborFinset w1 r2).mpr h.symm
    have h4 : ({w2, p1, q1, r2} : Finset V).card = 4 := by
      rw [Finset.card_insert_of_notMem (by simp [far_ne_n2 hw2 huvp hvpp1,
          far_ne_n2 hw2 huvq hvqq1, far_ne_n2 hw2 huvr hvrr2]),
        Finset.card_insert_of_notMem (by simp [n2_disj hc4 huvp huvq hpq hvpp1 hp1u hvqq1,
          n2_disj hc4 huvp huvr hpr hvpp1 hp1u hvrr2]),
        Finset.card_pair (n2_disj hc4 huvq huvr hqr hvqq1 hq1u hvrr2)]
    have hc := Finset.card_le_card hsub
    rw [card_neighborFinset_eq_degree, hdeg w1, h4] at hc
    omega
  have hw2r2 : ¬ G.Adj r2 w2 := fun h =>
    no_both_nb hc4 hvrr1 hvrr2 hr12 (far_ne_n1 hw2 huvr) hw2r1 h.symm
  have hAr_sw : (G.neighborFinset vr).erase u = {r2, r1} := by rw [hAr, Finset.pair_comm]
  have ⟨_, hq_adj⟩ := n2_nb_of_nadj_w hcard12 hdeg htf hc4 huvr huvp huvq hpr.symm hqr.symm hpq
    hAr_sw hAp hAq hw12 hw1 hw2 hw1r2 hw2r2
  rcases hq_adj with hr2q1 | hr2q2
  · -- 8-cycle: u - vr - r2 - q1 - w1 - w2 - p2 - vp - u
    apply hc8
    apply copy_eight G u vr r2 q1 w1 w2 p2 vp
      huvr hvrr2 hr2q1 hw1q1.symm hw_adj hw2p2 hvpp2.symm huvp.symm
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, not_false_eq_true, and_true]
    refine ⟨⟨G.ne_of_adj huvr, hr2u.symm, hq1u.symm, hw1.1.symm, hw2.1.symm, hp2u.symm, G.ne_of_adj huvp⟩,
      ⟨n1_ne_n2 htf huvr huvr hvrr2, n1_ne_n2 htf huvr huvq hvqq1,
        (far_ne_n1 hw1 huvr).symm, (far_ne_n1 hw2 huvr).symm,
        n1_ne_n2 htf huvr huvp hvpp2, hpr.symm⟩,
      ⟨n2_disj hc4 huvr huvq hqr.symm hvrr2 hr2u hvqq1, (far_ne_n2 hw1 huvr hvrr2).symm,
        (far_ne_n2 hw2 huvr hvrr2).symm, n2_disj hc4 huvr huvp hpr.symm hvrr2 hr2u hvpp2,
        (n1_ne_n2 htf huvp huvr hvrr2).symm⟩,
      ⟨(far_ne_n2 hw1 huvq hvqq1).symm, (far_ne_n2 hw2 huvq hvqq1).symm,
        n2_disj hc4 huvq huvp hpq.symm hvqq1 hq1u hvpp2,
        (n1_ne_n2 htf huvp huvq hvqq1).symm⟩,
      ⟨hw12, far_ne_n2 hw1 huvp hvpp2, far_ne_n1 hw1 huvp⟩,
      ⟨far_ne_n2 hw2 huvp hvpp2, far_ne_n1 hw2 huvp⟩,
      (n1_ne_n2 htf huvp huvp hvpp2).symm⟩
  · -- 8-cycle: r2 - vr - r1 - w2 - w1 - q1 - vq - q2 - r2
    apply hc8
    apply copy_eight G r2 vr r1 w2 w1 q1 vq q2
      hvrr2.symm hvrr1 hw2r1.symm hw_adj.symm hw1q1 hvqq1.symm hvqq2 hr2q2.symm
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, not_false_eq_true, and_true]
    refine ⟨⟨(n1_ne_n2 htf huvr huvr hvrr2).symm, hr12.symm, (far_ne_n2 hw2 huvr hvrr2).symm,
        (far_ne_n2 hw1 huvr hvrr2).symm, n2_disj hc4 huvr huvq hqr.symm hvrr2 hr2u hvqq1,
        (n1_ne_n2 htf huvq huvr hvrr2).symm, n2_disj hc4 huvr huvq hqr.symm hvrr2 hr2u hvqq2⟩,
      ⟨n1_ne_n2 htf huvr huvr hvrr1, (far_ne_n1 hw2 huvr).symm, (far_ne_n1 hw1 huvr).symm,
        n1_ne_n2 htf huvr huvq hvqq1, hqr.symm, n1_ne_n2 htf huvr huvq hvqq2⟩,
      ⟨(far_ne_n2 hw2 huvr hvrr1).symm, (far_ne_n2 hw1 huvr hvrr1).symm,
        n2_disj hc4 huvr huvq hqr.symm hvrr1 hr1u hvqq1,
        (n1_ne_n2 htf huvq huvr hvrr1).symm, n2_disj hc4 huvr huvq hqr.symm hvrr1 hr1u hvqq2⟩,
      ⟨hw12.symm, far_ne_n2 hw2 huvq hvqq1, far_ne_n1 hw2 huvq, far_ne_n2 hw2 huvq hvqq2⟩,
      ⟨far_ne_n2 hw1 huvq hvqq1, far_ne_n1 hw1 huvq, far_ne_n2 hw1 huvq hvqq2⟩,
      ⟨(n1_ne_n2 htf huvq huvq hvqq1).symm, hq12⟩,
      n1_ne_n2 htf huvq huvq hvqq2⟩

private lemma kill_12_B2 {V : Type} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (hcard12 : Fintype.card V = 12) (hdeg : ∀ x, G.degree x = 3)
    (htf : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    (hc4 : ¬ cycleGraph 4 ⊑ G) (hc8 : ¬ cycleGraph 8 ⊑ G)
    {u vp vq vr p1 p2 q1 q2 r1 r2 w1 w2 : V}
    (huvp : G.Adj u vp) (huvq : G.Adj u vq) (huvr : G.Adj u vr)
    (hpq : vp ≠ vq) (hpr : vp ≠ vr) (hqr : vq ≠ vr)
    (hAp : (G.neighborFinset vp).erase u = {p1, p2})
    (hAq : (G.neighborFinset vq).erase u = {q1, q2})
    (hAr : (G.neighborFinset vr).erase u = {r1, r2})
    (hw12 : w1 ≠ w2)
    (hw1 : w1 ≠ u ∧ ¬ G.Adj u w1 ∧ ∀ v, G.Adj u v → ¬ G.Adj v w1)
    (hw2 : w2 ≠ u ∧ ¬ G.Adj u w2 ∧ ∀ v, G.Adj u v → ¬ G.Adj v w2)
    (hw_adj : G.Adj w1 w2)
    (hw1p1 : G.Adj w1 p1) (hw1q1 : G.Adj w1 q1)
    (hw2p2 : G.Adj w2 p2) (hw2q2 : G.Adj w2 q2) : False := by
  obtain ⟨hvpp1, hvpp2, hp1u, hp2u, hp12⟩ := pair_adj_ne hdeg huvp hAp
  obtain ⟨hvqq1, hvqq2, hq1u, hq2u, hq12⟩ := pair_adj_ne hdeg huvq hAq
  obtain ⟨hvrr1, hvrr2, hr1u, hr2u, hr12⟩ := pair_adj_ne hdeg huvr hAr
  have hnw : ∀ r : V, G.Adj vr r → r ≠ u → ¬ G.Adj r w1 ∧ ¬ G.Adj r w2 := by
    intro r hvrr hru
    have hr_ne_p1 := n2_disj hc4 huvr huvp hpr.symm hvrr hru hvpp1
    have hr_ne_p2 := n2_disj hc4 huvr huvp hpr.symm hvrr hru hvpp2
    have hr_ne_q1 := n2_disj hc4 huvr huvq hqr.symm hvrr hru hvqq1
    have hr_ne_q2 := n2_disj hc4 huvr huvq hqr.symm hvrr hru hvqq2
    constructor
    · intro h
      have hsub : ({w2, p1, q1, r} : Finset V) ⊆ G.neighborFinset w1 := by
        intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with hz' | hz' | hz' | hz'
        · rw [hz']; exact (G.mem_neighborFinset w1 w2).mpr hw_adj
        · rw [hz']; exact (G.mem_neighborFinset w1 p1).mpr hw1p1
        · rw [hz']; exact (G.mem_neighborFinset w1 q1).mpr hw1q1
        · rw [hz']; exact (G.mem_neighborFinset w1 r).mpr h.symm
      have h4 : ({w2, p1, q1, r} : Finset V).card = 4 := by
        rw [Finset.card_insert_of_notMem (by simp [far_ne_n2 hw2 huvp hvpp1,
            far_ne_n2 hw2 huvq hvqq1, far_ne_n2 hw2 huvr hvrr]),
          Finset.card_insert_of_notMem (by simp [n2_disj hc4 huvp huvq hpq hvpp1 hp1u hvqq1,
            hr_ne_p1.symm]),
          Finset.card_pair hr_ne_q1.symm]
      have hc := Finset.card_le_card hsub
      rw [card_neighborFinset_eq_degree, hdeg w1, h4] at hc
      omega
    · intro h
      have hsub : ({w1, p2, q2, r} : Finset V) ⊆ G.neighborFinset w2 := by
        intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with hz' | hz' | hz' | hz'
        · rw [hz']; exact (G.mem_neighborFinset w2 w1).mpr hw_adj.symm
        · rw [hz']; exact (G.mem_neighborFinset w2 p2).mpr hw2p2
        · rw [hz']; exact (G.mem_neighborFinset w2 q2).mpr hw2q2
        · rw [hz']; exact (G.mem_neighborFinset w2 r).mpr h.symm
      have h4 : ({w1, p2, q2, r} : Finset V).card = 4 := by
        rw [Finset.card_insert_of_notMem (by simp [far_ne_n2 hw1 huvp hvpp2,
            far_ne_n2 hw1 huvq hvqq2, far_ne_n2 hw1 huvr hvrr]),
          Finset.card_insert_of_notMem (by simp [n2_disj hc4 huvp huvq hpq hvpp2 hp2u hvqq2,
            hr_ne_p2.symm]),
          Finset.card_pair hr_ne_q2.symm]
      have hc := Finset.card_le_card hsub
      rw [card_neighborFinset_eq_degree, hdeg w2, h4] at hc
      omega
  have ⟨hr1_p, hr1_q⟩ := n2_nb_of_nadj_w hcard12 hdeg htf hc4 huvr huvp huvq hpr.symm hqr.symm hpq
    hAr hAp hAq hw12 hw1 hw2 (hnw r1 hvrr1 hr1u).1 (hnw r1 hvrr1 hr1u).2
  have hAr_sw : (G.neighborFinset vr).erase u = {r2, r1} := by rw [hAr, Finset.pair_comm]
  have ⟨hr2_p, hr2_q⟩ := n2_nb_of_nadj_w hcard12 hdeg htf hc4 huvr huvp huvq hpr.symm hqr.symm hpq
    hAr_sw hAp hAq hw12 hw1 hw2 (hnw r2 hvrr2 hr2u).1 (hnw r2 hvrr2 hr2u).2
  have hno_same_p : ∀ p, G.Adj r1 p → G.Adj r2 p → p ≠ vr → False := by
    intro p h1 h2 hne
    rcases no_c4_of_not_copy hc4 hvrr1 h1 h2.symm hvrr2.symm with h | h
    · exact hne h.symm
    · exact hr12 h
  have hmk8 : ∀ (rA rB : V), G.Adj vr rA → rA ≠ u → G.Adj vr rB → rB ≠ u → rA ≠ rB →
      G.Adj rA p1 → G.Adj rA q2 → G.Adj rB p2 → G.Adj rB q1 → False := by
    intro rA rB hrA_adj hrAu hrB_adj hrBu hrAB hAp1 hAq2 hBp2 hBq1
    apply hc8
    apply copy_eight G rA p1 w1 q1 rB p2 w2 q2
      hAp1 hw1p1.symm hw1q1 hBq1.symm hBp2 hw2p2.symm hw2q2 hAq2.symm
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, not_false_eq_true, and_true]
    refine ⟨⟨n2_disj hc4 huvr huvp hpr.symm hrA_adj hrAu hvpp1, (far_ne_n2 hw1 huvr hrA_adj).symm,
        n2_disj hc4 huvr huvq hqr.symm hrA_adj hrAu hvqq1, hrAB,
        n2_disj hc4 huvr huvp hpr.symm hrA_adj hrAu hvpp2, (far_ne_n2 hw2 huvr hrA_adj).symm,
        n2_disj hc4 huvr huvq hqr.symm hrA_adj hrAu hvqq2⟩,
      ⟨(far_ne_n2 hw1 huvp hvpp1).symm, n2_disj hc4 huvp huvq hpq hvpp1 hp1u hvqq1,
        (n2_disj hc4 huvr huvp hpr.symm hrB_adj hrBu hvpp1).symm, hp12,
        (far_ne_n2 hw2 huvp hvpp1).symm, n2_disj hc4 huvp huvq hpq hvpp1 hp1u hvqq2⟩,
      ⟨far_ne_n2 hw1 huvq hvqq1, far_ne_n2 hw1 huvr hrB_adj, far_ne_n2 hw1 huvp hvpp2,
        hw12, far_ne_n2 hw1 huvq hvqq2⟩,
      ⟨(n2_disj hc4 huvr huvq hqr.symm hrB_adj hrBu hvqq1).symm,
        n2_disj hc4 huvq huvp hpq.symm hvqq1 hq1u hvpp2, (far_ne_n2 hw2 huvq hvqq1).symm, hq12⟩,
      ⟨n2_disj hc4 huvr huvp hpr.symm hrB_adj hrBu hvpp2, (far_ne_n2 hw2 huvr hrB_adj).symm,
        n2_disj hc4 huvr huvq hqr.symm hrB_adj hrBu hvqq2⟩,
      ⟨(far_ne_n2 hw2 huvp hvpp2).symm, n2_disj hc4 huvp huvq hpq hvpp2 hp2u hvqq2⟩,
      far_ne_n2 hw2 huvq hvqq2⟩
  have hno_w1 : ∀ r, G.Adj vr r → G.Adj r p1 → ¬ G.Adj r q1 := by
    intro r hvrr hp hq
    rcases no_c4_of_not_copy hc4 hp hw1p1.symm hw1q1 hq.symm with h | h
    · exact (far_ne_n2 hw1 huvr hvrr).symm h
    · exact n2_disj hc4 huvp huvq hpq hvpp1 hp1u hvqq1 h
  have hno_w2 : ∀ r, G.Adj vr r → G.Adj r p2 → ¬ G.Adj r q2 := by
    intro r hvrr hp hq
    rcases no_c4_of_not_copy hc4 hp hw2p2.symm hw2q2 hq.symm with h | h
    · exact (far_ne_n2 hw2 huvr hvrr).symm h
    · exact n2_disj hc4 huvp huvq hpq hvpp2 hp2u hvqq2 h
  rcases hr1_p with h1p1 | h1p2
  · have h1q2 : G.Adj r1 q2 := hr1_q.resolve_left (hno_w1 r1 hvrr1 h1p1)
    have h2p2 : G.Adj r2 p2 :=
      hr2_p.resolve_left (fun h => hno_same_p p1 h1p1 h (n1_ne_n2 htf huvr huvp hvpp1).symm)
    have h2q1 : G.Adj r2 q1 := hr2_q.resolve_right (hno_w2 r2 hvrr2 h2p2)
    exact hmk8 r1 r2 hvrr1 hr1u hvrr2 hr2u hr12 h1p1 h1q2 h2p2 h2q1
  · have h1q1 : G.Adj r1 q1 := hr1_q.resolve_right (hno_w2 r1 hvrr1 h1p2)
    have h2p1 : G.Adj r2 p1 :=
      hr2_p.resolve_right (fun h => hno_same_p p2 h1p2 h (n1_ne_n2 htf huvr huvp hvpp2).symm)
    have h2q2 : G.Adj r2 q2 := hr2_q.resolve_left (hno_w1 r2 hvrr2 h2p1)
    exact hmk8 r2 r1 hvrr2 hr2u hvrr1 hr1u hr12.symm h2p1 h2q2 h1p2 h1q1

private lemma kill_12_A2 {V : Type} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (hcard12 : Fintype.card V = 12) (hdeg : ∀ x, G.degree x = 3)
    (htf : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    (hc4 : ¬ cycleGraph 4 ⊑ G) (hc8 : ¬ cycleGraph 8 ⊑ G)
    {u vp vq vr p1 p2 q1 q2 r1 r2 w1 w2 : V}
    (huvp : G.Adj u vp) (huvq : G.Adj u vq) (huvr : G.Adj u vr)
    (hpq : vp ≠ vq) (hpr : vp ≠ vr) (hqr : vq ≠ vr)
    (hAp : (G.neighborFinset vp).erase u = {p1, p2})
    (hAq : (G.neighborFinset vq).erase u = {q1, q2})
    (hAr : (G.neighborFinset vr).erase u = {r1, r2})
    (hw12 : w1 ≠ w2)
    (hw1 : w1 ≠ u ∧ ¬ G.Adj u w1 ∧ ∀ v, G.Adj u v → ¬ G.Adj v w1)
    (hw2 : w2 ≠ u ∧ ¬ G.Adj u w2 ∧ ∀ v, G.Adj u v → ¬ G.Adj v w2)
    (hw1p1 : G.Adj w1 p1) (hw1q1 : G.Adj w1 q1) (hw1r1 : G.Adj w1 r1)
    (hw2p1 : G.Adj w2 p1) (hw2q2 : G.Adj w2 q2) (hw2r2 : G.Adj w2 r2) : False := by
  obtain ⟨hvpp1, hvpp2, hp1u, hp2u, hp12⟩ := pair_adj_ne hdeg huvp hAp
  obtain ⟨hvqq1, hvqq2, hq1u, hq2u, _⟩ := pair_adj_ne hdeg huvq hAq
  obtain ⟨hvrr1, hvrr2, hr1u, hr2u, _⟩ := pair_adj_ne hdeg huvr hAr
  have hnw1 : ¬ G.Adj p2 w1 := fun h =>
    no_both_nb hc4 hvpp1 hvpp2 hp12 (far_ne_n1 hw1 huvp) hw1p1 h.symm
  have hnw2 : ¬ G.Adj p2 w2 := fun h =>
    no_both_nb hc4 hvpp1 hvpp2 hp12 (far_ne_n1 hw2 huvp) hw2p1 h.symm
  have hAp_sw : (G.neighborFinset vp).erase u = {p2, p1} := by rw [hAp, Finset.pair_comm]
  have ⟨hp2q, hp2r⟩ := n2_nb_of_nadj_w hcard12 hdeg htf hc4 huvp huvq huvr hpq hpr hqr
    hAp_sw hAq hAr hw12 hw1 hw2 hnw1 hnw2
  have hno_qr1 : G.Adj p2 q1 → ¬ G.Adj p2 r1 := by
    intro h1 h2
    rcases no_c4_of_not_copy hc4 h1 hw1q1.symm hw1r1 h2.symm with h | h
    · exact (far_ne_n2 hw1 huvp hvpp2).symm h
    · exact n2_disj hc4 huvq huvr hqr hvqq1 hq1u hvrr1 h
  have hno_qr2 : G.Adj p2 q2 → ¬ G.Adj p2 r2 := by
    intro h1 h2
    rcases no_c4_of_not_copy hc4 h1 hw2q2.symm hw2r2 h2.symm with h | h
    · exact (far_ne_n2 hw2 huvp hvpp2).symm h
    · exact n2_disj hc4 huvq huvr hqr hvqq2 hq2u hvrr2 h
  rcases hp2q with hq1 | hq2
  · have hr2 : G.Adj p2 r2 := hp2r.resolve_left (hno_qr1 hq1)
    -- 8-cycle: u - vq - q1 - p2 - r2 - w2 - p1 - vp - u
    apply hc8
    apply copy_eight G u vq q1 p2 r2 w2 p1 vp
      huvq hvqq1 hq1.symm hr2 hw2r2.symm hw2p1 hvpp1.symm huvp.symm
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, not_false_eq_true, and_true]
    refine ⟨⟨G.ne_of_adj huvq, hq1u.symm, hp2u.symm, hr2u.symm, hw2.1.symm,
        hp1u.symm, G.ne_of_adj huvp⟩,
      ⟨n1_ne_n2 htf huvq huvq hvqq1, n1_ne_n2 htf huvq huvp hvpp2,
        n1_ne_n2 htf huvq huvr hvrr2, (far_ne_n1 hw2 huvq).symm,
        n1_ne_n2 htf huvq huvp hvpp1, hpq.symm⟩,
      ⟨n2_disj hc4 huvq huvp hpq.symm hvqq1 hq1u hvpp2,
        n2_disj hc4 huvq huvr hqr hvqq1 hq1u hvrr2, (far_ne_n2 hw2 huvq hvqq1).symm,
        n2_disj hc4 huvq huvp hpq.symm hvqq1 hq1u hvpp1, (n1_ne_n2 htf huvp huvq hvqq1).symm⟩,
      ⟨n2_disj hc4 huvp huvr hpr hvpp2 hp2u hvrr2, (far_ne_n2 hw2 huvp hvpp2).symm,
        hp12.symm, (n1_ne_n2 htf huvp huvp hvpp2).symm⟩,
      ⟨(far_ne_n2 hw2 huvr hvrr2).symm, n2_disj hc4 huvr huvp hpr.symm hvrr2 hr2u hvpp1,
        (n1_ne_n2 htf huvp huvr hvrr2).symm⟩,
      ⟨far_ne_n2 hw2 huvp hvpp1, far_ne_n1 hw2 huvp⟩,
      (n1_ne_n2 htf huvp huvp hvpp1).symm⟩
  · have hr1 : G.Adj p2 r1 := hp2r.resolve_right (hno_qr2 hq2)
    -- 8-cycle: u - vr - r1 - p2 - q2 - w2 - p1 - vp - u
    apply hc8
    apply copy_eight G u vr r1 p2 q2 w2 p1 vp
      huvr hvrr1 hr1.symm hq2 hw2q2.symm hw2p1 hvpp1.symm huvp.symm
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, not_false_eq_true, and_true]
    refine ⟨⟨G.ne_of_adj huvr, hr1u.symm, hp2u.symm, hq2u.symm, hw2.1.symm,
        hp1u.symm, G.ne_of_adj huvp⟩,
      ⟨n1_ne_n2 htf huvr huvr hvrr1, n1_ne_n2 htf huvr huvp hvpp2,
        n1_ne_n2 htf huvr huvq hvqq2, (far_ne_n1 hw2 huvr).symm,
        n1_ne_n2 htf huvr huvp hvpp1, hpr.symm⟩,
      ⟨n2_disj hc4 huvr huvp hpr.symm hvrr1 hr1u hvpp2,
        n2_disj hc4 huvr huvq hqr.symm hvrr1 hr1u hvqq2, (far_ne_n2 hw2 huvr hvrr1).symm,
        n2_disj hc4 huvr huvp hpr.symm hvrr1 hr1u hvpp1, (n1_ne_n2 htf huvp huvr hvrr1).symm⟩,
      ⟨n2_disj hc4 huvp huvq hpq hvpp2 hp2u hvqq2, (far_ne_n2 hw2 huvp hvpp2).symm,
        hp12.symm, (n1_ne_n2 htf huvp huvp hvpp2).symm⟩,
      ⟨(far_ne_n2 hw2 huvq hvqq2).symm, n2_disj hc4 huvq huvp hpq.symm hvqq2 hq2u hvpp1,
        (n1_ne_n2 htf huvp huvq hvqq2).symm⟩,
      ⟨far_ne_n2 hw2 huvp hvpp1, far_ne_n1 hw2 huvp⟩,
      (n1_ne_n2 htf huvp huvp hvpp1).symm⟩

private lemma kill_12_A1 {V : Type} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (hcard12 : Fintype.card V = 12) (hdeg : ∀ x, G.degree x = 3)
    (htf : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    (hc4 : ¬ cycleGraph 4 ⊑ G) (hc8 : ¬ cycleGraph 8 ⊑ G)
    {u v1 vq vr x1 x2 q1 q2 r1 r2 w1 w2 : V}
    (huv1 : G.Adj u v1) (huvq : G.Adj u vq) (huvr : G.Adj u vr)
    (h1q : v1 ≠ vq) (h1r : v1 ≠ vr) (hqr : vq ≠ vr)
    (hA1 : (G.neighborFinset v1).erase u = {x1, x2})
    (hAq : (G.neighborFinset vq).erase u = {q1, q2})
    (hAr : (G.neighborFinset vr).erase u = {r1, r2})
    (hw12 : w1 ≠ w2)
    (hw1 : w1 ≠ u ∧ ¬ G.Adj u w1 ∧ ∀ v, G.Adj u v → ¬ G.Adj v w1)
    (hw2 : w2 ≠ u ∧ ¬ G.Adj u w2 ∧ ∀ v, G.Adj u v → ¬ G.Adj v w2)
    (hw1x1 : G.Adj w1 x1) (hw1r1 : G.Adj w1 r1)
    (hw2x2 : G.Adj w2 x2) (hw2q2 : G.Adj w2 q2) (hw2r2 : G.Adj w2 r2)
    (hx1q2 : G.Adj x1 q2) : False := by
  obtain ⟨hv1x1, hv1x2, hx1u, _, _⟩ := pair_adj_ne hdeg huv1 hA1
  obtain ⟨hvqq1, hvqq2, hq1u, hq2u, hq12⟩ := pair_adj_ne hdeg huvq hAq
  obtain ⟨hvrr1, hvrr2, _, hr2u, hr12⟩ := pair_adj_ne hdeg huvr hAr
  -- r2's 3rd neighbor (besides vr and w2) must be q1!
  have hr2q1 : G.Adj r2 q1 := by
    have hcard1 : ((G.neighborFinset r2).erase vr |>.erase w2).card = 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨far_ne_n1 hw2 huvr,
          (G.mem_neighborFinset r2 w2).mpr hw2r2.symm⟩),
        Finset.card_erase_of_mem ((G.mem_neighborFinset r2 vr).mpr hvrr2.symm),
        card_neighborFinset_eq_degree, hdeg r2]
    obtain ⟨t, ht_eq⟩ := Finset.card_eq_one.mp hcard1
    have ht_mem : t ∈ ((G.neighborFinset r2).erase vr).erase w2 := by rw [ht_eq]; simp
    have ⟨htw2, ht_mem1⟩ := Finset.mem_erase.mp ht_mem
    have ⟨htvr, htN⟩ := Finset.mem_erase.mp ht_mem1
    have hrt : G.Adj r2 t := (G.mem_neighborFinset r2 t).mp htN
    rcases bfs12_cover hcard12 hdeg htf hc4 huv1 huvq huvr h1q h1r hqr hA1 hAq hAr hw12 hw1 hw2 t with
      h | h | h | h | h | h | h | h | h | h | h | h
    · rw [h] at hrt; exact absurd hrt (fun h' => htf u vr r2 huvr hvrr2 h')
    · rw [h] at hrt
      rcases no_c4_of_not_copy hc4 huvr hvrr2 hrt huv1.symm with h1 | h1
      · exact absurd h1.symm hr2u
      · exact absurd h1 h1r.symm
    · rw [h] at hrt
      rcases no_c4_of_not_copy hc4 huvr hvrr2 hrt huvq.symm with h1 | h1
      · exact absurd h1.symm hr2u
      · exact absurd h1 hqr.symm
    · exact absurd h htvr
    · rw [h] at hrt
      have hsub4 : ({v1, w1, q2, r2} : Finset V) ⊆ G.neighborFinset x1 := by
        intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with hz' | hz' | hz' | hz'
        · rw [hz']; exact (G.mem_neighborFinset x1 v1).mpr hv1x1.symm
        · rw [hz']; exact (G.mem_neighborFinset x1 w1).mpr hw1x1.symm
        · rw [hz']; exact (G.mem_neighborFinset x1 q2).mpr hx1q2
        · rw [hz']; exact (G.mem_neighborFinset x1 r2).mpr hrt.symm
      have h4 : ({v1, w1, q2, r2} : Finset V).card = 4 := by
        rw [Finset.card_insert_of_notMem (by simp [(far_ne_n1 hw1 huv1).symm,
            n1_ne_n2 htf huv1 huvq hvqq2, n1_ne_n2 htf huv1 huvr hvrr2]),
          Finset.card_insert_of_notMem (by simp [far_ne_n2 hw1 huvq hvqq2,
            far_ne_n2 hw1 huvr hvrr2]),
          Finset.card_pair (n2_disj hc4 huvq huvr hqr hvqq2 hq2u hvrr2)]
      have hc := Finset.card_le_card hsub4
      rw [card_neighborFinset_eq_degree, hdeg x1, h4] at hc
      omega
    · rw [h] at hrt; exact absurd hrt (fun h' => htf w2 r2 x2 hw2r2 h' hw2x2.symm)
    · rw [h] at hrt; exact hrt
    · rw [h] at hrt; exact absurd hrt (fun h' => htf w2 r2 q2 hw2r2 h' hw2q2.symm)
    · rw [h] at hrt; exact absurd hrt (fun h' => htf vr r2 r1 hvrr2 h' hvrr1.symm)
    · rw [h] at hrt; exact absurd hrt (G.loopless.irrefl r2)
    · rw [h] at hrt; exact absurd hrt (fun h' => no_both_nb hc4 hvrr1 hvrr2 hr12 (far_ne_n1 hw1 huvr) hw1r1 h'.symm)
    · exact absurd h htw2
  -- 8-cycle: u - v1 - x1 - q2 - w2 - r2 - q1 - vq - u
  apply hc8
  apply copy_eight G u v1 x1 q2 w2 r2 q1 vq
    huv1 hv1x1 hx1q2 hw2q2.symm hw2r2 hr2q1 hvqq1.symm huvq.symm
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, not_false_eq_true, and_true]
  refine ⟨⟨G.ne_of_adj huv1, hx1u.symm, hq2u.symm, hw2.1.symm, hr2u.symm, hq1u.symm, G.ne_of_adj huvq⟩,
    ⟨n1_ne_n2 htf huv1 huv1 hv1x1, n1_ne_n2 htf huv1 huvq hvqq2,
      (far_ne_n1 hw2 huv1).symm, n1_ne_n2 htf huv1 huvr hvrr2,
      n1_ne_n2 htf huv1 huvq hvqq1, h1q⟩,
    ⟨n2_disj hc4 huv1 huvq h1q hv1x1 hx1u hvqq2, (far_ne_n2 hw2 huv1 hv1x1).symm,
      n2_disj hc4 huv1 huvr h1r hv1x1 hx1u hvrr2,
      n2_disj hc4 huv1 huvq h1q hv1x1 hx1u hvqq1, (n1_ne_n2 htf huvq huv1 hv1x1).symm⟩,
    ⟨(far_ne_n2 hw2 huvq hvqq2).symm, n2_disj hc4 huvq huvr hqr hvqq2 hq2u hvrr2,
      hq12.symm, (n1_ne_n2 htf huvq huvq hvqq2).symm⟩,
    ⟨far_ne_n2 hw2 huvr hvrr2, far_ne_n2 hw2 huvq hvqq1, far_ne_n1 hw2 huvq⟩,
    ⟨n2_disj hc4 huvr huvq hqr.symm hvrr2 hr2u hvqq1, (n1_ne_n2 htf huvq huvr hvrr2).symm⟩,
    (n1_ne_n2 htf huvq huvq hvqq1).symm⟩

private lemma card_ge_ten_and_ne_twelve {V : Type} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hne : Nonempty V) (hdeg : ∀ x, G.degree x = 3)
    (htf : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    (hc4 : ¬ cycleGraph 4 ⊑ G) (hc8 : ¬ cycleGraph 8 ⊑ G) :
    10 ≤ Fintype.card V ∧ Fintype.card V ≠ 12 := by
  obtain ⟨u⟩ := hne
  have hN1_card : (G.neighborFinset u).card = 3 := by
    rw [card_neighborFinset_eq_degree, hdeg u]
  obtain ⟨v1, v2, v3, hv12, hv13, hv23, hN1_eq⟩ := Finset.card_eq_three.mp hN1_card
  have huv1 : G.Adj u v1 := (G.mem_neighborFinset u v1).mp (by rw [hN1_eq]; simp)
  have huv2 : G.Adj u v2 := (G.mem_neighborFinset u v2).mp (by rw [hN1_eq]; simp)
  have huv3 : G.Adj u v3 := (G.mem_neighborFinset u v3).mp (by rw [hN1_eq]; simp)
  have hpair : ∀ v : V, G.Adj u v → ∃ a b : V, a ≠ b ∧ (G.neighborFinset v).erase u = {a, b} := by
    intro v huv
    have hc : ((G.neighborFinset v).erase u).card = 2 := by
      rw [Finset.card_erase_of_mem ((G.mem_neighborFinset v u).mpr huv.symm),
        card_neighborFinset_eq_degree, hdeg v]
    exact Finset.card_eq_two.mp hc
  obtain ⟨a1, a2, ha12, hA1⟩ := hpair v1 huv1
  obtain ⟨b1, b2, hb12, hA2⟩ := hpair v2 huv2
  obtain ⟨c1, c2, hc12, hA3⟩ := hpair v3 huv3
  obtain ⟨hv1a1, hv1a2, ha1u, ha2u, _⟩ := pair_adj_ne hdeg huv1 hA1
  obtain ⟨hv2b1, hv2b2, hb1u, hb2u, _⟩ := pair_adj_ne hdeg huv2 hA2
  obtain ⟨hv3c1, hv3c2, hc1u, hc2u, _⟩ := pair_adj_ne hdeg huv3 hA3
  have h10_nodup := bfs10_nodup hdeg htf hc4 huv1 huv2 huv3 hv12 hv13 hv23 hA1 hA2 hA3
  let B2 : Finset V := [u, v1, v2, v3, a1, a2, b1, b2, c1, c2].toFinset
  have hB2_card : B2.card = 10 := by
    rw [List.toFinset_card_of_nodup h10_nodup]; rfl
  have hge10 : 10 ≤ Fintype.card V := by
    have := Finset.card_le_univ B2
    omega
  refine ⟨hge10, ?_⟩
  -- Now rule out |V| = 12
  intro hcard12
  have hrem_card : (Finset.univ \ B2).card = 2 := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.subset_univ _),
      Finset.card_univ, hcard12, hB2_card]
  obtain ⟨w1, w2, hw12, hrem_eq⟩ := Finset.card_eq_two.mp hrem_card
  have hw_far : ∀ w ∈ ({w1, w2} : Finset V),
      w ≠ u ∧ ¬ G.Adj u w ∧ ∀ v, G.Adj u v → ¬ G.Adj v w := by
    intro w hw
    have hwB : w ∉ B2 := (Finset.mem_sdiff.mp (by rw [hrem_eq]; exact hw)).2
    have hwu : w ≠ u := fun h => hwB (by rw [h]; simp [B2])
    refine ⟨hwu, ?_, ?_⟩
    · intro huw
      have hm : w ∈ G.neighborFinset u := (G.mem_neighborFinset u w).mpr huw
      rw [hN1_eq] at hm; simp only [Finset.mem_insert, Finset.mem_singleton] at hm
      rcases hm with h | h | h <;> exact hwB (by rw [h]; simp [B2])
    · intro v huv hvw
      have hv : v ∈ G.neighborFinset u := (G.mem_neighborFinset u v).mpr huv
      rw [hN1_eq] at hv; simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      have hw_er : w ∈ (G.neighborFinset v).erase u :=
        Finset.mem_erase.mpr ⟨hwu, (G.mem_neighborFinset v w).mpr hvw⟩
      rcases hv with h | h | h
      · rw [h, hA1] at hw_er; simp only [Finset.mem_insert, Finset.mem_singleton] at hw_er
        rcases hw_er with h' | h' <;> exact hwB (by rw [h']; simp [B2])
      · rw [h, hA2] at hw_er; simp only [Finset.mem_insert, Finset.mem_singleton] at hw_er
        rcases hw_er with h' | h' <;> exact hwB (by rw [h']; simp [B2])
      · rw [h, hA3] at hw_er; simp only [Finset.mem_insert, Finset.mem_singleton] at hw_er
        rcases hw_er with h' | h' <;> exact hwB (by rw [h']; simp [B2])
  have hw1 := hw_far w1 (by simp)
  have hw2 := hw_far w2 (by simp)
  have hw_pair_max1 : ∀ (w : V), (w ≠ u ∧ ¬ G.Adj u w ∧ ∀ t, G.Adj u t → ¬ G.Adj t w) →
      ∀ {v x y : V}, G.Adj u v → G.Adj v x → G.Adj v y → x ≠ y →
      (G.neighborFinset w ∩ {x, y}).card ≤ 1 := by
    intro w hw v x y huv hvx hvy hxy
    rw [Finset.card_le_one]
    intro z1 hz1 z2 hz2
    have h1 := Finset.mem_inter.mp hz1
    have h2 := Finset.mem_inter.mp hz2
    have hwz1 := (G.mem_neighborFinset w z1).mp h1.1
    have hwz2 := (G.mem_neighborFinset w z2).mp h2.1
    simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2
    rcases h1.2 with h1' | h1' <;> rcases h2.2 with h2' | h2'
    · rw [h1', h2']
    · rw [h1'] at hwz1; rw [h2'] at hwz2
      exact absurd hwz2 (no_both_nb hc4 hvx hvy hxy (far_ne_n1 hw huv) hwz1)
    · rw [h1'] at hwz1; rw [h2'] at hwz2
      exact absurd hwz1 (no_both_nb hc4 hvx hvy hxy (far_ne_n1 hw huv) hwz2)
    · rw [h1', h2']
  have hsym_pair : ∀ {v x y : V}, G.Adj u v → (G.neighborFinset v).erase u = {x, y} →
      ∀ z ∈ ({x, y} : Finset V), ∃ z', z' ≠ z ∧ (G.neighborFinset v).erase u = {z, z'} := by
    intro v x y huv heq z hz
    have ⟨_, _, _, _, hne⟩ := pair_adj_ne hdeg huv heq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with h | h
    · exact ⟨y, by rw [h]; exact hne.symm, by rw [h]; exact heq⟩
    · exact ⟨x, by rw [h]; exact hne, by rw [h, heq, Finset.pair_comm]⟩
  have hpair_other : ∀ {x y z : V}, z ∈ ({x, y} : Finset V) → ∀ z', z' ∈ ({x, y} : Finset V) →
      z' ≠ z → ({x, y} : Finset V) = {z, z'} := by
    intro x y z hz z' hz' hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz hz'
    rcases hz with h1 | h1 <;> rcases hz' with h2 | h2
    · exact absurd (h2.trans h1.symm) hne
    · rw [h1, h2]
    · rw [h1, h2, Finset.pair_comm]
    · exact absurd (h2.trans h1.symm) hne
  have hcov_all := bfs12_cover hcard12 hdeg htf hc4 huv1 huv2 huv3 hv12 hv13 hv23 hA1 hA2 hA3 hw12 hw1 hw2
  by_cases hw_adj : G.Adj w1 w2
  · -- Subcase B: G.Adj w1 w2. Each of w1, w2 has 2 neighbors in N2 (in 2 distinct pairs), disjoint.
    have hw_two : ∀ (w w' : V), w ∈ ({w1, w2} : Finset V) → w' ∈ ({w1, w2} : Finset V) → G.Adj w w' →
        (∃ a ∈ ({a1, a2} : Finset V), G.Adj w a) ∧ (∃ b ∈ ({b1, b2} : Finset V), G.Adj w b) ∨
        (∃ a ∈ ({a1, a2} : Finset V), G.Adj w a) ∧ (∃ c ∈ ({c1, c2} : Finset V), G.Adj w c) ∨
        (∃ b ∈ ({b1, b2} : Finset V), G.Adj w b) ∧ (∃ c ∈ ({c1, c2} : Finset V), G.Adj w c) := by
      intro w w' hw_mem hw'_mem hww'
      have hw := hw_far w hw_mem
      have hw_er : ((G.neighborFinset w).erase w').card = 2 := by
        rw [Finset.card_erase_of_mem ((G.mem_neighborFinset w w').mpr hww'),
          card_neighborFinset_eq_degree, hdeg w]
      have hsub : (G.neighborFinset w).erase w' ⊆
          (G.neighborFinset w ∩ {a1, a2}) ∪ ((G.neighborFinset w ∩ {b1, b2}) ∪ (G.neighborFinset w ∩ {c1, c2})) := by
        intro z hz
        have ⟨hzw', hzwN⟩ := Finset.mem_erase.mp hz
        have hwz := (G.mem_neighborFinset w z).mp hzwN
        rcases hcov_all z with h | h | h | h | h | h | h | h | h | h | h | h
        · rw [h] at hwz; exact absurd hwz.symm hw.2.1
        · rw [h] at hwz; exact absurd hwz.symm (hw.2.2 v1 huv1)
        · rw [h] at hwz; exact absurd hwz.symm (hw.2.2 v2 huv2)
        · rw [h] at hwz; exact absurd hwz.symm (hw.2.2 v3 huv3)
        · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hzwN, by simp [h]⟩)
        · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hzwN, by simp [h]⟩)
        · exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hzwN, by simp [h]⟩))
        · exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hzwN, by simp [h]⟩))
        · exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hzwN, by simp [h]⟩))
        · exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hzwN, by simp [h]⟩))
        · simp only [Finset.mem_insert, Finset.mem_singleton] at hw_mem hw'_mem
          rcases hw_mem with hw_e | hw_e
          · rw [hw_e, h] at hwz; exact absurd hwz (G.loopless.irrefl w1)
          · rcases hw'_mem with hw'_e | hw'_e
            · exact absurd (h.trans hw'_e.symm) hzw'
            · rw [hw_e, hw'_e] at hww'; exact absurd hww' (G.loopless.irrefl w2)
        · simp only [Finset.mem_insert, Finset.mem_singleton] at hw_mem hw'_mem
          rcases hw_mem with hw_e | hw_e
          · rcases hw'_mem with hw'_e | hw'_e
            · rw [hw_e, hw'_e] at hww'; exact absurd hww' (G.loopless.irrefl w1)
            · exact absurd (h.trans hw'_e.symm) hzw'
          · rw [hw_e, h] at hwz; exact absurd hwz (G.loopless.irrefl w2)
      have hcA := hw_pair_max1 w hw huv1 hv1a1 hv1a2 ha12
      have hcB := hw_pair_max1 w hw huv2 hv2b1 hv2b2 hb12
      have hcC := hw_pair_max1 w hw huv3 hv3c1 hv3c2 hc12
      have htot := (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
        (Nat.add_le_add_left (Finset.card_union_le _ _) _))
      have hpos_imp : ∀ {s : Finset V}, 0 < (G.neighborFinset w ∩ s).card → ∃ z ∈ s, G.Adj w z := by
        intro s hs
        obtain ⟨z, hz⟩ := Finset.card_pos.mp hs
        have h := Finset.mem_inter.mp hz
        exact ⟨z, h.2, (G.mem_neighborFinset w z).mp h.1⟩
      by_cases hA : 0 < (G.neighborFinset w ∩ {a1, a2}).card
      · by_cases hB : 0 < (G.neighborFinset w ∩ {b1, b2}).card
        · left; exact ⟨hpos_imp hA, hpos_imp hB⟩
        · right; left; exact ⟨hpos_imp hA, hpos_imp (by omega)⟩
      · right; right; exact ⟨hpos_imp (by omega), hpos_imp (by omega)⟩
    have hdisj_w : ∀ z, G.Adj w1 z → ¬ G.Adj w2 z := fun z h1 h2 => htf w1 w2 z hw_adj h2 h1.symm
    rcases hw_two w1 w2 (by simp) (by simp) hw_adj with ⟨⟨a, ha, hwa⟩, ⟨b, hb, hwb⟩⟩ |
        ⟨⟨a, ha, hwa⟩, ⟨c, hc, hwc⟩⟩ | ⟨⟨b, hb, hwb⟩, ⟨c, hc, hwc⟩⟩
    · rcases hw_two w2 w1 (by simp) (by simp) hw_adj.symm with ⟨⟨a', ha', hwa'⟩, ⟨b', hb', hwb'⟩⟩ |
          ⟨⟨a', ha', hwa'⟩, ⟨c', hc', hwc'⟩⟩ | ⟨⟨b', hb', hwb'⟩, ⟨c', hc', hwc'⟩⟩
      · exact kill_12_B2 hcard12 hdeg htf hc4 hc8 huv1 huv2 huv3 hv12 hv13 hv23
          (hA1.trans (hpair_other ha a' ha' (fun e => hdisj_w a hwa (by rw [← e]; exact hwa'))))
          (hA2.trans (hpair_other hb b' hb' (fun e => hdisj_w b hwb (by rw [← e]; exact hwb'))))
          hA3 hw12 hw1 hw2 hw_adj hwa hwb hwa' hwb'
      · obtain ⟨b', _, hA2'⟩ := hsym_pair huv2 hA2 b hb
        obtain ⟨c'', _, hA3'⟩ := hsym_pair huv3 hA3 c' hc'
        exact kill_12_B1 hcard12 hdeg htf hc4 hc8 huv1 huv2 huv3 hv12 hv13 hv23
          (hA1.trans (hpair_other ha a' ha' (fun e => hdisj_w a hwa (by rw [← e]; exact hwa'))))
          hA2' hA3' hw12 hw1 hw2 hw_adj hwa hwb hwa' hwc'
      · obtain ⟨a', _, hA1'⟩ := hsym_pair huv1 hA1 a ha
        obtain ⟨c'', _, hA3'⟩ := hsym_pair huv3 hA3 c' hc'
        exact kill_12_B1 hcard12 hdeg htf hc4 hc8 huv2 huv1 huv3 hv12.symm hv23 hv13
          (hA2.trans (hpair_other hb b' hb' (fun e => hdisj_w b hwb (by rw [← e]; exact hwb'))))
          hA1' hA3' hw12 hw1 hw2 hw_adj hwb hwa hwb' hwc'
    · rcases hw_two w2 w1 (by simp) (by simp) hw_adj.symm with ⟨⟨a', ha', hwa'⟩, ⟨b', hb', hwb'⟩⟩ |
          ⟨⟨a', ha', hwa'⟩, ⟨c', hc', hwc'⟩⟩ | ⟨⟨b', hb', hwb'⟩, ⟨c', hc', hwc'⟩⟩
      · obtain ⟨c'', _, hA3'⟩ := hsym_pair huv3 hA3 c hc
        obtain ⟨b'', _, hA2'⟩ := hsym_pair huv2 hA2 b' hb'
        exact kill_12_B1 hcard12 hdeg htf hc4 hc8 huv1 huv3 huv2 hv13 hv12 hv23.symm
          (hA1.trans (hpair_other ha a' ha' (fun e => hdisj_w a hwa (by rw [← e]; exact hwa'))))
          hA3' hA2' hw12 hw1 hw2 hw_adj hwa hwc hwa' hwb'
      · exact kill_12_B2 hcard12 hdeg htf hc4 hc8 huv1 huv3 huv2 hv13 hv12 hv23.symm
          (hA1.trans (hpair_other ha a' ha' (fun e => hdisj_w a hwa (by rw [← e]; exact hwa'))))
          (hA3.trans (hpair_other hc c' hc' (fun e => hdisj_w c hwc (by rw [← e]; exact hwc'))))
          hA2 hw12 hw1 hw2 hw_adj hwa hwc hwa' hwc'
      · obtain ⟨a', _, hA1'⟩ := hsym_pair huv1 hA1 a ha
        obtain ⟨b'', _, hA2'⟩ := hsym_pair huv2 hA2 b' hb'
        exact kill_12_B1 hcard12 hdeg htf hc4 hc8 huv3 huv1 huv2 hv13.symm hv23.symm hv12
          (hA3.trans (hpair_other hc c' hc' (fun e => hdisj_w c hwc (by rw [← e]; exact hwc'))))
          hA1' hA2' hw12 hw1 hw2 hw_adj hwc hwa hwc' hwb'
    · rcases hw_two w2 w1 (by simp) (by simp) hw_adj.symm with ⟨⟨a', ha', hwa'⟩, ⟨b', hb', hwb'⟩⟩ |
          ⟨⟨a', ha', hwa'⟩, ⟨c', hc', hwc'⟩⟩ | ⟨⟨b', hb', hwb'⟩, ⟨c', hc', hwc'⟩⟩
      · obtain ⟨c'', _, hA3'⟩ := hsym_pair huv3 hA3 c hc
        obtain ⟨a'', _, hA1'⟩ := hsym_pair huv1 hA1 a' ha'
        exact kill_12_B1 hcard12 hdeg htf hc4 hc8 huv2 huv3 huv1 hv23 hv12.symm hv13.symm
          (hA2.trans (hpair_other hb b' hb' (fun e => hdisj_w b hwb (by rw [← e]; exact hwb'))))
          hA3' hA1' hw12 hw1 hw2 hw_adj hwb hwc hwb' hwa'
      · obtain ⟨b', _, hA2'⟩ := hsym_pair huv2 hA2 b hb
        obtain ⟨a'', _, hA1'⟩ := hsym_pair huv1 hA1 a' ha'
        exact kill_12_B1 hcard12 hdeg htf hc4 hc8 huv3 huv2 huv1 hv23.symm hv13.symm hv12.symm
          (hA3.trans (hpair_other hc c' hc' (fun e => hdisj_w c hwc (by rw [← e]; exact hwc'))))
          hA2' hA1' hw12 hw1 hw2 hw_adj hwc hwb hwc' hwa'
      · exact kill_12_B2 hcard12 hdeg htf hc4 hc8 huv2 huv3 huv1 hv23 hv12.symm hv13.symm
          (hA2.trans (hpair_other hb b' hb' (fun e => hdisj_w b hwb (by rw [← e]; exact hwb'))))
          (hA3.trans (hpair_other hc c' hc' (fun e => hdisj_w c hwc (by rw [← e]; exact hwc'))))
          hA1 hw12 hw1 hw2 hw_adj hwb hwc hwb' hwc'
  · -- Subcase A: ¬ G.Adj w1 w2. Each of w1, w2 has 1 neighbor in each of {a1,a2}, {b1,b2}, {c1,c2}.
    have hw_three : ∀ w ∈ ({w1, w2} : Finset V),
        (∃ a ∈ ({a1, a2} : Finset V), G.Adj w a) ∧
        (∃ b ∈ ({b1, b2} : Finset V), G.Adj w b) ∧
        (∃ c ∈ ({c1, c2} : Finset V), G.Adj w c) := by
      intro w hw_mem
      have hw := hw_far w hw_mem
      have hsub : G.neighborFinset w ⊆
          (G.neighborFinset w ∩ {a1, a2}) ∪ ((G.neighborFinset w ∩ {b1, b2}) ∪ (G.neighborFinset w ∩ {c1, c2})) := by
        intro z hz
        have hwz := (G.mem_neighborFinset w z).mp hz
        rcases hcov_all z with h | h | h | h | h | h | h | h | h | h | h | h
        · rw [h] at hwz; exact absurd hwz.symm hw.2.1
        · rw [h] at hwz; exact absurd hwz.symm (hw.2.2 v1 huv1)
        · rw [h] at hwz; exact absurd hwz.symm (hw.2.2 v2 huv2)
        · rw [h] at hwz; exact absurd hwz.symm (hw.2.2 v3 huv3)
        · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hz, by simp [h]⟩)
        · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hz, by simp [h]⟩)
        · exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hz, by simp [h]⟩))
        · exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hz, by simp [h]⟩))
        · exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hz, by simp [h]⟩))
        · exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hz, by simp [h]⟩))
        · simp only [Finset.mem_insert, Finset.mem_singleton] at hw_mem
          rcases hw_mem with hw_e | hw_e
          · rw [hw_e, h] at hwz; exact absurd hwz (G.loopless.irrefl w1)
          · rw [hw_e, h] at hwz; exact absurd hwz.symm hw_adj
        · simp only [Finset.mem_insert, Finset.mem_singleton] at hw_mem
          rcases hw_mem with hw_e | hw_e
          · rw [hw_e, h] at hwz; exact absurd hwz hw_adj
          · rw [hw_e, h] at hwz; exact absurd hwz (G.loopless.irrefl w2)
      have hcA := hw_pair_max1 w hw huv1 hv1a1 hv1a2 ha12
      have hcB := hw_pair_max1 w hw huv2 hv2b1 hv2b2 hb12
      have hcC := hw_pair_max1 w hw huv3 hv3c1 hv3c2 hc12
      have htot := (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
        (Nat.add_le_add_left (Finset.card_union_le _ _) _))
      rw [card_neighborFinset_eq_degree, hdeg w] at htot
      have hpos_imp : ∀ {s : Finset V}, 0 < (G.neighborFinset w ∩ s).card → ∃ z ∈ s, G.Adj w z := by
        intro s hs
        obtain ⟨z, hz⟩ := Finset.card_pos.mp hs
        have h := Finset.mem_inter.mp hz
        exact ⟨z, h.2, (G.mem_neighborFinset w z).mp h.1⟩
      exact ⟨hpos_imp (by omega), hpos_imp (by omega), hpos_imp (by omega)⟩
    obtain ⟨⟨x1, hx1, hwx1⟩, ⟨y1, hy1, hwy1⟩, ⟨z1, hz1, hwz1⟩⟩ := hw_three w1 (by simp)
    obtain ⟨⟨x2, hx2, hwx2⟩, ⟨y2, hy2, hwy2⟩, ⟨z2, hz2, hwz2⟩⟩ := hw_three w2 (by simp)
    have hno_2ov : ∀ {p q : V}, G.Adj w1 p → G.Adj w2 p → G.Adj w1 q → G.Adj w2 q → p = q := by
      intro p q h1p h2p h1q h2q
      rcases no_c4_of_not_copy hc4 h1p h2p.symm h2q h1q.symm with h | h
      · exact absurd h hw12
      · exact h
    have hx1_spec : G.Adj v1 x1 ∧ x1 ≠ u := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx1
      rcases hx1 with h | h <;> rw [h] <;> exact ⟨by assumption, by assumption⟩
    have hy1_spec : G.Adj v2 y1 ∧ y1 ≠ u := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy1
      rcases hy1 with h | h <;> rw [h] <;> exact ⟨by assumption, by assumption⟩
    have hz1_spec : G.Adj v3 z1 ∧ z1 ≠ u := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz1
      rcases hz1 with h | h <;> rw [h] <;> exact ⟨by assumption, by assumption⟩
    by_cases hxeq : x1 = x2
    · rw [← hxeq] at hwx2
      have hyne : y1 ≠ y2 := fun e =>
        n2_disj hc4 huv1 huv2 hv12 hx1_spec.1 hx1_spec.2 hy1_spec.1
          (hno_2ov hwx1 hwx2 hwy1 (by rw [e]; exact hwy2))
      have hzne : z1 ≠ z2 := fun e =>
        n2_disj hc4 huv1 huv3 hv13 hx1_spec.1 hx1_spec.2 hz1_spec.1
          (hno_2ov hwx1 hwx2 hwz1 (by rw [e]; exact hwz2))
      obtain ⟨x', _, hA1'⟩ := hsym_pair huv1 hA1 x1 hx1
      exact kill_12_A2 hcard12 hdeg htf hc4 hc8 huv1 huv2 huv3 hv12 hv13 hv23
        hA1' (hA2.trans (hpair_other hy1 y2 hy2 hyne.symm))
        (hA3.trans (hpair_other hz1 z2 hz2 hzne.symm)) hw12 hw1 hw2
        hwx1 hwy1 hwz1 hwx2 hwy2 hwz2
    · by_cases hyeq : y1 = y2
      · rw [← hyeq] at hwy2
        have hzne : z1 ≠ z2 := fun e =>
          n2_disj hc4 huv2 huv3 hv23 hy1_spec.1 hy1_spec.2 hz1_spec.1
            (hno_2ov hwy1 hwy2 hwz1 (by rw [e]; exact hwz2))
        obtain ⟨y', _, hA2'⟩ := hsym_pair huv2 hA2 y1 hy1
        exact kill_12_A2 hcard12 hdeg htf hc4 hc8 huv2 huv1 huv3 hv12.symm hv23 hv13
          hA2' (hA1.trans (hpair_other hx1 x2 hx2 (Ne.symm hxeq)))
          (hA3.trans (hpair_other hz1 z2 hz2 hzne.symm)) hw12 hw1 hw2
          hwy1 hwx1 hwz1 hwy2 hwx2 hwz2
      · by_cases hzeq : z1 = z2
        · rw [← hzeq] at hwz2
          obtain ⟨z', _, hA3'⟩ := hsym_pair huv3 hA3 z1 hz1
          exact kill_12_A2 hcard12 hdeg htf hc4 hc8 huv3 huv1 huv2 hv13.symm hv23.symm hv12
            hA3' (hA1.trans (hpair_other hx1 x2 hx2 (Ne.symm hxeq)))
            (hA2.trans (hpair_other hy1 y2 hy2 (Ne.symm hyeq))) hw12 hw1 hw2
            hwz1 hwx1 hwy1 hwz2 hwx2 hwy2
        · -- Subcase A1: disjoint {x1,y1,z1} and {x2,y2,z2}!
          have hA1' := hA1.trans (hpair_other hx1 x2 hx2 (Ne.symm hxeq))
          have hA2' := hA2.trans (hpair_other hy1 y2 hy2 (Ne.symm hyeq))
          have hA3' := hA3.trans (hpair_other hz1 z2 hz2 (Ne.symm hzeq))
          obtain ⟨hv1x1, hv1x2, hx1u, _, _⟩ := pair_adj_ne hdeg huv1 hA1'
          -- x1's 3rd neighbor (besides v1 and w1) must be y2 or z2
          have hx1_nb : G.Adj x1 y2 ∨ G.Adj x1 z2 := by
            have hcard1 : ((G.neighborFinset x1).erase v1 |>.erase w1).card = 1 := by
              rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨far_ne_n1 hw1 huv1,
                  (G.mem_neighborFinset x1 w1).mpr hwx1.symm⟩),
                Finset.card_erase_of_mem ((G.mem_neighborFinset x1 v1).mpr hv1x1.symm),
                card_neighborFinset_eq_degree, hdeg x1]
            obtain ⟨t, ht_eq⟩ := Finset.card_eq_one.mp hcard1
            have ht_mem : t ∈ ((G.neighborFinset x1).erase v1).erase w1 := by rw [ht_eq]; simp
            have ⟨htw1, ht_mem1⟩ := Finset.mem_erase.mp ht_mem
            have ⟨htv1, htN⟩ := Finset.mem_erase.mp ht_mem1
            have hxt : G.Adj x1 t := (G.mem_neighborFinset x1 t).mp htN
            rcases bfs12_cover hcard12 hdeg htf hc4 huv1 huv2 huv3 hv12 hv13 hv23
                hA1' hA2' hA3' hw12 hw1 hw2 t with
              h | h | h | h | h | h | h | h | h | h | h | h
            · rw [h] at hxt; exact absurd hxt (fun h' => htf u v1 x1 huv1 hv1x1 h')
            · exact absurd h htv1
            · rw [h] at hxt
              rcases no_c4_of_not_copy hc4 huv1 hv1x1 hxt huv2.symm with h1 | h1
              · exact absurd h1.symm hx1u
              · exact absurd h1 hv12
            · rw [h] at hxt
              rcases no_c4_of_not_copy hc4 huv1 hv1x1 hxt huv3.symm with h1 | h1
              · exact absurd h1.symm hx1u
              · exact absurd h1 hv13
            · rw [h] at hxt; exact absurd hxt (G.loopless.irrefl x1)
            · rw [h] at hxt; exact absurd hxt (fun h' => htf v1 x1 x2 hv1x1 h' hv1x2.symm)
            · rw [h] at hxt; exact absurd hxt (fun h' => htf w1 x1 y1 hwx1 h' hwy1.symm)
            · rw [h] at hxt; exact Or.inl hxt
            · rw [h] at hxt; exact absurd hxt (fun h' => htf w1 x1 z1 hwx1 h' hwz1.symm)
            · rw [h] at hxt; exact Or.inr hxt
            · exact absurd h htw1
            · rw [h] at hxt
              exact absurd hxt (fun h' => no_both_nb hc4 hv1x1 hv1x2 hxeq (far_ne_n1 hw2 huv1) h'.symm hwx2)
          rcases hx1_nb with hx1y2 | hx1z2
          · exact kill_12_A1 hcard12 hdeg htf hc4 hc8 huv1 huv2 huv3 hv12 hv13 hv23
              hA1' hA2' hA3' hw12 hw1 hw2 hwx1 hwz1 hwx2 hwy2 hwz2 hx1y2
          · exact kill_12_A1 hcard12 hdeg htf hc4 hc8 huv1 huv3 huv2 hv13 hv12 hv23.symm
              hA1' hA3' hA2' hw12 hw1 hw2 hwx1 hwy1 hwx2 hwz2 hwy2 hx1z2

end Helpers

theorem main : H1 → H2 → OMA.R_Erdos64_erdos_64_R4.H2 := by
  intro h1 h2 V0 G0 _ _ hconn0 hdeg0 hvt0 _ _ _ _
  suffices hall : ∀ (n : ℕ) (V : Type) (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj],
      Fintype.card V = n → G.Connected → (∀ x, G.degree x = 3) →
      (∀ x y, ∃ g : G ≃g G, g x = y) →
      ∃ k : ℕ, 2 ≤ k ∧ cycleGraph (2 ^ k) ⊑ G by
    exact hall (Fintype.card V0) V0 G0 rfl hconn0 hdeg0 hvt0
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V G _ _ hcard hconn hdeg hvt
    -- 1. Check C4 and C8 directly
    by_cases hc4 : cycleGraph 4 ⊑ G
    · exact ⟨2, le_rfl, hc4⟩
    by_cases hc8 : cycleGraph 8 ⊑ G
    · exact ⟨3, by norm_num, hc8⟩
    -- 2. Check dyadic order |V| = 2^m via R4.transitive_dyadic_order
    by_cases hpow : ∃ m : ℕ, Fintype.card V = 2 ^ m
    · obtain ⟨m, hm⟩ := hpow
      have : Nonempty V := hconn.nonempty
      exact OMA.R_Erdos64_erdos_64_R4.transitive_dyadic_order G (fun x => by rw [hdeg x]) hvt hm
    -- 3. Check twice-prime order |V| = 2*p via R4.vertex_transitive_twice_prime
    by_cases h2p : ∃ p : ℕ, p.Prime ∧ Fintype.card V = 2 * p
    · obtain ⟨p, hp, hcard_p⟩ := h2p
      rcases OMA.R_Erdos64_erdos_64_R4.Erdos64TwicePrime.vertex_transitive_twice_prime
          G hp hcard_p hvt (fun x => by rw [hdeg x]) with h4 | h8 | h16
      · exact ⟨2, le_rfl, h4⟩
      · exact ⟨3, by norm_num, h8⟩
      · exact ⟨4, by norm_num, h16⟩
    -- 4. Eliminate triangles via triangle contraction
    by_cases htri : ∃ a b c : V, G.Adj a b ∧ G.Adj b c ∧ G.Adj c a
    · exact vt_cubic_triangle_contraction G hconn hdeg hvt hc4 htri
        (fun Q GQ _ _ hlt hQc hQd hQv => ih (Fintype.card Q) (hcard ▸ hlt) Q GQ rfl hQc hQd hQv)
    -- 5. Eliminate transitive-commuting involutions via 2-cover descent
    by_cases hinv : ∃ σ : G ≃g G, σ ≠ 1 ∧ (∀ x, σ (σ x) = x) ∧
        (∀ x y, ∃ g : G ≃g G, g x = y ∧ ∀ z, g (σ z) = σ (g z))
    · obtain ⟨σ, hσ_ne, hσ_inv, hσ_comm⟩ := hinv
      exact vt_cubic_central_involution G hconn hdeg hc4 σ hσ_ne hσ_inv hσ_comm
        (fun Q GQ _ _ hlt hQc hQd hQv => ih (Fintype.card Q) (hcard ▸ hlt) Q GQ rfl hQc hQd hQv)
    -- 6. Derive bridgelessness, triangle-freeness, even order, and |V| ≥ 18
    push Not at hpow h2p htri
    have htf : ∀ a b c : V, G.Adj a b → G.Adj b c → ¬ G.Adj c a := fun a b c h1' h2' h3' =>
      htri a b c h1' h2' h3'
    have hnobr : ∀ ⦃a b : V⦄, G.Adj a b → ¬ G.IsBridge s(a, b) :=
      fun _ _ hab => vt_cubic_bridgeless G hdeg hvt hab
    have heven : Even (Fintype.card V) := even_card_of_cubic G hdeg
    have ⟨hge10, hne12⟩ := card_ge_ten_and_ne_twelve G hconn.nonempty hdeg htf hc4 hc8
    have hge18 : 18 ≤ Fintype.card V := by
      have hne10 : Fintype.card V ≠ 10 := h2p 5 (by decide)
      have hne14 : Fintype.card V ≠ 14 := h2p 7 (by decide)
      have hne16 : Fintype.card V ≠ 16 := hpow 4
      obtain ⟨m, hm⟩ := heven
      omega
    -- 7. Split into bipartite (H1) and non-bipartite (H2)
    by_cases hbip : G.IsBipartite
    · exact h1 V G hconn hnobr hdeg hvt hbip hc4 hc8 heven hge18 hpow h2p hinv
    · exact h2 V G hconn hnobr hdeg hvt hbip htf hc4 hc8 heven hge18 hpow h2p hinv

end OMA.R_Erdos64_erdos_64_R4_H2_R1
