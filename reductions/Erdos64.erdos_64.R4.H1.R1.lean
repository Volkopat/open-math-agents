import OMAReductions.R_Erdos64_erdos_64_R4
import Mathlib

/-!
# Structural reduction of the non-vertex-transitive branch of Erdős Problem 64

Step H1 of Erdos64.erdos_64.R4 concerns connected C4-free C8-free non-vertex-transitive
graphs of minimum degree at least 3 in which high-degree vertices form an independent set
and every vertex has a cubic neighbor. This reduction proves five structural theorems in
Lean 4 and splits the branch into three strictly stronger subproblems (H1, H2, H3):

1. Exact 2/3 cubic density bound: double-counting edges between degree-3 vertices and
   degree-≥4 vertices proves 2|V| ≤ 3|V_3|, with equality only when every high-degree
   vertex has degree 4 and every cubic vertex has exactly 2 high-degree neighbors.
2. Equality-case 4-regular C4-free contraction (H1): when V_{≥4} ≠ ∅ and 2|V| = 3|V_3|,
   contracting each cubic vertex to an edge between its two degree-4 neighbors yields a
   4-regular C4-free graph (since any C4 lifts to a C8 in G); restricting to a connected
   component gives a connected 4-regular C4-free graph on at least 13 vertices whose
   2^k-cycle lifts to a 2^(k+1)-cycle in G.
3. Noncubic expansion bound and |V| ≥ 10 (H2): in the strict case 2|V| < 3|V_3|, every
   vertex v of degree d ≥ 4 forces 2d + 1 ≤ |V|, and every 4-vertex graph of minimum
   degree ≥ 2 contains a C4, ruling out |V| = 9 and forcing |V| ≥ 10.
4. Uniqueness and vertex-transitivity of the Petersen graph: every cubic triangle-free
   C4-free graph on 10 vertices admits a canonical rooted isomorphism to the Petersen
   graph, hence is vertex-transitive and cannot occur in R4.H1.
5. Cubic non-vertex-transitive order bounds (H3): every connected cubic
   non-vertex-transitive C4-free C8-free graph has even order |V| ≥ 12 (ruling out
   |V| ∈ {6, 8, 10} with a triangle via explicit C4/C8 constructions and |V| = 10
   triangle-free via Petersen uniqueness), and |V| ≥ 14 whenever triangle-free (by
   exhaustive elimination of 12-vertex cubic girth-≥5 graphs via C8).
-/

namespace OMA.R_Erdos64_erdos_64_R4_H1_R1

open SimpleGraph Finset Function
open scoped Classical

/-- Connected 4-regular C4-free graphs on at least 13 vertices (from the 2|V| = 3|V_3|
equality case of R4.H1). -/
def H1 : Prop :=
  ∀ (W : Type) (H : SimpleGraph W) [Fintype W] [DecidableRel H.Adj],
    H.Connected →
    (∀ v, H.degree v = 4) →
    (¬ cycleGraph 4 ⊑ H) →
    13 ≤ Fintype.card W →
    ∃ k : ℕ, 2 ≤ k ∧ cycleGraph (2 ^ k) ⊑ H

/-- Connected non-vertex-transitive C4-free C8-free noncubic graphs with minimum degree
at least 3, independent high-degree vertices, a cubic neighbor at every vertex, strictly
more than two-thirds cubic vertices, neighborhood bound 2d + 1 ≤ |V|, and |V| ≥ 10. -/
def H2 : Prop :=
  ∀ (V : Type) (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj],
    G.Connected →
    (∀ x, 3 ≤ G.degree x) →
    (∃ v, 3 < G.degree v) →
    (¬ ∀ x y, ∃ g : G ≃g G, g x = y) →
    (∀ ⦃a b⦄, G.Adj a b → G.degree a = 3 ∨ G.degree b = 3) →
    (∀ a, ∃ b, G.Adj a b ∧ G.degree b = 3) →
    (¬ cycleGraph 4 ⊑ G) →
    (¬ cycleGraph 8 ⊑ G) →
    2 * Fintype.card V < 3 * (Finset.univ.filter (fun x => G.degree x = 3)).card →
    (∀ v, 3 < G.degree v → 2 * G.degree v + 1 ≤ Fintype.card V) →
    10 ≤ Fintype.card V →
    ∃ k : ℕ, 2 ≤ k ∧ cycleGraph (2 ^ k) ⊑ G

/-- Connected cubic non-vertex-transitive C4-free C8-free graphs of even order at least 12,
and at least 14 whenever triangle-free. -/
def H3 : Prop :=
  ∀ (V : Type) (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj],
    G.Connected →
    (∀ x, G.degree x = 3) →
    (¬ ∀ x y, ∃ g : G ≃g G, g x = y) →
    (¬ cycleGraph 4 ⊑ G) →
    (¬ cycleGraph 8 ⊑ G) →
    Even (Fintype.card V) →
    12 ≤ Fintype.card V →
    ((∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a) → 14 ≤ Fintype.card V) →
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


/- ### Part 1: Exact 2/3 cubic density bound and equality-case 4-regular C4-free contraction -/

private lemma two_thirds_cubic_bound {V : Type} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hmin : ∀ x, 3 ≤ G.degree x)
    (hindep : ∀ ⦃a b⦄, G.Adj a b → G.degree a = 3 ∨ G.degree b = 3)
    (hcub_nb : ∀ a, ∃ b, G.Adj a b ∧ G.degree b = 3) :
    let T := Finset.univ.filter (fun x : V => G.degree x = 3)
    let H := Finset.univ.filter (fun x : V => 3 < G.degree x)
    2 * Fintype.card V ≤ 3 * T.card ∧
      (2 * Fintype.card V = 3 * T.card →
        (∀ v ∈ H, G.degree v = 4) ∧
        (∀ u ∈ T, (G.neighborFinset u ∩ H).card = 2)) := by
  intro T H
  have hTH_disj : Disjoint T H := by
    rw [Finset.disjoint_left]
    intro x hxT hxH
    have h1 := (Finset.mem_filter.mp hxT).2
    have h2 := (Finset.mem_filter.mp hxH).2
    omega
  have hTH_union : T ∪ H = Finset.univ := by
    ext x
    simp only [T, H, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    have := hmin x
    omega
  have hcard_sum : T.card + H.card = Fintype.card V := by
    rw [← Finset.card_union_of_disjoint hTH_disj, hTH_union, Finset.card_univ]
  have hH_sub_T : ∀ v ∈ H, G.neighborFinset v ∩ T = G.neighborFinset v := by
    intro v hv
    have hv3 : 3 < G.degree v := (Finset.mem_filter.mp hv).2
    ext u
    simp only [Finset.mem_inter, T, Finset.mem_filter, Finset.mem_univ, true_and,
      and_iff_left_iff_imp]
    intro hu
    have huv := (G.mem_neighborFinset v u).mp hu
    rcases hindep huv with h | h
    · omega
    · exact h
  have hH_lb : ∀ v ∈ H, 4 ≤ (G.neighborFinset v ∩ T).card := by
    intro v hv
    rw [hH_sub_T v hv, card_neighborFinset_eq_degree]
    have := (Finset.mem_filter.mp hv).2
    omega
  have hT_ub : ∀ u ∈ T, (G.neighborFinset u ∩ H).card ≤ 2 := by
    intro u hu
    have hu3 : G.degree u = 3 := (Finset.mem_filter.mp hu).2
    obtain ⟨b, hub, hb3⟩ := hcub_nb u
    have hsub : G.neighborFinset u ∩ H ⊆ (G.neighborFinset u).erase b := by
      intro x hx
      have ⟨hxN, hxH⟩ := Finset.mem_inter.mp hx
      have hxgt : 3 < G.degree x := (Finset.mem_filter.mp hxH).2
      refine Finset.mem_erase.mpr ⟨fun hxb => ?_, hxN⟩
      rw [hxb] at hxgt; omega
    calc (G.neighborFinset u ∩ H).card
        ≤ ((G.neighborFinset u).erase b).card := Finset.card_le_card hsub
      _ = 2 := by
        rw [Finset.card_erase_of_mem ((G.mem_neighborFinset u b).mpr hub),
          card_neighborFinset_eq_degree, hu3]
  have hdouble : ∑ v ∈ H, (G.neighborFinset v ∩ T).card = ∑ u ∈ T, (G.neighborFinset u ∩ H).card := by
    calc ∑ v ∈ H, (G.neighborFinset v ∩ T).card
        = ∑ v ∈ H, ∑ u ∈ T, if G.Adj v u then 1 else 0 := by
          refine Finset.sum_congr rfl (fun v _ => ?_)
          rw [← Finset.card_filter]
          congr 1; ext u; simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset, Finset.mem_filter]; exact and_comm
      _ = ∑ u ∈ T, ∑ v ∈ H, if G.Adj v u then 1 else 0 := Finset.sum_comm
      _ = ∑ u ∈ T, (G.neighborFinset u ∩ H).card := by
          refine Finset.sum_congr rfl (fun u _ => ?_)
          rw [← Finset.card_filter]
          congr 1; ext v; simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset, Finset.mem_filter]; rw [G.adj_comm]; exact and_comm
  have hsum_lb : 4 * H.card ≤ ∑ v ∈ H, (G.neighborFinset v ∩ T).card := by
    calc 4 * H.card = ∑ _v ∈ H, 4 := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ v ∈ H, (G.neighborFinset v ∩ T).card := Finset.sum_le_sum hH_lb
  have hsum_ub : ∑ u ∈ T, (G.neighborFinset u ∩ H).card ≤ 2 * T.card := by
    calc ∑ u ∈ T, (G.neighborFinset u ∩ H).card
        ≤ ∑ _u ∈ T, 2 := Finset.sum_le_sum hT_ub
      _ = 2 * T.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  refine ⟨by omega, ?_⟩
  intro heq
  have h42 : 4 * H.card = 2 * T.card := by omega
  have hsum_eq_H : ∑ v ∈ H, (G.neighborFinset v ∩ T).card = ∑ _v ∈ H, 4 := by
    have : ∑ _v ∈ H, 4 = 4 * H.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    omega
  have hsum_eq_T : ∑ u ∈ T, (G.neighborFinset u ∩ H).card = ∑ _u ∈ T, 2 := by
    have : ∑ _u ∈ T, 2 = 2 * T.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    omega
  constructor
  · intro v hv
    have h1 := (Finset.sum_eq_sum_iff_of_le (fun x hx => hH_lb x hx)).mp hsum_eq_H.symm v hv
    rw [hH_sub_T v hv, card_neighborFinset_eq_degree] at h1
    exact h1.symm
  · intro u hu
    exact (Finset.sum_eq_sum_iff_of_le (fun x hx => hT_ub x hx)).mp hsum_eq_T u hu

private lemma four_regular_c4_free_card_ge_13 {W : Type} [Fintype W] (H : SimpleGraph W)
    [DecidableRel H.Adj] (hne : Nonempty W) (hdeg : ∀ v, H.degree v = 4)
    (hc4 : ¬ cycleGraph 4 ⊑ H) : 13 ≤ Fintype.card W := by
  obtain ⟨v0⟩ := hne
  let N1 := H.neighborFinset v0
  have hN1_card : N1.card = 4 := by rw [card_neighborFinset_eq_degree, hdeg v0]
  let B1 := insert v0 N1
  have hv0_not_N1 : v0 ∉ N1 := by simp [N1]
  have hB1_card : B1.card = 5 := by rw [Finset.card_insert_of_notMem hv0_not_N1, hN1_card]
  let E : W → Finset W := fun u => H.neighborFinset u \ B1
  have hE_ge2 : ∀ u ∈ N1, 2 ≤ (E u).card := by
    intro u hu
    have hv0u : H.Adj v0 u := (H.mem_neighborFinset v0 u).mp hu
    have hmax1 : (H.neighborFinset u ∩ N1).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro x hx y hy
      have hx' := Finset.mem_inter.mp hx
      have hy' := Finset.mem_inter.mp hy
      have hux := (H.mem_neighborFinset u x).mp hx'.1
      have huy := (H.mem_neighborFinset u y).mp hy'.1
      have hv0x := (H.mem_neighborFinset v0 x).mp hx'.2
      have hv0y := (H.mem_neighborFinset v0 y).mp hy'.2
      rcases no_c4_of_not_copy hc4 hv0x hux.symm huy hv0y.symm with h | h
      · exact absurd h (H.ne_of_adj hv0u)
      · exact h
    have hsub_inter : B1 ∩ H.neighborFinset u ⊆ insert v0 (H.neighborFinset u ∩ N1) := by
      intro x hx
      have ⟨hxB, hxN⟩ := Finset.mem_inter.mp hx
      rcases Finset.mem_insert.mp hxB with h | h
      · rw [h]; exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_inter.mpr ⟨hxN, h⟩)
    have hinter_le2 : (B1 ∩ H.neighborFinset u).card ≤ 2 := by
      have h1 := Finset.card_le_card hsub_inter
      have h2 := Finset.card_insert_le v0 (H.neighborFinset u ∩ N1)
      omega
    have hsdiff : (E u).card = (H.neighborFinset u).card - (B1 ∩ H.neighborFinset u).card :=
      Finset.card_sdiff
    rw [card_neighborFinset_eq_degree, hdeg u] at hsdiff
    omega
  have hdisj_E : (N1 : Set W).PairwiseDisjoint E := by
    intro u1 hu1 u2 hu2 hne'
    change Disjoint (E u1) (E u2)
    rw [Finset.disjoint_left]
    intro w hw1 hw2
    have ⟨hwN1, hwB⟩ := Finset.mem_sdiff.mp hw1
    have ⟨hwN2, _⟩ := Finset.mem_sdiff.mp hw2
    have hv0u1 := (H.mem_neighborFinset v0 u1).mp hu1
    have hv0u2 := (H.mem_neighborFinset v0 u2).mp hu2
    have hu1w := (H.mem_neighborFinset u1 w).mp hwN1
    have hu2w := (H.mem_neighborFinset u2 w).mp hwN2
    have hwv0 : w ≠ v0 := fun h => hwB (by rw [h]; exact Finset.mem_insert_self _ _)
    rcases no_c4_of_not_copy hc4 hv0u1 hu1w hu2w.symm hv0u2.symm with h | h
    · exact hwv0 h.symm
    · exact hne' h
  have hdisj_top : Disjoint B1 (N1.biUnion E) := by
    rw [Finset.disjoint_left]
    intro w hwB hwU
    obtain ⟨u, _, hwE⟩ := Finset.mem_biUnion.mp hwU
    exact (Finset.mem_sdiff.mp hwE).2 hwB
  have hcard_bi : 8 ≤ (N1.biUnion E).card := by
    rw [Finset.card_biUnion (fun u1 hu1 u2 hu2 hne' => hdisj_E hu1 hu2 hne')]
    calc 8 = ∑ _u ∈ N1, 2 := by rw [Finset.sum_const, smul_eq_mul, hN1_card]
      _ ≤ ∑ u ∈ N1, (E u).card := Finset.sum_le_sum hE_ge2
  have hle := Finset.card_le_univ (B1 ∪ N1.biUnion E)
  rw [Finset.card_union_of_disjoint hdisj_top, hB1_card] at hle
  omega

private lemma equality_four_regular_contraction {V : Type} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hnoncub : ∃ v, 3 < G.degree v)
    (hindep : ∀ ⦃a b⦄, G.Adj a b → G.degree a = 3 ∨ G.degree b = 3)
    (hc4 : ¬ cycleGraph 4 ⊑ G) (hc8 : ¬ cycleGraph 8 ⊑ G)
    (hH_deg4 : ∀ v : V, 3 < G.degree v → G.degree v = 4)
    (hT_twoH : ∀ u : V, G.degree u = 3 →
      (G.neighborFinset u ∩ Finset.univ.filter (fun x : V => 3 < G.degree x)).card = 2)
    (h1 : H1) : ∃ k : ℕ, 2 ≤ k ∧ cycleGraph (2 ^ k) ⊑ G := by
  let H := Finset.univ.filter (fun x : V => 3 < G.degree x)
  let W := {v : V // 3 < G.degree v}
  let Q : SimpleGraph W := {
    Adj := fun x y => x ≠ y ∧ ∃ u : V, G.degree u = 3 ∧ G.Adj u x.1 ∧ G.Adj u y.1
    symm := ⟨fun _ _ ⟨hne, u, hu3, hux, huy⟩ => ⟨hne.symm, u, hu3, huy, hux⟩⟩
    loopless := ⟨fun _ ⟨hne, _⟩ => hne rfl⟩
  }
  have hother : ∀ (x : W) (u : V), G.Adj x.1 u →
      ∃! y : W, y ≠ x ∧ G.Adj u y.1 := by
    intro x u hxu
    have hu3 : G.degree u = 3 := by
      rcases hindep hxu with h | h
      · have := x.2; omega
      · exact h
    have hx_mem : x.1 ∈ G.neighborFinset u ∩ H :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset u x.1).mpr hxu.symm,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, x.2⟩⟩
    have hcard1 : ((G.neighborFinset u ∩ H).erase x.1).card = 1 := by
      rw [Finset.card_erase_of_mem hx_mem, hT_twoH u hu3]
    obtain ⟨yv, hyv_eq⟩ := Finset.card_eq_one.mp hcard1
    have hyv_mem : yv ∈ (G.neighborFinset u ∩ H).erase x.1 := by rw [hyv_eq]; simp
    have ⟨hyx, hyv_in⟩ := Finset.mem_erase.mp hyv_mem
    have ⟨hyN, hyH⟩ := Finset.mem_inter.mp hyv_in
    let y : W := ⟨yv, (Finset.mem_filter.mp hyH).2⟩
    refine ⟨y, ⟨fun h => hyx (congrArg Subtype.val h), (G.mem_neighborFinset u yv).mp hyN⟩, ?_⟩
    intro z ⟨hzx, huz⟩
    have hz_mem : z.1 ∈ (G.neighborFinset u ∩ H).erase x.1 :=
      Finset.mem_erase.mpr ⟨fun h => hzx (Subtype.ext h),
        Finset.mem_inter.mpr ⟨(G.mem_neighborFinset u z.1).mpr huz,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, z.2⟩⟩⟩
    rw [hyv_eq, Finset.mem_singleton] at hz_mem
    exact Subtype.ext hz_mem
  have hQ_deg : ∀ x : W, Q.degree x = 4 := by
    intro x
    rw [← card_neighborFinset_eq_degree]
    have hx4 : (G.neighborFinset x.1).card = 4 := by
      rw [card_neighborFinset_eq_degree, hH_deg4 x.1 x.2]
    rw [← hx4]
    symm
    refine Finset.card_bij
      (fun u (hu : u ∈ G.neighborFinset x.1) => (hother x u ((G.mem_neighborFinset x.1 u).mp hu)).choose)
      ?_ ?_ ?_
    · intro u hu
      have hxu := (G.mem_neighborFinset x.1 u).mp hu
      have hu3 : G.degree u = 3 := by
        rcases hindep hxu with h | h
        · have := x.2; omega
        · exact h
      have hspec := (hother x u hxu).choose_spec.1
      exact (Q.mem_neighborFinset x _).mpr ⟨hspec.1.symm, u, hu3, hxu.symm, hspec.2⟩
    · intro u1 hu1 u2 hu2 heq
      have hxu1 := (G.mem_neighborFinset x.1 u1).mp hu1
      have hxu2 := (G.mem_neighborFinset x.1 u2).mp hu2
      have hspec1 := (hother x u1 hxu1).choose_spec.1
      have hspec2 := (hother x u2 hxu2).choose_spec.1
      have hy_adj2 : G.Adj u2 ((hother x u1 hxu1).choose).1 := by rw [heq]; exact hspec2.2
      rcases no_c4_of_not_copy hc4 hxu1 hspec1.2 hy_adj2.symm hxu2.symm with h | h
      · exact absurd h.symm (fun h' => hspec1.1 (Subtype.ext h'))
      · exact h
    · intro y hy
      obtain ⟨hxy, u, _, hux, huy⟩ := (Q.mem_neighborFinset x y).mp hy
      have hu_mem : u ∈ G.neighborFinset x.1 := (G.mem_neighborFinset x.1 u).mpr hux.symm
      refine ⟨u, hu_mem, ?_⟩
      exact ((hother x u hux.symm).unique (hother x u hux.symm).choose_spec.1 ⟨hxy.symm, huy⟩)
  -- Cycle lifting: any m-cycle (m ≥ 3) in Q lifts to a (2*m)-cycle in G
  have hlift : ∀ (m : ℕ), 3 ≤ m → cycleGraph m ⊑ Q → cycleGraph (2 * m) ⊑ G := by
    intro m hm ⟨c⟩
    let : NeZero m := ⟨by omega⟩
    have hstep : ∀ i : Fin m, Q.Adj (c i) (c (i + 1)) := by
      intro i
      apply c.toHom.map_rel'
      apply cycleGraph_adj'.mpr
      right
      simp [Nat.mod_eq_of_lt (show 1 < m by omega)]
    have hmid_ex : ∀ i : Fin m, ∃ u : V, G.degree u = 3 ∧ G.Adj u (c i).1 ∧ G.Adj u (c (i + 1)).1 :=
      fun i => (hstep i).2
    let mid : Fin m → V := fun i => Classical.choose (hmid_ex i)
    have hmid_spec : ∀ i : Fin m, G.degree (mid i) = 3 ∧ G.Adj (mid i) (c i).1 ∧ G.Adj (mid i) (c (i + 1)).1 :=
      fun i => Classical.choose_spec (hmid_ex i)
    have hmid_inj : Function.Injective mid := by
      intro i j hij
      have hci_ne : (c i).1 ≠ (c (i + 1)).1 := fun h => (hstep i).1 (Subtype.ext h)
      have hsub : ({(c i).1, (c (i + 1)).1} : Finset V) ⊆ G.neighborFinset (mid i) ∩ H := by
        intro w hw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with h | h <;> rw [h]
        · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr (hmid_spec i).2.1,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, (c i).2⟩⟩
        · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr (hmid_spec i).2.2,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, (c (i + 1)).2⟩⟩
      have heq_set : ({(c i).1, (c (i + 1)).1} : Finset V) = G.neighborFinset (mid i) ∩ H :=
        Finset.eq_of_subset_of_card_le hsub (by rw [hT_twoH (mid i) (hmid_spec i).1, Finset.card_pair hci_ne])
      have hcj_mem : (c j).1 ∈ ({(c i).1, (c (i + 1)).1} : Finset V) := by
        rw [heq_set, hij]
        exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr (hmid_spec j).2.1,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, (c j).2⟩⟩
      have hcj1_mem : (c (j + 1)).1 ∈ ({(c i).1, (c (i + 1)).1} : Finset V) := by
        rw [heq_set, hij]
        exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr (hmid_spec j).2.2,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, (c (j + 1)).2⟩⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at hcj_mem hcj1_mem
      rcases hcj_mem with h1 | h1
      · exact (c.injective (Subtype.ext h1)).symm
      · have hj1 : j = i + 1 := c.injective (Subtype.ext h1)
        rcases hcj1_mem with h2 | h2
        · have hj2 : j + 1 = i := c.injective (Subtype.ext h2)
          have h20 : (1 : Fin m) + 1 = 0 := by
            have hadd : i + (1 + 1) = i + 0 := by rw [← add_assoc, ← hj1, hj2, add_zero]
            exact add_left_cancel hadd
          have hv : ((1 : Fin m) + 1).val = 0 := congrArg Fin.val h20
          rw [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (show 1 < m by omega),
            Nat.mod_eq_of_lt (show 1 + 1 < m by omega)] at hv
          omega
        · have hj2 : j + 1 = i + 1 := c.injective (Subtype.ext h2)
          have h10 : (1 : Fin m) = 0 := by
            have : j + 1 = j + 0 := by rw [hj2, ← hj1, add_zero]
            exact add_left_cancel this
          have hv : (1 : Fin m).val = 0 := congrArg Fin.val h10
          rw [Fin.val_one', Nat.mod_eq_of_lt (show 1 < m by omega)] at hv
          omega
    let seq : ℕ → V := fun j =>
      let idx : Fin m := ⟨(j / 2) % m, Nat.mod_lt _ (by omega)⟩
      if j % 2 = 0 then (c idx).1 else mid idx
    let L : List V := (List.range (2 * m)).map seq
    have hL_len : L.length = 2 * m := by simp [L]
    have hL_nodup : L.Nodup := by
      rw [List.nodup_map_iff_inj_on List.nodup_range]
      intro a ha b hb hab
      have ha' := List.mem_range.mp ha
      have hb' := List.mem_range.mp hb
      simp only [seq] at hab
      split_ifs at hab with h1 h2
      · have hidx := c.injective (Subtype.ext hab)
        have hval := congrArg Fin.val hidx
        simp only [Nat.mod_eq_of_lt (show a / 2 < m by omega),
          Nat.mod_eq_of_lt (show b / 2 < m by omega)] at hval
        omega
      · have hdeg_a := (c ⟨(a / 2) % m, Nat.mod_lt _ (by omega)⟩).2
        have hdeg_b := (hmid_spec ⟨(b / 2) % m, Nat.mod_lt _ (by omega)⟩).1
        rw [hab] at hdeg_a; omega
      · have hdeg_a := (hmid_spec ⟨(a / 2) % m, Nat.mod_lt _ (by omega)⟩).1
        have hdeg_b := (c ⟨(b / 2) % m, Nat.mod_lt _ (by omega)⟩).2
        rw [hab] at hdeg_a; omega
      · have hidx := hmid_inj hab
        have hval := congrArg Fin.val hidx
        simp only [Nat.mod_eq_of_lt (show a / 2 < m by omega),
          Nat.mod_eq_of_lt (show b / 2 < m by omega)] at hval
        omega
    have hL_chain : L.IsChain G.Adj := by
      rw [List.isChain_iff_getElem]
      intro j hj
      have hj' : j + 1 < 2 * m := by simpa [L] using hj
      simp only [L, List.getElem_map, List.getElem_range]
      by_cases heven : j % 2 = 0
      · have hodd : (j + 1) % 2 ≠ 0 := by omega
        have hdiv : (j + 1) / 2 = j / 2 := by omega
        simp only [seq, heven, ↓reduceIte, hodd, hdiv]
        exact (hmid_spec _).2.1.symm
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
        exact (hmid_spec _).2.2
    have hL_close : ∀ h : L ≠ [], G.Adj (L.getLast h) (L.head h) := by
      intro h
      have hlast : L.getLast h = seq (2 * m - 1) := by rw [List.getLast_eq_getElem]; simp [L]
      have hhead : L.head h = seq 0 := by rw [List.head_eq_getElem]; simp [L]
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
      exact (hmid_spec _).2.2
    have hcyc := OMA.R_Erdos64_erdos_64_R4.cycle_of_ring G L (by omega) hL_nodup hL_chain hL_close
    exact hL_len ▸ hcyc
  have hQ_noc4 : ¬ cycleGraph 4 ⊑ Q := fun h => hc8 (hlift 4 (by norm_num) h)
  -- Restrict Q to a single connected component WC so H1's Connected hypothesis holds
  obtain ⟨v0, hv0⟩ := hnoncub
  let x0 : W := ⟨v0, hv0⟩
  let WC := {x : W // Q.Reachable x0 x}
  let QC : SimpleGraph WC := Q.induce {x : W | Q.Reachable x0 x}
  have hQC_conn : QC.Connected := by
    refine { preconnected := ?_, nonempty := ⟨⟨x0, SimpleGraph.Reachable.refl x0⟩⟩ }
    have hreach0 : ∀ x : WC, QC.Reachable ⟨x0, SimpleGraph.Reachable.refl x0⟩ x := by
      rintro ⟨x, hx⟩
      rcases hx with ⟨p⟩
      have hrec : ∀ {a b : W} (q : Q.Walk a b) (ha : Q.Reachable x0 a),
          QC.Reachable ⟨a, ha⟩ ⟨b, ha.trans ⟨q⟩⟩ := by
        intro a b q ha
        induction q with
        | nil => exact SimpleGraph.Reachable.refl _
        | @cons u v w huv q' ih =>
          have hv : Q.Reachable x0 v := ha.trans huv.reachable
          have hadj : QC.Adj ⟨u, ha⟩ ⟨v, hv⟩ := huv
          exact hadj.reachable.trans (ih hv)
      exact hrec p (SimpleGraph.Reachable.refl x0)
    intro x y
    exact (hreach0 x).symm.trans (hreach0 y)
  have hQC_deg : ∀ x : WC, QC.degree x = 4 := by
    intro x
    rw [← card_neighborFinset_eq_degree, ← hQ_deg x.1, ← card_neighborFinset_eq_degree]
    refine Finset.card_bij (fun y _ => y.1) ?_ ?_ ?_
    · intro y hy
      exact (Q.mem_neighborFinset x.1 y.1).mpr ((QC.mem_neighborFinset x y).mp hy)
    · intro y1 _ y2 _ heq; exact Subtype.ext heq
    · intro y hy
      have hadj : Q.Adj x.1 y := (Q.mem_neighborFinset x.1 y).mp hy
      exact ⟨⟨y, x.2.trans hadj.reachable⟩, (QC.mem_neighborFinset x _).mpr hadj, rfl⟩
  have hQC_emb : QC ↪g Q := SimpleGraph.Embedding.induce _
  have hQC_noc4 : ¬ cycleGraph 4 ⊑ QC := fun ⟨c⟩ => hQ_noc4 ⟨hQC_emb.toCopy.comp c⟩
  have hQC_card13 : 13 ≤ Fintype.card WC :=
    four_regular_c4_free_card_ge_13 QC hQC_conn.nonempty hQC_deg hQC_noc4
  obtain ⟨k, hk, ⟨c⟩⟩ := h1 WC QC hQC_conn hQC_deg hQC_noc4 hQC_card13
  have hpow : 2 * 2 ^ k = 2 ^ (k + 1) := by rw [pow_succ, mul_comm]
  have hm3 : 3 ≤ 2 ^ k := by
    calc (3 : ℕ) ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  exact ⟨k + 1, by omega, hpow ▸ hlift (2 ^ k) hm3 ⟨hQC_emb.toCopy.comp c⟩⟩

/- ### Part 2: Noncubic neighborhood expansion bound and |V| ≥ 10 -/

private lemma c4_of_card_four_min_deg_two {V : Type} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {S : Finset V} (hS : S.card = 4)
    (hdeg2 : ∀ w ∈ S, 2 ≤ (G.neighborFinset w ∩ S).card) : cycleGraph 4 ⊑ G := by
  obtain ⟨w1, hw1⟩ := Finset.card_pos.mp (show 0 < S.card by omega)
  have hcard3 : (S.erase w1).card = 3 := by rw [Finset.card_erase_of_mem hw1, hS]
  obtain ⟨w2, w3, w4, h23, h24, h34, her⟩ := Finset.card_eq_three.mp hcard3
  have hw2 : w2 ∈ S := Finset.mem_of_mem_erase (by rw [her]; simp)
  have hw3 : w3 ∈ S := Finset.mem_of_mem_erase (by rw [her]; simp)
  have hw4 : w4 ∈ S := Finset.mem_of_mem_erase (by rw [her]; simp)
  have h12 : w1 ≠ w2 := (Finset.ne_of_mem_erase (by rw [her]; simp)).symm
  have h13 : w1 ≠ w3 := (Finset.ne_of_mem_erase (by rw [her]; simp)).symm
  have h14 : w1 ≠ w4 := (Finset.ne_of_mem_erase (by rw [her]; simp)).symm
  have hSeq : S = {w1, w2, w3, w4} := by rw [← Finset.insert_erase hw1, her]
  have h2of3 : ∀ {x a b c : V}, x ∈ S → S.erase x = {a, b, c} →
      (G.Adj x a ∧ G.Adj x b) ∨ (G.Adj x a ∧ G.Adj x c) ∨ (G.Adj x b ∧ G.Adj x c) := by
    intro x a b c hx hxer
    have hsub : G.neighborFinset x ∩ S ⊆ {a, b, c} := by
      rw [← hxer]
      intro z hz
      have ⟨hzN, hzS⟩ := Finset.mem_inter.mp hz
      exact Finset.mem_erase.mpr ⟨(G.ne_of_adj ((G.mem_neighborFinset x z).mp hzN)).symm, hzS⟩
    have h2 := hdeg2 x hx
    by_cases ha : G.Adj x a
    · by_cases hb : G.Adj x b
      · exact Or.inl ⟨ha, hb⟩
      · by_cases hc : G.Adj x c
        · exact Or.inr (Or.inl ⟨ha, hc⟩)
        · exfalso
          have hsub1 : G.neighborFinset x ∩ S ⊆ {a} := by
            intro z hz
            have hz3 := hsub hz
            have hxz := (G.mem_neighborFinset x z).mp (Finset.mem_inter.mp hz).1
            simp only [Finset.mem_insert, Finset.mem_singleton] at hz3 ⊢
            rcases hz3 with h | h | h
            · exact h
            · rw [h] at hxz; exact absurd hxz hb
            · rw [h] at hxz; exact absurd hxz hc
          have := Finset.card_le_card hsub1
          rw [Finset.card_singleton] at this; omega
    · by_cases hb : G.Adj x b
      · by_cases hc : G.Adj x c
        · exact Or.inr (Or.inr ⟨hb, hc⟩)
        · exfalso
          have hsub1 : G.neighborFinset x ∩ S ⊆ {b} := by
            intro z hz
            have hz3 := hsub hz
            have hxz := (G.mem_neighborFinset x z).mp (Finset.mem_inter.mp hz).1
            simp only [Finset.mem_insert, Finset.mem_singleton] at hz3 ⊢
            rcases hz3 with h | h | h
            · rw [h] at hxz; exact absurd hxz ha
            · exact h
            · rw [h] at hxz; exact absurd hxz hc
          have := Finset.card_le_card hsub1
          rw [Finset.card_singleton] at this; omega
      · exfalso
        have hsub1 : G.neighborFinset x ∩ S ⊆ {c} := by
          intro z hz
          have hz3 := hsub hz
          have hxz := (G.mem_neighborFinset x z).mp (Finset.mem_inter.mp hz).1
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz3 ⊢
          rcases hz3 with h | h | h
          · rw [h] at hxz; exact absurd hxz ha
          · rw [h] at hxz; exact absurd hxz hb
          · exact h
        have := Finset.card_le_card hsub1
        rw [Finset.card_singleton] at this; omega
  have hmk : ∀ (x a b d : V), x ∈ S → a ∈ S → b ∈ S → d ∈ S →
      x ≠ a → x ≠ b → x ≠ d → a ≠ b → a ≠ d → b ≠ d →
      S.erase d = {x, a, b} → S.erase a = {x, b, d} → S.erase b = {x, a, d} →
      G.Adj x a → G.Adj x b → cycleGraph 4 ⊑ G := by
    intro x a b d _ ha hb hd hxa hxb hxd hab had hbd herd hera herb h1 h2
    rcases h2of3 hd herd with ⟨hdx, hda⟩ | ⟨hdx, hdb⟩ | ⟨hda, hdb⟩
    · rcases h2of3 hb herb with ⟨_, hba⟩ | ⟨_, hbd'⟩ | ⟨hba, _⟩
      · exact OMA.R_Erdos64_erdos_64_R4.square_of_four hdx.symm hda hba.symm h2.symm hxa hbd.symm
      · exact OMA.R_Erdos64_erdos_64_R4.square_of_four h1 hda.symm hbd'.symm h2.symm hxd hab
      · exact OMA.R_Erdos64_erdos_64_R4.square_of_four hdx.symm hda hba.symm h2.symm hxa hbd.symm
    · rcases h2of3 ha hera with ⟨_, hab'⟩ | ⟨_, had'⟩ | ⟨hab', _⟩
      · exact OMA.R_Erdos64_erdos_64_R4.square_of_four hdx.symm hdb hab'.symm h1.symm hxb had.symm
      · exact OMA.R_Erdos64_erdos_64_R4.square_of_four h1 had' hdb h2.symm hxd hab
      · exact OMA.R_Erdos64_erdos_64_R4.square_of_four hdx.symm hdb hab'.symm h1.symm hxb had.symm
    · exact OMA.R_Erdos64_erdos_64_R4.square_of_four h1 hda.symm hdb h2.symm hxd hab
  have her2 : S.erase w2 = {w1, w3, w4} := by
    rw [hSeq]; ext z; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hz2, h | h | h | h⟩
      · exact Or.inl h
      · exact absurd h hz2
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    · rintro (rfl | rfl | rfl) <;> simp [h12, h23.symm, h24.symm]
  have her3 : S.erase w3 = {w1, w2, w4} := by
    rw [hSeq]; ext z; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hz3, h | h | h | h⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact absurd h hz3
      · exact Or.inr (Or.inr h)
    · rintro (rfl | rfl | rfl) <;> simp [h13, h23, h34.symm]
  have her4 : S.erase w4 = {w1, w2, w3} := by
    rw [hSeq]; ext z; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hz4, h | h | h | h⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
      · exact absurd h hz4
    · rintro (rfl | rfl | rfl) <;> simp [h14, h24, h34]
  have her2' : S.erase w2 = {w1, w4, w3} := by rw [her2, Finset.pair_comm w3 w4]
  have her3' : S.erase w3 = {w1, w4, w2} := by rw [her3, Finset.pair_comm w2 w4]
  have her4' : S.erase w4 = {w1, w3, w2} := by rw [her4, Finset.pair_comm w2 w3]
  rcases h2of3 hw1 her with ⟨e12, e13⟩ | ⟨e12, e14⟩ | ⟨e13, e14⟩
  · exact hmk w1 w2 w3 w4 hw1 hw2 hw3 hw4 h12 h13 h14 h23 h24 h34 her4 her2 her3 e12 e13
  · exact hmk w1 w2 w4 w3 hw1 hw2 hw4 hw3 h12 h14 h13 h24 h23 h34.symm her3 her2' her4 e12 e14
  · exact hmk w1 w3 w4 w2 hw1 hw3 hw4 hw2 h13 h14 h12 h34 h23.symm h24.symm her2 her3' her4' e13 e14

private lemma noncubic_ball_bound {V : Type} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hmin : ∀ x, 3 ≤ G.degree x) (hnoncub : ∃ v, 3 < G.degree v)
    (hc4 : ¬ cycleGraph 4 ⊑ G) :
    (∀ v, 3 < G.degree v → 2 * G.degree v + 1 ≤ Fintype.card V) ∧ 10 ≤ Fintype.card V := by
  have hexpand : ∀ v : V, ∃ N2 : Finset V,
      Disjoint (insert v (G.neighborFinset v)) N2 ∧
      G.degree v ≤ N2.card ∧
      ∀ w ∈ N2, (G.neighborFinset w ∩ insert v (G.neighborFinset v)).card ≤ 1 := by
    intro v
    let N1 := G.neighborFinset v
    let B1 := insert v N1
    let E : V → Finset V := fun u => G.neighborFinset u \ B1
    have hE_ge1 : ∀ u ∈ N1, 1 ≤ (E u).card := by
      intro u hu
      have hvu : G.Adj v u := (G.mem_neighborFinset v u).mp hu
      have hmax1 : (G.neighborFinset u ∩ N1).card ≤ 1 := by
        rw [Finset.card_le_one]
        intro x hx y hy
        have hx' := Finset.mem_inter.mp hx
        have hy' := Finset.mem_inter.mp hy
        rcases no_c4_of_not_copy hc4 ((G.mem_neighborFinset v x).mp hx'.2)
            ((G.mem_neighborFinset u x).mp hx'.1).symm
            ((G.mem_neighborFinset u y).mp hy'.1)
            ((G.mem_neighborFinset v y).mp hy'.2).symm with h | h
        · exact absurd h (G.ne_of_adj hvu)
        · exact h
      have hsub_inter : B1 ∩ G.neighborFinset u ⊆ insert v (G.neighborFinset u ∩ N1) := by
        intro x hx
        have ⟨hxB, hxN⟩ := Finset.mem_inter.mp hx
        rcases Finset.mem_insert.mp hxB with h | h
        · rw [h]; exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (Finset.mem_inter.mpr ⟨hxN, h⟩)
      have hinter_le2 : (B1 ∩ G.neighborFinset u).card ≤ 2 := by
        have h1 := Finset.card_le_card hsub_inter
        have h2 := Finset.card_insert_le v (G.neighborFinset u ∩ N1)
        omega
      have hsdiff : (E u).card = (G.neighborFinset u).card - (B1 ∩ G.neighborFinset u).card :=
        Finset.card_sdiff
      rw [card_neighborFinset_eq_degree] at hsdiff
      have := hmin u
      omega
    have hdisj_E : (N1 : Set V).PairwiseDisjoint E := by
      intro u1 hu1 u2 hu2 hne'
      change Disjoint (E u1) (E u2)
      rw [Finset.disjoint_left]
      intro w hw1 hw2
      have ⟨hwN1, hwB⟩ := Finset.mem_sdiff.mp hw1
      have ⟨hwN2, _⟩ := Finset.mem_sdiff.mp hw2
      have hwv : w ≠ v := fun h => hwB (by rw [h]; exact Finset.mem_insert_self _ _)
      rcases no_c4_of_not_copy hc4 ((G.mem_neighborFinset v u1).mp hu1)
          ((G.mem_neighborFinset u1 w).mp hwN1)
          ((G.mem_neighborFinset u2 w).mp hwN2).symm
          ((G.mem_neighborFinset v u2).mp hu2).symm with h | h
      · exact hwv h.symm
      · exact hne' h
    refine ⟨N1.biUnion E, ?_, ?_, ?_⟩
    · rw [Finset.disjoint_left]
      intro w hwB hwU
      obtain ⟨u, _, hwE⟩ := Finset.mem_biUnion.mp hwU
      exact (Finset.mem_sdiff.mp hwE).2 hwB
    · rw [Finset.card_biUnion (fun u1 hu1 u2 hu2 hne' => hdisj_E hu1 hu2 hne')]
      calc G.degree v = N1.card := (card_neighborFinset_eq_degree G v).symm
        _ = ∑ _u ∈ N1, 1 := by rw [Finset.sum_const, smul_eq_mul, mul_one]
        _ ≤ ∑ u ∈ N1, (E u).card := Finset.sum_le_sum hE_ge1
    · intro w hw
      obtain ⟨_, _, hwE⟩ := Finset.mem_biUnion.mp hw
      have hwB : w ∉ B1 := (Finset.mem_sdiff.mp hwE).2
      rw [Finset.card_le_one]
      intro x hx y hy
      have hx' := Finset.mem_inter.mp hx
      have hy' := Finset.mem_inter.mp hy
      have hwx := (G.mem_neighborFinset w x).mp hx'.1
      have hwy := (G.mem_neighborFinset w y).mp hy'.1
      have hxN1 : x ∈ N1 := by
        rcases Finset.mem_insert.mp hx'.2 with h | h
        · exfalso; rw [h] at hwx; exact hwB (Finset.mem_insert_of_mem ((G.mem_neighborFinset v w).mpr hwx.symm))
        · exact h
      have hyN1 : y ∈ N1 := by
        rcases Finset.mem_insert.mp hy'.2 with h | h
        · exfalso; rw [h] at hwy; exact hwB (Finset.mem_insert_of_mem ((G.mem_neighborFinset v w).mpr hwy.symm))
        · exact h
      have hwv : w ≠ v := fun h => hwB (by rw [h]; exact Finset.mem_insert_self _ _)
      rcases no_c4_of_not_copy hc4 ((G.mem_neighborFinset v x).mp hxN1) hwx.symm hwy
          ((G.mem_neighborFinset v y).mp hyN1).symm with h | h
      · exact absurd h hwv.symm
      · exact h
  have hbound : ∀ v : V, 3 < G.degree v → 2 * G.degree v + 1 ≤ Fintype.card V := by
    intro v _
    obtain ⟨N2, hdisj, hN2_ge, _⟩ := hexpand v
    have hle := Finset.card_le_univ (insert v (G.neighborFinset v) ∪ N2)
    rw [Finset.card_union_of_disjoint hdisj,
      Finset.card_insert_of_notMem (by simp), card_neighborFinset_eq_degree] at hle
    omega
  refine ⟨hbound, ?_⟩
  obtain ⟨v0, hv0⟩ := hnoncub
  have hge9 : 9 ≤ Fintype.card V := by have := hbound v0 hv0; omega
  by_contra hlt10
  have hcard9 : Fintype.card V = 9 := by omega
  have hdeg4 : G.degree v0 = 4 := by have := hbound v0 hv0; omega
  obtain ⟨N2, hdisj, hN2_ge, hN2_nb1⟩ := hexpand v0
  let B1 := insert v0 (G.neighborFinset v0)
  have hB1_card : B1.card = 5 := by
    rw [Finset.card_insert_of_notMem (by simp), card_neighborFinset_eq_degree, hdeg4]
  have hU_le : (B1 ∪ N2).card ≤ 9 := by
    have := Finset.card_le_univ (B1 ∪ N2); omega
  rw [Finset.card_union_of_disjoint hdisj, hB1_card] at hU_le
  have hN2_card : N2.card = 4 := by omega
  have hU_univ : B1 ∪ N2 = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_union_of_disjoint hdisj, hB1_card, hN2_card, hcard9]
  have hN2_deg2 : ∀ w ∈ N2, 2 ≤ (G.neighborFinset w ∩ N2).card := by
    intro w hw
    have hcov : G.neighborFinset w ⊆ (G.neighborFinset w ∩ B1) ∪ (G.neighborFinset w ∩ N2) := by
      intro z hz
      have : z ∈ B1 ∪ N2 := by rw [hU_univ]; exact Finset.mem_univ z
      rcases Finset.mem_union.mp this with hB | hN
      · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hz, hB⟩)
      · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hz, hN⟩)
    have hle := (Finset.card_le_card hcov).trans (Finset.card_union_le _ _)
    rw [card_neighborFinset_eq_degree] at hle
    have h1 : (G.neighborFinset w ∩ B1).card ≤ 1 := hN2_nb1 w hw
    have h3 := hmin w
    omega
  exact hc4 (c4_of_card_four_min_deg_two G hN2_card hN2_deg2)

/- ### Part 3: Uniqueness and vertex-transitivity of the Petersen graph -/

private lemma petersen_unique_vt {V : Type} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hcard10 : Fintype.card V = 10) (hdeg : ∀ x, G.degree x = 3)
    (htf : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    (hc4 : ¬ cycleGraph 4 ⊑ G) :
    ∀ x y : V, ∃ g : G ≃g G, g x = y := by
  let edges10 : List (Fin 10 × Fin 10) :=
    [(0,1),(0,2),(0,3),(1,4),(1,5),(2,6),(2,7),(3,8),(3,9),(4,6),(4,8),(5,7),(5,9),(6,9),(7,8)]
  let P10 : SimpleGraph (Fin 10) := SimpleGraph.fromRel (fun i j => (i, j) ∈ edges10)
  have hiso : ∀ u : V, ∃ e : P10 ≃g G, e 0 = u := by
    intro u
    have hN1_card : (G.neighborFinset u).card = 3 := by
      rw [card_neighborFinset_eq_degree, hdeg u]
    obtain ⟨v1, v2, v3, hv12, hv13, hv23, hN1_eq⟩ := Finset.card_eq_three.mp hN1_card
    have huv1 : G.Adj u v1 := (G.mem_neighborFinset u v1).mp (by rw [hN1_eq]; simp)
    have huv2 : G.Adj u v2 := (G.mem_neighborFinset u v2).mp (by rw [hN1_eq]; simp)
    have huv3 : G.Adj u v3 := (G.mem_neighborFinset u v3).mp (by rw [hN1_eq]; simp)
    have hpair : ∀ v : V, G.Adj u v → ∃ a b : V, (G.neighborFinset v).erase u = {a, b} := by
      intro v huv
      have hc : ((G.neighborFinset v).erase u).card = 2 := by
        rw [Finset.card_erase_of_mem ((G.mem_neighborFinset v u).mpr huv.symm),
          card_neighborFinset_eq_degree, hdeg v]
      obtain ⟨a, b, _, heq⟩ := Finset.card_eq_two.mp hc
      exact ⟨a, b, heq⟩
    obtain ⟨a1, a2, hA1⟩ := hpair v1 huv1
    obtain ⟨b10, b20, hA20⟩ := hpair v2 huv2
    obtain ⟨c10, c20, hA30⟩ := hpair v3 huv3
    -- Helper: in a 10-vertex girth ≥ 5 cubic graph, every vertex in one N2-pair has
    -- 1 neighbor in each of the other two N2-pairs
    have hn2_adj : ∀ {vp vq vr p1 p2 q1 q2 r1 r2 : V},
        G.Adj u vp → G.Adj u vq → G.Adj u vr → vp ≠ vq → vp ≠ vr → vq ≠ vr →
        (G.neighborFinset vp).erase u = {p1, p2} →
        (G.neighborFinset vq).erase u = {q1, q2} →
        (G.neighborFinset vr).erase u = {r1, r2} →
        (G.Adj p1 q1 ∨ G.Adj p1 q2) ∧ (G.Adj p1 r1 ∨ G.Adj p1 r2) := by
      intro vp vq vr p1 p2 q1 q2 r1 r2 huvp huvq huvr hpq hpr hqr hAp hAq hAr
      obtain ⟨hvpp1, hvpp2, hp1u, _, _⟩ := pair_adj_ne hdeg huvp hAp
      obtain ⟨hvqq1, hvqq2, _, _, hq12⟩ := pair_adj_ne hdeg huvq hAq
      obtain ⟨hvrr1, hvrr2, _, _, hr12⟩ := pair_adj_ne hdeg huvr hAr
      have h10 := bfs10_nodup hdeg htf hc4 huvp huvq huvr hpq hpr hqr hAp hAq hAr
      let L10 : List V := [u, vp, vq, vr, p1, p2, q1, q2, r1, r2]
      have hL10_univ : L10.toFinset = Finset.univ := by
        apply Finset.eq_univ_of_card
        rw [List.toFinset_card_of_nodup h10, hcard10]; rfl
      have hcov10 : ∀ z : V, z = u ∨ z = vp ∨ z = vq ∨ z = vr ∨
          z = p1 ∨ z = p2 ∨ z = q1 ∨ z = q2 ∨ z = r1 ∨ z = r2 := by
        intro z
        have hz : z ∈ L10 := List.mem_toFinset.mp (by rw [hL10_univ]; exact Finset.mem_univ z)
        simpa only [L10, List.mem_cons, List.not_mem_nil, or_false] using hz
      have hp1_sub : (G.neighborFinset p1).erase vp ⊆ {q1, q2, r1, r2} := by
        intro z hz
        have ⟨hzv, hzp1⟩ := Finset.mem_erase.mp hz
        have hpz := (G.mem_neighborFinset p1 z).mp hzp1
        rcases hcov10 z with h | h | h | h | h | h | h | h | h | h
        · rw [h] at hpz; exact absurd hpz (fun h' => htf u vp p1 huvp hvpp1 h')
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
        have hpx := (G.mem_neighborFinset p1 x).mp (Finset.mem_of_mem_erase hx'.1)
        have hpy := (G.mem_neighborFinset p1 y).mp (Finset.mem_of_mem_erase hy'.1)
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx' hy'
        rcases hx'.2 with h1 | h1 <;> rcases hy'.2 with h2 | h2
        · rw [h1, h2]
        · rw [h1] at hpx; rw [h2] at hpy; exact absurd hpy (no_both_nb hc4 hvqq1 hvqq2 hq12 hp1_ne_vq hpx)
        · rw [h1] at hpx; rw [h2] at hpy; exact absurd hpx (no_both_nb hc4 hvqq1 hvqq2 hq12 hp1_ne_vq hpy)
        · rw [h1, h2]
      have hmax1_r : (((G.neighborFinset p1).erase vp) ∩ {r1, r2}).card ≤ 1 := by
        rw [Finset.card_le_one]
        intro x hx y hy
        have hx' := Finset.mem_inter.mp hx
        have hy' := Finset.mem_inter.mp hy
        have hpx := (G.mem_neighborFinset p1 x).mp (Finset.mem_of_mem_erase hx'.1)
        have hpy := (G.mem_neighborFinset p1 y).mp (Finset.mem_of_mem_erase hy'.1)
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx' hy'
        rcases hx'.2 with h1 | h1 <;> rcases hy'.2 with h2 | h2
        · rw [h1, h2]
        · rw [h1] at hpx; rw [h2] at hpy; exact absurd hpy (no_both_nb hc4 hvrr1 hvrr2 hr12 hp1_ne_vr hpx)
        · rw [h1] at hpx; rw [h2] at hpy; exact absurd hpx (no_both_nb hc4 hvrr1 hvrr2 hr12 hp1_ne_vr hpy)
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
      obtain ⟨zq, hzq⟩ := Finset.card_pos.mp (show 0 < (((G.neighborFinset p1).erase vp) ∩ {q1, q2}).card by omega)
      obtain ⟨zr, hzr⟩ := Finset.card_pos.mp (show 0 < (((G.neighborFinset p1).erase vp) ∩ {r1, r2}).card by omega)
      have hzq' := Finset.mem_inter.mp hzq
      have hzr' := Finset.mem_inter.mp hzr
      constructor
      · have hadj := (G.mem_neighborFinset p1 zq).mp (Finset.mem_of_mem_erase hzq'.1)
        simp only [Finset.mem_insert, Finset.mem_singleton] at hzq'
        rcases hzq'.2 with h | h <;> (rw [h] at hadj; simp [hadj])
      · have hadj := (G.mem_neighborFinset p1 zr).mp (Finset.mem_of_mem_erase hzr'.1)
        simp only [Finset.mem_insert, Finset.mem_singleton] at hzr'
        rcases hzr'.2 with h | h <;> (rw [h] at hadj; simp [hadj])
    -- Align b1, b2 so a1 ~ b1 and c1, c2 so a1 ~ c1
    have ⟨ha1_b0, ha1_c0⟩ := hn2_adj huv1 huv2 huv3 hv12 hv13 hv23 hA1 hA20 hA30
    obtain ⟨b1, b2, hA2, ha1b1⟩ : ∃ b1 b2 : V, (G.neighborFinset v2).erase u = {b1, b2} ∧ G.Adj a1 b1 := by
      rcases ha1_b0 with h | h
      · exact ⟨b10, b20, hA20, h⟩
      · exact ⟨b20, b10, by rw [hA20, Finset.pair_comm], h⟩
    obtain ⟨c1, c2, hA3, ha1c1⟩ : ∃ c1 c2 : V, (G.neighborFinset v3).erase u = {c1, c2} ∧ G.Adj a1 c1 := by
      rcases ha1_c0 with h | h
      · exact ⟨c10, c20, hA30, h⟩
      · exact ⟨c20, c10, by rw [hA30, Finset.pair_comm], h⟩
    obtain ⟨hv1a1, hv1a2, _, _, ha12⟩ := pair_adj_ne hdeg huv1 hA1
    obtain ⟨hv2b1, hv2b2, _, _, hb12⟩ := pair_adj_ne hdeg huv2 hA2
    obtain ⟨hv3c1, hv3c2, _, _, hc12⟩ := pair_adj_ne hdeg huv3 hA3
    have hA1_sw : (G.neighborFinset v1).erase u = {a2, a1} := by rw [hA1, Finset.pair_comm]
    have ⟨ha2_b, ha2_c⟩ := hn2_adj huv1 huv2 huv3 hv12 hv13 hv23 hA1_sw hA2 hA3
    have ha2b2 : G.Adj a2 b2 := ha2_b.resolve_left (fun h =>
      no_both_nb hc4 hv1a1 hv1a2 ha12 (n1_ne_n2 htf huv1 huv2 hv2b1).symm ha1b1.symm h.symm)
    have ha2c2 : G.Adj a2 c2 := ha2_c.resolve_left (fun h =>
      no_both_nb hc4 hv1a1 hv1a2 ha12 (n1_ne_n2 htf huv1 huv3 hv3c1).symm ha1c1.symm h.symm)
    have ⟨_, hb1_c⟩ := hn2_adj huv2 huv1 huv3 hv12.symm hv23 hv13 hA2 hA1 hA3
    have hb1c2 : G.Adj b1 c2 := hb1_c.resolve_left (fun h => htf a1 b1 c1 ha1b1 h ha1c1.symm)
    have hA2_sw : (G.neighborFinset v2).erase u = {b2, b1} := by rw [hA2, Finset.pair_comm]
    have ⟨_, hb2_c⟩ := hn2_adj huv2 huv1 huv3 hv12.symm hv23 hv13 hA2_sw hA1 hA3
    have hb2c1 : G.Adj b2 c1 := hb2_c.resolve_right (fun h => htf a2 b2 c2 ha2b2 h ha2c2.symm)
    -- Construct the isomorphism P10 ≃g G sending 0 ↦ u
    have h10_nd := bfs10_nodup hdeg htf hc4 huv1 huv2 huv3 hv12 hv13 hv23 hA1 hA2 hA3
    let L10 : List V := [u, v1, v2, v3, a1, a2, b1, b2, c1, c2]
    let f : Fin 10 → V := fun i => L10[i.val]
    have hf_inj : Function.Injective f := by
      intro i j hij
      have h := (List.Nodup.get_inj_iff h10_nd).mp (by simpa [f, List.get_eq_getElem] using hij)
      exact Fin.ext (congrArg Fin.val h)
    have hf_bij : Function.Bijective f :=
      (Fintype.bijective_iff_injective_and_card f).mpr ⟨hf_inj, by simp [hcard10]⟩
    let e : Fin 10 ≃ V := Equiv.ofBijective f hf_bij
    have hnb_eq : ∀ (i n1 n2 n3 : Fin 10),
        n1 ≠ n2 → n1 ≠ n3 → n2 ≠ n3 →
        G.Adj (f i) (f n1) → G.Adj (f i) (f n2) → G.Adj (f i) (f n3) →
        ∀ j : Fin 10, G.Adj (f i) (f j) → j = n1 ∨ j = n2 ∨ j = n3 := by
      intro i n1 n2 n3 h12 h13 h23 e1 e2 e3 j hj
      have hsub : ({f n1, f n2, f n3} : Finset V) ⊆ G.neighborFinset (f i) := by
        intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with h | h | h <;> rw [h]
        · exact (G.mem_neighborFinset _ _).mpr e1
        · exact (G.mem_neighborFinset _ _).mpr e2
        · exact (G.mem_neighborFinset _ _).mpr e3
      have hcard3 : ({f n1, f n2, f n3} : Finset V).card = 3 := by
        rw [Finset.card_insert_of_notMem (by simp [hf_inj.ne h12, hf_inj.ne h13]),
          Finset.card_pair (hf_inj.ne h23)]
      have heq := Finset.eq_of_subset_of_card_le hsub
        (by rw [card_neighborFinset_eq_degree, hdeg, hcard3])
      have hmem : f j ∈ ({f n1, f n2, f n3} : Finset V) :=
        heq ▸ (G.mem_neighborFinset _ _).mpr hj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with h | h | h
      · exact Or.inl (hf_inj h)
      · exact Or.inr (Or.inl (hf_inj h))
      · exact Or.inr (Or.inr (hf_inj h))
    have hf_adj_fwd : ∀ i j : Fin 10, (i, j) ∈ edges10 → G.Adj (f i) (f j) := by
      intro i j hij
      simp only [edges10, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hij
      rcases hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        dsimp [f, L10] <;> assumption
    have hmap : ∀ {i j : Fin 10}, G.Adj (e i) (e j) ↔ P10.Adj i j := by
      intro i j
      constructor
      · intro hij
        have hij' : G.Adj (f i) (f j) := hij
        have hmkP : ∀ {x y : Fin 10}, (x, y) ∈ edges10 ∨ (y, x) ∈ edges10 → x ≠ y → P10.Adj x y :=
          fun h hne => ⟨hne, h⟩
        fin_cases i
        · rcases hnb_eq 0 1 2 3 (by decide) (by decide) (by decide) huv1 huv2 huv3 j hij' with
            rfl | rfl | rfl <;> exact hmkP (by simp [edges10]) (by decide)
        · rcases hnb_eq 1 0 4 5 (by decide) (by decide) (by decide) huv1.symm hv1a1 hv1a2 j hij' with
            rfl | rfl | rfl <;> exact hmkP (by simp [edges10]) (by decide)
        · rcases hnb_eq 2 0 6 7 (by decide) (by decide) (by decide) huv2.symm hv2b1 hv2b2 j hij' with
            rfl | rfl | rfl <;> exact hmkP (by simp [edges10]) (by decide)
        · rcases hnb_eq 3 0 8 9 (by decide) (by decide) (by decide) huv3.symm hv3c1 hv3c2 j hij' with
            rfl | rfl | rfl <;> exact hmkP (by simp [edges10]) (by decide)
        · rcases hnb_eq 4 1 6 8 (by decide) (by decide) (by decide) hv1a1.symm ha1b1 ha1c1 j hij' with
            rfl | rfl | rfl <;> exact hmkP (by simp [edges10]) (by decide)
        · rcases hnb_eq 5 1 7 9 (by decide) (by decide) (by decide) hv1a2.symm ha2b2 ha2c2 j hij' with
            rfl | rfl | rfl <;> exact hmkP (by simp [edges10]) (by decide)
        · rcases hnb_eq 6 2 4 9 (by decide) (by decide) (by decide) hv2b1.symm ha1b1.symm hb1c2 j hij' with
            rfl | rfl | rfl <;> exact hmkP (by simp [edges10]) (by decide)
        · rcases hnb_eq 7 2 5 8 (by decide) (by decide) (by decide) hv2b2.symm ha2b2.symm hb2c1 j hij' with
            rfl | rfl | rfl <;> exact hmkP (by simp [edges10]) (by decide)
        · rcases hnb_eq 8 3 4 7 (by decide) (by decide) (by decide) hv3c1.symm ha1c1.symm hb2c1.symm j hij' with
            rfl | rfl | rfl <;> exact hmkP (by simp [edges10]) (by decide)
        · rcases hnb_eq 9 3 5 6 (by decide) (by decide) (by decide) hv3c2.symm ha2c2.symm hb1c2.symm j hij' with
            rfl | rfl | rfl <;> exact hmkP (by simp [edges10]) (by decide)
      · rintro ⟨_, h | h⟩
        · exact hf_adj_fwd i j h
        · exact (hf_adj_fwd j i h).symm
    exact ⟨⟨e, hmap⟩, rfl⟩
  intro x y
  obtain ⟨ex, hex⟩ := hiso x
  obtain ⟨ey, hey⟩ := hiso y
  refine ⟨ex.symm.trans ey, ?_⟩
  show ey (ex.symm x) = y
  rw [← hex, ex.symm_apply_apply, hey]


private lemma tri10_finish_rz {V : Type} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hdeg : ∀ x, G.degree x = 3) (hc8 : ¬ cycleGraph 8 ⊑ G)
    {S6 R : Finset V} {a' b' c' p0 q0 p0' q0' r' w u1 u2 z : V}
    (hdisj : ∀ v ∈ R, v ∉ S6)
    (hw_nb_sub : ∀ v ∈ R, G.neighborFinset v ⊆ {a', b', c'} ∪ R)
    (hp0q0 : G.Adj p0 q0) (hp0p0' : G.Adj p0 p0') (hq0q0' : G.Adj q0 q0')
    (hp0S : p0 ∈ S6) (hq0S : q0 ∈ S6) (hp0'S : p0' ∈ S6) (hq0'S : q0' ∈ S6) (hr'S : r' ∈ S6)
    (hp0q0' : p0' ≠ q0') (hp0r' : p0' ≠ r') (hp0q0'_ne : p0 ≠ q0') (hq0p0'_ne : q0 ≠ p0')
    (h3eq : ({p0', q0', r'} : Finset V) = {a', b', c'})
    (hwR : w ∈ R) (hu1R : u1 ∈ R) (hu2R : u2 ∈ R) (hzR : z ∈ R)
    (hu1w : u1 ≠ w) (hu2w : u2 ≠ w) (hzw : z ≠ w) (hu12 : u1 ≠ u2) (hu1z : u1 ≠ z) (hu2z : u2 ≠ z)
    (hReq : R = {w, u1, u2, z})
    (hwp0' : G.Adj w p0') (hwq0' : G.Adj w q0') (hnwr' : ¬ G.Adj w r')
    (hp0'u1 : G.Adj p0' u1) (_hq0'u2 : G.Adj q0' u2)
    (hnp0'u2 : ¬ G.Adj p0' u2) (hnp0'z : ¬ G.Adj p0' z) (hnq0'z : ¬ G.Adj q0' z)
    (hr'u1 : G.Adj r' u1) (hnr'u2 : ¬ G.Adj r' u2) : False := by
  have hnotS6 : ∀ v ∈ R, ∀ s ∈ S6, v ≠ s := fun v hv s hs e => hdisj v hv (e ▸ hs)
  have hw_card1 : (((G.neighborFinset w).erase p0').erase q0').card = 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hp0q0'.symm, (G.mem_neighborFinset w q0').mpr hwq0'⟩),
      Finset.card_erase_of_mem ((G.mem_neighborFinset w p0').mpr hwp0'),
      card_neighborFinset_eq_degree, hdeg w]
  obtain ⟨tw, htw_eq⟩ := Finset.card_eq_one.mp hw_card1
  have htw_mem : tw ∈ ((G.neighborFinset w).erase p0').erase q0' := by rw [htw_eq]; simp
  have ⟨htwq0', htw1⟩ := Finset.mem_erase.mp htw_mem
  have ⟨htwp0', htwN⟩ := Finset.mem_erase.mp htw1
  have hwtw : G.Adj w tw := (G.mem_neighborFinset w tw).mp htwN
  have htw_in : tw = u1 ∨ tw = u2 ∨ tw = z := by
    have h := hw_nb_sub w hwR htwN
    rw [← h3eq, hReq] at h
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with (h' | h' | h') | (h' | h' | h' | h')
    · exact absurd h' htwp0'
    · exact absurd h' htwq0'
    · rw [h'] at hwtw; exact absurd hwtw hnwr'
    · rw [h'] at hwtw; exact absurd hwtw (G.loopless.irrefl w)
    · exact Or.inl h'
    · exact Or.inr (Or.inl h')
    · exact Or.inr (Or.inr h')
  rcases htw_in with htw_e | htw_e | htw_e
  · -- w ~ u1: w and u1 are saturated, leaving u2 with degree ≤ 2
    rw [htw_e] at hwtw htw_eq
    have hnw_u2 : ¬ G.Adj w u2 := fun h => by
      have : u2 ∈ ((G.neighborFinset w).erase p0').erase q0' :=
        Finset.mem_erase.mpr ⟨hnotS6 u2 hu2R q0' hq0'S, Finset.mem_erase.mpr ⟨hnotS6 u2 hu2R p0' hp0'S,
          (G.mem_neighborFinset w u2).mpr h⟩⟩
      rw [htw_eq, Finset.mem_singleton] at this; exact hu12 this.symm
    have hnu1_u2 : ¬ G.Adj u1 u2 := fun h => by
      have hsub4 : ({p0', r', w, u2} : Finset V) ⊆ G.neighborFinset u1 := by
        intro t ht; simp only [Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with e | e | e | e <;> rw [e]
        · exact (G.mem_neighborFinset u1 p0').mpr hp0'u1.symm
        · exact (G.mem_neighborFinset u1 r').mpr hr'u1.symm
        · exact (G.mem_neighborFinset u1 w).mpr hwtw.symm
        · exact (G.mem_neighborFinset u1 u2).mpr h
      have h4 : ({p0', r', w, u2} : Finset V).card = 4 := by
        rw [Finset.card_insert_of_notMem (by simp [hp0r', (hnotS6 w hwR p0' hp0'S).symm, (hnotS6 u2 hu2R p0' hp0'S).symm]),
          Finset.card_insert_of_notMem (by simp [(hnotS6 w hwR r' hr'S).symm, (hnotS6 u2 hu2R r' hr'S).symm]),
          Finset.card_pair hu2w.symm]
      have hc := Finset.card_le_card hsub4
      rw [card_neighborFinset_eq_degree, hdeg u1, h4] at hc; omega
    have hu2_sub : G.neighborFinset u2 ⊆ {q0', z} := by
      intro t ht
      have hu2t := (G.mem_neighborFinset u2 t).mp ht
      have h := hw_nb_sub u2 hu2R ht
      rw [← h3eq, hReq] at h
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at h ⊢
      rcases h with (e | e | e) | (e | e | e | e)
      · rw [e] at hu2t; exact absurd hu2t.symm hnp0'u2
      · exact Or.inl e
      · rw [e] at hu2t; exact absurd hu2t.symm hnr'u2
      · rw [e] at hu2t; exact absurd hu2t.symm hnw_u2
      · rw [e] at hu2t; exact absurd hu2t.symm hnu1_u2
      · rw [e] at hu2t; exact absurd hu2t (G.loopless.irrefl u2)
      · exact Or.inr e
    have hc := Finset.card_le_card hu2_sub
    rw [card_neighborFinset_eq_degree, hdeg u2] at hc
    have := Finset.card_le_two (a := q0') (b := z)
    omega
  · -- w ~ u2: z ~ r', u1, u2 giving C8: p0 - p0' - u1 - z - u2 - w - q0' - q0 - p0
    rw [htw_e] at hwtw htw_eq
    have hnw_z : ¬ G.Adj w z := fun h => by
      have : z ∈ ((G.neighborFinset w).erase p0').erase q0' :=
        Finset.mem_erase.mpr ⟨hnotS6 z hzR q0' hq0'S, Finset.mem_erase.mpr ⟨hnotS6 z hzR p0' hp0'S,
          (G.mem_neighborFinset w z).mpr h⟩⟩
      rw [htw_eq, Finset.mem_singleton] at this; exact hu2z this.symm
    have hz_sub : G.neighborFinset z ⊆ {r', u1, u2} := by
      intro t ht
      have hzt := (G.mem_neighborFinset z t).mp ht
      have h := hw_nb_sub z hzR ht
      rw [← h3eq, hReq] at h
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at h ⊢
      rcases h with (e | e | e) | (e | e | e | e)
      · rw [e] at hzt; exact absurd hzt.symm hnp0'z
      · rw [e] at hzt; exact absurd hzt.symm hnq0'z
      · exact Or.inl e
      · rw [e] at hzt; exact absurd hzt.symm hnw_z
      · exact Or.inr (Or.inl e)
      · exact Or.inr (Or.inr e)
      · rw [e] at hzt; exact absurd hzt (G.loopless.irrefl z)
    have hcard3 : ({r', u1, u2} : Finset V).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [(hnotS6 u1 hu1R r' hr'S).symm, (hnotS6 u2 hu2R r' hr'S).symm]),
        Finset.card_pair hu12]
    have hz_eq3 := Finset.eq_of_subset_of_card_le hz_sub
      (by rw [card_neighborFinset_eq_degree, hdeg z, hcard3])
    have hzu1 : G.Adj z u1 := (G.mem_neighborFinset z u1).mp (by rw [hz_eq3]; simp)
    have hzu2 : G.Adj z u2 := (G.mem_neighborFinset z u2).mp (by rw [hz_eq3]; simp)
    apply hc8
    apply copy_eight G p0 p0' u1 z u2 w q0' q0
      hp0p0' hp0'u1 hzu1.symm hzu2 hwtw.symm hwq0' hq0q0'.symm hp0q0.symm
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, not_false_eq_true, and_true]
    refine ⟨⟨G.ne_of_adj hp0p0', (hnotS6 u1 hu1R p0 hp0S).symm, (hnotS6 z hzR p0 hp0S).symm,
        (hnotS6 u2 hu2R p0 hp0S).symm, (hnotS6 w hwR p0 hp0S).symm, hp0q0'_ne, G.ne_of_adj hp0q0⟩,
      ⟨(hnotS6 u1 hu1R p0' hp0'S).symm, (hnotS6 z hzR p0' hp0'S).symm,
        (hnotS6 u2 hu2R p0' hp0'S).symm, (hnotS6 w hwR p0' hp0'S).symm, hp0q0', hq0p0'_ne.symm⟩,
      ⟨hu1z, hu12, hu1w, hnotS6 u1 hu1R q0' hq0'S, hnotS6 u1 hu1R q0 hq0S⟩,
      ⟨hu2z.symm, hzw, hnotS6 z hzR q0' hq0'S, hnotS6 z hzR q0 hq0S⟩,
      ⟨hu2w, hnotS6 u2 hu2R q0' hq0'S, hnotS6 u2 hu2R q0 hq0S⟩,
      ⟨hnotS6 w hwR q0' hq0'S, hnotS6 w hwR q0 hq0S⟩,
      (G.ne_of_adj hq0q0').symm⟩
  · -- w ~ z: u2 ~ q0', u1, z giving C8: p0 - p0' - u1 - u2 - z - w - q0' - q0 - p0
    rw [htw_e] at hwtw htw_eq
    have hnw_u2 : ¬ G.Adj w u2 := fun h => by
      have : u2 ∈ ((G.neighborFinset w).erase p0').erase q0' :=
        Finset.mem_erase.mpr ⟨hnotS6 u2 hu2R q0' hq0'S, Finset.mem_erase.mpr ⟨hnotS6 u2 hu2R p0' hp0'S,
          (G.mem_neighborFinset w u2).mpr h⟩⟩
      rw [htw_eq, Finset.mem_singleton] at this; exact hu2z this
    have hu2_sub : G.neighborFinset u2 ⊆ {q0', u1, z} := by
      intro t ht
      have hu2t := (G.mem_neighborFinset u2 t).mp ht
      have h := hw_nb_sub u2 hu2R ht
      rw [← h3eq, hReq] at h
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at h ⊢
      rcases h with (e | e | e) | (e | e | e | e)
      · rw [e] at hu2t; exact absurd hu2t.symm hnp0'u2
      · exact Or.inl e
      · rw [e] at hu2t; exact absurd hu2t.symm hnr'u2
      · rw [e] at hu2t; exact absurd hu2t.symm hnw_u2
      · exact Or.inr (Or.inl e)
      · rw [e] at hu2t; exact absurd hu2t (G.loopless.irrefl u2)
      · exact Or.inr (Or.inr e)
    have hcard3 : ({q0', u1, z} : Finset V).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [(hnotS6 u1 hu1R q0' hq0'S).symm, (hnotS6 z hzR q0' hq0'S).symm]),
        Finset.card_pair hu1z]
    have hu2_eq3 := Finset.eq_of_subset_of_card_le hu2_sub
      (by rw [card_neighborFinset_eq_degree, hdeg u2, hcard3])
    have hu2u1 : G.Adj u2 u1 := (G.mem_neighborFinset u2 u1).mp (by rw [hu2_eq3]; simp)
    have hu2z_adj : G.Adj u2 z := (G.mem_neighborFinset u2 z).mp (by rw [hu2_eq3]; simp)
    apply hc8
    apply copy_eight G p0 p0' u1 u2 z w q0' q0
      hp0p0' hp0'u1 hu2u1.symm hu2z_adj hwtw.symm hwq0' hq0q0'.symm hp0q0.symm
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, not_false_eq_true, and_true]
    refine ⟨⟨G.ne_of_adj hp0p0', (hnotS6 u1 hu1R p0 hp0S).symm, (hnotS6 u2 hu2R p0 hp0S).symm,
        (hnotS6 z hzR p0 hp0S).symm, (hnotS6 w hwR p0 hp0S).symm, hp0q0'_ne, G.ne_of_adj hp0q0⟩,
      ⟨(hnotS6 u1 hu1R p0' hp0'S).symm, (hnotS6 u2 hu2R p0' hp0'S).symm,
        (hnotS6 z hzR p0' hp0'S).symm, (hnotS6 w hwR p0' hp0'S).symm, hp0q0', hq0p0'_ne.symm⟩,
      ⟨hu12, hu1z, hu1w, hnotS6 u1 hu1R q0' hq0'S, hnotS6 u1 hu1R q0 hq0S⟩,
      ⟨hu2z, hu2w, hnotS6 u2 hu2R q0' hq0'S, hnotS6 u2 hu2R q0 hq0S⟩,
      ⟨hzw, hnotS6 z hzR q0' hq0'S, hnotS6 z hzR q0 hq0S⟩,
      ⟨hnotS6 w hwR q0' hq0'S, hnotS6 w hwR q0 hq0S⟩,
      (G.ne_of_adj hq0q0').symm⟩

private lemma tri10_kill_deg2 {V : Type} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hdeg : ∀ x, G.degree x = 3)
    (hc4 : ¬ cycleGraph 4 ⊑ G) (hc8 : ¬ cycleGraph 8 ⊑ G)
    {S6 R : Finset V} {a' b' c' p q r p' q' r' w : V}
    (hR4 : R.card = 4) (hdisj : ∀ v ∈ R, v ∉ S6)
    (hw_nb_sub : ∀ v ∈ R, G.neighborFinset v ⊆ {a', b', c'} ∪ R)
    (hpq : G.Adj p q) (hpp' : G.Adj p p') (hqq' : G.Adj q q') (hrr' : G.Adj r r')
    (hpq' : p' ≠ q') (hpr' : p' ≠ r') (hqr' : q' ≠ r') (hpq'_ne : p ≠ q') (hqp'_ne : q ≠ p')
    (hpS : p ∈ S6) (hqS : q ∈ S6) (hrS : r ∈ S6) (hp'S : p' ∈ S6) (hq'S : q' ∈ S6) (hr'S : r' ∈ S6)
    (h3eq : ({p', q', r'} : Finset V) = {a', b', c'})
    (hp'R : (G.neighborFinset p').erase p ⊆ R)
    (hq'R : (G.neighborFinset q').erase q ⊆ R)
    (hr'R : (G.neighborFinset r').erase r ⊆ R)
    (hwR : w ∈ R) (hwp' : G.Adj w p') (hwq' : G.Adj w q') (hnwr' : ¬ G.Adj w r') : False := by
  have hx_card : (((G.neighborFinset p').erase p).erase w).card = 1 := by
    have hwp : w ≠ p := fun e => hdisj w hwR (e ▸ hpS)
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hwp, (G.mem_neighborFinset p' w).mpr hwp'.symm⟩),
      Finset.card_erase_of_mem ((G.mem_neighborFinset p' p).mpr hpp'.symm),
      card_neighborFinset_eq_degree, hdeg p']
  obtain ⟨x, hx_eq⟩ := Finset.card_eq_one.mp hx_card
  have ⟨hxw, hx_er⟩ := Finset.mem_erase.mp (show x ∈ ((G.neighborFinset p').erase p).erase w by rw [hx_eq]; simp)
  have hxR : x ∈ R := hp'R hx_er
  have hp'x : G.Adj p' x := (G.mem_neighborFinset p' x).mp (Finset.mem_of_mem_erase hx_er)
  have hy_card : (((G.neighborFinset q').erase q).erase w).card = 1 := by
    have hwq : w ≠ q := fun e => hdisj w hwR (e ▸ hqS)
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hwq, (G.mem_neighborFinset q' w).mpr hwq'.symm⟩),
      Finset.card_erase_of_mem ((G.mem_neighborFinset q' q).mpr hqq'.symm),
      card_neighborFinset_eq_degree, hdeg q']
  obtain ⟨y, hy_eq⟩ := Finset.card_eq_one.mp hy_card
  have ⟨hyw, hy_er⟩ := Finset.mem_erase.mp (show y ∈ ((G.neighborFinset q').erase q).erase w by rw [hy_eq]; simp)
  have hyR : y ∈ R := hq'R hy_er
  have hq'y : G.Adj q' y := (G.mem_neighborFinset q' y).mp (Finset.mem_of_mem_erase hy_er)
  have hxy : x ≠ y := by
    intro h; rw [← h] at hq'y
    rcases no_c4_of_not_copy hc4 hwp' hp'x hq'y.symm hwq'.symm with h1 | h1
    · exact hxw.symm h1
    · exact hpq' h1
  have hR_er_card : (((R.erase w).erase x).erase y).card = 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hxy.symm, Finset.mem_erase.mpr ⟨hyw, hyR⟩⟩),
      Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hxw, hxR⟩),
      Finset.card_erase_of_mem hwR, hR4]
  obtain ⟨z, hz_eq⟩ := Finset.card_eq_one.mp hR_er_card
  have ⟨hzy, hz1⟩ := Finset.mem_erase.mp (show z ∈ ((R.erase w).erase x).erase y by rw [hz_eq]; simp)
  have ⟨hzx, hz2⟩ := Finset.mem_erase.mp hz1
  have ⟨hzw, hzR⟩ := Finset.mem_erase.mp hz2
  have hReq : R = {w, x, y, z} := by
    rw [← Finset.insert_erase hwR,
      ← Finset.insert_erase (Finset.mem_erase.mpr ⟨hxw, hxR⟩),
      ← Finset.insert_erase (Finset.mem_erase.mpr ⟨hxy.symm, Finset.mem_erase.mpr ⟨hyw, hyR⟩⟩),
      hz_eq]
  have hnp'y : ¬ G.Adj p' y := fun h => by
    have hy_in : y ∈ ((G.neighborFinset p').erase p).erase w :=
      Finset.mem_erase.mpr ⟨hyw, Finset.mem_erase.mpr ⟨fun e => hdisj y hyR (e ▸ hpS),
        (G.mem_neighborFinset p' y).mpr h⟩⟩
    rw [hx_eq, Finset.mem_singleton] at hy_in; exact hxy hy_in.symm
  have hnp'z : ¬ G.Adj p' z := fun h => by
    have hz_in : z ∈ ((G.neighborFinset p').erase p).erase w :=
      Finset.mem_erase.mpr ⟨hzw, Finset.mem_erase.mpr ⟨fun e => hdisj z hzR (e ▸ hpS),
        (G.mem_neighborFinset p' z).mpr h⟩⟩
    rw [hx_eq, Finset.mem_singleton] at hz_in; exact hzx hz_in
  have hnq'x : ¬ G.Adj q' x := fun h => by
    have hx_in : x ∈ ((G.neighborFinset q').erase q).erase w :=
      Finset.mem_erase.mpr ⟨hxw, Finset.mem_erase.mpr ⟨fun e => hdisj x hxR (e ▸ hqS),
        (G.mem_neighborFinset q' x).mpr h⟩⟩
    rw [hy_eq, Finset.mem_singleton] at hx_in; exact hxy hx_in
  have hnq'z : ¬ G.Adj q' z := fun h => by
    have hz_in : z ∈ ((G.neighborFinset q').erase q).erase w :=
      Finset.mem_erase.mpr ⟨hzw, Finset.mem_erase.mpr ⟨fun e => hdisj z hzR (e ▸ hqS),
        (G.mem_neighborFinset q' z).mpr h⟩⟩
    rw [hy_eq, Finset.mem_singleton] at hz_in; exact hzy hz_in
  have hr'_sub : (G.neighborFinset r').erase r ⊆ {x, y, z} := by
    intro t ht
    have htR : t ∈ R := hr'R ht
    rw [hReq] at htR
    simp only [Finset.mem_insert, Finset.mem_singleton] at htR ⊢
    rcases htR with h | h | h | h
    · exfalso; rw [h] at ht; exact hnwr' ((G.mem_neighborFinset r' w).mp (Finset.mem_of_mem_erase ht)).symm
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  have hr'_card2 : ((G.neighborFinset r').erase r).card = 2 := by
    rw [Finset.card_erase_of_mem ((G.mem_neighborFinset r' r).mpr hrr'.symm),
      card_neighborFinset_eq_degree, hdeg r']
  by_cases hrx : G.Adj r' x
  · by_cases hrz : G.Adj r' z
    · have hnry : ¬ G.Adj r' y := fun h => by
        have hsub3 : ({x, y, z} : Finset V) ⊆ (G.neighborFinset r').erase r := by
          intro t ht; simp only [Finset.mem_insert, Finset.mem_singleton] at ht
          rcases ht with e | e | e <;> rw [e]
          · exact Finset.mem_erase.mpr ⟨fun h' => hdisj x hxR (h' ▸ hrS), (G.mem_neighborFinset r' x).mpr hrx⟩
          · exact Finset.mem_erase.mpr ⟨fun h' => hdisj y hyR (h' ▸ hrS), (G.mem_neighborFinset r' y).mpr h⟩
          · exact Finset.mem_erase.mpr ⟨fun h' => hdisj z hzR (h' ▸ hrS), (G.mem_neighborFinset r' z).mpr hrz⟩
        have h3 : ({x, y, z} : Finset V).card = 3 := by
          rw [Finset.card_insert_of_notMem (by simp [hxy, hzx.symm]), Finset.card_pair hzy.symm]
        have := Finset.card_le_card hsub3; omega
      exact tri10_finish_rz G hdeg hc8 hdisj hw_nb_sub hpq hpp' hqq' hpS hqS hp'S hq'S hr'S
        hpq' hpr' hpq'_ne hqp'_ne h3eq hwR hxR hyR hzR hxw hyw hzw hxy hzx.symm hzy.symm hReq
        hwp' hwq' hnwr' hp'x hq'y hnp'y hnp'z hnq'z hrx hnry
    · -- z has no neighbors in {p', q', r'}, so z ~ w, x, y → C4: p' - w - z - x - p'
      have hz_sub : G.neighborFinset z ⊆ {w, x, y} := by
        intro t ht
        have hzt := (G.mem_neighborFinset z t).mp ht
        have h := hw_nb_sub z hzR ht
        rw [← h3eq, hReq] at h
        simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at h ⊢
        rcases h with (e | e | e) | (e | e | e | e)
        · rw [e] at hzt; exact absurd hzt.symm hnp'z
        · rw [e] at hzt; exact absurd hzt.symm hnq'z
        · rw [e] at hzt; exact absurd hzt.symm hrz
        · exact Or.inl e
        · exact Or.inr (Or.inl e)
        · exact Or.inr (Or.inr e)
        · rw [e] at hzt; exact absurd hzt (G.loopless.irrefl z)
      have hcard3 : ({w, x, y} : Finset V).card = 3 := by
        rw [Finset.card_insert_of_notMem (by simp [hxw.symm, hyw.symm]), Finset.card_pair hxy]
      have hz_eq3 := Finset.eq_of_subset_of_card_le hz_sub
        (by rw [card_neighborFinset_eq_degree, hdeg z, hcard3])
      have hzw_adj : G.Adj z w := (G.mem_neighborFinset z w).mp (by rw [hz_eq3]; simp)
      have hzx_adj : G.Adj z x := (G.mem_neighborFinset z x).mp (by rw [hz_eq3]; simp)
      rcases no_c4_of_not_copy hc4 hwp' hp'x hzx_adj.symm hzw_adj with h1 | h1
      · exact hxw.symm h1
      · exact hdisj z hzR (h1 ▸ hp'S)
  · have hr'_sub2 : (G.neighborFinset r').erase r ⊆ {y, z} := by
      intro t ht
      have h3 := hr'_sub ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at h3 ⊢
      rcases h3 with e | e | e
      · rw [e] at ht; exact absurd ((G.mem_neighborFinset r' x).mp (Finset.mem_of_mem_erase ht)) hrx
      · exact Or.inl e
      · exact Or.inr e
    have hr'_eq2 := Finset.eq_of_subset_of_card_le hr'_sub2
      (by rw [hr'_card2, Finset.card_pair hzy.symm])
    have hry : G.Adj r' y := (G.mem_neighborFinset r' y).mp (Finset.mem_of_mem_erase (by rw [hr'_eq2]; simp))
    have h3eq_sw : ({q', p', r'} : Finset V) = {a', b', c'} := by
      rw [← h3eq, Finset.insert_comm q' p' {r'}]
    have hReq_sw : R = {w, y, x, z} := by
      rw [hReq, Finset.insert_comm x y {z}]
    exact tri10_finish_rz G hdeg hc8 hdisj hw_nb_sub hpq.symm hqq' hpp' hqS hpS hq'S hp'S hr'S
      hpq'.symm hqr' hqp'_ne hpq'_ne h3eq_sw hwR hyR hxR hzR hyw hxw hzw hxy.symm hzy.symm hzx.symm hReq_sw
      hwq' hwp' hnwr' hq'y hp'x hnq'x hnq'z hnp'z hry hrx

/- ### Part 4: Order lower bound |V| ≥ 12 for cubic C4-free C8-free graphs with a triangle -/

private lemma cubic_tri_card_ge_12 {V : Type} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hdeg : ∀ x, G.degree x = 3)
    (hc4 : ¬ cycleGraph 4 ⊑ G) (hc8 : ¬ cycleGraph 8 ⊑ G)
    (htri : ∃ a b c : V, G.Adj a b ∧ G.Adj b c ∧ G.Adj c a) :
    12 ≤ Fintype.card V := by
  obtain ⟨a, b, c, hab, hbc, hca⟩ := htri
  have hab_ne : a ≠ b := G.ne_of_adj hab
  have hbc_ne : b ≠ c := G.ne_of_adj hbc
  have hca_ne : c ≠ a := G.ne_of_adj hca
  have hout : ∀ {x y z : V}, G.Adj x y → G.Adj y z → G.Adj z x →
      ∃! x' : V, G.Adj x x' ∧ x' ≠ y ∧ x' ≠ z := by
    intro x y z hxy hyz hzx
    have hcard1 : (((G.neighborFinset x).erase y).erase z).card = 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨(G.ne_of_adj hyz).symm,
            (G.mem_neighborFinset x z).mpr hzx.symm⟩),
        Finset.card_erase_of_mem ((G.mem_neighborFinset x y).mpr hxy),
        card_neighborFinset_eq_degree, hdeg x]
    obtain ⟨x', hx'_eq⟩ := Finset.card_eq_one.mp hcard1
    have hx'_mem : x' ∈ ((G.neighborFinset x).erase y).erase z := by rw [hx'_eq]; simp
    have ⟨hx'z, hx'1⟩ := Finset.mem_erase.mp hx'_mem
    have ⟨hx'y, hx'N⟩ := Finset.mem_erase.mp hx'1
    refine ⟨x', ⟨(G.mem_neighborFinset x x').mp hx'N, hx'y, hx'z⟩, ?_⟩
    intro w ⟨hxw, hwy, hwz⟩
    have hw_mem : w ∈ ((G.neighborFinset x).erase y).erase z :=
      Finset.mem_erase.mpr ⟨hwz, Finset.mem_erase.mpr ⟨hwy, (G.mem_neighborFinset x w).mpr hxw⟩⟩
    rw [hx'_eq, Finset.mem_singleton] at hw_mem
    exact hw_mem
  obtain ⟨a', ⟨haa', ha'b, ha'c⟩, ha'_uniq⟩ := hout hab hbc hca
  obtain ⟨b', ⟨hbb', hb'c, hb'a⟩, hb'_uniq⟩ := hout hbc hca hab
  obtain ⟨c', ⟨hcc', hc'a, hc'b⟩, hc'_uniq⟩ := hout hca hab hbc
  have ha'_ne_b' : a' ≠ b' := by
    intro h; rw [← h] at hbb'
    rcases no_c4_of_not_copy hc4 hca.symm hbc.symm hbb' haa'.symm with h1 | h1
    · exact hab_ne h1
    · exact ha'c.symm h1
  have ha'_ne_c' : a' ≠ c' := by
    intro h; rw [← h] at hcc'
    rcases no_c4_of_not_copy hc4 hab hbc hcc' haa'.symm with h1 | h1
    · exact hca_ne.symm h1
    · exact ha'b.symm h1
  have hb'_ne_c' : b' ≠ c' := by
    intro h; rw [← h] at hcc'
    rcases no_c4_of_not_copy hc4 hab.symm hca.symm hcc' hbb'.symm with h1 | h1
    · exact hbc_ne h1
    · exact hb'a.symm h1
  have ha'b'_nadj : ¬ G.Adj a' b' := fun h => by
    rcases no_c4_of_not_copy hc4 hab hbb' h.symm haa'.symm with h1 | h1
    · exact hb'a.symm h1
    · exact ha'b.symm h1
  have hb'c'_nadj : ¬ G.Adj b' c' := fun h => by
    rcases no_c4_of_not_copy hc4 hbc hcc' h.symm hbb'.symm with h1 | h1
    · exact hc'b.symm h1
    · exact hb'c.symm h1
  have hc'a'_nadj : ¬ G.Adj c' a' := fun h => by
    rcases no_c4_of_not_copy hc4 hca haa' h.symm hcc'.symm with h1 | h1
    · exact ha'c.symm h1
    · exact hc'a.symm h1
  have h6_nd : ([a, b, c, a', b', c'] : List V).Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, not_false_eq_true, and_true]
    refine ⟨⟨hab_ne, hca_ne.symm, G.ne_of_adj haa', hb'a.symm, hc'a.symm⟩,
      ⟨hbc_ne, ha'b.symm, G.ne_of_adj hbb', hc'b.symm⟩,
      ⟨ha'c.symm, hb'c.symm, G.ne_of_adj hcc'⟩,
      ⟨ha'_ne_b', ha'_ne_c'⟩, hb'_ne_c'⟩
  let S6 : Finset V := [a, b, c, a', b', c'].toFinset
  have hS6_card : S6.card = 6 := by rw [List.toFinset_card_of_nodup h6_nd]; rfl
  let R : Finset V := Finset.univ \ S6
  -- For any x ∈ {a', b', c'}, its 2 neighbors besides its triangle vertex lie inside R
  have hnb_in_R : ∀ {x t : V},
      G.Adj t x → (t = a ∧ x = a' ∨ t = b ∧ x = b' ∨ t = c ∧ x = c') →
      (G.neighborFinset x).erase t ⊆ R := by
    intro x t _ htx_eq w hw
    have ⟨hwt, hwN⟩ := Finset.mem_erase.mp hw
    have hxw := (G.mem_neighborFinset x w).mp hwN
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
    intro hwS6
    simp only [S6, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hwS6
    rcases htx_eq with ⟨ht, hx⟩ | ⟨ht, hx⟩ | ⟨ht, hx⟩
    · rw [ht] at hwt; rw [hx] at hxw
      rcases hwS6 with h | h | h | h | h | h
      · exact hwt h
      · rw [h] at hxw; exact ha'_ne_b' (hb'_uniq a' ⟨hxw.symm, ha'c, (G.ne_of_adj haa').symm⟩)
      · rw [h] at hxw; exact ha'_ne_c' (hc'_uniq a' ⟨hxw.symm, (G.ne_of_adj haa').symm, ha'b⟩)
      · rw [h] at hxw; exact G.loopless.irrefl a' hxw
      · rw [h] at hxw; exact ha'b'_nadj hxw
      · rw [h] at hxw; exact hc'a'_nadj hxw.symm
    · rw [ht] at hwt; rw [hx] at hxw
      rcases hwS6 with h | h | h | h | h | h
      · rw [h] at hxw; exact ha'_ne_b'.symm (ha'_uniq b' ⟨hxw.symm, (G.ne_of_adj hbb').symm, hb'c⟩)
      · exact hwt h
      · rw [h] at hxw; exact hb'_ne_c' (hc'_uniq b' ⟨hxw.symm, hb'a, (G.ne_of_adj hbb').symm⟩)
      · rw [h] at hxw; exact ha'b'_nadj hxw.symm
      · rw [h] at hxw; exact G.loopless.irrefl b' hxw
      · rw [h] at hxw; exact hb'c'_nadj hxw
    · rw [ht] at hwt; rw [hx] at hxw
      rcases hwS6 with h | h | h | h | h | h
      · rw [h] at hxw; exact ha'_ne_c'.symm (ha'_uniq c' ⟨hxw.symm, hc'b, (G.ne_of_adj hcc').symm⟩)
      · rw [h] at hxw; exact hb'_ne_c'.symm (hb'_uniq c' ⟨hxw.symm, (G.ne_of_adj hcc').symm, hc'a⟩)
      · exact hwt h
      · rw [h] at hxw; exact hc'a'_nadj hxw
      · rw [h] at hxw; exact hb'c'_nadj hxw.symm
      · rw [h] at hxw; exact G.loopless.irrefl c' hxw
  have ha'R_sub : (G.neighborFinset a').erase a ⊆ R := hnb_in_R haa' (Or.inl ⟨rfl, rfl⟩)
  have hb'R_sub : (G.neighborFinset b').erase b ⊆ R := hnb_in_R hbb' (Or.inr (Or.inl ⟨rfl, rfl⟩))
  have hc'R_sub : (G.neighborFinset c').erase c ⊆ R := hnb_in_R hcc' (Or.inr (Or.inr ⟨rfl, rfl⟩))
  have ha'R_card : ((G.neighborFinset a').erase a).card = 2 := by
    rw [Finset.card_erase_of_mem ((G.mem_neighborFinset a' a).mpr haa'.symm), card_neighborFinset_eq_degree, hdeg a']
  have hb'R_card : ((G.neighborFinset b').erase b).card = 2 := by
    rw [Finset.card_erase_of_mem ((G.mem_neighborFinset b' b).mpr hbb'.symm), card_neighborFinset_eq_degree, hdeg b']
  have hc'R_card : ((G.neighborFinset c').erase c).card = 2 := by
    rw [Finset.card_erase_of_mem ((G.mem_neighborFinset c' c).mpr hcc'.symm), card_neighborFinset_eq_degree, hdeg c']
  have hR_card_eq : R.card = Fintype.card V - 6 := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.subset_univ _), Finset.card_univ, hS6_card]
  have hge8 : 8 ≤ Fintype.card V := by
    have hle := Finset.card_le_card ha'R_sub
    have h6le := Finset.card_le_univ S6
    omega
  have hne8 : Fintype.card V ≠ 8 := by
    intro h8
    have hR2 : R.card = 2 := by omega
    have heq_a' : (G.neighborFinset a').erase a = R :=
      Finset.eq_of_subset_of_card_le ha'R_sub (by omega)
    have heq_b' : (G.neighborFinset b').erase b = R :=
      Finset.eq_of_subset_of_card_le hb'R_sub (by omega)
    obtain ⟨w1, w2, hw12, hReq⟩ := Finset.card_eq_two.mp hR2
    have ha'w1 : G.Adj a' w1 := (G.mem_neighborFinset a' w1).mp (Finset.mem_of_mem_erase (by rw [heq_a', hReq]; simp))
    have ha'w2 : G.Adj a' w2 := (G.mem_neighborFinset a' w2).mp (Finset.mem_of_mem_erase (by rw [heq_a', hReq]; simp))
    have hb'w1 : G.Adj b' w1 := (G.mem_neighborFinset b' w1).mp (Finset.mem_of_mem_erase (by rw [heq_b', hReq]; simp))
    have hb'w2 : G.Adj b' w2 := (G.mem_neighborFinset b' w2).mp (Finset.mem_of_mem_erase (by rw [heq_b', hReq]; simp))
    rcases no_c4_of_not_copy hc4 ha'w1 hb'w1.symm hb'w2 ha'w2.symm with h | h
    · exact ha'_ne_b' h
    · exact hw12 h
  have hne10 : Fintype.card V ≠ 10 := by
    intro h10
    have hR4 : R.card = 4 := by omega
    have hw_not_tri : ∀ w ∈ R, ¬ G.Adj w a ∧ ¬ G.Adj w b ∧ ¬ G.Adj w c := by
      intro w hw
      have hwS6 : w ∉ S6 := (Finset.mem_sdiff.mp hw).2
      refine ⟨?_, ?_, ?_⟩
      · intro hwa
        by_cases hwb : w = b
        · exact hwS6 (by rw [hwb]; simp [S6])
        · by_cases hwc : w = c
          · exact hwS6 (by rw [hwc]; simp [S6])
          · exact hwS6 (by rw [ha'_uniq w ⟨hwa.symm, hwb, hwc⟩]; simp [S6])
      · intro hwb
        by_cases hwc : w = c
        · exact hwS6 (by rw [hwc]; simp [S6])
        · by_cases hwa : w = a
          · exact hwS6 (by rw [hwa]; simp [S6])
          · exact hwS6 (by rw [hb'_uniq w ⟨hwb.symm, hwc, hwa⟩]; simp [S6])
      · intro hwc
        by_cases hwa : w = a
        · exact hwS6 (by rw [hwa]; simp [S6])
        · by_cases hwb : w = b
          · exact hwS6 (by rw [hwb]; simp [S6])
          · exact hwS6 (by rw [hc'_uniq w ⟨hwc.symm, hwa, hwb⟩]; simp [S6])
    have hw_nb_sub : ∀ w ∈ R, G.neighborFinset w ⊆ {a', b', c'} ∪ R := by
      intro w hw z hz
      have hwz := (G.mem_neighborFinset w z).mp hz
      by_cases hzS : z ∈ S6
      · simp only [S6, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hzS
        rcases hzS with h | h | h | h | h | h
        · rw [h] at hwz; exact absurd hwz (hw_not_tri w hw).1
        · rw [h] at hwz; exact absurd hwz (hw_not_tri w hw).2.1
        · rw [h] at hwz; exact absurd hwz (hw_not_tri w hw).2.2
        · exact Finset.mem_union_left _ (by simp [h])
        · exact Finset.mem_union_left _ (by simp [h])
        · exact Finset.mem_union_left _ (by simp [h])
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hzS⟩)
    -- Pigeonhole: some w ∈ R has ≥ 2 neighbors in {a', b', c'}
    let T3 : Finset V := {a', b', c'}
    have hsum6 : ∑ w ∈ R, (G.neighborFinset w ∩ T3).card = 6 := by
      calc ∑ w ∈ R, (G.neighborFinset w ∩ T3).card
          = ∑ w ∈ R, ∑ x ∈ T3, if G.Adj w x then 1 else 0 := by
            refine Finset.sum_congr rfl (fun w _ => ?_)
            rw [← Finset.card_filter]; congr 1; ext x
            simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset, Finset.mem_filter]; exact and_comm
        _ = ∑ x ∈ T3, ∑ w ∈ R, if G.Adj w x then 1 else 0 := Finset.sum_comm
        _ = ∑ x ∈ T3, (G.neighborFinset x ∩ R).card := by
            refine Finset.sum_congr rfl (fun x _ => ?_)
            rw [← Finset.card_filter]; congr 1; ext w
            simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset, Finset.mem_filter]
            rw [G.adj_comm]; exact and_comm
        _ = 6 := by
            have hT3_sum : ∑ x ∈ T3, (G.neighborFinset x ∩ R).card =
                (G.neighborFinset a' ∩ R).card + (G.neighborFinset b' ∩ R).card + (G.neighborFinset c' ∩ R).card := by
              rw [Finset.sum_insert (by simp [ha'_ne_b', ha'_ne_c']),
                Finset.sum_insert (by simp [hb'_ne_c']), Finset.sum_singleton]; ring
            have hca' : (G.neighborFinset a' ∩ R).card = 2 := by
              have : G.neighborFinset a' ∩ R = (G.neighborFinset a').erase a := by
                ext z; simp only [Finset.mem_inter, Finset.mem_erase]
                constructor
                · rintro ⟨hzN, hzR⟩; exact ⟨fun h => (Finset.mem_sdiff.mp hzR).2 (by rw [h]; simp [S6]), hzN⟩
                · intro h; exact ⟨h.2, ha'R_sub (Finset.mem_erase.mpr h)⟩
              rw [this, ha'R_card]
            have hcb' : (G.neighborFinset b' ∩ R).card = 2 := by
              have : G.neighborFinset b' ∩ R = (G.neighborFinset b').erase b := by
                ext z; simp only [Finset.mem_inter, Finset.mem_erase]
                constructor
                · rintro ⟨hzN, hzR⟩; exact ⟨fun h => (Finset.mem_sdiff.mp hzR).2 (by rw [h]; simp [S6]), hzN⟩
                · intro h; exact ⟨h.2, hb'R_sub (Finset.mem_erase.mpr h)⟩
              rw [this, hb'R_card]
            have hcc' : (G.neighborFinset c' ∩ R).card = 2 := by
              have : G.neighborFinset c' ∩ R = (G.neighborFinset c').erase c := by
                ext z; simp only [Finset.mem_inter, Finset.mem_erase]
                constructor
                · rintro ⟨hzN, hzR⟩; exact ⟨fun h => (Finset.mem_sdiff.mp hzR).2 (by rw [h]; simp [S6]), hzN⟩
                · intro h; exact ⟨h.2, hc'R_sub (Finset.mem_erase.mpr h)⟩
              rw [this, hc'R_card]
            rw [hT3_sum, hca', hcb', hcc']
    have hex_w2 : ∃ w ∈ R, 2 ≤ (G.neighborFinset w ∩ T3).card := by
      by_contra hno
      push Not at hno
      have hle4 : ∑ w ∈ R, (G.neighborFinset w ∩ T3).card ≤ 4 := by
        calc ∑ w ∈ R, (G.neighborFinset w ∩ T3).card
            ≤ ∑ _w ∈ R, 1 := Finset.sum_le_sum (fun w hw => by have := hno w hw; omega)
          _ = 4 := by rw [Finset.sum_const, smul_eq_mul, hR4, mul_one]
      omega
    obtain ⟨w, hwR, hw2⟩ := hex_w2
    by_cases hwa' : G.Adj w a'
    · by_cases hwb' : G.Adj w b'
      · by_cases hwc' : G.Adj w c'
        · -- Subcase 1: w ~ a', b', c'
          have hwa_ne : w ≠ a := fun e => (Finset.mem_sdiff.mp hwR).2 (by rw [e]; simp [S6])
          have hwb_ne : w ≠ b := fun e => (Finset.mem_sdiff.mp hwR).2 (by rw [e]; simp [S6])
          have hwc_ne : w ≠ c := fun e => (Finset.mem_sdiff.mp hwR).2 (by rw [e]; simp [S6])
          have hx_c : (((G.neighborFinset a').erase a).erase w).card = 1 := by
            rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hwa_ne, (G.mem_neighborFinset a' w).mpr hwa'.symm⟩), ha'R_card]
          have hy_c : (((G.neighborFinset b').erase b).erase w).card = 1 := by
            rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hwb_ne, (G.mem_neighborFinset b' w).mpr hwb'.symm⟩), hb'R_card]
          have hz_c : (((G.neighborFinset c').erase c).erase w).card = 1 := by
            rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hwc_ne, (G.mem_neighborFinset c' w).mpr hwc'.symm⟩), hc'R_card]
          obtain ⟨x, hx_eq⟩ := Finset.card_eq_one.mp hx_c
          obtain ⟨y, hy_eq⟩ := Finset.card_eq_one.mp hy_c
          obtain ⟨z, hz_eq⟩ := Finset.card_eq_one.mp hz_c
          have ⟨hxw, hx_er⟩ := Finset.mem_erase.mp (show x ∈ ((G.neighborFinset a').erase a).erase w by rw [hx_eq]; simp)
          have ⟨hyw, hy_er⟩ := Finset.mem_erase.mp (show y ∈ ((G.neighborFinset b').erase b).erase w by rw [hy_eq]; simp)
          have ⟨hzw, hz_er⟩ := Finset.mem_erase.mp (show z ∈ ((G.neighborFinset c').erase c).erase w by rw [hz_eq]; simp)
          have hxR : x ∈ R := ha'R_sub hx_er
          have hyR : y ∈ R := hb'R_sub hy_er
          have hzR : z ∈ R := hc'R_sub hz_er
          have ha'x : G.Adj a' x := (G.mem_neighborFinset a' x).mp (Finset.mem_of_mem_erase hx_er)
          have hb'y : G.Adj b' y := (G.mem_neighborFinset b' y).mp (Finset.mem_of_mem_erase hy_er)
          have hc'z : G.Adj c' z := (G.mem_neighborFinset c' z).mp (Finset.mem_of_mem_erase hz_er)
          have hxy : x ≠ y := fun e => by
            rw [← e] at hb'y
            rcases no_c4_of_not_copy hc4 hwa' ha'x hb'y.symm hwb'.symm with h1 | h1
            · exact hxw.symm h1
            · exact ha'_ne_b' h1
          have hxz : x ≠ z := fun e => by
            rw [← e] at hc'z
            rcases no_c4_of_not_copy hc4 hwa' ha'x hc'z.symm hwc'.symm with h1 | h1
            · exact hxw.symm h1
            · exact ha'_ne_c' h1
          have hyz : y ≠ z := fun e => by
            rw [← e] at hc'z
            rcases no_c4_of_not_copy hc4 hwb' hb'y hc'z.symm hwc'.symm with h1 | h1
            · exact hyw.symm h1
            · exact hb'_ne_c' h1
          have hReq : R = {w, x, y, z} := by
            have hsub4 : ({w, x, y, z} : Finset V) ⊆ R := by
              intro t ht; simp only [Finset.mem_insert, Finset.mem_singleton] at ht
              rcases ht with e | e | e | e <;> rw [e] <;> assumption
            have hcard4 : ({w, x, y, z} : Finset V).card = 4 := by
              rw [Finset.card_insert_of_notMem (by simp [hxw.symm, hyw.symm, hzw.symm]),
                Finset.card_insert_of_notMem (by simp [hxy, hxz]), Finset.card_pair hyz]
            exact (Finset.eq_of_subset_of_card_le hsub4 (by rw [hR4, hcard4])).symm
          -- x has no neighbor in {b', c', w}, so G.neighborFinset x ⊆ {a', y, z}, hence x ~ z!
          have hw_eq3 : G.neighborFinset w = {a', b', c'} := by
            have hsub : ({a', b', c'} : Finset V) ⊆ G.neighborFinset w := by
              intro t ht; simp only [Finset.mem_insert, Finset.mem_singleton] at ht
              rcases ht with e | e | e <;> rw [e]
              · exact (G.mem_neighborFinset w a').mpr hwa'
              · exact (G.mem_neighborFinset w b').mpr hwb'
              · exact (G.mem_neighborFinset w c').mpr hwc'
            have h3 : ({a', b', c'} : Finset V).card = 3 := by
              rw [Finset.card_insert_of_notMem (by simp [ha'_ne_b', ha'_ne_c']), Finset.card_pair hb'_ne_c']
            exact (Finset.eq_of_subset_of_card_le hsub (by rw [card_neighborFinset_eq_degree, hdeg w, h3])).symm
          have hx_sub : G.neighborFinset x ⊆ {a', y, z} := by
            intro t ht
            have hxt := (G.mem_neighborFinset x t).mp ht
            have h := hw_nb_sub x hxR ht
            rw [hReq] at h
            simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at h ⊢
            rcases h with (e | e | e) | (e | e | e | e)
            · exact Or.inl e
            · rw [e] at hxt
              have : x ∈ ((G.neighborFinset b').erase b).erase w :=
                Finset.mem_erase.mpr ⟨hxw, Finset.mem_erase.mpr ⟨fun h' => (Finset.mem_sdiff.mp hxR).2 (by rw [h']; simp [S6]),
                  (G.mem_neighborFinset b' x).mpr hxt.symm⟩⟩
              rw [hy_eq, Finset.mem_singleton] at this; exact absurd this hxy
            · rw [e] at hxt
              have : x ∈ ((G.neighborFinset c').erase c).erase w :=
                Finset.mem_erase.mpr ⟨hxw, Finset.mem_erase.mpr ⟨fun h' => (Finset.mem_sdiff.mp hxR).2 (by rw [h']; simp [S6]),
                  (G.mem_neighborFinset c' x).mpr hxt.symm⟩⟩
              rw [hz_eq, Finset.mem_singleton] at this; exact absurd this hxz
            · rw [e] at hxt
              have : x ∈ G.neighborFinset w := (G.mem_neighborFinset w x).mpr hxt.symm
              rw [hw_eq3] at this
              simp only [Finset.mem_insert, Finset.mem_singleton] at this
              rcases this with e' | e' | e' <;> exact absurd (by rw [e']; simp [S6] : x ∈ S6) (Finset.mem_sdiff.mp hxR).2
            · rw [e] at hxt; exact absurd hxt (G.loopless.irrefl x)
            · exact Or.inr (Or.inl e)
            · exact Or.inr (Or.inr e)
          have hnotS6 : ∀ v ∈ R, ∀ s ∈ S6, v ≠ s := fun v hv s hs e => (Finset.mem_sdiff.mp hv).2 (e ▸ hs)
          have hx_card3 : ({a', y, z} : Finset V).card = 3 := by
            rw [Finset.card_insert_of_notMem (by simp [(hnotS6 y hyR a' (by simp [S6])).symm,
              (hnotS6 z hzR a' (by simp [S6])).symm]), Finset.card_pair hyz]
          have hx_eq3 := Finset.eq_of_subset_of_card_le hx_sub
            (by rw [card_neighborFinset_eq_degree, hdeg x, hx_card3])
          have hxz_adj : G.Adj x z := (G.mem_neighborFinset x z).mp (by rw [hx_eq3]; simp)
          -- C8: a - a' - x - z - c' - w - b' - b - a
          apply hc8
          apply copy_eight G a a' x z c' w b' b
            haa' ha'x hxz_adj hc'z.symm hwc'.symm hwb' hbb'.symm hab.symm
          simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
            List.nodup_nil, not_false_eq_true, and_true]
          refine ⟨⟨G.ne_of_adj haa', (hnotS6 x hxR a (by simp [S6])).symm, (hnotS6 z hzR a (by simp [S6])).symm,
              hc'a.symm, (hnotS6 w hwR a (by simp [S6])).symm, hb'a.symm, hab_ne⟩,
            ⟨(hnotS6 x hxR a' (by simp [S6])).symm, (hnotS6 z hzR a' (by simp [S6])).symm,
              ha'_ne_c', (hnotS6 w hwR a' (by simp [S6])).symm, ha'_ne_b', ha'b⟩,
            ⟨hxz, hnotS6 x hxR c' (by simp [S6]), hxw, hnotS6 x hxR b' (by simp [S6]), hnotS6 x hxR b (by simp [S6])⟩,
            ⟨hnotS6 z hzR c' (by simp [S6]), hzw, hnotS6 z hzR b' (by simp [S6]), hnotS6 z hzR b (by simp [S6])⟩,
            ⟨(hnotS6 w hwR c' (by simp [S6])).symm, hb'_ne_c'.symm, hc'b⟩,
            ⟨hnotS6 w hwR b' (by simp [S6]), hnotS6 w hwR b (by simp [S6])⟩,
            (G.ne_of_adj hbb').symm⟩
        · exact tri10_kill_deg2 G hdeg hc4 hc8 hR4 (fun v hv => (Finset.mem_sdiff.mp hv).2) hw_nb_sub
            hab haa' hbb' hcc' ha'_ne_b' ha'_ne_c' hb'_ne_c' hb'a.symm ha'b.symm
            (by simp [S6]) (by simp [S6]) (by simp [S6]) (by simp [S6]) (by simp [S6]) (by simp [S6])
            rfl ha'R_sub hb'R_sub hc'R_sub hwR hwa' hwb' hwc'
      · have hwc' : G.Adj w c' := by
          by_contra hnc'
          have hsub1 : G.neighborFinset w ∩ T3 ⊆ {a'} := by
            intro t ht
            have ⟨htN, htT⟩ := Finset.mem_inter.mp ht
            have hwt := (G.mem_neighborFinset w t).mp htN
            simp only [T3, Finset.mem_insert, Finset.mem_singleton] at htT ⊢
            rcases htT with e | e | e
            · exact e
            · rw [e] at hwt; exact absurd hwt hwb'
            · rw [e] at hwt; exact absurd hwt hnc'
          have := Finset.card_le_card hsub1; rw [Finset.card_singleton] at this; omega
        exact tri10_kill_deg2 G hdeg hc4 hc8 hR4 (fun v hv => (Finset.mem_sdiff.mp hv).2) hw_nb_sub
          hca.symm haa' hcc' hbb' ha'_ne_c' ha'_ne_b' hb'_ne_c'.symm hc'a.symm ha'c.symm
          (by simp [S6]) (by simp [S6]) (by simp [S6]) (by simp [S6]) (by simp [S6]) (by simp [S6])
          (by rw [Finset.pair_comm c' b']) ha'R_sub hc'R_sub hb'R_sub hwR hwa' hwc' hwb'
    · have hwb'c' : G.Adj w b' ∧ G.Adj w c' := by
        have hsub2 : G.neighborFinset w ∩ T3 ⊆ {b', c'} := by
          intro t ht
          have ⟨htN, htT⟩ := Finset.mem_inter.mp ht
          have hwt := (G.mem_neighborFinset w t).mp htN
          simp only [T3, Finset.mem_insert, Finset.mem_singleton] at htT ⊢
          rcases htT with e | e | e
          · rw [e] at hwt; exact absurd hwt hwa'
          · exact Or.inl e
          · exact Or.inr e
        have heq2 := Finset.eq_of_subset_of_card_le hsub2
          (by rw [Finset.card_pair hb'_ne_c']; exact hw2)
        exact ⟨(G.mem_neighborFinset w b').mp (Finset.mem_inter.mp (show b' ∈ G.neighborFinset w ∩ T3 by rw [heq2]; simp)).1,
          (G.mem_neighborFinset w c').mp (Finset.mem_inter.mp (show c' ∈ G.neighborFinset w ∩ T3 by rw [heq2]; simp)).1⟩
      exact tri10_kill_deg2 G hdeg hc4 hc8 hR4 (fun v hv => (Finset.mem_sdiff.mp hv).2) hw_nb_sub
        hbc hbb' hcc' haa' hb'_ne_c' ha'_ne_b'.symm ha'_ne_c'.symm hc'b.symm hb'c.symm
        (by simp [S6]) (by simp [S6]) (by simp [S6]) (by simp [S6]) (by simp [S6]) (by simp [S6])
        (by rw [Finset.insert_comm b' c', Finset.pair_comm b' a', Finset.insert_comm c' a', Finset.pair_comm c' b'])
        hb'R_sub hc'R_sub ha'R_sub hwR hwb'c'.1 hwb'c'.2 hwa'
  have ⟨m, hm⟩ := even_card_of_cubic G hdeg
  omega

end Helpers

theorem main : H1 → H2 → H3 → OMA.R_Erdos64_erdos_64_R4.H1 := by
  intro h1 h2 h3 V G _ _ hconn hmin hnotvt hindep hcub_nb hc4 hc8
  by_cases hnoncub : ∃ v : V, 3 < G.degree v
  · have ⟨hle, heq_imp⟩ := two_thirds_cubic_bound G hmin hindep hcub_nb
    by_cases heq : 2 * Fintype.card V = 3 * (Finset.univ.filter (fun x : V => G.degree x = 3)).card
    · have ⟨hH4, hT2⟩ := heq_imp heq
      exact equality_four_regular_contraction G hnoncub hindep hc4 hc8
        (fun v hv => hH4 v (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩))
        (fun u hu => hT2 u (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu⟩)) h1
    · have hstrict : 2 * Fintype.card V < 3 * (Finset.univ.filter (fun x : V => G.degree x = 3)).card :=
        by omega
      have ⟨hball, hge10⟩ := noncubic_ball_bound G hmin hnoncub hc4
      exact h2 V G hconn hmin hnoncub hnotvt hindep hcub_nb hc4 hc8 hstrict hball hge10
  · push Not at hnoncub
    have hdeg : ∀ x : V, G.degree x = 3 := fun x => le_antisymm (hnoncub x) (hmin x)
    have heven : Even (Fintype.card V) := even_card_of_cubic G hdeg
    have hge12_and_tf : 12 ≤ Fintype.card V ∧
        ((∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a) → 14 ≤ Fintype.card V) := by
      by_cases htri : ∃ a b c : V, G.Adj a b ∧ G.Adj b c ∧ G.Adj c a
      · refine ⟨cubic_tri_card_ge_12 G hdeg hc4 hc8 htri, ?_⟩
        intro htf
        obtain ⟨a, b, c, hab, hbc, hca⟩ := htri
        exact absurd hca (htf a b c hab hbc)
      · push Not at htri
        have htf : ∀ a b c : V, G.Adj a b → G.Adj b c → ¬ G.Adj c a := htri
        have ⟨hge10, hne12⟩ := card_ge_ten_and_ne_twelve G hconn.nonempty hdeg htf hc4 hc8
        have hne10 : Fintype.card V ≠ 10 := fun h10 =>
          hnotvt (petersen_unique_vt G h10 hdeg htf hc4)
        obtain ⟨m, hm⟩ := heven
        exact ⟨by omega, fun _ => by omega⟩
    exact h3 V G hconn hdeg hnotvt hc4 hc8 heven hge12_and_tf.1 hge12_and_tf.2

end OMA.R_Erdos64_erdos_64_R4_H1_R1
