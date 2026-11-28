import OMAReductions.R_WrittenOnTheWallII_GraphConjecture40_conjecture40_R1_H2_R1
import Mathlib

/-!
# Reduction of the two-endpoint step `H1` (claim `S2`) of `WrittenOnTheWallII.GraphConjecture40.conjecture40.R1.H2.R1`

`S2`: in a connected bipartite graph `H` on `n` vertices, for any two vertices `x`, `y` of
different colours there is a path cover with at most `2 f - n - 1` paths in which `x` and `y`
are ends of their paths (`f` is the largest induced forest size, `p` the path cover number).

Proved here, with no hypothesis (induction on `n`, then on the number of edges):
* Bridges: if `ab` is a bridge with sides `K ∋ a` and `R ∋ b`, then `f(H) ≥ f(K) + f(R)` (putting a
  bridge back creates no cycle), and `S2` (or its one-cap or no-cap form) on each side, with the
  caps `x`, `y` wherever they lie, gives `S2` for `H`. One-vertex sides (leaves) and `K_2` included.
* Cut vertices: if `H` is bridgeless (so no vertex has degree one) and `H - w` is disconnected, let
  `K` be the component of `H - w` containing a neighbour `u` of `w` chosen so that `u` is not `x`
  or `y` and has the colour opposite to any cap in `K`, and `R` the other components. `S2` on `K`
  with caps `x`, `y`, `u`, its component form on `R`, and attaching `w` to the end `u` give `S2`
  for `H`, because both `K` and `R` contain an edge.
* Non-critical edges: if `f(H - e) ≤ f(H)` and `H - e` is connected, a cover of `H - e` is a cover
  of `H` with the same ends.
* Slack at least two (`p + n + 3 ≤ 2 f`): cut a minimum cover at `x` and at `y`.
* Peeling paths: let `q` be a path from `x` to `d` avoiding `y`, with `d` of the colour opposite
  to `x`, a neighbour `e` of `d` off `q`, and an edge off `q`. If `2 f(H - q) + |q| ≤ 2 f(H)`,
  a cover of `H - q` (component form) with caps `y`, `e`, extended by `q` through the edge `d e`,
  gives `S2`. The same at `y`.
* Feedback vertex number at most one (`f ≥ n - 1`): a tree, or four consecutive vertices of a cycle.
* Feedback vertex number two (`f = n - 2`): a six-vertex path, a four-vertex and a three-vertex path,
  or a Hamiltonian `x`-`y` path, found from cycles avoiding prescribed vertices (`s2t_small2`).

What is left, for 2-connected bipartite graphs that are bridgeless, in which deleting any edge
raises the forest number, and with `f ≤ n - 3`:
* `H1`: the bipartite case of Conjecture 40 there, `p + n + 1 ≤ 2 f`, for graphs with no
  peeling path at any pair (a peeling path at one pair already gives a cover of that size);
* `H2`: `S2` there when the slack is 0 or 1 (`p + n + 1 ≤ 2 f < p + n + 3`), for ends `x`, `y`
  at which no peeling path exists.
-/

namespace OMA.R_WrittenOnTheWallII_GraphConjecture40_conjecture40_R1_H2_R1_H1_R1

open SimpleGraph
open OMA.R_WrittenOnTheWallII_GraphConjecture40_conjecture40_R1_H2_R1 (nb0_cover_union
  nb0_forest_singleton nb0_cover_singleton nb0_cover_lift nb0_pick nb0_exists_forest_sub
  nb0_acyclic_union nb0_card_le_forest nb0_rb_refl nb0_rb_symm nb0_rb_trans nb0_rb_adj
  nb0_rb_mono nb0_comp_connected nb0_forest_superadd nb0_forest_le_G nb0_cover_extend
  nb0_mem_support_map)

/-- The bipartite case of Conjecture 40 for 2-connected bipartite graphs without bridges, in which
deleting any edge increases the largest induced forest, with feedback vertex number at least
three, and with no peeling path at all: for every two vertices `x`, `y` of different colours and
every path `q` from `x` avoiding `y`, ending at a vertex `d` of the other colour that has a
neighbour off `q`, with an edge off `q`, deleting `q` lowers `2 f` by less than its number of
vertices. -/
def H1 : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (H : SimpleGraph V) (c : V → Fin 2),
    (∀ u v, H.Adj u v → c u ≠ c v) → H.Connected →
    (∀ u v, H.Adj u v → (H.deleteEdges {s(u, v)}).Connected) →
    (∀ v : V, (H.induce ({v}ᶜ : Set V)).Connected) →
    (∀ u v, H.Adj u v →
      H.largestInducedForestSize < (H.deleteEdges {s(u, v)}).largestInducedForestSize) →
    H.largestInducedForestSize + 3 ≤ Fintype.card V →
    (∀ x y : V, c x ≠ c y →
      ∀ (d e : V) (q : H.Walk x d), q.IsPath → y ∉ q.support → c d ≠ c x → e ∉ q.support →
      H.Adj d e → (∃ a b, a ∉ q.support ∧ b ∉ q.support ∧ H.Adj a b) →
      2 * H.largestInducedForestSize <
        2 * (H.induce {z | z ∉ q.support}).largestInducedForestSize + q.length + 1) →
    H.pathCoverNumber + Fintype.card V + 1 ≤ 2 * H.largestInducedForestSize

/-- `S2` for the same class of graphs, when the slack `2 f - n - 1 - p` is 0 or 1, for prescribed
ends `x`, `y` at which no peeling path exists: for every path `q` from `x` avoiding `y`, ending at
a vertex `d` of the other colour that has a neighbour off `q`, with an edge off `q`, deleting `q`
lowers `2 f` by less than its number of vertices; and the same at `y`. -/
def H2 : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (H : SimpleGraph V) (c : V → Fin 2),
    (∀ u v, H.Adj u v → c u ≠ c v) → H.Connected →
    (∀ u v, H.Adj u v → (H.deleteEdges {s(u, v)}).Connected) →
    (∀ v : V, (H.induce ({v}ᶜ : Set V)).Connected) →
    (∀ u v, H.Adj u v →
      H.largestInducedForestSize < (H.deleteEdges {s(u, v)}).largestInducedForestSize) →
    H.largestInducedForestSize + 3 ≤ Fintype.card V →
    H.pathCoverNumber + Fintype.card V + 1 ≤ 2 * H.largestInducedForestSize →
    2 * H.largestInducedForestSize < H.pathCoverNumber + Fintype.card V + 3 →
    ∀ x y : V, c x ≠ c y →
    (∀ (d e : V) (q : H.Walk x d), q.IsPath → y ∉ q.support → c d ≠ c x → e ∉ q.support →
      H.Adj d e → (∃ a b, a ∉ q.support ∧ b ∉ q.support ∧ H.Adj a b) →
      2 * H.largestInducedForestSize <
        2 * (H.induce {z | z ∉ q.support}).largestInducedForestSize + q.length + 1) →
    (∀ (d e : V) (q : H.Walk y d), q.IsPath → x ∉ q.support → c d ≠ c y → e ∉ q.support →
      H.Adj d e → (∃ a b, a ∉ q.support ∧ b ∉ q.support ∧ H.Adj a b) →
      2 * H.largestInducedForestSize <
        2 * (H.induce {z | z ∉ q.support}).largestInducedForestSize + q.length + 1) →
    ∃ P : Finset (Finset V), H.IsPathCover P ∧
      (∀ s ∈ P, ∃ (u v : V) (q : H.Walk u v), q.IsPath ∧ s = q.support.toFinset ∧
        (x ∈ s → x = u ∨ x = v) ∧ (y ∈ s → y = u ∨ y = v)) ∧
      P.card + Fintype.card V + 1 ≤ 2 * H.largestInducedForestSize

section

variable {V : Type} [Fintype V] [DecidableEq V]

lemma good_of_cover (H : SimpleGraph V) (P : Finset (Finset V)) (hP : H.IsPathCover P) :
    ((∀ s1 ∈ P, ∀ s2 ∈ P, s1 ≠ s2 → Disjoint s1 s2) ∧ (Finset.univ ⊆ (P).biUnion id) ∧
    (∀ s ∈ P, ∃ (u v : V) (q : H.Walk u v), q.IsPath ∧ s = q.support.toFinset ∧
      ∀ t ∈ (∅ : Finset V), t ∈ s → t = u ∨ t = v)) := by
  obtain ⟨h1, h2, h3⟩ := hP
  refine ⟨h1, h2, ?_⟩
  intro s hs
  obtain ⟨u, v, q, hq, hsq⟩ := h3 s hs
  exact ⟨u, v, q, hq, hsq, fun t ht => absurd ht (Finset.notMem_empty t)⟩

/-- Splitting a path at `z` makes `z` an end and adds at most one path. -/
lemma good_split (H : SimpleGraph V) (P : Finset (Finset V)) (Z : Finset V)
    (hP : ((∀ s1 ∈ P, ∀ s2 ∈ P, s1 ≠ s2 → Disjoint s1 s2) ∧ (Finset.univ ⊆ (P).biUnion id) ∧
    (∀ s ∈ P, ∃ (u v : V) (q : H.Walk u v), q.IsPath ∧ s = q.support.toFinset ∧
      ∀ t ∈ Z, t ∈ s → t = u ∨ t = v))) (z : V) :
    ∃ P' : Finset (Finset V), ((∀ s1 ∈ P', ∀ s2 ∈ P', s1 ≠ s2 → Disjoint s1 s2) ∧ (Finset.univ ⊆ (P').biUnion id) ∧
    (∀ s ∈ P', ∃ (u v : V) (q : H.Walk u v), q.IsPath ∧ s = q.support.toFinset ∧
      ∀ t ∈ (insert z Z), t ∈ s → t = u ∨ t = v)) ∧ P'.card ≤ P.card + 1 := by
  obtain ⟨hd, hu, hw⟩ := hP
  have hzU : z ∈ P.biUnion id := hu (Finset.mem_univ z)
  obtain ⟨s0, hs0, hz0⟩ := Finset.mem_biUnion.mp hzU
  obtain ⟨u, v, q, hq, hs0eq, hZ⟩ := hw s0 hs0
  -- vertices of `z` lie in no other member
  have hother : ∀ s ∈ P, s ≠ s0 → z ∉ s := by
    intro s hs hne hzs
    exact Finset.disjoint_left.mp (hd s hs s0 hs0 hne) hzs hz0
  by_cases hend : z = u ∨ z = v
  · refine ⟨P, ⟨hd, hu, ?_⟩, by omega⟩
    intro s hs
    by_cases hss : s = s0
    · subst hss
      refine ⟨u, v, q, hq, hs0eq, ?_⟩
      intro t ht hts
      rcases Finset.mem_insert.mp ht with rfl | ht
      · exact hend
      · exact hZ t ht hts
    · obtain ⟨u', v', q', hq', hseq, hZ'⟩ := hw s hs
      refine ⟨u', v', q', hq', hseq, ?_⟩
      intro t ht hts
      rcases Finset.mem_insert.mp ht with rfl | ht
      · exact absurd hts (hother s hs hss)
      · exact hZ' t ht hts
  · push Not at hend
    have hzq : z ∈ q.support := by
      rw [hs0eq] at hz0
      exact List.mem_toFinset.mp hz0
    obtain ⟨w, hzw, r, hr⟩ := Walk.exists_eq_cons_of_ne hend.2 (q.dropUntil z hzq)
    have hspec := q.take_spec hzq
    have hsupp : q.support = (q.takeUntil z hzq).support ++ r.support := by
      conv_lhs => rw [← hspec]
      rw [Walk.support_append, hr, Walk.support_cons, List.tail_cons]
    have hnd : ((q.takeUntil z hzq).support ++ r.support).Nodup := by
      rw [← hsupp]; exact hq.support_nodup
    have hldisj := List.disjoint_of_nodup_append hnd
    have hq1 : (q.takeUntil z hzq).IsPath := hq.takeUntil hzq
    have hq2 : (Walk.cons hzw r).IsPath := by rw [← hr]; exact hq.dropUntil hzq
    have hr' : r.IsPath := ((Walk.cons_isPath_iff hzw r).mp hq2).1
    set A : Finset V := (q.takeUntil z hzq).support.toFinset with hA
    set B : Finset V := r.support.toFinset with hB
    have hAB : Disjoint A B := by
      rw [Finset.disjoint_left]
      intro a ha hb
      exact hldisj (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb)
    have hAs : A ⊆ s0 := by
      intro a ha
      rw [hs0eq, List.mem_toFinset, hsupp]
      exact List.mem_append_left _ (List.mem_toFinset.mp ha)
    have hBs : B ⊆ s0 := by
      intro a ha
      rw [hs0eq, List.mem_toFinset, hsupp]
      exact List.mem_append_right _ (List.mem_toFinset.mp ha)
    have hs0AB : s0 ⊆ A ∪ B := by
      intro a ha
      rw [hs0eq, List.mem_toFinset, hsupp, List.mem_append] at ha
      rcases ha with ha | ha
      · exact Finset.mem_union_left _ (List.mem_toFinset.mpr ha)
      · exact Finset.mem_union_right _ (List.mem_toFinset.mpr ha)
    have huA : u ∈ A := List.mem_toFinset.mpr (Walk.start_mem_support _)
    have hzA : z ∈ A := List.mem_toFinset.mpr (Walk.end_mem_support _)
    have hvB : v ∈ B := List.mem_toFinset.mpr (Walk.end_mem_support _)
    have hdisjO : ∀ s ∈ P.erase s0, Disjoint s s0 := by
      intro s hs
      exact hd s (Finset.mem_of_mem_erase hs) s0 hs0 (Finset.ne_of_mem_erase hs)
    have hAne : A.Nonempty := ⟨u, huA⟩
    have hBne : B.Nonempty := ⟨v, hvB⟩
    refine ⟨insert A (insert B (P.erase s0)), ⟨?_, ?_, ?_⟩, ?_⟩
    · intro s1 hs1 s2 hs2 hne
      rcases Finset.mem_insert.mp hs1 with rfl | hs1 <;>
        rcases Finset.mem_insert.mp hs2 with rfl | hs2
      · exact absurd rfl hne
      · rcases Finset.mem_insert.mp hs2 with rfl | hs2
        · exact hAB
        · exact Finset.disjoint_of_subset_left hAs (hdisjO s2 hs2).symm
      · rcases Finset.mem_insert.mp hs1 with rfl | hs1
        · exact hAB.symm
        · exact Finset.disjoint_of_subset_right hAs (hdisjO s1 hs1)
      · rcases Finset.mem_insert.mp hs1 with rfl | hs1 <;>
          rcases Finset.mem_insert.mp hs2 with rfl | hs2
        · exact absurd rfl hne
        · exact Finset.disjoint_of_subset_left hBs (hdisjO s2 hs2).symm
        · exact Finset.disjoint_of_subset_right hBs (hdisjO s1 hs1)
        · exact hd s1 (Finset.mem_of_mem_erase hs1) s2 (Finset.mem_of_mem_erase hs2) hne
    · intro a _
      obtain ⟨s, hs, has⟩ := Finset.mem_biUnion.mp (hu (Finset.mem_univ a))
      rw [Finset.mem_biUnion]
      by_cases hss : s = s0
      · subst hss
        rcases Finset.mem_union.mp (hs0AB has) with ha | ha
        · exact ⟨A, Finset.mem_insert_self _ _, ha⟩
        · exact ⟨B, Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), ha⟩
      · exact ⟨s, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_erase.mpr ⟨hss, hs⟩)), has⟩
    · intro s hs
      rcases Finset.mem_insert.mp hs with rfl | hs
      · refine ⟨u, z, q.takeUntil z hzq, hq1, rfl, ?_⟩
        intro t ht htA
        rcases Finset.mem_insert.mp ht with rfl | ht
        · exact Or.inr rfl
        · rcases hZ t ht (hAs htA) with h | h
          · exact Or.inl h
          · subst h
            exact absurd hvB (Finset.disjoint_left.mp hAB htA)
      · rcases Finset.mem_insert.mp hs with rfl | hs
        · refine ⟨w, v, r, hr', rfl, ?_⟩
          intro t ht htB
          rcases Finset.mem_insert.mp ht with rfl | ht
          · exact absurd htB (Finset.disjoint_left.mp hAB hzA)
          · rcases hZ t ht (hBs htB) with h | h
            · subst h
              exact absurd htB (Finset.disjoint_left.mp hAB huA)
            · exact Or.inr h
        · have hsP : s ∈ P := Finset.mem_of_mem_erase hs
          have hsne : s ≠ s0 := Finset.ne_of_mem_erase hs
          obtain ⟨u', v', q', hq', hseq, hZ'⟩ := hw s hsP
          refine ⟨u', v', q', hq', hseq, ?_⟩
          intro t ht hts
          rcases Finset.mem_insert.mp ht with rfl | ht
          · exact absurd hts (hother s hsP hsne)
          · exact hZ' t ht hts
    · have h1 := Finset.card_insert_le A (insert B (P.erase s0))
      have h2 := Finset.card_insert_le B (P.erase s0)
      have h3 := Finset.card_erase_of_mem hs0
      have h4 : 0 < P.card := Finset.card_pos.mpr ⟨s0, hs0⟩
      omega

/-- Turning a good cover for `{y, x}` into the form of the step. -/
lemma good_final (H : SimpleGraph V) (P : Finset (Finset V)) (x y : V)
    (hP : ((∀ s1 ∈ P, ∀ s2 ∈ P, s1 ≠ s2 → Disjoint s1 s2) ∧ (Finset.univ ⊆ (P).biUnion id) ∧
    (∀ s ∈ P, ∃ (u v : V) (q : H.Walk u v), q.IsPath ∧ s = q.support.toFinset ∧
      ∀ t ∈ (insert y (insert x (∅ : Finset V))), t ∈ s → t = u ∨ t = v))) :
    H.IsPathCover P ∧
      (∀ s ∈ P, ∃ (u v : V) (q : H.Walk u v), q.IsPath ∧ s = q.support.toFinset ∧
        (x ∈ s → x = u ∨ x = v) ∧ (y ∈ s → y = u ∨ y = v)) := by
  obtain ⟨h1, h2, h3⟩ := hP
  refine ⟨⟨h1, h2, ?_⟩, ?_⟩
  · intro s hs
    obtain ⟨u, v, q, hq, hsq, _⟩ := h3 s hs
    exact ⟨u, v, q, hq, hsq⟩
  · intro s hs
    obtain ⟨u, v, q, hq, hsq, hZ⟩ := h3 s hs
    refine ⟨u, v, q, hq, hsq, ?_, ?_⟩
    · exact hZ x (by simp)
    · exact hZ y (by simp)

/-- Slack at least two gives `S2` for every pair. -/
lemma slack_two (H : SimpleGraph V) (x y : V)
    (hs : H.pathCoverNumber + Fintype.card V + 3 ≤ 2 * H.largestInducedForestSize) :
    ∃ P : Finset (Finset V), H.IsPathCover P ∧
      (∀ s ∈ P, ∃ (u v : V) (q : H.Walk u v), q.IsPath ∧ s = q.support.toFinset ∧
        (x ∈ s → x = u ∨ x = v) ∧ (y ∈ s → y = u ∨ y = v)) ∧
      P.card + Fintype.card V + 1 ≤ 2 * H.largestInducedForestSize := by
  obtain ⟨P0, hP0c, hP0⟩ :=
    OMA.R_WrittenOnTheWallII_GraphConjecture40_conjecture40_R1_H2_R1.exists_pathCover_card_eq H
  obtain ⟨P1, hP1, hP1c⟩ := good_split H P0 ∅ (good_of_cover H P0 hP0) x
  obtain ⟨P2, hP2, hP2c⟩ := good_split H P1 _ hP1 y
  obtain ⟨hc1, hc2⟩ := good_final H P2 x y hP2
  exact ⟨P2, hc1, hc2, by omega⟩

lemma s2b_fin2 (a b d : Fin 2) (h1 : a ≠ b) (h2 : b ≠ d) : a = d := by
  revert a b d; decide

lemma s2b_nodup4 {a u v b : V} (h1 : a ≠ u) (h2 : a ≠ v) (h3 : a ≠ b) (h4 : u ≠ v) (h5 : u ≠ b)
    (h6 : v ≠ b) : [a, u, v, b].Nodup := by
  simp [h1, h2, h3, h4, h5, h6]

/-- Four consecutive vertices on a cycle of a bipartite graph whose two middle vertices avoid
`x` and `y`, given that `x` can only be the start vertex and `y` has the other colour. -/
lemma s2b_four (G : SimpleGraph V) (col : V → Fin 2) (hcol : ∀ u v, G.Adj u v → col u ≠ col v)
    {w : V} (c : G.Walk w w) (hc : c.IsCycle) (x y : V) (hx : x ∈ c.support → x = w)
    (hy : y ∈ c.support → col w ≠ col y) :
    ∃ a u v b : V, G.Adj a u ∧ G.Adj u v ∧ G.Adj v b ∧ [a, u, v, b].Nodup ∧
      u ≠ x ∧ u ≠ y ∧ v ≠ x ∧ v ≠ y := by
  match c, hc with
  | .nil, hc => exact absurd hc Walk.IsCycle.not_of_nil
  | .cons h1 .nil, _ => exact absurd h1 G.irrefl
  | .cons h1 (.cons h2 .nil), hc =>
    rw [Walk.cons_isCycle_iff] at hc
    exact absurd (by simp [Sym2.eq_swap]) hc.2
  | .cons h1 (.cons h2 (.cons h3 .nil)), _ =>
    exact absurd (s2b_fin2 _ _ _ (hcol _ _ h1) (hcol _ _ h2)) (hcol _ _ h3).symm
  | .cons (v := g1) h1 (.cons (v := g2) h2 (.cons (v := g3) h3 (.cons (v := g4) h4 p))), hc =>
    have hq := ((Walk.cons_isCycle_iff _ _).mp hc).1
    rw [Walk.isPath_def] at hq
    simp only [Walk.support_cons, List.nodup_cons, List.mem_cons, not_or] at hq
    have hg4 : g4 ∈ p.support := p.start_mem_support
    have hw : w ∈ p.support := p.end_mem_support
    obtain ⟨⟨h12, h13, h1p⟩, ⟨h23, h2p⟩, h3p, _⟩ := hq
    have h1w : g1 ≠ w := fun e => h1p (e ▸ hw)
    have h2w : g2 ≠ w := fun e => h2p (e ▸ hw)
    have h3w : g3 ≠ w := fun e => h3p (e ▸ hw)
    have hsupp : ∀ z, z = g1 ∨ z = g2 ∨ z = g3 → z ∈ (Walk.cons h1 (.cons h2 (.cons h3 (.cons h4 p)))).support := by
      rintro z (rfl | rfl | rfl) <;> simp
    have hxg : ∀ z, z = g1 ∨ z = g2 ∨ z = g3 → z ≠ x := by
      intro z hz e
      have := hx (e ▸ hsupp z hz)
      rcases hz with rfl | rfl | rfl
      · exact h1w (e.trans this)
      · exact h2w (e.trans this)
      · exact h3w (e.trans this)
    have hcg2 : col g2 = col w := (s2b_fin2 _ _ _ (hcol _ _ h2).symm (hcol _ _ h1).symm)
    have h2y : g2 ≠ y := by
      intro e
      exact hy (e ▸ hsupp g2 (Or.inr (Or.inl rfl))) (e ▸ hcg2.symm)
    by_cases h1y : g1 = y
    · refine ⟨g1, g2, g3, g4, h2, h3, h4, ?_, hxg g2 (by simp), h2y, hxg g3 (by simp), ?_⟩
      · exact s2b_nodup4 h12 h13 (fun e => h1p (e ▸ hg4)) h23 (fun e => h2p (e ▸ hg4))
          (fun e => h3p (e ▸ hg4))
      · intro e
        exact h13 (h1y.trans e.symm)
    · refine ⟨w, g1, g2, g3, h1, h2, h3, ?_, hxg g1 (by simp), h1y, hxg g2 (by simp), h2y⟩
      exact s2b_nodup4 (fun e => h1w e.symm) (fun e => h2w e.symm) (fun e => h3w e.symm) h12 h13 h23

/-- One path plus singletons is a path cover; its size is `n + 1 - |path|`. -/
lemma s2b_cover (G : SimpleGraph V) (x y : V) {a b : V} (q : G.Walk a b) (hq : q.IsPath)
    (hx : x ∈ q.support.toFinset → x = a ∨ x = b) (hy : y ∈ q.support.toFinset → y = a ∨ y = b) :
    ∃ P : Finset (Finset V), G.IsPathCover P ∧
      (∀ s ∈ P, ∃ (u v : V) (r : G.Walk u v), r.IsPath ∧ s = r.support.toFinset ∧
        (x ∈ s → x = u ∨ x = v) ∧ (y ∈ s → y = u ∨ y = v)) ∧
      P.card + q.support.toFinset.card = Fintype.card V + 1 := by
  set S := q.support.toFinset with hSdef
  have hmem : ∀ s ∈ insert S ((Finset.univ \ S).image (fun v => ({v} : Finset V))),
      s = S ∨ ∃ v, v ∉ S ∧ s = {v} := by
    intro s hs
    rw [Finset.mem_insert, Finset.mem_image] at hs
    rcases hs with h | ⟨v, hv, rfl⟩
    · exact Or.inl h
    · exact Or.inr ⟨v, by simpa using hv, rfl⟩
  have hnot : S ∉ (Finset.univ \ S).image (fun v => ({v} : Finset V)) := by
    intro h
    rw [Finset.mem_image] at h
    obtain ⟨v, hv, hvS⟩ := h
    have : v ∈ S := hvS ▸ Finset.mem_singleton_self v
    simp [this] at hv
  refine ⟨insert S ((Finset.univ \ S).image (fun v => ({v} : Finset V))), ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro s1 h1 s2 h2 hne
    rcases hmem s1 h1 with rfl | ⟨v1, hv1, rfl⟩ <;> rcases hmem s2 h2 with rfl | ⟨v2, hv2, rfl⟩
    · exact absurd rfl hne
    · exact Finset.disjoint_singleton_right.mpr hv2
    · exact Finset.disjoint_singleton_left.mpr hv1
    · refine Finset.disjoint_singleton.mpr ?_
      intro e; exact hne (e ▸ rfl)
  · intro v _
    rw [Finset.mem_biUnion]
    by_cases hv : v ∈ S
    · exact ⟨S, Finset.mem_insert_self _ _, hv⟩
    · exact ⟨{v}, Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨v, by simp [hv], rfl⟩),
        Finset.mem_singleton_self v⟩
  · intro s hs
    rcases hmem s hs with rfl | ⟨v, _, rfl⟩
    · exact ⟨a, b, q, hq, rfl⟩
    · exact ⟨v, v, Walk.nil, Walk.IsPath.nil, by simp⟩
  · intro s hs
    rcases hmem s hs with rfl | ⟨v, _, rfl⟩
    · exact ⟨a, b, q, hq, rfl, hx, hy⟩
    · refine ⟨v, v, Walk.nil, Walk.IsPath.nil, by simp, ?_, ?_⟩
      · intro h; left; simpa using h
      · intro h; left; simpa using h
  · rw [Finset.card_insert_of_notMem hnot, Finset.card_image_of_injective _ (fun u v h => by simpa using h),
      Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]
    have : S.card ≤ Fintype.card V := Finset.card_le_univ S
    omega

lemma s2b_forest_ge (G : SimpleGraph V) (h : G.IsAcyclic) :
    Fintype.card V ≤ G.largestInducedForestSize := by
  unfold SimpleGraph.largestInducedForestSize
  apply le_csSup
  · refine ⟨Fintype.card V, ?_⟩
    rintro n ⟨s, _, rfl⟩
    exact Finset.card_le_univ s
  · exact ⟨Finset.univ, h.induce _, Finset.card_univ⟩

/-- `S2` when the feedback vertex number is at most one. -/
theorem s2b_small (V : Type) [Fintype V] [DecidableEq V] (H : SimpleGraph V) (col : V → Fin 2)
    (hcol : ∀ u v, H.Adj u v → col u ≠ col v) (hconn : H.Connected) (x y : V) (hxy : col x ≠ col y)
    (hf : Fintype.card V ≤ H.largestInducedForestSize + 1) :
    ∃ P : Finset (Finset V), H.IsPathCover P ∧
      (∀ s ∈ P, ∃ (u v : V) (q : H.Walk u v), q.IsPath ∧ s = q.support.toFinset ∧
        (x ∈ s → x = u ∨ x = v) ∧ (y ∈ s → y = u ∨ y = v)) ∧
      P.card + Fintype.card V + 1 ≤ 2 * H.largestInducedForestSize := by
  have hxy' : x ≠ y := fun e => hxy (e ▸ rfl)
  by_cases hac : H.IsAcyclic
  · have hge := s2b_forest_ge H hac
    obtain ⟨r⟩ := hconn.preconnected x y
    cases r with
    | nil => exact absurd rfl hxy'
    | @cons _ w _ h r =>
      have hq : (Walk.cons h (Walk.nil : H.Walk w w)).IsPath := by
        simp [Walk.isPath_def, h.ne]
      obtain ⟨P, hP, hends, hcard⟩ := s2b_cover H x y _ hq
        (by intro hx; simp at hx; tauto) (by intro hy; simp at hy; tauto)
      refine ⟨P, hP, hends, ?_⟩
      have h2 : (Walk.cons h (Walk.nil : H.Walk w w)).support.toFinset.card = 2 := by
        simp [Finset.card_pair h.ne]
      omega
  · have hcyc : ∃ (w : V) (c : H.Walk w w), c.IsCycle := by
      by_contra hn
      push Not at hn
      exact hac (fun w c hc => hn w c hc)
    obtain ⟨w, c, hc⟩ := hcyc
    have hfour : ∃ a u v b : V, H.Adj a u ∧ H.Adj u v ∧ H.Adj v b ∧ [a, u, v, b].Nodup ∧
        u ≠ x ∧ u ≠ y ∧ v ≠ x ∧ v ≠ y := by
      by_cases hxc : x ∈ c.support
      · exact s2b_four H col hcol (c.rotate x hxc) (hc.rotate hxc) x y (fun _ => rfl) (fun _ => hxy)
      · by_cases hyc : y ∈ c.support
        · obtain ⟨a, u, v, b, h1, h2, h3, hnd, hux, huy, hvx, hvy⟩ :=
            s2b_four H col hcol (c.rotate y hyc) (hc.rotate hyc) y x (fun _ => rfl)
              (fun _ => hxy.symm)
          exact ⟨a, u, v, b, h1, h2, h3, hnd, huy, hux, hvy, hvx⟩
        · exact s2b_four H col hcol c hc x y (fun h => absurd h hxc) (fun h => absurd h hyc)
    obtain ⟨a, u, v, b, h1, h2, h3, hnd, hux, huy, hvx, hvy⟩ := hfour
    let q : H.Walk a b := Walk.cons h1 (Walk.cons h2 (Walk.cons h3 Walk.nil))
    have hsupp : q.support = [a, u, v, b] := rfl
    have hq : q.IsPath := by rw [Walk.isPath_def, hsupp]; exact hnd
    obtain ⟨P, hP, hends, hcard⟩ := s2b_cover H x y q hq
      (by intro hx; rw [hsupp] at hx; simp at hx; tauto)
      (by intro hy; rw [hsupp] at hy; simp at hy; tauto)
    refine ⟨P, hP, hends, ?_⟩
    have h4 : q.support.toFinset.card = 4 := by
      rw [List.toFinset_card_of_nodup (hsupp ▸ hnd), hsupp]; rfl
    have hfn : H.largestInducedForestSize + 1 ≥ Fintype.card V := hf
    omega

lemma map_caps {G H : SimpleGraph V} (hGH : G ≤ H) {P : Finset (Finset V)} {x y : V}
    (hP : G.IsPathCover P)
    (hc : ∀ s ∈ P, ∃ (u v : V) (q : G.Walk u v), q.IsPath ∧ s = q.support.toFinset ∧
        (x ∈ s → x = u ∨ x = v) ∧ (y ∈ s → y = u ∨ y = v)) :
    H.IsPathCover P ∧ (∀ s ∈ P, ∃ (u v : V) (q : H.Walk u v), q.IsPath ∧
      s = q.support.toFinset ∧ (x ∈ s → x = u ∨ x = v) ∧ (y ∈ s → y = u ∨ y = v)) := by
  refine ⟨⟨hP.1, hP.2.1, ?_⟩, ?_⟩
  · intro s hs
    obtain ⟨u, v, q, hq, hsq, -⟩ := hc s hs
    exact ⟨u, v, q.mapLe hGH, (Walk.isPath_mapLe hGH).mpr hq,
      by rw [Walk.support_mapLe_eq_support]; exact hsq⟩
  · intro s hs
    obtain ⟨u, v, q, hq, hsq, h1, h2⟩ := hc s hs
    exact ⟨u, v, q.mapLe hGH, (Walk.isPath_mapLe hGH).mpr hq,
      by rw [Walk.support_mapLe_eq_support]; exact hsq, h1, h2⟩

lemma fmt_good {G H : SimpleGraph V} (hGH : G ≤ H) {P : Finset (Finset V)} {x y : V}
    (h : ((∀ t₁ ∈ P, ∀ t₂ ∈ P, t₁ ≠ t₂ → Disjoint t₁ t₂) ∧ P.biUnion id = (Finset.univ : Finset V) ∧
  (∀ t ∈ P, ∃ (u₀ v₀ : V) (q₀ : G.Walk u₀ v₀), q₀.IsPath ∧ t = q₀.support.toFinset ∧
    ∀ z₀ ∈ ({x, y} : Finset V), z₀ ∈ t → z₀ = u₀ ∨ z₀ = v₀))) :
    H.IsPathCover P ∧ (∀ s ∈ P, ∃ (u v : V) (q : H.Walk u v), q.IsPath ∧
      s = q.support.toFinset ∧ (x ∈ s → x = u ∨ x = v) ∧ (y ∈ s → y = u ∨ y = v)) := by
  apply map_caps hGH
  · refine ⟨h.1, fun v _ => by rw [h.2.1]; exact Finset.mem_univ v, fun s hs => ?_⟩
    obtain ⟨u, v, q, hq, hsq, -⟩ := h.2.2 s hs
    exact ⟨u, v, q, hq, hsq⟩
  · intro s hs
    obtain ⟨u, v, q, hq, hsq, hz⟩ := h.2.2 s hs
    exact ⟨u, v, q, hq, hsq, hz x (by simp), hz y (by simp)⟩

/-- Deleting an edge that does not increase the forest number. -/
lemma step_edge (H : SimpleGraph V) (a b x y : V)
    (hf : (H.deleteEdges {s(a, b)}).largestInducedForestSize ≤ H.largestInducedForestSize)
    (h : ∃ P : Finset (Finset V), (H.deleteEdges {s(a, b)}).IsPathCover P ∧
      (∀ s ∈ P, ∃ (u v : V) (q : (H.deleteEdges {s(a, b)}).Walk u v), q.IsPath ∧ s = q.support.toFinset ∧
        (x ∈ s → x = u ∨ x = v) ∧ (y ∈ s → y = u ∨ y = v)) ∧
      P.card + Fintype.card V + 1 ≤ 2 * (H.deleteEdges {s(a, b)}).largestInducedForestSize) :
    ∃ P : Finset (Finset V), H.IsPathCover P ∧
      (∀ s ∈ P, ∃ (u v : V) (q : H.Walk u v), q.IsPath ∧ s = q.support.toFinset ∧
        (x ∈ s → x = u ∨ x = v) ∧ (y ∈ s → y = u ∨ y = v)) ∧
      P.card + Fintype.card V + 1 ≤ 2 * H.largestInducedForestSize := by
  obtain ⟨P, hP, hc, hcard⟩ := h
  obtain ⟨hP', hc'⟩ := map_caps (deleteEdges_le _) hP hc
  exact ⟨P, hP', hc', by omega⟩

lemma reach_or (H : SimpleGraph V) (a b : V) {u w : V} (p : H.Walk u w)
    (h : (H.deleteEdges {s(a, b)}).Reachable a u ∨ (H.deleteEdges {s(a, b)}).Reachable b u) :
    (H.deleteEdges {s(a, b)}).Reachable a w ∨ (H.deleteEdges {s(a, b)}).Reachable b w := by
  induction p with
  | nil => exact h
  | @cons u z w huz p ih =>
    apply ih
    by_cases hs : s(u, z) = s(a, b)
    · rcases Sym2.eq_iff.mp hs with ⟨-, rfl⟩ | ⟨-, rfl⟩
      · exact Or.inr (Reachable.refl _)
      · exact Or.inl (Reachable.refl _)
    · have hadj : (H.deleteEdges {s(a, b)}).Adj u z := by
        rw [deleteEdges_adj]; exact ⟨huz, by simpa using hs⟩
      rcases h with h | h
      · exact Or.inl (h.trans hadj.reachable)
      · exact Or.inr (h.trans hadj.reachable)

lemma walk_in (G : SimpleGraph V) (S : Finset V) (hcl : ∀ u v, u ∈ S → G.Adj u v → v ∈ S)
    {u w : V} (p : G.Walk u w) (hu : u ∈ S) : ∀ z ∈ p.support, z ∈ S := by
  induction p with
  | nil =>
    intro z hz
    rw [Walk.support_nil, List.mem_singleton] at hz
    exact hz ▸ hu
  | @cons u v w huv p ih =>
    intro z hz
    rw [Walk.support_cons, List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact hu
    · exact ih (hcl u v hu huv) z hz

lemma conn_in (G : SimpleGraph V) (S : Finset V) (r : V) (hr : r ∈ S)
    (hreach : ∀ v ∈ S, G.Reachable r v) (hcl : ∀ u v, u ∈ S → G.Adj u v → v ∈ S) :
    (G.induce (S : Set V)).Connected := by
  rw [connected_iff_exists_forall_reachable]
  refine ⟨⟨r, hr⟩, ?_⟩
  rintro ⟨v, hv⟩
  obtain ⟨p⟩ := hreach v hv
  exact ⟨p.induce (S : Set V) (fun z hz => Finset.mem_coe.mpr (walk_in G S hcl p hr z hz))⟩

/-- Putting a bridge back does not create a cycle. -/
lemma bridge_acyclic (H : SimpleGraph V) (a b : V)
    (hnr : ¬ (H.deleteEdges {s(a, b)}).Reachable a b) (F : Finset V)
    (hac : ((H.deleteEdges {s(a, b)}).induce (F : Set V)).IsAcyclic) :
    (H.induce (F : Set V)).IsAcyclic := by
  set G := H.deleteEdges {s(a, b)} with hG
  by_cases hF : a ∈ F ∧ b ∈ F
  · obtain ⟨ha, hb⟩ := hF
    have hle : H.induce (F : Set V) ≤
        G.induce (F : Set V) ⊔ edge (⟨a, ha⟩ : (F : Set V)) ⟨b, hb⟩ := by
      intro u v huv
      rw [sup_adj]
      by_cases hs : s(u.1, v.1) = s(a, b)
      · right
        rw [edge_adj]
        refine ⟨?_, huv.ne⟩
        rcases Sym2.eq_iff.mp hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · left; exact ⟨Subtype.ext h1, Subtype.ext h2⟩
        · right; exact ⟨Subtype.ext h1, Subtype.ext h2⟩
      · left
        show G.Adj u.1 v.1
        rw [hG, deleteEdges_adj]
        exact ⟨huv, by simpa using hs⟩
    have hnr' : ¬ (G.induce (F : Set V)).Reachable ⟨a, ha⟩ ⟨b, hb⟩ := by
      intro h
      exact hnr (h.map (Embedding.induce (G := G) (F : Set V)).toHom)
    exact (hac.sup_edge_of_not_reachable hnr').anti hle
  · have hle : H.induce (F : Set V) ≤ G.induce (F : Set V) := by
      intro u v huv
      show G.Adj u.1 v.1
      rw [hG, deleteEdges_adj]
      refine ⟨huv, ?_⟩
      intro hs
      rw [Set.mem_singleton_iff] at hs
      apply hF
      have hu : u.1 ∈ F := u.2
      have hv : v.1 ∈ F := v.2
      rcases Sym2.eq_iff.mp hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1] at hu; rw [h2] at hv; exact ⟨hu, hv⟩
      · rw [h1] at hu; rw [h2] at hv; exact ⟨hv, hu⟩
    exact hac.anti hle

/-- `S2` on one connected vertex set `K` (given `S2` for `G[K]`), with admissible caps `Z`. -/
lemma comp_one (n : ℕ) (ih : (∀ (W : Type) [Fintype W] [DecidableEq W], Fintype.card W < n →
      ∀ (G : SimpleGraph W) (c : W → Fin 2), (∀ u v, G.Adj u v → c u ≠ c v) → G.Connected →
      ∀ x y : W, c x ≠ c y →
      ∃ P : Finset (Finset W), G.IsPathCover P ∧
      (∀ s ∈ P, ∃ (u v : W) (q : G.Walk u v), q.IsPath ∧ s = q.support.toFinset ∧
        (x ∈ s → x = u ∨ x = v) ∧ (y ∈ s → y = u ∨ y = v)) ∧
      P.card + Fintype.card W + 1 ≤ 2 * G.largestInducedForestSize))
    (G : SimpleGraph V) (K : Finset V) (hKn : Fintype.card ↥(K : Set V) < n)
    (hK : (G.induce (K : Set V)).Connected) (c : V → Fin 2)
    (hc : ∀ a ∈ K, ∀ b ∈ K, G.Adj a b → c a ≠ c b)
    (Z : Finset V) (hZ : ∀ z1 ∈ Z, ∀ z2 ∈ Z, z1 ∈ K → z2 ∈ K → z1 ≠ z2 → c z1 ≠ c z2) :
    ∃ P : Finset (Finset V), ((∀ t₁ ∈ P, ∀ t₂ ∈ P, t₁ ≠ t₂ → Disjoint t₁ t₂) ∧ P.biUnion id = K ∧
  (∀ t ∈ P, ∃ (u₀ v₀ : V) (q₀ : G.Walk u₀ v₀), q₀.IsPath ∧ t = q₀.support.toFinset ∧
    ∀ z₀ ∈ Z, z₀ ∈ t → z₀ = u₀ ∨ z₀ = v₀)) ∧
      P.card + K.card ≤ 2 * (G.induce (K : Set V)).largestInducedForestSize ∧
      (2 ≤ K.card → P.card + K.card + 1 ≤ 2 * (G.induce (K : Set V)).largestInducedForestSize) := by
  obtain ⟨v0, hv0⟩ : ∃ v, v ∈ K := by
    obtain ⟨⟨v, hv⟩⟩ := hK.nonempty
    exact ⟨v, hv⟩
  by_cases hK2 : 2 ≤ K.card
  · obtain ⟨x, hxK, y, hyK, hxy, hZxy⟩ := nb0_pick G K hK hK2 c hc Z hZ
    obtain ⟨P', hP', hcap, hcard⟩ := ih (K : Set V) hKn (G.induce (K : Set V)) (fun a => c a.1)
      (fun a b hab => hc a.1 a.2 b.1 b.2 hab) hK ⟨x, hxK⟩ ⟨y, hyK⟩ hxy
    obtain ⟨P, hP, hPc⟩ := nb0_cover_lift G K ⟨x, hxK⟩ ⟨y, hyK⟩ P' hP' hcap Z hZxy
    have hcardK : Fintype.card (K : Set V) = K.card := by simp
    rw [hcardK] at hcard
    refine ⟨P, hP, by omega, fun _ => by omega⟩
  · have hK1 : K = {v0} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr
      refine ⟨hv0, fun a ha => ?_⟩
      by_contra hne
      have : ({a, v0} : Finset V) ⊆ K := by
        intro t ht
        rcases Finset.mem_insert.mp ht with rfl | ht
        · exact ha
        · rw [Finset.mem_singleton.mp ht]; exact hv0
      have := Finset.card_le_card this
      rw [Finset.card_pair hne] at this
      omega
    subst hK1
    refine ⟨{{v0}}, nb0_cover_singleton G v0 Z, ?_, fun h => (hK2 h).elim⟩
    have := nb0_forest_singleton G v0
    simp only [Finset.card_singleton]
    omega

/-- The bridge step: `S2` on the two sides of a bridge gives `S2`. -/
lemma step_bridge (n : ℕ)
    (ih : (∀ (W : Type) [Fintype W] [DecidableEq W], Fintype.card W < n →
      ∀ (G : SimpleGraph W) (c : W → Fin 2), (∀ u v, G.Adj u v → c u ≠ c v) → G.Connected →
      ∀ x y : W, c x ≠ c y →
      ∃ P : Finset (Finset W), G.IsPathCover P ∧
      (∀ s ∈ P, ∃ (u v : W) (q : G.Walk u v), q.IsPath ∧ s = q.support.toFinset ∧
        (x ∈ s → x = u ∨ x = v) ∧ (y ∈ s → y = u ∨ y = v)) ∧
      P.card + Fintype.card W + 1 ≤ 2 * G.largestInducedForestSize))
    (hn : Fintype.card V = n) (H : SimpleGraph V) (c : V → Fin 2)
    (hc : ∀ u v, H.Adj u v → c u ≠ c v) (hconn : H.Connected) (a b : V) (hab : H.Adj a b)
    (hdis : ¬ (H.deleteEdges {s(a, b)}).Connected) (x y : V) (hxy : c x ≠ c y) :
    ∃ P : Finset (Finset V), H.IsPathCover P ∧
      (∀ s ∈ P, ∃ (u v : V) (q : H.Walk u v), q.IsPath ∧ s = q.support.toFinset ∧
        (x ∈ s → x = u ∨ x = v) ∧ (y ∈ s → y = u ∨ y = v)) ∧
      P.card + Fintype.card V + 1 ≤ 2 * H.largestInducedForestSize := by
  classical
  set G := H.deleteEdges {s(a, b)} with hG
  have hGH : G ≤ H := deleteEdges_le _
  have hor : ∀ v, G.Reachable a v ∨ G.Reachable b v := fun v => by
    obtain ⟨p⟩ := hconn.preconnected a v
    exact reach_or H a b p (Or.inl (Reachable.refl _))
  have hnr : ¬ G.Reachable a b := by
    intro h
    apply hdis
    rw [connected_iff_exists_forall_reachable]
    exact ⟨a, fun v => (hor v).elim id (fun hb => h.trans hb)⟩
  set K := Finset.univ.filter (fun v => G.Reachable a v) with hK
  set R := Finset.univ.filter (fun v => ¬ G.Reachable a v) with hR
  have haK : a ∈ K := Finset.mem_filter.mpr ⟨Finset.mem_univ _, Reachable.refl _⟩
  have hbR : b ∈ R := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnr⟩
  have hbK : b ∉ K := fun h => hnr (Finset.mem_filter.mp h).2
  have haR : a ∉ R := fun h => (Finset.mem_filter.mp h).2 (Reachable.refl _)
  have hKR : Disjoint K R := Finset.disjoint_filter_filter_not _ _ _
  have hKRu : K ∪ R = Finset.univ := Finset.filter_union_filter_not_eq _ _
  have hcardn : K.card + R.card = n := by
    rw [← Finset.card_union_of_disjoint hKR, hKRu, Finset.card_univ, hn]
  have hclK : ∀ u v, u ∈ K → G.Adj u v → v ∈ K := by
    intro u v hu huv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hu).2.trans huv.reachable⟩
  have hclR : ∀ u v, u ∈ R → G.Adj u v → v ∈ R := by
    intro u v hu huv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      fun h => (Finset.mem_filter.mp hu).2 (h.trans huv.symm.reachable)⟩
  have hconnK := conn_in G K a haK (fun v hv => (Finset.mem_filter.mp hv).2) hclK
  have hconnR := conn_in G R b hbR
    (fun v hv => (hor v).resolve_left (Finset.mem_filter.mp hv).2) hclR
  have hcG : ∀ S : Finset V, ∀ u ∈ S, ∀ v ∈ S, G.Adj u v → c u ≠ c v :=
    fun _ u _ v _ h => hc u v (hGH h)
  have hcardK : Fintype.card (K : Set V) < n := by
    have : Fintype.card (K : Set V) = K.card := by simp
    rw [this]
    have := Finset.card_pos.mpr ⟨b, hbR⟩
    omega
  have hcardR : Fintype.card (R : Set V) < n := by
    have : Fintype.card (R : Set V) = R.card := by simp
    rw [this]
    have := Finset.card_pos.mpr ⟨a, haK⟩
    omega
  have hZ : ∀ z1 ∈ ({x, y} : Finset V), ∀ z2 ∈ ({x, y} : Finset V), z1 ≠ z2 → c z1 ≠ c z2 := by
    intro z1 h1 z2 h2 hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2
    rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl
    · exact (hne rfl).elim
    · exact hxy
    · exact fun h => hxy h.symm
    · exact (hne rfl).elim
  obtain ⟨PK, hPK, hPKc, hPKe⟩ := comp_one n ih G K hcardK hconnK c (hcG K) {x, y} (fun z1 h1 z2 h2 _ _ hne => hZ z1 h1 z2 h2 hne)
  obtain ⟨PR, hPR, hPRc, hPRe⟩ := comp_one n ih G R hcardR hconnR c (hcG R) {x, y} (fun z1 h1 z2 h2 _ _ hne => hZ z1 h1 z2 h2 hne)
  -- forests
  obtain ⟨F1, hF1K, hF1, hF1c⟩ := nb0_exists_forest_sub G K
  obtain ⟨F2, hF2R, hF2, hF2c⟩ := nb0_exists_forest_sub G R
  have hno : ∀ u ∈ F1, ∀ v ∈ F2, ¬ G.Adj u v := fun u hu v hv huv =>
    Finset.disjoint_left.mp hKR (hclK u v (hF1K hu) huv) (hF2R hv)
  have hacG := nb0_acyclic_union G F1 F2 hF1 hF2 hno
  have hacH := bridge_acyclic H a b hnr (F1 ∪ F2) hacG
  have hf := nb0_card_le_forest H (F1 ∪ F2) hacH
  have hd : Disjoint F1 F2 :=
    Finset.disjoint_of_subset_left hF1K (Finset.disjoint_of_subset_right hF2R hKR)
  rw [Finset.card_union_of_disjoint hd, hF1c, hF2c] at hf
  by_cases h2 : 2 ≤ K.card ∨ 2 ≤ R.card
  · have hU := nb0_cover_union hPK hPR hKR
    rw [hKRu] at hU
    obtain ⟨hP, hcap⟩ := fmt_good hGH hU
    refine ⟨PK ∪ PR, hP, hcap, ?_⟩
    have hPc : (PK ∪ PR).card ≤ PK.card + PR.card := Finset.card_union_le _ _
    rw [hn]
    rcases h2 with h2 | h2
    · have := hPKe h2
      omega
    · have := hPRe h2
      omega
  · push Not at h2
    have hK1 : K = {a} := Finset.eq_singleton_iff_unique_mem.mpr
      ⟨haK, fun v hv => Finset.card_le_one.mp (by omega) v hv a haK⟩
    have hR1 : R = {b} := Finset.eq_singleton_iff_unique_mem.mpr
      ⟨hbR, fun v hv => Finset.card_le_one.mp (by omega) v hv b hbR⟩
    have hfa := nb0_forest_singleton G a
    have hfb := nb0_forest_singleton G b
    rw [← hK1] at hfa
    rw [← hR1] at hfb
    have hall : ∀ v : V, v = a ∨ v = b := by
      intro v
      have hv : v ∈ K ∪ R := by rw [hKRu]; exact Finset.mem_univ v
      rw [hK1, hR1] at hv
      simpa using hv
    have hpath : (Walk.cons hab Walk.nil : H.Walk a b).IsPath :=
      (Walk.cons_isPath_iff hab Walk.nil).mpr ⟨Walk.IsPath.nil, by simp [hab.ne]⟩
    refine ⟨{{a, b}}, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
    · intro s1 hs1 s2 hs2 hne
      rw [Finset.mem_singleton] at hs1 hs2
      exact (hne (hs1.trans hs2.symm)).elim
    · intro v _
      simp only [Finset.singleton_biUnion, id]
      rcases hall v with rfl | rfl <;> simp
    · intro s hs
      rw [Finset.mem_singleton] at hs
      exact ⟨a, b, _, hpath, by rw [hs]; simp⟩
    · intro s hs
      rw [Finset.mem_singleton] at hs
      refine ⟨a, b, _, hpath, by rw [hs]; simp, ?_, ?_⟩
      · intro _; exact hall x
      · intro _; exact hall y
    · rw [Finset.card_singleton, hn]
      omega


/-- In a bridgeless connected graph with two vertices, every vertex has a neighbour other than any
given vertex (no vertex has degree one). -/
lemma noleaf_of_bridgeless (H : SimpleGraph V) (hconn : H.Connected)
    (hbr : ∀ a b, H.Adj a b → (H.deleteEdges {s(a, b)}).Connected) {x y : V} (hxy : x ≠ y) :
    ∀ u w : V, ∃ a, a ≠ w ∧ H.Adj u a := by
  intro u w
  obtain ⟨v, huv⟩ : ∃ v, H.Adj u v := by
    obtain ⟨z, hz⟩ : ∃ z, z ≠ u := by
      by_cases h : x = u
      · exact ⟨y, fun e => hxy (h.trans e.symm)⟩
      · exact ⟨x, h⟩
    obtain ⟨p⟩ := hconn.preconnected u z
    cases p with
    | nil => exact (hz rfl).elim
    | cons h _ => exact ⟨_, h⟩
  by_contra hcon
  push Not at hcon
  have hall : ∀ a, H.Adj u a → a = v := by
    intro a ha
    have hav : a = w := by
      by_contra h
      exact hcon a h ha
    have hvw : v = w := by
      by_contra h
      exact hcon v h huv
    rw [hav, hvw]
  obtain ⟨p⟩ := (hbr u v huv).preconnected u v
  cases p with
  | nil => exact huv.ne rfl
  | @cons _ z _ h _ =>
    rw [deleteEdges_adj] at h
    have hz := hall z h.1
    subst hz
    exact h.2 (Set.mem_singleton _)

/-- Every component of `H - w` contains a neighbour of `w`. -/
lemma exists_nbr_comp (G : SimpleGraph V) (w : V) : ∀ {z t : V} (p : G.Walk z t), t = w → z ≠ w →
    ∃ u, u ≠ w ∧ G.Adj u w ∧ (∃ (h₁ : z ∈ Finset.univ.erase w) (h₂ : u ∈ Finset.univ.erase w),
      (G.induce ((Finset.univ.erase w : Finset V) : Set V)).Reachable ⟨z, h₁⟩ ⟨u, h₂⟩) := by
  intro z t p
  induction p with
  | nil => intro h1 h2; exact (h2 h1).elim
  | @cons a b t' h p' ih =>
    intro ht ha
    have haB : a ∈ Finset.univ.erase w := Finset.mem_erase.mpr ⟨ha, Finset.mem_univ a⟩
    by_cases hb : b = w
    · exact ⟨a, ha, hb ▸ h, nb0_rb_refl G _ haB⟩
    · obtain ⟨u, huw, hu, hr⟩ := ih ht hb
      have hbB : b ∈ Finset.univ.erase w := Finset.mem_erase.mpr ⟨hb, Finset.mem_univ b⟩
      exact ⟨u, huw, hu, nb0_rb_trans (nb0_rb_adj haB hbB h) hr⟩

lemma rb_compl (G : SimpleGraph V) (w : V) {a b : V}
    (h : ∃ (h₁ : a ∈ Finset.univ.erase w) (h₂ : b ∈ Finset.univ.erase w),
      (G.induce ((Finset.univ.erase w : Finset V) : Set V)).Reachable ⟨a, h₁⟩ ⟨b, h₂⟩)
    (ha : a ∈ ({w}ᶜ : Set V)) (hb : b ∈ ({w}ᶜ : Set V)) :
    (G.induce ({w}ᶜ : Set V)).Reachable ⟨a, ha⟩ ⟨b, hb⟩ := by
  obtain ⟨_, _, ⟨p⟩⟩ := h
  have hq : ∀ z ∈ (p.map (Embedding.induce (G := G) _).toHom).support, z ∈ ({w}ᶜ : Set V) := by
    intro z hz
    obtain ⟨y, _, rfl⟩ := nb0_mem_support_map p hz
    exact Set.mem_compl_singleton_iff.mpr (Finset.mem_erase.mp y.2).1
  exact ⟨(p.map (Embedding.induce (G := G) _).toHom).induce _ hq⟩

/-- `S2` on every component of a vertex set `B` (component form, from `S2` on fewer vertices). -/
lemma comp_all (n : ℕ) (ih : (∀ (W : Type) [Fintype W] [DecidableEq W], Fintype.card W < n →
      ∀ (G : SimpleGraph W) (c : W → Fin 2), (∀ u v, G.Adj u v → c u ≠ c v) → G.Connected →
      ∀ x y : W, c x ≠ c y →
      ∃ P : Finset (Finset W), G.IsPathCover P ∧
      (∀ s ∈ P, ∃ (u v : W) (q : G.Walk u v), q.IsPath ∧ s = q.support.toFinset ∧
        (x ∈ s → x = u ∨ x = v) ∧ (y ∈ s → y = u ∨ y = v)) ∧
      P.card + Fintype.card W + 1 ≤ 2 * G.largestInducedForestSize))
    (G : SimpleGraph V) (c : V → Fin 2) :
    ∀ (m : ℕ) (B : Finset V), B.card = m → B.card < n →
    (∀ a ∈ B, ∀ b ∈ B, G.Adj a b → c a ≠ c b) →
    ∀ Z : Finset V, (∀ z1 ∈ Z, ∀ z2 ∈ Z, z1 ≠ z2 →
      (∃ (hx₀ : z1 ∈ B) (hy₀ : z2 ∈ B), (G.induce (B : Set V)).Reachable ⟨z1, hx₀⟩ ⟨z2, hy₀⟩) →
      c z1 ≠ c z2) →
    ∃ P : Finset (Finset V), ((∀ t₁ ∈ P, ∀ t₂ ∈ P, t₁ ≠ t₂ → Disjoint t₁ t₂) ∧ P.biUnion id = B ∧
      (∀ t ∈ P, ∃ (u₀ v₀ : V) (q₀ : G.Walk u₀ v₀), q₀.IsPath ∧ t = q₀.support.toFinset ∧
        ∀ z₀ ∈ Z, z₀ ∈ t → z₀ = u₀ ∨ z₀ = v₀)) ∧
      P.card + B.card ≤ 2 * (G.induce (B : Set V)).largestInducedForestSize ∧
      ((∃ a ∈ B, ∃ b ∈ B, G.Adj a b) →
        P.card + B.card + 1 ≤ 2 * (G.induce (B : Set V)).largestInducedForestSize) := by
  classical
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ihm =>
  intro B hBm hBn hc Z hZ
  by_cases hB : B = ∅
  · subst hB
    refine ⟨∅, ⟨by simp, by simp, by simp⟩, by simp, ?_⟩
    rintro ⟨a, ha, _⟩
    exact (Finset.notMem_empty a ha).elim
  obtain ⟨v, hv⟩ := Finset.nonempty_iff_ne_empty.mpr hB
  set K := B.filter (fun x => (∃ (hx₀ : v ∈ B) (hy₀ : x ∈ B),
    (G.induce (B : Set V)).Reachable ⟨v, hx₀⟩ ⟨x, hy₀⟩)) with hKdef
  set R := B.filter (fun x => ¬ (∃ (hx₀ : v ∈ B) (hy₀ : x ∈ B),
    (G.induce (B : Set V)).Reachable ⟨v, hx₀⟩ ⟨x, hy₀⟩)) with hRdef
  have hvK : v ∈ K := Finset.mem_filter.mpr ⟨hv, nb0_rb_refl G B hv⟩
  have hKB : K ⊆ B := Finset.filter_subset _ _
  have hRB : R ⊆ B := Finset.filter_subset _ _
  have hKR : Disjoint K R := Finset.disjoint_filter_filter_not B B _
  have hBKR : K ∪ R = B := Finset.filter_union_filter_not_eq _ B
  have hcardB : K.card + R.card = B.card := by
    rw [← Finset.card_union_of_disjoint hKR, hBKR]
  have hK1 : 1 ≤ K.card := Finset.card_pos.mpr ⟨v, hvK⟩
  have hno : ∀ a ∈ K, ∀ b ∈ R, ¬ G.Adj a b := by
    intro a ha b hb hab
    have hra := (Finset.mem_filter.mp ha).2
    have hb' := Finset.mem_filter.mp hb
    exact hb'.2 (nb0_rb_trans hra (nb0_rb_adj (hKB ha) hb'.1 hab))
  obtain ⟨PR, hPR, hPRc, hPRe⟩ := ihm R.card (by omega) R rfl (by omega)
    (fun a ha b hb hab => hc a (hRB ha) b (hRB hb) hab) Z
    (fun z1 h1 z2 h2 hne hr => hZ z1 h1 z2 h2 hne (nb0_rb_mono hRB hr))
  have hKconn := nb0_comp_connected G B K hv (fun x => Finset.mem_filter)
  have hKn : Fintype.card (K : Set V) < n := by
    have : Fintype.card (K : Set V) = K.card := by simp
    rw [this]
    omega
  obtain ⟨PK, hPK, hPKc, hPKe⟩ := comp_one n ih G K hKn hKconn c
    (fun a ha b hb hab => hc a (hKB ha) b (hKB hb) hab) Z
    (fun z1 h1 z2 h2 hz1 hz2 hne => hZ z1 h1 z2 h2 hne
      (nb0_rb_trans (nb0_rb_symm (Finset.mem_filter.mp hz1).2) (Finset.mem_filter.mp hz2).2))
  have hU := nb0_cover_union hPK hPR hKR
  rw [hBKR] at hU
  have hf := nb0_forest_superadd G K R hKR hno
  rw [hBKR] at hf
  have hPc : (PK ∪ PR).card ≤ PK.card + PR.card := Finset.card_union_le _ _
  refine ⟨PK ∪ PR, hU, by omega, ?_⟩
  rintro ⟨a, ha, b, hb, hab⟩
  by_cases haK : a ∈ K
  · have hbK : b ∈ K := by
      by_contra hbK
      have hbR : b ∈ R := by
        rw [← hBKR] at hb
        rcases Finset.mem_union.mp hb with h | h
        · exact (hbK h).elim
        · exact h
      exact hno a haK b hbR hab
    have hab' : a ≠ b := hab.ne
    have h2 : 2 ≤ K.card := by
      have : ({a, b} : Finset V) ⊆ K := by
        intro t ht
        rcases Finset.mem_insert.mp ht with rfl | ht
        · exact haK
        · rw [Finset.mem_singleton.mp ht]; exact hbK
      have := Finset.card_le_card this
      rwa [Finset.card_pair hab'] at this
    have := hPKe h2
    omega
  · have haR : a ∈ R := by
      rw [← hBKR] at ha
      rcases Finset.mem_union.mp ha with h | h
      · exact (haK h).elim
      · exact h
    have hbR : b ∈ R := by
      by_contra hbR
      have hbK : b ∈ K := by
        rw [← hBKR] at hb
        rcases Finset.mem_union.mp hb with h | h
        · exact h
        · exact (hbR h).elim
      exact hno b hbK a haR hab.symm
    have := hPRe ⟨a, haR, b, hbR, hab⟩
    omega

/-- Choice of the vertex `u` of `H - w` to which the cut vertex `w` is attached. -/
lemma choose_u (H : SimpleGraph V) (c : V → Fin 2) (hc : ∀ u v, H.Adj u v → c u ≠ c v)
    (B : Finset V) (w : V) (hmemB : ∀ z, z ∈ B ↔ z ≠ w)
    (hnbr : ∀ z, z ≠ w → ∃ u, u ≠ w ∧ H.Adj u w ∧
      (∃ (h₁ : z ∈ B) (h₂ : u ∈ B), (H.induce (B : Set V)).Reachable ⟨z, h₁⟩ ⟨u, h₂⟩))
    (pick : ∀ z, z ≠ w → ∃ u, u ≠ w ∧ H.Adj u w ∧
      ¬ (∃ (h₁ : z ∈ B) (h₂ : u ∈ B), (H.induce (B : Set V)).Reachable ⟨z, h₁⟩ ⟨u, h₂⟩))
    (x y : V) (hxy : c x ≠ c y)
    (hcase : x = w ∨ (x ≠ w ∧ y ≠ w ∧
      ((∃ (h₁ : x ∈ B) (h₂ : y ∈ B), (H.induce (B : Set V)).Reachable ⟨x, h₁⟩ ⟨y, h₂⟩) ∨
        c w = c x))) :
    ∃ u, u ≠ w ∧ H.Adj u w ∧ u ≠ x ∧ u ≠ y ∧
      (∀ z, (z = x ∨ z = y) → z ≠ w →
        (∃ (h₁ : z ∈ B) (h₂ : u ∈ B), (H.induce (B : Set V)).Reachable ⟨z, h₁⟩ ⟨u, h₂⟩) →
        c z ≠ c u) ∧
      ∃ r, r ≠ w ∧
        ¬ (∃ (h₁ : u ∈ B) (h₂ : r ∈ B), (H.induce (B : Set V)).Reachable ⟨u, h₁⟩ ⟨r, h₂⟩) := by
  have hneq : ∀ z u, z ≠ w →
      ¬ (∃ (h₁ : z ∈ B) (h₂ : u ∈ B), (H.induce (B : Set V)).Reachable ⟨z, h₁⟩ ⟨u, h₂⟩) →
      u ≠ z := by
    intro z u hz h e
    subst e
    exact h (nb0_rb_refl H B ((hmemB u).mpr hz))
  rcases hcase with hxw | ⟨hxw, hyw, hcase⟩
  · have hyw : y ≠ w := fun e => hxy (by rw [hxw, e])
    obtain ⟨u, huw, hu, hyu⟩ := pick y hyw
    refine ⟨u, huw, hu, fun e => huw (e.trans hxw), hneq y u hyw hyu, ?_, y, hyw,
      fun h => hyu (nb0_rb_symm h)⟩
    rintro z (rfl | rfl) hzw hzu
    · exact (hzw hxw).elim
    · exact (hyu hzu).elim
  · by_cases hR : (∃ (h₁ : x ∈ B) (h₂ : y ∈ B), (H.induce (B : Set V)).Reachable ⟨x, h₁⟩ ⟨y, h₂⟩)
    · obtain ⟨u, huw, hu, hxu⟩ := pick x hxw
      have hyu : ¬ (∃ (h₁ : y ∈ B) (h₂ : u ∈ B),
          (H.induce (B : Set V)).Reachable ⟨y, h₁⟩ ⟨u, h₂⟩) :=
        fun h => hxu (nb0_rb_trans hR h)
      refine ⟨u, huw, hu, hneq x u hxw hxu, hneq y u hyw hyu, ?_, x, hxw,
        fun h => hxu (nb0_rb_symm h)⟩
      rintro z (rfl | rfl) _ hzu
      · exact (hxu hzu).elim
      · exact (hyu hzu).elim
    · have hcw : c w = c x := hcase.resolve_left hR
      obtain ⟨u, huw, hu, hxu⟩ := hnbr x hxw
      have hcu : c u ≠ c w := hc u w hu
      have hxcu : c x ≠ c u := fun e => hcu (e.symm.trans hcw.symm)
      have hyu : ¬ (∃ (h₁ : y ∈ B) (h₂ : u ∈ B),
          (H.induce (B : Set V)).Reachable ⟨y, h₁⟩ ⟨u, h₂⟩) :=
        fun h => hR (nb0_rb_trans hxu (nb0_rb_symm h))
      refine ⟨u, huw, hu, fun e => hxcu (by rw [e]), hneq y u hyw hyu, ?_, y, hyw,
        fun h => hyu (nb0_rb_symm h)⟩
      rintro z (rfl | rfl) _ hzu
      · exact hxcu
      · exact (hyu hzu).elim

/-- The cut-vertex step: if `H - w` is disconnected and `H` has no vertex of degree one, then `S2`
on fewer vertices gives `S2` for `H`. -/
lemma step_cut (n : ℕ)
    (ih : (∀ (W : Type) [Fintype W] [DecidableEq W], Fintype.card W < n →
      ∀ (G : SimpleGraph W) (c : W → Fin 2), (∀ u v, G.Adj u v → c u ≠ c v) → G.Connected →
      ∀ x y : W, c x ≠ c y →
      ∃ P : Finset (Finset W), G.IsPathCover P ∧
      (∀ s ∈ P, ∃ (u v : W) (q : G.Walk u v), q.IsPath ∧ s = q.support.toFinset ∧
        (x ∈ s → x = u ∨ x = v) ∧ (y ∈ s → y = u ∨ y = v)) ∧
      P.card + Fintype.card W + 1 ≤ 2 * G.largestInducedForestSize))
    (hn : Fintype.card V = n) (H : SimpleGraph V) (c : V → Fin 2)
    (hc : ∀ u v, H.Adj u v → c u ≠ c v) (hconn : H.Connected)
    (hnoleaf : ∀ u w : V, ∃ a, a ≠ w ∧ H.Adj u a) (w : V)
    (hcut : ¬ (H.induce ({w}ᶜ : Set V)).Connected) (x y : V) (hxy : c x ≠ c y) :
    ∃ P : Finset (Finset V), H.IsPathCover P ∧
      (∀ s ∈ P, ∃ (u v : V) (q : H.Walk u v), q.IsPath ∧ s = q.support.toFinset ∧
        (x ∈ s → x = u ∨ x = v) ∧ (y ∈ s → y = u ∨ y = v)) ∧
      P.card + Fintype.card V + 1 ≤ 2 * H.largestInducedForestSize := by
  classical
  set B : Finset V := Finset.univ.erase w with hBdef
  have hmemB : ∀ z, z ∈ B ↔ z ≠ w := fun z => by simp [B]
  have hwB : w ∉ B := by simp [B]
  have hcardB : B.card + 1 = n := by
    rw [hBdef, Finset.card_erase_add_one (Finset.mem_univ w), Finset.card_univ, hn]
  -- two vertices of `H - w` in different components
  obtain ⟨a0, b0, ha0, hb0, hab⟩ : ∃ a b, a ≠ w ∧ b ≠ w ∧
      ¬ (∃ (h₁ : a ∈ B) (h₂ : b ∈ B), (H.induce (B : Set V)).Reachable ⟨a, h₁⟩ ⟨b, h₂⟩) := by
    by_contra hcon
    push Not at hcon
    apply hcut
    obtain ⟨z, hz, -⟩ := hnoleaf w w
    have : Nonempty ({w}ᶜ : Set V) := ⟨⟨z, Set.mem_compl_singleton_iff.mpr hz⟩⟩
    rw [connected_iff]
    refine ⟨fun p q => ?_, inferInstance⟩
    have hp : p.1 ≠ w := Set.mem_compl_singleton_iff.mp p.2
    have hq : q.1 ≠ w := Set.mem_compl_singleton_iff.mp q.2
    exact rb_compl H w (hcon p.1 q.1 hp hq) p.2 q.2
  have hnbr : ∀ z, z ≠ w → ∃ u, u ≠ w ∧ H.Adj u w ∧
      (∃ (h₁ : z ∈ B) (h₂ : u ∈ B), (H.induce (B : Set V)).Reachable ⟨z, h₁⟩ ⟨u, h₂⟩) := by
    intro z hz
    obtain ⟨p⟩ := hconn.preconnected z w
    exact exists_nbr_comp H w p rfl hz
  have hsplit : ∀ z, z ≠ w →
      ¬ (∃ (h₁ : z ∈ B) (h₂ : a0 ∈ B), (H.induce (B : Set V)).Reachable ⟨z, h₁⟩ ⟨a0, h₂⟩) ∨
      ¬ (∃ (h₁ : z ∈ B) (h₂ : b0 ∈ B), (H.induce (B : Set V)).Reachable ⟨z, h₁⟩ ⟨b0, h₂⟩) := by
    intro z _
    by_contra hcon
    push Not at hcon
    exact hab (nb0_rb_trans (nb0_rb_symm hcon.1) hcon.2)
  have pick : ∀ z, z ≠ w → ∃ u, u ≠ w ∧ H.Adj u w ∧
      ¬ (∃ (h₁ : z ∈ B) (h₂ : u ∈ B), (H.induce (B : Set V)).Reachable ⟨z, h₁⟩ ⟨u, h₂⟩) := by
    intro z hz
    rcases hsplit z hz with h | h
    · obtain ⟨u, huw, hu, hr⟩ := hnbr a0 ha0
      exact ⟨u, huw, hu, fun h' => h (nb0_rb_trans h' (nb0_rb_symm hr))⟩
    · obtain ⟨u, huw, hu, hr⟩ := hnbr b0 hb0
      exact ⟨u, huw, hu, fun h' => h (nb0_rb_trans h' (nb0_rb_symm hr))⟩
  -- the attachment vertex `u`
  obtain ⟨u, huw, hu, hux, huy, hcol, r, hrw, hr⟩ : ∃ u, u ≠ w ∧ H.Adj u w ∧ u ≠ x ∧ u ≠ y ∧
      (∀ z, (z = x ∨ z = y) → z ≠ w →
        (∃ (h₁ : z ∈ B) (h₂ : u ∈ B), (H.induce (B : Set V)).Reachable ⟨z, h₁⟩ ⟨u, h₂⟩) →
        c z ≠ c u) ∧
      ∃ r, r ≠ w ∧
        ¬ (∃ (h₁ : u ∈ B) (h₂ : r ∈ B), (H.induce (B : Set V)).Reachable ⟨u, h₁⟩ ⟨r, h₂⟩) := by
    by_cases hxw : x = w
    · exact choose_u H c hc B w hmemB hnbr pick x y hxy (Or.inl hxw)
    by_cases hyw : y = w
    · obtain ⟨u, h1, h2, h3, h4, h5, h6⟩ :=
        choose_u H c hc B w hmemB hnbr pick y x (Ne.symm hxy) (Or.inl hyw)
      exact ⟨u, h1, h2, h4, h3, fun z hz => h5 z hz.symm, h6⟩
    by_cases hR : (∃ (h₁ : x ∈ B) (h₂ : y ∈ B), (H.induce (B : Set V)).Reachable ⟨x, h₁⟩ ⟨y, h₂⟩)
    · exact choose_u H c hc B w hmemB hnbr pick x y hxy (Or.inr ⟨hxw, hyw, Or.inl hR⟩)
    by_cases hcw : c w = c x
    · exact choose_u H c hc B w hmemB hnbr pick x y hxy (Or.inr ⟨hxw, hyw, Or.inr hcw⟩)
    · have hcw' : c w = c y := s2b_fin2 _ _ _ hcw hxy
      obtain ⟨u, h1, h2, h3, h4, h5, h6⟩ :=
        choose_u H c hc B w hmemB hnbr pick y x (Ne.symm hxy) (Or.inr ⟨hyw, hxw, Or.inr hcw'⟩)
      exact ⟨u, h1, h2, h4, h3, fun z hz => h5 z hz.symm, h6⟩
  have huB : u ∈ B := (hmemB u).mpr huw
  -- the component `K` of `u` in `H - w`, and the rest `R`
  set K := B.filter (fun z => (∃ (h₁ : u ∈ B) (h₂ : z ∈ B),
    (H.induce (B : Set V)).Reachable ⟨u, h₁⟩ ⟨z, h₂⟩)) with hKdef
  set R := B.filter (fun z => ¬ (∃ (h₁ : u ∈ B) (h₂ : z ∈ B),
    (H.induce (B : Set V)).Reachable ⟨u, h₁⟩ ⟨z, h₂⟩)) with hRdef
  have hKB : K ⊆ B := Finset.filter_subset _ _
  have hRB : R ⊆ B := Finset.filter_subset _ _
  have hKR : Disjoint K R := Finset.disjoint_filter_filter_not B B _
  have hBKR : K ∪ R = B := Finset.filter_union_filter_not_eq _ B
  have huK : u ∈ K := Finset.mem_filter.mpr ⟨huB, nb0_rb_refl H B huB⟩
  have hno : ∀ a ∈ K, ∀ b ∈ R, ¬ H.Adj a b := by
    intro a ha b hb hab
    have hra := (Finset.mem_filter.mp ha).2
    have hb' := Finset.mem_filter.mp hb
    exact hb'.2 (nb0_rb_trans hra (nb0_rb_adj (hKB ha) hb'.1 hab))
  have hKconn := nb0_comp_connected H B K huB (fun z => Finset.mem_filter)
  -- `K` has an edge
  obtain ⟨u', hu'w, huu'⟩ := hnoleaf u w
  have hu'B : u' ∈ B := (hmemB u').mpr hu'w
  have hu'K : u' ∈ K := Finset.mem_filter.mpr ⟨hu'B, nb0_rb_adj huB hu'B huu'⟩
  have hK2 : 2 ≤ K.card := by
    have hsub : ({u, u'} : Finset V) ⊆ K := by
      intro t ht
      rcases Finset.mem_insert.mp ht with rfl | ht
      · exact huK
      · rw [Finset.mem_singleton.mp ht]; exact hu'K
    have := Finset.card_le_card hsub
    rwa [Finset.card_pair huu'.ne] at this
  -- `R` has an edge
  have hrB : r ∈ B := (hmemB r).mpr hrw
  have hrR : r ∈ R := Finset.mem_filter.mpr ⟨hrB, hr⟩
  obtain ⟨r', hr'w, hrr'⟩ := hnoleaf r w
  have hr'B : r' ∈ B := (hmemB r').mpr hr'w
  have hr'R : r' ∈ R := by
    refine Finset.mem_filter.mpr ⟨hr'B, fun h => hr ?_⟩
    exact nb0_rb_trans h (nb0_rb_adj hr'B hrB hrr'.symm)
  -- caps
  set Z : Finset V := insert u {x, y} with hZdef
  have hZmem : ∀ z ∈ Z, z ≠ u → z = x ∨ z = y := by
    intro z hz hzu
    rcases Finset.mem_insert.mp hz with h | h
    · exact (hzu h).elim
    · simpa using h
  have hZK : ∀ z1 ∈ Z, ∀ z2 ∈ Z, z1 ∈ K → z2 ∈ K → z1 ≠ z2 → c z1 ≠ c z2 := by
    have key : ∀ z ∈ Z, z ∈ K → z ≠ u → (z = x ∨ z = y) ∧ c z ≠ c u := by
      intro z hz hzK hzu
      have hxy' := hZmem z hz hzu
      exact ⟨hxy', hcol z hxy' ((hmemB z).mp (hKB hzK))
        (nb0_rb_symm (Finset.mem_filter.mp hzK).2)⟩
    intro z1 h1 z2 h2 hz1 hz2 hne
    by_cases h1u : z1 = u
    · rw [h1u] at hne ⊢
      exact fun h => (key z2 h2 hz2 (Ne.symm hne)).2 h.symm
    · by_cases h2u : z2 = u
      · rw [h2u]
        exact (key z1 h1 hz1 h1u).2
      · rcases (key z1 h1 hz1 h1u).1 with rfl | rfl <;>
          rcases (key z2 h2 hz2 h2u).1 with rfl | rfl
        · exact (hne rfl).elim
        · exact hxy
        · exact fun h => hxy h.symm
        · exact (hne rfl).elim
  have hZR : ∀ z1 ∈ Z, ∀ z2 ∈ Z, z1 ≠ z2 →
      (∃ (hx₀ : z1 ∈ R) (hy₀ : z2 ∈ R), (H.induce (R : Set V)).Reachable ⟨z1, hx₀⟩ ⟨z2, hy₀⟩) →
      c z1 ≠ c z2 := by
    intro z1 h1 z2 h2 hne hreach
    obtain ⟨hz1, hz2, _⟩ := hreach
    have hu1 : z1 ≠ u := fun e => Finset.disjoint_left.mp hKR huK (e ▸ hz1)
    have hu2 : z2 ≠ u := fun e => Finset.disjoint_left.mp hKR huK (e ▸ hz2)
    rcases hZmem z1 h1 hu1 with rfl | rfl <;> rcases hZmem z2 h2 hu2 with rfl | rfl
    · exact (hne rfl).elim
    · exact hxy
    · exact fun h => hxy h.symm
    · exact (hne rfl).elim
  have hKn : Fintype.card (K : Set V) < n := by
    have h1 : Fintype.card (K : Set V) = K.card := by simp
    have h2 := Finset.card_le_card hKB
    omega
  obtain ⟨PK, hPK, -, hPKe⟩ := comp_one n ih H K hKn hKconn c
    (fun a _ b _ h => hc a b h) Z hZK
  obtain ⟨PR, hPR, -, hPRe⟩ := comp_all n ih H c R.card R rfl
    (by have := Finset.card_le_card hRB; omega) (fun a _ b _ h => hc a b h) Z hZR
  have hPKe' := hPKe hK2
  have hPRe' := hPRe ⟨r, hrR, r', hr'R, hrr'⟩
  have hU := nb0_cover_union hPK hPR hKR
  rw [hBKR] at hU
  obtain ⟨P', hP', hP'c⟩ := nb0_cover_extend hU hwB (Finset.mem_insert_self u _) huB hu.symm
  have hins : insert w B = Finset.univ := Finset.insert_erase (Finset.mem_univ w)
  rw [hins] at hP'
  have hfinal : ((∀ t₁ ∈ P', ∀ t₂ ∈ P', t₁ ≠ t₂ → Disjoint t₁ t₂) ∧
      P'.biUnion id = (Finset.univ : Finset V) ∧
      (∀ t ∈ P', ∃ (u₀ v₀ : V) (q₀ : H.Walk u₀ v₀), q₀.IsPath ∧ t = q₀.support.toFinset ∧
        ∀ z₀ ∈ ({x, y} : Finset V), z₀ ∈ t → z₀ = u₀ ∨ z₀ = v₀)) := by
    refine ⟨hP'.1, hP'.2.1, fun t ht => ?_⟩
    obtain ⟨u₀, v₀, q₀, hq₀, ht₀, hz₀⟩ := hP'.2.2 t ht
    refine ⟨u₀, v₀, q₀, hq₀, ht₀, fun z hz hzt => hz₀ z ?_ hzt⟩
    have hzZ : z ∈ Z := Finset.mem_insert_of_mem hz
    have hzu : z ≠ u := by
      rcases Finset.mem_insert.mp hz with e | e
      · rw [e]; exact Ne.symm hux
      · rw [Finset.mem_singleton.mp e]; exact Ne.symm huy
    exact Finset.mem_erase.mpr ⟨hzu, hzZ⟩
  obtain ⟨hP, hcap⟩ := fmt_good le_rfl hfinal
  refine ⟨P', hP, hcap, ?_⟩
  have hf1 := nb0_forest_superadd H K R hKR hno
  rw [hBKR] at hf1
  have hf2 := nb0_forest_le_G H B
  have hPc : (PK ∪ PR).card ≤ PK.card + PR.card := Finset.card_union_le _ _
  have hKRc : K.card + R.card = B.card := by
    rw [← Finset.card_union_of_disjoint hKR, hBKR]
  omega

/-- Caps on vertices outside the covered set are free. -/
lemma cov_insert_cap (G : SimpleGraph V) {S : Finset V} {P : Finset (Finset V)} {Z : Finset V}
    (h : ((∀ t₁ ∈ P, ∀ t₂ ∈ P, t₁ ≠ t₂ → Disjoint t₁ t₂) ∧ P.biUnion id = S ∧
      (∀ t ∈ P, ∃ (u₀ v₀ : V) (q₀ : G.Walk u₀ v₀), q₀.IsPath ∧ t = q₀.support.toFinset ∧
        ∀ z₀ ∈ Z, z₀ ∈ t → z₀ = u₀ ∨ z₀ = v₀))) {z : V} (hz : z ∉ S) :
    ((∀ t₁ ∈ P, ∀ t₂ ∈ P, t₁ ≠ t₂ → Disjoint t₁ t₂) ∧ P.biUnion id = S ∧
      (∀ t ∈ P, ∃ (u₀ v₀ : V) (q₀ : G.Walk u₀ v₀), q₀.IsPath ∧ t = q₀.support.toFinset ∧
        ∀ z₀ ∈ insert z Z, z₀ ∈ t → z₀ = u₀ ∨ z₀ = v₀)) := by
  refine ⟨h.1, h.2.1, fun t ht => ?_⟩
  obtain ⟨u₀, v₀, q₀, hq₀, ht₀, hz₀⟩ := h.2.2 t ht
  refine ⟨u₀, v₀, q₀, hq₀, ht₀, fun z' hz' hzt => ?_⟩
  rcases Finset.mem_insert.mp hz' with e | e
  · subst e
    have : t ⊆ S := by rw [← h.2.1]; exact Finset.subset_biUnion_of_mem id ht
    exact (hz (this hzt)).elim
  · exact hz₀ z' e hzt

/-- Attaching a path `x … d` to a capped vertex `e` (adjacent to `d`) of a cover. -/
lemma attach_path (G : SimpleGraph V) (T : Finset V) (e : V) (he : e ∉ T) :
    ∀ {x d : V} (q : G.Walk x d), q.IsPath → G.Adj d e →
    ∀ (S : Finset V) (P : Finset (Finset V)), e ∈ S →
    (∀ z ∈ q.support, z ∉ S) → (∀ z ∈ q.support, z ∉ T) →
    ((∀ t₁ ∈ P, ∀ t₂ ∈ P, t₁ ≠ t₂ → Disjoint t₁ t₂) ∧ P.biUnion id = S ∧
      (∀ t ∈ P, ∃ (u₀ v₀ : V) (q₀ : G.Walk u₀ v₀), q₀.IsPath ∧ t = q₀.support.toFinset ∧
        ∀ z₀ ∈ insert e T, z₀ ∈ t → z₀ = u₀ ∨ z₀ = v₀)) →
    ∃ P' : Finset (Finset V),
      ((∀ t₁ ∈ P', ∀ t₂ ∈ P', t₁ ≠ t₂ → Disjoint t₁ t₂) ∧ P'.biUnion id = S ∪ q.support.toFinset ∧
      (∀ t ∈ P', ∃ (u₀ v₀ : V) (q₀ : G.Walk u₀ v₀), q₀.IsPath ∧ t = q₀.support.toFinset ∧
        ∀ z₀ ∈ insert x T, z₀ ∈ t → z₀ = u₀ ∨ z₀ = v₀)) ∧ P'.card = P.card := by
  intro x d q
  induction q with
  | @nil u =>
    intro _ hde S P heS hS _ hcov
    have hdS : u ∉ S := hS u (by simp)
    have h1 := cov_insert_cap G hcov hdS
    obtain ⟨P', hP', hc⟩ := nb0_cover_extend h1 hdS
      (Finset.mem_insert_of_mem (Finset.mem_insert_self e T)) heS hde
    have hZ : (insert u (insert e T)).erase e = insert u T := by
      rw [Finset.erase_insert_of_ne hde.ne, Finset.erase_insert he]
    rw [hZ] at hP'
    have hU : insert u S = S ∪ (Walk.nil : G.Walk u u).support.toFinset := by
      rw [Walk.support_nil, List.toFinset_cons, List.toFinset_nil, Finset.union_insert,
        Finset.union_empty]
    rw [hU] at hP'
    exact ⟨P', hP', hc⟩
  | @cons a b d' h q' ihq =>
    intro hq hde S P heS hS hT hcov
    have hq' : q'.IsPath := ((Walk.cons_isPath_iff h q').mp hq).1
    have haq' : a ∉ q'.support := ((Walk.cons_isPath_iff h q').mp hq).2
    obtain ⟨P1, hP1, hP1c⟩ := ihq hq' hde S P heS (fun z hz => hS z (by simp [hz]))
      (fun z hz => hT z (by simp [hz])) hcov
    have haS : a ∉ S ∪ q'.support.toFinset := by
      rw [Finset.mem_union, List.mem_toFinset]
      rintro (h' | h')
      · exact hS a (by simp) h'
      · exact haq' h'
    have h2 := cov_insert_cap G hP1 haS
    have hbS : b ∈ S ∪ q'.support.toFinset :=
      Finset.mem_union_right _ (List.mem_toFinset.mpr q'.start_mem_support)
    obtain ⟨P2, hP2, hP2c⟩ := nb0_cover_extend h2 haS
      (Finset.mem_insert_of_mem (Finset.mem_insert_self b T)) hbS h
    have hbT : b ∉ T := hT b (by simp)
    have hZ : (insert a (insert b T)).erase b = insert a T := by
      rw [Finset.erase_insert_of_ne h.ne, Finset.erase_insert hbT]
    rw [hZ] at hP2
    have hU : insert a (S ∪ q'.support.toFinset) = S ∪ (Walk.cons h q').support.toFinset := by
      rw [Walk.support_cons, List.toFinset_cons, Finset.union_insert]
    rw [hU] at hP2
    exact ⟨P2, hP2, hP2c.trans hP1c⟩

/-- The path step (bipartite peeling at an end): a path `q` from `x` to `d` avoiding `y`, with
`d` of the other colour than `x` and a neighbour `e` of `d` off the path, such that
`2 f(H - q) + |q| ≤ 2 f(H)` and `H - q` has an edge, gives `S2` for `x`, `y`. -/
lemma step_path (n : ℕ)
    (ih : (∀ (W : Type) [Fintype W] [DecidableEq W], Fintype.card W < n →
      ∀ (G : SimpleGraph W) (c : W → Fin 2), (∀ u v, G.Adj u v → c u ≠ c v) → G.Connected →
      ∀ x y : W, c x ≠ c y →
      ∃ P : Finset (Finset W), G.IsPathCover P ∧
      (∀ s ∈ P, ∃ (u v : W) (q : G.Walk u v), q.IsPath ∧ s = q.support.toFinset ∧
        (x ∈ s → x = u ∨ x = v) ∧ (y ∈ s → y = u ∨ y = v)) ∧
      P.card + Fintype.card W + 1 ≤ 2 * G.largestInducedForestSize))
    (hn : Fintype.card V = n) (H : SimpleGraph V) (c : V → Fin 2)
    (hc : ∀ u v, H.Adj u v → c u ≠ c v)
    (x y d e : V) (hxy : c x ≠ c y) (q : H.Walk x d) (hq : q.IsPath) (hyq : y ∉ q.support)
    (hcd : c d ≠ c x) (heq : e ∉ q.support) (hde : H.Adj d e)
    (hedge : ∃ a b, a ∉ q.support ∧ b ∉ q.support ∧ H.Adj a b)
    (hf : 2 * (H.induce {z | z ∉ q.support}).largestInducedForestSize + q.length + 1 ≤
      2 * H.largestInducedForestSize) :
    ∃ P : Finset (Finset V), H.IsPathCover P ∧
      (∀ s ∈ P, ∃ (u v : V) (q : H.Walk u v), q.IsPath ∧ s = q.support.toFinset ∧
        (x ∈ s → x = u ∨ x = v) ∧ (y ∈ s → y = u ∨ y = v)) ∧
      P.card + Fintype.card V + 1 ≤ 2 * H.largestInducedForestSize := by
  classical
  set X : Finset V := q.support.toFinset with hXdef
  set B : Finset V := Finset.univ \ X with hBdef
  have hmemB : ∀ z, z ∈ B ↔ z ∉ q.support := fun z => by simp [B, X]
  have hBset : ((B : Finset V) : Set V) = {z | z ∉ q.support} := by
    ext z
    simp [B, X]
  have hXcard : X.card = q.length + 1 := by
    rw [hXdef, List.toFinset_card_of_nodup hq.support_nodup, Walk.length_support]
  have hcardB : B.card + X.card = n := by
    rw [hBdef, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, hn]
    have := Finset.card_le_univ X
    omega
  have hfB : 2 * (H.induce (B : Set V)).largestInducedForestSize + q.length + 1 ≤
      2 * H.largestInducedForestSize := by
    rw [hBset]
    exact hf
  have hce : c e = c x := s2b_fin2 _ _ _ (hc d e hde).symm hcd
  have hey : e ≠ y := fun h => hxy (by rw [← hce, h])
  have heB : e ∈ B := (hmemB e).mpr heq
  have hyB : y ∈ B := (hmemB y).mpr hyq
  have hZ : ∀ z1 ∈ insert e ({y} : Finset V), ∀ z2 ∈ insert e ({y} : Finset V), z1 ≠ z2 →
      (∃ (hx₀ : z1 ∈ B) (hy₀ : z2 ∈ B), (H.induce (B : Set V)).Reachable ⟨z1, hx₀⟩ ⟨z2, hy₀⟩) →
      c z1 ≠ c z2 := by
    intro z1 h1 z2 h2 hne _
    simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2
    rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl
    · exact (hne rfl).elim
    · rw [hce]; exact hxy
    · rw [hce]; exact fun h => hxy h.symm
    · exact (hne rfl).elim
  obtain ⟨P0, hP0, -, hP0e⟩ := comp_all n ih H c B.card B rfl (by omega)
    (fun p _ q _ h => hc p q h) (insert e {y}) hZ
  obtain ⟨a, b, ha, hb, hab⟩ := hedge
  have hP0e' := hP0e ⟨a, (hmemB a).mpr ha, b, (hmemB b).mpr hb, hab⟩
  obtain ⟨P', hP', hP'c⟩ := attach_path H {y} e (by simpa using hey) q hq hde B P0 heB
    (fun z hz hzB => ((hmemB z).mp hzB) hz)
    (fun z hz hzy => hyq (Finset.mem_singleton.mp hzy ▸ hz)) hP0
  have hU : B ∪ q.support.toFinset = Finset.univ := by
    ext z
    simp only [Finset.mem_union, Finset.mem_univ, iff_true, List.mem_toFinset]
    by_cases h : z ∈ q.support
    · exact Or.inr h
    · exact Or.inl ((hmemB z).mpr h)
  rw [hU] at hP'
  obtain ⟨hP, hcap⟩ := fmt_good le_rfl hP'
  refine ⟨P', hP, hcap, ?_⟩
  omega

lemma s2t_four (G : SimpleGraph V) (col : V → Fin 2) (hcol : ∀ u v, G.Adj u v → col u ≠ col v)
    {w : V} (c : G.Walk w w) (hc : c.IsCycle) (x y : V) (hx : x ∈ c.support → x = w)
    (hy : y ∈ c.support → col w ≠ col y) :
    ∃ a u v b : V, G.Adj a u ∧ G.Adj u v ∧ G.Adj v b ∧ [a, u, v, b].Nodup ∧
      u ≠ x ∧ u ≠ y ∧ v ≠ x ∧ v ≠ y ∧
      a ∈ c.support ∧ u ∈ c.support ∧ v ∈ c.support ∧ b ∈ c.support := by
  match c, hc with
  | .nil, hc => exact absurd hc Walk.not_isCycle_nil
  | .cons h1 .nil, _ => exact absurd h1 G.irrefl
  | .cons h1 (.cons h2 .nil), hc =>
    rw [Walk.cons_isCycle_iff] at hc
    exact absurd (by simp [Sym2.eq_swap]) hc.2
  | .cons h1 (.cons h2 (.cons h3 .nil)), _ =>
    exact absurd (s2b_fin2 _ _ _ (hcol _ _ h1) (hcol _ _ h2)) (hcol _ _ h3).symm
  | .cons (v := g1) h1 (.cons (v := g2) h2 (.cons (v := g3) h3 (.cons (v := g4) h4 p))), hc =>
    have hq := ((Walk.cons_isCycle_iff _ _).mp hc).1
    rw [Walk.isPath_def] at hq
    simp only [Walk.support_cons, List.nodup_cons, List.mem_cons, not_or] at hq
    have hg4 : g4 ∈ p.support := p.start_mem_support
    have hw : w ∈ p.support := p.end_mem_support
    have hs : ∀ z, z = w ∨ z = g1 ∨ z = g2 ∨ z = g3 ∨ z = g4 →
        z ∈ (Walk.cons h1 (.cons h2 (.cons h3 (.cons h4 p)))).support := by
      rintro z (rfl | rfl | rfl | rfl | rfl) <;> simp [hg4]
    have c1 := hcol _ _ h1
    have c2 := hcol _ _ h2
    have h2y : g2 ≠ y := by
      intro e
      have := hy (e ▸ hs g2 (by simp))
      rw [← e] at this
      exact this (s2b_fin2 _ _ _ c1 c2)
    by_cases h1y : g1 = y
    · refine ⟨g1, g2, g3, g4, h2, h3, h4, ?_, ?_, h2y, ?_, ?_, hs _ (by simp), hs _ (by simp),
        hs _ (by simp), hs _ (by simp)⟩
      · simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil,
          List.nodup_nil, not_false_eq_true, and_true]
        grind
      · intro e; have := hx (e ▸ hs g2 (by simp)); grind
      · intro e; have := hx (e ▸ hs g3 (by simp)); grind
      · intro e; grind
    · refine ⟨w, g1, g2, g3, h1, h2, h3, ?_, ?_, h1y, ?_, h2y, hs _ (by simp), hs _ (by simp),
        hs _ (by simp), hs _ (by simp)⟩
      · simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil,
          List.nodup_nil, not_false_eq_true, and_true]
        grind
      · intro e; have := hx (e ▸ hs g1 (by simp)); grind
      · intro e; have := hx (e ▸ hs g2 (by simp)); grind

/-- Rotation-free form: any cycle, any pair of different colours. -/
lemma s2t_four' (G : SimpleGraph V) (col : V → Fin 2) (hcol : ∀ u v, G.Adj u v → col u ≠ col v)
    {w : V} (c : G.Walk w w) (hc : c.IsCycle) (x y : V) (hxy : col x ≠ col y) :
    ∃ a u v b : V, G.Adj a u ∧ G.Adj u v ∧ G.Adj v b ∧ [a, u, v, b].Nodup ∧
      u ≠ x ∧ u ≠ y ∧ v ≠ x ∧ v ≠ y ∧
      a ∈ c.support ∧ u ∈ c.support ∧ v ∈ c.support ∧ b ∈ c.support := by
  by_cases hxc : x ∈ c.support
  · obtain ⟨a, u, v, b, h1, h2, h3, hnd, h4, h5, h6, h7, m1, m2, m3, m4⟩ :=
      s2t_four G col hcol (c.rotate x hxc) (hc.rotate hxc) x y (fun _ => rfl) (fun _ => hxy)
    simp only [Walk.mem_support_rotate_iff] at m1 m2 m3 m4
    exact ⟨a, u, v, b, h1, h2, h3, hnd, h4, h5, h6, h7, m1, m2, m3, m4⟩
  · by_cases hyc : y ∈ c.support
    · obtain ⟨a, u, v, b, h1, h2, h3, hnd, h4, h5, h6, h7, m1, m2, m3, m4⟩ :=
        s2t_four G col hcol (c.rotate y hyc) (hc.rotate hyc) y x (fun _ => rfl)
          (fun _ => hxy.symm)
      simp only [Walk.mem_support_rotate_iff] at m1 m2 m3 m4
      exact ⟨a, u, v, b, h1, h2, h3, hnd, h5, h4, h7, h6, m1, m2, m3, m4⟩
    · exact s2t_four G col hcol c hc x y (fun h => absurd h hxc) (fun h => absurd h hyc)

/-- Two disjoint paths plus singletons. -/
lemma s2t_cover2 (G : SimpleGraph V) (x y : V) {a b a' b' : V} (q : G.Walk a b) (hq : q.IsPath)
    (q' : G.Walk a' b') (hq' : q'.IsPath) (hdisj : Disjoint q.support.toFinset q'.support.toFinset)
    (hx : x ∈ q.support.toFinset → x = a ∨ x = b) (hy : y ∈ q.support.toFinset → y = a ∨ y = b)
    (hx' : x ∈ q'.support.toFinset → x = a' ∨ x = b')
    (hy' : y ∈ q'.support.toFinset → y = a' ∨ y = b') :
    ∃ P : Finset (Finset V), G.IsPathCover P ∧
      (∀ s ∈ P, ∃ (u v : V) (r : G.Walk u v), r.IsPath ∧ s = r.support.toFinset ∧
        (x ∈ s → x = u ∨ x = v) ∧ (y ∈ s → y = u ∨ y = v)) ∧
      P.card + q.support.toFinset.card + q'.support.toFinset.card = Fintype.card V + 2 := by
  set S := q.support.toFinset with hSdef
  set S' := q'.support.toFinset with hS'def
  set R := (Finset.univ \ (S ∪ S')).image (fun v => ({v} : Finset V)) with hRdef
  have hmem : ∀ s ∈ insert S (insert S' R), s = S ∨ s = S' ∨ ∃ v, v ∉ S ∧ v ∉ S' ∧ s = {v} := by
    intro s hs
    rw [Finset.mem_insert, Finset.mem_insert, hRdef, Finset.mem_image] at hs
    rcases hs with h | h | ⟨v, hv, rfl⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_union, not_or, true_and] at hv
      exact Or.inr (Or.inr ⟨v, hv.1, hv.2, rfl⟩)
  have haS : a ∈ S := by simp [hSdef]
  have ha'S' : a' ∈ S' := by simp [hS'def]
  have hSS' : S ≠ S' := by
    intro e
    exact Finset.disjoint_left.mp hdisj haS (by rw [← e]; exact haS)
  have hSR : S ∉ R := by
    intro h
    rw [hRdef, Finset.mem_image] at h
    obtain ⟨v, hv, hvS⟩ := h
    have : v ∈ S := hvS ▸ Finset.mem_singleton_self v
    simp [this] at hv
  have hS'R : S' ∉ R := by
    intro h
    rw [hRdef, Finset.mem_image] at h
    obtain ⟨v, hv, hvS⟩ := h
    have : v ∈ S' := hvS ▸ Finset.mem_singleton_self v
    simp [this] at hv
  refine ⟨insert S (insert S' R), ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro s1 h1 s2 h2 hne
    rcases hmem s1 h1 with rfl | rfl | ⟨v1, hv1, hv1', rfl⟩ <;>
      rcases hmem s2 h2 with rfl | rfl | ⟨v2, hv2, hv2', rfl⟩
    · exact absurd rfl hne
    · exact hdisj
    · exact Finset.disjoint_singleton_right.mpr hv2
    · exact hdisj.symm
    · exact absurd rfl hne
    · exact Finset.disjoint_singleton_right.mpr hv2'
    · exact Finset.disjoint_singleton_left.mpr hv1
    · exact Finset.disjoint_singleton_left.mpr hv1'
    · refine Finset.disjoint_singleton.mpr ?_
      intro e; exact hne (e ▸ rfl)
  · intro v _
    rw [Finset.mem_biUnion]
    by_cases hv : v ∈ S
    · exact ⟨S, Finset.mem_insert_self _ _, hv⟩
    · by_cases hv' : v ∈ S'
      · exact ⟨S', Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), hv'⟩
      · exact ⟨{v}, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (by rw [hRdef, Finset.mem_image]; exact ⟨v, by simp [hv, hv'], rfl⟩)),
          Finset.mem_singleton_self v⟩
  · intro s hs
    rcases hmem s hs with rfl | rfl | ⟨v, _, _, rfl⟩
    · exact ⟨a, b, q, hq, rfl⟩
    · exact ⟨a', b', q', hq', rfl⟩
    · exact ⟨v, v, Walk.nil, Walk.IsPath.nil, by simp⟩
  · intro s hs
    rcases hmem s hs with rfl | rfl | ⟨v, _, _, rfl⟩
    · exact ⟨a, b, q, hq, rfl, hx, hy⟩
    · exact ⟨a', b', q', hq', rfl, hx', hy'⟩
    · refine ⟨v, v, Walk.nil, Walk.IsPath.nil, by simp, ?_, ?_⟩
      · intro h; left; simpa using h
      · intro h; left; simpa using h
  · have hS'nR : S ∉ insert S' R := by
      rw [Finset.mem_insert, not_or]; exact ⟨hSS', hSR⟩
    rw [Finset.card_insert_of_notMem hS'nR, Finset.card_insert_of_notMem hS'R, hRdef,
      Finset.card_image_of_injective _ (fun u v h => by simpa using h),
      Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
      Finset.card_union_of_disjoint hdisj]
    have : (S ∪ S').card ≤ Fintype.card V := Finset.card_le_univ _
    rw [Finset.card_union_of_disjoint hdisj] at this
    omega

lemma s2t_swap (H : SimpleGraph V) (x y : V)
    (h : (∃ P : Finset (Finset V), H.IsPathCover P ∧
      (∀ s ∈ P, ∃ (u v : V) (r : H.Walk u v), r.IsPath ∧ s = r.support.toFinset ∧
        (x ∈ s → x = u ∨ x = v) ∧ (y ∈ s → y = u ∨ y = v)) ∧
      P.card + 5 ≤ Fintype.card V)) : (∃ P : Finset (Finset V), H.IsPathCover P ∧
      (∀ s ∈ P, ∃ (u v : V) (r : H.Walk u v), r.IsPath ∧ s = r.support.toFinset ∧
        (y ∈ s → y = u ∨ y = v) ∧ (x ∈ s → x = u ∨ x = v)) ∧
      P.card + 5 ≤ Fintype.card V) := by
  obtain ⟨P, hP, he, hc⟩ := h
  refine ⟨P, hP, ?_, hc⟩
  intro s hs
  obtain ⟨u, v, r, hr, hs', h1, h2⟩ := he s hs
  exact ⟨u, v, r, hr, hs', h2, h1⟩

/-- A path on six vertices whose four inner vertices avoid `x` and `y`. -/
lemma s2t_path6 (H : SimpleGraph V) (x y : V) {a0 a1 a2 a3 a4 a5 : V}
    (h01 : H.Adj a0 a1) (h12 : H.Adj a1 a2) (h23 : H.Adj a2 a3) (h34 : H.Adj a3 a4)
    (h45 : H.Adj a4 a5) (hnd : [a0, a1, a2, a3, a4, a5].Nodup)
    (i1 : a1 ≠ x ∧ a1 ≠ y) (i2 : a2 ≠ x ∧ a2 ≠ y) (i3 : a3 ≠ x ∧ a3 ≠ y) (i4 : a4 ≠ x ∧ a4 ≠ y) :
    (∃ P : Finset (Finset V), H.IsPathCover P ∧
      (∀ s ∈ P, ∃ (u v : V) (r : H.Walk u v), r.IsPath ∧ s = r.support.toFinset ∧
        (x ∈ s → x = u ∨ x = v) ∧ (y ∈ s → y = u ∨ y = v)) ∧
      P.card + 5 ≤ Fintype.card V) := by
  let q : H.Walk a0 a5 := Walk.cons h01 (Walk.cons h12 (Walk.cons h23 (Walk.cons h34
    (Walk.cons h45 Walk.nil))))
  have hs : q.support = [a0, a1, a2, a3, a4, a5] := rfl
  have hq : q.IsPath := by rw [Walk.isPath_def, hs]; exact hnd
  obtain ⟨P, hP, he, hc⟩ := s2b_cover H x y q hq
    (by intro h; rw [hs] at h; simp at h; grind) (by intro h; rw [hs] at h; simp at h; grind)
  refine ⟨P, hP, he, ?_⟩
  have : q.support.toFinset.card = 6 := by
    rw [List.toFinset_card_of_nodup (hs ▸ hnd), hs]; rfl
  omega

/-- A path on four vertices and a disjoint path on three vertices, inner vertices avoiding `x`, `y`. -/
lemma s2t_path43 (H : SimpleGraph V) (x y : V) {a0 a1 a2 a3 b0 b1 b2 : V}
    (h01 : H.Adj a0 a1) (h12 : H.Adj a1 a2) (h23 : H.Adj a2 a3)
    (k01 : H.Adj b0 b1) (k12 : H.Adj b1 b2) (hnd : [a0, a1, a2, a3, b0, b1, b2].Nodup)
    (i1 : a1 ≠ x ∧ a1 ≠ y) (i2 : a2 ≠ x ∧ a2 ≠ y) (j1 : b1 ≠ x ∧ b1 ≠ y) :
    (∃ P : Finset (Finset V), H.IsPathCover P ∧
      (∀ s ∈ P, ∃ (u v : V) (r : H.Walk u v), r.IsPath ∧ s = r.support.toFinset ∧
        (x ∈ s → x = u ∨ x = v) ∧ (y ∈ s → y = u ∨ y = v)) ∧
      P.card + 5 ≤ Fintype.card V) := by
  let q : H.Walk a0 a3 := Walk.cons h01 (Walk.cons h12 (Walk.cons h23 Walk.nil))
  let q' : H.Walk b0 b2 := Walk.cons k01 (Walk.cons k12 Walk.nil)
  have hs : q.support = [a0, a1, a2, a3] := rfl
  have hs' : q'.support = [b0, b1, b2] := rfl
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil,
    List.nodup_nil, not_false_eq_true, and_true] at hnd
  have hnd1 : [a0, a1, a2, a3].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil,
      List.nodup_nil, not_false_eq_true, and_true]; grind
  have hnd2 : [b0, b1, b2].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil,
      List.nodup_nil, not_false_eq_true, and_true]; grind
  have hq : q.IsPath := by rw [Walk.isPath_def, hs]; exact hnd1
  have hq' : q'.IsPath := by rw [Walk.isPath_def, hs']; exact hnd2
  have hdisj : Disjoint q.support.toFinset q'.support.toFinset := by
    rw [hs, hs', Finset.disjoint_left]
    intro z hz hz'
    simp only [List.mem_toFinset, List.mem_cons, List.not_mem_nil,
      or_false] at hz hz'
    grind
  obtain ⟨P, hP, he, hc⟩ := s2t_cover2 H x y q hq q' hq' hdisj
    (by intro h; rw [hs] at h; simp at h; grind) (by intro h; rw [hs] at h; simp at h; grind)
    (by intro h; rw [hs'] at h; simp at h; grind) (by intro h; rw [hs'] at h; simp at h; grind)
  refine ⟨P, hP, he, ?_⟩
  have e1 : q.support.toFinset.card = 4 := by
    rw [List.toFinset_card_of_nodup (hs ▸ hnd1), hs]; rfl
  have e2 : q'.support.toFinset.card = 3 := by
    rw [List.toFinset_card_of_nodup (hs' ▸ hnd2), hs']; rfl
  omega

/-- A vertex of a cycle has two different neighbours on the cycle. -/
lemma s2t_cycnbr (G : SimpleGraph V) {w : V} (c : G.Walk w w) (hc : c.IsCycle) {v : V}
    (hv : v ∈ c.support) :
    ∃ u1 u2 : V, u1 ≠ u2 ∧ G.Adj v u1 ∧ G.Adj v u2 ∧ u1 ∈ c.support ∧ u2 ∈ c.support := by
  set c' := c.rotate v hv with hc'
  have hcc : c'.IsCycle := hc.rotate hv
  have hnn : ¬ c'.Nil := hcc.not_nil
  refine ⟨c'.snd, c'.penultimate, hcc.snd_ne_penultimate, c'.adj_snd hnn,
    (c'.adj_penultimate hnn).symm, ?_, ?_⟩
  · have := c'.getVert_mem_support 1
    rw [hc', Walk.mem_support_rotate_iff] at this
    exact this
  · have := c'.getVert_mem_support (c'.length - 1)
    rw [hc', Walk.mem_support_rotate_iff] at this
    exact this

/-- The hexagon case: `x a b y c d` is a 6-cycle and `x`, `y` are antipodal on it. -/
lemma s2t_hex (H : SimpleGraph V) (col : V → Fin 2) (hcol : ∀ u v, H.Adj u v → col u ≠ col v)
    (havoid : ∀ v : V, ∃ (w : V) (c : H.Walk w w), c.IsCycle ∧ v ∉ c.support)
    (x y : V) (hxy : col x ≠ col y) {a b c d : V}
    (hxa : H.Adj x a) (hab : H.Adj a b) (hby : H.Adj b y) (hyc : H.Adj y c) (hcd : H.Adj c d)
    (hdx : H.Adj d x) (hnd : [x, a, b, y, c, d].Nodup) :
    (∃ P : Finset (Finset V), H.IsPathCover P ∧
      (∀ s ∈ P, ∃ (u v : V) (r : H.Walk u v), r.IsPath ∧ s = r.support.toFinset ∧
        (x ∈ s → x = u ∨ x = v) ∧ (y ∈ s → y = u ∨ y = v)) ∧
      P.card + 5 ≤ Fintype.card V) := by
  have cxa := hcol _ _ hxa
  have cab := hcol _ _ hab
  have cby := hcol _ _ hby
  have cyc := hcol _ _ hyc
  have ccd := hcol _ _ hcd
  have cdx := hcol _ _ hdx
  have hnd' := hnd
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil,
    List.nodup_nil, not_false_eq_true, and_true] at hnd'
  by_cases hac : H.Adj a c
  · exact s2t_path6 H x y hby.symm hab.symm hac hcd hdx
      (by simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil,
        List.nodup_nil, not_false_eq_true, and_true]; grind)
      (by grind) (by grind) (by grind) (by grind)
  by_cases hbd : H.Adj b d
  · exact s2t_path6 H x y hxa hab hbd hcd.symm hyc.symm
      (by simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil,
        List.nodup_nil, not_false_eq_true, and_true]; grind)
      (by grind) (by grind) (by grind) (by grind)
  by_cases ea : ∃ z, H.Adj a z ∧ z ≠ x ∧ z ≠ a ∧ z ≠ b ∧ z ≠ y ∧ z ≠ c ∧ z ≠ d
  · obtain ⟨z, hz, z1, z2, z3, z4, z5, z6⟩ := ea
    exact s2t_path43 H x y hz.symm hab hby hdx.symm hcd.symm
      (by simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil,
        List.nodup_nil, not_false_eq_true, and_true]; grind)
      (by grind) (by grind) (by grind)
  by_cases eb : ∃ z, H.Adj b z ∧ z ≠ x ∧ z ≠ a ∧ z ≠ b ∧ z ≠ y ∧ z ≠ c ∧ z ≠ d
  · obtain ⟨z, hz, z1, z2, z3, z4, z5, z6⟩ := eb
    exact s2t_path43 H x y hz.symm hab.symm hxa.symm hyc hcd
      (by simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil,
        List.nodup_nil, not_false_eq_true, and_true]; grind)
      (by grind) (by grind) (by grind)
  by_cases ec : ∃ z, H.Adj c z ∧ z ≠ x ∧ z ≠ a ∧ z ≠ b ∧ z ≠ y ∧ z ≠ c ∧ z ≠ d
  · obtain ⟨z, hz, z1, z2, z3, z4, z5, z6⟩ := ec
    exact s2t_path43 H x y hz.symm hcd hdx hby.symm hab.symm
      (by simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil,
        List.nodup_nil, not_false_eq_true, and_true]; grind)
      (by grind) (by grind) (by grind)
  by_cases ed : ∃ z, H.Adj d z ∧ z ≠ x ∧ z ≠ a ∧ z ≠ b ∧ z ≠ y ∧ z ≠ c ∧ z ≠ d
  · obtain ⟨z, hz, z1, z2, z3, z4, z5, z6⟩ := ed
    exact s2t_path43 H x y hz.symm hcd.symm hyc.symm hxa hab
      (by simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil,
        List.nodup_nil, not_false_eq_true, and_true]; grind)
      (by grind) (by grind) (by grind)
  push Not at ea eb ec ed
  -- neighbourhoods of `a b c d` inside the hexagon
  have na : ∀ z, H.Adj a z → z = x ∨ z = b := by
    intro z hz
    have cz := hcol _ _ hz
    by_cases z1 : z = x
    · exact Or.inl z1
    by_cases z3 : z = b
    · exact Or.inr z3
    exfalso
    have z2 : z ≠ a := fun e => H.irrefl (e ▸ hz)
    have z4 : z ≠ y := by intro e; subst e; grind
    have z5 : z ≠ c := by intro e; subst e; exact hac hz
    have z6 : z ≠ d := by intro e; subst e; grind
    exact z6 (ea z hz z1 z2 z3 z4 z5)
  have nb : ∀ z, H.Adj b z → z = a ∨ z = y := by
    intro z hz
    have cz := hcol _ _ hz
    by_cases z2 : z = a
    · exact Or.inl z2
    by_cases z4 : z = y
    · exact Or.inr z4
    exfalso
    have z1 : z ≠ x := by intro e; subst e; grind
    have z3 : z ≠ b := fun e => H.irrefl (e ▸ hz)
    have z5 : z ≠ c := by intro e; subst e; grind
    have z6 : z ≠ d := by intro e; subst e; exact hbd hz
    exact z6 (eb z hz z1 z2 z3 z4 z5)
  have nc : ∀ z, H.Adj c z → z = y ∨ z = d := by
    intro z hz
    have cz := hcol _ _ hz
    by_cases z4 : z = y
    · exact Or.inl z4
    by_cases z6 : z = d
    · exact Or.inr z6
    exfalso
    have z1 : z ≠ x := by intro e; subst e; grind
    have z2 : z ≠ a := by intro e; subst e; exact hac hz.symm
    have z3 : z ≠ b := by intro e; subst e; grind
    have z5 : z ≠ c := fun e => H.irrefl (e ▸ hz)
    exact z6 (ec z hz z1 z2 z3 z4 z5)
  have nd : ∀ z, H.Adj d z → z = c ∨ z = x := by
    intro z hz
    have cz := hcol _ _ hz
    by_cases z5 : z = c
    · exact Or.inl z5
    by_cases z1 : z = x
    · exact Or.inr z1
    exfalso
    have z2 : z ≠ a := by intro e; subst e; grind
    have z3 : z ≠ b := by intro e; subst e; exact hbd hz.symm
    have z4 : z ≠ y := by intro e; subst e; grind
    have z6 : z ≠ d := fun e => H.irrefl (e ▸ hz)
    exact z6 (ed z hz z1 z2 z3 z4 z5)
  obtain ⟨w, C, hC, hxC⟩ := havoid x
  have haC : a ∉ C.support := by
    intro h
    obtain ⟨u1, u2, hne, h1, h2, m1, m2⟩ := s2t_cycnbr H C hC h
    rcases na u1 h1 with rfl | rfl
    · exact hxC m1
    rcases na u2 h2 with rfl | rfl
    · exact hxC m2
    exact hne rfl
  have hdC : d ∉ C.support := by
    intro h
    obtain ⟨u1, u2, hne, h1, h2, m1, m2⟩ := s2t_cycnbr H C hC h
    rcases nd u1 h1 with rfl | rfl
    · rcases nd u2 h2 with rfl | rfl
      · exact hne rfl
      · exact hxC m2
    · exact hxC m1
  have hbC : b ∉ C.support := by
    intro h
    obtain ⟨u1, u2, hne, h1, h2, m1, m2⟩ := s2t_cycnbr H C hC h
    rcases nb u1 h1 with rfl | rfl
    · exact haC m1
    rcases nb u2 h2 with rfl | rfl
    · exact haC m2
    exact hne rfl
  obtain ⟨p0, p1, p2, p3, h1, h2, h3, hpn, u1, u2, u3, u4, m0, m1, m2, m3⟩ :=
    s2t_four' H col hcol C hC x y hxy
  have q0 : p0 ≠ x ∧ p0 ≠ a ∧ p0 ≠ b := ⟨fun e => hxC (e ▸ m0), fun e => haC (e ▸ m0),
    fun e => hbC (e ▸ m0)⟩
  have q1 : p1 ≠ x ∧ p1 ≠ a ∧ p1 ≠ b := ⟨fun e => hxC (e ▸ m1), fun e => haC (e ▸ m1),
    fun e => hbC (e ▸ m1)⟩
  have q2 : p2 ≠ x ∧ p2 ≠ a ∧ p2 ≠ b := ⟨fun e => hxC (e ▸ m2), fun e => haC (e ▸ m2),
    fun e => hbC (e ▸ m2)⟩
  have q3 : p3 ≠ x ∧ p3 ≠ a ∧ p3 ≠ b := ⟨fun e => hxC (e ▸ m3), fun e => haC (e ▸ m3),
    fun e => hbC (e ▸ m3)⟩
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil,
    List.nodup_nil, not_false_eq_true, and_true] at hpn
  exact s2t_path43 H x y h1 h2 h3 hxa hab
    (by simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil,
      List.nodup_nil, not_false_eq_true, and_true]; grind)
    ⟨u1, u2⟩ ⟨u3, u4⟩ (by grind)

/-- A cycle of length at least six, with `x` only possibly at the start, gives five path edges. -/
lemma s2t_big6 (H : SimpleGraph V) (col : V → Fin 2) (hcol : ∀ u v, H.Adj u v → col u ≠ col v)
    (havoid : ∀ v : V, ∃ (w : V) (c : H.Walk w w), c.IsCycle ∧ v ∉ c.support)
    (x y : V) (hxy : col x ≠ col y) {w : V} (c : H.Walk w w) (hc : c.IsCycle)
    (hlen : 6 ≤ c.length) (hx : x ∈ c.support → x = w) (hy : y ∈ c.support → col w ≠ col y) :
    (∃ P : Finset (Finset V), H.IsPathCover P ∧
      (∀ s ∈ P, ∃ (u v : V) (r : H.Walk u v), r.IsPath ∧ s = r.support.toFinset ∧
        (x ∈ s → x = u ∨ x = v) ∧ (y ∈ s → y = u ∨ y = v)) ∧
      P.card + 5 ≤ Fintype.card V) := by
  match c, hc, hlen with
  | .nil, _, hlen => simp at hlen
  | .cons _ .nil, _, hlen => simp at hlen
  | .cons _ (.cons _ .nil), _, hlen => simp at hlen
  | .cons _ (.cons _ (.cons _ .nil)), _, hlen => simp at hlen
  | .cons _ (.cons _ (.cons _ (.cons _ .nil))), _, hlen => simp at hlen
  | .cons _ (.cons _ (.cons _ (.cons _ (.cons _ .nil)))), _, hlen => simp at hlen
  | .cons (v := g1) h1 (.cons (v := g2) h2 (.cons (v := g3) h3 (.cons (v := g4) h4
      (.cons (v := g5) h5 (.cons (v := g6) h6 p))))), hc, _ =>
    have hq := ((Walk.cons_isCycle_iff _ _).mp hc).1
    rw [Walk.isPath_def] at hq
    simp only [Walk.support_cons, List.nodup_cons, List.mem_cons, not_or] at hq
    have hg6 : g6 ∈ p.support := p.start_mem_support
    have hw : w ∈ p.support := p.end_mem_support
    obtain ⟨⟨n12, n13, n14, n15, n1p⟩, ⟨n23, n24, n25, n2p⟩, ⟨n34, n35, n3p⟩, ⟨n45, n4p⟩, n5p, _⟩ := hq
    have n16 : g1 ≠ g6 := fun e => n1p (e ▸ hg6)
    have n26 : g2 ≠ g6 := fun e => n2p (e ▸ hg6)
    have n36 : g3 ≠ g6 := fun e => n3p (e ▸ hg6)
    have n46 : g4 ≠ g6 := fun e => n4p (e ▸ hg6)
    have n56 : g5 ≠ g6 := fun e => n5p (e ▸ hg6)
    have n1w : g1 ≠ w := fun e => n1p (e ▸ hw)
    have n2w : g2 ≠ w := fun e => n2p (e ▸ hw)
    have n3w : g3 ≠ w := fun e => n3p (e ▸ hw)
    have n4w : g4 ≠ w := fun e => n4p (e ▸ hw)
    have n5w : g5 ≠ w := fun e => n5p (e ▸ hw)
    have hs : ∀ z, z = w ∨ z = g1 ∨ z = g2 ∨ z = g3 ∨ z = g4 ∨ z = g5 ∨ z = g6 →
        z ∈ (Walk.cons h1 (.cons h2 (.cons h3 (.cons h4 (.cons h5 (.cons h6 p)))))).support := by
      rintro z (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> simp [hg6]
    have c1 := hcol _ _ h1
    have c2 := hcol _ _ h2
    have c3 := hcol _ _ h3
    have c4 := hcol _ _ h4
    have x1 : g1 ≠ x := fun e => n1w (e.trans (hx (e ▸ hs g1 (by simp))))
    have x2 : g2 ≠ x := fun e => n2w (e.trans (hx (e ▸ hs g2 (by simp))))
    have x3 : g3 ≠ x := fun e => n3w (e.trans (hx (e ▸ hs g3 (by simp))))
    have x4 : g4 ≠ x := fun e => n4w (e.trans (hx (e ▸ hs g4 (by simp))))
    have x5 : g5 ≠ x := fun e => n5w (e.trans (hx (e ▸ hs g5 (by simp))))
    have y2 : g2 ≠ y := by
      intro e
      have := hy (e ▸ hs g2 (by simp))
      rw [← e] at this
      grind
    have y4 : g4 ≠ y := by
      intro e
      have := hy (e ▸ hs g4 (by simp))
      rw [← e] at this
      grind
    by_cases y1 : g1 = y
    · exact s2t_path6 H x y h2 h3 h4 h5 h6
        (by simp only [List.nodup_cons, List.mem_cons, not_or,
          List.not_mem_nil, List.nodup_nil, not_false_eq_true, and_true]; grind)
        ⟨x2, fun e => n12 (y1.trans e.symm)⟩ ⟨x3, fun e => n13 (y1.trans e.symm)⟩
        ⟨x4, fun e => n14 (y1.trans e.symm)⟩ ⟨x5, fun e => n15 (y1.trans e.symm)⟩
    by_cases y3 : g3 = y
    · by_cases h6w : g6 = w
      · subst h6w
        by_cases hxw : x = g6
        · subst hxw
          exact s2t_hex H col hcol havoid x y hxy h1 h2 (y3 ▸ h3) (y3 ▸ h4) h5 h6
            (by rw [← y3]; simp only [List.nodup_cons, List.mem_cons, not_or,
              List.not_mem_nil, List.nodup_nil, not_false_eq_true, and_true]; grind)
        · have x0 : g6 ≠ x := fun e => hxw e.symm
          exact s2t_path6 H x y h4 h5 h6 h1 h2
            (by simp only [List.nodup_cons, List.mem_cons, not_or,
              List.not_mem_nil, List.nodup_nil, not_false_eq_true, and_true]; grind)
            ⟨x4, y4⟩ ⟨x5, fun e => n35 (y3.trans e.symm)⟩ ⟨x0, fun e => n36 (y3.trans e.symm)⟩
            ⟨x1, fun e => n13 (e.trans y3.symm)⟩
      · exact s2t_path43 H x y h4 h5 h6 h1 h2
          (by simp only [List.nodup_cons, List.mem_cons, not_or,
            List.not_mem_nil, List.nodup_nil, not_false_eq_true, and_true]; grind)
          ⟨x4, fun e => n34 (y3.trans e.symm)⟩ ⟨x5, fun e => n35 (y3.trans e.symm)⟩ ⟨x1, y1⟩
    · exact s2t_path6 H x y h1 h2 h3 h4 h5
        (by simp only [List.nodup_cons, List.mem_cons, not_or,
          List.not_mem_nil, List.nodup_nil, not_false_eq_true, and_true]; grind)
        ⟨x1, y1⟩ ⟨x2, y2⟩ ⟨x3, y3⟩ ⟨x4, y4⟩

/-- Any cycle of length at least six. -/
lemma s2t_big6' (H : SimpleGraph V) (col : V → Fin 2) (hcol : ∀ u v, H.Adj u v → col u ≠ col v)
    (havoid : ∀ v : V, ∃ (w : V) (c : H.Walk w w), c.IsCycle ∧ v ∉ c.support)
    (x y : V) (hxy : col x ≠ col y) {w : V} (c : H.Walk w w) (hc : c.IsCycle)
    (hlen : 6 ≤ c.length) : (∃ P : Finset (Finset V), H.IsPathCover P ∧
      (∀ s ∈ P, ∃ (u v : V) (r : H.Walk u v), r.IsPath ∧ s = r.support.toFinset ∧
        (x ∈ s → x = u ∨ x = v) ∧ (y ∈ s → y = u ∨ y = v)) ∧
      P.card + 5 ≤ Fintype.card V) := by
  by_cases hxc : x ∈ c.support
  · exact s2t_big6 H col hcol havoid x y hxy (c.rotate x hxc) (hc.rotate hxc)
      (by simpa using hlen) (fun _ => rfl) (fun _ => hxy)
  · by_cases hyc : y ∈ c.support
    · exact s2t_swap H y x (s2t_big6 H col hcol havoid y x hxy.symm (c.rotate y hyc)
        (hc.rotate hyc) (by simpa using hlen) (fun _ => rfl) (fun _ => hxy.symm))
    · exact s2t_big6 H col hcol havoid x y hxy c hc hlen (fun h => absurd h hxc)
        (fun h => absurd h hyc)

/-- Every cycle of a bipartite graph has length at least six or is a 4-cycle. -/
lemma s2t_cyc46 (G : SimpleGraph V) (col : V → Fin 2) (hcol : ∀ u v, G.Adj u v → col u ≠ col v)
    {w : V} (c : G.Walk w w) (hc : c.IsCycle) :
    6 ≤ c.length ∨ ∃ a0 a1 a2 a3 : V, G.Adj a0 a1 ∧ G.Adj a1 a2 ∧ G.Adj a2 a3 ∧ G.Adj a3 a0 ∧
      [a0, a1, a2, a3].Nodup ∧ a0 ∈ c.support ∧ a1 ∈ c.support ∧ a2 ∈ c.support ∧
      a3 ∈ c.support := by
  match c, hc with
  | .nil, hc => exact absurd hc Walk.not_isCycle_nil
  | .cons h1 .nil, _ => exact absurd h1 G.irrefl
  | .cons h1 (.cons h2 .nil), hc =>
    rw [Walk.cons_isCycle_iff] at hc
    exact absurd (by simp [Sym2.eq_swap]) hc.2
  | .cons h1 (.cons h2 (.cons h3 .nil)), _ =>
    exact absurd (s2b_fin2 _ _ _ (hcol _ _ h1) (hcol _ _ h2)) (hcol _ _ h3).symm
  | .cons (v := g1) h1 (.cons (v := g2) h2 (.cons (v := g3) h3 (.cons h4 .nil))), hc =>
    right
    have hq := ((Walk.cons_isCycle_iff _ _).mp hc).1
    rw [Walk.isPath_def] at hq
    simp only [Walk.support_cons, Walk.support_nil, List.nodup_cons, List.mem_cons,
      not_or, List.not_mem_nil] at hq
    refine ⟨w, g1, g2, g3, h1, h2, h3, h4, ?_, by simp, by simp, by simp, by simp⟩
    simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil,
      List.nodup_nil, not_false_eq_true, and_true]
    grind
  | .cons h1 (.cons h2 (.cons h3 (.cons h4 (.cons h5 .nil)))), _ =>
    have := hcol _ _ h1
    have := hcol _ _ h2
    have := hcol _ _ h3
    have := hcol _ _ h4
    have := hcol _ _ h5
    exfalso
    grind
  | .cons _ (.cons _ (.cons _ (.cons _ (.cons _ (.cons _ _))))), _ =>
    left
    simp only [Walk.length_cons]
    omega

/-- An explicit 4-cycle as a cycle walk. -/
lemma s2t_mk4 (G : SimpleGraph V) {a0 a1 a2 a3 : V} (h01 : G.Adj a0 a1) (h12 : G.Adj a1 a2)
    (h23 : G.Adj a2 a3) (h30 : G.Adj a3 a0) (hnd : [a0, a1, a2, a3].Nodup) :
    ∃ c : G.Walk a0 a0, c.IsCycle ∧ c.support = [a0, a1, a2, a3, a0] := by
  refine ⟨Walk.cons h01 (Walk.cons h12 (Walk.cons h23 (Walk.cons h30 Walk.nil))), ?_, rfl⟩
  rw [Walk.cons_isCycle_iff, Walk.isPath_def]
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil,
    List.nodup_nil, not_false_eq_true, and_true] at hnd
  constructor
  · simp only [Walk.support_cons, Walk.support_nil, List.nodup_cons, List.mem_cons,
      not_or, List.not_mem_nil, List.nodup_nil, not_false_eq_true, and_true]
    grind
  · simp only [Walk.edges_cons, Walk.edges_nil, List.mem_cons, List.mem_singleton,
      List.not_mem_nil, or_false, Sym2.eq_iff, not_or]
    grind

/-- An explicit 6-cycle as a cycle walk. -/
lemma s2t_mk6 (G : SimpleGraph V) {a0 a1 a2 a3 a4 a5 : V} (h01 : G.Adj a0 a1)
    (h12 : G.Adj a1 a2) (h23 : G.Adj a2 a3) (h34 : G.Adj a3 a4) (h45 : G.Adj a4 a5)
    (h50 : G.Adj a5 a0) (hnd : [a0, a1, a2, a3, a4, a5].Nodup) :
    ∃ c : G.Walk a0 a0, c.IsCycle ∧ c.length = 6 := by
  refine ⟨Walk.cons h01 (Walk.cons h12 (Walk.cons h23 (Walk.cons h34 (Walk.cons h45
    (Walk.cons h50 Walk.nil))))), ?_, rfl⟩
  rw [Walk.cons_isCycle_iff, Walk.isPath_def]
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil,
    List.nodup_nil, not_false_eq_true, and_true] at hnd
  constructor
  · simp only [Walk.support_cons, Walk.support_nil, List.nodup_cons, List.mem_cons,
      not_or, List.not_mem_nil, List.nodup_nil, not_false_eq_true, and_true]
    grind
  · simp only [Walk.edges_cons, Walk.edges_nil, List.mem_cons, List.mem_singleton,
      List.not_mem_nil, or_false, Sym2.eq_iff, not_or]
    grind

/-- A 4-path inside an explicit 4-cycle with middle vertices avoiding `x`, `y`. -/
lemma s2t_in4 (G : SimpleGraph V) (col : V → Fin 2) (hcol : ∀ u v, G.Adj u v → col u ≠ col v)
    (x y : V) (hxy : col x ≠ col y) {a0 a1 a2 a3 : V} (h01 : G.Adj a0 a1) (h12 : G.Adj a1 a2)
    (h23 : G.Adj a2 a3) (h30 : G.Adj a3 a0) (hnd : [a0, a1, a2, a3].Nodup) :
    ∃ p0 p1 p2 p3 : V, G.Adj p0 p1 ∧ G.Adj p1 p2 ∧ G.Adj p2 p3 ∧ [p0, p1, p2, p3].Nodup ∧
      p1 ≠ x ∧ p1 ≠ y ∧ p2 ≠ x ∧ p2 ≠ y ∧
      (p0 = a0 ∨ p0 = a1 ∨ p0 = a2 ∨ p0 = a3) ∧ (p1 = a0 ∨ p1 = a1 ∨ p1 = a2 ∨ p1 = a3) ∧
      (p2 = a0 ∨ p2 = a1 ∨ p2 = a2 ∨ p2 = a3) ∧ (p3 = a0 ∨ p3 = a1 ∨ p3 = a2 ∨ p3 = a3) := by
  obtain ⟨c, hc, hs⟩ := s2t_mk4 G h01 h12 h23 h30 hnd
  obtain ⟨p0, p1, p2, p3, e1, e2, e3, hn, i1, i2, i3, i4, m0, m1, m2, m3⟩ :=
    s2t_four' G col hcol c hc x y hxy
  rw [hs] at m0 m1 m2 m3
  simp only [List.mem_cons, List.not_mem_nil, or_false] at m0 m1 m2 m3
  refine ⟨p0, p1, p2, p3, e1, e2, e3, hn, i1, i2, i3, i4, ?_, ?_, ?_, ?_⟩ <;> grind

lemma s2t_nd_app {l1 l2 L1 L2 : List V} (h1 : l1.Nodup) (h2 : l2.Nodup) (s1 : ∀ i ∈ l1, i ∈ L1)
    (s2 : ∀ j ∈ l2, j ∈ L2) (hd : (L1 ++ L2).Nodup) : (l1 ++ l2).Nodup :=
  List.nodup_append.mpr ⟨h1, h2, fun a ha b hb => (List.nodup_append.mp hd).2.2 a (s1 a ha) b (s2 b hb)⟩

/-- Two vertex-disjoint 4-cycles. -/
lemma s2t_disj (H : SimpleGraph V) (col : V → Fin 2) (hcol : ∀ u v, H.Adj u v → col u ≠ col v)
    (x y : V) (hxy : col x ≠ col y) {a0 a1 a2 a3 b0 b1 b2 b3 : V}
    (h01 : H.Adj a0 a1) (h12 : H.Adj a1 a2) (h23 : H.Adj a2 a3) (h30 : H.Adj a3 a0)
    (k01 : H.Adj b0 b1) (k12 : H.Adj b1 b2) (k23 : H.Adj b2 b3) (k30 : H.Adj b3 b0)
    (hnd : [a0, a1, a2, a3, b0, b1, b2, b3].Nodup) : (∃ P : Finset (Finset V), H.IsPathCover P ∧
      (∀ s ∈ P, ∃ (u v : V) (r : H.Walk u v), r.IsPath ∧ s = r.support.toFinset ∧
        (x ∈ s → x = u ∨ x = v) ∧ (y ∈ s → y = u ∨ y = v)) ∧
      P.card + 5 ≤ Fintype.card V) := by
  have hnd0 := hnd
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil,
    List.nodup_nil, not_false_eq_true, and_true] at hnd
  obtain ⟨p0, p1, p2, p3, e1, e2, e3, hn, i1, i2, i3, i4, m0, m1, m2, m3⟩ :=
    s2t_in4 H col hcol x y hxy h01 h12 h23 h30 (by
      simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil,
        List.nodup_nil, not_false_eq_true, and_true]; grind)
  obtain ⟨r0, r1, r2, r3, f1, f2, f3, hn', j1, j2, j3, j4, n0, n1, n2, n3⟩ :=
    s2t_in4 H col hcol x y hxy k01 k12 k23 k30 (by
      simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil,
        List.nodup_nil, not_false_eq_true, and_true]; grind)
  have hr3 : [r0, r1, r2].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil,
      List.nodup_nil, not_false_eq_true, and_true] at hn' ⊢; grind
  exact s2t_path43 H x y e1 e2 e3 f1 f2
    (s2t_nd_app (l1 := [p0, p1, p2, p3]) (l2 := [r0, r1, r2]) (L1 := [a0, a1, a2, a3])
      (L2 := [b0, b1, b2, b3]) hn hr3
      (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢
          rcases hi with rfl | rfl | rfl | rfl <;> assumption)
      (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢
          rcases hi with rfl | rfl | rfl <;> assumption) hnd0)
    ⟨i1, i2⟩ ⟨i3, i4⟩ ⟨j1, j2⟩

/-- Two 4-cycles sharing exactly one vertex `s`. -/
lemma s2t_bow (H : SimpleGraph V) (col : V → Fin 2) (hcol : ∀ u v, H.Adj u v → col u ≠ col v)
    (x y : V) (hxy : col x ≠ col y) {s a1 a2 a3 b1 b2 b3 : V}
    (h01 : H.Adj s a1) (h12 : H.Adj a1 a2) (h23 : H.Adj a2 a3) (h30 : H.Adj a3 s)
    (k01 : H.Adj s b1) (k12 : H.Adj b1 b2) (k23 : H.Adj b2 b3) (k30' : H.Adj b3 s)
    (hnd : [s, a1, a2, a3, b1, b2, b3].Nodup) : (∃ P : Finset (Finset V), H.IsPathCover P ∧
      (∀ s ∈ P, ∃ (u v : V) (r : H.Walk u v), r.IsPath ∧ s = r.support.toFinset ∧
        (x ∈ s → x = u ∨ x = v) ∧ (y ∈ s → y = u ∨ y = v)) ∧
      P.card + 5 ≤ Fintype.card V) := by
  have c1 := hcol _ _ h01
  have c2 := hcol _ _ h12
  have d1 := hcol _ _ k01
  have d2 := hcol _ _ k12
  have hnd0 := hnd
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil,
    List.nodup_nil, not_false_eq_true, and_true] at hnd
  have hA : [a1, a2, a3].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil,
      List.nodup_nil, not_false_eq_true, and_true]; grind
  have hB : [b1, b2, b3].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil,
      List.nodup_nil, not_false_eq_true, and_true]; grind
  by_cases ha : a2 ≠ x ∧ a2 ≠ y
  · obtain ⟨p0, p1, p2, p3, e1, e2, e3, hn, i1, i2, i3, i4, m0, m1, m2, m3⟩ :=
      s2t_in4 H col hcol x y hxy k01 k12 k23 k30' (by
        simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil,
          List.nodup_nil, not_false_eq_true, and_true]; grind)
    have hd : ([s, b1, b2, b3] ++ [a1, a2, a3]).Nodup := by
      simp only [List.cons_append, List.nil_append, List.nodup_cons, List.mem_cons,
        not_or, List.not_mem_nil, List.nodup_nil, not_false_eq_true,
        and_true]; grind
    exact s2t_path43 H x y e1 e2 e3 h12 h23
      (s2t_nd_app (l1 := [p0, p1, p2, p3]) (l2 := [a1, a2, a3]) (L1 := [s, b1, b2, b3])
        (L2 := [a1, a2, a3]) hn hA
        (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢
            rcases hi with rfl | rfl | rfl | rfl <;> assumption)
        (fun j hj => hj) hd) ⟨i1, i2⟩ ⟨i3, i4⟩ ha
  · have hb : b2 ≠ x ∧ b2 ≠ y := by
      constructor <;> intro e <;> grind
    obtain ⟨p0, p1, p2, p3, e1, e2, e3, hn, i1, i2, i3, i4, m0, m1, m2, m3⟩ :=
      s2t_in4 H col hcol x y hxy h01 h12 h23 h30 (by
        simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil,
          List.nodup_nil, not_false_eq_true, and_true]; grind)
    exact s2t_path43 H x y e1 e2 e3 k12 k23
      (s2t_nd_app (l1 := [p0, p1, p2, p3]) (l2 := [b1, b2, b3]) (L1 := [s, a1, a2, a3])
        (L2 := [b1, b2, b3]) hn hB
        (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢
            rcases hi with rfl | rfl | rfl | rfl <;> assumption)
        (fun j hj => hj) hnd0) ⟨i1, i2⟩ ⟨i3, i4⟩ hb

/-- An explicit 6-cycle. -/
lemma s2t_cyc6 (H : SimpleGraph V) (col : V → Fin 2) (hcol : ∀ u v, H.Adj u v → col u ≠ col v)
    (havoid : ∀ v : V, ∃ (w : V) (c : H.Walk w w), c.IsCycle ∧ v ∉ c.support)
    (x y : V) (hxy : col x ≠ col y) {a0 a1 a2 a3 a4 a5 : V} (h01 : H.Adj a0 a1)
    (h12 : H.Adj a1 a2) (h23 : H.Adj a2 a3) (h34 : H.Adj a3 a4) (h45 : H.Adj a4 a5)
    (h50 : H.Adj a5 a0) (hnd : [a0, a1, a2, a3, a4, a5].Nodup) : (∃ P : Finset (Finset V), H.IsPathCover P ∧
      (∀ s ∈ P, ∃ (u v : V) (r : H.Walk u v), r.IsPath ∧ s = r.support.toFinset ∧
        (x ∈ s → x = u ∨ x = v) ∧ (y ∈ s → y = u ∨ y = v)) ∧
      P.card + 5 ≤ Fintype.card V) := by
  obtain ⟨c, hc, hl⟩ := s2t_mk6 H h01 h12 h23 h34 h45 h50 hnd
  exact s2t_big6' H col hcol havoid x y hxy c hc (by omega)

/-- Case of the 4-cycle analysis: `w0 ∉ C`, `w1 ∈ C`, `w3 ∉ C`. -/
lemma s2t_qsub (H : SimpleGraph V) (col : V → Fin 2) (hcol : ∀ u v, H.Adj u v → col u ≠ col v)
    (havoid : ∀ v : V, ∃ (w : V) (c : H.Walk w w), c.IsCycle ∧ v ∉ c.support)
    (x y : V) (hxy : col x ≠ col y) {u0 u1 u2 u3 w0 w1 w2 w3 : V}
    (h01 : H.Adj u0 u1) (h12 : H.Adj u1 u2) (h23 : H.Adj u2 u3) (h30 : H.Adj u3 u0)
    (hnd : [u0, u1, u2, u3].Nodup)
    (k01 : H.Adj w0 w1) (k12 : H.Adj w1 w2) (k23 : H.Adj w2 w3) (k30 : H.Adj w3 w0)
    (hnd' : [w0, w1, w2, w3].Nodup)
    (o0 : w0 ≠ u0 ∧ w0 ≠ u1 ∧ w0 ≠ u2 ∧ w0 ≠ u3) (i1 : w1 = u1 ∨ w1 = u2 ∨ w1 = u3)
    (o2 : w2 ≠ u0) (o3 : w3 ≠ u0 ∧ w3 ≠ u1 ∧ w3 ≠ u2 ∧ w3 ≠ u3) : (∃ P : Finset (Finset V), H.IsPathCover P ∧
      (∀ s ∈ P, ∃ (u v : V) (r : H.Walk u v), r.IsPath ∧ s = r.support.toFinset ∧
        (x ∈ s → x = u ∨ x = v) ∧ (y ∈ s → y = u ∨ y = v)) ∧
      P.card + 5 ≤ Fintype.card V) := by
  have c1 := hcol _ _ h01
  have c2 := hcol _ _ h12
  have c3 := hcol _ _ h23
  have d2 := hcol _ _ k12
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil,
    List.nodup_nil, not_false_eq_true, and_true] at hnd hnd'
  by_cases i2 : w2 = u1 ∨ w2 = u2 ∨ w2 = u3
  · rcases i1 with rfl | rfl | rfl <;> rcases i2 with rfl | rfl | rfl
    · exact absurd rfl hnd'.2.1.1
    · exact s2t_cyc6 H col hcol havoid x y hxy h01 k01.symm k30.symm k23.symm h23 h30 (by
        simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil,
          List.nodup_nil, not_false_eq_true, and_true]; grind)
    · exfalso; grind
    · exact s2t_cyc6 H col hcol havoid x y hxy h01 k23 k30 k01 h23 h30 (by
        simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil,
          List.nodup_nil, not_false_eq_true, and_true]; grind)
    · exact absurd rfl hnd'.2.1.1
    · exact s2t_cyc6 H col hcol havoid x y hxy h01 h12 k01.symm k30.symm k23.symm h30 (by
        simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil,
          List.nodup_nil, not_false_eq_true, and_true]; grind)
    · exfalso; grind
    · exact s2t_cyc6 H col hcol havoid x y hxy h01 h12 k23 k30 k01 h30 (by
        simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil,
          List.nodup_nil, not_false_eq_true, and_true]; grind)
    · exact absurd rfl hnd'.2.1.1
  · push Not at i2
    rcases i1 with rfl | rfl | rfl
    · exact s2t_bow H col hcol x y hxy h12 h23 h30 h01 k12 k23 k30 k01 (by
        simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil,
          List.nodup_nil, not_false_eq_true, and_true]; grind)
    · exact s2t_bow H col hcol x y hxy h23 h30 h01 h12 k12 k23 k30 k01 (by
        simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil,
          List.nodup_nil, not_false_eq_true, and_true]; grind)
    · exact s2t_bow H col hcol x y hxy h30 h01 h12 h23 k12 k23 k30 k01 (by
        simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil,
          List.nodup_nil, not_false_eq_true, and_true]; grind)

/-- Analysis of a second 4-cycle `w0 w1 w2 w3` avoiding `u0`, with `w0 ∉ C`. -/
lemma s2t_qcore (H : SimpleGraph V) (col : V → Fin 2) (hcol : ∀ u v, H.Adj u v → col u ≠ col v)
    (havoid : ∀ v : V, ∃ (w : V) (c : H.Walk w w), c.IsCycle ∧ v ∉ c.support)
    (x y : V) (hxy : col x ≠ col y) {u0 u1 u2 u3 w0 w1 w2 w3 : V}
    (h01 : H.Adj u0 u1) (h12 : H.Adj u1 u2) (h23 : H.Adj u2 u3) (h30 : H.Adj u3 u0)
    (hnd : [u0, u1, u2, u3].Nodup)
    (k01 : H.Adj w0 w1) (k12 : H.Adj w1 w2) (k23 : H.Adj w2 w3) (k30 : H.Adj w3 w0)
    (hnd' : [w0, w1, w2, w3].Nodup)
    (o0 : w0 ≠ u0 ∧ w0 ≠ u1 ∧ w0 ≠ u2 ∧ w0 ≠ u3) (o1 : w1 ≠ u0) (o2 : w2 ≠ u0) (o3 : w3 ≠ u0) :
    (∃ P : Finset (Finset V), H.IsPathCover P ∧
      (∀ s ∈ P, ∃ (u v : V) (r : H.Walk u v), r.IsPath ∧ s = r.support.toFinset ∧
        (x ∈ s → x = u ∨ x = v) ∧ (y ∈ s → y = u ∨ y = v)) ∧
      P.card + 5 ≤ Fintype.card V) ∨ ∃ q, q ≠ u0 ∧ q ≠ u1 ∧ q ≠ u2 ∧ q ≠ u3 ∧ H.Adj q u1 ∧ H.Adj q u3 := by
  have c1 := hcol _ _ h01
  have c2 := hcol _ _ h12
  have c3 := hcol _ _ h23
  have d1 := hcol _ _ k01
  have d4 := hcol _ _ k30
  have hnd0 := hnd
  have hnd0' := hnd'
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil,
    List.nodup_nil, not_false_eq_true, and_true] at hnd hnd'
  by_cases A : w1 = u1 ∨ w1 = u2 ∨ w1 = u3
  · by_cases B : w3 = u1 ∨ w3 = u2 ∨ w3 = u3
    · rcases A with rfl | rfl | rfl <;> rcases B with rfl | rfl | rfl
      · exact absurd rfl hnd'.2.1.2
      · exfalso; grind
      · exact Or.inr ⟨w0, o0.1, o0.2.1, o0.2.2.1, o0.2.2.2, k01, k30.symm⟩
      · exfalso; grind
      · exact absurd rfl hnd'.2.1.2
      · exfalso; grind
      · exact Or.inr ⟨w0, o0.1, o0.2.1, o0.2.2.1, o0.2.2.2, k30.symm, k01⟩
      · exfalso; grind
      · exact absurd rfl hnd'.2.1.2
    · push Not at B
      exact Or.inl (s2t_qsub H col hcol havoid x y hxy h01 h12 h23 h30 hnd0 k01 k12 k23 k30
        hnd0' o0 A o2 ⟨o3, B⟩)
  · push Not at A
    by_cases B : w3 = u1 ∨ w3 = u2 ∨ w3 = u3
    · exact Or.inl (s2t_qsub H col hcol havoid x y hxy h01 h12 h23 h30 hnd0 k30.symm k23.symm
        k12.symm k01.symm (by
          simp only [List.nodup_cons, List.mem_cons, not_or,
            List.not_mem_nil, List.nodup_nil, not_false_eq_true, and_true]; grind)
        o0 B o2 ⟨o1, A⟩)
    · push Not at B
      left
      by_cases C : w2 = u1 ∨ w2 = u2 ∨ w2 = u3
      · rcases C with rfl | rfl | rfl
        · exact s2t_bow H col hcol x y hxy h12 h23 h30 h01 k23 k30 k01 k12 (by
            simp only [List.nodup_cons, List.mem_cons, not_or,
              List.not_mem_nil, List.nodup_nil, not_false_eq_true, and_true]; grind)
        · exact s2t_bow H col hcol x y hxy h23 h30 h01 h12 k23 k30 k01 k12 (by
            simp only [List.nodup_cons, List.mem_cons, not_or,
              List.not_mem_nil, List.nodup_nil, not_false_eq_true, and_true]; grind)
        · exact s2t_bow H col hcol x y hxy h30 h01 h12 h23 k23 k30 k01 k12 (by
            simp only [List.nodup_cons, List.mem_cons, not_or,
              List.not_mem_nil, List.nodup_nil, not_false_eq_true, and_true]; grind)
      · push Not at C
        exact s2t_disj H col hcol x y hxy h01 h12 h23 h30 k01 k12 k23 k30 (by
          simp only [List.nodup_cons, List.mem_cons, not_or,
            List.not_mem_nil, List.nodup_nil, not_false_eq_true, and_true]; grind)

/-- A second 4-cycle avoiding `u0`: some vertex of it lies outside `C`. -/
lemma s2t_quad (H : SimpleGraph V) (col : V → Fin 2) (hcol : ∀ u v, H.Adj u v → col u ≠ col v)
    (havoid : ∀ v : V, ∃ (w : V) (c : H.Walk w w), c.IsCycle ∧ v ∉ c.support)
    (x y : V) (hxy : col x ≠ col y) {u0 u1 u2 u3 w0 w1 w2 w3 : V}
    (h01 : H.Adj u0 u1) (h12 : H.Adj u1 u2) (h23 : H.Adj u2 u3) (h30 : H.Adj u3 u0)
    (hnd : [u0, u1, u2, u3].Nodup)
    (k01 : H.Adj w0 w1) (k12 : H.Adj w1 w2) (k23 : H.Adj w2 w3) (k30 : H.Adj w3 w0)
    (hnd' : [w0, w1, w2, w3].Nodup)
    (o0 : w0 ≠ u0) (o1 : w1 ≠ u0) (o2 : w2 ≠ u0) (o3 : w3 ≠ u0) :
    (∃ P : Finset (Finset V), H.IsPathCover P ∧
      (∀ s ∈ P, ∃ (u v : V) (r : H.Walk u v), r.IsPath ∧ s = r.support.toFinset ∧
        (x ∈ s → x = u ∨ x = v) ∧ (y ∈ s → y = u ∨ y = v)) ∧
      P.card + 5 ≤ Fintype.card V) ∨ ∃ q, q ≠ u0 ∧ q ≠ u1 ∧ q ≠ u2 ∧ q ≠ u3 ∧ H.Adj q u1 ∧ H.Adj q u3 := by
  have hnd0' := hnd'
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil,
    List.nodup_nil, not_false_eq_true, and_true] at hnd'
  by_cases e0 : w0 ≠ u1 ∧ w0 ≠ u2 ∧ w0 ≠ u3
  · exact s2t_qcore H col hcol havoid x y hxy h01 h12 h23 h30 hnd k01 k12 k23 k30 hnd0'
      ⟨o0, e0⟩ o1 o2 o3
  by_cases e1 : w1 ≠ u1 ∧ w1 ≠ u2 ∧ w1 ≠ u3
  · exact s2t_qcore H col hcol havoid x y hxy h01 h12 h23 h30 hnd k12 k23 k30 k01 (by
      simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil,
        List.nodup_nil, not_false_eq_true, and_true]; grind) ⟨o1, e1⟩ o2 o3 o0
  by_cases e2 : w2 ≠ u1 ∧ w2 ≠ u2 ∧ w2 ≠ u3
  · exact s2t_qcore H col hcol havoid x y hxy h01 h12 h23 h30 hnd k23 k30 k01 k12 (by
      simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil,
        List.nodup_nil, not_false_eq_true, and_true]; grind) ⟨o2, e2⟩ o3 o0 o1
  by_cases e3 : w3 ≠ u1 ∧ w3 ≠ u2 ∧ w3 ≠ u3
  · exact s2t_qcore H col hcol havoid x y hxy h01 h12 h23 h30 hnd k30 k01 k12 k23 (by
      simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil,
        List.nodup_nil, not_false_eq_true, and_true]; grind) ⟨o3, e3⟩ o0 o1 o2
  exfalso
  grind

/-- From a 4-cycle and `tau ≥ 2`. -/
lemma s2t_four_cycle (H : SimpleGraph V) (col : V → Fin 2)
    (hcol : ∀ u v, H.Adj u v → col u ≠ col v)
    (havoid : ∀ v : V, ∃ (w : V) (c : H.Walk w w), c.IsCycle ∧ v ∉ c.support)
    (x y : V) (hxy : col x ≠ col y) {u0 u1 u2 u3 : V}
    (h01 : H.Adj u0 u1) (h12 : H.Adj u1 u2) (h23 : H.Adj u2 u3) (h30 : H.Adj u3 u0)
    (hnd : [u0, u1, u2, u3].Nodup) : (∃ P : Finset (Finset V), H.IsPathCover P ∧
      (∀ s ∈ P, ∃ (u v : V) (r : H.Walk u v), r.IsPath ∧ s = r.support.toFinset ∧
        (x ∈ s → x = u ∨ x = v) ∧ (y ∈ s → y = u ∨ y = v)) ∧
      P.card + 5 ≤ Fintype.card V) := by
  have hnd0 := hnd
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil,
    List.nodup_nil, not_false_eq_true, and_true] at hnd
  have c1 := hcol _ _ h01
  have c2 := hcol _ _ h12
  obtain ⟨w, c, hc, hu0⟩ := havoid u0
  rcases s2t_cyc46 H col hcol c hc with hl | ⟨w0, w1, w2, w3, k01, k12, k23, k30, hnd', m0, m1, m2, m3⟩
  · exact s2t_big6' H col hcol havoid x y hxy c hc hl
  rcases s2t_quad H col hcol havoid x y hxy h01 h12 h23 h30 hnd0 k01 k12 k23 k30 hnd'
    (fun e => hu0 (e ▸ m0)) (fun e => hu0 (e ▸ m1)) (fun e => hu0 (e ▸ m2))
    (fun e => hu0 (e ▸ m3)) with h | ⟨q, q0, q1, q2, q3, hq1, hq3⟩
  · exact h
  obtain ⟨w', c', hc', hu1⟩ := havoid u1
  rcases s2t_cyc46 H col hcol c' hc' with hl | ⟨z0, z1, z2, z3, l01, l12, l23, l30, hnd'', n0, n1, n2, n3⟩
  · exact s2t_big6' H col hcol havoid x y hxy c' hc' hl
  rcases s2t_quad H col hcol havoid x y hxy h12 h23 h30 h01 (by
      simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil,
        List.nodup_nil, not_false_eq_true, and_true]; grind) l01 l12 l23 l30 hnd''
    (fun e => hu1 (e ▸ n0)) (fun e => hu1 (e ▸ n1)) (fun e => hu1 (e ▸ n2))
    (fun e => hu1 (e ▸ n3)) with h | ⟨s, s1, s2, s3, s0, hs2, hs0⟩
  · exact h
  have cq := hcol _ _ hq1
  have cs := hcol _ _ hs2
  exact s2t_cyc6 H col hcol havoid x y hxy hq1.symm hq3 h30 hs0.symm hs2 h12.symm (by
    simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil,
      List.nodup_nil, not_false_eq_true, and_true]; grind)

lemma s2t_avoid (H : SimpleGraph V) (hf : H.largestInducedForestSize + 2 ≤ Fintype.card V)
    (v : V) : ∃ (w : V) (c : H.Walk w w), c.IsCycle ∧ v ∉ c.support := by
  by_contra hne
  push Not at hne
  have hac : (H.induce ((Finset.univ.erase v : Finset V) : Set V)).IsAcyclic := by
    intro w c hc
    have h := hne _ (c.map (Embedding.induce (G := H) _).toHom)
      (hc.map (Embedding.induce (G := H) _).injective)
    rw [Walk.support_map, List.mem_map] at h
    obtain ⟨z, _, hz⟩ := h
    have := z.prop
    simp only [Finset.coe_erase, Finset.coe_univ, Set.mem_diff, Set.mem_univ,
      Set.mem_singleton_iff, true_and] at this
    exact this hz
  have : (Finset.univ.erase v).card ≤ H.largestInducedForestSize := by
    unfold SimpleGraph.largestInducedForestSize
    apply le_csSup
    · exact ⟨Fintype.card V, by rintro n ⟨s, _, rfl⟩; exact Finset.card_le_univ s⟩
    · exact ⟨_, hac, rfl⟩
  rw [Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ] at this
  omega

/-- `tau ≥ 2` gives five path edges with `x`, `y` as ends. -/
theorem s2t_tau2 (H : SimpleGraph V) (col : V → Fin 2) (hcol : ∀ u v, H.Adj u v → col u ≠ col v)
    (x y : V) (hxy : col x ≠ col y) (hf : H.largestInducedForestSize + 2 ≤ Fintype.card V) :
    (∃ P : Finset (Finset V), H.IsPathCover P ∧
      (∀ s ∈ P, ∃ (u v : V) (r : H.Walk u v), r.IsPath ∧ s = r.support.toFinset ∧
        (x ∈ s → x = u ∨ x = v) ∧ (y ∈ s → y = u ∨ y = v)) ∧
      P.card + 5 ≤ Fintype.card V) := by
  have havoid := s2t_avoid H hf
  obtain ⟨w, c, hc, _⟩ := havoid x
  rcases s2t_cyc46 H col hcol c hc with hl | ⟨u0, u1, u2, u3, h01, h12, h23, h30, hnd, _⟩
  · exact s2t_big6' H col hcol havoid x y hxy c hc hl
  · exact s2t_four_cycle H col hcol havoid x y hxy h01 h12 h23 h30 hnd

/-- `S2` whenever the feedback vertex number is at most two. -/
theorem s2t_small2 (V : Type) [Fintype V] [DecidableEq V] (H : SimpleGraph V) (col : V → Fin 2)
    (hcol : ∀ u v, H.Adj u v → col u ≠ col v) (hconn : H.Connected) (x y : V) (hxy : col x ≠ col y)
    (hf : Fintype.card V ≤ H.largestInducedForestSize + 2) :
    ∃ P : Finset (Finset V), H.IsPathCover P ∧
      (∀ s ∈ P, ∃ (u v : V) (q : H.Walk u v), q.IsPath ∧ s = q.support.toFinset ∧
        (x ∈ s → x = u ∨ x = v) ∧ (y ∈ s → y = u ∨ y = v)) ∧
      P.card + Fintype.card V + 1 ≤ 2 * H.largestInducedForestSize := by
  by_cases h1 : Fintype.card V ≤ H.largestInducedForestSize + 1
  · exact s2b_small V H col hcol hconn x y hxy h1
  · obtain ⟨P, hP, he, hc⟩ := s2t_tau2 H col hcol x y hxy (by omega)
    exact ⟨P, hP, he, by omega⟩

/-- The reduction, by induction on the number of vertices and then of edges. -/
theorem reduce (hA : H1) (hB : H2) : ∀ (n : ℕ) (V : Type) [Fintype V] [DecidableEq V],
    Fintype.card V = n → ∀ (H : SimpleGraph V) (c : V → Fin 2),
    (∀ u v, H.Adj u v → c u ≠ c v) → H.Connected → ∀ x y : V, c x ≠ c y →
    ∃ P : Finset (Finset V), H.IsPathCover P ∧
      (∀ s ∈ P, ∃ (u v : V) (q : H.Walk u v), q.IsPath ∧ s = q.support.toFinset ∧
        (x ∈ s → x = u ∨ x = v) ∧ (y ∈ s → y = u ∨ y = v)) ∧
      P.card + Fintype.card V + 1 ≤ 2 * H.largestInducedForestSize := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
  intro V _ _ hn
  have ih' : (∀ (W : Type) [Fintype W] [DecidableEq W], Fintype.card W < n →
      ∀ (G : SimpleGraph W) (c : W → Fin 2), (∀ u v, G.Adj u v → c u ≠ c v) → G.Connected →
      ∀ x y : W, c x ≠ c y →
      ∃ P : Finset (Finset W), G.IsPathCover P ∧
      (∀ s ∈ P, ∃ (u v : W) (q : G.Walk u v), q.IsPath ∧ s = q.support.toFinset ∧
        (x ∈ s → x = u ∨ x = v) ∧ (y ∈ s → y = u ∨ y = v)) ∧
      P.card + Fintype.card W + 1 ≤ 2 * G.largestInducedForestSize) :=
    fun W _ _ hW => ihn _ hW W rfl
  suffices hm : ∀ (m : ℕ) (H : SimpleGraph V), H.edgeSet.ncard = m → ∀ (c : V → Fin 2),
      (∀ u v, H.Adj u v → c u ≠ c v) → H.Connected → ∀ x y : V, c x ≠ c y →
      ∃ P : Finset (Finset V), H.IsPathCover P ∧
      (∀ s ∈ P, ∃ (u v : V) (q : H.Walk u v), q.IsPath ∧ s = q.support.toFinset ∧
        (x ∈ s → x = u ∨ x = v) ∧ (y ∈ s → y = u ∨ y = v)) ∧
      P.card + Fintype.card V + 1 ≤ 2 * H.largestInducedForestSize by
    intro H
    exact hm _ H rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ihm =>
  intro H hHm c hc hconn x y hxy
  classical
  by_cases hbr : ∃ a b, H.Adj a b ∧ ¬ (H.deleteEdges {s(a, b)}).Connected
  · obtain ⟨a, b, hab, hdis⟩ := hbr
    exact step_bridge n ih' hn H c hc hconn a b hab hdis x y hxy
  push Not at hbr
  have hxy' : x ≠ y := fun e => hxy (e ▸ rfl)
  have hnoleaf := noleaf_of_bridgeless H hconn hbr hxy'
  by_cases hcut : ∃ w, ¬ (H.induce ({w}ᶜ : Set V)).Connected
  · obtain ⟨w, hw⟩ := hcut
    exact step_cut n ih' hn H c hc hconn hnoleaf w hw x y hxy
  push Not at hcut
  by_cases he : ∃ a b, H.Adj a b ∧
      (H.deleteEdges {s(a, b)}).largestInducedForestSize ≤ H.largestInducedForestSize
  · obtain ⟨a, b, hab, hf⟩ := he
    apply step_edge H a b x y hf
    have hlt : (H.deleteEdges {s(a, b)}).edgeSet.ncard < m := by
      rw [← hHm, edgeSet_deleteEdges]
      exact Set.ncard_sdiff_singleton_lt_of_mem (H.mem_edgeSet.mpr hab)
    exact ihm _ hlt _ rfl c (fun u v h => hc u v (deleteEdges_le _ h)) (hbr a b hab) x y hxy
  push Not at he
  by_cases hsm : Fintype.card V ≤ H.largestInducedForestSize + 2
  · exact s2t_small2 V H c hc hconn x y hxy hsm
  have hconj : H.pathCoverNumber + Fintype.card V + 1 ≤ 2 * H.largestInducedForestSize := by
    by_cases hpeel : ∃ (x' y' d e : V) (q : H.Walk x' d), c x' ≠ c y' ∧ q.IsPath ∧
        y' ∉ q.support ∧ c d ≠ c x' ∧ e ∉ q.support ∧ H.Adj d e ∧
        (∃ a b, a ∉ q.support ∧ b ∉ q.support ∧ H.Adj a b) ∧
        2 * (H.induce {z | z ∉ q.support}).largestInducedForestSize + q.length + 1 ≤
          2 * H.largestInducedForestSize
    · obtain ⟨x', y', d, e, q, h0, h1, h2, h3, h4, h5, h6, h7⟩ := hpeel
      obtain ⟨P, hP, -, hcard⟩ := step_path n ih' hn H c hc x' y' d e h0 q h1 h2 h3 h4 h5 h6 h7
      have hle : H.pathCoverNumber ≤ P.card := by
        unfold SimpleGraph.pathCoverNumber
        exact Nat.sInf_le ⟨P, rfl, hP⟩
      omega
    · exact hA V H c hc hconn hbr hcut he (by omega)
        (fun x' y' hxy' d e q h1 h2 h3 h4 h5 h6 => by
          by_contra hcon
          exact hpeel ⟨x', y', d, e, q, hxy', h1, h2, h3, h4, h5, h6, by omega⟩)
  by_cases hs : H.pathCoverNumber + Fintype.card V + 3 ≤ 2 * H.largestInducedForestSize
  · exact slack_two H x y hs
  by_cases hpx : ∃ (d e : V) (q : H.Walk x d), q.IsPath ∧ y ∉ q.support ∧ c d ≠ c x ∧
      e ∉ q.support ∧ H.Adj d e ∧ (∃ a b, a ∉ q.support ∧ b ∉ q.support ∧ H.Adj a b) ∧
      2 * (H.induce {z | z ∉ q.support}).largestInducedForestSize + q.length + 1 ≤
        2 * H.largestInducedForestSize
  · obtain ⟨d, e, q, h1, h2, h3, h4, h5, h6, h7⟩ := hpx
    exact step_path n ih' hn H c hc x y d e hxy q h1 h2 h3 h4 h5 h6 h7
  by_cases hpy : ∃ (d e : V) (q : H.Walk y d), q.IsPath ∧ x ∉ q.support ∧ c d ≠ c y ∧
      e ∉ q.support ∧ H.Adj d e ∧ (∃ a b, a ∉ q.support ∧ b ∉ q.support ∧ H.Adj a b) ∧
      2 * (H.induce {z | z ∉ q.support}).largestInducedForestSize + q.length + 1 ≤
        2 * H.largestInducedForestSize
  · obtain ⟨d, e, q, h1, h2, h3, h4, h5, h6, h7⟩ := hpy
    obtain ⟨P, hP, hcap, hcard⟩ :=
      step_path n ih' hn H c hc y x d e (Ne.symm hxy) q h1 h2 h3 h4 h5 h6 h7
    refine ⟨P, hP, fun s hs => ?_, hcard⟩
    obtain ⟨u, v, q, hq, hsq, h1, h2⟩ := hcap s hs
    exact ⟨u, v, q, hq, hsq, h2, h1⟩
  exact hB V H c hc hconn hbr hcut he (by omega) hconj (by omega) x y hxy
    (fun d e q h1 h2 h3 h4 h5 h6 => by
      by_contra hcon
      exact hpx ⟨d, e, q, h1, h2, h3, h4, h5, h6, by omega⟩)
    (fun d e q h1 h2 h3 h4 h5 h6 => by
      by_contra hcon
      exact hpy ⟨d, e, q, h1, h2, h3, h4, h5, h6, by omega⟩)

end

theorem main : H1 → H2 → OMA.R_WrittenOnTheWallII_GraphConjecture40_conjecture40_R1_H2_R1.H1 := by
  intro hA hB V _ _ H c hc hconn x y hxy
  exact reduce hA hB _ V rfl H c hc hconn x y hxy

end OMA.R_WrittenOnTheWallII_GraphConjecture40_conjecture40_R1_H2_R1_H1_R1
