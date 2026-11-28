import OMAReductions.R_Erdos60_erdos_60_variants_two_copies_R1

/-!
Proof of `OMA.R_Erdos60_erdos_60_variants_two_copies_R1.H2`.
Each ordered pair `(p1, p2)` with `u - p1 - p2 - v` a path in `F` gives, together with the edge
`uv` of `G`, an injective map from the four-cycle `0 - 1 - 2 - 3 - 0` to `G` sending
`0, 1, 2, 3` to `u, p1, p2, v` (the four vertices are distinct because `uv` is not an edge of
`F`). The image subgraph is a copy of the four-cycle in `G`. Different pairs give different
subgraphs: in the image, the neighbour of `u` other than `v` is `p1` and the neighbour of `v`
other than `u` is `p2`. So the number of pairs is at most the number of copies.
-/

namespace OMAProof.Erdos60ClosePath

open SimpleGraph Finset

/-- The closed walk `u, p.1, p.2, v` as a map from the vertices of the four-cycle. -/
def cyc {n : ℕ} (u v : Fin n) (p : Fin n × Fin n) : Fin 4 → Fin n := ![u, p.1, p.2, v]

/-- The six distinctness facts of a path `u, p.1, p.2, v`. -/
structure Distinct {n : ℕ} (u v : Fin n) (p : Fin n × Fin n) : Prop where
  u1 : u ≠ p.1
  u2 : u ≠ p.2
  uv : u ≠ v
  p12 : p.1 ≠ p.2
  p1v : p.1 ≠ v
  p2v : p.2 ≠ v

theorem cyc_injective {n : ℕ} {u v : Fin n} {p : Fin n × Fin n} (h : Distinct u v p) :
    Function.Injective (cyc u v p) := by
  have := h.u1; have := h.u2; have := h.uv; have := h.p12; have := h.p1v; have := h.p2v
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp [cyc] at hij ⊢ <;> simp_all

theorem cyc_adj {n : ℕ} (G : SimpleGraph (Fin n)) {u v : Fin n} {p : Fin n × Fin n}
    (h1 : G.Adj u p.1) (h2 : G.Adj p.1 p.2) (h3 : G.Adj p.2 v) (h4 : G.Adj u v) :
    ∀ {i j : Fin 4}, (cycleGraph 4).Adj i j → G.Adj (cyc u v p i) (cyc u v p j) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> first
    | exact absurd hij (by decide)
    | simp only [cyc]; simp [h1, h2, h3, h4, h1.symm, h2.symm, h3.symm, h4.symm]

/-- The four-cycle copy given by a path. -/
def cycCopy {n : ℕ} (G : SimpleGraph (Fin n)) {u v : Fin n} {p : Fin n × Fin n}
    (h1 : G.Adj u p.1) (h2 : G.Adj p.1 p.2) (h3 : G.Adj p.2 v) (h4 : G.Adj u v)
    (hd : Distinct u v p) : Copy (cycleGraph 4) G :=
  ⟨⟨cyc u v p, cyc_adj G h1 h2 h3 h4⟩, cyc_injective hd⟩

theorem toSubgraph_adj_iff {n : ℕ} {G : SimpleGraph (Fin n)} (c : Copy (cycleGraph 4) G)
    (x y : Fin n) :
    c.toSubgraph.Adj x y ↔ ∃ a b, (cycleGraph 4).Adj a b ∧ c a = x ∧ c b = y := by
  simp [Copy.toSubgraph, Subgraph.map_adj, Relation.Map]

end OMAProof.Erdos60ClosePath

open OMAProof.Erdos60ClosePath SimpleGraph Finset in
theorem OMA.solution : OMA.R_Erdos60_erdos_60_variants_two_copies_R1.H2 := by
  intro n F G _ hFG u v hnot huv
  classical
  have dist : ∀ p : Fin n × Fin n, F.Adj u p.1 ∧ F.Adj p.1 p.2 ∧ F.Adj p.2 v →
      Distinct u v p := by
    rintro p ⟨h1, h2, h3⟩
    refine ⟨h1.ne, ?_, huv.ne, h2.ne, ?_, h3.ne⟩
    · rintro e; rw [← e] at h3; exact hnot h3
    · rintro e; rw [e] at h1; exact hnot h1
  let φ : Fin n × Fin n → G.Subgraph := fun p =>
    if h : F.Adj u p.1 ∧ F.Adj p.1 p.2 ∧ F.Adj p.2 v then
      (cycCopy G (hFG h.1) (hFG h.2.1) (hFG h.2.2) huv (dist p h)).toSubgraph
    else ⊥
  unfold copyCount
  apply card_le_card_of_injOn φ
  · intro p hp
    have hp' := (mem_filter.mp hp).2
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq, φ, dif_pos hp']
    exact ⟨Copy.isoToSubgraph _⟩
  · intro p hp q hq hpq
    have hp' := (mem_filter.mp (mem_coe.mp hp)).2
    have hq' := (mem_filter.mp (mem_coe.mp hq)).2
    simp only [φ, dif_pos hp', dif_pos hq'] at hpq
    have dp := dist p hp'
    have dq := dist q hq'
    have a1 : (cycCopy G (hFG hp'.1) (hFG hp'.2.1) (hFG hp'.2.2) huv dp).toSubgraph.Adj u p.1 :=
      (toSubgraph_adj_iff _ _ _).mpr ⟨0, 1, by decide, rfl, rfl⟩
    have a2 : (cycCopy G (hFG hp'.1) (hFG hp'.2.1) (hFG hp'.2.2) huv dp).toSubgraph.Adj p.2 v :=
      (toSubgraph_adj_iff _ _ _).mpr ⟨2, 3, by decide, rfl, rfl⟩
    rw [hpq, toSubgraph_adj_iff] at a1 a2
    have := dp.u1; have := dp.u2; have := dp.uv; have := dp.p12; have := dp.p1v; have := dp.p2v
    have := dq.u1; have := dq.u2; have := dq.p12; have := dq.p1v; have := dq.p2v
    obtain ⟨a, b, hab, ha, hb⟩ := a1
    obtain ⟨c, d, hcd, hc, hd⟩ := a2
    have e1 : q.1 = p.1 := by
      fin_cases a <;> fin_cases b <;> first
        | exact absurd hab (by decide)
        | (simp [cycCopy, cyc] at ha hb; simp_all)
    have e2 : q.2 = p.2 := by
      fin_cases c <;> fin_cases d <;> first
        | exact absurd hcd (by decide)
        | (simp [cycCopy, cyc] at hc hd; simp_all)
    exact Prod.ext e1.symm e2.symm
