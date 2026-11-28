import OMAReductions.R_Erdos552_erdos_552_parts_ii_R2_H2_R1

/-!
# Saturating a quadrilateral-free graph (step H1 of reduction R2.H2.R1 of Erdős 552 (ii))

Among the finitely many quadrilateral-free graphs on `Fin N` containing `G`, take a maximal one
`S`. For a non-edge `xy`, the graph `S ⊔ {xy}` strictly contains `S`, hence contains a copy of
the 4-cycle. Exactly one edge of that copy is `xy` (two of its edges cannot both be `xy`, since
the copy is injective), so the other three edges lie in `S` and form a path `x - a - b - y`
through two further distinct vertices.
-/

open SimpleGraph

namespace OMA.Erdos552SatH1

/-- A 4-cycle `p0 p1 p2 p3` in `S ⊔ {xy}` whose edge `p0 p1` is not in `S` yields the path. -/
theorem path_of_cycle {N : ℕ} {S : SimpleGraph (Fin N)} {x y p0 p1 p2 p3 : Fin N}
    (d01 : p0 ≠ p1) (d02 : p0 ≠ p2) (d03 : p0 ≠ p3) (d12 : p1 ≠ p2) (d13 : p1 ≠ p3)
    (d23 : p2 ≠ p3)
    (h01 : (S ⊔ fromEdgeSet {s(x, y)}).Adj p0 p1) (h12 : (S ⊔ fromEdgeSet {s(x, y)}).Adj p1 p2)
    (h23 : (S ⊔ fromEdgeSet {s(x, y)}).Adj p2 p3) (h30 : (S ⊔ fromEdgeSet {s(x, y)}).Adj p3 p0)
    (hn : ¬ S.Adj p0 p1) :
    ∃ a b, a ≠ y ∧ b ≠ x ∧ S.Adj x a ∧ S.Adj a b ∧ S.Adj b y := by
  simp only [sup_adj, fromEdgeSet_adj, Set.mem_singleton_iff, Sym2.eq_iff] at h01 h12 h23 h30
  rcases h01 with h | ⟨⟨hx, hy⟩ | ⟨hy, hx⟩, -⟩
  · exact absurd h hn
  · rw [← hx, ← hy] at h12 h23 h30 ⊢
    have e12 : S.Adj p1 p2 := by
      rcases h12 with h | ⟨h | h, -⟩
      exacts [h, absurd h.1.symm d01, absurd h.2.symm d02]
    have e23 : S.Adj p2 p3 := by
      rcases h23 with h | ⟨h | h, -⟩
      exacts [h, absurd h.1.symm d02, absurd h.1.symm d12]
    have e30 : S.Adj p3 p0 := by
      rcases h30 with h | ⟨h | h, -⟩
      exacts [h, absurd h.1.symm d03, absurd h.1.symm d13]
    exact ⟨p3, p2, d13.symm, d02.symm, e30.symm, e23.symm, e12.symm⟩
  · rw [← hx, ← hy] at h12 h23 h30 ⊢
    have e12 : S.Adj p1 p2 := by
      rcases h12 with h | ⟨h | h, -⟩
      exacts [h, absurd h.2.symm d02, absurd h.1.symm d01]
    have e23 : S.Adj p2 p3 := by
      rcases h23 with h | ⟨h | h, -⟩
      exacts [h, absurd h.1.symm d12, absurd h.1.symm d02]
    have e30 : S.Adj p3 p0 := by
      rcases h30 with h | ⟨h | h, -⟩
      exacts [h, absurd h.1.symm d13, absurd h.1.symm d03]
    exact ⟨p2, p3, d02.symm, d13.symm, e12, e23, e30⟩

/-- The adjacent pairs of the 4-cycle. -/
theorem cycle4_adj : ∀ a b : Fin 4, (cycleGraph 4).Adj a b →
    (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) ∨ (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 1) ∨
    (a = 2 ∧ b = 3) ∨ (a = 3 ∧ b = 2) ∨ (a = 3 ∧ b = 0) ∨ (a = 0 ∧ b = 3) := by
  decide

end OMA.Erdos552SatH1

open OMA.Erdos552SatH1 in
theorem OMA.solution : OMA.R_Erdos552_erdos_552_parts_ii_R2_H2_R1.H1 := by
  intro N G hG
  classical
  obtain ⟨S, hS⟩ := (Finset.univ.filter
    (fun S : SimpleGraph (Fin N) => G ≤ S ∧ ¬ (cycleGraph 4).IsContained S)).exists_maximal
    ⟨G, Finset.mem_filter.2 ⟨Finset.mem_univ _, le_rfl, hG⟩⟩
  have hSP := (Finset.mem_filter.1 hS.1).2
  refine ⟨S, hSP.1, hSP.2, fun x y hxy hn => ?_⟩
  have hlt : S ≤ S ⊔ fromEdgeSet {s(x, y)} := le_sup_left
  have hxy' : (S ⊔ fromEdgeSet {s(x, y)}).Adj x y := by
    simp [sup_adj, fromEdgeSet_adj, hxy]
  have hc : (cycleGraph 4).IsContained (S ⊔ fromEdgeSet {s(x, y)}) := by
    by_contra hfree
    have hmem : S ⊔ fromEdgeSet {s(x, y)} ∈ Finset.univ.filter
        (fun S : SimpleGraph (Fin N) => G ≤ S ∧ ¬ (cycleGraph 4).IsContained S) :=
      Finset.mem_filter.2 ⟨Finset.mem_univ _, hSP.1.trans hlt, hfree⟩
    have hle := hS.2 hmem hlt
    exact hn (hle hxy')
  obtain ⟨f⟩ := hc
  have hadj : ∀ i j : Fin 4, (cycleGraph 4).Adj i j →
      (S ⊔ fromEdgeSet {s(x, y)}).Adj (f i) (f j) := fun i j h => f.toHom.map_adj h
  have dist : ∀ i j : Fin 4, i ≠ j → f i ≠ f j := fun i j h e => h (f.injective e)
  have a01 := hadj 0 1 (by decide)
  have a12 := hadj 1 2 (by decide)
  have a23 := hadj 2 3 (by decide)
  have a30 := hadj 3 0 (by decide)
  have d01 := dist 0 1 (by decide)
  have d02 := dist 0 2 (by decide)
  have d03 := dist 0 3 (by decide)
  have d12 := dist 1 2 (by decide)
  have d13 := dist 1 3 (by decide)
  have d23 := dist 2 3 (by decide)
  by_cases h01 : S.Adj (f 0) (f 1)
  · by_cases h12 : S.Adj (f 1) (f 2)
    · by_cases h23 : S.Adj (f 2) (f 3)
      · by_cases h30 : S.Adj (f 3) (f 0)
        · exfalso
          apply hSP.2
          refine ⟨⟨⟨f, fun {a b} h => ?_⟩, f.injective⟩⟩
          rcases cycle4_adj a b h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
            ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact h01
          · exact h01.symm
          · exact h12
          · exact h12.symm
          · exact h23
          · exact h23.symm
          · exact h30
          · exact h30.symm
        · exact path_of_cycle d03.symm d13.symm d23.symm d01 d02 d12 a30 a01 a12 a23 h30
      · exact path_of_cycle d23 d02.symm d12.symm d03.symm d13.symm d01 a23 a30 a01 a12 h23
    · exact path_of_cycle d12 d13 d01.symm d23 d02.symm d03.symm a12 a23 a30 a01 h12
  · exact path_of_cycle d01 d02 d03 d12 d13 d23 a01 a12 a23 a30 h01
