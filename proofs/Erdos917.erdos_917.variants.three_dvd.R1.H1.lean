import OMAReductions.R_Erdos917_erdos_917_variants_three_dvd_R1
-- Step Erdos917.erdos_917.variants.three_dvd.R1.H1: hypothesis H1 of reduction Erdos917.erdos_917.variants.three_dvd.R1
-- Credit: @Raimo33
-- Proof adapted from the merged proof of Erdos917.erdos_917.variants.lower_construction.R1.H1 (same statement word for word).

/-! An odd cycle is three-critical: deleting a vertex or edge allows an
alternating coloring starting at the break. The parity lemmas are from
the repository's proof of the Dirac six-critical construction (Erdős 1032). -/

open SimpleGraph Finset
namespace OMA.OddCycle

def diracParity {k : ℕ} (r u : Fin (k + 3)) : Fin 2 :=
  ⟨(u - r).val % 2, Nat.mod_lt _ (by decide)⟩

lemma diracCycle_step {k : ℕ} {u v : Fin (k + 3)}
    (hadj : (cycleGraph (k + 3)).Adj u v) : u + 1 = v ∨ v + 1 = u := by
  rcases (cycleGraph_adj (n := k + 1)).mp hadj with h | h
  · right
    calc
      v + 1 = (u - v) + v := by rw [h]; exact add_comm _ _
      _ = u := sub_add_cancel _ _
  · left
    calc
      u + 1 = (v - u) + u := by rw [h]; exact add_comm _ _
      _ = v := sub_add_cancel _ _

lemma diracParity_eq_of_step {k : ℕ} {r u v : Fin (k + 3)}
    (hstep : u + 1 = v) (heq : diracParity r u = diracParity r v) : v = r := by
  let w := u - r
  have hshift : v - r = w + 1 := by
    rw [← hstep]
    dsimp only [w]
    abel
  have hpar : w.val % 2 = (v - r).val % 2 := congrArg Fin.val heq
  have hval : (v - r).val = (w.val + 1) % (k + 3) := by
    rw [hshift, Fin.val_add, Fin.val_one]
  have hwrap : w.val + 1 = k + 3 := by
    by_contra h
    have hlt : w.val + 1 < k + 3 := by have := w.isLt; omega
    rw [Nat.mod_eq_of_lt hlt] at hval
    omega
  have hz : v - r = 0 := by
    apply Fin.ext
    rw [hval, hwrap, Nat.mod_self]
    rfl
  exact sub_eq_zero.mp hz

lemma diracParity_collision {k : ℕ} {r u v : Fin (k + 3)}
    (hadj : (cycleGraph (k + 3)).Adj u v) (h : diracParity r u = diracParity r v) :
    (u + 1 = v ∧ v = r) ∨ (v + 1 = u ∧ u = r) :=
  (diracCycle_step hadj).imp (fun hs => ⟨hs, diracParity_eq_of_step hs h⟩)
    (fun hs => ⟨hs, diracParity_eq_of_step hs h.symm⟩)

lemma diracParity_valid_away {k : ℕ} {r u v : Fin (k + 3)} (hu : u ≠ r) (hv : v ≠ r)
    (hadj : (cycleGraph (k + 3)).Adj u v) : diracParity r u ≠ diracParity r v := by
  intro h
  exact (diracParity_collision hadj h).elim (fun hc => hv hc.2) (fun hc => hu hc.2)

lemma diracParity_valid_without_edge {k : ℕ} {a b u v : Fin (k + 3)} (hab : a + 1 = b)
    (hpair : s(u, v) ≠ s(a, b)) (hadj : (cycleGraph (k + 3)).Adj u v) :
    diracParity b u ≠ diracParity b v := by
  intro h
  rcases diracParity_collision hadj h with ⟨hstep, hv⟩ | ⟨hstep, hu⟩
  · have hu : u = a := add_right_cancel (hstep.trans (hv.trans hab.symm))
    exact hpair (Sym2.eq_iff.mpr (Or.inl ⟨hu, hv⟩))
  · have hv : v = a := add_right_cancel (hstep.trans (hu.trans hab.symm))
    exact hpair (Sym2.eq_iff.mpr (Or.inr ⟨hu, hv⟩))

end OMA.OddCycle

open OMA.OddCycle

theorem OMA.solution : OMA.R_Erdos917_erdos_917_variants_three_dvd_R1.H1 := by
  intro b hodd hb
  obtain ⟨k, rfl⟩ : ∃ k, b = k + 3 := ⟨b-3, by omega⟩
  let G := cycleGraph (k+3)
  have hχ : G.chromaticNumber = 3 := chromaticNumber_cycleGraph_of_odd _ (by omega) hodd
  refine ⟨G, ⟨⟨hχ, ?_⟩, ?_⟩, ?_⟩
  · intro r
    let S := (⊤ : G.Subgraph).deleteVerts ({r} : Set _)
    change S.coe.chromaticNumber < (⊤ : G.Subgraph).coe.chromaticNumber
    rw [chromaticNumber_congr (Subgraph.topIso (G := G)), hχ]
    have hcol : S.coe.Colorable 2 := by
      refine ⟨Coloring.mk (fun x => diracParity r x.val) ?_⟩
      intro x y h
      exact diracParity_valid_away x.property.2 y.property.2 (S.coe_adj_sub _ _ h)
    exact hcol.chromaticNumber_le.trans_lt (by decide)
  · refine Sym2.ind fun a b (hab : G.Adj a b) => ?_
    change (G.deleteEdges {s(a,b)}).chromaticNumber < G.chromaticNumber
    rw [hχ]
    have del (c e : Fin (k+3)) (hce : c+1 = e) : (G.deleteEdges {s(c,e)}).Colorable 2 := by
      refine ⟨Coloring.mk (diracParity e) ?_⟩
      intro x y h
      obtain ⟨hxy, hne⟩ := deleteEdges_adj.mp h
      exact diracParity_valid_without_edge hce hne hxy
    rcases diracCycle_step hab with h | h
    · exact (del a b h).chromaticNumber_le.trans_lt (by decide)
    · rw [Sym2.eq_swap]
      exact (del b a h).chromaticNumber_le.trans_lt (by decide)
  · rw [← coe_edgeFinset, Set.ncard_coe_finset]
    have h := sum_degrees_eq_twice_card_edges G
    simp only [G, cycleGraph_degree_three_le, sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at h
    change (cycleGraph (k+3)).edgeFinset.card = _
    omega

