import FormalConjectures.Wikipedia.RamseyNumbers
import Mathlib.Combinatorics.SimpleGraph.CycleGraph

open RamseyNumbers SimpleGraph

-- A triangle-free neighborhood is independent. Applying this to both colors
-- bounds their degrees at the same vertex, though those degrees add to five.
set_option maxRecDepth 4000 in
set_option maxHeartbeats 800000 in
theorem OMA.solution : type_of% @RamseyNumbers.ramsey_number_three_three := by
  rw [classicalRamsey_eq_sInf]
  apply IsLeast.csInf_eq
  constructor
  · classical
    rintro G ⟨hG, hC⟩
    have low (H : SimpleGraph (Fin 6)) (h : H.CliqueFree 3) (hc : Hᶜ.CliqueFree 3) :
        H.degree 0 < 3 := by
      by_contra! hd
      apply hc.mono hd (H.neighborFinset 0)
      refine ⟨?_, rfl⟩
      rw [H.coe_neighborFinset, H.isClique_compl]
      exact H.isIndepSet_neighborSet_of_triangleFree h 0
    have := low G hG hC
    have hd := low Gᶜ hC (by simpa using hG)
    rw [G.degree_compl, Fintype.card_fin] at hd
    omega
  · intro n hn
    by_contra! hlt
    have mono : Monotone (fun m => IsGraphRamsey m 3 3) :=
      monotone_nat_of_le_succ fun m => IsGraphRamsey.succ m 3 3
    apply mono (show n ≤ 5 by omega) hn (cycleGraph 5)
    unfold CliqueFree
    decide
