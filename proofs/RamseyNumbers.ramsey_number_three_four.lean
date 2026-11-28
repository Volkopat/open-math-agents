import FormalConjectures.Wikipedia.RamseyNumbers
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Nat.Dist

open RamseyNumbers SimpleGraph

private def G8 : SimpleGraph (Fin 8) where
  Adj u v := Nat.dist u.1 v.1 = 1 ∨ Nat.dist u.1 v.1 = 4 ∨ Nat.dist u.1 v.1 = 7
  symm := ⟨by decide⟩
  loopless := ⟨by decide⟩

private instance : DecidableRel G8.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

private lemma hG8 : G8.CliqueFree 3 ∧ G8ᶜ.CliqueFree 4 := by unfold CliqueFree; decide +kernel

theorem OMA.solution : type_of% @RamseyNumbers.ramsey_number_three_four := by
  classical
  rw [classicalRamsey_eq_sInf]
  refine IsLeast.csInf_eq ⟨?_, fun n hn => by_contra fun hlt =>
    (monotone_nat_of_le_succ (f := fun m => IsGraphRamsey m 3 4)
      (fun m => IsGraphRamsey.succ m 3 4) (by omega : n ≤ 8) hn) G8 hG8⟩
  have h6 : IsGraphRamsey 6 3 3 := by
    rintro K ⟨h1, h2⟩
    have hld (M : SimpleGraph (Fin 6)) (ha : M.CliqueFree 3) (hb : Mᶜ.CliqueFree 3) : M.degree 0 < 3 :=
      by_contra fun hd => hb.mono (not_lt.mp hd) (M.neighborFinset 0)
        ⟨by rw [M.coe_neighborFinset, M.isClique_compl]; exact M.isIndepSet_neighborSet_of_triangleFree ha 0, rfl⟩
    have := hld K h1 h2; have := hld Kᶜ h2 (by simpa using h1)
    rw [K.degree_compl, Fintype.card_fin] at this; omega
  rintro G ⟨hG, hGc⟩
  have hdeg (v : Fin 9) : G.degree v = 3 := by
    have hup : G.degree v < 4 := by_contra fun h =>
      hGc.mono (not_lt.mp h) (G.neighborFinset v)
        ⟨by rw [G.coe_neighborFinset, G.isClique_compl]; exact G.isIndepSet_neighborSet_of_triangleFree hG v, rfl⟩
    have hcu : Gᶜ.degree v < 6 := by_contra fun h => by
      obtain ⟨f, hf⟩ := Function.Embedding.exists_of_card_le_finset
        (α := Fin 6) (s := Gᶜ.neighborFinset v) (by simpa using not_lt.mp h)
      refine h6 (G.comap f) ⟨CliqueFree.comap (Embedding.comap f G).isContained hG, fun t ht => ?_⟩
      obtain ⟨a, b, c, hab, hac, hbc, _⟩ := is3Clique_iff.mp ht
      let ec := Embedding.complEquiv (Embedding.comap f G)
      refine hGc _ ((is3Clique_triple_iff.mpr
        ⟨ec.map_adj_iff.mpr hab, ec.map_adj_iff.mpr hac, ec.map_adj_iff.mpr hbc⟩).insert (a := v) ?_)
      intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl | rfl <;> exact (Gᶜ.mem_neighborFinset v _).mp (hf ⟨_, rfl⟩)
    rw [G.degree_compl, Fintype.card_fin] at hcu; omega
  have hsum := G.sum_degrees_eq_twice_card_edges
  simp [hdeg] at hsum; omega
