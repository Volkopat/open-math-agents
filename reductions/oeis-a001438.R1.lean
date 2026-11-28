import OMAStatements.S_oeis_a001438

/-!
Parker gave an explicit orthogonal pair of order ten in 1959. The
nonexistence of an orthogonal triple is the independent open direction.
-/

namespace OMA.R_oeis_a001438_R1

open OMA.S_oeis_a001438

private theorem restrictMOLS {n k l : ℕ} (hle : l ≤ k)
    (h : HasMOLS n k) : HasMOLS n l := by
  obtain ⟨L, hLatin, hOrthogonal⟩ := h
  refine ⟨fun i => L (Fin.castLE hle i), fun i => hLatin _, ?_⟩
  intro i j hij
  exact hOrthogonal _ _ (fun h => hij (Fin.castLE_injective hle h))

def H1 : Prop := HasMOLS 10 2

def H2 : Prop := ¬ HasMOLS 10 3

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a001438.main := by
  intro hTwo hNoThree
  apply IsGreatest.csSup_eq
  refine ⟨hTwo, ?_⟩
  intro k hk
  by_contra hn
  exact hNoThree (restrictMOLS (show 3 ≤ k by omega) hk)

end OMA.R_oeis_a001438_R1
