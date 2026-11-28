import OMAReductions.R_oeis_a001438_R1

/-! An explicit pair of orthogonal Latin squares of order 10, found by computer search: a random
Latin square `sqA` with 868 transversals, and `sqB` built from 10 disjoint transversals of `sqA`
found by exact cover. The Latin property of both squares and their orthogonality are checked by
the kernel. -/

namespace OMA.A001438

def sqA : Fin 10 → Fin 10 → Fin 10 :=
  ![![1, 0, 2, 6, 8, 3, 7, 5, 4, 9],
    ![0, 8, 3, 5, 4, 2, 1, 9, 7, 6],
    ![9, 6, 4, 1, 5, 0, 2, 7, 3, 8],
    ![2, 5, 9, 8, 0, 4, 6, 3, 1, 7],
    ![3, 7, 0, 4, 6, 9, 8, 1, 5, 2],
    ![7, 3, 1, 9, 2, 6, 4, 0, 8, 5],
    ![4, 2, 6, 0, 1, 7, 5, 8, 9, 3],
    ![8, 4, 7, 2, 3, 5, 9, 6, 0, 1],
    ![5, 9, 8, 3, 7, 1, 0, 2, 6, 4],
    ![6, 1, 5, 7, 9, 8, 3, 4, 2, 0]]

def sqB : Fin 10 → Fin 10 → Fin 10 :=
  ![![5, 6, 0, 1, 7, 3, 4, 2, 8, 9],
    ![8, 0, 2, 3, 9, 6, 1, 4, 7, 5],
    ![3, 8, 7, 4, 6, 9, 2, 0, 5, 1],
    ![1, 4, 6, 8, 2, 5, 0, 7, 9, 3],
    ![4, 5, 1, 2, 3, 8, 9, 6, 0, 7],
    ![9, 1, 3, 0, 4, 7, 6, 5, 2, 8],
    ![0, 9, 4, 7, 8, 2, 5, 3, 1, 6],
    ![6, 3, 8, 5, 0, 1, 7, 9, 4, 2],
    ![7, 2, 5, 9, 1, 0, 3, 8, 6, 4],
    ![2, 7, 9, 6, 5, 4, 8, 1, 3, 0]]

end OMA.A001438

theorem OMA.solution : OMA.R_oeis_a001438_R1.H1 := by
  unfold OMA.R_oeis_a001438_R1.H1 OMA.S_oeis_a001438.HasMOLS
  refine ⟨![OMA.A001438.sqA, OMA.A001438.sqB], ?_, ?_⟩
  · unfold OMA.S_oeis_a001438.IsLatin
    decide +kernel
  · unfold OMA.S_oeis_a001438.Orthogonal
    decide +kernel
