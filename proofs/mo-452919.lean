import OMAStatements.S_mo_452919
import Mathlib

/-!
A three-vertex counterexample to MathOverflow 452919, using the loops permitted
by the registered Digraph statement. Its edges contain the directed three-cycle
0 → 1 → 2 → 0, so the uniform return path below covers every edge.

The matrix sends (1,-1,0) to (-1,-1,1), then to zero. The generalized-eigenvector
obstruction follows @wtho704's pending proof #20527. The original Lean disproof
is by @OrangeHeadz (#11144), using Benjamin Steinberg's four-vertex example:
https://mathoverflow.net/a/452979. No minimum-size claim is made here.
-/

namespace MO452919

open Matrix

/-- The adjacency matrix of the counterexample, with integer entries. -/
def M : Matrix (Fin 3) (Fin 3) ℤ := !![0, 1, 1; 0, 1, 1; 1, 0, 1]

/-- The counterexample digraph. -/
def G : Digraph (Fin 3) := ⟨fun i j => M i j = 1⟩

instance decAdj : DecidableRel G.Adj := fun i j => inferInstanceAs (Decidable (M i j = 1))

/-- For each edge `u → v`, a directed path from `v` back to `u` through distinct vertices. -/
def pth (u v : Fin 3) : List (Fin 3) :=
  if u = v then [v] else if u = v + 1 then [v,u] else [v,v+1,u]

theorem edges : ∀ u v : Fin 3, G.Adj u v → OMA.S_mo_452919.EdgeOnCycle G u v := by
  intro u v h
  refine ⟨pth u v, ?_⟩
  revert u v
  decide

theorem not_diag [DecidableRel G.Adj] (P : Matrix (Fin 3) (Fin 3) ℂ) (d : Fin 3 → ℂ)
    (hP : IsUnit P.det)
    (h : OMA.S_mo_452919.adjMatrix G * P = P * Matrix.diagonal d) : False := by
  let A := OMA.S_mo_452919.adjMatrix G
  let x : Fin 3 → ℂ := ![1, -1, 0]
  let y : Fin 3 → ℂ := ![-1, -1, 1]
  have ⟨hx, hy⟩ : A *ᵥ x = y ∧ A *ᵥ y = 0 := by
    constructor <;> funext i <;> fin_cases i <;>
      norm_num [A, OMA.S_mo_452919.adjMatrix, G, M, x, y, mulVec, dotProduct,
        Fin.sum_univ_three, cons_val_two]
  have hmap (v : Fin 3 → ℂ) : A *ᵥ (P *ᵥ v) = P *ᵥ (fun i => d i * v i) := by
    rw [Matrix.mulVec_mulVec, h, ← Matrix.mulVec_mulVec]
    exact congrArg P.mulVec (funext (Matrix.mulVec_diagonal d v))
  have hunit : IsUnit P := (Matrix.isUnit_iff_isUnit_det P).mpr hP
  obtain ⟨z, hz⟩ := Matrix.mulVec_surjective_iff_isUnit.mpr hunit x
  let t : Fin 3 → ℂ := fun i => d i * z i
  have ht : P *ᵥ t = y := by
    change P *ᵥ (fun i => d i * z i) = y
    rw [← hmap, hz, hx]
  have hnull : P *ᵥ (fun i => d i * t i) = 0 := by
    rw [← hmap, ht, hy]
  have hzero : (fun i => d i * t i) = 0 :=
    Matrix.mulVec_injective_iff_isUnit.mpr hunit (hnull.trans (Matrix.mulVec_zero P).symm)
  have ht0 : t = 0 := by
    funext i
    rcases mul_eq_zero.mp (congrFun hzero i) with hdi | hti
    · simp [t, hdi]
    · exact hti
  have hy0 : y = 0 := by simpa [ht0] using ht.symm
  have hy1 := congrFun hy0 (1 : Fin 3)
  norm_num [y] at hy1

end MO452919

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_452919.main) := by
  intro h
  obtain ⟨P, d, hP, hPD⟩ := h (Fin 3) MO452919.G MO452919.edges
  exact MO452919.not_diag P d hP hPD
