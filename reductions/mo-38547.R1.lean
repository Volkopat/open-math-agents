import OMAStatements.S_mo_38547
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
Bacher's rooted tree-color product is the diagonal-degree Cramer vector over
the binary field.  Step one is the combinatorial transfer-current identity.
Step two only asks a Turing machine to compute grounded binary Laplacian
determinants and cofactors.  The proof below converts the two expressions
for all symmetric matrices, including singular ones.
-/

open Matrix OMA.S_mo_38547

namespace OMA.R_mo_38547_R1

/-- Convert the rooted spanning-tree colorings into signed tree-path currents
by Cauchy–Binet on the reduced incidence matrix with one row replaced. -/
def H1 : Prop := by
  classical
  exact ∀ (n : ℕ) (G : SimpleGraph (Fin (n+1))), G.Connected →
    let L := (G.lapMatrix (ZMod 2)).submatrix Fin.succ Fin.succ
    output G = false :: List.ofFn (fun v => decide (L.cramer L.diag v = 1))

/-- Compute binary principal cofactors of a grounded Laplacian from
the adjacency encoding by polynomial-time Gaussian elimination. -/
def H2 : Prop := by
  classical
  exact ∃ solve : List Bool → List Bool,
    Nonempty (Turing.TM2ComputableInPolyTime id id solve) ∧
    ∀ (n : ℕ) (G : SimpleGraph (Fin (n+1))),
      let L := (G.lapMatrix (ZMod 2)).submatrix Fin.succ Fin.succ
      solve (input G) = false :: List.ofFn (fun v => decide (L.det * L.adjugate v v = 1))

lemma add_self_two (a : ZMod 2) : a + a = 0 := by
  fin_cases a <;> decide

lemma square_two (a : ZMod 2) : a * a = a := by
  exact (by decide : ∀ x : ZMod 2, x * x = x) a

lemma symmetric_sum {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → ι → ZMod 2) (h : ∀ i j, f i j = f j i) :
    (∑ i ∈ s, ∑ j ∈ s, f i j) = ∑ i ∈ s, f i i := by
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha, Finset.sum_add_distrib, ih]
    have hc : (∑ i ∈ s, f i a) = ∑ i ∈ s, f a i := Finset.sum_congr rfl fun i _ => h i a
    rw [hc]
    generalize (∑ i ∈ s, f a i) = u
    rw [show f a a + u + (u + ∑ i ∈ s, f i i) =
        f a a + (u + u) + ∑ i ∈ s, f i i by abel, add_self_two, add_zero]

lemma adjugate_diag {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι (ZMod 2)) (hA : A.IsSymm) (v : ι) :
    (A.adjugate *ᵥ A.diag) v = A.det * A.adjugate v v := by
  let f := fun i j : ι => A.adjugate v i * A i j * A.adjugate v j
  have hs : ∀ i j, f i j = f j i := by
    intro i j
    dsimp [f]
    rw [hA.apply i j]
    ring
  have hdiag (i : ι) : f i i = A.adjugate v i * A i i := by
    dsimp [f]
    rw [show A.adjugate v i * A i i * A.adjugate v i =
      (A.adjugate v i * A.adjugate v i) * A i i by ring, square_two]
  have hm : (A.adjugate * A * A.adjugate) v v = A.det * A.adjugate v v := by
    rw [Matrix.adjugate_mul, Matrix.smul_mul, one_mul]
    rfl
  rw [← hm, Matrix.mul_apply]
  simp only [Matrix.mul_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  change (∑ i, A.adjugate v i * A i i) =
    ∑ i, ∑ j, A.adjugate v i * A i j * A.adjugate j v
  calc
    _ = ∑ i, f i i := Finset.sum_congr rfl fun i _ => (hdiag i).symm
    _ = ∑ i, ∑ j, f i j := (symmetric_sum Finset.univ f hs).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      dsimp [f]
      rw [hA.adjugate.apply v j]

theorem main : H1 → H2 → type_of% @OMA.S_mo_38547.main := by
  classical
  intro h1 h2
  obtain ⟨solve, machine, hsolve⟩ := h2
  refine ⟨solve, machine, ?_⟩
  intro n G hG
  let L := (G.lapMatrix (ZMod 2)).submatrix Fin.succ Fin.succ
  have hL : L.IsSymm := (G.isSymm_lapMatrix (ZMod 2)).submatrix Fin.succ
  rw [hsolve n G, h1 n G hG]
  change false :: List.ofFn (fun v => decide (L.det * L.adjugate v v = 1)) =
    false :: List.ofFn (fun v => decide (L.cramer L.diag v = 1))
  rw [Matrix.cramer_eq_adjugate_mulVec]
  simp_rw [adjugate_diag L hL]

end OMA.R_mo_38547_R1
