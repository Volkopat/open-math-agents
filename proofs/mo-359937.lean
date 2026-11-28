import OMAStatements.S_mo_359937
import Mathlib

/-! The dense Householder reflection 2J/n−I gives counterexamples in all
dimensions at least three except four. Here J is the all-ones matrix. -/
namespace CubicReflection
open Matrix
noncomputable section

def J (n : ℕ) : Matrix (Fin n) (Fin n) ℝ := fun _ _ => 1
def linear (n : ℕ) (a b : ℝ) : Matrix (Fin n) (Fin n) ℝ := a • 1 + b • J n

lemma JJ (n : ℕ) : J n * J n = (n:ℝ) • J n := by
  ext i j; simp [J,Matrix.mul_apply]
lemma prod_linear (n : ℕ) (a b c d : ℝ) :
    linear n a b * linear n c d = linear n (a*c) (a*d+b*c+n*b*d) := by
  unfold linear
  simp only [Matrix.add_mul,Matrix.mul_add,Matrix.smul_mul,Matrix.mul_smul,Matrix.one_mul,
    Matrix.mul_one,JJ,smul_smul,add_smul]
  module
lemma linear_T (n : ℕ) (a b : ℝ) : (linear n a b).transpose = linear n a b := by
  ext i j; simp [linear,J,Matrix.one_apply,eq_comm]

def H (n : ℕ) := linear n (-1) (2/(n:ℝ))

lemma H_square {n : ℕ} (hn : 0 < n) : H n * H n = 1 := by
  have nz : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [H,prod_linear]
  have : (-1:ℝ)*(2/n)+(2/n)*(-1)+n*(2/n)*(2/n) = 0 := by field_simp; ring
  rw [this]; norm_num [linear]

lemma cube_linear (n : ℕ) (a b : ℝ) :
    (linear n a b).map (fun x => x^3) = linear n ((a+b)^3-b^3) (b^3) := by
  ext i j; by_cases eqn : i=j <;> simp [linear,J,Matrix.one_apply,eqn]

lemma cube_eq (n : ℕ) (a b : ℝ) (i j : Fin n) :
    ∑ k, linear n a b i k ^ 3 * linear n a b j k =
    ∑ k, linear n a b j k ^ 3 * linear n a b i k := by
  let M := ((linear n a b).map fun x => x^3) * (linear n a b).transpose
  have h : M.transpose = M := by
    dsimp only [M]
    rw [linear_T,cube_linear,prod_linear,linear_T]
  exact congrArg (fun A : Matrix (Fin n) (Fin n) ℝ => A j i) h

lemma dense {n : ℕ} (hn : 3 ≤ n) (i j : Fin n) : H n i j ≠ 0 := by
  have hr : (3:ℝ) ≤ n := by exact_mod_cast hn
  by_cases eqn : i=j
  · simp [H,linear,J,Matrix.one_apply,eqn]
    intro e
    have nz : (n:ℝ) ≠ 0 := by linarith
    field_simp at e
    linarith
  · simp [H,linear,J,Matrix.one_apply,eqn]; positivity

lemma unequal {n : ℕ} (hn : 3 ≤ n) (hfour : n ≠ 4) {i j : Fin n} (hij : i ≠ j) :
    |H n i i| ≠ |H n i j| := by
  have hr : (3:ℝ) ≤ n := by exact_mod_cast hn
  have pos : (0:ℝ) < n := by linarith
  have neg : (-1:ℝ) + 2/n ≤ 0 := by
    have := (div_le_iff₀ pos).mpr (show (2:ℝ) ≤ 1*n by linarith)
    linarith
  have diag : H n i i = -1+2/(n:ℝ) := by simp [H,linear,J,Matrix.one_apply]
  have off : H n i j = 2/(n:ℝ) := by simp [H,linear,J,Matrix.one_apply,hij]
  rw [diag,off,abs_of_nonpos neg,abs_of_pos (show (0:ℝ) < 2/n by positivity)]
  intro e
  field_simp at e
  exact hfour (by exact_mod_cast (show (n:ℝ)=4 by linarith))

end
end CubicReflection
namespace CubicReflection
open Matrix OMA.S_mo_359937

/-- In each dimension at least three other than four the same reflection is
dense, has both cubic symmetries, and has different absolute diagonal and
off-diagonal entries. -/
lemma family {n : ℕ} (hn : 3 ≤ n) (h4 : n ≠ 4) :
    H n * (H n).transpose = 1 ∧ (H n).transpose * H n = 1 ∧
    ¬ HasBlockDecomposition (H n) ∧
    (∀ i j, ∑ k, H n i k ^ 3 * H n j k = ∑ k, H n j k ^ 3 * H n i k) ∧
    (∀ i j, ∑ k, H n k i ^ 3 * H n k j = ∑ k, H n k j ^ 3 * H n k i) ∧
    ∃ i j, H n i i ≠ 0 ∧ H n i j ≠ 0 ∧ |H n i i| ≠ |H n i j| := by
  have sy : (H n).transpose = H n := linear_T _ _ _
  have cu := cube_eq n (-1) (2/(n:ℝ))
  have rows (i j : Fin n) := cu i j
  have xy (i j : Fin n) : H n i j = H n j i :=
    congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M j i) sy
  refine ⟨by rw [sy]; exact H_square (by omega),by rw [sy]; exact H_square (by omega),?_,rows,?_,?_⟩
  · rintro ⟨S,T,⟨i,hi⟩,hs,ht,hzero⟩
    have hu : T = Finset.univ := Finset.eq_univ_of_forall (fun j => by
      by_contra missing
      exact dense hn i j (hzero i j (Or.inl ⟨hi,missing⟩)))
    rw [hu,Finset.card_univ,Fintype.card_fin] at ht
    omega
  · intro i j
    calc
      _ = ∑ k, H n i k ^ 3 * H n j k := Finset.sum_congr rfl fun k _ => by rw [xy k i,xy k j]
      _ = ∑ k, H n j k ^ 3 * H n i k := rows i j
      _ = _ := Finset.sum_congr rfl fun k _ => by rw [xy k j,xy k i]
  · let i : Fin n := ⟨0,by omega⟩
    let j : Fin n := ⟨1,by omega⟩
    exact ⟨i,j,dense hn _ _,dense hn _ _,unequal hn h4 (by intro e; have := congrArg Fin.val e; simp [i,j] at this)⟩
end CubicReflection

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_359937.main) := by
  intro h
  obtain ⟨orth,orth',irr,rows,cols,i,j,hii,hij,ne⟩ :=
    CubicReflection.family (n:=3) (by decide) (by decide)
  exact ne (h 3 _ orth orth' irr rows cols i i i j hii hij)
