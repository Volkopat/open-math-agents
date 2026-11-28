import Mathlib

/-!
# Gaussian Gram matrices and entrywise powers

Source: Titouan Vayer, https://mathoverflow.net/questions/462055 (CC BY-SA 4.0).
Credit: @connoranderson.

The finite-dimensional form of Schoenberg's criterion characterizes Gaussian
Gram matrices with positive entries, unit diagonal and symmetry by positive
semidefiniteness of their positive entrywise powers. The coordinates below
give squared Euclidean distance on at most n coordinates.
-/

namespace OMA.S_mo_462055

noncomputable def pw {n} (C : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of (fun i j => C i j ^ t)

noncomputable def anch {n} (C : Matrix (Fin n) (Fin n) ℝ) (a : Fin n) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of (fun i j => (Real.log (C i j)-Real.log (C i a)-Real.log (C a j))/2)

def Gaussian {n} (C : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∃ x : Fin n → Fin n → ℝ, ∀ i j, C i j = Real.exp (-(∑ l, (x i l-x j l)^2))

theorem main : ∀ {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ),
    Gaussian C ↔ C.IsSymm ∧ (∀ i, C i i=1) ∧ (∀ i j, 0<C i j) ∧
      ∀ t : ℝ, 0<t → (pw C t).PosSemidef := by
  sorry

end OMA.S_mo_462055
