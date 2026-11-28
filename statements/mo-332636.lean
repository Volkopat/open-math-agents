import Mathlib

/-!
# The full set of best approximations in the matrix spectral norm

Source: Doris, https://mathoverflow.net/questions/332636 (CC BY-SA 4.0).
Contribution by @connoranderson.

At a suitable minimizer the common maximal right singular vectors and their
left images determine all affine directions of the minimizer set. The rank
of the explicitly defined direction subspace gives its affine dimension.
-/

namespace OMA.S_mo_332636
open Matrix
open scoped Matrix
abbrev Rect (m n : ℕ) := Matrix (Fin m) (Fin n) ℝ
noncomputable def specNorm {m n : ℕ} (A : Rect m n) :=
  ‖A.toEuclideanLin.toContinuousLinearMap‖
def opt {m n : ℕ} (L : Submodule ℝ (Rect m n)) (X : Rect m n) (c : ℝ) :=
  {M | M ∈ L ∧ specNorm (X-M)=c}
def active {m n : ℕ} (R : Rect m n) (c : ℝ) (v : Fin n → ℝ) : Prop :=
  Rᵀ *ᵥ (R*ᵥv)=c^2 • v
def directions {m n : ℕ} (L : Submodule ℝ (Rect m n)) (R : Rect m n) (c : ℝ) :
    Submodule ℝ (Rect m n) where
  carrier := {H | H ∈ L ∧ ∀ v,active R c v → H*ᵥv=0 ∧ Hᵀ*ᵥ(R*ᵥv)=0}
  zero_mem' := ⟨L.zero_mem,by simp⟩
  add_mem' := by
    rintro H K ⟨hH,hHa⟩ ⟨hK,hKa⟩
    refine ⟨L.add_mem hH hK,?_⟩
    intro v hv
    simp only [Matrix.transpose_add,Matrix.add_mulVec,(hHa v hv).1,(hHa v hv).2,(hKa v hv).1,(hKa v hv).2,add_zero,and_self]
  smul_mem' := by
    rintro c H ⟨hH,hHa⟩
    refine ⟨L.smul_mem c hH,?_⟩
    intro v hv
    simp only [Matrix.transpose_smul,Matrix.smul_mulVec,(hHa v hv).1,(hHa v hv).2,smul_zero,and_self]

theorem main : ∀ (m n : ℕ) (L : Submodule ℝ (Rect m n)) (X : Rect m n) (c : ℝ),
    0 < c → IsLeast ((fun M : Rect m n => specNorm (X-M)) '' (L : Set (Rect m n))) c →
    ∃ M₀ ∈ opt L X c,
      Submodule.span ℝ ((fun M => M-M₀) '' opt L X c) = directions L (X-M₀) c ∧
      ((∃! M, M ∈ opt L X c) ↔ directions L (X-M₀) c=⊥) ∧
      ∀ M ∈ opt L X c, ∀ v, active (X-M₀) c v →
        (X-M)*ᵥv=(X-M₀)*ᵥv ∧ (X-M)ᵀ*ᵥ((X-M₀)*ᵥv)=c^2 • v := by
  sorry
end OMA.S_mo_332636
