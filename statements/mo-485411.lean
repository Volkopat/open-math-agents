import Mathlib

/-!
# Two least-loss criteria in classical multidimensional scaling

Source: guest, https://mathoverflow.net/questions/485411 (CC BY-SA).
K. V. Mardia (1978), Section 2, https://doi.org/10.1080/03610927808827707,
credits J. C. Gower (1966) for the Euclidean projection criterion.
Credit: @connoranderson. Centering is explicit. Projectors are real symmetric
idempotents of prescribed trace, their dimension. Squaring the Frobenius norm
preserves all its minimizers.
-/
namespace OMA.S_mo_485411
open Matrix Finset
abbrev Rect (n d : ℕ) := Matrix (Fin n) (Fin d) ℝ
abbrev Mat (d : ℕ) := Rect d d
def Projector {d : ℕ} (k : ℕ) (P : Mat d) : Prop :=
  Pᵀ = P ∧ P*P=P ∧ P.trace=k
def Centered {n d : ℕ} (X : Rect n d) : Prop := ∀ j, ∑ i, X i j=0
def dsq {n d} (X : Rect n d) (i j : Fin n) : ℝ := ∑ l,(X i l-X j l)^2
def distanceLoss {n d} (X : Rect n d) (P : Mat d) : ℝ :=
  ∑ i, ∑ j, (dsq X i j - dsq (X*P) i j)
def gramLoss {n d} (X : Rect n d) (P : Mat d) : ℝ :=
  ∑ i, ∑ j, ((X*Xᵀ) i j - ((X*P)*(X*P)ᵀ) i j)^2
def Minimizes {d} (k : ℕ) (f : Mat d → ℝ) (P : Mat d) : Prop :=
  Projector k P ∧ ∀ Z, Projector k Z → f P≤f Z

theorem main :
    (∀ (d k : ℕ) (P : Mat d), Projector k P ↔ Pᵀ=P ∧ P*P=P ∧ P.rank=k) ∧
    (∀ (n d k : ℕ) (X : Rect n d), 0<n → k<d → Centered X →
      (∃ P, Minimizes k (distanceLoss X) P) ∧
        ∀ P, Minimizes k (distanceLoss X) P ↔ Minimizes k (gramLoss X) P) ∧
    (∃ (X : Rect 2 2) (P Z : Mat 2), Minimizes 1 (distanceLoss X) P ∧
      Projector 1 Z ∧ gramLoss X Z < gramLoss X P) := by
  sorry
end OMA.S_mo_485411
