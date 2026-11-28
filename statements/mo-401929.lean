import Mathlib

/-!
# Recovering a Gram matrix after translating all samples

Source: rostader, https://mathoverflow.net/questions/401929 (CC BY-SA).
Credit: @connoranderson.
The shifted matrix determines the original quadratic form on the orthogonal
complement of the translation. Even with unit samples and a simple leading
eigenvector in the translation direction, its full spectrum can vary.
-/
namespace OMA.S_mo_401929
open Matrix Finset
abbrev Vec (n : ℕ) := Fin n → ℝ
abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ
def gram {ι : Type*} [Fintype ι] {n : ℕ} (x : ι → Vec n) : Mat n := ∑ t,vecMulVec (x t) (x t)
abbrev Sample := Fin 2 × Fin 6

theorem main :
    (∀ {T n : ℕ} (x : Fin T → Vec n) (e : Vec n),
      let D := gram (fun t => x t+e) - gram x
      D = vecMulVec ((∑ t,x t) + (T:ℝ) • e) e + vecMulVec e (∑ t,x t) ∧ D.rank ≤ 2 ∧
      ∀ u : Vec n, u ≠ 0 → u ⬝ᵥ e=0 → ∀ a b : ℝ,
        gram x *ᵥ u=a • u → gram (fun t => x t+e) *ᵥ u=b • u → a=b) ∧
    (∃ x y : Sample → Vec 2, (∀ t,x t ⬝ᵥ x t=1 ∧ y t ⬝ᵥ y t=1) ∧
      gram (fun t => x t+![1,0]) = !![72/5,0;0,32/5] ∧
      gram (fun t => y t+![1,0]) = !![72/5,0;0,32/5] ∧
      gram x = !![28/5,0;0,32/5] ∧ gram y = !![28/5,24/5;24/5,32/5] ∧
      (gram x).charpoly ≠ (gram y).charpoly) := by
  sorry
end OMA.S_mo_401929
