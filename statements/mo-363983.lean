import Mathlib

/-!
# When separated kernel matrices have uniformly bounded condition numbers

Source: Rajesh Dachiraju, https://mathoverflow.net/questions/363983 (CC BY-SA 4.0).
Credit: @connoranderson.

For an ordered configuration in one dimension, separation by ε is equivalent
to every interval of k consecutive gaps having length at least kε. The
ridged matrix has entries g(|xᵢ−xⱼ|) plus α on the diagonal. Its spectral
condition number is the ratio of its greatest to its least eigenvalue.

The constant kernel gives unbounded condition numbers already on grids of
exactly fixed mesh. For nonnegative, nonincreasing radial profiles in one
dimension, uniform boundedness is equivalent to summability on that mesh.
-/
namespace OMA.S_mo_363983
open Matrix
abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ
noncomputable def gram {n : ℕ} (g : ℝ → ℝ) (x : Fin n → ℝ) : Mat n :=
  Matrix.of (fun i j => g |x i - x j|)
def positiveKernel (g : ℝ → ℝ) : Prop := ∀ (n : ℕ) (x : Fin n → ℝ), (gram g x).PosSemidef
def separated {n : ℕ} (ε : ℝ) (x : Fin n → ℝ) : Prop :=
  ∀ i j, i < j → ε ≤ x j - x i
noncomputable def ridge {n : ℕ} (g : ℝ → ℝ) (α : ℝ) (x : Fin n → ℝ) : Mat n :=
  gram g x + α • 1
noncomputable def condition {n : ℕ} (A : Mat n) : ℝ :=
  sSup (spectrum ℝ A) / sInf (spectrum ℝ A)
def boundedCondition (g : ℝ → ℝ) (α ε : ℝ) : Prop :=
  ∃ K : ℝ, ∀ (n : ℕ) (x : Fin (n+1) → ℝ), separated ε x → condition (ridge g α x) ≤ K

theorem main :
    (positiveKernel (fun _ => 1) ∧
      (∀ (n : ℕ) (x : Fin (n+2) → ℝ) (α : ℝ), 0 < α →
        condition (ridge (fun _ => 1) α x) = (α+(n+2))/α) ∧
      ∀ α ε : ℝ, 0 < α → 0 < ε → ∀ K : ℝ,
      ∃ n : ℕ, K < condition (ridge (fun _ => 1) α (fun i : Fin (n+2) => (i.val:ℝ)*ε))) ∧
    ∀ (g : ℝ → ℝ) (α ε : ℝ), positiveKernel g → (∀ t ≥ 0, 0 ≤ g t) →
      AntitoneOn g (Set.Ici 0) → 0 < α → 0 < ε →
      (boundedCondition g α ε ↔ Summable (fun j : ℕ => g ((j:ℝ)*ε))) := by
  sorry
end OMA.S_mo_363983
