import Mathlib

/-!
# Sign of a constrained energy for periodic Sobolev functions

Source: R. N. Marley, https://mathoverflow.net/questions/332533 (CC BY-SA 4.0).
There are n+1 spatial coordinates, and the index 0 denotes the distinguished
first one. The period relation is the simultaneous translation written in the
question. The real and imaginary parts are recorded separately, along with
their weak partial derivatives. The two proposed energies use the same constraint.
Credit: @connoranderson.
-/

namespace OMA.S_mo_332533
open Set MeasureTheory Finset

abbrev Space (n : ℕ) := Fin (n+1) → ℝ

def locallyL2 {n : ℕ} (f : Space n → ℝ) : Prop :=
  AEStronglyMeasurable f volume ∧ LocallyIntegrable (fun x => (f x)^2) volume

def sobolev {n : ℕ} (f : Space n → ℝ) (df : Space n → Space n) : Prop :=
  locallyL2 f ∧ ∀ i, locallyL2 (fun x => df x i) ∧ ∀ φ : Space n → ℝ,
    ContDiff ℝ ⊤ φ → HasCompactSupport φ →
    (∫ x, f x * fderiv ℝ φ x (Pi.single i 1)) = -∫ x, df x i * φ x

def periodic {n : ℕ} (T : ℝ) (f : Space n → ℝ) : Prop :=
  ∀ x, f (fun i => x i+T) = f x

noncomputable def constraint {n : ℕ} (T : ℝ) (u : Space n → ℝ) (dv : Space n → Space n) : ℝ :=
  ∫ x in Icc (0:Space n) (fun _ => T), dv x 0 * (u x-1)

noncomputable def energy {n : ℕ} (full : Bool) (T : ℝ) (u : Space n → ℝ)
    (du dv : Space n → Space n) : ℝ :=
  ∫ x in Icc (0:Space n) (fun _ => T),
      (if full then ∑ i, (du x i)^2 else (du x 0)^2)/2 +
        dv x 0 / Real.sqrt 2 * (u x-1)^2

def positiveForSmall (full : Bool) : Prop :=
  ∀ (n : ℕ) (T : ℝ), 0<T → ∃ δ : ℝ, 0<δ ∧ ∀ ε : ℝ, 0<ε → ε<δ →
    ∀ (u v : Space n → ℝ) (du dv : Space n → Space n),
      periodic T u → periodic T v → sobolev u du → sobolev v dv →
      constraint T u dv = ε → 0 < energy full T u du dv

theorem main : positiveForSmall false ∨ positiveForSmall true := by
  sorry

end OMA.S_mo_332533
