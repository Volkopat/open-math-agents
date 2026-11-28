import Mathlib

/-!
# Largest circular disks inside an ellipsoid

Source: Nandakumar R, https://mathoverflow.net/questions/400902 (CC BY-SA 4.0).
Credit: @connoranderson.

Coordinates are principal-axis coordinates, with semiaxes a ≥ b ≥ c > 0.
A translated planar disk is parametrized by an orthonormal pair. The first
claim gives the optimal radius; the next describes all disks attaining it.
The last claim realizes the optimum as an entire circular plane section.
Pietro Majer identified the middle semiaxis in comments on the question.
-/

namespace OMA.S_mo_400902

abbrev Point := Fin 3 → ℝ

def Frame (u v : Point) : Prop := u ⬝ᵥ u = 1 ∧ v ⬝ᵥ v = 1 ∧ u ⬝ᵥ v = 0

noncomputable def quad (a b c : ℝ) (x : Point) :=
  (x 0 / a)^2 + (x 1 / b)^2 + (x 2 / c)^2

def Fits (a b c r : ℝ) (o u v : Point) : Prop :=
  ∀ s t : ℝ, s^2+t^2 ≤ r^2 → quad a b c (o+s • u+t • v) ≤ 1

noncomputable def gapX (a b : ℝ) := (b⁻¹)^2-(a⁻¹)^2
noncomputable def gapZ (b c : ℝ) := (c⁻¹)^2-(b⁻¹)^2

theorem main : ∀ a b c : ℝ, 0<c → c≤b → b≤a →
    (∀ (r : ℝ) (o u v : Point), 0≤r → Frame u v → Fits a b c r o u v → r≤b) ∧
    (∀ o u v : Point, Frame u v → (Fits a b c b o u v ↔
      o=0 ∧ (b=c ∨ ∃ m : ℝ, gapZ b c * m^2 ≤ gapX a b ∧
        u 2=m*u 0 ∧ v 2=m*v 0))) ∧
    (∃ u v : Point, Frame u v ∧ ∀ s t : ℝ,
      quad a b c (s • u+t • v) = (s^2+t^2)/b^2) := by
  sorry

end OMA.S_mo_400902
