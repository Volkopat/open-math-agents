import OMAReductions.R_Jacobson_jacobson_conjecture_R1
import Mathlib

/-! Step Jacobson.jacobson_conjecture.R1.H1, the commutative and semiprimary cases. For a
commutative Noetherian ring this is Krull's intersection theorem,
`Ideal.iInf_pow_smul_eq_bot_of_le_jacobson`, applied to the ring itself. For a semiprimary ring the
Jacobson radical is nilpotent. -/

namespace OMA.JacobsonH1

open Ring

theorem main (R : Type) [inst : Ring R] [IsNoetherianRing R] [IsRightNoetherianRing R]
    (h : (∀ x y : R, x * y = y * x) ∨ IsSemiprimaryRing R) : Jacobson.JacobsonConjectureFor R := by
  unfold Jacobson.JacobsonConjectureFor
  rcases h with hcomm | hsp
  · letI cR : CommRing R := { inst with mul_comm := hcomm }
    have hle : jacobson R ≤ Ideal.jacobson (⊥ : Ideal R) := by rw [Ideal.jacobson_bot]
    have key := Ideal.iInf_pow_smul_eq_bot_of_le_jacobson (M := R) (jacobson R) hle
    simp only [smul_eq_mul, Ideal.mul_top] at key
    exact key
  · obtain ⟨n, hn⟩ := hsp.isNilpotent
    exact le_antisymm ((iInf_le _ n).trans (le_of_eq hn)) bot_le

end OMA.JacobsonH1

theorem OMA.solution : OMA.R_Jacobson_jacobson_conjecture_R1.H1 :=
  fun R _ _ _ h => OMA.JacobsonH1.main R h
