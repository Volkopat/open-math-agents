import Mathlib

/-!
# Optimizing the eigenvalue ratio for a Lyapunov equation

Source: Ludwig, https://mathoverflow.net/questions/299752 (CC BY-SA 4.0).
Credit: @connoranderson. Rodrigo de Azevedo linked the related companion
matrix case, https://mathoverflow.net/questions/249052.

The source assumes positive definite solutions for positive definite forcing
matrices. In particular, S is the solution for identity forcing. The result
below only requires this instance of the assumption. It gives the maximum,
attained for identity forcing, and parametrizes all optimizing pairs (P,Q).
The first matrix in each pair is the solution, and the second is the forcing.
-/
namespace OMA.S_mo_299752
open Matrix
abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ
def lyap {n : ℕ} (A P : Mat n) := -(A*P + P*Aᵀ)
noncomputable def low {n : ℕ} (M : Mat n) := sInf (spectrum ℝ M)
noncomputable def high {n : ℕ} (M : Mat n) := sSup (spectrum ℝ M)
def ratios {n : ℕ} (A : Mat n) : Set ℝ :=
  {r | ∃ P Q : Mat n, P.PosDef ∧ Q.PosDef ∧ lyap A P=Q ∧ r=low Q/high P}
def optimal {n : ℕ} (A : Mat n) (value : ℝ) : Set (Mat n × Mat n) :=
  {w | w.1.PosDef ∧ w.2.PosDef ∧ lyap A w.1=w.2 ∧ low w.2/high w.1=value}
def parameters {n : ℕ} (A S : Mat n) : Set (Mat n × Mat n) :=
  {w | ∃ (q : ℝ) (H : Mat n), 0 < q ∧ H.PosSemidef ∧
    (high S • (1:Mat n) - S - H).PosSemidef ∧ (lyap A H).PosSemidef ∧
    w.1=q • (S+H) ∧ w.2=q • (1+lyap A H)}

theorem main : ∀ (n : ℕ) (A S : Mat (n+1)), S.PosDef → lyap A S=1 →
    IsGreatest (ratios A) (high S)⁻¹ ∧ optimal A (high S)⁻¹ = parameters A S := by
  sorry
end OMA.S_mo_299752
