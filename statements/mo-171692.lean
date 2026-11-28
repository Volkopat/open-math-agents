import Mathlib

/-!
# Relative entropy along a majorization chain

Source: prime, https://mathoverflow.net/questions/171692 (CC BY-SA 3.0).
Credit: @connoranderson.

A triple of strictly positive distributions on three outcomes simultaneously
reverses both proposed inequalities. The two comparisons do hold under the
respective neighboring likelihood-ratio hypotheses below.
-/

namespace OMA.S_mo_171692

noncomputable def kl {n} (P Q : Fin n → ℝ) : ℝ := ∑ i, P i * Real.log (P i / Q i)

def Dist {n} (P : Fin n → ℝ) : Prop := (∀ i, 0 < P i) ∧ (∑ i, P i) = 1 ∧ Antitone P

def Majorizes {n} (P Q : Fin n → ℝ) : Prop :=
  (∑ i, P i) = (∑ i, Q i) ∧ ∀ k : ℕ,
    (∑ i : Fin n, if i.val < k then Q i else 0) ≤ ∑ i : Fin n, if i.val < k then P i else 0

theorem main : (∃ P Q R : Fin 3 → ℝ, Dist P ∧ Dist Q ∧ Dist R ∧
      Majorizes P Q ∧ Majorizes Q R ∧ kl P R < kl P Q ∧ kl R P < kl Q P) ∧
    (∀ P Q R : Fin 2 → ℝ, Dist P → Dist Q → Dist R → Majorizes P Q → Majorizes Q R →
      kl P Q ≤ kl P R ∧ kl Q P ≤ kl R P) ∧
    ∀ {n} (P Q R : Fin n → ℝ), Dist P → Dist Q → Dist R →
      Majorizes P Q → Majorizes Q R →
      (Antitone (fun i => Q i/R i) → kl P Q ≤ kl P R) ∧
      (Antitone (fun i => P i/Q i) → kl Q P ≤ kl R P) := by
  sorry

end OMA.S_mo_171692
