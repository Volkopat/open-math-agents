import Mathlib

/-!
# MathOverflow 128018

Source: https://mathoverflow.net/questions/128018
-/

namespace OMA.S_mo_128018

open Polynomial

noncomputable def integerImage (P : ℤ[X]) : ℚ[X] := P.map (Int.castRingHom ℚ)

def monicGCD (P Q G : ℚ[X]) : Prop :=
  G.Monic ∧ G ∣ P ∧ G ∣ Q ∧ ∀ H : ℚ[X], H ∣ P → H ∣ Q → H ∣ G

def leastIntegralMultiple (G : ℚ[X]) (D : ℤ[X]) : Prop :=
  ∃ n : ℕ, 0 < n ∧ integerImage D = C (n : ℚ) * G ∧
    ∀ m : ℕ, 0 < m →
      (∃ E : ℤ[X], integerImage E = C (m : ℚ) * G) → n ≤ m

noncomputable def complexValue (P : ℤ[X]) (x : ℂ) : ℂ :=
  (P.map (Int.castRingHom ℂ)).eval x

theorem main : ∀ (P Q D : ℤ[X]) (G : ℚ[X]),
    monicGCD (integerImage P) (integerImage Q) G → leastIntegralMultiple G D →
    ∀ x : ℂ, (∃ a : ℤ, complexValue P x = a) → (∃ b : ℤ, complexValue Q x = b) →
      ∃ a b d : ℤ, complexValue P x = a ∧ complexValue Q x = b ∧
        complexValue D x = d ∧ d ∣ a ∧ d ∣ b := by
  sorry

end OMA.S_mo_128018
