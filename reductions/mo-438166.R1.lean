import OMAStatements.S_mo_438166
import Mathlib

/- Square-zero base change and unbounded finite Tor amplitudes, following
OpenAI, openai/math at 3344da59 (Apache-2.0); MathOverflow question 438166
by Finitistic dimension (CC BY-SA). -/
namespace OMA.R_mo_438166_R1
open CategoryTheory CategoryTheory.Limits
noncomputable section

def H1 : Prop := ∃ (A : Type) (_ : Ring A) (_ : Algebra ℂ A) (D : Type) (_ : Ring D)
    (e : A →+* D) (g : ℕ) (F : ModuleCat.{0} A ⥤ ModuleCat.{0} D) (_ : F.Additive),
    Module.Finite ℂ A ∧ Function.Surjective e ∧
    (∀ x y : A, e x = 0 → e y = 0 → x*y = 0) ∧
    (∀ V : ModuleCat.{0} D, HasProjectiveDimensionLE V g) ∧
    Nonempty (F ⊣ ModuleCat.restrictScalars e) ∧
    ∀ m : ℕ, ∃ N : ModuleCat.{0} A, Module.Finite A N ∧
      (∃ b : ℕ, ∀ n > b, IsZero ((F.leftDerived n).obj N)) ∧
      ∃ n ≥ m, ¬ IsZero ((F.leftDerived n).obj N)

def H2 : Prop := ∀ (A : Type) [Ring A] [Algebra ℂ A] (D : Type) [Ring D]
    (e : A →+* D) (g : ℕ) (F : ModuleCat.{0} A ⥤ ModuleCat.{0} D) [F.Additive],
    Module.Finite ℂ A → Function.Surjective e →
    (∀ x y : A, e x = 0 → e y = 0 → x*y = 0) →
    (∀ V : ModuleCat.{0} D, HasProjectiveDimensionLE V g) →
    Nonempty (F ⊣ ModuleCat.restrictScalars e) →
    ∀ N : ModuleCat.{0} A, Module.Finite A N →
      (∃ b : ℕ, ∀ n > b, IsZero ((F.leftDerived n).obj N)) → projectiveDimension N < ⊤

def H3 : Prop := ∀ (A D : Type) [Ring A] [Ring D]
    (F : ModuleCat.{0} A ⥤ ModuleCat.{0} D) [F.Additive] (N : ModuleCat.{0} A) (n : ℕ),
    ¬ IsZero ((F.leftDerived n).obj N) → (n : WithBot ℕ∞) ≤ projectiveDimension N

theorem main : H1 → H2 → H3 → type_of% @OMA.S_mo_438166.main := by
  rintro ⟨A, rA, aA, D, rD, e, g, F, addF, fin, surj, sq, gd, adj, family⟩ upper lower
  letI := rA
  letI := aA
  letI := rD
  letI := addF
  refine ⟨ℂ, inferInstance, A, rA, aA, inferInstance, ?_, fin, ?_⟩
  · rw [ringKrullDim_eq_zero_of_field]; decide
  · apply ENat.WithBot.eq_top_iff_forall_ge.mpr
    intro m
    obtain ⟨N, hN, hb, n, hmn, hn⟩ := family m
    have hp := upper A D e g F fin surj sq gd adj N hN hb
    have hl := lower A D F N n hn
    have hmn' : (m : WithBot ℕ∞) ≤ n := by exact_mod_cast hmn
    exact (hmn'.trans hl).trans (le_iSup_of_le N (le_iSup_of_le hN (le_iSup_of_le hp le_rfl)))
end
end OMA.R_mo_438166_R1
