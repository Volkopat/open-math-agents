import OMAStatements.S_mse_2161989
import Mathlib

/-! A Pell solution at p with denominator divisible by t descends to p*t².
The fundamental denominator descends exactly when t divides it. The squared
fundamental unit gives a second slice: if its denominator 2ab is divisible
by t and t exceeds 2a, the descended denominator is smaller than b.
In either case the squarefree kernel p itself beats the proposed record. -/

namespace OMA.R_mse_2161989_R1
open OMA.S_mse_2161989

def H1 : Prop := ∀ p t : ℕ, p.Prime → 1 < t →
    (t ∣ f p ∨ ∃ a : ℕ, p * (f p) ^ 2 + 1 = a * a ∧ 2 * a < t ∧ t ∣ 2 * a * f p) →
    f (p * t ^ 2) < f p

def H2 : Prop := ∀ s : ℕ, 46 < s → ¬ s.Prime → ¬ IsSquare s →
    (∀ p t : ℕ, p.Prime → 1 < t → s = p * t ^ 2 →
      ¬ (t ∣ f p ∨ ∃ a : ℕ, p * (f p) ^ 2 + 1 = a * a ∧ 2 * a < t ∧ t ∣ 2 * a * f p)) →
    ∃ p : ℕ, p.Prime ∧ p < s ∧ f s < f p

theorem main : H1 → H2 → type_of% @OMA.S_mse_2161989.main := by
  intro h1 h2 s hs hnp hns
  by_cases h : ∃ p t : ℕ, p.Prime ∧ 1 < t ∧ s = p * t ^ 2 ∧
      (t ∣ f p ∨ ∃ a : ℕ, p * (f p) ^ 2 + 1 = a * a ∧ 2 * a < t ∧ t ∣ 2 * a * f p)
  · obtain ⟨p, t, hp, ht, rfl, hm⟩ := h
    have hgt : 1 < t ^ 2 := by nlinarith
    exact ⟨p, hp, by simpa using Nat.mul_lt_mul_of_pos_left hgt hp.pos, h1 p t hp ht hm⟩
  · apply h2 s hs hnp hns
    exact fun p t hp ht he hm => h ⟨p, t, hp, ht, he, hm⟩

end OMA.R_mse_2161989_R1
