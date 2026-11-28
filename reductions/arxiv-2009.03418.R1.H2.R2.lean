import OMAReductions.R_arxiv_2009_03418_R1
import Mathlib

/-! Adapted from OpenAI openai/math@3344da59991ed94f9ba711217b29c1d760badfa6,
CompleteCrossing/{Drawing,Deletion,Hill,Main}. Apache-2.0. -/
namespace OMA.R_arxiv_2009_03418_R1_H2_R2
open OMA.S_arxiv_2009_03418 Set
open scoped BigOperators Classical
noncomputable section
theorem hill_numerator_dvd (n : ℕ) :
    4 ∣ n / 2 * ((n - 1) / 2) * ((n - 2) / 2) * ((n - 3) / 2) := by
  have h₂ : (n - 2) / 2 = n / 2 - 1 := by omega
  have h₃ : (n - 3) / 2 = (n - 1) / 2 - 1 := by omega
  rw [h₂, h₃]
  convert Nat.mul_dvd_mul (Nat.two_dvd_mul_sub_one (n / 2))
    (Nat.two_dvd_mul_sub_one ((n - 1) / 2)) using 1
  ring

theorem hill_odd (s : ℕ) : hill (2 * s + 1) = (s.choose 2) ^ 2 := by
  have h₀ : (2 * s + 1) / 2 = s := by omega
  have h₁ : (2 * s + 1 - 1) / 2 = s := by omega
  have h₂ : (2 * s + 1 - 2) / 2 = s - 1 := by omega
  have h₃ : (2 * s + 1 - 3) / 2 = s - 1 := by omega
  have hdiv := Nat.two_dvd_mul_sub_one s
  obtain ⟨a, ha⟩ := hdiv
  rw [hill, h₀, h₁, h₂, h₃, Nat.choose_two_right]
  have hp : s * s * (s - 1) * (s - 1) = 4 * a ^ 2 := by nlinarith [ha]
  rw [hp, ha]
  simp

lemma four_mul_hill (n : ℕ) :
    4 * hill n = n / 2 * ((n - 1) / 2) * ((n - 2) / 2) * ((n - 3) / 2) := by
  exact Nat.mul_div_cancel' (hill_numerator_dvd n)

lemma four_mul_hill_even (s : ℕ) :
    4 * hill (2 * s) = s * (s - 1) ^ 2 * (s - 2) := by
  rw [four_mul_hill]
  have h0 : 2 * s / 2 = s := by omega
  have h1 : (2 * s - 1) / 2 = s - 1 := by omega
  have h2 : (2 * s - 2) / 2 = s - 1 := by omega
  have h3 : (2 * s - 3) / 2 = s - 2 := by omega
  rw [h0, h1, h2, h3]
  ring

lemma four_mul_hill_preceding (s : ℕ) :
    4 * hill (2 * s - 1) = (s - 1) ^ 2 * (s - 2) ^ 2 := by
  rw [four_mul_hill]
  have h0 : (2 * s - 1) / 2 = s - 1 := by omega
  have h1 : (2 * s - 1 - 1) / 2 = s - 1 := by omega
  have h2 : (2 * s - 1 - 2) / 2 = s - 2 := by omega
  have h3 : (2 * s - 1 - 3) / 2 = s - 2 := by omega
  rw [h0, h1, h2, h3]
  ring

lemma hill_deletion_relation (s : ℕ) :
    (2 * s - 4) * hill (2 * s) = 2 * s * hill (2 * s - 1) := by
  have hs : 2 * s - 4 = 2 * (s - 2) := by omega
  apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < 4)
  calc
    4 * ((2 * s - 4) * hill (2 * s)) =
        (2 * s - 4) * (4 * hill (2 * s)) := by ring
    _ = (2 * s - 4) * (s * (s - 1) ^ 2 * (s - 2)) := by rw [four_mul_hill_even]
    _ = 2 * s * ((s - 1) ^ 2 * (s - 2) ^ 2) := by rw [hs]; ring
    _ = 4 * (2 * s * hill (2 * s - 1)) := by rw [← four_mul_hill_preceding]; ring

lemma even_lower_bound_of_deletion (s c : ℕ) (hs : 3 ≤ s)
    (h : 2 * s * hill (2 * s - 1) ≤ (2 * s - 4) * c) : hill (2 * s) ≤ c := by
  rw [← hill_deletion_relation] at h
  have hp : 0 < 2 * s - 4 := by omega
  nlinarith

def H1 : Prop := ∀ s : ℕ, 2 ≤ s → ∀ D : AdmissibleDrawing (completeGraph (2*s+1)), (s.choose 2)^2 ≤ crossingCount D

def H2 : Prop := ∀ n : ℕ, 4 ≤ n → ∀ D : AdmissibleDrawing (completeGraph (n+1)),
  ∃ A : Fin (n+1) → AdmissibleDrawing (completeGraph n), (∑ v, crossingCount (A v)) ≤ (n+1-4) * crossingCount D

theorem main : H1 → H2 → OMA.R_arxiv_2009_03418_R1.H2 := by
  intro odd del n hn D
  by_cases hsmall : n < 5
  · interval_cases n <;> norm_num [hill]
  by_cases hparity : n % 2 = 1
  · obtain ⟨s, rfl⟩ : ∃ s, n = 2 * s + 1 := ⟨n / 2, by omega⟩
    rw [hill_odd]; exact odd s (by omega) D
  obtain ⟨s, rfl⟩ : ∃ s, n = 2 * s + 2 := ⟨n / 2 - 1, by omega⟩
  obtain ⟨A, hA⟩ := del (2*s+1) (by omega) D
  have hl : ∀ v, hill (2*s+1) ≤ crossingCount (A v) := by
    intro v; rw [hill_odd]; exact odd s (by omega) (A v)
  have hh := (Finset.sum_le_sum (s := Finset.univ) (fun v _ => hl v)).trans hA
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hh
  have he : 2 * (s + 1) = 2 * s + 2 := by omega
  have ho : 2 * s + 2 - 1 = 2 * s + 1 := by omega
  conv_lhs => rw [← he]
  apply even_lower_bound_of_deletion (s + 1) _ (by omega)
  simpa only [he, ho, Nat.add_assoc] using hh
end
end OMA.R_arxiv_2009_03418_R1_H2_R2
