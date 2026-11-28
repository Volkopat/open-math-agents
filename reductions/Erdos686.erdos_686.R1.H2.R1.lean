import OMAReductions.R_Erdos686_erdos_686_R1
import Mathlib

-- Credit: @JaviSoto
/-! Classify length-two square ratios by the positive solutions of a Pell-type
equation. The recurrence is the Vieta involution followed by a coordinate
swap. Its two parameters are strictly less than the candidate square root,
so it gives a finite test. Only square roots failing the test need a longer
representation. The separate root 3 has the known length-three witness.
See also the length-two families in the discussion of Erdős problem 686. -/

open Finset
namespace OMA.R_Erdos686_erdos_686_R1_H2_R1

/-- Exact finite classification for a product of two consecutive integers. -/
def H1 : Prop := ∀ a : ℕ, 2 ≤ a →
  ((∃ n m : ℕ, n + 2 ≤ m ∧ a ^ 2 * (n + 1) * (n + 2) = (m + 1) * (m + 2)) ↔
  ∃ n < a, ∃ j < a,
    ((fun z : ℤ × ℤ => (2 * (2 * (n : ℤ) + 3) * z.1 - z.2, z.1))^[j] (1, 0)).1 = a)

/-- The residual case: a square root other than three outside every
length-two Pell family needs a representation of length at least three. -/
def H2 : Prop := ∀ a : ℕ, 2 ≤ a → a ≠ 3 → (∀ s : ℕ, a ≠ 4*s+6) →
  (∀ n < a, ∀ j < a,
    ((fun z : ℤ × ℤ => (2 * (2 * (n : ℤ) + 3) * z.1 - z.2, z.1))^[j] (1, 0)).1 ≠ a) →
  ∃ k ≥ 3, ∃ n m : ℕ, n + k ≤ m ∧
    ((a ^ 2 : ℕ) : ℚ) = ((∏ i ∈ Icc 1 k, (m + i) : ℕ) : ℚ) /
      ((∏ i ∈ Icc 1 k, (n + i) : ℕ) : ℚ)

theorem main : H1 → H2 → OMA.R_Erdos686_erdos_686_R1.H2 := by
  intro exactTwo longer N hN ⟨a,ha⟩
  have hN' : N = a^2 := by simpa [pow_two] using ha
  clear ha
  subst N
  have h2 : 2 ≤ a := by by_contra! h; interval_cases a <;> contradiction
  by_cases three : a=3
  · subst a
    exact Erdos686.erdos_686.variants.nine
  by_cases passes : ∃ n < a, ∃ j < a,
      ((fun z : ℤ × ℤ => (2 * (2 * (n : ℤ) + 3) * z.1 - z.2, z.1))^[j] (1, 0)).1 = a
  · obtain ⟨n,m,sep,eq⟩ := (exactTwo a h2).mpr passes
    refine ⟨2, by decide,n,m,sep,?_⟩
    simp only [prod_Icc_succ_top (by decide : 1≤2), Icc_self,prod_singleton]
    apply (eq_div_iff (by positivity)).mpr
    exact_mod_cast (by simpa [Nat.mul_assoc] using eq : a^2*((n+1)*(n+2))=(m+1)*(m+2))
  · push Not at passes
    have first (s : ℕ) : a ≠ 4*s+6 := by
      rintro rfl
      apply passes s (by omega) 1 (by omega)
      change 2*(2*(s:ℤ)+3)*1-0 = ((4*s+6:ℕ):ℤ)
      push_cast
      ring
    obtain ⟨k,hk,n,m,sep,h⟩ := longer a h2 three first passes
    exact ⟨k,by omega,n,m,sep,h⟩

end OMA.R_Erdos686_erdos_686_R1_H2_R1
