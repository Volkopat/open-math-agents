import OMAStatements.S_oeis_a266230
import Mathlib

/-! Two polynomial families give every m ≤ 5 congruent to 5 mod 42 and
every m ≥ 81 congruent to 27 mod 54. Weighted homogeneity reduces the
remaining nonzero targets to integers free of nontrivial sixth powers. -/
namespace OMA.R_oeis_a266230_R1

def H1 : Prop := ∀ m : ℤ, (m = 0 ∨ (m ≤ 5 ∧ m % 42 = 5) ∨
  (81 ≤ m ∧ m % 54 = 27)) → ∃ x y z : ℤ, 0<x ∧ 0<y ∧ 0<z ∧ m+x^2=y^3+z^3

def H2 : Prop := ∀ m : ℤ, m ≠ 0 →
  (∀ d : ℕ, 2 ≤ d → ¬ (d:ℤ)^6 ∣ m) →
  ¬ (m ≤ 5 ∧ m % 42 = 5) → ¬ (81 ≤ m ∧ m % 54 = 27) →
  ∃ x y z : ℤ, 0<x ∧ 0<y ∧ 0<z ∧ m+x^2=y^3+z^3

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a266230.main := by
  intro explicit primitive m
  induction h : m.natAbs using Nat.strong_induction_on generalizing m with
  | h N ih =>
    by_cases hcase : m = 0 ∨ (m ≤ 5 ∧ m%42=5) ∨ (81 ≤ m ∧ m%54=27)
    · exact explicit m hcase
    push_neg at hcase
    by_cases hf : ∀ d : ℕ, 2 ≤ d → ¬ (d:ℤ)^6 ∣ m
    · exact primitive m hcase.1 hf (fun h => hcase.2.1 h.1 h.2)
        (fun h => hcase.2.2 h.1 h.2)
    push_neg at hf
    obtain ⟨d,hd,t,ht⟩ := hf
    have ht0 : t ≠ 0 := fun hz => hcase.1 (by simp [ht,hz])
    have hd' : 1 < d^6 := one_lt_pow₀ (by omega) (by decide)
    have habs : m.natAbs = d^6*t.natAbs := by simp [ht,Int.natAbs_mul,Int.natAbs_pow]
    have hlt : t.natAbs < N := by
      rw [← h,habs]
      exact lt_mul_of_one_lt_left (Int.natAbs_pos.mpr ht0) hd'
    obtain ⟨x,y,z,hx,hy,hz,he⟩ := ih _ hlt t rfl
    have hdpos : (0:ℤ) < d := by exact_mod_cast (show 0<d by omega)
    refine ⟨(d:ℤ)^3*x,(d:ℤ)^2*y,(d:ℤ)^2*z,by positivity,by positivity,by positivity,?_⟩
    rw [ht]
    linear_combination (d:ℤ)^6*he

end OMA.R_oeis_a266230_R1
