import OMAReductions.R_OeisA55487_conjecture_R1

/-!
# Short shifted-prime splits up to 240

Extend the checked range past the original cutoff of 100 using pairs whose
inverse-totient loss satisfies the cubic inequality in the parent reduction.
The shorter finite target has explicit Lucas certificates.
-/

namespace OMA.R_OeisA55487_conjecture_R1_H1_R1

open OeisA55487

/-- The next finite block admits shifted-prime splits within the cubic range. -/
def H1 : Prop :=
  ∀ n : ℕ, 100 < n → n ≤ 240 →
    ∃ x y : ℕ, n.factorial = x*y ∧ (x+1).Prime ∧ (y+1).Prime ∧
      (x+y+1)^3 ≤ n.factorial^2

/-- Existence of a split for the indices beyond the new checked range. -/
def H2 : Prop :=
  ∀ n : ℕ, 240 < n → ¬ isFactorialPrime n →
    ∃ x y : ℕ, n.factorial = x*y ∧ (x+1).Prime ∧ (y+1).Prime

theorem main : H1 → H2 → OMA.R_OeisA55487_conjecture_R1.H1 := by
  intro hfinite hlarge n hn hnonprime
  by_cases hcut : n ≤ 240
  · obtain ⟨x,y,hprod,hx,hy,_⟩ := hfinite n hn hcut
    exact ⟨x,y,hprod,hx,hy⟩
  · exact hlarge n (by omega) hnonprime

end OMA.R_OeisA55487_conjecture_R1_H1_R1
