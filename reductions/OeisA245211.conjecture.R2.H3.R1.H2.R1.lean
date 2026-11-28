import OMAReductions.R_OeisA245211_conjecture_R2_H3_R1

/-!
# Separate the 69-factor case from the remaining large counts

The non-prime-power hypothesis excludes counts 67, 71, and 73.
After excluding count 69, oddness raises the remaining bound to 75.
-/

namespace OMA.R_OeisA245211_conjecture_R2_H3_R1_H2_R1

/-- The squarefree 69-factor case has no fixed point. -/
def H1 : Prop :=
  ∀ n : ℕ, Squarefree n → n.primeFactors.card = 69 →
    OeisA245211.a n ≠ n

/-- The remaining odd counts are at least 75 and are not prime powers. -/
def H2 : Prop :=
  ∀ n : ℕ, Squarefree n → 75 ≤ n.primeFactors.card →
    Odd n.primeFactors.card →
    (∀ q k : ℕ, q.Prime → 0 < k → n.primeFactors.card ≠ q ^ k) →
    OeisA245211.a n ≠ n

theorem main : H1 → H2 → OMA.R_OeisA245211_conjecture_R2_H3_R1.H2 := by
  intro h1 h2 n hs h67 hodd hnp
  by_cases h69 : n.primeFactors.card = 69
  · exact h1 n hs h69
  · apply h2 n hs ?_ hodd hnp
    have hne67 : n.primeFactors.card ≠ 67 := by
      simpa only [pow_one] using hnp 67 1 (by norm_num) (by decide)
    have hne71 : n.primeFactors.card ≠ 71 := by
      simpa only [pow_one] using hnp 71 1 (by norm_num) (by decide)
    have hne73 : n.primeFactors.card ≠ 73 := by
      simpa only [pow_one] using hnp 73 1 (by norm_num) (by decide)
    obtain ⟨k, hk⟩ := hodd
    omega

end OMA.R_OeisA245211_conjecture_R2_H3_R1_H2_R1
