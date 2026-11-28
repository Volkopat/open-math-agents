import OMAStatements.S_mse_1838931
import Mathlib

namespace OMA.R_mse_1838931_R1

/-- Wilson reflection for prime divisors of Euclid numbers q! + 1, with q an odd prime. -/
def H1 : Prop :=
    (∀ N : ℕ, ∃ p q : ℕ, N < q ∧ q < p ∧ p.Prime ∧ q.Prime ∧ p ∣ q.factorial + 1) ∧
    ∀ p q : ℕ, p.Prime → q.Prime → 2 < q → p ∣ q.factorial + 1 →
    q < p ∧ 2 < p - q ∧ q ≡ (p - q).factorial [MOD p]

def H2 : Prop := ∀ p : ℕ, p.Prime → 5 < p →
    (∀ q : ℕ, q.Prime → 2 < q → ¬ p ∣ q.factorial + 1) →
    ∃ q m : ℕ, q.Prime ∧ q < p ∧ 2 < m ∧ m < p ∧ q ≡ m.factorial [MOD p]

theorem main : H1 → H2 → type_of% @OMA.S_mse_1838931.main := by
  intro h1 h2 p hp h5
  by_cases h : ∃ q : ℕ, q.Prime ∧ 2 < q ∧ p ∣ q.factorial + 1
  · obtain ⟨q,hq,hq2,hd⟩ := h
    obtain ⟨hlt,hm,he⟩  := h1.2 p q hp hq hq2 hd
    exact ⟨q, p-q, hq, hlt, hm, by omega, he⟩
  · exact h2 p hp h5 (fun q hq hq2 hd => h ⟨q,hq,hq2,hd⟩)

end OMA.R_mse_1838931_R1
