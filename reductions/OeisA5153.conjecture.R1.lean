import FormalConjectures.OEIS.«5153»

/-!
Every odd n at least 3 is a prime plus a practical number (Switkay).
Classical slice: doubling preserves practicality (write m as 2a + b with
a represented by distinct divisors d of q, then use the divisors 2d and,
if b = 1, the divisor 1), so every power of two and every 3 * 2^j with
j at least 1 is practical. H1 covers every n for which n - 2^k or
n - 3 * 2^(k+1) is prime for some k. H2 is the remaining odd n, a subset
of the de Polignac (obstinate) numbers, where the conjecture stays open.
-/

namespace OMA.R_OeisA5153_conjecture_R1

def H1 : Prop := ∀ n k : ℕ, ((n - 2 ^ k).Prime ∨ (n - 3 * 2 ^ (k + 1)).Prime) →
    ∃ p q : ℕ, p.Prime ∧ OeisA5153.A q ∧ n = p + q

def H2 : Prop := ∀ n : ℕ, 3 ≤ n → Odd n →
    (∀ k : ℕ, ¬ (n - 2 ^ k).Prime ∧ ¬ (n - 3 * 2 ^ (k + 1)).Prime) →
    ∃ p q : ℕ, p.Prime ∧ OeisA5153.A q ∧ n = p + q

theorem main : H1 → H2 → type_of% @OeisA5153.conjecture := by
  intro h₁ h₂ n hn hodd
  by_cases h : ∃ k : ℕ, (n - 2 ^ k).Prime ∨ (n - 3 * 2 ^ (k + 1)).Prime
  · obtain ⟨k, hk⟩ := h
    exact h₁ n k hk
  · push_neg at h
    exact h₂ n hn hodd (fun k => ⟨h k |>.1, h k |>.2⟩)

end OMA.R_OeisA5153_conjecture_R1
