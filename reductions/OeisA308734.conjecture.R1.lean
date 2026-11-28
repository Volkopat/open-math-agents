import FormalConjectures.OEIS.«308734»

/-!
Sun's four-square refinement: n > 1 is (2^a 3^b)^2 + (2^c 5^d)^2 + x^2 + y^2.
Classical slice: whenever some residual n - (2^a 3^b)^2 - (2^c 5^d)^2 has
every prime factor congruent to 3 mod 4 to an even power, the Fermat-Euler
two-square theorem writes it as x^2 + y^2 (H1). The main theorem also
descends from 4m to m by doubling every term (a and c go up by one), so the
open remainder H2 only concerns n not divisible by 4 whose residuals all
fail the two-square criterion.
-/

namespace OMA.R_OeisA308734_conjecture_R1

def H1 : Prop := ∀ n a b c d : ℕ, (2 ^ a * 3 ^ b) ^ 2 + (2 ^ c * 5 ^ d) ^ 2 ≤ n →
    (∀ q ∈ (n - (2 ^ a * 3 ^ b) ^ 2 - (2 ^ c * 5 ^ d) ^ 2).primeFactors, q % 4 = 3 →
      Even (padicValNat q (n - (2 ^ a * 3 ^ b) ^ 2 - (2 ^ c * 5 ^ d) ^ 2))) →
    OeisA308734.A n

def H2 : Prop := ∀ n : ℕ, 1 < n → ¬ 4 ∣ n →
    (∀ a b c d : ℕ, (2 ^ a * 3 ^ b) ^ 2 + (2 ^ c * 5 ^ d) ^ 2 ≤ n →
      ∃ q ∈ (n - (2 ^ a * 3 ^ b) ^ 2 - (2 ^ c * 5 ^ d) ^ 2).primeFactors, q % 4 = 3 ∧
        ¬ Even (padicValNat q (n - (2 ^ a * 3 ^ b) ^ 2 - (2 ^ c * 5 ^ d) ^ 2))) →
    OeisA308734.A n

private theorem dilate (m : ℕ) (h : OeisA308734.A m) : OeisA308734.A (4 * m) := by
  obtain ⟨a, b, c, d, x, y, rfl⟩ := h
  exact ⟨a + 1, b, c + 1, d, 2 * x, 2 * y, by ring⟩

theorem main : H1 → H2 → type_of% @OeisA308734.conjecture := by
  intro h₁ h₂ n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    by_cases h4 : 4 ∣ n
    · obtain ⟨m, rfl⟩ := h4
      by_cases hm : m = 1
      · subst hm
        exact ⟨0, 0, 0, 0, 1, 1, by norm_num⟩
      · exact dilate m (ih m (by omega) (by omega))
    by_cases h : ∃ a b c d : ℕ, (2 ^ a * 3 ^ b) ^ 2 + (2 ^ c * 5 ^ d) ^ 2 ≤ n ∧
        ∀ q ∈ (n - (2 ^ a * 3 ^ b) ^ 2 - (2 ^ c * 5 ^ d) ^ 2).primeFactors, q % 4 = 3 →
          Even (padicValNat q (n - (2 ^ a * 3 ^ b) ^ 2 - (2 ^ c * 5 ^ d) ^ 2))
    · obtain ⟨a, b, c, d, hle, hc⟩ := h
      exact h₁ n a b c d hle hc
    · apply h₂ n hn h4
      intro a b c d hle
      by_contra hne
      apply h
      refine ⟨a, b, c, d, hle, fun q hq h3 => ?_⟩
      by_contra hodd
      exact hne ⟨q, hq, h3, hodd⟩

end OMA.R_OeisA308734_conjecture_R1
