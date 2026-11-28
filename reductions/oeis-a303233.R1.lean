import OMAStatements.S_oeis_a303233
import Mathlib

/-! Two triangular summands can be eliminated exactly. For fixed powers of
two, the remaining quantity m is a sum of two triangular numbers precisely
when every prime congruent to 3 modulo 4 has even valuation in 4m+1.
The open part is finding a pair of powers that passes this arithmetic test. -/

namespace OMA.R_oeis_a303233_R1

def H1 : Prop := ∀ n c d : ℕ, 2 ^ c + 2 ^ d ≤ n →
    let m := n - (2 ^ c + 2 ^ d)
    (∃ a b : ℕ, a * (a + 1) / 2 + b * (b + 1) / 2 + 2 ^ c + 2 ^ d = n) ↔
    ∀ q ∈ (4 * m + 1).primeFactors, q % 4 = 3 → Even (padicValNat q (4 * m + 1))

def H2 : Prop := ∀ n : ℕ, 1 < n → ∃ c d : ℕ, 2 ^ c + 2 ^ d ≤ n ∧
    let m := n - (2 ^ c + 2 ^ d)
    ∀ q ∈ (4 * m + 1).primeFactors, q % 4 = 3 → Even (padicValNat q (4 * m + 1))

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a303233.main := by
  intro h1 h2 n hn
  obtain ⟨c, d, hle, hf⟩ := h2 n hn
  obtain ⟨a, b, hab⟩ := (h1 n c d hle).mpr hf
  exact ⟨a, b, c, d, hab⟩

end OMA.R_oeis_a303233_R1
