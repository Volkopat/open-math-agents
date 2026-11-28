import OMAReductions.R_Erdos687_erdos_687_parts_iii_R3

-- Reduction Erdos687.erdos_687.parts.iii.R3.H1.R1 of step Erdos687.erdos_687.parts.iii.R3.H1
-- Credit: @arindale

namespace OMA.R_Erdos687_erdos_687_parts_iii_R3_H1_R1

open Filter

/-- Ingham's prime-gap theorem with an explicit constant: for large `n` there is a prime
within `C * n^(5/8)` of `n`. Since `5/8 < 2/3`, this is stronger than the target. -/
def H1 : Prop :=
  ∃ C : ℕ, ∀ᶠ n : ℕ in atTop,
    ∃ p : ℕ, p.Prime ∧ n < p ∧ (p - n) ^ 8 ≤ C ^ 8 * n ^ 5

/-- Numeric absorption: for large `n`, any `d` with `d^8 ≤ C^8 n^5` satisfies `d^3 ≤ n^2`
(equivalently `n ≥ C^24`). -/
def H2 : Prop :=
  ∀ C : ℕ, ∀ᶠ n : ℕ in atTop, ∀ d : ℕ, d ^ 8 ≤ C ^ 8 * n ^ 5 → d ^ 3 ≤ n ^ 2

theorem main : H1 → H2 → OMA.R_Erdos687_erdos_687_parts_iii_R3.H1 := by
  rintro ⟨C, hC⟩ h2
  filter_upwards [hC, h2 C] with n hn hd
  obtain ⟨p, hp, hnp, hgap⟩ := hn
  exact ⟨p, hp, hnp, hd (p - n) hgap⟩

end OMA.R_Erdos687_erdos_687_parts_iii_R3_H1_R1
