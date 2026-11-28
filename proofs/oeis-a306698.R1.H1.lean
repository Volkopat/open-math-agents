import OMAReductions.R_oeis_a306698_R1
import Mathlib

/-! Both branches of the recursion change the term by `n + 1` modulo `3`, since
`-2 (n + 1) ≡ n + 1 (mod 3)`. So `a n ≡ n (n + 1) / 2 (mod 3)`, which is `0` or `1`. -/

namespace OMA.Step_oeis_a306698_R1_H1

open OMA.S_oeis_a306698

theorem invariant (n : ℕ) :
    (n % 3 = 0 ∧ sequence n % 3 = 0) ∨ (n % 3 = 1 ∧ sequence n % 3 = 1) ∨
      (n % 3 = 2 ∧ sequence n % 3 = 0) := by
  induction n with
  | zero => left; exact ⟨rfl, rfl⟩
  | succ n ih =>
    have hs : sequence (n + 1) = if 2 * (n + 1) < sequence n ∧ sequence n - 2 * (n + 1) ∉ (state n).2
        then sequence n - 2 * (n + 1) else sequence n + (n + 1) := rfl
    rw [hs]
    split_ifs with h
    · have := h.1
      omega
    · omega

end OMA.Step_oeis_a306698_R1_H1

theorem OMA.solution : OMA.R_oeis_a306698_R1.H1 := by
  rintro _ ⟨n, rfl⟩
  have := OMA.Step_oeis_a306698_R1_H1.invariant n
  show _ ∨ _
  omega
