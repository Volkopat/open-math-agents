import OMAReductions.R_OeisA7918_conjecture1_R1

-- Step OeisA7918.conjecture1.R1.H1: hypothesis H1 of reduction OeisA7918.conjecture1.R1
-- Credit: @Raimo33

theorem OMA.solution : OMA.R_OeisA7918_conjecture1_R1.H1 := by
  intro n p0 d hn ⟨hd, hp⟩
  have h0 : p0.Prime := by simpa using hp 0 hn
  have hle : n ≤ p0 := by
    by_contra hlt
    rw [not_le] at hlt
    have h := hp p0 hlt
    have heq : p0 + p0 * d = p0 * (1 + d) := by ring
    rw [heq] at h
    have := Nat.prime_mul_iff.mp h
    rcases this with ⟨_, h1⟩ | ⟨_, h1⟩
    · omega
    · have h3 := h0.two_le
      omega
  exact Nat.sInf_le ⟨h0, hle⟩
