import OMAReductions.R_Erdos242_erdos_242_R1_H1_R1_H1_R1

-- Step Erdos242.erdos_242.R1.H1.R1.H1.R1.H2: hypothesis H2 of reduction Erdos242.erdos_242.R1.H1.R1.H1.R1
-- Credit: @luciusacarr
-- Three explicit Erdős–Straus identities:
--   p ≡ 29 (mod 44): 4/p = 1/(4d) + 1/(44d) + 1/(11dp),  d = (3p+1)/44
--   p ≡ 41 (mod 44): 4/p = 1/(11d) + 1/(4dp) + 1/(44dp), d = (p+3)/44
--   p ≡ 65 (mod 88): 4/p = 1/(22d) + 1/(dp) + 1/(22dp),  d = (p+23)/88

theorem OMA.solution : OMA.R_Erdos242_erdos_242_R1_H1_R1_H1_R1.H2 := by
  intro p _ h24 _ h11
  rcases h11 with h | h | h
  · -- p ≡ 29 mod 44
    obtain ⟨k, rfl⟩ : ∃ k, p = 44 * k + 29 := ⟨p / 44, by omega⟩
    refine ⟨4 * (3 * k + 2), 44 * (3 * k + 2), 11 * (3 * k + 2) * (44 * k + 29),
      by omega, by omega, by nlinarith, ?_⟩
    push_cast
    field_simp
    ring
  · -- p ≡ 41 mod 44
    obtain ⟨k, rfl⟩ : ∃ k, p = 44 * k + 41 := ⟨p / 44, by omega⟩
    refine ⟨11 * (k + 1), 4 * (k + 1) * (44 * k + 41), 44 * (k + 1) * (44 * k + 41),
      by omega, by nlinarith, by nlinarith, ?_⟩
    push_cast
    field_simp
    ring
  · -- p ≡ 65 mod 88
    obtain ⟨k, rfl⟩ : ∃ k, p = 88 * k + 65 := ⟨p / 88, by omega⟩
    refine ⟨22 * (k + 1), (k + 1) * (88 * k + 65), 22 * (k + 1) * (88 * k + 65),
      by omega, by nlinarith, by nlinarith, ?_⟩
    push_cast
    field_simp
    ring
