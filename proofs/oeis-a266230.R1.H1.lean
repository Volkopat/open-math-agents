import OMAReductions.R_oeis_a266230_R1

/-! Three explicit families. For `m = 0`: `0 + 3^2 = 1^3 + 2^3`. For `m ≤ 5`, `m ≡ 5 (mod 42)`,
write `m = 47 - 42 t` with `t ≥ 1`; then
`(47 - 42 t) + (t^3 + 6 t + 4)^2 = (2 t - 1)^3 + (t^2 + 4)^3`.
For `m ≥ 81`, `m ≡ 27 (mod 54)`, write `m = 54 s + 27` with `s ≥ 1`; then
`(54 s + 27) + (s^3 + 6 s^2 + 6 s)^2 = (2 s + 3)^3 + (s^2 + 4 s)^3`. -/

namespace OMA.A266230H1

theorem H1_proof : OMA.R_oeis_a266230_R1.H1 := by
  intro m hm
  rcases hm with rfl | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨3, 1, 2, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · obtain ⟨t, htd⟩ : ∃ t : ℤ, t = (47 - m) / 42 := ⟨_, rfl⟩
    have ht : m = 47 - 42 * t := by omega
    have ht1 : 1 ≤ t := by omega
    have hpos : (0 : ℤ) < t := by linarith
    have hcube : (0 : ℤ) < t ^ 3 := pow_pos hpos 3
    refine ⟨t ^ 3 + 6 * t + 4, 2 * t - 1, t ^ 2 + 4, by linarith, by linarith, by positivity, ?_⟩
    rw [ht]
    ring
  · obtain ⟨s, hsd⟩ : ∃ s : ℤ, s = (m - 27) / 54 := ⟨_, rfl⟩
    have hs : m = 54 * s + 27 := by omega
    have hs1 : 1 ≤ s := by omega
    have hpos : (0 : ℤ) < s := by linarith
    have hcube : (0 : ℤ) < s ^ 3 := pow_pos hpos 3
    have hsq : (0 : ℤ) < s ^ 2 := pow_pos hpos 2
    refine ⟨s ^ 3 + 6 * s ^ 2 + 6 * s, 2 * s + 3, s ^ 2 + 4 * s, by linarith, by linarith,
      by linarith, ?_⟩
    rw [hs]
    ring

end OMA.A266230H1

theorem OMA.solution : OMA.R_oeis_a266230_R1.H1 := OMA.A266230H1.H1_proof
