import OMAReductions.R_OeisA262824_conjecture_1_R1

/-!
# Proof of `OeisA262824.conjecture_1.R1.H1`

By Fermat's two-square theorem (`Nat.eq_sq_add_sq_iff`), write `q = a^2 + b^2`. Let `t = min a b`
and `u = max a b`, so `2 * t^2 ≤ a^2 + b^2 = q ≤ 2 * s^4`, giving `t ≤ s^2`. Setting
`w = 6 * s * u`, `x = 2 * s^2 - 2 * t`, `y = 2 * s^2 + t`, `z = t` satisfies the identity
`w^2 + x^3 + 2 * y^3 + 6 * z^3 = 24 * s^6 + 36 * s^2 * (u^2 + t^2) = 24 * s^6 + 36 * s^2 * q`.
-/

theorem OMA.solution : OMA.R_OeisA262824_conjecture_1_R1.H1 := by
  intro s q hq hpf
  obtain ⟨a, b, hab⟩ := Nat.eq_sq_add_sq_iff.mpr hpf
  set t := min a b
  set u := max a b
  have htu : q = u ^ 2 + t ^ 2 := by
    rw [hab]
    rcases le_total a b with h | h
    · simp only [t, u, min_eq_left h, max_eq_right h]; ring
    · simp only [t, u, min_eq_right h, max_eq_left h]
  have hle : t ≤ u := min_le_max
  have ht2 : t ^ 2 ≤ s ^ 4 := by
    have : t ^ 2 ≤ u ^ 2 := Nat.pow_le_pow_left hle 2
    nlinarith
  have ht : t ≤ s ^ 2 := by
    have : t ^ 2 ≤ (s ^ 2) ^ 2 := by
      calc t ^ 2 ≤ s ^ 4 := ht2
        _ = (s ^ 2) ^ 2 := by ring
    nlinarith
  refine ⟨6 * s * u, 2 * s ^ 2 - 2 * t, 2 * s ^ 2 + t, t, ?_⟩
  have hsub : 2 * t ≤ 2 * s ^ 2 := by omega
  zify [hsub]
  have htuZ : (q : ℤ) = (u : ℤ) ^ 2 + (t : ℤ) ^ 2 := by exact_mod_cast htu
  rw [htuZ]
  ring
