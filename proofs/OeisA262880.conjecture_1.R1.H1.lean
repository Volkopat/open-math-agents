import OMAReductions.R_OeisA262880_conjecture_1_R1

/-!
# Step H1 of the reduction OeisA262880.conjecture_1.R1

Write `d ^ 3 = 2 s + 1` and `W = 2 s w + s + w`, so `2 W + 1 = d ^ 3 (2 w + 1)`. Since
`8 T(m) + 1 = (2 m + 1) ^ 2`, the identity `8 n + 1 = d ^ 6 (8 r + 1)` becomes
`n = T(W) + (d² x)³ + b (d² y)³ + c (d² z)³`, and `W ≥ s ≥ 1` because `d ≥ 2`.
-/

theorem OMA.solution : OMA.R_OeisA262880_conjecture_1_R1.H1 := by
  intro b c n r d w x y z hd hodd he hr
  have hT : ∀ m : ℕ, 2 * Nat.triangular m = m * (m + 1) := by
    intro m
    unfold Nat.triangular
    exact Nat.mul_div_cancel' (Nat.even_mul_succ_self m).two_dvd
  obtain ⟨s, hs⟩ : Odd (d ^ 3) := hodd.pow
  have hs1 : 1 ≤ s := by
    have : 8 ≤ d ^ 3 := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ d ^ 3 := Nat.pow_le_pow_left hd 3
    omega
  refine ⟨2 * s * w + s + w, d ^ 2 * x, d ^ 2 * y, d ^ 2 * z, by positivity, ?_⟩
  have hTW := hT (2 * s * w + s + w)
  have hTw := hT w
  have h8 : 8 * n = 8 * (Nat.triangular (2 * s * w + s + w) + (d ^ 2 * x) ^ 3 +
      b * (d ^ 2 * y) ^ 3 + c * (d ^ 2 * z) ^ 3) := by
    zify at he hr hTW hTw hs ⊢
    linear_combination he + 8 * (d : ℤ) ^ 6 * hr - 4 * hTW + 4 * (d : ℤ) ^ 6 * hTw +
      ((d : ℤ) ^ 3 + 2 * s + 1) * (2 * w + 1) ^ 2 * hs
  omega
