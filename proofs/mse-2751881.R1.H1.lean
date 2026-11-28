import OMAReductions.R_mse_2751881_R1

/-! The condition on m says m = u² + v² (`Nat.eq_sq_add_sq_iff`). Then
4h³ + 54h(u² + v²) = (h + 3u)³ + (h - 3u)³ + (h + 3v)³ + (h - 3v)³. -/

theorem OMA.solution : OMA.R_mse_2751881_R1.H1 := by
  rintro n ⟨h, m, hn, hm⟩
  obtain ⟨u, v, huv⟩ := Nat.eq_sq_add_sq_iff.2 hm
  refine ⟨h + 3 * u, h - 3 * u, h + 3 * v, h - 3 * v, ?_⟩
  rw [hn, huv]
  push_cast
  ring
