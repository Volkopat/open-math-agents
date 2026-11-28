import OMAStatements.S_oeis_a162311

/-! We use @agchua's Thue–Morse pairing argument from PR #30660. Switching
between the two sequences on alternate indices makes the state change
exactly at equality hits, where it agrees with the unshifted sequence. -/

namespace W3A162311

open OMA.S_oeis_a162311

private abbrev t := A010060

private theorem t_lt (j : ℕ) : t j < 2 := Nat.mod_lt _ (by decide)

private theorem pair (j : ℕ) (hj : j % 2 = 0) : t (j + 1) + t j = 1 := by
  rcases Nat.eq_zero_or_pos j with rfl | hp
  · decide
  · unfold t A010060
    rw [Nat.digits_def' (by decide : 1 < 2) (Nat.succ_pos j),
      Nat.digits_def' (by decide : 1 < 2) hp, List.sum_cons, List.sum_cons,
      show (j + 1) % 2 = 1 by omega, show (j + 1) / 2 = j / 2 by omega, hj]
    omega

private def W (k j : ℕ) : ℕ := if j % 2 = 0 then t (j + k) else t j

private theorem step (k j : ℕ) (hk : k % 2 = 1) :
    W k (j + 1) = W k j ↔ t j ≠ t (j + k) := by
  have h₀ := t_lt j
  have h₁ := t_lt (j + k)
  by_cases hj : j % 2 = 0
  · have h := pair j hj
    simp only [W, if_pos hj, if_neg (show ¬ (j + 1) % 2 = 0 by omega)]
    omega
  · have h := pair (j + k) (by omega)
    simp only [W, if_neg hj, if_pos (show (j + 1) % 2 = 0 by omega)]
    rw [show j + 1 + k = j + k + 1 by omega]
    omega

theorem solve : type_of% @OMA.S_oeis_a162311.main := by
  intro k hk n m hnm hn hm hgap
  have hit (j : ℕ) (h : t j = t (j + k)) : W k j = t j := by simp [W, ← h]
  have same (d : ℕ) : n + 1 + d ≤ m → W k (n + 1 + d) = W k (n + 1) := by
    induction d with
    | zero => intro _; rfl
    | succ d ih =>
      intro hd
      exact ((step k (n + 1 + d) hk).2 (hgap _ (by omega) (by omega))).trans (ih (by omega))
  have h := same (m - n - 1) (by omega)
  rw [show n + 1 + (m - n - 1) = m by omega, hit m hm] at h
  have hne : W k (n + 1) ≠ W k n := fun he => (step k n hk).1 he hn
  rwa [← h, hit n hn] at hne

end W3A162311

theorem OMA.solution : type_of% @OMA.S_oeis_a162311.main := W3A162311.solve
