import OMAStatements.S_oeis_a200218

namespace OMA.P200218

open OMA.S_oeis_a200218

lemma pw_succ (k : ℕ) : pw (k + 1)
    = (682 * (pw k).1 + 125 * 61 * (pw k).2, 61 * (pw k).1 + 682 * (pw k).2) := by
  rw [pw]

/-- The odd powers: the pair for the exponent 2j+1. -/
def P (j : ℕ) : ℤ × ℤ := pw (2 * j + 1)

/-- The sign (-1)^(j+1). -/
def sg (j : ℕ) : ℤ := (-1) ^ (j + 1)

lemma sg_sq (j : ℕ) : sg j ^ 2 = 1 := by
  unfold sg
  rw [← pow_mul]
  exact Even.neg_one_pow ⟨j + 1, by ring⟩

lemma P_zero : P 0 = (682, 61) := by
  unfold P
  have e : 2 * 0 + 1 = 0 + 1 := by norm_num
  rw [e, pw_succ, pw]
  norm_num

lemma P_succ (j : ℕ) : P (j + 1)
    = (930249 * (P j).1 + 125 * 83204 * (P j).2, 83204 * (P j).1 + 930249 * (P j).2) := by
  unfold P
  have e : 2 * (j + 1) + 1 = (2 * j + 1) + 1 + 1 := by ring
  rw [e, pw_succ, pw_succ]
  apply Prod.ext
  · dsimp only
    ring
  · dsimp only
    ring

lemma P_norm (j : ℕ) : (P j).1 ^ 2 - 125 * (P j).2 ^ 2 = -1 := by
  induction j with
  | zero => rw [P_zero]; norm_num
  | succ j ih =>
    rw [P_succ]
    dsimp only
    linear_combination ih

lemma P_pos (j : ℕ) : 682 ≤ (P j).1 ∧ 61 ≤ (P j).2 := by
  induction j with
  | zero => rw [P_zero]; norm_num
  | succ j ih =>
    obtain ⟨h1, h2⟩ := ih
    rw [P_succ]
    dsimp only
    constructor <;> linarith

lemma x_eq (j : ℕ) : x (j + 1)
    = (((P j).1 : ℚ) ^ 2 - 6 * (sg j : ℚ) * ((P j).1 : ℚ) + 4) / 5 := by
  have hg : (sg j : ℚ) ^ 2 = 1 := by exact_mod_cast sg_sq j
  have hs : (sg j : ℚ) = (-1) ^ (j + 1) := by
    unfold sg
    push_cast
    rfl
  unfold x t P
  have e : 2 * (j + 1) - 1 = 2 * j + 1 := by omega
  rw [e, ← hs]
  linear_combination ((((pw (2 * j + 1)).1 : ℚ)) ^ 2 / 5) * hg

lemma key_id (E F g : ℤ) (hg : g ^ 2 = 1) (hn : E ^ 2 - 125 * F ^ 2 = -1) :
    (E ^ 2 - 6 * g * E + 4) ^ 3
      = 125 * (F * (E ^ 2 - 9 * g * E + 19)) ^ 2 + 27 * (2 * g * E - 11) := by
  linear_combination (-27 * E ^ 2 * (-4 * E ^ 2 + 8 * E * g + 375 * F ^ 2 - 16)) * hg
    + (E ^ 4 - 18 * E ^ 3 * g + 119 * E ^ 2 - 342 * E * g + 361) * hn

/-- The rounded square root in closed form. -/
lemma y_eq (j : ℕ) : y (j + 1)
    = (P j).2 * ((P j).1 ^ 2 - 9 * sg j * (P j).1 + 19) := by
  obtain ⟨hE, hF⟩ := P_pos j
  have hg := sg_sq j
  have hk := key_id (P j).1 (P j).2 (sg j) hg (P_norm j)
  have hxe := x_eq j
  unfold y
  rw [round_eq, Int.floor_eq_iff]
  push_cast
  generalize (P j).1 = E at hE hk hxe ⊢
  generalize (P j).2 = F at hF hk ⊢
  generalize x (j + 1) = xx at hxe ⊢
  have hER : (682 : ℝ) ≤ (E : ℝ) := by exact_mod_cast hE
  have hFR : (61 : ℝ) ≤ (F : ℝ) := by exact_mod_cast hF
  have hkR : ((E : ℝ) ^ 2 - 6 * (sg j : ℝ) * (E : ℝ) + 4) ^ 3
      = 125 * ((F : ℝ) * ((E : ℝ) ^ 2 - 9 * (sg j : ℝ) * (E : ℝ) + 19)) ^ 2
        + 27 * (2 * (sg j : ℝ) * (E : ℝ) - 11) := by exact_mod_cast hk
  have hx : (xx : ℝ) ^ 3
      = ((F : ℝ) * ((E : ℝ) ^ 2 - 9 * (sg j : ℝ) * (E : ℝ) + 19)) ^ 2
        + 27 * (2 * (sg j : ℝ) * (E : ℝ) - 11) / 125 := by
    rw [hxe]
    push_cast
    linear_combination hkR / 125
  have hgc : sg j = 1 ∨ sg j = -1 := by
    have h0 : (sg j - 1) * (sg j + 1) = 0 := by linear_combination hg
    rcases mul_eq_zero.mp h0 with h | h
    · left; linarith
    · right; linarith
  have hgR : (sg j : ℝ) = 1 ∨ (sg j : ℝ) = -1 := by
    rcases hgc with h | h
    · left; rw [h]; norm_num
    · right; rw [h]; norm_num
  rw [hx]
  generalize (sg j : ℝ) = g at hgR ⊢
  have hQ : (E : ℝ) ≤ (E : ℝ) ^ 2 - 9 * g * (E : ℝ) + 19 := by
    rcases hgR with h | h <;> rw [h] <;> nlinarith
  have hY : (E : ℝ) ≤ (F : ℝ) * ((E : ℝ) ^ 2 - 9 * g * (E : ℝ) + 19) := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (F : ℝ) - 1)
      (by linarith : (0 : ℝ) ≤ (E : ℝ) ^ 2 - 9 * g * (E : ℝ) + 19)]
  have hD1 : -((E : ℝ) / 2) ≤ 27 * (2 * g * (E : ℝ) - 11) / 125 := by
    rcases hgR with h | h <;> rw [h] <;> linarith
  have hD2 : 27 * (2 * g * (E : ℝ) - 11) / 125 ≤ (E : ℝ) / 2 := by
    rcases hgR with h | h <;> rw [h] <;> linarith
  generalize (F : ℝ) * ((E : ℝ) ^ 2 - 9 * g * (E : ℝ) + 19) = Y at hY ⊢
  generalize 27 * (2 * g * (E : ℝ) - 11) / 125 = D at hD1 hD2 ⊢
  have h1 : (Y - 1 / 2) ^ 2 ≤ Y ^ 2 + D := by nlinarith
  have h2 : Y ^ 2 + D < (Y + 1 / 2) ^ 2 := by nlinarith
  have h3 : Real.sqrt ((Y - 1 / 2) ^ 2) = Y - 1 / 2 := Real.sqrt_sq (by linarith)
  have h4 : Real.sqrt ((Y + 1 / 2) ^ 2) = Y + 1 / 2 := Real.sqrt_sq (by linarith)
  have h5 : Real.sqrt ((Y - 1 / 2) ^ 2) ≤ Real.sqrt (Y ^ 2 + D) := Real.sqrt_le_sqrt h1
  have h6 : Real.sqrt (Y ^ 2 + D) < Real.sqrt ((Y + 1 / 2) ^ 2) :=
    Real.sqrt_lt_sqrt (le_trans (sq_nonneg _) h1) h2
  rw [h3] at h5
  rw [h4] at h6
  constructor <;> linarith

lemma a_eq (j : ℕ) : a (j + 1) = 27 * (2 * (sg j : ℚ) * ((P j).1 : ℚ) - 11) / 125 := by
  unfold a
  rw [x_eq, y_eq]
  have hk := key_id (P j).1 (P j).2 (sg j) (sg_sq j) (P_norm j)
  have hkQ : (((P j).1 : ℚ) ^ 2 - 6 * (sg j : ℚ) * ((P j).1 : ℚ) + 4) ^ 3
      = 125 * (((P j).2 : ℚ) * (((P j).1 : ℚ) ^ 2 - 9 * (sg j : ℚ) * ((P j).1 : ℚ) + 19)) ^ 2
        + 27 * (2 * (sg j : ℚ) * ((P j).1 : ℚ) - 11) := by exact_mod_cast hk
  push_cast
  linear_combination hkQ / 125

end OMA.P200218

open OMA.S_oeis_a200218 OMA.P200218 in
theorem OMA.solution : type_of% @OMA.S_oeis_a200218.main := by
  intro n hn
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 4 := ⟨n - 4, by omega⟩
  have e1 : j + 4 - 1 = j + 3 := by omega
  have e2 : j + 4 - 2 = j + 2 := by omega
  have e3 : j + 4 - 3 = j + 1 := by omega
  rw [e1, e2, e3]
  have h4 : a (j + 4) = _ := a_eq (j + 3)
  have h3 : a (j + 3) = _ := a_eq (j + 2)
  have h2 : a (j + 2) = _ := a_eq (j + 1)
  have h1 : a (j + 1) = _ := a_eq (j)
  rw [h4, h3, h2, h1]
  have p3 : P (j + 3) = _ := P_succ (j + 2)
  have p2 : P (j + 2) = _ := P_succ (j + 1)
  have p1 : P (j + 1) = _ := P_succ (j)
  simp only [p3, p2, p1, sg]
  push_cast
  ring
