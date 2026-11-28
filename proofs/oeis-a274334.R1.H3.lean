import OMAReductions.R_oeis_a274334_R1
import Mathlib

-- Step oeis-a274334.R1.H3: hypothesis H3 of reduction oeis-a274334.R1
-- Credit: @Raimo33

def icb (r : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, lo, _ => lo
  | f + 1, lo, hi =>
    if hi ≤ lo + 1 then lo
    else if ((lo + hi) / 2) ^ 3 ≤ r then icb r f ((lo + hi) / 2) hi
    else icb r f lo ((lo + hi) / 2)

lemma icb_spec (z : ℕ) : ∀ f lo hi, lo ≤ z → z < hi → hi - lo ≤ f → icb (z ^ 3) f lo hi = z
  | 0, lo, hi, h1, h2, h3 => by omega
  | f + 1, lo, hi, h1, h2, h3 => by
    simp only [icb]
    split_ifs with h4 h5
    · omega
    · have : (lo + hi) / 2 ≤ z := (Nat.pow_le_pow_iff_left (by norm_num)).mp h5
      exact icb_spec z f _ hi this h2 (by omega)
    · have : z < (lo + hi) / 2 := by
        by_contra hc
        exact h5 (Nat.pow_le_pow_left (by omega) 3)
      exact icb_spec z f lo _ h1 this (by omega)

def cnd (k w x y : ℕ) : Bool :=
  !(decide (w ^ 3 + x ^ 3 + y ^ 3 < k ^ 3)) ||
    decide ((icb (k ^ 3 - (w ^ 3 + x ^ 3 + y ^ 3)) k 0 k) ^ 3 ≠ k ^ 3 - (w ^ 3 + x ^ 3 + y ^ 3))

def rowOK (k w : ℕ) : Bool :=
  (List.range' w (k - w)).all fun x => (List.range' x (k - x)).all fun y => cnd k w x y

lemma lt_of_cube_lt {a k : ℕ} (h : a ^ 3 < k ^ 3) : a < k :=
  lt_of_pow_lt_pow_left₀ 3 (Nat.zero_le _) h

lemma sort3 (w x y : ℕ) : ∃ a b c : ℕ, a ≤ b ∧ b ≤ c ∧
    a ^ 3 + b ^ 3 + c ^ 3 = w ^ 3 + x ^ 3 + y ^ 3 ∧
    (a = w ∨ a = x ∨ a = y) ∧ (b = w ∨ b = x ∨ b = y) ∧ (c = w ∨ c = x ∨ c = y) := by
  rcases le_total w x with h1 | h1 <;> rcases le_total x y with h2 | h2 <;>
    rcases le_total w y with h3 | h3 <;>
    first
    | exact ⟨w, x, y, by omega, by omega, by ring, by simp, by simp, by simp⟩
    | exact ⟨w, y, x, by omega, by omega, by ring, by simp, by simp, by simp⟩
    | exact ⟨x, w, y, by omega, by omega, by ring, by simp, by simp, by simp⟩
    | exact ⟨x, y, w, by omega, by omega, by ring, by simp, by simp, by simp⟩
    | exact ⟨y, w, x, by omega, by omega, by ring, by simp, by simp, by simp⟩
    | exact ⟨y, x, w, by omega, by omega, by ring, by simp, by simp, by simp⟩

lemma not_term (k : ℕ) (h : ∀ w, 1 ≤ w → w < k → rowOK k w = true) :
    ¬ OMA.S_oeis_a274334.IsTerm k := by
  rintro ⟨w, x, y, z, hw, hx, hy, hz, e⟩
  obtain ⟨a, b, c, hab, hbc, hs, ha, hb, hc⟩ := sort3 w x y
  have pw : 0 < w ^ 3 := by positivity
  have px : 0 < x ^ 3 := by positivity
  have py : 0 < y ^ 3 := by positivity
  have pz : 0 < z ^ 3 := by positivity
  have hwk : w < k := lt_of_cube_lt (by omega)
  have hxk : x < k := lt_of_cube_lt (by omega)
  have hyk : y < k := lt_of_cube_lt (by omega)
  have hzk : z < k := lt_of_cube_lt (by omega)
  have ha1 : 1 ≤ a := by omega
  have hck : c < k := by omega
  have := h a ha1 (by omega)
  simp only [rowOK, List.all_eq_true, List.mem_range'_1] at this
  have := this b ⟨hab, by omega⟩ c ⟨hbc, by omega⟩
  have hs' : a ^ 3 + b ^ 3 + c ^ 3 < k ^ 3 := by omega
  have hr : k ^ 3 - (a ^ 3 + b ^ 3 + c ^ 3) = z ^ 3 := by omega
  simp only [cnd, hr, icb_spec z k 0 k (Nat.zero_le _) hzk (by omega)] at this
  simp [hs'] at this

lemma ok0 : ∀ w, 1 ≤ w → w < 0 → rowOK 0 w = true := by
  intro w h1 h2; omega

lemma ok1 : ∀ w, 1 ≤ w → w < 1 → rowOK 1 w = true := by
  intro w h1 h2; omega

lemma c2_1 : ∀ w, 1 ≤ w → w < 2 → rowOK 2 w = true := by decide +kernel

lemma ok2 : ∀ w, 1 ≤ w → w < 2 → rowOK 2 w = true := by
  intro w h1 h2
  exact c2_1 w (by omega) h2

lemma c3_1 : ∀ w, 1 ≤ w → w < 3 → rowOK 3 w = true := by decide +kernel

lemma ok3 : ∀ w, 1 ≤ w → w < 3 → rowOK 3 w = true := by
  intro w h1 h2
  exact c3_1 w (by omega) h2

lemma c4_1 : ∀ w, 1 ≤ w → w < 4 → rowOK 4 w = true := by decide +kernel

lemma ok4 : ∀ w, 1 ≤ w → w < 4 → rowOK 4 w = true := by
  intro w h1 h2
  exact c4_1 w (by omega) h2

lemma c5_1 : ∀ w, 1 ≤ w → w < 5 → rowOK 5 w = true := by decide +kernel

lemma ok5 : ∀ w, 1 ≤ w → w < 5 → rowOK 5 w = true := by
  intro w h1 h2
  exact c5_1 w (by omega) h2

lemma c6_1 : ∀ w, 1 ≤ w → w < 6 → rowOK 6 w = true := by decide +kernel

lemma ok6 : ∀ w, 1 ≤ w → w < 6 → rowOK 6 w = true := by
  intro w h1 h2
  exact c6_1 w (by omega) h2

lemma c8_1 : ∀ w, 1 ≤ w → w < 8 → rowOK 8 w = true := by decide +kernel

lemma ok8 : ∀ w, 1 ≤ w → w < 8 → rowOK 8 w = true := by
  intro w h1 h2
  exact c8_1 w (by omega) h2

lemma c9_1 : ∀ w, 1 ≤ w → w < 9 → rowOK 9 w = true := by decide +kernel

lemma ok9 : ∀ w, 1 ≤ w → w < 9 → rowOK 9 w = true := by
  intro w h1 h2
  exact c9_1 w (by omega) h2

lemma c10_1 : ∀ w, 1 ≤ w → w < 10 → rowOK 10 w = true := by decide +kernel

lemma ok10 : ∀ w, 1 ≤ w → w < 10 → rowOK 10 w = true := by
  intro w h1 h2
  exact c10_1 w (by omega) h2

lemma c11_1 : ∀ w, 1 ≤ w → w < 11 → rowOK 11 w = true := by decide +kernel

lemma ok11 : ∀ w, 1 ≤ w → w < 11 → rowOK 11 w = true := by
  intro w h1 h2
  exact c11_1 w (by omega) h2

lemma c15_1 : ∀ w, 1 ≤ w → w < 15 → rowOK 15 w = true := by decide +kernel

lemma ok15 : ∀ w, 1 ≤ w → w < 15 → rowOK 15 w = true := by
  intro w h1 h2
  exact c15_1 w (by omega) h2

lemma c16_1 : ∀ w, 1 ≤ w → w < 16 → rowOK 16 w = true := by decide +kernel

lemma ok16 : ∀ w, 1 ≤ w → w < 16 → rowOK 16 w = true := by
  intro w h1 h2
  exact c16_1 w (by omega) h2

lemma c17_1 : ∀ w, 1 ≤ w → w < 17 → rowOK 17 w = true := by decide +kernel

lemma ok17 : ∀ w, 1 ≤ w → w < 17 → rowOK 17 w = true := by
  intro w h1 h2
  exact c17_1 w (by omega) h2

lemma c19_1 : ∀ w, 1 ≤ w → w < 19 → rowOK 19 w = true := by decide +kernel

lemma ok19 : ∀ w, 1 ≤ w → w < 19 → rowOK 19 w = true := by
  intro w h1 h2
  exact c19_1 w (by omega) h2

lemma c22_1 : ∀ w, 1 ≤ w → w < 22 → rowOK 22 w = true := by decide +kernel

lemma ok22 : ∀ w, 1 ≤ w → w < 22 → rowOK 22 w = true := by
  intro w h1 h2
  exact c22_1 w (by omega) h2

lemma c27_1 : ∀ w, 1 ≤ w → w < 27 → rowOK 27 w = true := by decide +kernel

lemma ok27 : ∀ w, 1 ≤ w → w < 27 → rowOK 27 w = true := by
  intro w h1 h2
  exact c27_1 w (by omega) h2

lemma c29_1 : ∀ w, 1 ≤ w → w < 29 → rowOK 29 w = true := by decide +kernel

lemma ok29 : ∀ w, 1 ≤ w → w < 29 → rowOK 29 w = true := by
  intro w h1 h2
  exact c29_1 w (by omega) h2

lemma c47_1 : ∀ w, 1 ≤ w → w < 7 → rowOK 47 w = true := by decide +kernel

lemma c47_7 : ∀ w, 7 ≤ w → w < 15 → rowOK 47 w = true := by decide +kernel

lemma c47_15 : ∀ w, 15 ≤ w → w < 47 → rowOK 47 w = true := by decide +kernel

lemma ok47 : ∀ w, 1 ≤ w → w < 47 → rowOK 47 w = true := by
  intro w h1 h2
  by_cases h7 : w < 7
  · exact c47_1 w (by omega) h7
  by_cases h15 : w < 15
  · exact c47_7 w (by omega) h15
  exact c47_15 w (by omega) h2

lemma c58_1 : ∀ w, 1 ≤ w → w < 4 → rowOK 58 w = true := by decide +kernel

lemma c58_4 : ∀ w, 4 ≤ w → w < 8 → rowOK 58 w = true := by decide +kernel

lemma c58_8 : ∀ w, 8 ≤ w → w < 13 → rowOK 58 w = true := by decide +kernel

lemma c58_13 : ∀ w, 13 ≤ w → w < 19 → rowOK 58 w = true := by decide +kernel

lemma c58_19 : ∀ w, 19 ≤ w → w < 28 → rowOK 58 w = true := by decide +kernel

lemma c58_28 : ∀ w, 28 ≤ w → w < 58 → rowOK 58 w = true := by decide +kernel

lemma ok58 : ∀ w, 1 ≤ w → w < 58 → rowOK 58 w = true := by
  intro w h1 h2
  by_cases h4 : w < 4
  · exact c58_1 w (by omega) h4
  by_cases h8 : w < 8
  · exact c58_4 w (by omega) h8
  by_cases h13 : w < 13
  · exact c58_8 w (by omega) h13
  by_cases h19 : w < 19
  · exact c58_13 w (by omega) h19
  by_cases h28 : w < 28
  · exact c58_19 w (by omega) h28
  exact c58_28 w (by omega) h2

lemma c61_1 : ∀ w, 1 ≤ w → w < 4 → rowOK 61 w = true := by decide +kernel

lemma c61_4 : ∀ w, 4 ≤ w → w < 7 → rowOK 61 w = true := by decide +kernel

lemma c61_7 : ∀ w, 7 ≤ w → w < 11 → rowOK 61 w = true := by decide +kernel

lemma c61_11 : ∀ w, 11 ≤ w → w < 16 → rowOK 61 w = true := by decide +kernel

lemma c61_16 : ∀ w, 16 ≤ w → w < 22 → rowOK 61 w = true := by decide +kernel

lemma c61_22 : ∀ w, 22 ≤ w → w < 31 → rowOK 61 w = true := by decide +kernel

lemma c61_31 : ∀ w, 31 ≤ w → w < 61 → rowOK 61 w = true := by decide +kernel

lemma ok61 : ∀ w, 1 ≤ w → w < 61 → rowOK 61 w = true := by
  intro w h1 h2
  by_cases h4 : w < 4
  · exact c61_1 w (by omega) h4
  by_cases h7 : w < 7
  · exact c61_4 w (by omega) h7
  by_cases h11 : w < 11
  · exact c61_7 w (by omega) h11
  by_cases h16 : w < 16
  · exact c61_11 w (by omega) h16
  by_cases h22 : w < 22
  · exact c61_16 w (by omega) h22
  by_cases h31 : w < 31
  · exact c61_22 w (by omega) h31
  exact c61_31 w (by omega) h2

lemma c71_1 : ∀ w, 1 ≤ w → w < 3 → rowOK 71 w = true := by decide +kernel

lemma c71_3 : ∀ w, 3 ≤ w → w < 5 → rowOK 71 w = true := by decide +kernel

lemma c71_5 : ∀ w, 5 ≤ w → w < 7 → rowOK 71 w = true := by decide +kernel

lemma c71_7 : ∀ w, 7 ≤ w → w < 9 → rowOK 71 w = true := by decide +kernel

lemma c71_9 : ∀ w, 9 ≤ w → w < 12 → rowOK 71 w = true := by decide +kernel

lemma c71_12 : ∀ w, 12 ≤ w → w < 15 → rowOK 71 w = true := by decide +kernel

lemma c71_15 : ∀ w, 15 ≤ w → w < 18 → rowOK 71 w = true := by decide +kernel

lemma c71_18 : ∀ w, 18 ≤ w → w < 22 → rowOK 71 w = true := by decide +kernel

lemma c71_22 : ∀ w, 22 ≤ w → w < 27 → rowOK 71 w = true := by decide +kernel

lemma c71_27 : ∀ w, 27 ≤ w → w < 33 → rowOK 71 w = true := by decide +kernel

lemma c71_33 : ∀ w, 33 ≤ w → w < 43 → rowOK 71 w = true := by decide +kernel

lemma c71_43 : ∀ w, 43 ≤ w → w < 71 → rowOK 71 w = true := by decide +kernel

lemma ok71 : ∀ w, 1 ≤ w → w < 71 → rowOK 71 w = true := by
  intro w h1 h2
  by_cases h3 : w < 3
  · exact c71_1 w (by omega) h3
  by_cases h5 : w < 5
  · exact c71_3 w (by omega) h5
  by_cases h7 : w < 7
  · exact c71_5 w (by omega) h7
  by_cases h9 : w < 9
  · exact c71_7 w (by omega) h9
  by_cases h12 : w < 12
  · exact c71_9 w (by omega) h12
  by_cases h15 : w < 15
  · exact c71_12 w (by omega) h15
  by_cases h18 : w < 18
  · exact c71_15 w (by omega) h18
  by_cases h22 : w < 22
  · exact c71_18 w (by omega) h22
  by_cases h27 : w < 27
  · exact c71_22 w (by omega) h27
  by_cases h33 : w < 33
  · exact c71_27 w (by omega) h33
  by_cases h43 : w < 43
  · exact c71_33 w (by omega) h43
  exact c71_43 w (by omega) h2

theorem OMA.solution : OMA.R_oeis_a274334_R1.H3 := by
  intro k hk
  simp only [Finset.mem_insert, Finset.mem_singleton] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact not_term _ ok0
  · exact not_term _ ok1
  · exact not_term _ ok2
  · exact not_term _ ok3
  · exact not_term _ ok4
  · exact not_term _ ok5
  · exact not_term _ ok6
  · exact not_term _ ok8
  · exact not_term _ ok9
  · exact not_term _ ok10
  · exact not_term _ ok11
  · exact not_term _ ok15
  · exact not_term _ ok16
  · exact not_term _ ok17
  · exact not_term _ ok19
  · exact not_term _ ok22
  · exact not_term _ ok27
  · exact not_term _ ok29
  · exact not_term _ ok47
  · exact not_term _ ok58
  · exact not_term _ ok61
  · exact not_term _ ok71
