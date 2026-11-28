import OMAReductions.R_Arxiv_1601_03081_crystals_components_unique_R3

-- Step Arxiv.1601.03081.crystals_components_unique.R3.H1: hypothesis H1 of reduction Arxiv.1601.03081.crystals_components_unique.R3
-- Credit: @luciusacarr
-- H1 := ∀ n a b : ℕ, IsCrystalWithComponents n a b → a≤b →     (a=5 ∧ b=7) ∨ (∃ d : ℕ, a=2*d+7 ∧ b=2*d^2+12*d+17) ∨     (∃ j : ℕ, a=2*j^2+4*j+1 ∧ b=2*j^2+8*j+7) ∨     ∃ q : ℕ, 5≤q ∧ 2*q<a ∧ (a+b)^2=q*((a+1)*(b+1))

/-! Write `(a+b)^2 = q(a+1)(b+1)`. For `q ≤ 4` a direct computation: `q = 3` gives only `(5,7)`
and `q = 4` gives the parabolic family. For `q ≥ 5` and `a ≤ 2q`, Vieta jumping in `b` gives the
partner `c = q(a+1) - 2a - b` with `c b = a^2 - q(a+1)` and the same equation; then
`1 ≤ c < a`, the size bound forces `c ≤ 6`, and only `c = 1` survives, which is the cubic family. -/

namespace OMA.S3H1

theorem core (a b q : ℤ) (ha : 2 ≤ a) (hab : a ≤ b) (hq : 5 ≤ q) (h2q : a ≤ 2 * q)
    (e : (a + b) ^ 2 = q * ((a + 1) * (b + 1))) :
    a = 2 * q - 1 ∧ b = 2 * q ^ 2 - 4 * q + 1 := by
  obtain ⟨c, hc⟩ : ∃ c, c = q * (a + 1) - 2 * a - b := ⟨_, rfl⟩
  have hcb : c * b = a ^ 2 - q * (a + 1) := by rw [hc]; linear_combination (-1 : ℤ) * e
  have hce : (a + c) ^ 2 = q * ((a + 1) * (c + 1)) := by rw [hc]; linear_combination e
  have hc0 : -1 ≤ c := by
    by_contra hlt
    have h1 : (a + 1) * (c + 1) < 0 := mul_neg_of_pos_of_neg (by linarith) (by linarith)
    have h2 : q * ((a + 1) * (c + 1)) < 0 := mul_neg_of_pos_of_neg (by linarith) h1
    nlinarith [sq_nonneg (a + c)]
  have hcm1 : c ≠ -1 := by
    rintro rfl
    have : (a - 1) ^ 2 = 0 := by nlinarith
    have : a - 1 = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
    linarith
  have hcz : c ≠ 0 := by
    rintro rfl
    have h : (a + 1) * (q - a + 1) = 1 := by nlinarith
    rcases le_or_gt (q - a + 1) 0 with h3 | h3
    · nlinarith
    · nlinarith
  have hc1 : 1 ≤ c := by omega
  have hca : c < a := by nlinarith
  have hc6 : c ≤ 6 := by
    have h1 : a * ((a + 1) * (c + 1)) ≤ 2 * q * ((a + 1) * (c + 1)) :=
      mul_le_mul_of_nonneg_right h2q (by positivity)
    have h2 : (a + c) ^ 2 < 4 * a ^ 2 := by nlinarith
    have h3 : a * ((a + 1) * (c + 1)) < a * (8 * a) := by nlinarith
    have h4 : (a + 1) * (c + 1) < 8 * a := lt_of_mul_lt_mul_left h3 (by linarith)
    nlinarith
  have hA : a * ((a + 1) * (c + 1)) ≤ 2 * q * ((a + 1) * (c + 1)) :=
    mul_le_mul_of_nonneg_right h2q (by positivity)
  have hB : 5 * ((a + 1) * (c + 1)) ≤ q * ((a + 1) * (c + 1)) :=
    mul_le_mul_of_nonneg_right hq (by positivity)
  interval_cases c
  · have h : (a + 1) * (a + 1 - 2 * q) = 0 := by nlinarith
    rcases mul_eq_zero.mp h with h | h
    · linarith
    · have ha' : a = 2 * q - 1 := by linarith
      refine ⟨ha', ?_⟩
      subst ha'
      nlinarith
  all_goals nlinarith

end OMA.S3H1

open Arxiv.«1601.03081» in
theorem OMA.solution : OMA.R_Arxiv_1601_03081_crystals_components_unique_R3.H1 := by
  intro n a b h hab
  have hd := ((isCrystalWithComponents_iff_sum_sq_dvd n a b).mp h)
  obtain ⟨-, ha, hb, -, q, hq0⟩ := hd
  have hq : (a + b) ^ 2 = q * ((a + 1) * (b + 1)) := by rw [hq0]; ring
  clear hq0
  by_cases big : 5 ≤ q ∧ 2 * q < a
  · exact Or.inr (Or.inr (Or.inr ⟨q, big.1, big.2, hq⟩))
  rcases lt_or_ge q 5 with hq5 | hq5
  · interval_cases q
    · nlinarith
    · nlinarith
    · have hb3 : b ≤ 3 := by nlinarith
      have ha3 : a ≤ 3 := by nlinarith
      interval_cases a <;> interval_cases b <;> omega
    · have hb3 : b ≤ 12 := by nlinarith
      have ha3 : a ≤ 12 := by omega
      interval_cases a <;> interval_cases b <;> simp_all
    · obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hab
      have ht : t * t = 8 * a + 4 * t + 4 := by nlinarith
      rcases Nat.even_or_odd' t with ⟨m, rfl | rfl⟩
      · have hm : m * m = 2 * a + 2 * m + 1 := by nlinarith
        rcases Nat.even_or_odd' m with ⟨k, rfl | rfl⟩
        · have h2 : 4 * (k * k) = 2 * a + 4 * k + 1 := by nlinarith [hm]
          generalize k * k = K at h2
          omega
        · have hk : 2 * (k * k) = a + 1 := by nlinarith
          obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by
            rcases k with _ | k
            · omega
            · omega⟩
          refine Or.inr (Or.inr (Or.inl ⟨j, ?_, ?_⟩)) <;> nlinarith
      · have h' : 4 * (m * m) + 4 * m + 1 = 8 * a + 8 * m + 8 := by nlinarith
        generalize m * m = M at h'
        omega
  · have h2q : a ≤ 2 * q := by omega
    have key := OMA.S3H1.core a b q (by exact_mod_cast ha) (by exact_mod_cast hab)
      (by exact_mod_cast hq5) (by exact_mod_cast h2q) (by exact_mod_cast hq)
    obtain ⟨d, rfl⟩ : ∃ d, q = d + 4 := ⟨q - 4, by omega⟩
    obtain ⟨k1, k2⟩ := key
    refine Or.inr (Or.inl ⟨d, ?_, ?_⟩)
    · push_cast at k1
      omega
    · have : (b : ℤ) = 2 * (d : ℤ) ^ 2 + 12 * d + 17 := by rw [k2]; push_cast; ring
      exact_mod_cast this
