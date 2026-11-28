import OMAStatements.S_oeis_a267209

namespace OMA.S_oeis_a267209

open PowerSeries

def fl : ℕ → ℕ
  | 0 => 2004
  | 1 => 2298
  | 2 => 1311
  | _ => 3747

def Vnat (t a : ℕ) : Bool :=
  if t < a then decide (t % 2 = 1)
  else if t - a ≤ 1 then decide (t % 2 = 0 ∨ t - a = 1)
  else if a = 0 then decide (t % 3 ≠ 0)
  else (fl (t % 4)).testBit ((t - a) % 12)

def V (t : ℕ) (x : ℤ) : Bool := Vnat t x.natAbs

def r109 (l m r : Bool) : Bool :=
  Nat.testBit 109 (4 * l.toNat + 2 * m.toNat + r.toNat)

lemma r109_symm (l m r : Bool) : r109 l m r = r109 r m l := by
  cases l <;> cases m <;> cases r <;> rfl

lemma step_checks :
    (∀ t < 3, r109 (Vnat t 1) (Vnat t 0) (Vnat t 1) = Vnat (t + 1) 0) ∧
    (∀ m < 12,
      r109 ((fl (m % 4)).testBit ((m + 11) % 12)) (decide (m % 3 ≠ 0))
        ((fl (m % 4)).testBit ((m + 11) % 12)) = decide ((m + 1) % 3 ≠ 0)) ∧
    (∀ t < 4, r109 (Vnat t 0) (Vnat t 1) (Vnat t 2) = Vnat (t + 1) 1) ∧
    (∀ m < 12,
      r109 (decide (m % 3 ≠ 0)) ((fl (m % 4)).testBit ((m + 11) % 12))
        ((fl (m % 4)).testBit ((m + 10) % 12)) = (fl ((m + 1) % 4)).testBit m) ∧
    (∀ p < 2, r109 (decide (p = 1)) (decide (p = 1)) (decide (p = 1)) = decide ((p + 1) % 2 = 1)) ∧
    (∀ p < 4, ∀ k < 4,
      r109 (Vnat (3 + p + k) (3 + p)) (Vnat (3 + p + k) (4 + p)) (Vnat (3 + p + k) (5 + p)) =
        Vnat (4 + p + k) (4 + p)) ∧
    (∀ m < 4, ∀ d < 12,
      r109 ((fl m).testBit ((d + 1) % 12)) ((fl m).testBit d) ((fl m).testBit ((d + 11) % 12)) =
        (fl ((m + 1) % 4)).testBit ((d + 1) % 12)) := by
  decide +kernel

lemma vnat_shift (t a T A : ℕ) (ha : 1 ≤ a) (hA : 1 ≤ A)
    (hm4 : t % 4 = T % 4) (hlt : t < a ↔ T < A) (hsub : t - a = T - A) :
    Vnat t a = Vnat T A := by
  have hm2 : t % 2 = T % 2 := by omega
  unfold Vnat
  by_cases h1 : t < a
  · rw [if_pos h1, if_pos (hlt.mp h1), hm2]
  · rw [if_neg h1, if_neg (mt hlt.mpr h1), hsub]
    by_cases h2 : T - A ≤ 1
    · rw [if_pos h2, if_pos h2, hm2]
    · rw [if_neg h2, if_neg h2, if_neg (by omega), if_neg (by omega), hm4]

lemma vnat_step_zero (t : ℕ) : r109 (Vnat t 1) (Vnat t 0) (Vnat t 1) = Vnat (t + 1) 0 := by
  rcases Nat.lt_or_ge t 3 with ht | ht
  · exact step_checks.1 t ht
  · have h := step_checks.2.1 (t % 12) (Nat.mod_lt _ (by omega))
    have h1 : Vnat t 1 = (fl ((t % 12) % 4)).testBit ((t % 12 + 11) % 12) := by
      unfold Vnat; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      have e1 : t % 4 = (t % 12) % 4 := by omega
      have e2 : (t - 1) % 12 = (t % 12 + 11) % 12 := by omega
      rw [e1, e2]
    have h0 : Vnat t 0 = decide ((t % 12) % 3 ≠ 0) := by
      unfold Vnat; rw [if_neg (by omega), if_neg (by omega), if_pos rfl]
      exact decide_eq_decide.mpr (by omega)
    have h2 : Vnat (t + 1) 0 = decide ((t % 12 + 1) % 3 ≠ 0) := by
      unfold Vnat; rw [if_neg (by omega), if_neg (by omega), if_pos rfl]
      exact decide_eq_decide.mpr (by omega)
    rw [h1, h0, h2]; exact h

lemma vnat_step_pos (t a : ℕ) (ha : 1 ≤ a) :
    r109 (Vnat t (a - 1)) (Vnat t a) (Vnat t (a + 1)) = Vnat (t + 1) a := by
  rcases eq_or_lt_of_le ha with rfl | ha2
  · rcases Nat.lt_or_ge t 4 with ht | ht
    · exact step_checks.2.2.1 t ht
    · have h := step_checks.2.2.2.1 (t % 12) (Nat.mod_lt _ (by omega))
      have h0 : Vnat t 0 = decide ((t % 12) % 3 ≠ 0) := by
        unfold Vnat; rw [if_neg (by omega), if_neg (by omega), if_pos rfl]
        exact decide_eq_decide.mpr (by omega)
      have h1 : Vnat t 1 = (fl ((t % 12) % 4)).testBit ((t % 12 + 11) % 12) := by
        unfold Vnat; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
        have e1 : t % 4 = (t % 12) % 4 := by omega
        have e2 : (t - 1) % 12 = (t % 12 + 11) % 12 := by omega
        rw [e1, e2]
      have h2 : Vnat t 2 = (fl ((t % 12) % 4)).testBit ((t % 12 + 10) % 12) := by
        unfold Vnat; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
        have e1 : t % 4 = (t % 12) % 4 := by omega
        have e2 : (t - 2) % 12 = (t % 12 + 10) % 12 := by omega
        rw [e1, e2]
      have h3 : Vnat (t + 1) 1 = (fl ((t % 12 + 1) % 4)).testBit (t % 12) := by
        unfold Vnat; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
        have e1 : (t + 1) % 4 = (t % 12 + 1) % 4 := by omega
        have e2 : (t + 1 - 1) % 12 = t % 12 := by omega
        rw [e1, e2]
      rw [h0, h1, h2, h3]; exact h
  · rcases Nat.lt_or_ge (t + 1) a with hfar | hnear
    · have h := step_checks.2.2.2.2.1 (t % 2) (Nat.mod_lt _ (by omega))
      unfold Vnat
      rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), if_pos (by omega)]
      have e : (t + 1) % 2 = (t % 2 + 1) % 2 := by omega
      rw [e]; exact h
    · rcases Nat.lt_or_ge t (a + 3) with hedge | hint
      · set p := a % 4
        set k := t + 1 - a
        have h := step_checks.2.2.2.2.2.1 p (Nat.mod_lt _ (by omega)) k (by omega)
        rw [vnat_shift t (a - 1) (3 + p + k) (3 + p) (by omega) (by omega) (by omega) (by omega) (by omega),
            vnat_shift t a (3 + p + k) (4 + p) (by omega) (by omega) (by omega) (by omega) (by omega),
            vnat_shift t (a + 1) (3 + p + k) (5 + p) (by omega) (by omega) (by omega) (by omega) (by omega),
            vnat_shift (t + 1) a (4 + p + k) (4 + p) (by omega) (by omega) (by omega) (by omega) (by omega)]
        exact h
      · have h := step_checks.2.2.2.2.2.2 (t % 4) (Nat.mod_lt _ (by omega))
          ((t - a) % 12) (Nat.mod_lt _ (by omega))
        unfold Vnat
        rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
            if_neg (by omega), if_neg (by omega), if_neg (by omega),
            if_neg (by omega), if_neg (by omega), if_neg (by omega),
            if_neg (by omega), if_neg (by omega), if_neg (by omega)]
        have e1 : (t - (a - 1)) % 12 = ((t - a) % 12 + 1) % 12 := by omega
        have e2 : (t - (a + 1)) % 12 = ((t - a) % 12 + 11) % 12 := by omega
        have e3 : (t + 1) % 4 = (t % 4 + 1) % 4 := by omega
        have e4 : (t + 1 - a) % 12 = ((t - a) % 12 + 1) % 12 := by omega
        rw [e1, e2, e3, e4]; exact h

lemma state_eq_V (t : ℕ) (x : ℤ) : state 109 t x = V t x := by
  induction t generalizing x with
  | zero =>
    unfold state V Vnat
    by_cases hx : x = 0
    · subst hx; rfl
    · rw [if_pos (Int.natAbs_pos.mpr hx)]; simp [hx]
  | succ t ih =>
    change r109 (state 109 t (x - 1)) (state 109 t x) (state 109 t (x + 1)) = V (t + 1) x
    rw [ih, ih, ih]
    rcases Nat.eq_zero_or_pos x.natAbs with ha0 | hapos
    · have hx0 := Int.natAbs_eq_zero.mp ha0; subst hx0; exact vnat_step_zero t
    · rcases le_or_gt 0 x with hx | hx
      · have h1 : (x - 1).natAbs = x.natAbs - 1 := by omega
        have h2 : (x + 1).natAbs = x.natAbs + 1 := by omega
        unfold V; rw [h1, h2]; exact vnat_step_pos t x.natAbs hapos
      · have h1 : (x - 1).natAbs = x.natAbs + 1 := by omega
        have h2 : (x + 1).natAbs = x.natAbs - 1 := by omega
        unfold V; rw [h1, h2, r109_symm]; exact vnat_step_pos t x.natAbs hapos

lemma c_val (n : ℕ) : c n = if n = 0 then 1 else if n % 3 = 0 then 0 else 1 := by
  unfold c; rw [state_eq_V]; unfold V Vnat
  simp only [Int.natAbs_zero, Nat.not_lt_zero, Nat.sub_zero, ↓reduceIte]
  rcases n with _ | _ | n
  · rfl
  · rfl
  · rw [if_neg (by omega)]; by_cases h : (n + 2) % 3 = 0 <;> simp [h]

lemma a_succ (n : ℕ) : a (n + 1) = 10 * a n + c (n + 1) := by
  rw [a, Finset.sum_range_succ, Nat.sub_self, pow_zero, mul_one, a, Finset.mul_sum]
  congr 1; apply Finset.sum_congr rfl; intro k hk
  rw [Finset.mem_range] at hk
  rw [show n + 1 - k = (n - k) + 1 by omega, pow_succ]; ring

lemma rec_main (n : ℕ) (hn : 3 < n) :
    (a n : ℤ) = 10 * a (n - 1) + a (n - 3) - 10 * a (n - 4) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  have h1 : a (m + 4) = 10 * a (m + 3) + c (m + 4) := a_succ (m + 3)
  have h2 : a (m + 1) = 10 * a m + c (m + 1) := a_succ m
  have hc : c (m + 4) = c (m + 1) := by
    simp [c_val, show (m + 4) % 3 = (m + 1) % 3 by omega]
  have s1 : m + 4 - 1 = m + 3 := by omega
  have s3 : m + 4 - 3 = m + 1 := by omega
  have s4 : m + 4 - 4 = m := by omega
  rw [s1, s3, s4]; omega

theorem main_proof :
    (∀ n : ℕ, 3 < n → (a n : ℤ) = 10 * a (n - 1) + a (n - 3) - 10 * a (n - 4)) ∧
    A = (1 + X + X ^ 2 - X ^ 3) * ((1 - X) * (1 - 10 * X) * (1 + X + X ^ 2))⁻¹ := by
  refine ⟨rec_main, ?_⟩
  set D : ℚ⟦X⟧ := (1 - X) * (1 - 10 * X) * (1 + X + X ^ 2)
  have hD0 : constantCoeff D ≠ 0 := by simp [D]
  have hDexp : A * D = A - C 10 * (A * X ^ 1) - A * X ^ 3 + C 10 * (A * X ^ 4) := by
    simp only [D, map_ofNat]; ring
  have hNexp : (1 + X + X ^ 2 - X ^ 3 : ℚ⟦X⟧) = 1 + X ^ 1 + X ^ 2 - X ^ 3 := by ring
  have key : A * D = 1 + X + X ^ 2 - X ^ 3 := by
    rw [hDexp, hNexp]; ext n
    simp only [map_add, map_sub, coeff_C_mul, coeff_mul_X_pow', coeff_X_pow, coeff_one, A, coeff_mk]
    rcases Nat.lt_or_ge n 4 with hn | hn
    · have a0 : a 0 = 1 := by simp [a, c_val]
      have a1 : a 1 = 11 := by rw [a_succ, a0, c_val]; rfl
      have a2 : a 2 = 111 := by rw [a_succ, a1, c_val]; rfl
      have a3 : a 3 = 1110 := by rw [a_succ, a2, c_val]; rfl
      interval_cases n <;> simp [a0, a1, a2, a3] <;> norm_num
    · have hr : (a n : ℚ) = 10 * a (n - 1) + a (n - 3) - 10 * a (n - 4) := by
        exact_mod_cast rec_main n (by omega)
      simp only [show 1 ≤ n by omega, show 3 ≤ n by omega, show 4 ≤ n by omega,
        show n ≠ 0 by omega, show n ≠ 1 by omega, show n ≠ 2 by omega, show n ≠ 3 by omega, ↓reduceIte]
      linarith
  rw [← key, mul_assoc, PowerSeries.mul_inv_cancel _ hD0, mul_one]

end OMA.S_oeis_a267209

theorem OMA.solution : type_of% @OMA.S_oeis_a267209.main :=
  OMA.S_oeis_a267209.main_proof