import OMAReductions.R_Arxiv_1601_03081_crystals_components_unique_R1_H1_R1_H2_R1_H1_R1_H1_R1
import Mathlib

-- Step Arxiv.1601.03081.crystals_components_unique.R1.H1.R1.H2.R1.H1.R1.H1.R1.H2: hypothesis H2 of reduction Arxiv.1601.03081.crystals_components_unique.R1.H1.R1.H2.R1.H1.R1.H1.R1
-- Credit: @sebastianbachmaier
-- H2 := ∀ m t : ℕ, 129 ≤ m → Odd m → Odd t → t < 4*m^2 →     let c := 2*t^2-1     let b := 2*(t+1)^2-1     let a := b/m     m ∣ b → 3 ≤ a → a < c → a.Coprime c → c.Coprime b →     (∀ ell : ℕ, ell.Prime → ell ∣ m ∨ ell ∣ c ∨ ell ∣ b → ell%8=1 ∨ ell%8=7) →     c%8=1 ∧ b%8=7 →     ((m*c : ℕ) : ℤ)+1 ∣ ((a : ℤ)-1)^2 →     ((m*c : ℕ) : ℤ)+1 ∣ (((m : ℤ)^2-1)*((m : ℤ)^2-4*m-1))^2 →     (a : ℤ)+1 ∣ (((m : ℤ)^2-1)*((m : ℤ)^2+4*m-1))^2 →     ((m : ℤ)^3 < 4*((t : ℤ)+1)^2 ∧ ∃ quotient : ℤ, 1 ≤ quotient ∧ quotient < 64*(m : ℤ) ∧       (2*((t : ℤ)+1)^2-((m : ℤ)+1))^2 = quotient*(m : ℤ)^2*((m : ℤ)*(2*(t : ℤ)^2-1)+1)) →     16*((a+1)*(m*c+1)) ≤ (a+m*c)^2 →     ¬ ((a+1)*(m*c+1) ∣ (a+m*c)^2)

namespace CrystalFinite

lemma step1 (m s a w : ℤ) (h1 : m*a = 2*s^2 - 1)
    (hw : (a-1)^2 = (2*m*s^2 - 4*m*s + m + 1) * w) :
    ∃ j : ℤ, 8*m*s*(m-1)^2 - (m+1)^4 + 8*m*(m+1) = (2*m*s^2 - 4*m*s + m + 1) * j :=
  ⟨8*m - m^4*w + (2*m*s^2 - 4*m*s + m + 1) + 2*(4*m*s - (m+1)^2), by
    linear_combination (-m^4) * hw
      + m*(m^2*(a-1) + (2*m*s^2 - 4*m*s + m + 1) + (4*m*s - (m+1)^2)) * h1⟩

lemma key (m s a : ℤ) (hm : 21 ≤ m) (h1 : m*a = 2*s^2 - 1)
    (hdiv : (2*m*s^2 - 4*m*s + m + 1) ∣ (a-1)^2) : s ≤ 4*m := by
  by_contra hlt0
  have hlt : 4*m < s := not_le.mp hlt0
  obtain ⟨w, hw⟩ := hdiv
  obtain ⟨j, hR⟩ := step1 m s a w h1 hw
  have hm0 : (0:ℤ) ≤ m := by linarith
  have hm1 : (0:ℤ) ≤ m - 1 := by linarith
  have hs0 : (0:ℤ) ≤ s := by linarith
  have hms : (0:ℤ) ≤ m*s := mul_nonneg hm0 hs0
  have p2 : (0:ℤ) ≤ m*s*(s-2) := mul_nonneg hms (by linarith)
  have hD : (0:ℤ) < 2*m*s^2 - 4*m*s + m + 1 := by linarith [p2]
  obtain ⟨k, hk⟩ : ∃ k : ℤ, j + 1 = m * k :=
    ⟨(8*s*(m-1)^2 + 8*(m+1) - (m^3+4*m^2+6*m+4)) - j*(2*s^2 - 4*s + 1), by
      linear_combination (-1 : ℤ) * hR⟩
  rcases le_or_gt k 0 with hk0 | hk0
  · have hmk : m * k ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hm0 hk0
    have hj : j ≤ -1 := by linarith
    have hB : (2*m*s^2 - 4*m*s + m + 1) * j ≤ (2*m*s^2 - 4*m*s + m + 1) * (-1) :=
      mul_le_mul_of_nonneg_left hj hD.le
    have p1 : (0:ℤ) ≤ m*(m-1)^2*(s-m) :=
      mul_nonneg (mul_nonneg hm0 (sq_nonneg (m-1))) (by linarith)
    have h3 : (m+1)^2 ≤ 2*(m*(m-1)) := by
      linarith [mul_nonneg (show (0:ℤ) ≤ m - 21 by linarith) hm0]
    have h4 : (m+1)^2*(m+1)^2 ≤ (2*(m*(m-1)))*(2*(m*(m-1))) :=
      mul_le_mul h3 h3 (sq_nonneg (m+1))
        (mul_nonneg (by norm_num) (mul_nonneg hm0 hm1))
    linarith [hR, hB, p1, p2, h4, sq_nonneg (m*(m-1)), sq_nonneg m, hm]
  · have hk1 : (1:ℤ) ≤ k := by omega
    have hmk : m * 1 ≤ m * k := mul_le_mul_of_nonneg_left hk1 hm0
    have hj : m - 1 ≤ j := by linarith
    have hA : (2*m*s^2 - 4*m*s + m + 1) * (m-1) ≤ (2*m*s^2 - 4*m*s + m + 1) * j :=
      mul_le_mul_of_nonneg_left hj hD.le
    have q1 : (0:ℤ) ≤ m*s*(m-1)*(s-(4*m-2)) :=
      mul_nonneg (mul_nonneg hms hm1) (by linarith)
    have ha : (484:ℤ) ≤ (m+1)^2 := by
      linarith [mul_nonneg (show (0:ℤ) ≤ m - 21 by linarith) (show (0:ℤ) ≤ m + 23 by linarith)]
    have hb : 484 * (m+1)^2 ≤ (m+1)^2 * (m+1)^2 :=
      mul_le_mul_of_nonneg_right ha (sq_nonneg (m+1))
    linarith [hR, hA, q1, hb, sq_nonneg m, hm]

lemma big (m s a : ℤ) (hm : 129 ≤ m) (hs0 : 0 ≤ s) (hs : s ≤ 4*m) (ha : 3 ≤ a)
    (h1 : m*a = 2*s^2 - 1) (hdiv : (2*m*s^2 - 4*m*s + m + 1) ∣ (a-1)^2) : False := by
  have hm0 : (0:ℤ) ≤ m := by linarith
  have hma3 : m*3 ≤ m*a := mul_le_mul_of_nonneg_left ha hm0
  have hs3 : 3 ≤ s := by
    by_contra hlt
    have hlt' : s ≤ 2 := by omega
    have h4 : s^2 ≤ 4 := by
      linarith [mul_nonneg (show (0:ℤ) ≤ 2 - s by linarith) (show (0:ℤ) ≤ 2 + s by linarith)]
    linarith
  have hapos : (0:ℤ) < (a-1)^2 := pow_pos (by linarith) 2
  have hDle : 2*m*s^2 - 4*m*s + m + 1 ≤ (a-1)^2 := Int.le_of_dvd hapos hdiv
  have pa : (0:ℤ) ≤ (m-32)*s*(s-3) :=
    mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
  have pb : (0:ℤ) ≤ (m-96)*s := mul_nonneg (by linarith) (by linarith)
  have hDbig : 64*s^2 ≤ 2*m*s^2 - 4*m*s + m + 1 := by linarith [pa, pb]
  have h64 : m^2*(64*s^2) ≤ m^2*(2*m*s^2 - 4*m*s + m + 1) :=
    mul_le_mul_of_nonneg_left hDbig (sq_nonneg m)
  have hD2 : m^2*(2*m*s^2 - 4*m*s + m + 1) ≤ m^2*(a-1)^2 :=
    mul_le_mul_of_nonneg_left hDle (sq_nonneg m)
  have e : m^2*(a-1)^2 = (2*s^2-1-m)^2 := by
    linear_combination (m*a - m + (2*s^2 - 1 - m)) * h1
  have hpos : (0:ℤ) < (1+m)*(4*s^2-1-m) := mul_pos (by linarith) (by linarith)
  have hs2 : s^2 ≤ 16*m^2 := by
    linarith [mul_nonneg (show (0:ℤ) ≤ 4*m - s by linarith) (show (0:ℤ) ≤ 4*m + s by linarith)]
  have hs4 : s^2*s^2 ≤ s^2*(16*m^2) := mul_le_mul_of_nonneg_left hs2 (sq_nonneg s)
  linarith [h64, hD2, e, hpos, hs4]

def chk (m t : ℕ) : Bool :=
  decide (¬ ((2*((t+1)*(t+1)) - 1) % m = 0 ∧ 3 ≤ (2*((t+1)*(t+1)) - 1)/m ∧
    (((2*((t+1)*(t+1)) - 1)/m - 1)*((2*((t+1)*(t+1)) - 1)/m - 1)) % (m*(2*(t*t) - 1) + 1) = 0))

def allT (m : ℕ) : ℕ → Bool
  | 0 => true
  | n+1 => chk m n && allT m n

def allM : ℕ → Bool
  | 0 => true
  | n+1 => (decide (n < 21) || allT n (4*n)) && allM n

lemma allT_sound (m : ℕ) : ∀ n, allT m n = true → ∀ t, t < n → chk m t = true := by
  intro n
  induction n with
  | zero => intro _ t ht; omega
  | succ n ih =>
    intro h t ht
    have h2 : (chk m n && allT m n) = true := h
    rw [Bool.and_eq_true] at h2
    rcases Nat.lt_succ_iff_lt_or_eq.mp ht with h' | h'
    · exact ih h2.2 t h'
    · rw [h']; exact h2.1

lemma allM_sound : ∀ n, allM n = true → ∀ m, m < n → 21 ≤ m → allT m (4*m) = true := by
  intro n
  induction n with
  | zero => intro _ m hm _; omega
  | succ n ih =>
    intro h m hm h21
    have h2 : ((decide (n < 21) || allT n (4*n)) && allM n) = true := h
    rw [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h2
    rcases Nat.lt_succ_iff_lt_or_eq.mp hm with h' | h'
    · exact ih h2.2 m h' h21
    · subst h'
      rcases h2.1 with h3 | h3
      · omega
      · exact h3

lemma allM_ok : allM 129 = true := by decide +kernel

lemma core (a c m t : ℕ) (hm : 21 ≤ m) (ha : 3 ≤ a) (hc : c+1 = 2*t^2)
    (hma : m*a+1 = 2*(t+1)^2) (hdivZ : (m:ℤ)*(c:ℤ) + 1 ∣ ((a:ℤ)-1)^2) : False := by
  have hcz : (c:ℤ) + 1 = 2*(t:ℤ)^2 := by exact_mod_cast hc
  have hmaz : (m:ℤ)*a + 1 = 2*((t:ℤ)+1)^2 := by exact_mod_cast hma
  have hma' : (m:ℤ)*(a:ℤ) = 2*((t:ℤ)+1)^2 - 1 := by linarith
  have hdiv' : (2*(m:ℤ)*((t:ℤ)+1)^2 - 4*(m:ℤ)*((t:ℤ)+1) + (m:ℤ) + 1) ∣ ((a:ℤ)-1)^2 := by
    have e : 2*(m:ℤ)*((t:ℤ)+1)^2 - 4*(m:ℤ)*((t:ℤ)+1) + (m:ℤ) + 1 = (m:ℤ)*(c:ℤ) + 1 := by
      have hc2 : (c:ℤ) = 2*(t:ℤ)^2 - 1 := by linarith
      rw [hc2]; ring
    rw [e]; exact hdivZ
  have hs := key (m:ℤ) ((t:ℤ)+1) (a:ℤ) (by exact_mod_cast hm) hma' hdiv'
  by_cases hm' : m ≤ 128
  · have ht : t < 4*m := by omega
    have h1 := allT_sound m (4*m) (allM_sound 129 allM_ok m (by omega) hm) t ht
    unfold chk at h1
    have h2 := of_decide_eq_true h1
    have hsq1 : (t+1)^2 = (t+1)*(t+1) := pow_two _
    have hsq0 : t^2 = t*t := pow_two _
    have e1 : 2*((t+1)*(t+1)) - 1 = m*a := by omega
    have e2 : 2*(t*t) - 1 = c := by omega
    have hmpos : 0 < m := by omega
    have hdn : m*c+1 ∣ (a-1)*(a-1) := by
      have ha1 : ((a - 1 : ℕ) : ℤ) = (a:ℤ) - 1 := by omega
      have e3 : (((a-1)*(a-1) : ℕ) : ℤ) = ((a:ℤ)-1)^2 := by
        rw [Nat.cast_mul, ha1, pow_two]
      have e4 : ((m*c+1 : ℕ) : ℤ) = (m:ℤ)*(c:ℤ)+1 := by
        rw [Nat.cast_add, Nat.cast_mul, Nat.cast_one]
      apply Int.natCast_dvd_natCast.mp
      rw [e3, e4]; exact hdivZ
    refine h2 ⟨?_, ?_, ?_⟩
    · rw [e1]; exact Nat.mul_mod_right m a
    · rw [e1, Nat.mul_div_cancel_left a hmpos]; exact ha
    · rw [e1, e2, Nat.mul_div_cancel_left a hmpos]; exact Nat.mod_eq_zero_of_dvd hdn
  · exact big (m:ℤ) ((t:ℤ)+1) (a:ℤ) (by omega) (by omega) hs (by omega) hma' hdiv'

end CrystalFinite

theorem OMA.solution : OMA.R_Arxiv_1601_03081_crystals_components_unique_R1_H1_R1_H2_R1_H1_R1_H1_R1.H2 := by
  intro m t hm hmo hto htlt c b a hmb ha hac hcop1 hcop2 hprime hres hdiv hdiv2 hdiv3 hq hlow hfin
  have hc : c = 2*t^2 - 1 := rfl
  have hb : b = 2*(t+1)^2 - 1 := rfl
  have hmaeq : m*a = b := Nat.mul_div_cancel' hmb
  have ht1 : 1 ≤ t := by
    obtain ⟨k, hk⟩ := hto
    omega
  have hp0 : 0 < t^2 := pow_pos (by omega) 2
  have hp1 : 0 < (t+1)^2 := pow_pos (by omega) 2
  have hc' : c + 1 = 2*t^2 := by omega
  have hma : m*a + 1 = 2*(t+1)^2 := by omega
  exact CrystalFinite.core a c m t (by omega) ha hc' hma (by exact_mod_cast hdiv)
