import OMAReductions.R_Arxiv_1601_03081_crystals_components_unique_R1_H2_R1_H2_R1_H1_R1
import Mathlib

-- Step Arxiv.1601.03081.crystals_components_unique.R1.H2.R1.H2.R1.H1.R1.H1: hypothesis H1 of reduction Arxiv.1601.03081.crystals_components_unique.R1.H2.R1.H2.R1.H1.R1
-- Credit: @sebastianbachmaier
-- H1 := ∀ g y z d : ℕ,     1 < g → 33 ≤ y → Odd g → Odd y → Odd z → g*y ≤ z →     (g+1)*(y*z+1) ∣ (g+y*z)^2 →     0 < d → d < 2*(y-1) → d % 2 = 0 →     (g+1 ∣ ((y+1)*(d+(y-1)*y*(1+2*y)))^2) →     (g*y+1 ∣ ((y+1)*(d+(y-1)*(y+2)))^2) →     (∀ p : ℕ, p.Prime → p ∣ g*y*z → p % 8 = 1 ∨ p % 8 = 7) →     ((y : ℤ) ∣ ((d : ℤ)-3)^2-8) → 66 ≤ d →     (g*y+z)^2 = 4*((g*y+1)*(z+1)) → g = z

namespace CrystalMirror

lemma step1 (m t a w : ℤ) (h1 : m*a = 2*t^2 - 1)
    (hw : (a-1)^2 = (2*m*t^2 + 4*m*t + m + 1) * w) :
    ∃ j : ℤ, -(8*m*t*(m-1)^2) - (m+1)^4 + 8*m*(m+1) = (2*m*t^2 + 4*m*t + m + 1) * j :=
  ⟨8*m - m^4*w + (2*m*t^2 + 4*m*t + m + 1) + 2*(-(4*m*t) - (m+1)^2), by
    linear_combination (-m^4) * hw
      + m*(m^2*(a-1) + (2*m*t^2 + 4*m*t + m + 1) + (-(4*m*t) - (m+1)^2)) * h1⟩

lemma mirror (m t a : ℤ) (hm : 33 ≤ m) (ht : 1 ≤ t) (ha : 2 ≤ a) (h1 : m*a = 2*t^2 - 1)
    (hdiv : (2*m*t^2 + 4*m*t + m + 1) ∣ (a-1)^2) :
    (∃ r : ℤ, 0 < r ∧ r < m ∧ m ≤ 290 ∧
        2*r*(r + 4*m^2 + 2) + 2*m + 5 = m^3 + 4*m^2 + 16*r*m) ∨
      (t ≤ 5*m ∧ m ≤ 49) := by
  have hdiv' := hdiv
  obtain ⟨w, hw⟩ := hdiv
  obtain ⟨j, hR⟩ := step1 m t a w h1 hw
  have hm0 : (0:ℤ) ≤ m := by linarith
  have hm1 : (0:ℤ) ≤ m - 1 := by linarith
  have ht0 : (0:ℤ) ≤ t := by linarith
  have hmt : (0:ℤ) ≤ m*t := mul_nonneg hm0 ht0
  have hmtt : (0:ℤ) ≤ m*t*t := mul_nonneg hmt ht0
  have hD : (0:ℤ) < 2*m*t^2 + 4*m*t + m + 1 := by linarith [hmtt, hmt]
  obtain ⟨k, hk⟩ : ∃ k : ℤ, j + 1 = m * k :=
    ⟨(-(8*t*(m-1)^2) + 8*(m+1) - (m^3+4*m^2+6*m+4)) - j*(2*t^2 + 4*t + 1), by
      linear_combination (-1 : ℤ) * hR⟩
  rcases lt_trichotomy k 0 with hk0 | hk0 | hk0
  · have hk1 : k ≤ -1 := by omega
    have hmk : m * k ≤ m * (-1) := mul_le_mul_of_nonneg_left hk1 hm0
    have hj : j ≤ -(m+1) := by linarith
    have hC : (2*m*t^2 + 4*m*t + m + 1) * j ≤ (2*m*t^2 + 4*m*t + m + 1) * (-(m+1)) :=
      mul_le_mul_of_nonneg_left hj hD.le
    have htle : t ≤ 5*m := by
      by_contra hcon
      have hcon' : 5*m+1 ≤ t := by omega
      have q1 : (0:ℤ) ≤ m*t*((m+1)*(t-(5*m+1))) :=
        mul_nonneg hmt (mul_nonneg (by linarith) (by linarith))
      have q2 : (0:ℤ) ≤ m*(m^2+16*m-1)*(t-(5*m+1)) :=
        mul_nonneg (mul_nonneg hm0 (by linarith [sq_nonneg m])) (by linarith)
      linarith [hR, hC, q1, q2, pow_nonneg hm0 4, pow_nonneg hm0 3, sq_nonneg m, hm]
    have hm49 : m ≤ 49 := by
      by_contra hcon
      have hm50 : 50 ≤ m := by omega
      have hapos : (0:ℤ) < (a-1)^2 := pow_pos (by linarith) 2
      have hDle : 2*m*t^2 + 4*m*t + m + 1 ≤ (a-1)^2 := Int.le_of_dvd hapos hdiv'
      have hD2 : m^2*(2*m*t^2 + 4*m*t + m + 1) ≤ m^2*(a-1)^2 :=
        mul_le_mul_of_nonneg_left hDle (sq_nonneg m)
      have e : m^2*(a-1)^2 = (2*t^2-1-m)^2 := by
        linear_combination (m*a - m + (2*t^2 - 1 - m)) * h1
      have hma1 : m*1 ≤ m*a := mul_le_mul_of_nonneg_left (by linarith) hm0
      have hpos : (0:ℤ) < (1+m)*(4*t^2-1-m) := mul_pos (by linarith) (by linarith)
      have ht2 : t^2 ≤ 25*m^2 := by
        linarith [mul_nonneg (show (0:ℤ) ≤ 5*m - t by linarith) (show (0:ℤ) ≤ 5*m + t by linarith)]
      have ht4 : t^2*t^2 ≤ t^2*(25*m^2) := mul_le_mul_of_nonneg_left ht2 (sq_nonneg t)
      have q3 : (0:ℤ) ≤ (m-50)*(m^2*t^2) :=
        mul_nonneg (by linarith) (mul_nonneg (sq_nonneg m) (sq_nonneg t))
      have q4 : (0:ℤ) ≤ m^2*(m*t) := mul_nonneg (sq_nonneg m) hmt
      linarith [hD2, e, hpos, ht4, q3, q4, pow_nonneg hm0 3, sq_nonneg m]
    exact Or.inr ⟨htle, hm49⟩
  · subst hk0
    have hj : j = -1 := by linarith
    have hRD : -(8*m*t*(m-1)^2) - (m+1)^4 + 8*m*(m+1) + (2*m*t^2 + 4*m*t + m + 1) = 0 := by
      rw [hj] at hR
      linarith
    obtain ⟨r, hr⟩ : ∃ r : ℤ, r = t - 4*(m-1)^2 + 2 := ⟨_, rfl⟩
    have heq0 : m*(2*r*t - (m+1)*(m^2+3*m-5)) = 0 := by
      rw [hr]
      linear_combination hRD
    have hrt : 2*r*t = (m+1)*(m^2+3*m-5) := by
      rcases mul_eq_zero.mp heq0 with h | h
      · linarith
      · linarith
    have hP : (0:ℤ) < (m+1)*(m^2+3*m-5) := mul_pos (by linarith) (by linarith [sq_nonneg m])
    have hrpos : 0 < r := by
      by_contra hcon
      have h' : t*r ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht0 (by linarith)
      linarith [hrt, hP, h']
    have htr : t = r + 4*(m-1)^2 - 2 := by linarith [hr]
    have heq : 2*r*(r + 4*m^2 + 2) + 2*m + 5 = m^3 + 4*m^2 + 16*r*m := by
      linear_combination hrt - (2*r)*htr
    have hrm : r < m := by
      by_contra hcon
      have q6 : (0:ℤ) ≤ m*(m-2)*(r-m) :=
        mul_nonneg (mul_nonneg hm0 (by linarith)) (by linarith)
      have q7 : (0:ℤ) ≤ m^2*(7*m-20) := mul_nonneg (sq_nonneg m) (by linarith)
      linarith [heq, q6, q7, sq_nonneg r, hrpos, hm]
    have hm290 : m ≤ 290 := by
      by_contra hcon
      have hm291 : 291 ≤ m := by omega
      have hc0 : (0:ℤ) ≤ 32*m^2 - 64*m + 16 := by
        linarith [mul_nonneg hm0 (show (0:ℤ) ≤ m - 2 by linarith)]
      rcases le_or_gt (8*r) (m+5) with h8 | h8
      · have hA := mul_le_mul h8
          (show 8*r + (32*m^2 - 64*m + 16) ≤ (m+5) + (32*m^2 - 64*m + 16) by linarith)
          (by linarith) (by linarith)
        linarith [hA, heq, sq_nonneg m, hm291]
      · have h8' : m + 6 ≤ 8*r := by omega
        have hA := mul_le_mul h8'
          (show (m+6) + (32*m^2 - 64*m + 16) ≤ 8*r + (32*m^2 - 64*m + 16) by linarith)
          (by linarith) (by linarith)
        linarith [hA, heq,
          mul_nonneg (show (0:ℤ) ≤ m - 291 by linarith) (show (0:ℤ) ≤ m - 1 by linarith)]
    exact Or.inl ⟨r, hrpos, hrm, hm290, heq⟩
  · exfalso
    have hk1 : (1:ℤ) ≤ k := by omega
    have hmk : m * 1 ≤ m * k := mul_le_mul_of_nonneg_left hk1 hm0
    have hj : 0 ≤ j := by linarith
    have hDj : (0:ℤ) ≤ (2*m*t^2 + 4*m*t + m + 1) * j := mul_nonneg hD.le hj
    have q8 : (0:ℤ) ≤ m*t*(m-1)^2 := mul_nonneg hmt (sq_nonneg (m-1))
    have ha484 : (484:ℤ) ≤ (m+1)^2 := by
      linarith [mul_nonneg (show (0:ℤ) ≤ m - 21 by linarith) (show (0:ℤ) ≤ m + 23 by linarith)]
    have hb484 : 484 * (m+1)^2 ≤ (m+1)^2 * (m+1)^2 :=
      mul_le_mul_of_nonneg_right ha484 (sq_nonneg (m+1))
    linarith [hR, hDj, q8, hb484, sq_nonneg m, hm]

def allBelow (f : ℕ → Bool) : ℕ → Bool
  | 0 => true
  | n+1 => f n && allBelow f n

lemma allBelow_sound (f : ℕ → Bool) :
    ∀ n, allBelow f n = true → ∀ t, t < n → f t = true := by
  intro n
  induction n with
  | zero => intro _ t ht; omega
  | succ n ih =>
    intro h t ht
    have h2 : (f n && allBelow f n) = true := h
    rw [Bool.and_eq_true] at h2
    rcases Nat.lt_succ_iff_lt_or_eq.mp ht with h' | h'
    · exact ih h2.2 t h'
    · rw [h']; exact h2.1

def chkR (m r : ℕ) : Bool :=
  decide (2*r*(r + 4*(m*m) + 2) + 2*m + 5 ≠ m*m*m + 4*(m*m) + 16*r*m)

def chkD (m t : ℕ) : Bool :=
  decide (¬ ((2*(t*t) - 1) % m = 0 ∧ 2 ≤ (2*(t*t) - 1)/m ∧
    (((2*(t*t) - 1)/m - 1)*((2*(t*t) - 1)/m - 1)) % (m*(2*((t+1)*(t+1)) - 1) + 1) = 0))

lemma checkR :
    allBelow (fun m => decide (m < 33) || allBelow (fun r => chkR m r) m) 291 = true := by
  decide +kernel

lemma checkD :
    allBelow (fun m => decide (m < 33) || allBelow (fun t => chkD m t) (5*m+1)) 50 = true := by
  decide +kernel

end CrystalMirror

theorem OMA.solution : OMA.R_Arxiv_1601_03081_crystals_components_unique_R1_H2_R1_H2_R1_H1_R1.H1 := by
  intro g y z d hg hy hgo hyo hzo hle hdvd hd0 hd1 hd2 hgd hgd' hprime hyd hd66 hq
  exfalso
  obtain ⟨t, ht1, ht2⟩ :=
    OMA.R_Arxiv_1601_03081_crystals_components_unique_R1_H2_R1_H2_R1_H1_R1.consecutive_squares
      (hgo.mul hyo) hzo hle hq
  have hdz :=
    OMA.R_Arxiv_1601_03081_crystals_components_unique_R1_H2_R1_H2_R1_H1_R1.largeComponent_dvd
      g (y*z) hdvd
  have ht0 : 0 < t := by
    by_contra h0
    have h00 : t = 0 := by omega
    rw [h00] at ht1
    norm_num at ht1
  have h1z : (g:ℤ)*(y:ℤ) + 1 = 2*(t:ℤ)^2 := by exact_mod_cast ht1
  have h1 : (y:ℤ)*(g:ℤ) = 2*(t:ℤ)^2 - 1 := by linarith
  have h2z : (z:ℤ) + 1 = 2*((t:ℤ)+1)^2 := by exact_mod_cast ht2
  have hz : (z:ℤ) = 2*((t:ℤ)+1)^2 - 1 := by linarith
  have hdivZ : (y:ℤ)*(z:ℤ) + 1 ∣ ((g:ℤ)-1)^2 := by exact_mod_cast hdz
  have hdiv' : (2*(y:ℤ)*(t:ℤ)^2 + 4*(y:ℤ)*(t:ℤ) + (y:ℤ) + 1) ∣ ((g:ℤ)-1)^2 := by
    have e : 2*(y:ℤ)*(t:ℤ)^2 + 4*(y:ℤ)*(t:ℤ) + (y:ℤ) + 1 = (y:ℤ)*(z:ℤ) + 1 := by
      rw [hz]; ring
    rw [e]; exact hdivZ
  rcases CrystalMirror.mirror (y:ℤ) (t:ℤ) (g:ℤ) (by omega) (by omega) (by omega) h1 hdiv' with
    ⟨r, hr0, hrm, hm290, heq⟩ | ⟨ht5, hm49⟩
  · lift r to ℕ using hr0.le
    have hrm' : r < y := by exact_mod_cast hrm
    have heq' : 2*r*(r + 4*(y*y) + 2) + 2*y + 5 = y*y*y + 4*(y*y) + 16*r*y := by
      have h : 2*(r:ℤ)*((r:ℤ) + 4*((y:ℤ)*(y:ℤ)) + 2) + 2*(y:ℤ) + 5
          = (y:ℤ)*(y:ℤ)*(y:ℤ) + 4*((y:ℤ)*(y:ℤ)) + 16*(r:ℤ)*(y:ℤ) := by
        linear_combination heq
      exact_mod_cast h
    have hc : (decide (y < 33) || CrystalMirror.allBelow (fun r => CrystalMirror.chkR y r) y) = true :=
      CrystalMirror.allBelow_sound _ 291 CrystalMirror.checkR y (by omega)
    rw [Bool.or_eq_true, decide_eq_true_eq] at hc
    rcases hc with hc | hc
    · omega
    · have hc2 : CrystalMirror.chkR y r = true := CrystalMirror.allBelow_sound _ y hc r hrm'
      unfold CrystalMirror.chkR at hc2
      exact (of_decide_eq_true hc2) heq'
  · have ht5' : t < 5*y+1 := by omega
    have hc : (decide (y < 33) || CrystalMirror.allBelow (fun t => CrystalMirror.chkD y t) (5*y+1)) = true :=
      CrystalMirror.allBelow_sound _ 50 CrystalMirror.checkD y (by omega)
    rw [Bool.or_eq_true, decide_eq_true_eq] at hc
    rcases hc with hc | hc
    · omega
    · have hc2 : CrystalMirror.chkD y t = true :=
        CrystalMirror.allBelow_sound _ (5*y+1) hc t ht5'
      unfold CrystalMirror.chkD at hc2
      have h2 := of_decide_eq_true hc2
      have hsq1 : (t+1)^2 = (t+1)*(t+1) := pow_two _
      have hsq0 : t^2 = t*t := pow_two _
      have hcomm : g*y = y*g := Nat.mul_comm g y
      have e1 : 2*(t*t) - 1 = y*g := by omega
      have e2 : 2*((t+1)*(t+1)) - 1 = z := by omega
      have hypos : 0 < y := by omega
      have hdn : y*z+1 ∣ (g-1)*(g-1) := by
        have ha1 : ((g - 1 : ℕ) : ℤ) = (g:ℤ) - 1 := by omega
        have e3 : (((g-1)*(g-1) : ℕ) : ℤ) = ((g:ℤ)-1)^2 := by
          rw [Nat.cast_mul, ha1, pow_two]
        have e4 : ((y*z+1 : ℕ) : ℤ) = (y:ℤ)*(z:ℤ)+1 := by
          rw [Nat.cast_add, Nat.cast_mul, Nat.cast_one]
        apply Int.natCast_dvd_natCast.mp
        rw [e3, e4]; exact hdivZ
      refine h2 ⟨?_, ?_, ?_⟩
      · rw [e1]; exact Nat.mul_mod_right y g
      · rw [e1, Nat.mul_div_cancel_left g hypos]; omega
      · rw [e1, e2, Nat.mul_div_cancel_left g hypos]; exact Nat.mod_eq_zero_of_dvd hdn
