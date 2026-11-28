import OMAStatements.S_oeis_a105565
import Mathlib

open OMA.S_oeis_a105565
open Finset Real

private theorem fib_not_ten_pow {n : ℕ} (hn : 0 < n) (k : ℕ) :
    Nat.fib k ≠ 10^n := by
  intro he
  have hd : 10 ∣ Nat.fib k := by rw [he]; exact dvd_pow_self 10 hn.ne'
  have hg : 10 ∣ Nat.fib (Nat.gcd 15 k) := by
    rw [Nat.fib_gcd]
    exact Nat.dvd_gcd (by decide) hd
  have hle : Nat.gcd 15 k ≤ 15 := Nat.gcd_le_left k (by decide)
  have h15 : Nat.gcd 15 k = 15 := by
    by_contra h
    have hp : 0 < Nat.gcd 15 k := Nat.gcd_pos_of_pos_left k (by decide)
    have hh : ∀ j : Fin 15, 0 < j.val → ¬10 ∣ Nat.fib j.val := by decide +kernel
    exact hh ⟨Nat.gcd 15 k, by omega⟩ hp hg
  have hdiv : 15 ∣ k := by rw [← h15]; exact Nat.gcd_dvd_right 15 k
  have h61 : 61 ∣ Nat.fib k := dvd_trans (by decide : 61 ∣ Nat.fib 15) (Nat.fib_dvd 15 k hdiv)
  rw [he] at h61
  exact (by decide : ¬ 61 ∣ 10) ((by norm_num : Nat.Prime 61).dvd_of_dvd_pow h61)

private theorem fib_close (k : ℕ) :
    |goldenRatio^k / √5 - (Nat.fib k : ℝ)| < 1 := by
  have hs : 1 < √(5:ℝ) := by
    nlinarith [Real.sq_sqrt (by norm_num : 0 ≤ (5:ℝ)), Real.sqrt_nonneg (5:ℝ)]
  have hc : |goldenConj| ≤ 1 := by
    rw [abs_of_neg Real.goldenConj_neg]
    linarith [Real.neg_one_lt_goldenConj]
  have hck : |goldenConj|^k ≤ 1 := pow_le_one₀ (abs_nonneg _) hc
  rw [Real.coe_fib_eq, ← sub_div, sub_sub_cancel, abs_div, abs_pow, abs_of_pos (by linarith : 0 < √(5:ℝ))]
  exact (div_lt_one (by linarith)).mpr (hck.trans_lt hs)

private noncomputable def R : ℝ := log 10 / log goldenRatio
private noncomputable def C : ℝ := log 5 / (2 * log goldenRatio)
private noncomputable def L (n : ℕ) : ℝ := (n : ℝ)*R+C

private theorem log_phi_pos : 0 < log goldenRatio :=
  log_pos Real.one_lt_goldenRatio

private theorem ratio_bounds : 4 < R ∧ R < 5 ∧ 0 < C ∧ C < 3 := by
  have hs : 2 < √(5:ℝ) := by
    nlinarith [Real.sq_sqrt (by norm_num : 0 ≤ (5:ℝ)), Real.sqrt_nonneg (5:ℝ)]
  have hphi : (3:ℝ)/2 < goldenRatio := by unfold Real.goldenRatio; linarith
  have h2 := Real.goldenRatio_sq
  have h4 : goldenRatio^4 = 3*goldenRatio+2 := by linear_combination (goldenRatio^2+goldenRatio+2)*h2
  have h5 : goldenRatio^5 = 5*goldenRatio+3 := by linear_combination (goldenRatio^3+goldenRatio^2+2*goldenRatio+3)*h2
  have h6 : goldenRatio^6 = 8*goldenRatio+5 := by linear_combination (goldenRatio^4+goldenRatio^3+2*goldenRatio^2+3*goldenRatio+5)*h2
  have hlo : goldenRatio^4 < 10 := by rw [h4]; linarith [Real.goldenRatio_lt_two]
  have hhi : (10:ℝ) < goldenRatio^5 := by rw [h5]; linarith
  have hc : (5:ℝ) < goldenRatio^6 := by rw [h6]; linarith
  have ll := Real.log_lt_log (pow_pos Real.goldenRatio_pos 4) hlo
  have lh := Real.log_lt_log (by norm_num : (0:ℝ)<10) hhi
  have lc := Real.log_lt_log (by norm_num : (0:ℝ)<5) hc
  rw [Real.log_pow] at ll lh lc
  constructor
  · exact (lt_div_iff₀ log_phi_pos).mpr (by norm_num at ll ⊢; linarith)
  constructor
  · exact (div_lt_iff₀ log_phi_pos).mpr (by norm_num at lh ⊢; linarith)
  have hd : 0 < 2 * log goldenRatio := mul_pos (by norm_num) log_phi_pos
  constructor
  · exact div_pos (log_pos (by norm_num)) hd
  · exact (div_lt_iff₀ hd).mpr (by norm_num at lc ⊢; linarith)

private theorem threshold {n : ℕ} (hn : 0 < n) (k : ℕ) :
    (Nat.fib k < 10^n ∧ (k : ℝ) < L n) ∨ (10^n ≤ Nat.fib k ∧ L n < (k : ℝ)) := by
  have hw := fib_close k
  rw [abs_lt] at hw
  have hs : 0 < √(5:ℝ) := by positivity
  have hlog : log ((10:ℝ)^n * √5) = L n * log goldenRatio := by
    rw [Real.log_mul (by positivity) hs.ne', Real.log_pow, Real.log_sqrt (by norm_num)]
    unfold L R C
    field_simp [log_phi_pos.ne']
  have hklog := Real.log_pow goldenRatio k
  by_cases hf : Nat.fib k < 10^n
  · have hb : (Nat.fib k : ℝ)+1 ≤ (10:ℝ)^n := by exact_mod_cast (show Nat.fib k+1 ≤ 10^n by omega)
    have hb' : goldenRatio^k < (10:ℝ)^n * √5 :=
      (div_lt_iff₀ hs).mp (by linarith)
    have h := Real.log_lt_log (pow_pos Real.goldenRatio_pos k) hb'
    rw [hklog, hlog] at h
    exact Or.inl ⟨hf, lt_of_mul_lt_mul_right h log_phi_pos.le⟩
  · have hfn : 10^n < Nat.fib k := lt_of_le_of_ne (by omega) (fib_not_ten_pow hn k).symm
    have hb : (10:ℝ)^n+1 ≤ (Nat.fib k : ℝ) := by exact_mod_cast (show 10^n+1 ≤ Nat.fib k by omega)
    have hb' : (10:ℝ)^n * √5 < goldenRatio^k :=
      (lt_div_iff₀ hs).mp (by linarith)
    have h := Real.log_lt_log (by positivity : 0 < (10:ℝ)^n * √5) hb'
    rw [hklog, hlog] at h
    exact Or.inr ⟨by omega, lt_of_mul_lt_mul_right h log_phi_pos.le⟩

private theorem bound_fib {n : ℕ} (hn : 0 < n) : 10^n ≤ Nat.fib (5*n+3) := by
  rcases threshold hn (5*n+3) with ⟨_,h⟩ | ⟨h,_⟩
  · have hb := ratio_bounds
    unfold L at h
    push_cast at h
    nlinarith only [h, hb.2.1, hb.2.2.2, Nat.cast_nonneg (α := ℝ) n]
  · exact h

private theorem exists_cutoff (n : ℕ) : ∃ k : ℕ, 10^n ≤ Nat.fib k := by
  by_cases hn : n = 0
  · subst n
    exact ⟨1, by decide⟩
  · exact ⟨5*n+3, bound_fib (by omega)⟩

private noncomputable def T (n : ℕ) : ℕ := Nat.find (exists_cutoff n)

private theorem cutoff (n k : ℕ) : Nat.fib k < 10^n ↔ k < T n := by
  constructor
  · intro h
    by_contra! hh
    exact (not_le_of_gt h) ((Nat.find_spec (exists_cutoff n)).trans (Nat.fib_mono hh))
  · intro h
    exact Nat.lt_of_not_ge (Nat.find_min (exists_cutoff n) h)

private theorem cutoff_bounds {n : ℕ} (hn : 0 < n) :
    (T n : ℝ)-1 < L n ∧ L n < T n := by
  have ht : 0 < T n := (cutoff n 0).mp (by simp)
  have hlo := (cutoff n (T n - 1)).mpr (by omega)
  have hhi := Nat.find_spec (exists_cutoff n)
  constructor
  · rcases threshold hn (T n - 1) with ⟨_,h⟩ | ⟨h,_⟩
    · simpa [Nat.cast_sub (by omega : 1 ≤ T n)] using h
    · omega
  · rcases threshold hn (T n) with ⟨h,_⟩ | ⟨_,h⟩
    · exact False.elim (not_lt_of_ge hhi h)
    · exact h

private theorem count_digits {n : ℕ} (hn : 0 < n) :
    a n = if T n - T (n-1) = 5 then 1 else 0 := by
  unfold a
  rw [if_pos hn]
  dsimp
  have hu : T n ≤ 5*n+3 := Nat.find_min' (exists_cutoff n) (bound_fib hn)
  have hh : (Finset.range (5*n+10)).filter
        (fun k => 10^(n-1) ≤ Nat.fib k ∧ Nat.fib k < 10^n) =
      Finset.Ico (T (n-1)) (T n) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico, cutoff, ← not_lt]
    omega
  rw [hh, Nat.card_Ico]

private theorem cutoff_step {n : ℕ} (hn : 0 < n) :
    T (n+1) = T n+4 ∨ T (n+1) = T n+5 := by
  have b := cutoff_bounds hn
  have c := cutoff_bounds (show 0 < n+1 by omega)
  have h : L (n+1) = L n+R := by unfold L; push_cast; ring
  have bR := ratio_bounds
  rw [h] at c
  have hlow : (T n : ℝ)+3 < T (n+1) := by linarith [b.1,c.2,bR.1]
  have hhigh : (T (n+1) : ℝ) < T n+6 := by linarith [b.2,c.1,bR.2.1]
  have hl : T n+3 < T (n+1) := by exact_mod_cast hlow
  have hh : T (n+1) < T n+6 := by exact_mod_cast hhigh
  omega

private theorem base_cutoff : T 1 = 7 := by
  have h₁ : 6 < T 1 := (cutoff 1 6).mp (by decide)
  have h₂ : T 1 ≤ 7 := Nat.find_min' (exists_cutoff 1) (by decide : 10^1 ≤ Nat.fib 7)
  omega

private theorem sum_count (n : ℕ) (hn : 1 ≤ n) : s n = (T n : ℝ)-4*n-3 := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases h0 : n = 0
    · subst n
      change s 1 = _
      unfold s
      rw [show Finset.Icc (1:ℕ) 1 = {1} by simp, Finset.sum_singleton]
      norm_num [base_cutoff, show a 1 = 0 by decide +kernel]
    · unfold s
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n+1)]
      change s n + (a (n+1) : ℝ) = _
      rw [ih (by omega), count_digits (by omega : 0 < n+1), Nat.add_sub_cancel]
      rcases cutoff_step (by omega : 0 < n) with h | h
      · rw [h, if_neg (by omega)]
        push_cast
        ring
      · rw [h, if_pos (by omega)]
        push_cast
        ring

theorem OMA.solution : type_of% @OMA.S_oeis_a105565.main := by
  intro n hn
  rw [sum_count n hn]
  have h := cutoff_bounds (show 0 < n by omega)
  change C - 1 - 2 < (T n : ℝ)-4*n-3-(R-4)*n ∧
    (T n : ℝ)-4*n-3-(R-4)*n < C-1-1
  unfold L at h
  constructor <;> linarith [h.1,h.2]