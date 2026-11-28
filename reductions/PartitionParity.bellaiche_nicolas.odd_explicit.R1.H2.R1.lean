import OMAReductions.R_PartitionParity_bellaiche_nicolas_odd_explicit_R1
import Mathlib

/-!
Bellaïche and Nicolas, *Parité des coefficients de formes modulaires*, Theorem 6.
The transfer inequality (6.16) and Hecke support estimate (6.18) imply the requested
large-range bound. The proof chooses a dyadic nilpotence parameter and accounts for
the factorial and logarithmic losses, including the explicit numerical constant.
We use the Euler product Δ = q E(q)^24 in characteristic two, with E the Euler pentagonal series.
-/
namespace OMA.R_PartitionParity_bellaiche_nicolas_odd_explicit_R1_H2_R1

open Real
open scoped Classical


theorem parameter (L : ℝ) (hL : 24 < L) :
    ∃ e h : ℕ, h+1 = 2^e ∧ 4 ≤ h ∧ L ≤ 8*h ∧ 4*((h:ℝ)-1) < L := by
  obtain ⟨q,lo,hi⟩ := exists_nat_pow_near (x := L/8+1) (by linarith) (by norm_num : 1 < (2:ℝ))
  have choose (e : ℕ) (a : L/8+1 ≤ (2:ℝ)^e) (b : (2:ℝ)^e < L/4+2) :
      ∃ e h : ℕ, h+1 = 2^e ∧ 4 ≤ h ∧ L ≤ 8*h ∧ 4*((h:ℝ)-1) < L := by
    let h := 2^e - 1
    have eqn : h+1 = 2^e := by
      have : 0 < (2:ℕ)^e := by positivity
      dsimp [h]; omega
    have ec : (h:ℝ)+1 = (2:ℝ)^e := by exact_mod_cast eqn
    have : (3:ℝ) < h := by linarith
    exact ⟨e,h,eqn,by exact_mod_cast this,by linarith,by linarith⟩
  rcases lo.lt_or_eq with h|h
  · exact choose (q+1) hi.le (by rw [pow_succ]; linarith)
  · exact choose q h.ge (by linarith)

theorem factorial_scaled (m : ℕ) (hm : 1 ≤ m) :
    (m.factorial:ℝ) * exp ((m:ℝ)-1) ≤ sqrt m * (m:ℝ)^m := by
  have hs := Stirling.stirlingSeq'_antitone (Nat.zero_le (m-1))
  change Stirling.stirlingSeq ((m-1)+1) ≤ Stirling.stirlingSeq 1 at hs
  rw [Nat.sub_add_cancel hm, Stirling.stirlingSeq_one, Stirling.stirlingSeq] at hs
  have mp : (0:ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have two : 0 < sqrt (2:ℝ) := by positivity
  have hd : 0 < sqrt (2*(m:ℝ))*((m:ℝ)/exp 1)^m := by positivity
  have h := (div_le_div_iff₀ hd two).mp hs
  rw [sqrt_mul (by norm_num : (0:ℝ) ≤ 2), div_pow] at h
  rw [exp_sub, show (m:ℝ) = (m:ℝ)*1 by ring, Real.exp_nat_mul]
  field_simp [ne_of_gt (Real.exp_pos 1)] at h ⊢
  nlinarith only [h,two,mul_pos two (show 0 < exp 1 by positivity)]

theorem log_loss (m : ℕ) (hm : 1 ≤ m) (L : ℝ) (hL : 4*(m:ℝ) ≤ L) :
    (4*(m:ℝ))^m ≤ (L - log L)^m * (2*sqrt m) := by
  have mp : (0:ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have m1 : (1:ℝ) ≤ m := by exact_mod_cast hm
  let b : ℝ := 4*m
  have bp : 0 < b := by dsimp [b]; positivity
  have b1 : 1 ≤ b := by dsimp [b]; linarith
  have LL : 0 < L := lt_of_lt_of_le bp hL
  have hg : b - log b ≤ L - log L := by
    have hh := log_le_sub_one_of_pos (div_pos LL bp)
    rw [log_div LL.ne' bp.ne'] at hh
    have hq : L/b - 1 ≤ L-b := by
      rw [sub_le_iff_le_add,div_le_iff₀ bp]
      nlinarith [mul_nonneg (sub_nonneg.mpr hL) (sub_nonneg.mpr b1)]
    linarith
  let z := log b / b
  have z0 : 0 ≤ z := div_nonneg (log_nonneg b1) bp.le
  have zhalf : z ≤ 1/2 := by
    apply (div_le_iff₀ bp).mpr
    have hf : log 4 ≤ 2 := by
      rw [show (4:ℝ) = 2^2 by norm_num,log_pow]
      norm_num
      linarith [log_le_sub_one_of_pos (by norm_num : 0 < (2:ℝ))]
    dsimp [b]; rw [log_mul (by norm_num) mp.ne']
    linarith [log_le_sub_one_of_pos mp]
  have zp : 0 < 1-z := by linarith
  have lower : -(2*z) ≤ log (1-z) := by
    have hz := one_sub_inv_le_log_of_pos zp
    have hrec : (1-z)⁻¹ ≤ 1+2*z := by
      rw [inv_le_iff_one_le_mul₀ zp]
      nlinarith [mul_nonneg z0 (show 0 ≤ 1-2*z by linarith)]
    linarith
  have hz : z*b = log b := div_mul_cancel₀ _ bp.ne'
  have hl : -log b/2 ≤ (m:ℝ)*log (1-z) := by
    dsimp [b] at hz
    nlinarith [mul_le_mul_of_nonneg_left lower mp.le]
  have hpow := Real.exp_le_exp.mpr hl
  rw [Real.exp_nat_mul, Real.exp_log zp] at hpow
  have hs : exp (-log b/2) = (sqrt b)⁻¹ := by
    rw [neg_div,exp_neg,exp_half,exp_log bp]
  rw [hs] at hpow
  have hmul := (inv_le_iff_one_le_mul₀ (show 0 < sqrt b from sqrt_pos.mpr bp)).mp hpow
  have e : b * (1-z) = b-log b := by nlinarith
  have hbn : 0 ≤ b-log b := e ▸ mul_nonneg bp.le zp.le
  have ha := pow_le_pow_left₀ hbn hg m
  have hb := mul_le_mul_of_nonneg_left hmul (pow_nonneg bp.le m)
  rw [← e, mul_pow] at ha
  have sq : sqrt b = 2*sqrt m := by dsimp [b]; rw [sqrt_mul (by norm_num)]; norm_num
  rw [sq] at hb
  change b^m ≤ _
  nlinarith only [hb,mul_le_mul_of_nonneg_right ha (show 0 ≤ 2*sqrt (m:ℝ) by positivity)]

theorem combined_loss (m : ℕ) (hm : 1 ≤ m) (L : ℝ) (hL : 4*(m:ℝ) ≤ L) :
    ((4:ℝ)^m * m.factorial) * exp ((m:ℝ)-1) ≤
      2*((m:ℝ)+1)*(L-log L)^m := by
  have hf := factorial_scaled m hm
  have ht := log_loss m hm L hL
  rw [mul_pow] at ht
  have lpos : 0 < L := by
    have : (1:ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have nonneg : 0 ≤ L-log L := by linarith [log_le_sub_one_of_pos lpos]
  have sq := Real.sq_sqrt (Nat.cast_nonneg m)
  calc
    _ ≤ (4:ℝ)^m * (sqrt m * (m:ℝ)^m) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hf (by positivity)
    _ = sqrt m * ((4:ℝ)^m * (m:ℝ)^m) := by ring
    _ ≤ sqrt m * ((L-log L)^m * (2*sqrt m)) :=
          mul_le_mul_of_nonneg_left ht (sqrt_nonneg _)
    _ = 2*(m:ℝ)*(L-log L)^m := by linear_combination 2*(L-log L)^m*sq
    _ ≤ _ := by nlinarith [pow_nonneg nonneg m]

theorem numeric_transfer (x W A : ℝ) (m : ℕ) (hm : 1 ≤ m) (hx : 2 ≤ x)
    (hL : 4*(m:ℝ) ≤ log (log (8*x))) (lg : log (8*x) ≤ 1.001 * log x)
    (hA : 0 ≤ A)
    (transfer : ((m:ℝ)+1)*W ≤ A*sqrt (3*x))
    (support : 0.4*π^2*x*(log (log (8*x))-log (log (log (8*x))))^m ≤
      W*((m.factorial:ℝ)*4^(m+1))*log (8*x)) :
    0.28*exp ((m:ℝ)-1)*sqrt x / log x ≤ A := by
  let L := log (log (8*x))
  let F := (4:ℝ)^m * m.factorial
  let E := exp ((m:ℝ)-1)
  let Y := (L-log L)^m
  have hp : 0 < F := by dsimp [F]; positivity
  have he : 0 < E := exp_pos _
  have hx0 : 0 < x := by linarith
  have lx : 0 < log x := log_pos (by linarith)
  have lx8 : 0 < log (8*x) := log_pos (by linarith)
  have sqp : 0 < sqrt x := sqrt_pos.mpr hx0
  have c := combined_loss m hm L hL
  change F*E ≤ 2*((m:ℝ)+1)*Y at c
  change 0.4*π^2*x*Y ≤ _ at support
  have su : 0.4*π^2*x*Y ≤ W*F*4*log (8*x) := by
    convert support using 1; dsimp [F]; rw [pow_succ]; ring
  have prod : (0.4*π^2*sqrt x*E)*(F*sqrt x) ≤
        (8*sqrt 3*A*log (8*x))*(F*sqrt x) := by
    calc
      _ = (0.4*π^2*x)*(F*E) := by linear_combination 0.4*π^2*F*E * (Real.sq_sqrt hx0.le)
      _ ≤ (0.4*π^2*x)*(2*((m:ℝ)+1)*Y) := by gcongr
      _ = (2*((m:ℝ)+1))*(0.4*π^2*x*Y) := by ring
      _ ≤ (2*((m:ℝ)+1))*(W*F*4*log (8*x)) := by gcongr
      _ = (2*F*4*log (8*x))*(((m:ℝ)+1)*W) := by ring
      _ ≤ (2*F*4*log (8*x))*(A*sqrt (3*x)) := by gcongr
      _ = _ := by rw [sqrt_mul (by norm_num : (0:ℝ) ≤ 3)]; ring
  have clean := le_of_mul_le_mul_right prod (mul_pos hp sqp)
  have cc : 0.28*(8*sqrt 3*1.001) ≤ 0.4*π^2 := by
    have hs : sqrt 3 ≤ 1.74 := (sqrt_le_left (by norm_num)).mpr (by norm_num)
    nlinarith [Real.pi_gt_d4, sq_nonneg (π-3.1415)]
  apply (div_le_iff₀ lx).mpr
  change 0.28*E*sqrt x ≤ A*log x
  apply le_of_mul_le_mul_left (a := 8*sqrt 3*1.001) _ (by positivity)
  calc
    _ = (0.28*(8*sqrt 3*1.001))*(sqrt x*E) := by ring
    _ ≤ 0.4*π^2*(sqrt x*E) := by gcongr
    _ = _ := (mul_assoc _ _ _).symm
    _ ≤ 8*sqrt 3*A*log (8*x) := clean
    _ ≤ 8*sqrt 3*A*(1.001*log x) := by gcongr
    _ = _ := by ring

/-- Comparison of odd partition counts with the support of a power of Δ, (6.16). -/
def H1 : Prop := ∀ x : ℝ, 2 ≤ x → exp (exp 24) / 8 < x →
  let L := log (log (8*x))
  ∀ e h : ℕ, h+1 = 2^e → 4 ≤ h → L ≤ 8*(h:ℝ) → 4*((h:ℝ)-1) < L →
    let k := (4^(e+1)-1)/3
    let Δ : PowerSeries (ZMod 2) := PowerSeries.X * PowerSeries.pentagonalSeries (ZMod 2) ^ 24
    let W := ((Finset.range (⌊8*x⌋₊+1)).filter fun n => PowerSeries.coeff n (Δ^k) ≠ 0).card
    (h:ℝ)*W ≤ ({n : ℕ | n ≤ x ∧ Odd (Nat.partitionNumber n)}.ncard:ℝ) * sqrt (3*x)

/-- Explicit lower bound for the support of the chosen mod-2 form, (6.18). -/
def H2 : Prop := ∀ x : ℝ, 2 ≤ x → exp (exp 24) / 8 < x →
  let L := log (log (8*x))
  ∀ e h : ℕ, h+1 = 2^e → 4 ≤ h → L ≤ 8*(h:ℝ) → 4*((h:ℝ)-1) < L →
    let k := (4^(e+1)-1)/3
    let Δ : PowerSeries (ZMod 2) := PowerSeries.X * PowerSeries.pentagonalSeries (ZMod 2) ^ 24
    let W := ((Finset.range (⌊8*x⌋₊+1)).filter fun n => PowerSeries.coeff n (Δ^k) ≠ 0).card
    let m := h-1
    0.4*π^2*x*(L-log L)^m ≤ (W:ℝ)*((m.factorial:ℝ)*4^(m+1))*log (8*x)

theorem main : H1 → H2 → OMA.R_PartitionParity_bellaiche_nicolas_odd_explicit_R1.H2 := by
  intro transfer support x hx hlarge
  have h8 : exp (exp 24) < 8*x := by linarith
  have lx8 : exp 24 < log (8*x) := Real.lt_log_iff_exp_lt (by linarith) |>.mpr h8
  have hL : 24 < log (log (8*x)) := (Real.lt_log_iff_exp_lt (lt_trans (exp_pos _) lx8)).mpr lx8
  obtain ⟨e,h,he,hh,hlo,hhi⟩ := parameter _ hL
  have hx8 : log x ≤ log (8*x) := log_le_log (by linarith) (by linarith)
  have lpos : 0 < log x := log_pos (by linarith)
  have ratio : log (8*x) ≤ 1.001 * log x := by
    have hnum : (8000:ℝ) ≤ exp 24 := by
      calc (8000:ℝ) ≤ 2^(24:ℕ) := by norm_num
           _ ≤ (exp 1)^(24:ℕ) := pow_le_pow_left₀ (by norm_num) (by linarith [Real.exp_one_gt_d9]) _
           _ = exp 24 := by rw [← Real.exp_nat_mul]; norm_num
    rw [log_mul (by norm_num) (by linarith : x ≠ 0)] at lx8 ⊢
    linarith [log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 8)]
  refine ⟨h, (log_le_log lpos hx8).trans hlo, ?_⟩
  have one : 1 ≤ h-1 := by omega
  have heq : ((h-1:ℕ):ℝ) = (h:ℝ)-1 := by rw [Nat.cast_sub (by omega : 1 ≤ h)]; norm_num
  have hval : ((h-1:ℕ):ℝ)+1 = h := by linarith
  have shift : ((h-1:ℕ):ℝ)-1 = (h:ℝ)-2 := by linarith
  have t := transfer x hx hlarge e h he hh hlo hhi
  have s := support x hx hlarge e h he hh hlo hhi
  have v := numeric_transfer x _ _ (h-1) one hx (by rw [heq]; exact hhi.le) ratio
    (Nat.cast_nonneg _) (by rw [hval]; exact t) s
  simpa only [shift] using v

end OMA.R_PartitionParity_bellaiche_nicolas_odd_explicit_R1_H2_R1
