import OMAStatements.S_oeis_a241622
import Mathlib

namespace OMA.Windows241622

open OMA.S_oeis_a241622 Finset PowerSeries

private abbrev Word (n k : ℕ) := Fin k → Fin (n+1)

/-- Include the last two entries of the current prefix when checking a continuation. -/
private def allowed (n : ℕ) : (k b c : ℕ) → Word n k → Prop
  | 0, _, _, _ => True
  | k+1, b, c, x => b+c+(x 0).val ≤ n ∧ allowed n k c (x 0).val (fun i => x i.succ)

private abbrev Cont (n k b c : ℕ) := {x : Word n k // allowed n k b c x}

private noncomputable instance (n k b c : ℕ) : Fintype (Cont n k b c) := Fintype.ofFinite _

private def split (n k b c : ℕ) (h : b+c ≤ n) :
    Cont n (k+1) b c ≃ (Σ d : Fin (n-b-c+1), Cont n k c d.val) where
  toFun x := ⟨⟨(x.val 0).val,by have := x.property.1; omega⟩,
    ⟨fun i => x.val i.succ,x.property.2⟩⟩
  invFun z :=
    let d : Fin (n+1) := ⟨z.1.val,by have := z.1.isLt; omega⟩
    ⟨Fin.cons d z.2.val,show b+c+d.val ≤ n ∧ _ from
      ⟨by dsimp [d]; have := z.1.isLt; omega,z.2.property⟩⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  right_inv z := by rcases z with ⟨d,x⟩; rfl

private noncomputable def v (n k b c : ℕ) : ℚ := Fintype.card (Cont n k b c)

private theorem step (n k b c : ℕ) (h : b+c ≤ n) :
    v n (k+1) b c = ∑ d ∈ range (n-b-c+1), v n k c d := by
  unfold v
  rw [Fintype.card_congr (split n k b c h),Fintype.card_sigma,Nat.cast_sum,
    ← Fin.sum_univ_eq_sum_range]

private theorem base (n b c : ℕ) : v n 0 b c = 1 := by
  have : Unique (Cont n 0 b c) :=
    { default := ⟨Fin.elim0,True.intro⟩
      uniq := fun x => Subtype.ext (funext fun j => j.elim0) }
  simp [v]

private theorem valid (n : ℕ) (x : Word n 9) : good x = true ↔ allowed n 9 0 0 x := by
  simp [good,allowed,Finset.sum_range_succ,OMA.S_oeis_a241622.get]
  constructor
  · intro h
    have h0 := h 0 (by decide)
    have h1 := h 1 (by decide)
    have h2 := h 2 (by decide)
    have h3 := h 3 (by decide)
    have h4 := h 4 (by decide)
    have h5 := h 5 (by decide)
    have h6 := h 6 (by decide)
    simp_all
    omega
  · intro h i hi
    interval_cases i <;> simp_all

private theorem array_count (n : ℕ) : (a n : ℚ) = v n 9 0 0 := by
  classical
  let e : {x : Word n 9 // good x = true} ≃ Cont n 9 0 0 :=
    Equiv.subtypeEquivRight (valid n)
  have h := Fintype.card_congr e
  rw [Fintype.card_subtype] at h
  unfold a v
  exact_mod_cast h

private abbrev Formula := ℚ → ℚ → ℚ → ℚ

private def Counts (k : ℕ) (P : Formula) : Prop :=
  ∀ n b c : ℕ, b+c ≤ n → v n k b c = P n b c

private theorem advance (k : ℕ) (P H : Formula) (prev : Counts k P)
    (hz : ∀ x b, H x b 0 = 0)
    (hd : ∀ x b t, H x b (t+1) = H x b t + P x b t) :
    Counts (k+1) (fun x b c => H x c (x-b-c+1)) := by
  intro n b c h
  rw [step n k b c h]
  have partialSum (t : ℕ) (ht : t ≤ n-b-c+1) :
      ∑ j ∈ range t, v n k c j = H n c t := by
    induction t with
    | zero => simp [hz]
    | succ t ih =>
      rw [sum_range_succ,ih (by omega),prev n c t (by omega),Nat.cast_succ,hd]
  rw [partialSum _ le_rfl]
  push_cast [Nat.cast_sub (by omega : b ≤ n),Nat.cast_sub (by omega : c ≤ n-b)]
  rfl

private theorem count0 : Counts 0 (fun _ _ _ => 1) := fun n b c _ => base n b c

private def H1 (_x _b t : ℚ) : ℚ :=
  (t)/1

private theorem count1 : Counts 1 (fun x b c => H1 x c (x-b-c+1)) := by
  apply advance 0 _ H1 count0
  · intro x b; unfold H1; ring
  · intro x b t; unfold H1; ring

private def H2 (x b t : ℚ) : ℚ :=
  (t*(-2*b - t + 2*x + 3))/2

private theorem count2 : Counts 2 (fun x b c => H2 x c (x-b-c+1)) := by
  apply advance 1 _ H2 count1
  · intro x b; unfold H2; ring
  · intro x b t; unfold H2 H1; ring

private def H3 (x b t : ℚ) : ℚ :=
  (t*(b*(-3*b - 3) + t*(t - 3*x - 6) + x*(3*x + 12) + 11))/6

private theorem count3 : Counts 3 (fun x b c => H3 x c (x-b-c+1)) := by
  apply advance 2 _ H3 count2
  · intro x b; unfold H3; ring
  · intro x b t; unfold H3 H2; ring

private def H4 (x b t : ℚ) : ℚ :=
  (t*(b*(b*(-2*b - 3) - 1) + t*(b*(-3*b - 3) + t*(t - 2*x - 4) - 1) + x*(x*(2*x + 12) + 24) + 16))/12

private theorem count4 : Counts 4 (fun x b c => H4 x c (x-b-c+1)) := by
  apply advance 3 _ H4 count3
  · intro x b; unfold H4; ring
  · intro x b t; unfold H4 H3; ring

private def H5 (x b t : ℚ) : ℚ :=
  (t*(b*(b*(b*(2*b - 4*x - 4) - 6*x - 10) - 2*x - 4) + t*(b*(b*(4*b - 6*x - 6) - 6*x - 10) + t*(b*(2*b + 2) + t*(x + 2) + x*(-2*x - 8) - 8) - x - 2) + x*(x*(x*(2*x + 16) + 48) + 64) + 32))/24

private theorem count5 : Counts 5 (fun x b c => H5 x c (x-b-c+1)) := by
  apply advance 4 _ H5 count4
  · intro x b; unfold H5; ring
  · intro x b t; unfold H5 H4; ring

private def H6 (x b t : ℚ) : ℚ :=
  (t*(b*(b*(b*(b*(30*x + 60) + x*(-60*x - 180) - 100) + x*(-90*x - 360) - 330) + x*(-30*x - 150) - 170) + t*(b*(b*(b*(60*x + 120) + x*(-90*x - 270) - 165) + x*(-90*x - 330) - 285) + t*(b*(b*(-20*b + 60*x + 90) + 60*x + 110) + t*(b*(-15*b - 15) + t*(-6*x - 12) + x*(30*x + 120) + 120) + x*(x*(-40*x - 240) - 470) - 300) + x*(-30*x - 120) - 120) + x*(x*(x*(x*(30*x + 300) + 1210) + 2460) + 2516) + 1032))/720

private theorem count6 : Counts 6 (fun x b c => H6 x c (x-b-c+1)) := by
  apply advance 5 _ H6 count5
  · intro x b; unfold H6; ring
  · intro x b t; unfold H6 H5; ring

private def H7 (x b t : ℚ) : ℚ :=
  (t*(b*(b*(b*(b*(b*(42*x + 84) + 105*x + 245) + x*(x*(-140*x - 840) - 1680) - 1050) + x*(x*(-210*x - 1260) - 2625) - 1883) + x*(x*(-70*x - 420) - 882) - 672) + t*(b*(b*(b*(b*(105*x + 210) + 210*x + 490) + x*(x*(-210*x - 1260) - 2520) - 1575) + x*(x*(-210*x - 1260) - 2625) - 1855) + t*(b*(b*(b*(-35*b + 140*x + 210) + 210*x + 455) + 70*x + 210) + t*(b*(b*(-70*b + 105*x + 105) + 105*x + 175) + t*(b*(-42*b - 42) + t*(5*t - 28*x - 56) + x*(42*x + 168) + 140) + x*(x*(35*x + 210) + 525) + 490) + x*(x*(x*(-105*x - 840) - 2625) - 3780) - 2065) + x*(x*(-35*x - 210) - 497) - 434) + x*(x*(x*(x*(x*(98*x + 1176) + 5915) + 15960) + 24395) + 20076) + 6960))/5040

private theorem count7 : Counts 7 (fun x b c => H7 x c (x-b-c+1)) := by
  apply advance 6 _ H7 count6
  · intro x b; unfold H7; ring
  · intro x b t; unfold H7 H6; ring

private def H8 (x b t : ℚ) : ℚ :=
  (t*(b*(b*(b*(b*(b*(b*(-20*b + 28*x - 14) + x*(84*x + 420) + 490) + x*(210*x + 910) + 1120) + x*(x*(x*(-280*x - 2240) - 6720) - 8960) - 4410) + x*(x*(x*(-420*x - 3360) - 10290) - 14294) - 7658) + x*(x*(x*(-140*x - 1120) - 3444) - 4816) - 2612) + t*(b*(b*(b*(b*(b*(-70*b + 84*x - 42) + x*(210*x + 1050) + 1225) + x*(420*x + 1820) + 2240) + x*(x*(x*(-420*x - 3360) - 10080) - 13440) - 6615) + x*(x*(x*(-420*x - 3360) - 10290) - 14294) - 7658) + t*(b*(b*(b*(b*(-84*b - 210) + x*(280*x + 1120) + 1120) + x*(420*x + 1680) + 1890) + x*(140*x + 560) + 644) + t*(b*(b*(b*(-35*b - 140*x - 350) + x*(210*x + 630) + 455) + x*(210*x + 770) + 770) + t*(b*(b*(-84*x - 168) - 84*x - 168) + t*(t^2 + x*(-28*x - 112) - 126) + x*(x*(56*x + 336) + 700) + 504) + x*(x*(x*(70*x + 560) + 1750) + 2520) + 1449) + x*(x*(x*(x*(-196*x - 1960) - 7980) - 16520) - 17444) - 7560) + x*(x*(x*(-70*x - 560) - 1722) - 2408) - 1324) + x*(x*(x*(x*(x*(x*(188*x + 2632) + 15876) + 53480) + 108696) + 133392) + 91624) + 27216))/20160

private theorem count8 : Counts 8 (fun x b c => H8 x c (x-b-c+1)) := by
  apply advance 7 _ H8 count7
  · intro x b; unfold H8; ring
  · intro x b t; unfold H8 H7; ring

private def H9 (x b t : ℚ) : ℚ :=
  (t*(b*(b*(b*(b*(b*(b*(b*(3*b - 24*x - 36) - 84*x - 196) + x*(x*(168*x + 1008) + 2016) + 1218) + x*(x*(420*x + 2730) + 6090) + 4571) + x*(x*(x*(x*(-420*x - 4200) - 16940) - 34020) - 33460) - 12474) + x*(x*(x*(x*(-630*x - 6300) - 25830) - 54138) - 57834) - 25042) + x*(x*(x*(x*(-210*x - 2100) - 8638) - 18396) - 20360) - 9372) + t*(b*(b*(b*(b*(b*(b*(12*b - 84*x - 126) - 252*x - 588) + x*(x*(420*x + 2520) + 5040) + 3045) + x*(x*(840*x + 5460) + 12180) + 9198) + x*(x*(x*(x*(-630*x - 6300) - 25410) - 51030) - 50358) - 18963) + x*(x*(x*(x*(-630*x - 6300) - 25830) - 53970) - 57330) - 24666) + t*(b*(b*(b*(b*(b*(28*b - 84*x - 84) + x*(-210*x - 1050) - 1295) + x*(x*(560*x + 2940) + 4900) + 2310) + x*(x*(840*x + 5250) + 10920) + 7567) + x*(x*(280*x + 2100) + 5054) + 4074) + t*(b*(b*(b*(b*(42*b + 105) + x*(-420*x - 1680) - 1680) + x*(x*(420*x + 1890) + 2520) + 735) + x*(x*(420*x + 2310) + 4200) + 2478) + t*(b*(b*(b*(21*b + 84*x + 210) + x*(-252*x - 882) - 777) + x*(-252*x - 966) - 966) + t*(b*(b*(42*x + 84) + 42*x + 84) + t*(x*(12*x + 48) + 48) + x*(x*(-70*x - 420) - 854) - 588) + x*(x*(x*(105*x + 840) + 2499) + 3276) + 1596) + x*(x*(x*(x*(105*x + 1050) + 4445) + 9870) + 11410) + 5460) + x*(x*(x*(x*(x*(-294*x - 3528) - 17955) - 49560) - 78183) - 66780) - 24108) + x*(x*(x*(x*(-105*x - 1050) - 4375) - 9450) - 10556) - 4872) + x*(x*(x*(x*(x*(x*(x*(273*x + 4368) + 30744) + 124320) + 315987) + 517272) + 533052) + 316464) + 82944))/60480

private theorem count9 : Counts 9 (fun x b c => H9 x c (x-b-c+1)) := by
  apply advance 8 _ H9 count8
  · intro x b; unfold H9; ring
  · intro x b t; unfold H9 H8; ring

private def P (x : ℚ) : ℚ :=
  (x*(x*(x*(x*(x*(x*(x*(x*(131*x + 2358) + 18822) + 87444) + 260547) + 516222) + 679828) + 573336) + 280512) + 60480)/60480

private theorem value (n : ℕ) : (a n : ℚ) = P n := by
  rw [array_count,count9 n 0 0 (by omega)]
  unfold P H9; push_cast; ring

private theorem recurrence (n : ℕ) (hn : 11 ≤ n) :
    (a n : ℚ) = 10 * a (n - 1) - 45 * a (n - 2) + 120 * a (n - 3) - 210 * a (n - 4) + 252 * a (n - 5) - 210 * a (n - 6) + 120 * a (n - 7) - 45 * a (n - 8) + 10 * a (n - 9) - a (n - 10) := by
  obtain ⟨m,rfl⟩ : ∃ m, n=m+11 := ⟨n-11,by omega⟩
  simp only [show m+11-1 = m+10 by omega,show m+11-2 = m+9 by omega,show m+11-3 = m+8 by omega,show m+11-4 = m+7 by omega,show m+11-5 = m+6 by omega,show m+11-6 = m+5 by omega,show m+11-7 = m+4 by omega,show m+11-8 = m+3 by omega,show m+11-9 = m+2 by omega,show m+11-10 = m+1 by omega,value,P]
  push_cast
  ring

private theorem generating :
    PowerSeries.mk (fun n => if n < 1 then 0 else (a n : ℚ)) * ((1 - X) ^ 10 : PowerSeries ℚ) = X * (41 + 146 * X + 460 * X ^ 2 - 19 * X ^ 3 + 283 * X ^ 4 - 209 * X ^ 5 + 120 * X ^ 6 - 45 * X ^ 7 + 10 * X ^ 8 - X ^ 9) := by
  let S := mk (fun n => if n < 1 then 0 else (a n : ℚ))
  change S * _ = _
  have lhs : S*(1-X)^10 = S - (10:ℕ) • (S*X^1) + (45:ℕ) • (S*X^2) - (120:ℕ) • (S*X^3) + (210:ℕ) • (S*X^4) - (252:ℕ) • (S*X^5) + (210:ℕ) • (S*X^6) - (120:ℕ) • (S*X^7) + (45:ℕ) • (S*X^8) - (10:ℕ) • (S*X^9) + (S*X^10) := by simp only [nsmul_eq_mul]; ring
  have rhs : (X * (41 + 146 * X + 460 * X ^ 2 - 19 * X ^ 3 + 283 * X ^ 4 - 209 * X ^ 5 + 120 * X ^ 6 - 45 * X ^ 7 + 10 * X ^ 8 - X ^ 9) : PowerSeries ℚ) = (41:ℕ) • X^1 + (146:ℕ) • X^2 + (460:ℕ) • X^3 - (19:ℕ) • X^4 + (283:ℕ) • X^5 - (209:ℕ) • X^6 + (120:ℕ) • X^7 - (45:ℕ) • X^8 + (10:ℕ) • X^9 - X^10 := by simp only [nsmul_eq_mul]; ring
  rw [lhs,rhs]
  ext n
  simp only [map_add,map_sub,map_nsmul,coeff_mul_X_pow',coeff_X_pow,S,coeff_mk]
  by_cases h : 11 ≤ n
  · have recn := recurrence n h
    simp only [nsmul_eq_mul,if_pos (show 1 ≤ n by omega),
      if_pos (show 2 ≤ n by omega),
      if_pos (show 3 ≤ n by omega),
      if_pos (show 4 ≤ n by omega),
      if_pos (show 5 ≤ n by omega),
      if_pos (show 6 ≤ n by omega),
      if_pos (show 7 ≤ n by omega),
      if_pos (show 8 ≤ n by omega),
      if_pos (show 9 ≤ n by omega),
      if_pos (show 10 ≤ n by omega),
      if_neg (show ¬ n < 1 by omega),
      if_neg (show ¬ n-1 < 1 by omega),
      if_neg (show ¬ n-2 < 1 by omega),
      if_neg (show ¬ n-3 < 1 by omega),
      if_neg (show ¬ n-4 < 1 by omega),
      if_neg (show ¬ n-5 < 1 by omega),
      if_neg (show ¬ n-6 < 1 by omega),
      if_neg (show ¬ n-7 < 1 by omega),
      if_neg (show ¬ n-8 < 1 by omega),
      if_neg (show ¬ n-9 < 1 by omega),
      if_neg (show ¬ n-10 < 1 by omega),
      if_neg (show n ≠ 1 by omega),
      if_neg (show n ≠ 2 by omega),
      if_neg (show n ≠ 3 by omega),
      if_neg (show n ≠ 4 by omega),
      if_neg (show n ≠ 5 by omega),
      if_neg (show n ≠ 6 by omega),
      if_neg (show n ≠ 7 by omega),
      if_neg (show n ≠ 8 by omega),
      if_neg (show n ≠ 9 by omega),
      if_neg (show n ≠ 10 by omega)]
    norm_num
    linarith
  · interval_cases n <;> norm_num [value,P]

theorem result : type_of% @OMA.S_oeis_a241622.main := ⟨generating,recurrence⟩

end OMA.Windows241622

theorem OMA.solution : type_of% @OMA.S_oeis_a241622.main := OMA.Windows241622.result
