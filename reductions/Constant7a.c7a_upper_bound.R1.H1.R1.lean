import OMAReductions.R_Constant7a_c7a_upper_bound_R1

/-!
# Bai's arithmetic normalization for the irrationality measure of π

Based on Bai, arXiv:2609.11276v2, sections 2–4. An explicit multinomial
term and a rational evaluation bound give the required exponential window
for the residue without a local central limit theorem. Integer rescaling
uses only an upper bound on the cost of clearing denominators.
Credit: @AlfredMelson.
-/

namespace OMA.R_Constant7a_c7a_upper_bound_R1_H1_R1
open Polynomial Finset

/-- The term at a*n is maximal in the binomial expansion with weights a and b. -/
private theorem binomial_mode (a b n : ℕ) (_ha : 0 < a) (hb : 0 < b) :
    ((a+b)^(a+b))^n ≤ ((a+b)*n+1) * ((a+b)*n).choose (a*n) * (a^a*b^b)^n := by
  let N := (a+b)*n
  let T := fun j : ℕ => a^j*b^(N-j)*N.choose j
  have ratio (j : ℕ) (hj : j < N) :
      T (j+1)*((j+1)*b)=T j*((N-j)*a) := by
    dsimp [T]
    have e : N-j = (N-(j+1))+1 := by omega
    conv_rhs => arg 1; rw [e,pow_succ]
    rw [pow_succ a]
    have h := Nat.choose_succ_right_eq N j
    linear_combination (a^j*b^(N-(j+1))*a*b)*h
  have left (j : ℕ) (h : j < a*n) : T j ≤ T (j+1) := by
    have hN : j < N := by dsimp [N]; rw [add_mul]; omega
    have hj : j+1 ≤ a*n := by omega
    have d : (j+1)*b ≤ (N-j)*a := by
      have h' : b*n ≤ N-j := by dsimp [N]; rw [add_mul]; omega
      calc
        _ ≤ a*n*b := Nat.mul_le_mul_right b hj
        _ = b*n*a := by ring
        _ ≤ _ := Nat.mul_le_mul_right a h'
    exact (Nat.le_of_mul_le_mul_right (by rw [ratio j hN]; exact Nat.mul_le_mul_left _ d) (by positivity : 0 < (j+1)*b))
  have right (j : ℕ) (h : a*n ≤ j) (hN : j < N) : T (j+1) ≤ T j := by
    have hb' : N-j ≤ b*n := by dsimp [N]; rw [add_mul]; omega
    have d : (N-j)*a ≤ (j+1)*b := by
      calc
        _ ≤ b*n*a := Nat.mul_le_mul_right a hb'
        _ = a*n*b := by ring
        _ ≤ _ := Nat.mul_le_mul_right b (by omega)
    exact (Nat.le_of_mul_le_mul_right (by rw [ratio j hN]; exact Nat.mul_le_mul_left _ d) (by positivity : 0 < (j+1)*b))
  have maxT (j) (hj : j ≤ N) : T j ≤ T (a*n) := by
    rcases le_total j (a*n) with le|le
    · obtain ⟨d,hd⟩ := Nat.exists_eq_add_of_le le
      suffices ∀ t, j+t ≤ a*n → T j ≤ T (j+t) by simpa [← hd] using this d (by omega)
      intro t
      induction t with
      | zero => simp
      | succ t ih => intro h; exact (ih (by omega)).trans (left _ (by omega))
    · obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le le
      induction d with
      | zero => simp
      | succ d ih => exact (right (a*n+d) (by omega) (by omega)).trans (ih (by omega) (by omega))
  calc
    _ = ∑ j ∈ range (N+1), T j := by rw [← pow_mul,add_pow]; simp [N,T]
    _ ≤ ∑ _j ∈ range (N+1), T (a*n) := sum_le_sum fun j hj => maxT j (by simpa using hj)
    _ = _ := by
      simp only [sum_const,card_range,nsmul_eq_mul,Nat.cast_id,T,N,add_mul,Nat.add_sub_cancel_left,mul_pow,← pow_mul]
      ring

private theorem real_mode (a b n : ℕ) (ha : 0 < a) (hb : 0 < b) (h : a+b ≤ 9769) :
    (((a+b : ℕ) : ℝ)^(a+b)/((a:ℝ)^a*(b:ℝ)^b))^n ≤
      (9769*(n:ℝ)+1)*(((a+b)*n).choose (a*n) : ℝ) := by
  rw [div_pow, div_le_iff₀ (by positivity)]
  have hc := binomial_mode a b n ha hb
  have up : (a+b)*n+1 ≤ 9769*n+1 := by gcongr
  exact_mod_cast hc.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ up))
private theorem pick (Q : ℕ[X]) (w i a b k : ℕ) :
    w^a * (Q^b).coeff k * (a+b).choose a ≤
      ((C w*X^i+Q)^(a+b)).coeff (i*a+k) := by
  rw [add_pow, finsetSum_coeff]
  have h := Finset.single_le_sum (s:=range (a+b+1))
    (f:=fun j => (((C w*X^i)^j*Q^(a+b-j)*((a+b).choose j : ℕ[X])).coeff (i*a+k)))
    (fun _ _ => Nat.zero_le _) (show a∈range (a+b+1) by simp)
  apply le_trans _ h
  simp only [Nat.add_sub_cancel_left,mul_pow,← pow_mul,← map_pow,mul_assoc,
    coeff_C_mul]
  simp [Nat.add_comm (i*a) k]

private theorem shift_choose (n : ℕ) (hn : 0 < n) :
    (9769*n).choose (2339*n) ≤ (9769*n) * (2339*n+(7430*n-1)).choose (7430*n-1) := by
  let N := 9769*n-1
  have add : N+1=9769*n := by dsimp [N]; omega
  have eq : 2339*n+(7430*n-1)=N := by dsimp [N]; omega
  have eq' : N-(2339*n)=7430*n-1 := by dsimp [N]; omega
  rw [eq, ← eq', Nat.choose_symm (by dsimp [N]; omega)]
  have h := Nat.choose_mul_succ_eq N (2339*n)
  rw [add] at h
  calc
    _ ≤ (9769*n).choose (2339*n)*(9769*n-2339*n) := Nat.le_mul_of_pos_right _ (by omega)
    _ = _ := by rw [← h,mul_comm]

/-- Select 1485, 1420, 637, 152, 19, 1 copies per block of the six monomials.
Their degrees sum to 3231, leaving degree 2339 for the denominator. -/
private theorem numerator_term (n : ℕ) :
    (2^(1485*n)*(8^(1420*n)*(15^(637*n)*(15^(152*n)*(8^(19*n)*2^n*((20*n).choose (19*n)))*((172*n).choose (152*n)))*((809*n).choose (637*n)))*((2229*n).choose (1420*n)))*((3714*n).choose (1485*n))) ≤ (((C 2*X^0+(C 8*X^1+(C 15*X^2+(C 15*X^3+(C 8*X^4+C 2*X^5))))) : ℕ[X])^(3714*n)).coeff (3231*n) := by
  let Q5 : ℕ[X] := C 2*X^5
  let Q4 : ℕ[X] := C 8*X^4 + Q5
  let Q3 : ℕ[X] := C 15*X^3 + Q4
  let Q2 : ℕ[X] := C 15*X^2 + Q3
  let Q1 : ℕ[X] := C 8*X^1 + Q2
  let Q0 : ℕ[X] := C 2*X^0 + Q1
  have h5 : 2^n ≤ (Q5^n).coeff (5*n) := by
    simp only [Q5,mul_pow,← map_pow,← pow_mul,coeff_C_mul_X_pow,if_true,le_refl]
  have h4 : (8^(19*n)*2^n*((20*n).choose (19*n))) ≤ (Q4^(20*n)).coeff (81*n) := by
    have step := pick Q5 8 4 (19*n) (1*n) (5*n)
    rw [show 19*n+1*n=20*n by omega,show 4*(19*n)+5*n=81*n by omega] at step
    apply le_trans _ step
    gcongr
    simpa only [one_mul] using h5
  have h3 : (15^(152*n)*(8^(19*n)*2^n*((20*n).choose (19*n)))*((172*n).choose (152*n))) ≤ (Q3^(172*n)).coeff (537*n) := by
    have step := pick Q4 15 3 (152*n) (20*n) (81*n)
    rw [show 152*n+20*n=172*n by omega,show 3*(152*n)+81*n=537*n by omega] at step
    apply le_trans _ step
    gcongr
  have h2 : (15^(637*n)*(15^(152*n)*(8^(19*n)*2^n*((20*n).choose (19*n)))*((172*n).choose (152*n)))*((809*n).choose (637*n))) ≤ (Q2^(809*n)).coeff (1811*n) := by
    have step := pick Q3 15 2 (637*n) (172*n) (537*n)
    rw [show 637*n+172*n=809*n by omega,show 2*(637*n)+537*n=1811*n by omega] at step
    apply le_trans _ step
    gcongr
  have h1 : (8^(1420*n)*(15^(637*n)*(15^(152*n)*(8^(19*n)*2^n*((20*n).choose (19*n)))*((172*n).choose (152*n)))*((809*n).choose (637*n)))*((2229*n).choose (1420*n))) ≤ (Q1^(2229*n)).coeff (3231*n) := by
    have step := pick Q2 8 1 (1420*n) (809*n) (1811*n)
    rw [show 1420*n+809*n=2229*n by omega,show 1*(1420*n)+1811*n=3231*n by omega] at step
    apply le_trans _ step
    gcongr
  have h0 : (2^(1485*n)*(8^(1420*n)*(15^(637*n)*(15^(152*n)*(8^(19*n)*2^n*((20*n).choose (19*n)))*((172*n).choose (152*n)))*((809*n).choose (637*n)))*((2229*n).choose (1420*n)))*((3714*n).choose (1485*n))) ≤ (Q0^(3714*n)).coeff (3231*n) := by
    have step := pick Q1 2 0 (1485*n) (2229*n) (3231*n)
    rw [show 1485*n+2229*n=3714*n by omega,show 0*(1485*n)+3231*n=3231*n by omega] at step
    apply le_trans _ step
    gcongr
  exact h0

private theorem lower_count (n A : ℕ) (hn : 0 < n)
    (hA : (((C 2*X^0+(C 8*X^1+(C 15*X^2+(C 15*X^3+(C 8*X^4+C 2*X^5))))) : ℕ[X])^(3714*n)).coeff (3231*n) *
      (2339*n+(7430*n-1)).choose (7430*n-1) ≤ A) :
    ((25:ℝ)*2^3716*(2^1485*8^1420*15^637*15^152*8^19*2^1)*((3714:ℝ)^3714/(1485^1485*2229^2229))*((2229:ℝ)^2229/(1420^1420*809^809))*((809:ℝ)^809/(637^637*172^172))*((172:ℝ)^172/(152^152*20^20))*((20:ℝ)^20/(19^19*1^1))*((9769:ℝ)^9769/(2339^2339*7430^7430)))^n ≤ (9769*(n:ℝ)+1)^7*((25*2^3716:ℝ)^n*A) := by
  let D : ℝ := 9769*(n:ℝ)+1
  have num := numerator_term n
  have shift := shift_choose n hn
  have count : (2^(1485*n)*(8^(1420*n)*(15^(637*n)*(15^(152*n)*(8^(19*n)*2^n*((20*n).choose (19*n)))*((172*n).choose (152*n)))*((809*n).choose (637*n)))*((2229*n).choose (1420*n)))*((3714*n).choose (1485*n))) * ((9769*n).choose (2339*n)) ≤ (9769*n+1)*A := by
    calc
      _ ≤ _ := Nat.mul_le_mul num shift
      _ = 9769*n*((((C 2*X^0+(C 8*X^1+(C 15*X^2+(C 15*X^3+(C 8*X^4+C 2*X^5))))) : ℕ[X])^(3714*n)).coeff (3231*n) *
              (2339*n+(7430*n-1)).choose (7430*n-1)) := by ac_rfl
      _ ≤ _ := Nat.mul_le_mul (by omega) hA
  have cr : (((2^(1485*n)*(8^(1420*n)*(15^(637*n)*(15^(152*n)*(8^(19*n)*2^n*((20*n).choose (19*n)))*((172*n).choose (152*n)))*((809*n).choose (637*n)))*((2229*n).choose (1420*n)))*((3714*n).choose (1485*n))) * ((9769*n).choose (2339*n)) : ℕ) : ℝ) ≤ D*A := by dsimp [D]; exact_mod_cast count
  push_cast only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] at cr
  let t0 : ℝ := ((3714:ℝ)^3714/(1485^1485*2229^2229))
  let c0 : ℝ := ((3714*n).choose (1485*n))
  have h0 : t0^n ≤ D*c0 := real_mode 1485 2229 n (by decide) (by decide) (by decide)
  let t1 : ℝ := ((2229:ℝ)^2229/(1420^1420*809^809))
  let c1 : ℝ := ((2229*n).choose (1420*n))
  have h1 : t1^n ≤ D*c1 := real_mode 1420 809 n (by decide) (by decide) (by decide)
  let t2 : ℝ := ((809:ℝ)^809/(637^637*172^172))
  let c2 : ℝ := ((809*n).choose (637*n))
  have h2 : t2^n ≤ D*c2 := real_mode 637 172 n (by decide) (by decide) (by decide)
  let t3 : ℝ := ((172:ℝ)^172/(152^152*20^20))
  let c3 : ℝ := ((172*n).choose (152*n))
  have h3 : t3^n ≤ D*c3 := real_mode 152 20 n (by decide) (by decide) (by decide)
  let t4 : ℝ := ((20:ℝ)^20/(19^19*1^1))
  let c4 : ℝ := ((20*n).choose (19*n))
  have h4 : t4^n ≤ D*c4 := by
    simpa only [Nat.reduceAdd,Nat.cast_ofNat,Nat.cast_one,t4,c4,D] using real_mode 19 1 n (by decide) (by decide) (by decide)
  let t5 : ℝ := ((9769:ℝ)^9769/(2339^2339*7430^7430))
  let c5 : ℝ := ((9769*n).choose (2339*n))
  have h5 : t5^n ≤ D*c5 := real_mode 2339 7430 n (by decide) (by decide) (by decide)
  change ((2:ℝ)^(1485*n)*((8:ℝ)^(1420*n)*((15:ℝ)^(637*n)*((15:ℝ)^(152*n)*((8:ℝ)^(19*n)*2^n*c4)*c3)*c2)*c1)*c0)*c5 ≤ D*A at cr
  let Z : ℝ := 25*2^3716
  change (Z*(2^1485*8^1420*15^637*15^152*8^19*2^1)*t0*t1*t2*t3*t4*t5)^n ≤ D^7*(Z^n*A)
  have hZ : 0 ≤ Z := by dsimp [Z]; positivity
  have ht0 : 0 ≤ t0 := by dsimp [t0]; positivity
  have ht1 : 0 ≤ t1 := by dsimp [t1]; positivity
  have ht2 : 0 ≤ t2 := by dsimp [t2]; positivity
  have ht3 : 0 ≤ t3 := by dsimp [t3]; positivity
  have ht4 : 0 ≤ t4 := by dsimp [t4]; positivity
  have ht5 : 0 ≤ t5 := by dsimp [t5]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  calc
    _ = Z^n*((2:ℝ)^(1485*n)*(8:ℝ)^(1420*n)*(15:ℝ)^(637*n)*(15:ℝ)^(152*n)*(8:ℝ)^(19*n)*2^n)*t0^n*t1^n*t2^n*t3^n*t4^n*t5^n := by simp only [mul_pow,← pow_mul,one_mul]
    _ ≤ Z^n*((2:ℝ)^(1485*n)*(8:ℝ)^(1420*n)*(15:ℝ)^(637*n)*(15:ℝ)^(152*n)*(8:ℝ)^(19*n)*2^n)*(D*c0)*(D*c1)*(D*c2)*(D*c3)*(D*c4)*(D*c5) := by gcongr
    _ = D^6*Z^n*(((2:ℝ)^(1485*n)*((8:ℝ)^(1420*n)*((15:ℝ)^(637*n)*((15:ℝ)^(152*n)*((8:ℝ)^(19*n)*2^n*c4)*c3)*c2)*c1)*c0)*c5) := by rw [show D^6=D*D*D*D*D*D by ring]; ac_rfl
    _ ≤ D^6*Z^n*(D*A) := by gcongr
    _ = _ := by rw [pow_succ D 6]; ac_rfl
private theorem numerical_lower : (279925/10000 : ℝ)^5570 ≤ ((25:ℝ)*2^3716*(2^1485*8^1420*15^637*15^152*8^19*2^1)*((3714:ℝ)^3714/(1485^1485*2229^2229))*((2229:ℝ)^2229/(1420^1420*809^809))*((809:ℝ)^809/(637^637*172^172))*((172:ℝ)^172/(152^152*20^20))*((20:ℝ)^20/(19^19*1^1))*((9769:ℝ)^9769/(2339^2339*7430^7430))) := by
  have h := (by decide +kernel : (279925/10000 : ℚ)^5570 ≤ ((25:ℚ)*2^3716*(2^1485*8^1420*15^637*15^152*8^19*2^1)*((3714:ℚ)^3714/(1485^1485*2229^2229))*((2229:ℚ)^2229/(1420^1420*809^809))*((809:ℚ)^809/(637^637*172^172))*((172:ℚ)^172/(152^152*20^20))*((20:ℚ)^20/(19^19*1^1))*((9769:ℚ)^9769/(2339^2339*7430^7430))))
  have h' := (Rat.cast_le (K:=ℝ)).2 h
  push_cast at h'
  exact h'
private theorem numerical_upper : (25*2^3716*(2+8*(299/1250:ℝ)+15*(299/1250:ℝ)^2+15*(299/1250:ℝ)^3+8*(299/1250:ℝ)^4+2*(299/1250:ℝ)^5)^3714/((1-(299/1250:ℝ))^7430*(299/1250:ℝ)^5570)) ≤ (279928/10000 : ℝ)^5570 := by
  have h := (by decide +kernel : (25*2^3716*(2+8*(299/1250:ℚ)+15*(299/1250:ℚ)^2+15*(299/1250:ℚ)^3+8*(299/1250:ℚ)^4+2*(299/1250:ℚ)^5)^3714/((1-(299/1250:ℚ))^7430*(299/1250:ℚ)^5570)) ≤ (279928/10000 : ℚ)^5570)
  have h' := (Rat.cast_le (K:=ℝ)).2 h
  push_cast at h'
  exact h'
open Polynomial Finset
private theorem upper_series (B : ℕ[X]) (K D : ℕ) (x : ℝ) (hx : 0 < x) (hx' : x < 1) :
    (↑(∑ j ∈ range (K+1), B.coeff j * (K-j+D).choose D) : ℝ)*x^K ≤
      B.eval₂ (Nat.castRingHom ℝ) x / (1-x)^(D+1) := by
  have series := hasSum_choose_mul_geometric_of_norm_lt_one D (r:=x) (by simpa [abs_of_pos hx] using hx')
  have bound (j : ℕ) :
      ((j+D).choose D : ℝ)*x^j ≤ 1/(1-x)^(D+1) :=
    by
      rw [← series.tsum_eq]
      exact series.summable.le_tsum j (by intros; positivity)
  let A : ℕ → ℝ := fun j => (B.coeff j : ℝ)*x^j
  have small : ∑ j ∈ range (K+1), A j ≤ B.eval₂ (Nat.castRingHom ℝ) x := by
    rw [Polynomial.eval₂_eq_sum_range' _ (n:=K+B.natDegree+1) (by omega)]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) (by intros; dsimp [A]; positivity)
  push_cast
  rw [Finset.sum_mul]
  calc
    _ ≤ ∑ j ∈ range (K+1), A j*(1/(1-x)^(D+1)) := by
      apply sum_le_sum
      intro j hj
      have e : j+(K-j)=K := by simp at hj; omega
      calc
        _ = A j*(((K-j+D).choose D : ℝ)*x^(K-j)) := by dsimp [A]; rw [← e]; simp; ring
        _ ≤ _ := by gcongr; apply bound
    _ ≤ _ := by rw [← Finset.sum_mul]; simp only [div_eq_mul_inv,one_mul]; exact mul_le_mul_of_nonneg_right small (by positivity)
private theorem exp_lower_input : Real.exp 3.33193 ≤ 279924/10000 := by
  have h := Real.exp_bound' (by norm_num : (0:ℝ) ≤ 0.33193)
    (by norm_num : (0.33193:ℝ) ≤ 1) (by decide : 0 < 10)
  norm_num [Finset.sum_range_succ,Nat.factorial] at h
  rw [show (3.33193:ℝ) = 1*(3:ℕ)+0.33193 by norm_num,Real.exp_add,
    mul_comm (1:ℝ),Real.exp_nat_mul]
  calc
    _ ≤ (2.7182818286:ℝ)^3 * _ := by gcongr; exact Real.exp_one_lt_d9.le
    _ ≤ _ := by nlinarith
private theorem exp_upper_input : (279928/10000:ℝ) ≤ Real.exp 3.33195 := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 0.33195) 9
  norm_num [Finset.sum_range_succ,Nat.factorial] at h
  rw [show (3.33195:ℝ) = (3:ℕ)*1+0.33195 by norm_num,Real.exp_add,Real.exp_nat_mul]
  calc
    _ ≤ (2.7182818283:ℝ)^3 * Real.exp 0.33195 := by nlinarith
    _ ≤ _ := by gcongr; exact Real.exp_one_gt_d9.le
open Filter
private theorem absorb {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ∀ᶠ n : ℕ in atTop, 8*(9769*(n:ℝ)+1)^7*a^n ≤ b^n := by
  have hb := ha.trans hab
  have little := isLittleO_pow_const_mul_const_pow_const_pow_of_norm_lt 7
    (r₁:=a) (r₂:=b) (by rwa [Real.norm_eq_abs,abs_of_pos ha])
  filter_upwards [little.bound (show (0:ℝ) < 1/(8*9770^7) by positivity),eventually_ge_atTop 1] with n h hn
  have hn' : 1 ≤ (n:ℝ) := by exact_mod_cast hn
  simp only [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (n:ℝ)^7*a^n),
    abs_of_pos (pow_pos hb n)] at h
  have h' : 8*9770^7*((n:ℝ)^7*a^n) ≤ b^n := by linarith
  calc
    _ ≤ 8*(9770*(n:ℝ))^7*a^n := by gcongr; linarith
    _ = _ := by rw [mul_pow]; ring
    _ ≤ _ := h'

private theorem fit {m cap j v lo hi : ℝ} {U V : ℤ}
    (hm : 0 < m) (hcap : m ≤ cap) (form : m*j=(U:ℝ)+(V:ℝ)*Real.pi)
    (coeff : |(V:ℝ)|=m*v) (hv : 0 ≤ v) (small : 2*lo ≤ cap*v) (large : cap*v ≤ hi) :
    ∃ (M : ℝ) (A B : ℤ), 0 < M ∧ M ≤ cap ∧ M*j=(A:ℝ)+(B:ℝ)*Real.pi ∧
      lo ≤ |(B:ℝ)| ∧ |(B:ℝ)| ≤ hi := by
  have capPos := hm.trans_le hcap
  let k := ⌊cap/m⌋₊
  have one : 1 ≤ k := (Nat.one_le_floor_iff _).mpr ((one_le_div hm).mpr hcap)
  have fk : (k:ℝ) ≤ cap/m := Nat.floor_le (by positivity)
  have cr := Nat.lt_floor_add_one (cap/m)
  have low : cap ≤ 2*((k:ℝ)*m) := by
    have h' : cap < ((k:ℝ)+1)*m := (div_lt_iff₀ hm).mp cr
    have hk : (1:ℝ) ≤ k := by exact_mod_cast one
    nlinarith [mul_nonneg (sub_nonneg.mpr hk) hm.le]
  have up := (le_div_iff₀ hm).mp fk
  refine ⟨k*m,k*U,k*V,by positivity,up,?_,?_,?_⟩
  · push_cast; linear_combination (k:ℝ)*form
  · push_cast
    rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg _),coeff]
    nlinarith [mul_le_mul_of_nonneg_right low hv]
  · push_cast
    rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg _),coeff,←mul_assoc]
    exact (mul_le_mul_of_nonneg_right up hv).trans large

/-- Explicit exponential window for Bai's positive residue coefficient.
A single prescribed multinomial term supplies the lower estimate. -/
private theorem rates :
    ∀ᶠ n : ℕ in atTop,
      2*Real.exp ((5570*3.331925:ℝ)*n) ≤ ((25*2^3716:ℝ)^n*((∑ j ∈ range (5570*n+1), (((C 2*X^0+(C 8*X^1+(C 15*X^2+(C 15*X^3+(C 8*X^4+C 2*X^5))))) : ℕ[X])^(3714*n)).coeff j *
    (5570*n-j+(7430*n-1)).choose (7430*n-1)) : ℕ)/4) ∧
      ((25*2^3716:ℝ)^n*((∑ j ∈ range (5570*n+1), (((C 2*X^0+(C 8*X^1+(C 15*X^2+(C 15*X^3+(C 8*X^4+C 2*X^5))))) : ℕ[X])^(3714*n)).coeff j *
    (5570*n-j+(7430*n-1)).choose (7430*n-1)) : ℕ)/4) ≤ Real.exp ((5570*3.33195:ℝ)*n) := by
  let a := Real.exp 3.331925 ^ 5570
  let b := (279925/10000:ℝ)^5570
  have hab : a < b := by
    apply pow_lt_pow_left₀ _ (by positivity) (by decide)
    exact ((Real.exp_lt_exp.mpr (by norm_num : (3.331925:ℝ) < 3.33193)).trans_le exp_lower_input).trans (by norm_num)
  filter_upwards [absorb (a:=a) (by positivity) hab,eventually_ge_atTop 1] with n loss hn
  let P : ℕ[X] := (C 2*X^0+(C 8*X^1+(C 15*X^2+(C 15*X^3+(C 8*X^4+C 2*X^5)))))
  let A : ℕ := (∑ j ∈ range (5570*n+1), (((C 2*X^0+(C 8*X^1+(C 15*X^2+(C 15*X^3+(C 8*X^4+C 2*X^5))))) : ℕ[X])^(3714*n)).coeff j *
    (5570*n-j+(7430*n-1)).choose (7430*n-1))
  let Z : ℝ := 25*2^3716
  change 2*Real.exp ((5570*3.331925:ℝ)*n) ≤ Z^n*A/4 ∧ Z^n*A/4 ≤ Real.exp ((5570*3.33195:ℝ)*n)
  have oneTerm : (P^(3714*n)).coeff (3231*n)*(2339*n+(7430*n-1)).choose (7430*n-1) ≤ A := by
    dsimp only [A]
    have h := single_le_sum (s:=range (5570*n+1))
      (f:=fun j => (P^(3714*n)).coeff j*(5570*n-j+(7430*n-1)).choose (7430*n-1))
      (fun _ _ => Nat.zero_le _) (show 3231*n ∈ range (5570*n+1) by simp; omega)
    rwa [show 5570*n-3231*n=2339*n by omega] at h
  have count := lower_count n A hn oneTerm
  have compare := (pow_le_pow_left₀ (by positivity) numerical_lower n).trans count
  change b^n ≤ (9769*(n:ℝ)+1)^7*(Z^n*A) at compare
  have conv (r : ℝ) : (Real.exp r ^ 5570)^n = Real.exp ((5570*r)*n) := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
    congr 1
    ring
  constructor
  · rw [← conv]
    change 2*a^n ≤ Z^n*A/4
    have l := loss.trans compare
    have hd : 0 < (9769*(n:ℝ)+1)^7 := by positivity
    apply (le_div_iff₀ (by norm_num : (0:ℝ)<4)).2
    apply (le_of_mul_le_mul_left _ hd)
    convert l using 1 <;> ring
  · let x : ℝ := 299/1250
    have u := upper_series (P^(3714*n)) (5570*n) (7430*n-1) x (by norm_num [x]) (by norm_num [x])
    change (A:ℝ)*x^(5570*n) ≤ _ at u
    rw [show 7430*n-1+1=7430*n by omega, Polynomial.eval₂_pow] at u
    let y := P.eval₂ (Nat.castRingHom ℝ) x
    change (A:ℝ)*x^(5570*n) ≤ y^(3714*n)/(1-x)^(7430*n) at u
    have hx : 0 < x := by norm_num [x]
    have hx1 : 0 < 1-x := by norm_num [x]
    have denpos : 0 < (1-x)^(7430*n)*x^(5570*n) := by positivity
    have ratio : (A:ℝ) ≤ (y^3714/((1-x)^7430*x^5570))^n := by
      rw [div_pow,mul_pow,←pow_mul,←pow_mul,←pow_mul,le_div_iff₀ denpos]
      have h := (le_div_iff₀ (pow_pos hx1 _)).mp u
      linarith only [h]
    have hy : y = 2+8*x+15*x^2+15*x^3+8*x^4+2*x^5 := by
      dsimp only [y,P]
      simp only [Polynomial.eval₂_add,Polynomial.eval₂_mul,Polynomial.eval₂_ofNat,Polynomial.eval₂_pow,Polynomial.eval₂_X,Polynomial.eval₂_C,map_ofNat]
      ring
    have num : Z*(y^3714/((1-x)^7430*x^5570)) ≤ (279928/10000:ℝ)^5570 := by
      rw [hy,mul_div_assoc']
      exact numerical_upper
    have realBound : Z^n*(A:ℝ) ≤ (Real.exp 3.33195^5570)^n := by
      calc
        _ ≤ Z^n*(y^3714/((1-x)^7430*x^5570))^n := mul_le_mul_of_nonneg_left ratio (by dsimp [Z]; positivity)
        _ = _ := (mul_pow ..).symm
        _ ≤ ((279928/10000:ℝ)^5570)^n := pow_le_pow_left₀ (by rw [hy]; dsimp [Z]; positivity) num _
        _ ≤ _ := by gcongr; exact exp_upper_input
    rw [conv] at realBound
    have pos : 0 ≤ Z^n*(A:ℝ) := by dsimp [Z]; positivity
    exact (div_le_self pos (by norm_num)).trans realBound
open Finset Polynomial
private theorem binary_coeff (Q R : ℕ[X]) (n j : ℕ) (hj : j ≤ 5570*n) :
    2^(929*n) ∣ (((C 2*Q+X^2*R)^(3714*n)).coeff j) := by
  rw [add_pow,finsetSum_coeff]
  apply Finset.dvd_sum
  intro a _
  simp only [mul_pow, ← map_pow, ← pow_mul, coeff_mul_natCast]
  by_cases ha : 929*n ≤ a
  · apply dvd_mul_of_dvd_left _ _
    rw [mul_assoc,coeff_C_mul]
    exact dvd_mul_of_dvd_left (pow_dvd_pow 2 ha) _
  · have h : ¬ 2*(3714*n-a) ≤ j := by omega
    apply dvd_mul_of_dvd_left _ _
    rw [show C (2^a)*Q^a*(X^(2*(3714*n-a))*R^(3714*n-a)) =
      X^(2*(3714*n-a))*(C (2^a)*Q^a*R^(3714*n-a)) by ac_rfl, coeff_X_pow_mul', if_neg h]
    exact dvd_zero _

private theorem reduced_lcm_pos (N : ℕ) (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime ∧ p ≤ N) :
    0 < ((Icc 1 N).lcm id)/(∏ p ∈ s,p) := by
  have ha : 0 < (Icc 1 N).lcm id := Nat.pos_of_ne_zero (lcm_ne_zero_iff.mpr (by
    intro j hj; have := (mem_Icc.mp hj).1; simpa using (by omega : j≠0)))
  have hb : 0 < ∏ p ∈ s,p := prod_pos (fun p hp => (hs p hp).1.pos)
  have d : (∏ p ∈ s,p) ∣ (Icc 1 N).lcm id := by
    apply Finset.prod_dvd_of_isRelPrime
    · intro a ha b hb ne
      exact Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes (hs a ha).1 (hs b hb).1).mpr ne)
    · intro p hp
      exact Finset.dvd_lcm (f:=id) (mem_Icc.mpr ⟨(hs p hp).1.pos,(hs p hp).2⟩)
  exact Nat.div_pos (Nat.le_of_dvd ha d) hb

/-- The coefficient in Bai's real linear form already contains the residual
power of 2 needed to make its normalized multiple an integer. -/
private theorem coeff_integer (n L A : ℕ) (dvd : 2^(929*n) ∣ A) :
    ∃ V : ℤ, (V:ℝ) = -(16*(L:ℝ)/2^(4645*n))*((25*2^3716:ℝ)^n*(A:ℝ)/4) := by
  obtain ⟨z,rfl⟩ := dvd
  refine ⟨-((4*L*25^n*z : ℕ) : ℤ),?_⟩
  push_cast
  rw [mul_pow,←pow_mul]
  have powEq : (2:ℝ)^(4645*n) = 2^(3716*n)*2^(929*n) := by rw [←pow_add]; congr 1; omega
  rw [powEq]
  field_simp
  ring

/-- Integrality of the rational remainder, with Bai's explicit prime deletions.
The logarithmic residue coefficient is the displayed positive convolution. -/
def H1 : Prop := ∀ᶠ n : ℕ in atTop,
    let L : ℕ := ((Icc 1 (7430*n)).lcm id / (∏ p ∈ ((Icc 1 (7430*n)).filter fun p : ℕ => p.Prime ∧ 5 < p ∧ 7430*n < p*p ∧
      (3714*n+p)%(2*p)+4*((3714*n)%p) < 2*((5570*n)%p)),p))
    let P : ℕ[X] := (C 2*X^0+(C 8*X^1+(C 15*X^2+(C 15*X^3+(C 8*X^4+C 2*X^5)))))
    let A : ℕ := ∑ j ∈ range (5570*n+1), (P^(3714*n)).coeff j *
      (5570*n-j+(7430*n-1)).choose (7430*n-1)
    ∃ U : ℤ, (16*(L:ℝ)/2^(4645*n))*((-(∫ y in (-2 : ℝ)..2,
      let t := (-1 : ℂ) + (y : ℂ) * Complex.I
      (5 * t ^ (3714 * n) * (t ^ 4 + 6 * t ^ 2 + 25) ^ (3714 * n) /
        (25 - t ^ 2) ^ (5570 * n + 1)).re)) +
      ((25*2^3716:ℝ)^n*A/4)*Real.pi) = (U:ℝ)

/-- One-sided prime saving in the cost of the reduced least common multiple. -/
def H2 : Prop := ∀ᶠ n : ℕ in atTop,
    let L : ℕ := ((Icc 1 (7430*n)).lcm id / (∏ p ∈ ((Icc 1 (7430*n)).filter fun p : ℕ => p.Prime ∧ 5 < p ∧ 7430*n < p*p ∧
      (3714*n+p)%(2*p)+4*((3714*n)%p) < 2*((5570*n)%p)),p))
    16*(L:ℝ)/2^(4645*n) ≤ Real.exp ((5570*0.539995:ℝ)*n)

theorem main : H1 → H2 → OMA.R_Constant7a_c7a_upper_bound_R1.H1 := by
  intro arith cost
  filter_upwards [arith,cost,rates] with n integ upper bounds
  let s := ((Icc 1 (7430*n)).filter fun p : ℕ => p.Prime ∧ 5 < p ∧ 7430*n < p*p ∧
      (3714*n+p)%(2*p)+4*((3714*n)%p) < 2*((5570*n)%p))
  let L : ℕ := (Icc 1 (7430*n)).lcm id / ∏ p ∈ s,p
  let m := 16*(L:ℝ)/2^(4645*n)
  let P : ℕ[X] := (C 2*X^0+(C 8*X^1+(C 15*X^2+(C 15*X^3+(C 8*X^4+C 2*X^5)))))
  let A : ℕ := ∑ j ∈ range (5570*n+1), (P^(3714*n)).coeff j *
      (5570*n-j+(7430*n-1)).choose (7430*n-1)
  let v := (25*2^3716:ℝ)^n*A/4
  let j := (-(∫ y in (-2 : ℝ)..2,
      let t := (-1 : ℂ) + (y : ℂ) * Complex.I
      (5 * t ^ (3714 * n) * (t ^ 4 + 6 * t ^ 2 + 25) ^ (3714 * n) /
        (25 - t ^ 2) ^ (5570 * n + 1)).re))
  change ∃ U : ℤ, m*(j+v*Real.pi)=(U:ℝ) at integ
  obtain ⟨U,hU⟩ := integ
  have hL : 0 < L := reduced_lcm_pos _ s (fun p hp =>
    ⟨(mem_filter.mp hp).2.1,(mem_Icc.mp (mem_filter.mp hp).1).2⟩)
  have hm : 0 < m := by dsimp [m]; positivity
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have d : 2^(929*n) ∣ A := by
    apply Finset.dvd_sum
    intro j hj
    apply dvd_mul_of_dvd_left _ _
    have poly : P = C 2*(C 1+C 4*X)+X^2*(C 15+C 15*X+C 8*X^2+C 2*X^3) := by
      dsimp only [P]; simp only [pow_zero,pow_one,mul_one,Polynomial.C_ofNat,map_one]; ring
    rw [poly]
    exact binary_coeff _ _ _ _ (by simpa using hj)
  obtain ⟨V,hV⟩ := coeff_integer n L A d
  change (V:ℝ) = -m*v at hV
  have form : m*j=(U:ℝ)+(V:ℝ)*Real.pi := by rw [← hU,hV]; ring
  have ab : |(V:ℝ)|=m*v := by rw [hV,neg_mul,abs_neg,abs_of_nonneg (mul_nonneg hm.le hv)]
  rw [OMA.R_Constant7a_c7a_upper_bound_R1.contour_eq n]
  apply fit hm upper form ab hv
  · calc
      _ = Real.exp ((5570*0.539995:ℝ)*n)*(2*Real.exp ((5570*3.331925:ℝ)*n)) := by
        rw [mul_left_comm,←Real.exp_add]; congr 2; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left bounds.1 (Real.exp_pos _).le
  · calc
      _ ≤ Real.exp ((5570*0.539995:ℝ)*n)*Real.exp ((5570*3.33195:ℝ)*n) :=
        mul_le_mul_of_nonneg_left bounds.2 (Real.exp_pos _).le
      _ ≤ _ := by rw [←Real.exp_add,Real.exp_le_exp]; nlinarith [Nat.cast_nonneg (α:=ℝ) n]

end OMA.R_Constant7a_c7a_upper_bound_R1_H1_R1
