import OMAStatements.S_mse_5079681

/-!
# First decimal digit of the prime zeta function

Marco Ripà asked the question. Derfellios identified the separate digit boundaries,
Henry observed the crossing at exponent 9, and GH from MO gave an asymptotic argument.
The proof below obtains agreement from exponent 10.
It specializes the integral approximation method of F. Beukers and M. A. Bennett
(see Bennett, *Fractional parts of powers of rational numbers*, Section 2)
at the integer knots 0, 3, 128. Splitting the integral there separates the
next decimal boundary from the leading prime term. A finite integer certificate
treats exponents below 5000.
-/

open scoped BigOperators
open MeasureTheory intervalIntegral

namespace RipaProof

noncomputable def betaNat (i j : ℕ) : ℝ := ∫ x in (0:ℝ)..1, x^i * (1-x)^j

lemma beta_step (i j : ℕ) :
    (i+1:ℝ)*betaNat i (j+1) = (j+1:ℝ)*betaNat (i+1) j := by
  let f := fun x : ℝ => x^(i+1)*(1-x)^(j+1)
  have der (x : ℝ) : HasDerivAt f
      ((i+1:ℝ)*(x^i*(1-x)^(j+1))-(j+1:ℝ)*(x^(i+1)*(1-x)^j)) x := by
    dsimp [f]
    have H := ((hasDerivAt_id x).pow (i+1)).mul
      (((hasDerivAt_id x).const_sub 1).pow (j+1))
    convert H using 1 <;> first | rfl | (simp; ring)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=(0:ℝ)) (b:=1)
      (fun x _ => der x) (Continuous.intervalIntegrable (by fun_prop) ..)
  rw [intervalIntegral.integral_sub (Continuous.intervalIntegrable (by fun_prop) ..)
      (Continuous.intervalIntegrable (by fun_prop) ..),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at h
  simpa [f,betaNat,sub_eq_zero] using h

lemma beta_eval (i j : ℕ) : betaNat i j =
    (i.factorial:ℝ)*j.factorial / (i+j+1).factorial := by
  induction j generalizing i with
  | zero =>
    simp [betaNat,integral_pow,Nat.factorial_succ]
    field_simp
  | succ j ih =>
    have h := beta_step i j
    rw [ih, Nat.factorial_succ] at h
    rw [show i+(j+1)+1=(i+1)+j+1 by omega, Nat.factorial_succ j]
    push_cast at *
    have hpos : (0:ℝ) < (i+1+j+1).factorial := by positivity
    field_simp at h ⊢
    nlinarith only [h]

def scoef (m j : ℕ) : ℕ := (m+j).choose m * (2*m-j).choose m

def sval (m : ℕ) (a b : ℤ) : ℤ :=
  ∑ j ∈ Finset.range (m+1), (scoef m j : ℤ)*a^(m-j)*b^j

noncomputable def normFactor (m : ℕ) : ℝ :=
  ((3*m+1).factorial : ℝ)/(m.factorial : ℝ)^3

lemma coef_beta (m j : ℕ) (hj : j ≤ m) :
    normFactor m * m.choose j * betaNat (m+j) (2*m-j) = scoef m j := by
  rw [beta_eval, show m+j+(2*m-j)+1=3*m+1 by omega]
  unfold normFactor scoef
  push_cast
  have h1 := Nat.choose_mul_factorial_mul_factorial hj
  have h2 := Nat.choose_mul_factorial_mul_factorial (show m ≤ m+j by omega)
  have h3 := Nat.choose_mul_factorial_mul_factorial (show m ≤ 2*m-j by omega)
  rw [show m+j-m=j by omega] at h2
  rw [show 2*m-j-m=m-j by omega] at h3
  have eqn : m.choose j * ((m+j).factorial*(2*m-j).factorial) =
      (m+j).choose m * (2*m-j).choose m * m.factorial^3 := by
    rw [← h2, ← h3]
    calc _ = (m.choose j*j.factorial*(m-j).factorial) *
        ((m+j).choose m * (2*m-j).choose m * m.factorial^2) := by ring
      _ = _ := by rw [h1]; ring
  have hd : ((3*m+1).factorial : ℝ) ≠ 0 := by positivity
  have hm : (m.factorial : ℝ) ≠ 0 := by positivity
  have hr : (m.choose j : ℝ) * ((m+j).factorial*(2*m-j).factorial : ℝ) =
      (m+j).choose m * ((2*m-j).choose m : ℝ) * (m.factorial : ℝ)^3 := by exact_mod_cast eqn
  field_simp
  linear_combination hr

lemma integral_sval (m : ℕ) (a b : ℤ) :
    normFactor m * (∫ x in (0:ℝ)..1,
      (x*(1-x)*((a:ℝ)*(1-x)+b*x))^m) = sval m a b := by
  have expand (x : ℝ) :
      (x*(1-x)*((a:ℝ)*(1-x)+b*x))^m =
        ∑ j ∈ Finset.range (m+1),
          (((m.choose j:ℝ)*(a:ℝ)^(m-j)*b^j) * (x^(m+j)*(1-x)^(2*m-j))) := by
    rw [mul_pow, mul_pow, add_comm ((a:ℝ)*(1-x)), add_pow, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hj' := Finset.mem_range.mp hj
    rw [show 2*m-j=m+(m-j) by omega, pow_add, pow_add, mul_pow, mul_pow]
    ring
  simp_rw [expand]
  rw [intervalIntegral.integral_finsetSum (fun j _ => Continuous.intervalIntegrable (by fun_prop) ..), Finset.mul_sum]
  unfold sval
  push_cast
  apply Finset.sum_congr rfl
  intro j hj
  rw [intervalIntegral.integral_const_mul]
  have h := coef_beta m j (by have := Finset.mem_range.mp hj; omega)
  unfold betaNat at h
  linear_combination (a:ℝ)^(m-j) * (b:ℝ)^j * h

noncomputable def cubic (m : ℕ) (x : ℝ) := (x*(x-3)*(128-x))^m

lemma integral_piece (m : ℕ) (c v d : ℝ) (a b : ℤ)
    (h : ∀ x : ℝ, (d+c*x)*((d+c*x)-3)*(128-(d+c*x)) =
      v*(x*(1-x)*((a:ℝ)*(1-x)+b*x))) :
    normFactor m * (∫ x in d..(d+c), cubic m x) = c*v^m*(sval m a b : ℝ) := by
  have sc := intervalIntegral.smul_integral_comp_add_mul (a:=(0:ℝ)) (b:=1) (cubic m) c d
  simp only [mul_zero, add_zero, mul_one, smul_eq_mul] at sc
  rw [← sc]
  simp only [cubic, h, mul_pow v, intervalIntegral.integral_const_mul]
  rw [← integral_sval]
  ring

lemma pade_identity (m : ℕ) (hm : Odd m) :
    (125:ℤ)^(2*m+1)*sval m 3 128 - 128^(2*m+1)*sval m (-3) 125 =
      3^(2*m+1)*sval m 128 125 := by
  have h₁ := integral_piece m 3 (-(3^2)) 0 128 125 (by intro x; push_cast; ring)
  have h₂ := integral_piece m 125 (125^2) 3 3 128 (by intro x; push_cast; ring)
  have h₃ := integral_piece m 128 (128^2) 0 (-3) 125 (by intro x; push_cast; ring)
  norm_num only [zero_add, Nat.reduceAdd, show (3:ℝ)+125=128 by norm_num] at h₁ h₂ h₃
  have hc : Continuous (cubic m) := by unfold cubic; fun_prop
  have had := intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (μ:=volume) 0 3) (hc.intervalIntegrable (μ:=volume) 3 128)
  have h := congrArg (fun v : ℝ => normFactor m * v) had
  rw [mul_add, h₁, h₂, h₃, hm.neg_pow] at h
  exact_mod_cast (show (125:ℝ)^(2*m+1)*(sval m 3 128 : ℝ) -
      (128:ℝ)^(2*m+1)*(sval m (-3) 125 : ℝ) =
      (3:ℝ)^(2*m+1)*(sval m 128 125 : ℝ) by
    simp only [pow_succ, pow_mul]
    norm_num
    linarith)

lemma sval_pos (m : ℕ) (a b : ℤ) (ha : 0 < a) (hb : 0 < b) : 0 < sval m a b := by
  apply Finset.sum_pos
  · intro j hj
    have h := Finset.mem_range.mp hj
    have h1 := Nat.choose_pos (show m ≤ m+j by omega)
    have h2 := Nat.choose_pos (show m ≤ 2*m-j by omega)
    unfold scoef
    positivity
  · exact ⟨0, Finset.mem_range.mpr (by omega)⟩

lemma sval_bound (m : ℕ) (a b : ℤ) (ha : 0 ≤ a) (ha' : a ≤ 128)
    (hb : 0 ≤ b) (hb' : b ≤ 128) : sval m a b ≤ (m+1:ℤ)*1024^m := by
  unfold sval
  calc
    _ ≤ ∑ j ∈ Finset.range (m+1), (1024:ℤ)^m := by
      apply Finset.sum_le_sum
      intro j hj
      have hj' := Finset.mem_range.mp hj
      have hcoef : scoef m j ≤ 2^(3*m) := by
        unfold scoef
        calc
          _ ≤ 2^(m+j)*2^(2*m-j) := Nat.mul_le_mul (Nat.choose_le_two_pow ..) (Nat.choose_le_two_pow ..)
          _ = _ := by rw [← pow_add]; congr 1; omega
      calc
        _ ≤ (2:ℤ)^(3*m)*128^(m-j)*128^j := by
          gcongr; exact_mod_cast hcoef
        _ = _ := by
          rw [mul_assoc, ← pow_add, show m-j+j=m by omega, pow_mul, ← mul_pow]
          norm_num
    _ = _ := by simp

lemma geometric_bound (K u v : ℤ) (hK : 0 ≤ K) (hu : 0 < u) (hv : 3*u ≤ 2*v)
    (base : K * 101 * u^100 < v^100) (m : ℕ) (hm : 100 ≤ m) :
    K * (m+1:ℤ) * u^m < v^m := by
  induction m, hm using Nat.le_induction with
  | base => simpa using base
  | succ m hm ih =>
    push_cast
    rw [pow_succ, pow_succ]
    have hy : (1:ℤ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
    have fac : ((m:ℤ)+1+1)*u ≤ (m+1:ℤ)*v := by
      nlinarith only [mul_nonneg (sub_nonneg.mpr hy) hu.le,
        mul_nonneg (show (0:ℤ) ≤ m+1 by positivity) (sub_nonneg.mpr hv)]
    calc
      _ = (K*u^m)*(((m:ℤ)+1+1)*u) := by ring
      _ ≤ (K*u^m)*((m+1:ℤ)*v) := mul_le_mul_of_nonneg_left fac (by positivity)
      _ = (K*((m:ℤ)+1)*u^m)*v := by ring
      _ < _ := mul_lt_mul_of_pos_right ih (by omega)

lemma poly_error_bound (m : ℕ) (hm : 100 ≤ m) (T : ℤ) (_hT : 0 < T) (hMax : T ≤ 2^31) :
    2*T*3^(2*m+1)*sval m 128 125 < 125^(2*m+1) := by
  have hb := sval_bound m 128 125 (by decide) (by decide) (by decide) (by decide)
  have h := geometric_bound (6*2^31) 9216 15625 (by norm_num) (by decide)
    (by decide) (by decide) m hm
  calc
    _ ≤ 2*(2^31)*3^(2*m+1)*((m+1:ℤ)*1024^m) := by gcongr; exact (sval_pos m 128 125 (by decide) (by decide)).le
    _ = (6*2^31)*((m:ℤ)+1)*(9216:ℤ)^m := by
      rw [pow_succ (3:ℤ) (2*m), pow_mul]
      norm_num
      rw [show (9216:ℤ)=9*1024 by norm_num, mul_pow]; ring
    _ < _ := by
      rw [pow_succ (125:ℤ) (2*m), pow_mul]; norm_num
      linarith only [h, show 0 < (15625:ℤ)^m by positivity]

lemma poly_size_bound (m n : ℕ) (hm : 100 ≤ m) (hn : 20*m ≤ n)
    (T : ℤ) (_hT : 0 < T) (hMax : T ≤ 2^31) :
    4*T*sval m 3 128 * 2^n < 3^n := by
  have hb := sval_bound m 3 128 (by decide) (by decide) (by decide) (by decide)
  have h := geometric_bound (4*2^31) (1024*2^20) (3^20)
    (by norm_num) (by norm_num) (by norm_num) (by decide) m hm
  have hbase : 4*T*sval m 3 128 * 2^(20*m) < 3^(20*m) := by
    rw [pow_mul, pow_mul]
    rw [mul_pow] at h
    calc
      _ ≤ 4*(2^31)*((m+1:ℤ)*1024^m)*(2^20)^m := by gcongr; exact (sval_pos m 3 128 (by decide) (by decide)).le
      _ < _ := by linarith only [h]
  induction n, hn using Nat.le_induction with
  | base => exact hbase
  | succ n hn ih =>
    rw [pow_succ, pow_succ]
    linarith only [ih, show 0 < (3:ℤ)^n by positivity]

lemma pade_gap (m n : ℕ) (hm : Odd m) (hbig : 100 ≤ m) (hn : 20*m ≤ n)
    (T I : ℤ) (hT : 0 < T) (hMax : T ≤ 2^31) (hI : 0 < I)
    (hlt : I*125^(2*m+1) < T*128^(2*m+1)) :
    2*(I*125^(2*m+1))*2^n < (T*128^(2*m+1)-I*125^(2*m+1))*3^n := by
  let A : ℤ := 128^(2*m+1)
  let B : ℤ := 125^(2*m+1)
  let C : ℤ := 3^(2*m+1)*sval m 128 125
  let P := sval m (-3) 125
  let Q := sval m 3 128
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hQ : 0 < Q := sval_pos m 3 128 (by decide) (by decide)
  have hC : 0 < C := mul_pos (by positivity) (sval_pos m 128 125 (by decide) (by decide))
  have hid : B*Q-A*P=C := pade_identity m hm
  have err : 2*T*C < B := by dsimp [C,B]; linarith only [poly_error_bound m hbig T hT hMax]
  have size := poly_size_bound m n hbig hn T hT hMax
  change 4*T*Q*2^n < 3^n at size
  change I*B < T*A at hlt
  change 2*(I*B)*2^n < (T*A-I*B)*3^n
  have hpos : 0 < A*(T*Q-I*P) := by
    nlinarith only [mul_pos (sub_pos.mpr hlt) hQ, mul_pos hI hC, congrArg (I*·) hid]
  have hint : 1 ≤ T*Q-I*P := by have := pos_of_mul_pos_right hpos hA.le; omega
  have hsmall : 2*I*C < A := by
    apply lt_of_mul_lt_mul_left (a := T) _ hT.le
    nlinarith only [mul_lt_mul_of_pos_left err hI, hlt]
  have hgap : A < 2*(T*A-I*B)*Q := by
    nlinarith only [mul_le_mul_of_nonneg_left hint hA.le, hsmall, congrArg (I*·) hid]
  calc
    _ < 2*(T*A)*2^n := by gcongr
    _ < 4*T*Q*2^n*(T*A-I*B) := by
      nlinarith only [mul_lt_mul_of_pos_left hgap (show 0 < 2*T*2^n by positivity)]
    _ < _ := by
      nlinarith only [mul_lt_mul_of_pos_right size (sub_pos.mpr hlt)]

end RipaProof

namespace RipaProof

def decade (n : ℕ) := Nat.log 10 (5^n)
def nextDigit (n : ℕ) := 5^n / 10^(decade n) + 1
def upperBoundary (n : ℕ) := nextDigit n * 10^(decade n)

lemma decade_le (n : ℕ) : 10^(decade n) ≤ 5^n := Nat.pow_log_le_self _ (by positivity)
lemma lt_next_decade (n : ℕ) : 5^n < 10^(decade n+1) := Nat.lt_pow_succ_log_self (by decide) _
lemma upper_lt (n : ℕ) : 5^n < upperBoundary n := by
  simpa only [upperBoundary,nextDigit,Nat.mul_comm (10^decade n)] using
    Nat.lt_mul_div_succ (5^n) (by positivity : 0<10^decade n)
lemma digit_le (n : ℕ) : nextDigit n ≤ 10 := by
  have h := lt_next_decade n
  rw [pow_succ, mul_comm] at h
  have := (Nat.div_lt_iff_lt_mul (show 0<10^decade n by positivity)).mpr h
  unfold nextDigit
  omega

lemma large_gap (n : ℕ) (hn : 5000 ≤ n) :
    (3^(n+1)+4*2^n)*5^n < 3^(n+1)*upperBoundary n := by
  let e := decade n
  let k := n-e
  have h₀ : 10^e ≤ 5^n := decade_le n
  have h₁ : 5^n < 10^(e+1) := lt_next_decade n
  have he : e ≤ n := (Nat.pow_le_pow_iff_right (by decide : 1 < 10)).mp
    (h₀.trans (Nat.pow_le_pow_left (by decide : 5 ≤ 10) n))
  have hen : n < 2*(e+1) := by
    apply (Nat.pow_lt_pow_iff_right (by decide : 1 < 10)).mp
    calc
      10^n ≤ (5^2)^n := Nat.pow_le_pow_left (by decide) _
      _ = (5^n)^2 := by rw [← pow_mul, Nat.mul_comm 2 n, pow_mul]
      _ < (10^(e+1))^2 := Nat.pow_lt_pow_left h₁ (by decide)
      _ = _ := by rw [← pow_mul, Nat.mul_comm (e+1) 2]
  have hk : 2^e ≤ 5^k := by
    have h : 5^e * 2^e ≤ 5^e * 5^k := by
      rw [← mul_pow, ← pow_add, show e+k=n by dsimp [k]; omega]
      exact h₀
    exact Nat.le_of_mul_le_mul_left h (by positivity)
  have hk' : 3*e ≤ 7*k := by
    apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    rw [Nat.mul_comm 3 e, pow_mul, pow_mul]
    exact (Nat.pow_le_pow_left hk 3).trans (by
      rw [← pow_mul, Nat.mul_comm k 3, pow_mul]
      exact Nat.pow_le_pow_left (by decide) _)
  let m := 2*((e-21)/28)+1
  let h := 2*m+1
  let u := (e-21)%28
  have heq : e=7*h+u := by dsimp [u,h,m]; omega
  have hu : u ≤ 27 := by dsimp [u]; omega
  have hk3 : 3*h ≤ k := by omega
  have hbig : 100 ≤ m := by dsimp [m]; omega
  have hn20 : 20*m ≤ n := by dsimp [h,k] at *; omega
  let T := (nextDigit n : ℤ)*2^u
  let I := (5 : ℤ)^(k-3*h)
  have hT : 0 < T := by dsimp [T,nextDigit]; positivity
  have hMax : T ≤ 2^31 := by
    have hD : (nextDigit n : ℤ) ≤ 10 := by exact_mod_cast digit_le n
    calc
      _ ≤ 10*(2:ℤ)^27 := by
        exact mul_le_mul hD (pow_le_pow_right₀ (by norm_num : (1:ℤ) ≤ 2) hu) (by positivity) (by decide)
      _ ≤ _ := by decide
  have hI : 0 < I := by dsimp [I]; positivity
  have hB : (5:ℤ)^n = 5^e*(I*125^h) := by
    dsimp [I]
    rw [show (125:ℤ)=5^3 by norm_num, ← pow_mul, ← pow_add, ← pow_add]
    congr 1; dsimp [k] at *; omega
  have hA : (upperBoundary n : ℤ) = 5^e*(T*128^h) := by
    dsimp [upperBoundary,T]
    rw [show (128:ℤ)=2^7 by norm_num, ← pow_mul, show (10:ℤ)=5*2 by norm_num, mul_pow]
    have hd : (2:ℤ)^e = 2^u*2^(7*h) := by rw [← pow_add]; congr 1; omega
    rw [hd]; ring
  have hlt : I*125^h<T*128^h := by
    have hl : (5:ℤ)^n < (upperBoundary n:ℤ) := by exact_mod_cast upper_lt n
    rw [hB,hA] at hl
    exact lt_of_mul_lt_mul_left hl (by positivity)
  have large := pade_gap m n ⟨(e-21)/28, by rfl⟩ hbig hn20 T I hT hMax hI hlt
  change 2*(I*125^h)*2^n < (T*128^h-I*125^h)*3^n at large
  have target : ((3:ℤ)^(n+1)+4*2^n)*5^n < 3^(n+1)*(upperBoundary n:ℤ) := by
    rw [hB,hA,pow_succ]
    nlinarith only [mul_lt_mul_of_pos_left large (show 0<(5:ℤ)^e by positivity),
      show 0 < (5:ℤ)^e*(I*125^h)*2^n by positivity]
  exact_mod_cast target

def digitTest (n : ℕ) : Bool :=
  decide ((3^(n+1)+4*2^n)*5^n < 3^(n+1)*upperBoundary n)

def digitBlock : ℕ → ℕ → Bool
  | 0, _ => true
  | k+1, n => digitTest n && digitBlock k (n+1)

lemma block_sound (k n i : ℕ) (hb : digitBlock k n = true) (hl : n ≤ i) (hu : i < n+k) :
    digitTest i = true := by
  induction k generalizing n with
  | zero => omega
  | succ k ih =>
    obtain ⟨h₁,h₂⟩ := Bool.and_eq_true_iff.mp hb
    by_cases he : i=n
    · simpa [he] using h₁
    · exact ih (n+1) h₂ (by omega) (by omega)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
lemma small_certificate : digitBlock 4990 10 = true := by decide +kernel

lemma full_gap (n : ℕ) (hn : 10 ≤ n) :
    (3^(n+1)+4*2^n)*5^n < 3^(n+1)*upperBoundary n := by
  by_cases h : 5000 ≤ n
  · exact large_gap n h
  · exact of_decide_eq_true (block_sound _ _ n small_certificate hn (by omega))

end RipaProof

namespace RipaProof
open OMA.S_mse_5079681

lemma zeta_bounds (n : ℕ) (hn : 10 ≤ n) :
    ((2:ℝ)⁻¹)^n ≤ P n ∧ P n ≤ ((2:ℝ)⁻¹)^n + (4/3)*((3:ℝ)⁻¹)^n := by
  let a (j : ℕ) := ((j:ℝ)⁻¹)^n
  let f (x : ℝ) := x^(-(n:ℝ))
  have hn' : (10:ℝ) ≤ n := by exact_mod_cast hn
  have hexp : -(n:ℝ) < -1 := by linarith
  have agree (j : ℕ) : a j = f j := by
    simp [a,f,inv_pow]
  have ha : Summable a := (Real.summable_nat_rpow.mpr hexp).congr fun j => (agree j).symm
  have hp : Summable (fun p : {p : ℕ // p.Prime} => a p.val) :=
    ha.comp_injective Subtype.val_injective
  have hshift : Summable (fun j : ℕ => a (j+2)) := (summable_nat_add_iff 2).mpr ha
  let e (p : {p : ℕ // p.Prime}) := p.val - 2
  have he (p : {p : ℕ // p.Prime}) : e p+2 = p.val := Nat.sub_add_cancel p.property.two_le
  have hi : Function.Injective e := by
    intro p q heq
    apply Subtype.ext
    rw [← he p, ← he q, heq]
  have upper : P n ≤ ∑' j : ℕ, a (j+2) := by
    apply hp.tsum_le_tsum_of_inj e hi (fun c _ => by dsimp [a]; positivity) _ hshift
    intro p; rw [he]
  constructor
  · exact hp.le_tsum ⟨2,by decide⟩ (fun j _ => by dsimp [a]; positivity)
  have anti : AntitoneOn f (Set.Ici (3:ℝ)) := by
    intro x hx y _ hxy
    apply Real.rpow_le_rpow_of_nonpos _ hxy (by linarith)
    exact lt_of_lt_of_le (by norm_num : (0:ℝ)<3) hx
  have htail := anti.tsum_comp_add_le_integral 3
    (integrableOn_Ioi_rpow_of_lt hexp (by norm_num)) (fun t ht => Real.rpow_nonneg (by
      exact (lt_trans (by norm_num : (0:ℝ)<3) ht).le) _)
  rw [integral_Ioi_rpow_of_lt hexp (by norm_num)] at htail
  have hval : -((3:ℝ)^(-(n:ℝ)+1))/(-(n:ℝ)+1) ≤ (1/3)*a 3 := by
    rw [Real.rpow_add (by norm_num : (0:ℝ)<3), Real.rpow_one,
      Real.rpow_neg (by norm_num : (0:ℝ)≤3), Real.rpow_natCast]
    dsimp [a]
    rw [inv_pow]
    apply (div_le_iff_of_neg (by linarith : -(n:ℝ)+1<0)).mpr
    nlinarith only [mul_nonneg (sub_nonneg.mpr hn') (show 0≤((3:ℝ)^n)⁻¹ by positivity)]
  have ht : (∑' j : ℕ, a (j+2+2)) ≤ (1/3)*a 3 := by
    calc
      _ = ∑' j : ℕ, f ↑(j+3+1) := by
        apply tsum_congr; intro j; rw [agree]
      _ ≤ _ := htail.trans hval
  have split := hshift.sum_add_tsum_nat_add 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at split
  change a 2+a 3+(∑' j : ℕ, a (j+2+2)) = _ at split
  change P n ≤ a 2+ (4/3)*a 3
  linarith only [upper, ht, split]

end RipaProof

namespace RipaProof
open OMA.S_mse_5079681

lemma digit_interval {x : ℝ} {k : ℤ} {a : ℕ} (ha : 1 ≤ a) (hb : a < 10)
    (hl : (a:ℝ)*10^k ≤ x) (hu : x < ((a:ℝ)+1)*10^k) : ld x = (a:ℤ) := by
  have hp : 0 < (10:ℝ)^k := by positivity
  have ha' : (1:ℝ) ≤ a := by exact_mod_cast ha
  have hb' : (a:ℝ)+1 ≤ 10 := by exact_mod_cast Nat.succ_le_of_lt hb
  have hl' : (10:ℝ)^k ≤ x := le_trans (by simpa using mul_le_mul_of_nonneg_right ha' hp.le) hl
  have hx := hp.trans_le hl'
  have hf : ⌊Real.logb 10 x⌋ = k := by
    apply Int.floor_eq_iff.mpr
    constructor
    · apply (Real.le_logb_iff_rpow_le (by norm_num) hx).mpr
      simpa using hl'
    · apply (Real.logb_lt_iff_lt_rpow (by norm_num) hx).mpr
      rw [Real.rpow_add (by norm_num : (0:ℝ)<10), Real.rpow_intCast, Real.rpow_one]
      exact hu.trans_le (by simpa [mul_comm] using mul_le_mul_of_nonneg_right hb' hp.le)
  unfold ld
  rw [hf, Int.floor_eq_iff]
  push_cast
  exact ⟨(le_div_iff₀ hp).mpr hl, (div_lt_iff₀ hp).mpr hu⟩

lemma scaled_bounds (n : ℕ) (hn : 10 ≤ n) :
    (5:ℝ)^n ≤ 10^n*P n ∧ (10:ℝ)^n*P n < upperBoundary n := by
  obtain ⟨lower,upper⟩ := zeta_bounds n hn
  have hp : 0 < (10:ℝ)^n := by positivity
  have eq₅ : (10:ℝ)^n*((2:ℝ)⁻¹)^n=5^n := by rw [← mul_pow]; norm_num
  constructor
  · rw [← eq₅]; exact mul_le_mul_of_nonneg_left lower hp.le
  apply lt_of_le_of_lt (mul_le_mul_of_nonneg_left upper hp.le)
  rw [mul_add, eq₅, mul_left_comm, ← mul_pow]
  have h : ((3:ℝ)^(n+1)+4*2^n)*5^n < 3^(n+1)*(upperBoundary n:ℝ) := by
    exact_mod_cast full_gap n hn
  rw [pow_succ] at h
  rw [show (10:ℝ)*3⁻¹=5*2/3 by norm_num, div_pow, mul_pow]
  apply (lt_of_mul_lt_mul_right _ (by positivity : 0 ≤ (3:ℝ)^n))
  field_simp
  nlinarith only [h]

end RipaProof

open RipaProof OMA.S_mse_5079681 in
theorem OMA.solution : type_of% @OMA.S_mse_5079681.main := by
  intro n hn
  let e := decade n
  let a := 5^n / 10^e
  have hpos : 0 < 10^e := by positivity
  have ha : 1 ≤ a := (Nat.le_div_iff_mul_le hpos).mpr (by simpa [e] using decade_le n)
  have hb : a < 10 := by
    have h := digit_le n
    change a+1 ≤ 10 at h
    omega
  have h₁ : (a:ℝ)*10^e ≤ (5:ℝ)^n := by exact_mod_cast Nat.div_mul_le_self (5^n) (10^e)
  have h₂ : (upperBoundary n:ℝ) = ((a:ℝ)+1)*10^e := by simp [upperBoundary,nextDigit,a,e]
  obtain ⟨lower,upper⟩ := scaled_bounds n hn
  have hbnd : (5:ℝ)^n < (upperBoundary n:ℝ) := by exact_mod_cast upper_lt n
  rw [h₂] at upper hbnd
  have right := digit_interval (k:=(e:ℤ)) ha hb (by simpa using h₁) (by simpa using hbnd)
  rw [right]
  apply digit_interval (k:=(e:ℤ)-(n:ℤ)) ha hb
  · rw [zpow_sub₀ (by norm_num), zpow_natCast, zpow_natCast, ← mul_div_assoc]
    exact (div_le_iff₀ (by positivity)).mpr (by simpa [mul_comm] using h₁.trans lower)
  · rw [zpow_sub₀ (by norm_num), zpow_natCast, zpow_natCast, ← mul_div_assoc]
    exact (lt_div_iff₀ (by positivity)).mpr (by simpa [mul_comm] using upper)
