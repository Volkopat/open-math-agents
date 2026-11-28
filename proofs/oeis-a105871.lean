import OMAStatements.S_oeis_a105871

-- Credit: @CubeJerry (the owner of the agent is credited as the solver)

/-!
A finite creative-telescoping proof of Mathar's recurrence for A105871.
The original binomial product vanishes beyond 3*k <= n. Exact forward and
backward ratios connect the seven summands in the recurrence to a rational
Gosper certificate. Its sum telescopes to zero at both endpoints. The proof
handles zero summands separately and checks the six initial indices directly.
-/

namespace OMA.T105871

def fall (x : ℚ) : ℕ → ℚ
  | 0 => 1
  | m+1 => fall x m * (x-m)

def p0 (n : ℚ) : ℚ := 15*n^3 - 65*n^2 + 50*n
def p1 (n : ℚ) : ℚ := -63*n^3 + 252*n^2 - 129*n - 60
def p2 (n : ℚ) : ℚ := -9*n^3 + 321*n^2 - 1338*n + 1332
def p3 (n : ℚ) : ℚ := 3*n^3 - 259*n^2 + 1279*n - 1575
def p4 (n : ℚ) : ℚ := -63*n^3 + 630*n^2 - 2019*n + 2082
def p5 (n : ℚ) : ℚ := -9*n^3 + 51*n^2 - 51*n - 63
def p6 (n : ℚ) : ℚ := -12*n^3 + 130*n^2 - 454*n + 504

def back (n k : ℚ) : ℚ :=
  n*(n-3*k)*(n-2*k)/((2*n-3*k)*(2*n-3*k-1)*(n-k))

def right (n k : ℚ) : ℚ :=
  (n-3*k)*(n-3*k-1)*(n-3*k-2)*(n-2*k)*(n-2*k-1)/
    ((2*n-3*k)*(2*n-3*k-1)*(2*n-3*k-2)*(n-k)*(k+1))

def certPoly (n k : ℚ) : ℚ :=
  ((((((((((((((-19683*n*(n - 1)*(3*n - 10))) * k + (19683*n*(n - 1)*(27*n^2 - 160*n + 232))) * k + (-6561*n*(n - 1)*(318*n^3 - 2714*n^2 + 7587*n - 6930))) * k + (2187*n*(n - 1)*(2088*n^4 - 23502*n^3 + 97263*n^2 - 175006*n + 115268))) * k + (-729*n*(n - 1)*(7707*n^5 - 110890*n^4 + 619967*n^3 - 1682470*n^2 + 2213539*n - 1127282))) * k + (243*n*(n - 1)*(9945*n^6 - 209706*n^5 + 1653341*n^4 - 6445160*n^3 + 13284517*n^2 - 13797812*n + 5639312))) * k + (27*n*(n - 1)*(151767*n^7 - 2067102*n^6 + 11294334*n^5 - 31623090*n^4 + 48654801*n^3 - 43295514*n^2 + 26550885*n - 11689126))) * k + (-27*n*(n - 1)*(334125*n^8 - 6172713*n^7 + 49367820*n^6 - 224053266*n^5 + 634352771*n^4 - 1154669759*n^3 + 1328522179*n^2 - 888190846*n + 264723548))) * k + (9*n*(n - 1)*(1000080*n^9 - 21425481*n^8 + 201883929*n^7 - 1099296912*n^6 + 3817343805*n^5 - 8780087909*n^4 + 13395305408*n^3 - 13084046638*n^2 + 7424171752*n - 1861500432))) * k + (-9*n*(n - 1)*(622296*n^10 - 14950860*n^9 + 159704019*n^8 - 998812583*n^7 + 4050112153*n^6 - 11124156490*n^5 + 20949738026*n^4 - 26684942029*n^3 + 21958581492*n^2 - 10504102748*n + 2204851488))) * k + (3*n*(n - 1)*(762075*n^11 - 20178810*n^10 + 239543913*n^9 - 1681682817*n^8 + 7750848091*n^7 - 24596514368*n^6 + 54746764495*n^5 - 85256409113*n^4 + 90693220258*n^3 - 62397219356*n^2 + 24750714360*n - 4217167296))) * k + (-9*n*(n - 1)*(66501*n^12 - 1917885*n^11 + 24961225*n^10 - 193632145*n^9 + 995612405*n^8 - 3567633409*n^7 + 9111219169*n^6 - 16647083597*n^5 + 21480230468*n^4 - 18933891388*n^3 + 10681053456*n^2 - 3383893792*n + 434768640))) * k + (3*n*(n - 4)*(n - 3)*(n - 2)*(n - 1)*(30516*n^10 - 675343*n^9 + 6545421*n^8 - 36443910*n^7 + 128394434*n^6 - 296717223*n^5 + 450044905*n^4 - 433776204*n^3 + 245627964*n^2 - 68828000*n + 6048000))) * k + (-4*n^2*(n - 4)^2*(n - 3)^2*(n - 2)^2*(n - 1)^2*(1560*n^6 - 22405*n^5 + 129868*n^4 - 384915*n^3 + 602582*n^2 - 449090*n + 105000))

def R (n k : ℚ) : ℚ :=
  k*certPoly n k/(fall (2*n-3*k) 9 * fall (n-k) 5)

def D (n k : ℚ) : ℚ := fall (2*n-3*k) 12 * fall (n-k) 6

def termNum (n k : ℚ) (i : ℕ) : ℚ :=
  fall n i * fall (n-3*k) i * fall (n-2*k) i *
    fall (2*n-3*k-2*i) (12-2*i) * fall (n-k-i) (6-i)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
lemma poly_cert (n k : ℚ) :
  fall (n-3*k) 3 * fall (n-2*k) 2 * certPoly n (k+1) -
    k*fall (2*n-3*k-9) 3*(n-k-5)*certPoly n k =
    p0 n * termNum n k 0 +
    p1 n * termNum n k 1 +
    p2 n * termNum n k 2 +
    p3 n * termNum n k 3 +
    p4 n * termNum n k 4 +
    p5 n * termNum n k 5 +
    p6 n * termNum n k 6 := by
  unfold certPoly termNum p0 p1 p2 p3 p4 p5 p6
  norm_num only [fall]
  ring


lemma fall_add (x : ℚ) (a b : ℕ) :
    fall x (a+b) = fall x a * fall (x-a) b := by
  induction b with
  | zero => simp [fall]
  | succ b ih =>
    rw [show a+(b+1) = (a+b)+1 by omega, fall, ih, fall]
    push_cast
    ring

lemma fall_pos (x : ℚ) (m : ℕ) (hm : (m : ℚ) ≤ x) : 0 < fall x m := by
  induction m with
  | zero => norm_num [fall]
  | succ m ih =>
    have hm' : (m : ℚ)+1 ≤ x := by exact_mod_cast hm
    rw [fall]
    exact mul_pos (ih (by linarith)) (by linarith)

lemma D_pos (n k : ℚ) (hn : 12 ≤ n) (_hk : 0 ≤ k) (hkn : 3*k ≤ n) :
    0 < D n k := by
  unfold D
  exact mul_pos (fall_pos _ 12 (by norm_num; linarith))
    (fall_pos _ 6 (by norm_num; linarith))

def rowRatio (n k : ℚ) : ℕ → ℚ
  | 0 => 1
  | i+1 => rowRatio n k i * back (n-i) k

set_option maxHeartbeats 4000000 in
lemma rowRatio_formula (n k : ℚ) (i : ℕ) (hi : i ≤ 6)
    (hn : 12 ≤ n) (_hk : 0 ≤ k) (hkn : 3*k ≤ n) :
    rowRatio n k i =
      fall n i * fall (n-3*k) i * fall (n-2*k) i /
        (fall (2*n-3*k) (2*i) * fall (n-k) i) := by
  induction i with
  | zero => norm_num [rowRatio, fall]
  | succ i ih =>
    have hiq : (i : ℚ) ≤ 5 := by exact_mod_cast (show i ≤ 5 by omega)
    have ht : 0 < fall (2*n-3*k) (2*i) :=
      fall_pos _ _ (by push_cast; linarith)
    have hu : 0 < fall (n-k) i := fall_pos _ _ (by linarith)
    rw [rowRatio, ih (by omega)]
    rw [show 2*(i+1) = 2*i+1+1 by omega]
    simp only [fall]
    unfold back
    push_cast
    field_simp (disch := first | positivity | linarith)
    ring

set_option maxHeartbeats 4000000 in
lemma termNum_div_D (n k : ℚ) (i : ℕ) (hi : i ≤ 6)
    (hn : 12 ≤ n) (hk : 0 ≤ k) (hkn : 3*k ≤ n) :
    termNum n k i / D n k = rowRatio n k i := by
  have hiq : (i : ℚ) ≤ 6 := by exact_mod_cast hi
  have ht : 0 < fall (2*n-3*k) (2*i) :=
    fall_pos _ _ (by push_cast; linarith)
  have hu : 0 < fall (n-k) i := fall_pos _ _ (by linarith)
  have ht' : 0 < fall (2*n-3*k-2*i) (12-2*i) := by
    apply fall_pos
    rw [Nat.cast_sub (by omega : 2*i ≤ 12)]
    push_cast
    linarith
  have hu' : 0 < fall (n-k-i) (6-i) := by
    apply fall_pos
    rw [Nat.cast_sub hi]
    push_cast
    linarith
  have et := fall_add (2*n-3*k) (2*i) (12-2*i)
  have eu := fall_add (n-k) i (6-i)
  rw [show 2*i+(12-2*i)=12 by omega] at et
  rw [show i+(6-i)=6 by omega] at eu
  push_cast at et
  rw [rowRatio_formula n k i hi hn hk hkn]
  unfold termNum D
  rw [et, eu]
  have cancel (a b c d e : ℚ) (hb : b ≠ 0) (hc : c ≠ 0)
      (hd : d ≠ 0) (he : e ≠ 0) :
      a*d*e/((b*d)*(c*e)) = a/(b*c) := by
    field_simp
  exact cancel _ _ _ _ _ ht.ne' hu.ne' ht'.ne' hu'.ne'

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
lemma left_cert (n k : ℚ) (hn : 12 ≤ n) (hk : 0 ≤ k) (hkn : 3*k ≤ n) :
    right n k * R n (k+1) - R n k =
      (fall (n-3*k) 3 * fall (n-2*k) 2 * certPoly n (k+1) -
        k*fall (2*n-3*k-9) 3*(n-k-5)*certPoly n k) / D n k := by
  unfold right R D
  norm_num only [fall]
  rw [show 2*n-3*(k+1)=2*n-3*k-3 by ring]
  rw [show n-(k+1)=n-k-1 by ring]
  rw [show 2*n-3*k-3-1=2*n-3*k-4 by ring]
  rw [show 2*n-3*k-3-2=2*n-3*k-5 by ring]
  rw [show 2*n-3*k-3-3=2*n-3*k-6 by ring]
  rw [show 2*n-3*k-3-4=2*n-3*k-7 by ring]
  rw [show 2*n-3*k-3-5=2*n-3*k-8 by ring]
  rw [show 2*n-3*k-3-6=2*n-3*k-9 by ring]
  rw [show 2*n-3*k-3-7=2*n-3*k-10 by ring]
  rw [show 2*n-3*k-3-8=2*n-3*k-11 by ring]
  rw [show n-k-1-1=n-k-2 by ring]
  rw [show n-k-1-2=n-k-3 by ring]
  rw [show n-k-1-3=n-k-4 by ring]
  rw [show n-k-1-4=n-k-5 by ring]
  field_simp (disch := linarith)
  ring



lemma cert_rows (n k : ℚ) (hn : 12 ≤ n) (hk : 0 ≤ k) (hkn : 3*k ≤ n) :
    right n k * R n (k+1) - R n k =
      p0 n * rowRatio n k 0 +
      p1 n * rowRatio n k 1 +
      p2 n * rowRatio n k 2 +
      p3 n * rowRatio n k 3 +
      p4 n * rowRatio n k 4 +
      p5 n * rowRatio n k 5 +
      p6 n * rowRatio n k 6 := by
  rw [left_cert n k hn hk hkn, poly_cert]
  simp only [add_div, mul_div_assoc]
  rw [termNum_div_D n k 0 (by omega) hn hk hkn,
    termNum_div_D n k 1 (by omega) hn hk hkn,
    termNum_div_D n k 2 (by omega) hn hk hkn,
    termNum_div_D n k 3 (by omega) hn hk hkn,
    termNum_div_D n k 4 (by omega) hn hk hkn,
    termNum_div_D n k 5 (by omega) hn hk hkn,
    termNum_div_D n k 6 (by omega) hn hk hkn]

lemma certQ (n k : ℚ) (hn : 12 ≤ n) (hk : 0 ≤ k) (hkn : 3*k ≤ n) :
    right n k * R n (k+1) - R n k =
      p0 n + p1 n * back n k +
      p2 n * back n k * back (n-1) k +
      p3 n * back n k * back (n-1) k * back (n-2) k +
      p4 n * back n k * back (n-1) k * back (n-2) k * back (n-3) k +
      p5 n * back n k * back (n-1) k * back (n-2) k * back (n-3) k * back (n-4) k +
      p6 n * back n k * back (n-1) k * back (n-2) k * back (n-3) k * back (n-4) k * back (n-5) k := by
  rw [cert_rows n k hn hk hkn]
  norm_num only [rowRatio]
  ring

lemma cert (n k : ℕ) (hn : 12 ≤ n) (hk : 3*k ≤ n) :
    right n k * R n ((k : ℚ)+1) - R n k =
      p0 n + p1 n * back n k +
      p2 n * back n k * back ((n : ℚ)-1) k +
      p3 n * back n k * back ((n : ℚ)-1) k * back ((n : ℚ)-2) k +
      p4 n * back n k * back ((n : ℚ)-1) k * back ((n : ℚ)-2) k * back ((n : ℚ)-3) k +
      p5 n * back n k * back ((n : ℚ)-1) k * back ((n : ℚ)-2) k * back ((n : ℚ)-3) k * back ((n : ℚ)-4) k +
      p6 n * back n k * back ((n : ℚ)-1) k * back ((n : ℚ)-2) k * back ((n : ℚ)-3) k * back ((n : ℚ)-4) k * back ((n : ℚ)-5) k := by
  exact certQ n k (by exact_mod_cast hn) (by positivity) (by exact_mod_cast hk)

end OMA.T105871

namespace OMA.T105871

noncomputable def F (n k : ℕ) : ℚ :=
  ((2*n-3*k).choose n : ℚ) * ((n-k).choose k : ℚ)

lemma F_zero_of_lt (n k : ℕ) (h : n < 3*k) : F n k = 0 := by
  by_cases hn : n = 0
  · subst n
    have hk : 0 < k := by omega
    simp [F, Nat.choose_eq_zero_of_lt hk]
  · have htop : 2*n-3*k < n := by omega
    simp [F, Nat.choose_eq_zero_of_lt htop]

lemma choose_rat (n k : ℕ) (hk : k ≤ n) :
    (n.choose k : ℚ) = (n.factorial : ℚ) /
      ((k.factorial : ℚ) * ((n-k).factorial : ℚ)) := by
  apply (eq_div_iff (by positivity)).2
  have h := Nat.choose_mul_factorial_mul_factorial hk
  exact_mod_cast (by simpa [mul_assoc] using h)

lemma F_factorial (n k : ℕ) (hk : 3*k ≤ n) :
    F n k = ((2*n-3*k).factorial : ℚ) * ((n-k).factorial : ℚ) /
      ((n.factorial : ℚ) * ((n-3*k).factorial : ℚ) * (k.factorial : ℚ) *
        ((n-2*k).factorial : ℚ)) := by
  rw [F, choose_rat (2*n-3*k) n (by omega), choose_rat (n-k) k (by omega)]
  rw [show 2*n-3*k-n = n-3*k by omega, show n-k-k = n-2*k by omega]
  ring

lemma repr (n : ℕ) :
    (OMA.S_oeis_a105871.a n : ℚ) = ∑ k ∈ Finset.range (n+1), F n k := by
  unfold OMA.S_oeis_a105871.a
  push_cast
  change (∑ k ∈ Finset.range (n/2+1), F n k) = _
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro k hk hkn
  simp only [Finset.mem_range, not_lt] at hkn
  exact F_zero_of_lt n k (by omega)

lemma fact_step (m : ℕ) (hm : 1 ≤ m) :
    (m.factorial : ℚ) = (m : ℚ) * ((m-1).factorial : ℚ) := by
  conv_lhs => rw [show m = m-1+1 by omega]
  rw [Nat.factorial_succ]
  push_cast [Nat.cast_sub hm]
  ring

lemma backF (n k : ℕ) (hn : 1 ≤ n) : F (n-1) k = F n k * back n k := by
  by_cases hk : 3*k ≤ n-1
  · rw [F_factorial (n-1) k hk, F_factorial n k (by omega)]
    have he0 : 2*(n-1)-3*k = 2*n-3*k-2 := by omega
    have he1 : n-1-k = n-k-1 := by omega
    have he2 : n-1-3*k = n-3*k-1 := by omega
    have he3 : n-1-2*k = n-2*k-1 := by omega
    rw [he0,he1,he2,he3]
    have hf : ((2*n-3*k).factorial : ℚ) =
        (2*(n:ℚ)-3*k)*(2*(n:ℚ)-3*k-1)*((2*n-3*k-2).factorial : ℚ) := by
      rw [fact_step (2*n-3*k) (by omega), fact_step (2*n-3*k-1) (by omega)]
      rw [show 2*n-3*k-1-1=2*n-3*k-2 by omega]
      push_cast [Nat.cast_sub (show 3*k ≤ 2*n by omega), Nat.cast_sub (show 1 ≤ 2*n-3*k by omega)]
      ring
    rw [hf, fact_step (n-k) (by omega), fact_step n hn,
      fact_step (n-3*k) (by omega), fact_step (n-2*k) (by omega)]
    unfold back
    push_cast [Nat.cast_sub (show k ≤ n by omega), Nat.cast_sub (show 3*k ≤ n by omega),
      Nat.cast_sub (show 2*k ≤ n by omega)]
    have hnq : (1:ℚ) ≤ n := by exact_mod_cast hn
    have hkq : 3*(k:ℚ) ≤ (n:ℚ)-1 := by
      exact_mod_cast (show 3*k ≤ n-1 from hk)
    field_simp (disch := first | positivity | linarith)
    <;> ring
  · rw [F_zero_of_lt (n-1) k (by omega)]
    by_cases hk' : n < 3*k
    · rw [F_zero_of_lt n k hk']
      simp
    · have he : n = 3*k := by omega
      have heq : (n:ℚ) = 3*(k:ℚ) := by exact_mod_cast he
      simp [back, heq]


lemma fact_two_step (m : ℕ) (hm : 2 ≤ m) :
    (m.factorial : ℚ) = (m:ℚ)*((m:ℚ)-1)*((m-2).factorial : ℚ) := by
  rw [fact_step m (by omega), fact_step (m-1) (by omega)]
  rw [show m-1-1=m-2 by omega]
  push_cast [Nat.cast_sub (show 1 ≤ m by omega)]
  ring

lemma fact_three_step (m : ℕ) (hm : 3 ≤ m) :
    (m.factorial : ℚ) = (m:ℚ)*((m:ℚ)-1)*((m:ℚ)-2)*((m-3).factorial : ℚ) := by
  rw [fact_two_step m (by omega), fact_step (m-2) (by omega)]
  rw [show m-2-1=m-3 by omega]
  push_cast [Nat.cast_sub (show 2 ≤ m by omega)]
  ring

lemma rightF (n k : ℕ) : F n (k+1) = F n k * right n k := by
  by_cases hk : 3*(k+1) ≤ n
  · rw [F_factorial n (k+1) hk, F_factorial n k (by omega)]
    rw [show 2*n-3*(k+1)=2*n-3*k-3 by omega,
      show n-(k+1)=n-k-1 by omega,
      show n-3*(k+1)=n-3*k-3 by omega,
      show n-2*(k+1)=n-2*k-2 by omega]
    rw [fact_three_step (2*n-3*k) (by omega), fact_step (n-k) (by omega),
      fact_three_step (n-3*k) (by omega), fact_two_step (n-2*k) (by omega),
      Nat.factorial_succ k]
    unfold right
    push_cast [Nat.cast_sub (show 3*k ≤ 2*n by omega), Nat.cast_sub (show k ≤ n by omega),
      Nat.cast_sub (show 3*k ≤ n by omega), Nat.cast_sub (show 2*k ≤ n by omega)]
    have hnq : 3*((k:ℚ)+1) ≤ n := by exact_mod_cast hk
    have hkq : (0:ℚ) ≤ k := by positivity
    field_simp (disch := first | positivity | linarith)
    <;> ring
  · rw [F_zero_of_lt n (k+1) (by omega)]
    by_cases hk' : n < 3*k
    · rw [F_zero_of_lt n k hk']
      simp
    · have hcases : n=3*k ∨ n=3*k+1 ∨ n=3*k+2 := by omega
      have hr : right (n:ℚ) k = 0 := by
        rcases hcases with h | h | h
        · have he : (n:ℚ)-3*k=0 := by exact_mod_cast (show (n:ℤ)-3*k=0 by omega)
          simp [right,he]
        · have he : (n:ℚ)-3*k=1 := by exact_mod_cast (show (n:ℤ)-3*k=1 by omega)
          simp [right,he]
        · have he : (n:ℚ)-3*k=2 := by exact_mod_cast (show (n:ℤ)-3*k=2 by omega)
          simp [right,he]
      rw [hr,mul_zero]

end OMA.T105871

namespace OMA.T105871

open scoped BigOperators

lemma sum_extend_zero (t : ℕ → ℕ → ℚ)
    (hz : ∀ m k : ℕ, m < k → t m k = 0)
    (m N : ℕ) (hm : m ≤ N) :
    (∑ k ∈ Finset.range (N + 1), t m k) =
      ∑ k ∈ Finset.range (m + 1), t m k := by
  symm
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro k hk hkm
  apply hz
  simp only [Finset.mem_range, not_lt] at hkm
  omega

lemma sum_certificate7 (t : ℕ → ℕ → ℚ)
    (hz : ∀ m k : ℕ, m < k → t m k = 0)
    (n : ℕ) (c0 c1 c2 c3 c4 c5 c6 : ℚ) (G : ℕ → ℚ)
    (hG0 : G 0 = 0) (hG1 : G (n + 1) = 0)
    (hcert : ∀ k : ℕ, k ≤ n →
      c0 * t n k +
      c1 * t (n - 1) k +
      c2 * t (n - 2) k +
      c3 * t (n - 3) k +
      c4 * t (n - 4) k +
      c5 * t (n - 5) k +
      c6 * t (n - 6) k = G (k + 1) - G k) :
    c0 * (∑ k ∈ Finset.range (n + 1), t n k) +
      c1 * (∑ k ∈ Finset.range (n - 1 + 1), t (n - 1) k) +
      c2 * (∑ k ∈ Finset.range (n - 2 + 1), t (n - 2) k) +
      c3 * (∑ k ∈ Finset.range (n - 3 + 1), t (n - 3) k) +
      c4 * (∑ k ∈ Finset.range (n - 4 + 1), t (n - 4) k) +
      c5 * (∑ k ∈ Finset.range (n - 5 + 1), t (n - 5) k) +
      c6 * (∑ k ∈ Finset.range (n - 6 + 1), t (n - 6) k) = 0 := by
  rw [← sum_extend_zero t hz (n - 1) n (by omega),
    ← sum_extend_zero t hz (n - 2) n (by omega),
    ← sum_extend_zero t hz (n - 3) n (by omega),
    ← sum_extend_zero t hz (n - 4) n (by omega),
    ← sum_extend_zero t hz (n - 5) n (by omega),
    ← sum_extend_zero t hz (n - 6) n (by omega)]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  calc
    (∑ k ∈ Finset.range (n + 1), (c0 * t n k +
      c1 * t (n - 1) k +
      c2 * t (n - 2) k +
      c3 * t (n - 3) k +
      c4 * t (n - 4) k +
      c5 * t (n - 5) k +
      c6 * t (n - 6) k)) =
        ∑ k ∈ Finset.range (n + 1), (G (k + 1) - G k) := by
      apply Finset.sum_congr rfl
      intro k hk
      exact hcert k (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hk)
    _ = 0 := by rw [Finset.sum_range_sub, hG0, hG1, sub_self]

end OMA.T105871

namespace OMA.T105871

lemma back_iter (n k j : ℕ) (hj : j ≤ n) :
    F (n - j) k = F n k *
      ∏ i ∈ Finset.range j, back ((n : ℚ) - i) k := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hjn : j ≤ n := by omega
    have h := backF (n - j) k (by omega)
    rw [Nat.sub_sub] at h
    rw [h, ih hjn, Finset.prod_range_succ, Nat.cast_sub hjn]
    ring

end OMA.T105871

namespace OMA.T105871

lemma large_recurrence (n : ℕ) (hn : 12 ≤ n) :
    p0 n * (OMA.S_oeis_a105871.a n : ℚ) +
      p1 n * (OMA.S_oeis_a105871.a (n - 1) : ℚ) +
      p2 n * (OMA.S_oeis_a105871.a (n - 2) : ℚ) +
      p3 n * (OMA.S_oeis_a105871.a (n - 3) : ℚ) +
      p4 n * (OMA.S_oeis_a105871.a (n - 4) : ℚ) +
      p5 n * (OMA.S_oeis_a105871.a (n - 5) : ℚ) +
      p6 n * (OMA.S_oeis_a105871.a (n - 6) : ℚ) = 0 := by
  rw [repr n, repr (n - 1), repr (n - 2), repr (n - 3), repr (n - 4), repr (n - 5), repr (n - 6)]
  apply sum_certificate7 F (fun m k h => F_zero_of_lt m k (by omega)) n
    (p0 n) (p1 n) (p2 n) (p3 n) (p4 n) (p5 n) (p6 n) (fun k => F n k * R n k)
  · simp [R]
  · rw [F_zero_of_lt n (n+1) (by omega), zero_mul]
  intro k hk
  by_cases hk3 : 3*k ≤ n
  · have hc := certQ (n:ℚ) (k:ℚ) (by exact_mod_cast hn) (by positivity)
      (by exact_mod_cast hk3)
    have h1 := back_iter n k 1 (by omega)
    have h2 := back_iter n k 2 (by omega)
    have h3 := back_iter n k 3 (by omega)
    have h4 := back_iter n k 4 (by omega)
    have h5 := back_iter n k 5 (by omega)
    have h6 := back_iter n k 6 (by omega)
    norm_num only [Finset.prod_range_succ, Finset.prod_range_zero, Nat.cast_zero,
      Nat.cast_one, sub_zero, one_mul] at h1 h2 h3 h4 h5 h6
    rw [h1, h2, h3, h4, h5, h6, rightF]
    push_cast
    linear_combination -(F n k)*hc
  · have hzero : ∀ j : ℕ, F (n-j) k = 0 := by
      intro j
      exact F_zero_of_lt (n-j) k (by omega)
    have h0 : F n k = 0 := F_zero_of_lt n k (by omega)
    have hnext : F n (k+1) = 0 := F_zero_of_lt n (k+1) (by omega)
    simp only [hzero, h0, hnext, mul_zero, zero_mul, add_zero, sub_zero]

end OMA.T105871

namespace OMA.T105871

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma small_cases (n : ℕ) (h6 : 6 ≤ n) (h12 : n < 12) :
    (15 * (n : ℤ) ^ 3 - 65 * (n : ℤ) ^ 2 + 50 * (n : ℤ)) * OMA.S_oeis_a105871.a n
      + (-63 * (n : ℤ) ^ 3 + 252 * (n : ℤ) ^ 2 - 129 * (n : ℤ) - 60) * OMA.S_oeis_a105871.a (n - 1)
      + (-9 * (n : ℤ) ^ 3 + 321 * (n : ℤ) ^ 2 - 1338 * (n : ℤ) + 1332) * OMA.S_oeis_a105871.a (n - 2)
      + (3 * (n : ℤ) ^ 3 - 259 * (n : ℤ) ^ 2 + 1279 * (n : ℤ) - 1575) * OMA.S_oeis_a105871.a (n - 3)
      + (-63 * (n : ℤ) ^ 3 + 630 * (n : ℤ) ^ 2 - 2019 * (n : ℤ) + 2082) * OMA.S_oeis_a105871.a (n - 4)
      + (-9 * (n : ℤ) ^ 3 + 51 * (n : ℤ) ^ 2 - 51 * (n : ℤ) - 63) * OMA.S_oeis_a105871.a (n - 5)
      + (-12 * (n : ℤ) ^ 3 + 130 * (n : ℤ) ^ 2 - 454 * (n : ℤ) + 504) * OMA.S_oeis_a105871.a (n - 6) = 0 := by
  interval_cases n <;> norm_num [OMA.S_oeis_a105871.a, Finset.sum_range_succ,
    Nat.choose_eq_factorial_div_factorial, Nat.choose_eq_zero_of_lt]

end OMA.T105871

open OMA.T105871

theorem OMA.solution : type_of% @OMA.S_oeis_a105871.main := by
  intro n hn
  by_cases h12 : n < 12
  · exact small_cases n hn h12
  · have h := large_recurrence n (by omega)
    unfold p0 p1 p2 p3 p4 p5 p6 at h
    exact_mod_cast h
