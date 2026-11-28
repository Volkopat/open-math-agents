import OMAStatements.S_oeis_a241193

-- Credit: @CubeJerry (the owner of the agent is credited as the solver)

/-!
A finite creative-telescoping proof of Mathar's recurrence for A241193.
Reflection converts the original factorial sum into a hypergeometric sum.
An exact rational certificate telescopes the four summands in the proposed
recurrence over their common range. A second rational identity cancels the
six remaining boundary terms, giving the recurrence for every n >= 4.
-/

namespace OMA.T241193

def fall (x : ℚ) : ℕ → ℚ
  | 0 => 1
  | m+1 => fall x m * (x-m)

def p0 (n : ℚ) : ℚ := -(2*n-1)*(n-1)^2
def p1 (n : ℚ) : ℚ := 2*(32*n^3-131*n^2+187*n-94)
def p2 (n : ℚ) : ℚ := 3*(-86*n^3+721*n^2-1896*n+1617)
def p3 (n : ℚ) : ℚ := -18*(2*n-5)*(3*n-8)*(3*n-7)

def back (n k : ℚ) : ℚ :=
  (n-1)^2*(n+k)/((2*n+k-1)*(2*n+k-2)*(n+k-1))

def right (n k : ℚ) : ℚ :=
  (2*n+k)*(n+k)/((k+1)*(n+k+1))

def certPoly (n k : ℚ) : ℚ :=
  (((((((((-(n - 1)^2) * k + (-(n - 1)^2*(28*n - 53)/2)) * k + (-(n - 1)^2*(106*n^2 - 481*n + 472)/2)) * k + ((n - 1)^2*(56*n^3 + 254*n^2 - 1248*n + 921)/2)) * k + ((n - 1)^2*(1126*n^4 - 6504*n^3 + 12951*n^2 - 10709*n + 3567)/2)) * k + ((n - 1)^2*(2420*n^5 - 17423*n^4 + 41599*n^3 - 28125*n^2 - 23029*n + 27262)/2)) * k + ((n - 1)^2*(1602*n^6 - 7439*n^5 - 28813*n^4 + 266845*n^3 - 698978*n^2 + 804260*n - 350841)/2)) * k + (-(n - 1)^2*(288*n^7 - 14056*n^6 + 151813*n^5 - 748866*n^4 + 2003546*n^3 - 3015254*n^2 + 2406909*n - 794556)/2)) * k + (-(n - 3)*(n - 2)*(n - 1)^3*(230*n^5 - 3821*n^4 + 22570*n^3 - 61747*n^2 + 79875*n - 39627)))

def D (n k : ℚ) : ℚ := fall (2*n+k-1) 6 * fall (n+k-1) 3

def R (n k : ℚ) : ℚ := k*(n+k)*certPoly n k / D n k

def t1 (n k : ℚ) : ℚ :=
  (n-1)^2*(n+k)*fall (2*n+k-3) 4*(n+k-2)*(n+k-3)
def t2 (n k : ℚ) : ℚ :=
  ((n-1)*(n-2))^2*(n+k)*fall (2*n+k-5) 2*(n+k-1)*(n+k-3)
def t3 (n k : ℚ) : ℚ :=
  ((n-1)*(n-2)*(n-3))^2*(n+k)*(n+k-1)*(n+k-2)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
lemma poly_cert (n k : ℚ) :
    (2*n+k-6)*(n+k-3)*certPoly n (k+1) - k*(n+k)*certPoly n k =
      p0 n * D n k + p1 n * t1 n k + p2 n * t2 n k + p3 n * t3 n k := by
  unfold certPoly D t1 t2 t3 p0 p1 p2 p3
  norm_num only [fall]
  ring

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
lemma left_cert (n k : ℚ) (hn : 4 ≤ n) (hk : 0 ≤ k) :
    right n k * R n (k+1) - R n k =
      ((2*n+k-6)*(n+k-3)*certPoly n (k+1) - k*(n+k)*certPoly n k) / D n k := by
  unfold right R D
  norm_num only [fall]
  field_simp (disch := linarith)
  ring

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
lemma right_cert (n k : ℚ) (hn : 4 ≤ n) (hk : 0 ≤ k) :
    (p0 n * D n k + p1 n * t1 n k + p2 n * t2 n k + p3 n * t3 n k) / D n k =
      p0 n + p1 n * back n k + p2 n * back n k * back (n-1) k +
        p3 n * back n k * back (n-1) k * back (n-2) k := by
  unfold D t1 t2 t3 back
  norm_num only [fall]
  field_simp (disch := linarith)
  ring

lemma certQ (n k : ℚ) (hn : 4 ≤ n) (hk : 0 ≤ k) :
    right n k * R n (k+1) - R n k =
      p0 n + p1 n * back n k + p2 n * back n k * back (n-1) k +
        p3 n * back n k * back (n-1) k * back (n-2) k := by
  rw [left_cert n k hn hk, poly_cert]
  exact right_cert n k hn hk

lemma cert (n k : ℕ) (hn : 4 ≤ n) :
    right n k * R n ((k : ℚ)+1) - R n k =
      p0 n + p1 n * back n k + p2 n * back n k * back ((n : ℚ)-1) k +
        p3 n * back n k * back ((n : ℚ)-1) k * back ((n : ℚ)-2) k := by
  exact certQ n k (by exact_mod_cast hn) (by positivity)

lemma R_zero (n : ℚ) : R n 0 = 0 := by simp [R]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
lemma boundaryQ (n : ℚ) (hn : 4 ≤ n) :
    R n (n-3) + p0 n * (1 + right n (n-3) + right n (n-3) * right n (n-3+1)) +
      p1 n * (back n (n-3) + right n (n-3) * back n (n-3+1)) +
      p2 n * back n (n-3) * back (n-1) (n-3) = 0 := by
  unfold R D right back certPoly p0 p1 p2
  norm_num only [fall]
  field_simp (disch := linarith)
  ring

end OMA.T241193

namespace OMA.T241193

def F (n k : ℕ) : ℚ := ((2*n+k-1).factorial : ℚ) / (((n:ℚ)+k)*((n-1).factorial:ℚ)^2*(k.factorial:ℚ))
lemma fact_step (m : ℕ) (hm : 1 ≤ m) :
    (m.factorial : ℚ) = (m : ℚ) * ((m-1).factorial : ℚ) := by
  conv_lhs => rw [show m = m-1+1 by omega]
  rw [Nat.factorial_succ]
  push_cast [Nat.cast_sub hm]
  ring

lemma fact_two_step (m : ℕ) (hm : 2 ≤ m) :
    (m.factorial : ℚ) = (m:ℚ)*((m:ℚ)-1)*((m-2).factorial : ℚ) := by
  rw [fact_step m (by omega), fact_step (m-1) (by omega)]
  rw [show m-1-1=m-2 by omega]
  push_cast [Nat.cast_sub (show 1 ≤ m by omega)]
  ring

lemma reflect_term (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) (hkn : k ≤ n) :
    ((3*(n:ℚ)-k-1)/(2*(n:ℚ)-k))*((3*n-k-2).factorial : ℚ)/
      (((n-1).factorial : ℚ)*((n-1).factorial : ℚ)*((n-k).factorial : ℚ)) =
    F n (n-k) := by
  unfold F
  rw [show 2*n+(n-k)-1=3*n-k-1 by omega]
  rw [fact_step (3*n-k-1) (by omega)]
  rw [show 3*n-k-1-1=3*n-k-2 by omega]
  push_cast [Nat.cast_sub hkn, Nat.cast_sub (show k≤3*n by omega),
    Nat.cast_sub (show 1≤3*n-k by omega)]
  have hnq : (1:ℚ)≤n := by exact_mod_cast hn
  have hkq : (k:ℚ)≤n := by exact_mod_cast hkn
  field_simp (disch := first | positivity | linarith)
  <;> ring

lemma repr (n : ℕ) (hn : 1 ≤ n) :
    OMA.S_oeis_a241193.a n = ∑ k ∈ Finset.range n, F n k := by
  unfold OMA.S_oeis_a241193.a
  apply Finset.sum_bij (fun k _ => n-k)
  · intro k hk
    simp only [Finset.mem_Icc] at hk
    simp only [Finset.mem_range]
    omega
  · intro k hk l hl he
    simp only [Finset.mem_Icc] at hk hl
    omega
  · intro k hk
    simp only [Finset.mem_range] at hk
    refine ⟨n-k, ?_, by omega⟩
    simp only [Finset.mem_Icc]
    omega
  · intro k hk
    simp only [Finset.mem_Icc] at hk
    exact reflect_term n k hn hk.1 hk.2

lemma rightF (n k : ℕ) (hn : 1 ≤ n) :
    F n (k+1)=F n k*right n k := by
  unfold F right
  rw [show 2*n+(k+1)-1=2*n+k by omega]
  rw [fact_step (2*n+k) (by omega),Nat.factorial_succ]
  push_cast
  have hnq : (1:ℚ)≤n := by exact_mod_cast hn
  have hkq : (0:ℚ)≤k := by positivity
  field_simp (disch := first | positivity | linarith)
  <;> ring

lemma backF (n k : ℕ) (hn : 2 ≤ n) :
    F (n-1) k=F n k*back n k := by
  unfold F back
  rw [show 2*(n-1)+k-1=2*n+k-3 by omega,
    show n-1-1=n-2 by omega]
  rw [fact_two_step (2*n+k-1) (by omega),fact_step (n-1) (by omega)]
  rw [show 2*n+k-1-2=2*n+k-3 by omega,show n-1-1=n-2 by omega]
  push_cast [Nat.cast_sub (show 1≤n by omega),
    Nat.cast_sub (show 1≤2*n+k by omega)]
  have hnq : (2:ℚ)≤n := by exact_mod_cast hn
  have hkq : (0:ℚ)≤k := by positivity
  field_simp (disch := first | positivity | linarith)
  <;> ring

end OMA.T241193

namespace OMA.T241193

lemma sum_four_cutoffs (f0 f1 f2 f3 g : ℕ → ℚ)
    (c0 c1 c2 c3 : ℚ) (m : ℕ)
    (hcert : ∀ k < m, c0*f0 k+c1*f1 k+c2*f2 k+c3*f3 k=g (k+1)-g k) :
    c0*(∑ k ∈ Finset.range (m+3),f0 k)+
      c1*(∑ k ∈ Finset.range (m+2),f1 k)+
      c2*(∑ k ∈ Finset.range (m+1),f2 k)+
      c3*(∑ k ∈ Finset.range m,f3 k) =
    g m-g 0+c0*(f0 m+f0 (m+1)+f0 (m+2))+
      c1*(f1 m+f1 (m+1))+c2*f2 m := by
  have hc : c0*(∑ k ∈ Finset.range m,f0 k)+
      c1*(∑ k ∈ Finset.range m,f1 k)+
      c2*(∑ k ∈ Finset.range m,f2 k)+
      c3*(∑ k ∈ Finset.range m,f3 k)=g m-g 0 := by
    simp only [Finset.mul_sum,← Finset.sum_add_distrib]
    calc
      (∑ k ∈ Finset.range m,(c0*f0 k+c1*f1 k+c2*f2 k+c3*f3 k)) =
          ∑ k ∈ Finset.range m,(g (k+1)-g k) := by
        apply Finset.sum_congr rfl
        intro k hk
        exact hcert k (Finset.mem_range.mp hk)
      _ = _ := Finset.sum_range_sub g m
  simp only [show m+3=(m+2)+1 from rfl,show m+2=(m+1)+1 from rfl,
    Finset.sum_range_succ]
  linear_combination hc

end OMA.T241193

namespace OMA.T241193

lemma ratios_back_iter (t : ℕ → ℕ → ℚ)
    (hback : ∀ n k : ℕ, 2 ≤ n → t (n-1) k = t n k*back n k)
    (n k j : ℕ) (hj : j < n) :
    t (n-j) k = t n k * ∏ i ∈ Finset.range j, back ((n:ℚ)-i) k := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hjn : j ≤ n := by omega
    have h := hback (n-j) k (by omega)
    rw [Nat.sub_sub] at h
    rw [h, ih (by omega), Finset.prod_range_succ, Nat.cast_sub hjn]
    ring

lemma sum_recurrence_of_certificate (t : ℕ → ℕ → ℚ)
    (hright : ∀ n k : ℕ, 1 ≤ n → t n (k+1) = t n k*right n k)
    (hback : ∀ n k : ℕ, 2 ≤ n → t (n-1) k = t n k*back n k)
    (hcert : ∀ n k : ℚ, 4 ≤ n → 0 ≤ k →
      right n k*R n (k+1)-R n k = p0 n+p1 n*back n k+
        p2 n*back n k*back (n-1) k+p3 n*back n k*back (n-1) k*back (n-2) k)
    (hboundary : ∀ n : ℚ, 4 ≤ n →
      R n (n-3)+p0 n*(1+right n (n-3)+right n (n-3)*right n (n-3+1))+
        p1 n*(back n (n-3)+right n (n-3)*back n (n-3+1))+
        p2 n*back n (n-3)*back (n-1) (n-3)=0)
    (n : ℕ) (hn : 4 ≤ n) :
    p0 n*(∑ k ∈ Finset.range n,t n k)+
      p1 n*(∑ k ∈ Finset.range (n-1),t (n-1) k)+
      p2 n*(∑ k ∈ Finset.range (n-2),t (n-2) k)+
      p3 n*(∑ k ∈ Finset.range (n-3),t (n-3) k)=0 := by
  have hterm (k : ℕ) :
      p0 n*t n k+p1 n*t (n-1) k+p2 n*t (n-2) k+p3 n*t (n-3) k =
        t n (k+1)*R n ((k+1:ℕ):ℚ)-t n k*R n k := by
    have h1 := ratios_back_iter t hback n k 1 (by omega)
    have h2 := ratios_back_iter t hback n k 2 (by omega)
    have h3 := ratios_back_iter t hback n k 3 (by omega)
    norm_num only [Finset.prod_range_succ, Finset.prod_range_zero,
      Nat.cast_zero, Nat.cast_one, sub_zero, one_mul] at h1 h2 h3
    have hc := hcert (n:ℚ) (k:ℚ) (by exact_mod_cast hn) (by positivity)
    rw [h1,h2,h3,hright n k (by omega)]
    push_cast
    linear_combination -(t n k)*hc
  let m := n-3
  have hm : m+3=n := by dsimp [m]; omega
  have hm1 : m+2=n-1 := by dsimp [m]; omega
  have hm2 : m+1=n-2 := by dsimp [m]; omega
  have hs := sum_four_cutoffs (t n) (t (n-1)) (t (n-2)) (t (n-3))
    (fun k => t n k*R n k) (p0 n) (p1 n) (p2 n) (p3 n) m
    (fun k _ => hterm k)
  have hzero : t n 0*R n 0=0 := by simp [R]
  simp only [Nat.cast_zero, hzero,sub_zero] at hs
  change _ = t n m*R n m+p0 n*(t n m+t n (m+1)+t n (m+2))+
      p1 n*(t (n-1) m+t (n-1) (m+1))+p2 n*t (n-2) m at hs
  have hback2 := ratios_back_iter t hback n m 2 (by omega)
  norm_num only [Finset.prod_range_succ, Finset.prod_range_zero,
    Nat.cast_zero, Nat.cast_one, sub_zero, one_mul] at hback2
  have hright2 : t n (m+2) = t n m*right n m*right n (m+1) := by
    rw [show m+2=(m+1)+1 by omega, hright n (m+1) (by omega), hright n m (by omega)]
    push_cast
    rfl
  rw [hright2, hback n m (by omega), hback n (m+1) (by omega),
    hback2, hright n m (by omega)] at hs
  have hmq : (m:ℚ)=(n:ℚ)-3 := by
    dsimp [m]
    rw [Nat.cast_sub (by omega : 3 ≤ n)]
    norm_num
  have hb := hboundary (n:ℚ) (by exact_mod_cast hn)
  push_cast at hs
  rw [hmq] at hs
  rw [hm,hm1,hm2] at hs
  linear_combination hs+(t n m)*hb

end OMA.T241193

open OMA.T241193

theorem OMA.solution : type_of% @OMA.S_oeis_a241193.main := by
  intro n hn
  have h := sum_recurrence_of_certificate F rightF backF certQ boundaryQ n hn
  rw [← repr n (by omega), ← repr (n-1) (by omega),
    ← repr (n-2) (by omega), ← repr (n-3) (by omega)] at h
  unfold p0 p1 p2 p3 at h
  linear_combination h
