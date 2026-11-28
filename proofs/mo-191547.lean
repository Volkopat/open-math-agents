import OMAStatements.S_mo_191547

/-
David S. Newman asked whether the integer parts of three-halves powers
form an additive basis of order three. Around the square of an odd
integer the two neighboring discrete slopes lie in a common pair of
consecutive integers. Moving two inputs in opposite directions covers
a full interval. A third input brings the desired residual into it.
The small initial ranges are certified by exact binary masks.
Deshouillers and Konyagin studied binary representations below this
exponent, and Balanzario, Garaev and Zuazua established exceptional-set
bounds. The present construction covers every nonnegative target.
-/

namespace NewmanBasis

def val (n : ℕ) : ℕ := (n^3).sqrt

lemma at_square (v : ℕ) : val (v^2) = v^3 := by
  unfold val
  rw [show (v^2)^3 = (v^3)^2 by ring, Nat.sqrt_eq']

lemma real_bounds (n : ℕ) :
    (val n : ℝ) ≤ (Real.sqrt n)^3 ∧ (Real.sqrt n)^3 < (val n : ℝ) + 1 := by
  have h : ((Real.sqrt (n : ℝ))^3)^2 = (n : ℝ)^3 := by
    rw [show ((Real.sqrt (n : ℝ))^3)^2 = ((Real.sqrt (n : ℝ))^2)^3 by ring,
      Real.sq_sqrt (by positivity)]
  have lo := Nat.sqrt_le' (n^3)
  have hi := Nat.lt_succ_sqrt' (n^3)
  constructor
  · apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    rw [h]
    exact_mod_cast lo
  · apply (sq_lt_sq₀ (by positivity) (by positivity)).mp
    rw [h]
    exact_mod_cast hi

lemma increments (n m M : ℕ) (hl : 4*m^2 ≤ 9*n) (hu : 9*(n+1) ≤ 4*M^2) :
    val n + m ≤ val (n+1) ∧ val (n+1) ≤ val n + M := by
  let a := Real.sqrt (n : ℝ)
  let b := Real.sqrt ((n+1 : ℕ) : ℝ)
  have ha : 0 ≤ a := Real.sqrt_nonneg _
  have hb : 0 ≤ b := Real.sqrt_nonneg _
  have ha2 : a^2 = n := Real.sq_sqrt (by positivity)
  have hb2 : b^2 = (n:ℝ)+1 := by simpa [b] using Real.sq_sqrt (show 0 ≤ ((n+1:ℕ):ℝ) by positivity)
  have hdiff : b^2-a^2 = 1 := by linarith
  have lowerSq : (2*(m:ℝ))^2 ≤ (3*a)^2 := by
    have h' : 4*(m:ℝ)^2 ≤ 9*n := by exact_mod_cast hl
    nlinarith only [h',ha2]
  have upperSq : (3*b)^2 ≤ (2*(M:ℝ))^2 := by
    have h' : 9*((n:ℝ)+1) ≤ 4*(M:ℝ)^2 := by exact_mod_cast hu
    nlinarith only [h',hb2]
  have lo := (sq_le_sq₀ (by positivity) (by positivity)).mp lowerSq
  have hi := (sq_le_sq₀ (by positivity) (by positivity)).mp upperSq
  have lowId : 2*(b^3-a^3)-3*a = (b-a)^2*(2*b+a) := by linear_combination 3*a*hdiff
  have highId : 3*b-2*(b^3-a^3) = (b-a)^2*(b+2*a) := by linear_combination -3*b*hdiff
  obtain ⟨h1,h2⟩ := real_bounds n
  obtain ⟨h3,h4⟩ := real_bounds (n+1)
  change (val n : ℝ) ≤ a^3 at h1
  change a^3 < (val n : ℝ)+1 at h2
  change (val (n+1) : ℝ) ≤ b^3 at h3
  change b^3 < (val (n+1) : ℝ)+1 at h4
  have l : (val n : ℝ)+m < val (n+1)+1 := by
    linarith only [h1,h4,lo,lowId, mul_nonneg (sq_nonneg (b-a)) (show 0≤2*b+a by linarith)]
  have u : (val (n+1):ℝ) < (val n:ℝ)+M+1 := by
    linarith only [h2,h3,hi,highId, mul_nonneg (sq_nonneg (b-a)) (show 0≤b+2*a by linarith)]
  exact ⟨Nat.le_of_lt_succ (by exact_mod_cast l), Nat.le_of_lt_succ (by exact_mod_cast u)⟩

lemma approximate (R t : ℕ) (hR : R < t^3) :
    ∃ c, val c ≤ R ∧ R < val c + 2*t := by
  let P := fun c => val c ≤ R
  let c := Nat.findGreatest P (t^2)
  have hc : P c := Nat.findGreatest_spec (Nat.zero_le _) (show P 0 by simp [P,val])
  have hc' : c < t^2 := by
    have h := Nat.findGreatest_le (P := P) (n := t^2)
    change c ≤ t^2 at h
    have hne : c ≠ t^2 := by
      intro e
      change val c ≤ R at hc
      rw [e, at_square] at hc
      omega
    omega
  have hn := Nat.findGreatest_is_greatest (P:=P) (n:=t^2) (k:=c+1) (Nat.lt_succ_self c) hc'
  change ¬ val (c+1) ≤ R at hn
  have inc := (increments c 0 (2*t) (by simp) (by nlinarith only [hc',Nat.zero_le (t^2)])).2
  exact ⟨c, hc, by omega⟩

def extend (B : ℕ) : ℕ → ℕ
  | 0 => 0
  | k+1 => extend B k ||| (B <<< val k)

lemma extend_sound {B n j : ℕ} (h : (extend B n).testBit j = true) :
    ∃ k b, j = val k + b ∧ B.testBit b = true := by
  induction n with
  | zero => simp [extend] at h
  | succ n ih =>
    simp only [extend,Nat.testBit_or,Bool.or_eq_true] at h
    rcases h with h | h
    · exact ih h
    · simp only [Nat.testBit_shiftLeft,Bool.and_eq_true,decide_eq_true_eq] at h
      exact ⟨n,j-val n,by omega,h.2⟩

lemma bit_interval {M a l n : ℕ}
    (h : ((M >>> a) &&& (2^l-1)) = 2^l-1) (ha : a ≤ n) (hl : n < a+l) :
    M.testBit n = true := by
  have e := congrArg (fun x : ℕ => x.testBit (n-a)) h
  have hn : n-a < l := by omega
  simpa [Nat.testBit_and,Nat.testBit_shiftRight,Nat.testBit_two_pow_sub_one,hn,
    show a+(n-a)=n by omega] using e

def twoMask : ℕ := extend (extend 1 1701) 1701

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
lemma twoBits : ((twoMask >>> 1600) &&& (2^62001-1)) = 2^62001-1 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
lemma threeBits : (extend (extend (extend 1 140) 140) 140 &&& (2^1600-1)) = 2^1600-1 := by
  decide +kernel

lemma two_range {n : ℕ} (ha : 1600 ≤ n) (hb : n ≤ 63600) :
    ∃ a b, n = val a + val b := by
  have bits := bit_interval (M:=twoMask) (a:=1600) (l:=62001) (n:=n) twoBits ha (by omega)
  change (extend (extend 1 1701) 1701).testBit n = true at bits
  obtain ⟨a,r,h,hr⟩ := extend_sound bits
  obtain ⟨b,z,g,hz⟩ := extend_sound hr
  have := Nat.testBit_one_eq_true_iff_self_eq_zero.mp hz
  exact ⟨a,b,by omega⟩

lemma small_range {n : ℕ} (hn : n < 1600) : ∃ a b c, n = val a + val b + val c := by
  have hh : ((extend (extend (extend 1 140) 140) 140 >>> 0) &&& (2^1600-1)) = 2^1600-1 := by
    rw [Nat.shiftRight_zero]; exact threeBits
  obtain ⟨a,r,h,hr⟩ := extend_sound (bit_interval hh (Nat.zero_le n) (by omega))
  obtain ⟨b,s,g,hs⟩ := extend_sound hr
  obtain ⟨c,z,f,hz⟩ := extend_sound hs
  have := Nat.testBit_one_eq_true_iff_self_eq_zero.mp hz
  exact ⟨a,b,c,by omega⟩
lemma endpoint_gains (t r : ℕ) (ht : 2000 ≤ t) (hr : r ≤ 5) :
    let u := 12*t+2*r+1
    2*u^3 + 2*t ≤ val (u^2+6*t) + val (u^2-6*t) := by
  let u := 12*t+2*r+1
  change 2*u^3 + 2*t ≤ val (u^2+6*t) + val (u^2-6*t)
  have hs : 6*t ≤ u^2 := by dsimp [u]; nlinarith
  have hg : 9*u*t ≤ u^3+t := by
    have h9 : 9 ≤ u := by dsimp [u]; omega
    have htu : t ≤ u := by dsimp [u]; omega
    calc
      9*u*t ≤ u*u*u := by gcongr
      _ ≤ u^3+t := by nlinarith only [Nat.zero_le t]
  have plus : u^3+9*u*t+t ≤ val (u^2+6*t) := by
    apply Nat.le_sqrt'.2
    zify
    obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le ht
    dsimp [u]
    interval_cases r <;> push_cast <;>
      apply sub_nonneg.mp <;> ring_nf <;> positivity
  have minus : u^3+t-9*u*t ≤ val (u^2-6*t) := by
    apply Nat.le_sqrt'.2
    zify [hs,hg]
    obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le ht
    dsimp [u]
    interval_cases r <;> push_cast <;>
      apply sub_nonneg.mp <;> ring_nf <;> positivity
  omega

lemma residual_bound (t r : ℕ) (ht : 2000 ≤ t) (hr : r ≤ 5) :
    let u := 12*t+2*r+1
    2*(u+2)^3 < 2*u^3+t^3 := by
  dsimp only
  zify
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le ht
  interval_cases r <;> push_cast <;> apply sub_pos.mp <;> ring_nf <;> positivity

lemma crosses {W : ℕ → ℕ} {d y : ℕ} (h0 : W 0 ≤ y) (hd : y ≤ W d)
    (step : ∀ k < d, W (k+1) ≤ W k + 1) : ∃ k ≤ d, W k = y := by
  induction d with
  | zero => exact ⟨0,le_rfl,by omega⟩
  | succ d ih =>
    by_cases h : y ≤ W d
    · obtain ⟨k,hk,hy⟩ := ih h (fun k h' => step k (by omega))
      exact ⟨k,by omega,hy⟩
    · have := step d (by omega)
      exact ⟨d+1,le_rfl,by omega⟩

lemma centered (t r R : ℕ) (ht : 2000 ≤ t) (hr : r ≤ 5) (hR : R < t^3) :
    let u := 12*t+2*r+1
    ∃ a b c, 2*u^3 + R = val a + val b + val c := by
  let u := 12*t+2*r+1
  let m := 18*t+3*r+1
  let W := fun k => val (u^2+k)+val (u^2-k)
  change ∃ a b c, 2*u^3 + R = val a + val b + val c
  obtain ⟨c,hc,he⟩ := approximate R t hR
  have hs : 6*t ≤ u^2 := by dsimp [u]; nlinarith
  have band (n : ℕ) (lo : u^2-6*t ≤ n) (hi : n+1 ≤ u^2+6*t) :
      val n + m ≤ val (n+1) ∧ val (n+1) ≤ val n + (m+1) := by
    apply increments
    · have h : u^2 ≤ n+6*t := by omega
      dsimp [u] at h
      dsimp [m]
      nlinarith only [h,Nat.zero_le r,Nat.zero_le t]
    · dsimp [u] at hi
      dsimp [m]
      nlinarith only [hi,Nat.zero_le r,Nat.zero_le t]
  have step (k : ℕ) (hk : k<6*t) : W (k+1) ≤ W k+1 := by
    have hp := (band (u^2+k) (by omega) (by omega)).2
    have hn := (band (u^2-(k+1)) (by omega) (by omega)).1
    rw [show u^2-(k+1)+1 = u^2-k by omega] at hn
    dsimp [W]
    rw [show u^2+(k+1) = u^2+k+1 by omega]
    omega
  have low : W 0 = 2*u^3 := by simp [W,at_square,two_mul]
  have high := endpoint_gains t r ht hr
  change 2*u^3+2*t ≤ W (6*t) at high
  obtain ⟨k,hk,e⟩ := crosses (W:=W) (d:=6*t) (y:=2*u^3+(R-val c)) (by omega) (by omega) step
  exact ⟨u^2+k,u^2-k,c,by dsimp [W] at e; omega⟩

lemma large {N : ℕ} (hN : 2*24001^3 ≤ N) : ∃ a b c, N = val a + val b + val c := by
  let P := fun k : ℕ => 2*(2*k+1)^3 ≤ N
  let g := Nat.findGreatest P N
  have h0 : P g := Nat.findGreatest_spec (m:=12000) (by omega) (show P 12000 from hN)
  have gmin : 12000 ≤ g := by
    by_contra! h
    exact Nat.findGreatest_is_greatest (P:=P) h (by omega) (show P 12000 from hN)
  change 2*(2*g+1)^3 ≤ N at h0
  have hs : g+1 ≤ N := by nlinarith only [h0,Nat.zero_le g,Nat.zero_le (g^2),Nat.zero_le (g^3)]
  have h1 := Nat.findGreatest_is_greatest (P:=P) (n:=N) (k:=g+1) (Nat.lt_succ_self g) hs
  let t := g/6
  let r := g%6
  have ht : 2000 ≤ t := by dsimp [t]; omega
  have hr : r ≤ 5 := by dsimp [r]; omega
  have eqg : 2*g+1 = 12*t+2*r+1 := by dsimp [t,r]; omega
  rw [eqg] at h0
  change ¬ 2*(2*(g+1)+1)^3 ≤ N at h1
  rw [show 2*(g+1)+1 = (12*t+2*r+1)+2 by omega] at h1
  have hres := residual_bound t r ht hr
  let R := N-2*(12*t+2*r+1)^3
  have hR : R < t^3 := by dsimp [R]; dsimp only at hres; omega
  obtain ⟨a,b,c,e⟩ := centered t r R ht hr hR
  exact ⟨a,b,c,by dsimp [R] at e; omega⟩

lemma all_values (N : ℕ) : ∃ a b c, N = val a + val b + val c := by
  by_cases big : 2*24001^3 ≤ N
  · exact large big
  by_cases small : N < 1600
  · exact small_range small
  have bound : N-1600 < 31000^3 := by omega
  obtain ⟨c,hc,hgap⟩ := approximate (N-1600) 31000 bound
  obtain ⟨a,b,h⟩ := two_range (n:=N-val c) (by omega) (by omega)
  exact ⟨a,b,c,by omega⟩

end NewmanBasis

theorem OMA.solution : type_of% @OMA.S_mo_191547.main := by
  exact NewmanBasis.all_values
