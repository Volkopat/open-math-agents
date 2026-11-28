import OMAReductions.R_OeisA67599_conjecture_R2

/-!
# Three ordered prime factors in an A067599 fixed point

This file proves the exact equivalence in R2.H2. The finite checks are split into
decimal intervals. Each closed test is decided by the kernel, and the bounded
induction lemmas show that their union covers every possible repeated final exponent.
-/

-- Credit: @SHIN09-git

/-
# Three distinct prime factors in OEIS A067599

All statements use the decimal encoding in the original problem.
-/

namespace A067599Three

open OeisA67599

/-- The place value by which a decimal block shifts the preceding digits. -/
def place (x : ℕ) : ℕ := 10 ^ (Nat.digits 10 x).length

private theorem place_le {x : ℕ} (hx : 0 < x) : place x ≤ 10*x := by
  have hh : 0 < (Nat.digits 10 x).length :=
    (Nat.lt_digits_length_iff (by decide : 1 < 10) x).2 (by simp; omega)
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hh)
  have := (Nat.lt_digits_length_iff (by decide : 1 < 10) x).1
    (show k < (Nat.digits 10 x).length by omega)
  simp only [place, hk, pow_succ]
  omega

private theorem lt_place (x : ℕ) : x < place x :=
  Nat.lt_base_pow_length_digits (by decide : 1 < 10)

private theorem dedup_run {p : ℕ} {xs : List ℕ} (i : ℕ) (h : p ∉ xs) :
    (List.replicate (i+1) p ++ xs).dedup = p :: xs.dedup := by
  induction i with
  | zero => simp [List.dedup_cons_of_notMem h]
  | succ i ih =>
    rw [List.replicate_succ, List.cons_append, List.dedup_cons_of_mem]
    · exact ih
    · simp [List.mem_replicate]

/-- The original encoding on three ordered distinct primes. -/
theorem three_encoding {p q r : ℕ} (i j k : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hr : r.Prime) (hpq : p < q) (hqr : q < r) :
    a (p^(i+1)*q^(j+1)*r^(k+1)) =
      (((((p*place (i+1)+(i+1))*place q+q)*place (j+1)+(j+1))*place r+r)*
        place (k+1)+(k+1)) := by
  let lp := List.replicate (i+1) p
  let lq := List.replicate (j+1) q
  let lr := List.replicate (k+1) r
  have hpr := hpq.trans hqr
  have h1 := Nat.perm_primeFactorsList_mul (pow_ne_zero (i+1) hp.ne_zero)
    (pow_ne_zero (j+1) hq.ne_zero)
  have h2 := Nat.perm_primeFactorsList_mul
    (Nat.mul_ne_zero (pow_ne_zero (i+1) hp.ne_zero) (pow_ne_zero (j+1) hq.ne_zero))
    (pow_ne_zero (k+1) hr.ne_zero)
  rw [hp.primeFactorsList_pow, hq.primeFactorsList_pow] at h1
  rw [hr.primeFactorsList_pow] at h2
  have hperm := h2.trans (h1.append_right lr)
  have hs : ((lp ++ lq) ++ lr).Pairwise (· ≤ ·) := by
    simp [lp, lq, lr, List.pairwise_append, List.mem_replicate, hpq.le, hqr.le, hpr.le]
  have hlist : (p^(i+1)*q^(j+1)*r^(k+1)).primeFactorsList = (lp ++ lq) ++ lr :=
    hperm.eq_of_pairwise' (Nat.primeFactorsList_sorted _).pairwise hs
  have hnp : p ∉ lq ++ lr := by simp [lq, lr, List.mem_replicate, hpq.ne, hpr.ne]
  have hnq : q ∉ lr := by simp [lr, List.mem_replicate, hqr.ne]
  have hd : ((lp ++ lq) ++ lr).dedup = [p,q,r] := by
    rw [List.append_assoc, dedup_run i hnp, dedup_run j hnq]
    simp [lr, List.replicate_dedup]
  have hn : 2 ≤ p^(i+1)*q^(j+1)*r^(k+1) := by
    have hb : 2 ≤ r^(k+1) := le_trans hr.two_le
      (by simpa using (Nat.pow_le_pow_right hr.pos (show 1 ≤ k+1 by omega)))
    have hpos : 1 ≤ p^(i+1)*q^(j+1) := Nat.mul_pos (pow_pos hp.pos _) (pow_pos hq.pos _)
    exact hb.trans (by simpa using Nat.mul_le_mul_right (r^(k+1)) hpos)
  rw [a, if_neg (Nat.not_lt.mpr hn), hlist, hd]
  simp [lp, lq, lr, List.count_append, List.count_replicate, hpq.ne, hqr.ne, hpr.ne,
    Ne.symm hpq.ne, Ne.symm hqr.ne, Ne.symm hpr.ne, concatenateNats, place]

private theorem append_bound {z K v x : ℕ} (hz : z ≤ K*v) (hv : 0 < v) (hx : 0 < x) :
    z*place x+x ≤ (10*K+1)*(v*x) := by
  have h₁ := Nat.mul_le_mul hz (place_le hx)
  have h₂ := Nat.mul_le_mul_right x hv
  nlinarith only [h₁,h₂]

private theorem growth {p q r i j k : ℕ} (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (h : p^(i+1)*q^(j+1)*r^(k+1) =
      (((((p*place (i+1)+(i+1))*place q+q)*place (j+1)+(j+1))*place r+r)*
        place (k+1)+(k+1))) :
    p^i*q^j*r^k ≤ 111111*(i+1)*(j+1)*(k+1) := by
  have h₁ := append_bound (show p ≤ 1*p by simp) hp (Nat.succ_pos i)
  have h₂ := append_bound h₁ (by positivity) hq
  have h₃ := append_bound h₂ (by positivity) (Nat.succ_pos j)
  have h₄ := append_bound h₃ (by positivity) hr
  have h₅ := append_bound h₄ (by positivity) (Nat.succ_pos k)
  apply Nat.le_of_mul_le_mul_left (c:=p*q*r) _ (by positivity)
  rw [pow_succ p i, pow_succ q j, pow_succ r k] at h
  nlinarith only [h,h₅]

private theorem smaller_factors {x y z u v w : ℕ} (hv : 0 < v) (hw : 0 < w)
    (hy : v ≤ y) (hz : w ≤ z) (h : x*y*z ≤ u*v*w) : x ≤ u := by
  apply Nat.le_of_mul_le_mul_right _ (Nat.mul_pos hv hw)
  calc x*(v*w) ≤ x*(y*z) := Nat.mul_le_mul_left _ (Nat.mul_le_mul hy hz)
       _ ≤ u*(v*w) := by simpa [Nat.mul_assoc] using h

private theorem index_le_pow {s : ℕ} (h : 2 ≤ s) (i : ℕ) : i+1 ≤ s^i :=
  le_trans (Nat.succ_le_of_lt (show i < 2^i from Nat.lt_two_pow_self)) (Nat.pow_le_pow_left h i)

private theorem cutoff_two (i : ℕ) (hi : 22 ≤ i) : 111111*(i+1) < 2^i := by
  induction i, hi using Nat.le_induction with
  | base => decide
  | succ i hi ih => rw [pow_succ]; omega

private theorem cutoff_three (j : ℕ) (hj : 13 ≤ j) : 111111*(j+1) < 3^j := by
  induction j, hj using Nat.le_induction with
  | base => decide
  | succ j hj ih => rw [pow_succ]; omega

private theorem cutoff_five (k : ℕ) (hk : 9 ≤ k) : 111111*(k+1) < 5^k := by
  induction k, hk using Nat.le_induction with
  | base => decide
  | succ k hk ih => rw [pow_succ]; omega

private theorem r_five {p q r : ℕ} (hp : p.Prime) (hr : r.Prime)
    (hpq : p < q) (hqr : q < r) : 5 ≤ r := by
  have := hp.two_le
  have h4 : r ≠ 4 := by rintro rfl; norm_num at hr
  omega

/-- Uniform growth and exponent bounds for a three-prime fixed point. -/
theorem exponent_bounds {p q r i j k : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p < q) (hqr : q < r)
    (h : a (p^(i+1)*q^(j+1)*r^(k+1)) = p^(i+1)*q^(j+1)*r^(k+1)) :
    p^i*q^j*r^k ≤ 111111*(i+1)*(j+1)*(k+1) ∧
    p^i ≤ 111111*(i+1) ∧ q^j ≤ 111111*(j+1) ∧ r^k ≤ 111111*(k+1) ∧
    i < 22 ∧ j < 13 ∧ k < 9 := by
  have H := growth hp.pos hq.pos hr.pos (h.symm.trans (three_encoding i j k hp hq hr hpq hqr))
  have P := index_le_pow hp.two_le i
  have Q := index_le_pow hq.two_le j
  have R := index_le_pow hr.two_le k
  have Bp := smaller_factors (Nat.succ_pos j) (Nat.succ_pos k) Q R H
  have Bq := smaller_factors (x:=q^j) (u:=111111*(j+1))
    (Nat.succ_pos i) (Nat.succ_pos k) P R (by simpa [mul_assoc,mul_comm,mul_left_comm] using H)
  have Br := smaller_factors (x:=r^k) (u:=111111*(k+1))
    (Nat.succ_pos i) (Nat.succ_pos j) P Q (by simpa [mul_assoc,mul_comm,mul_left_comm] using H)
  refine ⟨H,Bp,Bq,Br,?_,?_,?_⟩
  · by_contra! hi
    have := cutoff_two i hi
    have := Nat.pow_le_pow_left hp.two_le i
    omega
  · by_contra! hj
    have := cutoff_three j hj
    have := Nat.pow_le_pow_left (show 3 ≤ q by have := hp.two_le; omega) j
    omega
  · by_contra! hk
    have := cutoff_five k hk
    have := Nat.pow_le_pow_left (r_five hp hr hpq hqr) k
    omega

/-- Decimal prefix formed by the first two prime/exponent pairs. -/
def head (p a q b : ℕ) : ℕ := ((p*place a+a)*place q+q)*place b+b

/-- If the last exponent is one, its prime is recovered from its decimal length. -/
theorem last_prime_iff {p q r a₁ b : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p < q) (hqr : q < r) (ha : 0 < a₁) (hb : 0 < b) :
    a (p^a₁*q^b*r) = p^a₁*q^b*r ↔
      (p^a₁*q^b-10)*r = 10*head p a₁ q b*place r+1 := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ha)
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hb)
  have H := three_encoding i j 0 hp hq hr hpq hqr
  change a (p^(i+1)*q^(j+1)*r^1) = (head p (i+1) q (j+1)*place r+r)*10+1 at H
  rw [pow_one] at H
  rw [H]
  set M := p^(i+1)*q^(j+1)
  set C := head p (i+1) q (j+1)
  constructor
  · intro eq
    have hm : 10 ≤ M := by
      by_contra! hs
      have ht := Nat.mul_le_mul_right r hs.le
      nlinarith only [ht,eq]
    have hsplit := congrArg (· * r) (Nat.sub_add_cancel hm)
    nlinarith only [eq,hsplit]
  · intro eq
    have hm : 10 ≤ M := by
      by_contra! hs
      simp [Nat.sub_eq_zero_of_le hs.le] at eq
    have hsplit := Nat.sub_add_cancel hm
    nlinarith only [eq, congrArg (· * r) hsplit]

/-- Numerical window for the first two prime powers; valid at every digit length. -/
theorem prefix_window {p q r a₁ b : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p < q) (hqr : q < r) (ha : 0 < a₁) (hb : 0 < b)
    (h : a (p^a₁*q^b*r) = p^a₁*q^b*r) :
    10*head p a₁ q b+10 < p^a₁*q^b ∧ p^a₁*q^b ≤ 100*head p a₁ q b+10 := by
  have eq := (last_prime_iff hp hq hr hpq hqr ha hb).mp h
  set M := p^a₁*q^b
  set C := head p a₁ q b
  have hm : 10 ≤ M := by
    by_contra! hs
    simp [Nat.sub_eq_zero_of_le hs.le] at eq
  have eq' : M*r = 10*C*place r+10*r+1 := by
    have hh := congrArg (· * r) (Nat.sub_add_cancel hm)
    nlinarith only [eq,hh]
  constructor
  · by_contra! ht
    have H := Nat.mul_le_mul_right r ht
    have H' := Nat.mul_le_mul_left (10*C) (lt_place r).le
    nlinarith only [eq',H,H']
  · by_contra! ht
    have H := Nat.mul_le_mul_right r (show 100*C+11 ≤ M by omega)
    have H' := Nat.mul_le_mul_left (10*C) (place_le hr.pos)
    have hr' := hr.two_le
    nlinarith only [eq',H,H',hr']

/-- Divisor equation for the branch with both larger primes occurring once. -/
theorem bilinear_identity {p q r a₁ : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p < q) (hqr : q < r) (ha : 0 < a₁) (h : a (p^a₁*q*r) = p^a₁*q*r) :
    ((p^a₁ : ℤ)*q-10)*((p^a₁ : ℤ)*r-100*(place r : ℤ)) =
    (p^a₁ : ℤ)*((10*((p*place a₁+a₁)*place q : ℕ)+1)*(10*(place r : ℤ))+1) +
      1000*(place r : ℤ) := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ha)
  have H := three_encoding i 0 0 hp hq hr hpq hqr
  change a (p^(i+1)*q^1*r^1) =
    ((((p*place (i+1)+(i+1))*place q+q)*10+1)*place r+r)*10+1 at H
  simp only [pow_one] at H
  rw [h] at H
  have H' := congrArg (Nat.cast (R:=ℤ)) H
  push_cast at H' ⊢
  linear_combination (p:ℤ)^i.succ * H'

end A067599Three

/-
# Finite certificates for the largest prime in A067599

The square branch recovers the middle factor by division. The other branch
checks decimal intervals by bisection. ThreePrimeTail proves that each
candidate fixed point would be detected by the appropriate check.
-/

namespace A067599Three.Check


/-- Check every integer below n, stopping as soon as a test fails. -/
def below : ℕ → (ℕ → Bool) → Bool
  | 0, _ => true
  | n + 1, f => f n && below n f

theorem use_below {n t : ℕ} {f : ℕ → Bool} (h : below n f = true) (ht : t < n) :
    f t = true := by
  induction n with
  | zero => omega
  | succ n ih =>
    have parts : f n = true ∧ below n f = true := by
      simpa only [below, Bool.and_eq_true] using h
    by_cases smaller : t < n
    · exact ih parts.2 smaller
    · have same : t = n := by omega
      simpa only [same] using parts.1

private theorem below_succ {n : ℕ} {f : ℕ → Bool} (h : below n f = true) (hf : f n = true) :
    below (n+1) f = true := by
  simp only [below, Bool.and_eq_true]
  exact ⟨hf,h⟩

private theorem below_zero (f : ℕ → Bool) : below 0 f = true := rfl

-- Concatenate two verified consecutive ranges of the same predicate.
private theorem below_extend (n m : ℕ) (f : ℕ → Bool)
    (hFirst : below n f = true) (hRest : below m (fun t => f (n + t)) = true) :
    below (n + m) f = true := by
  induction m with
  | zero => exact hFirst
  | succ m ih =>
    have parts : f (n + m) = true ∧ below m (fun t => f (n + t)) = true := by
      simpa only [below, Bool.and_eq_true] using hRest
    exact below_succ (ih parts.2) parts.1


def segment (lo hi : ℕ) (f : ℕ → Bool) : Bool :=
  let n := hi+1-lo
  below (n/128+1) fun b => below (min 128 (n-128*b)) fun j => f (lo+128*b+j)

theorem use_segment {lo hi r : ℕ} {f : ℕ → Bool} (h : segment lo hi f = true)
    (hl : lo ≤ r) (hu : r ≤ hi) : f r = true := by
  let t := r-lo
  have ht : t < hi+1-lo := by dsimp [t]; omega
  have hb : t/128 < (hi+1-lo)/128+1 := by omega
  have hj : t%128 < min 128 (hi+1-lo-128*(t/128)) := by omega
  have H := use_below (use_below h hb) hj
  have he : lo+128*(t/128)+t%128 = r := by dsimp [t]; omega
  simpa only [he] using H

def shortPlace (x : ℕ) : ℕ :=
  if x<10 then 10 else if x<100 then 100 else if x<1000 then 1000 else 10000

def squareMiss (a V r Q : ℕ) : Bool :=
  let A := 2*shortPlace a+a
  let den := 2^a*r^2-100*V
  let num := (100*A*Q+10)*V+10*r+2
  let q := num/den
  decide (¬(den*q = num ∧ 2 < q ∧ q < r ∧ Q/10 ≤ q ∧ q < Q))

def squareRow (i : ℕ) : Bool :=
  let a := i+1
  let A := 2*shortPlace a+a
  below 6 fun d =>
    let V := 10^(d+1)
    let hi := min (V-1) (((1000*A+122)*V/2^a).sqrt)
    segment (10^d) hi fun r => below 6 fun u => squareMiss a V r (10^(u+1))


private def squareCap (i d : ℕ) : ℕ :=
  let a := i+1
  let V := 10^(d+1)
  min (V-1) (((1000*(2*shortPlace a+a)+122)*V/2^a).sqrt)

private def squareBlock (i d b : ℕ) : Bool :=
  let lo := 10^d
  let n := squareCap i d+1-lo
  below (min 128 (n-128*b)) fun j =>
    below 6 fun u => squareMiss (i+1) (10^(d+1)) (lo+128*b+j) (10^(u+1))

private def squareWidth (i d : ℕ) : Bool :=
  below ((squareCap i d+1-10^d)/128+1) (squareBlock i d)

private theorem width_of_blocks (i d blocks : ℕ)
    (hcount : (squareCap i d+1-10^d)/128+1 = blocks)
    (h : below blocks (squareBlock i d) = true) : squareWidth i d = true := by
  unfold squareWidth
  rwa [hcount]

private theorem row_of_widths (i : ℕ) (h : below 6 (squareWidth i) = true) :
    squareRow i = true := h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_0_0 : below 1 (squareBlock 0 0) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_0_1 : below 1 (squareBlock 0 1) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_0_2 : below 8 (squareBlock 0 2) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_0_3_8 : below 8 (squareBlock 0 3) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_0_3_16 : below 16 (squareBlock 0 3) = true :=
  below_extend 8 8 (squareBlock 0 3)
    (square_0_3_8) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_0_3_24 : below 24 (squareBlock 0 3) = true :=
  below_extend 16 8 (squareBlock 0 3)
    (square_0_3_16) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_0_3_32 : below 32 (squareBlock 0 3) = true :=
  below_extend 24 8 (squareBlock 0 3)
    (square_0_3_24) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_0_3_40 : below 40 (squareBlock 0 3) = true :=
  below_extend 32 8 (squareBlock 0 3)
    (square_0_3_32) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_0_3_48 : below 48 (squareBlock 0 3) = true :=
  below_extend 40 8 (squareBlock 0 3)
    (square_0_3_40) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_0_3_56 : below 56 (squareBlock 0 3) = true :=
  below_extend 48 8 (squareBlock 0 3)
    (square_0_3_48) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_0_3_64 : below 64 (squareBlock 0 3) = true :=
  below_extend 56 8 (squareBlock 0 3)
    (square_0_3_56) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_0_3 : below 71 (squareBlock 0 3) = true :=
  below_extend 64 7 (squareBlock 0 3)
    (square_0_3_64) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_0_4_8 : below 8 (squareBlock 0 4) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_0_4_16 : below 16 (squareBlock 0 4) = true :=
  below_extend 8 8 (squareBlock 0 4)
    (square_0_4_8) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_0_4_24 : below 24 (squareBlock 0 4) = true :=
  below_extend 16 8 (squareBlock 0 4)
    (square_0_4_16) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_0_4_32 : below 32 (squareBlock 0 4) = true :=
  below_extend 24 8 (squareBlock 0 4)
    (square_0_4_24) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_0_4_40 : below 40 (squareBlock 0 4) = true :=
  below_extend 32 8 (squareBlock 0 4)
    (square_0_4_32) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_0_4_48 : below 48 (squareBlock 0 4) = true :=
  below_extend 40 8 (squareBlock 0 4)
    (square_0_4_40) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_0_4_56 : below 56 (squareBlock 0 4) = true :=
  below_extend 48 8 (squareBlock 0 4)
    (square_0_4_48) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_0_4_64 : below 64 (squareBlock 0 4) = true :=
  below_extend 56 8 (squareBlock 0 4)
    (square_0_4_56) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_0_4_72 : below 72 (squareBlock 0 4) = true :=
  below_extend 64 8 (squareBlock 0 4)
    (square_0_4_64) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_0_4_80 : below 80 (squareBlock 0 4) = true :=
  below_extend 72 8 (squareBlock 0 4)
    (square_0_4_72) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_0_4_88 : below 88 (squareBlock 0 4) = true :=
  below_extend 80 8 (squareBlock 0 4)
    (square_0_4_80) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_0_4_96 : below 96 (squareBlock 0 4) = true :=
  below_extend 88 8 (squareBlock 0 4)
    (square_0_4_88) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_0_4_104 : below 104 (squareBlock 0 4) = true :=
  below_extend 96 8 (squareBlock 0 4)
    (square_0_4_96) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_0_4_112 : below 112 (squareBlock 0 4) = true :=
  below_extend 104 8 (squareBlock 0 4)
    (square_0_4_104) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_0_4_120 : below 120 (squareBlock 0 4) = true :=
  below_extend 112 8 (squareBlock 0 4)
    (square_0_4_112) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_0_4_128 : below 128 (squareBlock 0 4) = true :=
  below_extend 120 8 (squareBlock 0 4)
    (square_0_4_120) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_0_4_136 : below 136 (squareBlock 0 4) = true :=
  below_extend 128 8 (squareBlock 0 4)
    (square_0_4_128) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_0_4_144 : below 144 (squareBlock 0 4) = true :=
  below_extend 136 8 (squareBlock 0 4)
    (square_0_4_136) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_0_4_152 : below 152 (squareBlock 0 4) = true :=
  below_extend 144 8 (squareBlock 0 4)
    (square_0_4_144) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_0_4_160 : below 160 (squareBlock 0 4) = true :=
  below_extend 152 8 (squareBlock 0 4)
    (square_0_4_152) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_0_4_168 : below 168 (squareBlock 0 4) = true :=
  below_extend 160 8 (squareBlock 0 4)
    (square_0_4_160) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_0_4 : below 176 (squareBlock 0 4) = true :=
  below_extend 168 8 (squareBlock 0 4)
    (square_0_4_168) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_0_5_8 : below 8 (squareBlock 0 5) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_0_5_16 : below 16 (squareBlock 0 5) = true :=
  below_extend 8 8 (squareBlock 0 5)
    (square_0_5_8) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_0_5 : below 22 (squareBlock 0 5) = true :=
  below_extend 16 6 (squareBlock 0 5)
    (square_0_5_16) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem widths_0 : below 6 (squareWidth 0) = true :=
  @below_succ 5 (squareWidth 0) (@below_succ 4 (squareWidth 0) (@below_succ 3 (squareWidth 0) (@below_succ 2 (squareWidth 0) (@below_succ 1 (squareWidth 0) (@below_succ 0 (squareWidth 0) (below_zero (squareWidth 0)) (width_of_blocks 0 0 1 (by decide +kernel) square_0_0)) (width_of_blocks 0 1 1 (by decide +kernel) square_0_1)) (width_of_blocks 0 2 8 (by decide +kernel) square_0_2)) (width_of_blocks 0 3 71 (by decide +kernel) square_0_3)) (width_of_blocks 0 4 176 (by decide +kernel) square_0_4)) (width_of_blocks 0 5 22 (by decide +kernel) square_0_5)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_1_0 : below 1 (squareBlock 1 0) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_1_1 : below 1 (squareBlock 1 1) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_1_2 : below 8 (squareBlock 1 2) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_1_3_8 : below 8 (squareBlock 1 3) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_1_3_16 : below 16 (squareBlock 1 3) = true :=
  below_extend 8 8 (squareBlock 1 3)
    (square_1_3_8) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_1_3_24 : below 24 (squareBlock 1 3) = true :=
  below_extend 16 8 (squareBlock 1 3)
    (square_1_3_16) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_1_3_32 : below 32 (squareBlock 1 3) = true :=
  below_extend 24 8 (squareBlock 1 3)
    (square_1_3_24) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_1_3_40 : below 40 (squareBlock 1 3) = true :=
  below_extend 32 8 (squareBlock 1 3)
    (square_1_3_32) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_1_3_48 : below 48 (squareBlock 1 3) = true :=
  below_extend 40 8 (squareBlock 1 3)
    (square_1_3_40) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_1_3 : below 51 (squareBlock 1 3) = true :=
  below_extend 48 3 (squareBlock 1 3)
    (square_1_3_48) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_1_4_8 : below 8 (squareBlock 1 4) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_1_4_16 : below 16 (squareBlock 1 4) = true :=
  below_extend 8 8 (squareBlock 1 4)
    (square_1_4_8) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_1_4_24 : below 24 (squareBlock 1 4) = true :=
  below_extend 16 8 (squareBlock 1 4)
    (square_1_4_16) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_1_4_32 : below 32 (squareBlock 1 4) = true :=
  below_extend 24 8 (squareBlock 1 4)
    (square_1_4_24) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_1_4_40 : below 40 (squareBlock 1 4) = true :=
  below_extend 32 8 (squareBlock 1 4)
    (square_1_4_32) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_1_4_48 : below 48 (squareBlock 1 4) = true :=
  below_extend 40 8 (squareBlock 1 4)
    (square_1_4_40) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_1_4_56 : below 56 (squareBlock 1 4) = true :=
  below_extend 48 8 (squareBlock 1 4)
    (square_1_4_48) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_1_4_64 : below 64 (squareBlock 1 4) = true :=
  below_extend 56 8 (squareBlock 1 4)
    (square_1_4_56) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_1_4_72 : below 72 (squareBlock 1 4) = true :=
  below_extend 64 8 (squareBlock 1 4)
    (square_1_4_64) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_1_4_80 : below 80 (squareBlock 1 4) = true :=
  below_extend 72 8 (squareBlock 1 4)
    (square_1_4_72) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_1_4_88 : below 88 (squareBlock 1 4) = true :=
  below_extend 80 8 (squareBlock 1 4)
    (square_1_4_80) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_1_4_96 : below 96 (squareBlock 1 4) = true :=
  below_extend 88 8 (squareBlock 1 4)
    (square_1_4_88) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_1_4_104 : below 104 (squareBlock 1 4) = true :=
  below_extend 96 8 (squareBlock 1 4)
    (square_1_4_96) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_1_4 : below 106 (squareBlock 1 4) = true :=
  below_extend 104 2 (squareBlock 1 4)
    (square_1_4_104) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_1_5 : below 1 (squareBlock 1 5) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem widths_1 : below 6 (squareWidth 1) = true :=
  @below_succ 5 (squareWidth 1) (@below_succ 4 (squareWidth 1) (@below_succ 3 (squareWidth 1) (@below_succ 2 (squareWidth 1) (@below_succ 1 (squareWidth 1) (@below_succ 0 (squareWidth 1) (below_zero (squareWidth 1)) (width_of_blocks 1 0 1 (by decide +kernel) square_1_0)) (width_of_blocks 1 1 1 (by decide +kernel) square_1_1)) (width_of_blocks 1 2 8 (by decide +kernel) square_1_2)) (width_of_blocks 1 3 51 (by decide +kernel) square_1_3)) (width_of_blocks 1 4 106 (by decide +kernel) square_1_4)) (width_of_blocks 1 5 1 (by decide +kernel) square_1_5)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_2_0 : below 1 (squareBlock 2 0) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_2_1 : below 1 (squareBlock 2 1) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_2_2 : below 8 (squareBlock 2 2) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_2_3_8 : below 8 (squareBlock 2 3) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_2_3_16 : below 16 (squareBlock 2 3) = true :=
  below_extend 8 8 (squareBlock 2 3)
    (square_2_3_8) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_2_3_24 : below 24 (squareBlock 2 3) = true :=
  below_extend 16 8 (squareBlock 2 3)
    (square_2_3_16) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_2_3_32 : below 32 (squareBlock 2 3) = true :=
  below_extend 24 8 (squareBlock 2 3)
    (square_2_3_24) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_2_3 : below 35 (squareBlock 2 3) = true :=
  below_extend 32 3 (squareBlock 2 3)
    (square_2_3_32) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_2_4_8 : below 8 (squareBlock 2 4) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_2_4_16 : below 16 (squareBlock 2 4) = true :=
  below_extend 8 8 (squareBlock 2 4)
    (square_2_4_8) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_2_4_24 : below 24 (squareBlock 2 4) = true :=
  below_extend 16 8 (squareBlock 2 4)
    (square_2_4_16) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_2_4_32 : below 32 (squareBlock 2 4) = true :=
  below_extend 24 8 (squareBlock 2 4)
    (square_2_4_24) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_2_4_40 : below 40 (squareBlock 2 4) = true :=
  below_extend 32 8 (squareBlock 2 4)
    (square_2_4_32) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_2_4_48 : below 48 (squareBlock 2 4) = true :=
  below_extend 40 8 (squareBlock 2 4)
    (square_2_4_40) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_2_4 : below 55 (squareBlock 2 4) = true :=
  below_extend 48 7 (squareBlock 2 4)
    (square_2_4_48) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_2_5 : below 1 (squareBlock 2 5) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem widths_2 : below 6 (squareWidth 2) = true :=
  @below_succ 5 (squareWidth 2) (@below_succ 4 (squareWidth 2) (@below_succ 3 (squareWidth 2) (@below_succ 2 (squareWidth 2) (@below_succ 1 (squareWidth 2) (@below_succ 0 (squareWidth 2) (below_zero (squareWidth 2)) (width_of_blocks 2 0 1 (by decide +kernel) square_2_0)) (width_of_blocks 2 1 1 (by decide +kernel) square_2_1)) (width_of_blocks 2 2 8 (by decide +kernel) square_2_2)) (width_of_blocks 2 3 35 (by decide +kernel) square_2_3)) (width_of_blocks 2 4 55 (by decide +kernel) square_2_4)) (width_of_blocks 2 5 1 (by decide +kernel) square_2_5)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_3_0 : below 1 (squareBlock 3 0) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_3_1 : below 1 (squareBlock 3 1) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_3_2 : below 8 (squareBlock 3 2) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_3_3_8 : below 8 (squareBlock 3 3) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_3_3_16 : below 16 (squareBlock 3 3) = true :=
  below_extend 8 8 (squareBlock 3 3)
    (square_3_3_8) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_3_3 : below 23 (squareBlock 3 3) = true :=
  below_extend 16 7 (squareBlock 3 3)
    (square_3_3_16) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_3_4_8 : below 8 (squareBlock 3 4) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_3_4_16 : below 16 (squareBlock 3 4) = true :=
  below_extend 8 8 (squareBlock 3 4)
    (square_3_4_8) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_3_4 : below 18 (squareBlock 3 4) = true :=
  below_extend 16 2 (squareBlock 3 4)
    (square_3_4_16) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_3_5 : below 1 (squareBlock 3 5) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem widths_3 : below 6 (squareWidth 3) = true :=
  @below_succ 5 (squareWidth 3) (@below_succ 4 (squareWidth 3) (@below_succ 3 (squareWidth 3) (@below_succ 2 (squareWidth 3) (@below_succ 1 (squareWidth 3) (@below_succ 0 (squareWidth 3) (below_zero (squareWidth 3)) (width_of_blocks 3 0 1 (by decide +kernel) square_3_0)) (width_of_blocks 3 1 1 (by decide +kernel) square_3_1)) (width_of_blocks 3 2 8 (by decide +kernel) square_3_2)) (width_of_blocks 3 3 23 (by decide +kernel) square_3_3)) (width_of_blocks 3 4 18 (by decide +kernel) square_3_4)) (width_of_blocks 3 5 1 (by decide +kernel) square_3_5)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_4_0 : below 1 (squareBlock 4 0) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_4_1 : below 1 (squareBlock 4 1) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_4_2 : below 7 (squareBlock 4 2) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_4_3_8 : below 8 (squareBlock 4 3) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_4_3 : below 15 (squareBlock 4 3) = true :=
  below_extend 8 7 (squareBlock 4 3)
    (square_4_3_8) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_4_4 : below 1 (squareBlock 4 4) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_4_5 : below 1 (squareBlock 4 5) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem widths_4 : below 6 (squareWidth 4) = true :=
  @below_succ 5 (squareWidth 4) (@below_succ 4 (squareWidth 4) (@below_succ 3 (squareWidth 4) (@below_succ 2 (squareWidth 4) (@below_succ 1 (squareWidth 4) (@below_succ 0 (squareWidth 4) (below_zero (squareWidth 4)) (width_of_blocks 4 0 1 (by decide +kernel) square_4_0)) (width_of_blocks 4 1 1 (by decide +kernel) square_4_1)) (width_of_blocks 4 2 7 (by decide +kernel) square_4_2)) (width_of_blocks 4 3 15 (by decide +kernel) square_4_3)) (width_of_blocks 4 4 1 (by decide +kernel) square_4_4)) (width_of_blocks 4 5 1 (by decide +kernel) square_4_5)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_5_0 : below 1 (squareBlock 5 0) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_5_1 : below 1 (squareBlock 5 1) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_5_2 : below 5 (squareBlock 5 2) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_5_3 : below 8 (squareBlock 5 3) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_5_4 : below 1 (squareBlock 5 4) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_5_5 : below 1 (squareBlock 5 5) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem widths_5 : below 6 (squareWidth 5) = true :=
  @below_succ 5 (squareWidth 5) (@below_succ 4 (squareWidth 5) (@below_succ 3 (squareWidth 5) (@below_succ 2 (squareWidth 5) (@below_succ 1 (squareWidth 5) (@below_succ 0 (squareWidth 5) (below_zero (squareWidth 5)) (width_of_blocks 5 0 1 (by decide +kernel) square_5_0)) (width_of_blocks 5 1 1 (by decide +kernel) square_5_1)) (width_of_blocks 5 2 5 (by decide +kernel) square_5_2)) (width_of_blocks 5 3 8 (by decide +kernel) square_5_3)) (width_of_blocks 5 4 1 (by decide +kernel) square_5_4)) (width_of_blocks 5 5 1 (by decide +kernel) square_5_5)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_6_0 : below 1 (squareBlock 6 0) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_6_1 : below 1 (squareBlock 6 1) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_6_2 : below 3 (squareBlock 6 2) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_6_3 : below 4 (squareBlock 6 3) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_6_4 : below 1 (squareBlock 6 4) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_6_5 : below 1 (squareBlock 6 5) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem widths_6 : below 6 (squareWidth 6) = true :=
  @below_succ 5 (squareWidth 6) (@below_succ 4 (squareWidth 6) (@below_succ 3 (squareWidth 6) (@below_succ 2 (squareWidth 6) (@below_succ 1 (squareWidth 6) (@below_succ 0 (squareWidth 6) (below_zero (squareWidth 6)) (width_of_blocks 6 0 1 (by decide +kernel) square_6_0)) (width_of_blocks 6 1 1 (by decide +kernel) square_6_1)) (width_of_blocks 6 2 3 (by decide +kernel) square_6_2)) (width_of_blocks 6 3 4 (by decide +kernel) square_6_3)) (width_of_blocks 6 4 1 (by decide +kernel) square_6_4)) (width_of_blocks 6 5 1 (by decide +kernel) square_6_5)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_7_0 : below 1 (squareBlock 7 0) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_7_1 : below 1 (squareBlock 7 1) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_7_2 : below 2 (squareBlock 7 2) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_7_3 : below 1 (squareBlock 7 3) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_7_4 : below 1 (squareBlock 7 4) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_7_5 : below 1 (squareBlock 7 5) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem widths_7 : below 6 (squareWidth 7) = true :=
  @below_succ 5 (squareWidth 7) (@below_succ 4 (squareWidth 7) (@below_succ 3 (squareWidth 7) (@below_succ 2 (squareWidth 7) (@below_succ 1 (squareWidth 7) (@below_succ 0 (squareWidth 7) (below_zero (squareWidth 7)) (width_of_blocks 7 0 1 (by decide +kernel) square_7_0)) (width_of_blocks 7 1 1 (by decide +kernel) square_7_1)) (width_of_blocks 7 2 2 (by decide +kernel) square_7_2)) (width_of_blocks 7 3 1 (by decide +kernel) square_7_3)) (width_of_blocks 7 4 1 (by decide +kernel) square_7_4)) (width_of_blocks 7 5 1 (by decide +kernel) square_7_5)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_8_0 : below 1 (squareBlock 8 0) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_8_1 : below 1 (squareBlock 8 1) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_8_2 : below 2 (squareBlock 8 2) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_8_3 : below 1 (squareBlock 8 3) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_8_4 : below 1 (squareBlock 8 4) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_8_5 : below 1 (squareBlock 8 5) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem widths_8 : below 6 (squareWidth 8) = true :=
  @below_succ 5 (squareWidth 8) (@below_succ 4 (squareWidth 8) (@below_succ 3 (squareWidth 8) (@below_succ 2 (squareWidth 8) (@below_succ 1 (squareWidth 8) (@below_succ 0 (squareWidth 8) (below_zero (squareWidth 8)) (width_of_blocks 8 0 1 (by decide +kernel) square_8_0)) (width_of_blocks 8 1 1 (by decide +kernel) square_8_1)) (width_of_blocks 8 2 2 (by decide +kernel) square_8_2)) (width_of_blocks 8 3 1 (by decide +kernel) square_8_3)) (width_of_blocks 8 4 1 (by decide +kernel) square_8_4)) (width_of_blocks 8 5 1 (by decide +kernel) square_8_5)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_9_0 : below 1 (squareBlock 9 0) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_9_1 : below 1 (squareBlock 9 1) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_9_2 : below 3 (squareBlock 9 2) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_9_3 : below 4 (squareBlock 9 3) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_9_4 : below 1 (squareBlock 9 4) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_9_5 : below 1 (squareBlock 9 5) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem widths_9 : below 6 (squareWidth 9) = true :=
  @below_succ 5 (squareWidth 9) (@below_succ 4 (squareWidth 9) (@below_succ 3 (squareWidth 9) (@below_succ 2 (squareWidth 9) (@below_succ 1 (squareWidth 9) (@below_succ 0 (squareWidth 9) (below_zero (squareWidth 9)) (width_of_blocks 9 0 1 (by decide +kernel) square_9_0)) (width_of_blocks 9 1 1 (by decide +kernel) square_9_1)) (width_of_blocks 9 2 3 (by decide +kernel) square_9_2)) (width_of_blocks 9 3 4 (by decide +kernel) square_9_3)) (width_of_blocks 9 4 1 (by decide +kernel) square_9_4)) (width_of_blocks 9 5 1 (by decide +kernel) square_9_5)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_10_0 : below 1 (squareBlock 10 0) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_10_1 : below 1 (squareBlock 10 1) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_10_2 : below 2 (squareBlock 10 2) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_10_3 : below 1 (squareBlock 10 3) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_10_4 : below 1 (squareBlock 10 4) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_10_5 : below 1 (squareBlock 10 5) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem widths_10 : below 6 (squareWidth 10) = true :=
  @below_succ 5 (squareWidth 10) (@below_succ 4 (squareWidth 10) (@below_succ 3 (squareWidth 10) (@below_succ 2 (squareWidth 10) (@below_succ 1 (squareWidth 10) (@below_succ 0 (squareWidth 10) (below_zero (squareWidth 10)) (width_of_blocks 10 0 1 (by decide +kernel) square_10_0)) (width_of_blocks 10 1 1 (by decide +kernel) square_10_1)) (width_of_blocks 10 2 2 (by decide +kernel) square_10_2)) (width_of_blocks 10 3 1 (by decide +kernel) square_10_3)) (width_of_blocks 10 4 1 (by decide +kernel) square_10_4)) (width_of_blocks 10 5 1 (by decide +kernel) square_10_5)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_11_0 : below 1 (squareBlock 11 0) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_11_1 : below 1 (squareBlock 11 1) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_11_2 : below 2 (squareBlock 11 2) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_11_3 : below 1 (squareBlock 11 3) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_11_4 : below 1 (squareBlock 11 4) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_11_5 : below 1 (squareBlock 11 5) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem widths_11 : below 6 (squareWidth 11) = true :=
  @below_succ 5 (squareWidth 11) (@below_succ 4 (squareWidth 11) (@below_succ 3 (squareWidth 11) (@below_succ 2 (squareWidth 11) (@below_succ 1 (squareWidth 11) (@below_succ 0 (squareWidth 11) (below_zero (squareWidth 11)) (width_of_blocks 11 0 1 (by decide +kernel) square_11_0)) (width_of_blocks 11 1 1 (by decide +kernel) square_11_1)) (width_of_blocks 11 2 2 (by decide +kernel) square_11_2)) (width_of_blocks 11 3 1 (by decide +kernel) square_11_3)) (width_of_blocks 11 4 1 (by decide +kernel) square_11_4)) (width_of_blocks 11 5 1 (by decide +kernel) square_11_5)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_12_0 : below 1 (squareBlock 12 0) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_12_1 : below 1 (squareBlock 12 1) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_12_2 : below 1 (squareBlock 12 2) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_12_3 : below 1 (squareBlock 12 3) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_12_4 : below 1 (squareBlock 12 4) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_12_5 : below 1 (squareBlock 12 5) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem widths_12 : below 6 (squareWidth 12) = true :=
  @below_succ 5 (squareWidth 12) (@below_succ 4 (squareWidth 12) (@below_succ 3 (squareWidth 12) (@below_succ 2 (squareWidth 12) (@below_succ 1 (squareWidth 12) (@below_succ 0 (squareWidth 12) (below_zero (squareWidth 12)) (width_of_blocks 12 0 1 (by decide +kernel) square_12_0)) (width_of_blocks 12 1 1 (by decide +kernel) square_12_1)) (width_of_blocks 12 2 1 (by decide +kernel) square_12_2)) (width_of_blocks 12 3 1 (by decide +kernel) square_12_3)) (width_of_blocks 12 4 1 (by decide +kernel) square_12_4)) (width_of_blocks 12 5 1 (by decide +kernel) square_12_5)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_13_0 : below 1 (squareBlock 13 0) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_13_1 : below 1 (squareBlock 13 1) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_13_2 : below 1 (squareBlock 13 2) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_13_3 : below 1 (squareBlock 13 3) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_13_4 : below 1 (squareBlock 13 4) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_13_5 : below 1 (squareBlock 13 5) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem widths_13 : below 6 (squareWidth 13) = true :=
  @below_succ 5 (squareWidth 13) (@below_succ 4 (squareWidth 13) (@below_succ 3 (squareWidth 13) (@below_succ 2 (squareWidth 13) (@below_succ 1 (squareWidth 13) (@below_succ 0 (squareWidth 13) (below_zero (squareWidth 13)) (width_of_blocks 13 0 1 (by decide +kernel) square_13_0)) (width_of_blocks 13 1 1 (by decide +kernel) square_13_1)) (width_of_blocks 13 2 1 (by decide +kernel) square_13_2)) (width_of_blocks 13 3 1 (by decide +kernel) square_13_3)) (width_of_blocks 13 4 1 (by decide +kernel) square_13_4)) (width_of_blocks 13 5 1 (by decide +kernel) square_13_5)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_14_0 : below 1 (squareBlock 14 0) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_14_1 : below 1 (squareBlock 14 1) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_14_2 : below 1 (squareBlock 14 2) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_14_3 : below 1 (squareBlock 14 3) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_14_4 : below 1 (squareBlock 14 4) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_14_5 : below 1 (squareBlock 14 5) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem widths_14 : below 6 (squareWidth 14) = true :=
  @below_succ 5 (squareWidth 14) (@below_succ 4 (squareWidth 14) (@below_succ 3 (squareWidth 14) (@below_succ 2 (squareWidth 14) (@below_succ 1 (squareWidth 14) (@below_succ 0 (squareWidth 14) (below_zero (squareWidth 14)) (width_of_blocks 14 0 1 (by decide +kernel) square_14_0)) (width_of_blocks 14 1 1 (by decide +kernel) square_14_1)) (width_of_blocks 14 2 1 (by decide +kernel) square_14_2)) (width_of_blocks 14 3 1 (by decide +kernel) square_14_3)) (width_of_blocks 14 4 1 (by decide +kernel) square_14_4)) (width_of_blocks 14 5 1 (by decide +kernel) square_14_5)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_15_0 : below 1 (squareBlock 15 0) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_15_1 : below 1 (squareBlock 15 1) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_15_2 : below 1 (squareBlock 15 2) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_15_3 : below 1 (squareBlock 15 3) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_15_4 : below 1 (squareBlock 15 4) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_15_5 : below 1 (squareBlock 15 5) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem widths_15 : below 6 (squareWidth 15) = true :=
  @below_succ 5 (squareWidth 15) (@below_succ 4 (squareWidth 15) (@below_succ 3 (squareWidth 15) (@below_succ 2 (squareWidth 15) (@below_succ 1 (squareWidth 15) (@below_succ 0 (squareWidth 15) (below_zero (squareWidth 15)) (width_of_blocks 15 0 1 (by decide +kernel) square_15_0)) (width_of_blocks 15 1 1 (by decide +kernel) square_15_1)) (width_of_blocks 15 2 1 (by decide +kernel) square_15_2)) (width_of_blocks 15 3 1 (by decide +kernel) square_15_3)) (width_of_blocks 15 4 1 (by decide +kernel) square_15_4)) (width_of_blocks 15 5 1 (by decide +kernel) square_15_5)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_16_0 : below 1 (squareBlock 16 0) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_16_1 : below 1 (squareBlock 16 1) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_16_2 : below 1 (squareBlock 16 2) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_16_3 : below 1 (squareBlock 16 3) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_16_4 : below 1 (squareBlock 16 4) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_16_5 : below 1 (squareBlock 16 5) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem widths_16 : below 6 (squareWidth 16) = true :=
  @below_succ 5 (squareWidth 16) (@below_succ 4 (squareWidth 16) (@below_succ 3 (squareWidth 16) (@below_succ 2 (squareWidth 16) (@below_succ 1 (squareWidth 16) (@below_succ 0 (squareWidth 16) (below_zero (squareWidth 16)) (width_of_blocks 16 0 1 (by decide +kernel) square_16_0)) (width_of_blocks 16 1 1 (by decide +kernel) square_16_1)) (width_of_blocks 16 2 1 (by decide +kernel) square_16_2)) (width_of_blocks 16 3 1 (by decide +kernel) square_16_3)) (width_of_blocks 16 4 1 (by decide +kernel) square_16_4)) (width_of_blocks 16 5 1 (by decide +kernel) square_16_5)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_17_0 : below 1 (squareBlock 17 0) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_17_1 : below 1 (squareBlock 17 1) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_17_2 : below 1 (squareBlock 17 2) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_17_3 : below 1 (squareBlock 17 3) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_17_4 : below 1 (squareBlock 17 4) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_17_5 : below 1 (squareBlock 17 5) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem widths_17 : below 6 (squareWidth 17) = true :=
  @below_succ 5 (squareWidth 17) (@below_succ 4 (squareWidth 17) (@below_succ 3 (squareWidth 17) (@below_succ 2 (squareWidth 17) (@below_succ 1 (squareWidth 17) (@below_succ 0 (squareWidth 17) (below_zero (squareWidth 17)) (width_of_blocks 17 0 1 (by decide +kernel) square_17_0)) (width_of_blocks 17 1 1 (by decide +kernel) square_17_1)) (width_of_blocks 17 2 1 (by decide +kernel) square_17_2)) (width_of_blocks 17 3 1 (by decide +kernel) square_17_3)) (width_of_blocks 17 4 1 (by decide +kernel) square_17_4)) (width_of_blocks 17 5 1 (by decide +kernel) square_17_5)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_18_0 : below 1 (squareBlock 18 0) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_18_1 : below 1 (squareBlock 18 1) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_18_2 : below 1 (squareBlock 18 2) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_18_3 : below 1 (squareBlock 18 3) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_18_4 : below 1 (squareBlock 18 4) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_18_5 : below 1 (squareBlock 18 5) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem widths_18 : below 6 (squareWidth 18) = true :=
  @below_succ 5 (squareWidth 18) (@below_succ 4 (squareWidth 18) (@below_succ 3 (squareWidth 18) (@below_succ 2 (squareWidth 18) (@below_succ 1 (squareWidth 18) (@below_succ 0 (squareWidth 18) (below_zero (squareWidth 18)) (width_of_blocks 18 0 1 (by decide +kernel) square_18_0)) (width_of_blocks 18 1 1 (by decide +kernel) square_18_1)) (width_of_blocks 18 2 1 (by decide +kernel) square_18_2)) (width_of_blocks 18 3 1 (by decide +kernel) square_18_3)) (width_of_blocks 18 4 1 (by decide +kernel) square_18_4)) (width_of_blocks 18 5 1 (by decide +kernel) square_18_5)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_19_0 : below 1 (squareBlock 19 0) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_19_1 : below 1 (squareBlock 19 1) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_19_2 : below 1 (squareBlock 19 2) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_19_3 : below 1 (squareBlock 19 3) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_19_4 : below 1 (squareBlock 19 4) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_19_5 : below 1 (squareBlock 19 5) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem widths_19 : below 6 (squareWidth 19) = true :=
  @below_succ 5 (squareWidth 19) (@below_succ 4 (squareWidth 19) (@below_succ 3 (squareWidth 19) (@below_succ 2 (squareWidth 19) (@below_succ 1 (squareWidth 19) (@below_succ 0 (squareWidth 19) (below_zero (squareWidth 19)) (width_of_blocks 19 0 1 (by decide +kernel) square_19_0)) (width_of_blocks 19 1 1 (by decide +kernel) square_19_1)) (width_of_blocks 19 2 1 (by decide +kernel) square_19_2)) (width_of_blocks 19 3 1 (by decide +kernel) square_19_3)) (width_of_blocks 19 4 1 (by decide +kernel) square_19_4)) (width_of_blocks 19 5 1 (by decide +kernel) square_19_5)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_20_0 : below 1 (squareBlock 20 0) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_20_1 : below 1 (squareBlock 20 1) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_20_2 : below 1 (squareBlock 20 2) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_20_3 : below 1 (squareBlock 20 3) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_20_4 : below 1 (squareBlock 20 4) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_20_5 : below 1 (squareBlock 20 5) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem widths_20 : below 6 (squareWidth 20) = true :=
  @below_succ 5 (squareWidth 20) (@below_succ 4 (squareWidth 20) (@below_succ 3 (squareWidth 20) (@below_succ 2 (squareWidth 20) (@below_succ 1 (squareWidth 20) (@below_succ 0 (squareWidth 20) (below_zero (squareWidth 20)) (width_of_blocks 20 0 1 (by decide +kernel) square_20_0)) (width_of_blocks 20 1 1 (by decide +kernel) square_20_1)) (width_of_blocks 20 2 1 (by decide +kernel) square_20_2)) (width_of_blocks 20 3 1 (by decide +kernel) square_20_3)) (width_of_blocks 20 4 1 (by decide +kernel) square_20_4)) (width_of_blocks 20 5 1 (by decide +kernel) square_20_5)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_21_0 : below 1 (squareBlock 21 0) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_21_1 : below 1 (squareBlock 21 1) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_21_2 : below 1 (squareBlock 21 2) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_21_3 : below 1 (squareBlock 21 3) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_21_4 : below 1 (squareBlock 21 4) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem square_21_5 : below 1 (squareBlock 21 5) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem widths_21 : below 6 (squareWidth 21) = true :=
  @below_succ 5 (squareWidth 21) (@below_succ 4 (squareWidth 21) (@below_succ 3 (squareWidth 21) (@below_succ 2 (squareWidth 21) (@below_succ 1 (squareWidth 21) (@below_succ 0 (squareWidth 21) (below_zero (squareWidth 21)) (width_of_blocks 21 0 1 (by decide +kernel) square_21_0)) (width_of_blocks 21 1 1 (by decide +kernel) square_21_1)) (width_of_blocks 21 2 1 (by decide +kernel) square_21_2)) (width_of_blocks 21 3 1 (by decide +kernel) square_21_3)) (width_of_blocks 21 4 1 (by decide +kernel) square_21_4)) (width_of_blocks 21 5 1 (by decide +kernel) square_21_5)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem all_widths_8 : below 8 (squareRow) = true :=
  @below_succ 7 (squareRow) (@below_succ 6 (squareRow) (@below_succ 5 (squareRow) (@below_succ 4 (squareRow) (@below_succ 3 (squareRow) (@below_succ 2 (squareRow) (@below_succ 1 (squareRow) (@below_succ 0 (squareRow) (below_zero (squareRow)) (row_of_widths 0 widths_0)) (row_of_widths 1 widths_1)) (row_of_widths 2 widths_2)) (row_of_widths 3 widths_3)) (row_of_widths 4 widths_4)) (row_of_widths 5 widths_5)) (row_of_widths 6 widths_6)) (row_of_widths 7 widths_7)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem all_widths_16 : below 16 (squareRow) = true :=
  @below_succ 15 (squareRow) (@below_succ 14 (squareRow) (@below_succ 13 (squareRow) (@below_succ 12 (squareRow) (@below_succ 11 (squareRow) (@below_succ 10 (squareRow) (@below_succ 9 (squareRow) (@below_succ 8 (squareRow) (all_widths_8) (row_of_widths 8 widths_8)) (row_of_widths 9 widths_9)) (row_of_widths 10 widths_10)) (row_of_widths 11 widths_11)) (row_of_widths 12 widths_12)) (row_of_widths 13 widths_13)) (row_of_widths 14 widths_14)) (row_of_widths 15 widths_15)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem all_widths : below 22 (squareRow) = true :=
  @below_succ 21 (squareRow) (@below_succ 20 (squareRow) (@below_succ 19 (squareRow) (@below_succ 18 (squareRow) (@below_succ 17 (squareRow) (@below_succ 16 (squareRow) (all_widths_16) (row_of_widths 16 widths_16)) (row_of_widths 17 widths_17)) (row_of_widths 18 widths_18)) (row_of_widths 19 widths_19)) (row_of_widths 20 widths_20)) (row_of_widths 21 widths_21)

theorem squares_checked : below 22 squareRow = true := all_widths

def rootMiss (m e z : ℕ) : ℕ → ℕ → ℕ → Bool
  | 0, _, _ => false
  | fuel+1, lo, hi =>
    if hi < lo ∨ 10*lo+z < m*lo^e ∨ m*hi^e < 10*hi+z then true else
      let t := (lo+hi)/2
      if m*t^e < 10*t+z then rootMiss m e z fuel (t+1) hi
      else if 10*t+z < m*t^e then rootMiss m e z fuel lo (t-1)
      else false

def nonlinearDigits (p q i j k : ℕ) : Bool :=
  let m := p^(i+1)*q^(j+1)
  let C := ((p*shortPlace (i+1)+(i+1))*shortPlace q+q)*shortPlace (j+1)+(j+1)
  let cap := if k=1 then 222222 else 999
  below 6 fun d =>
    let V := 10^(d+1)
    rootMiss m (k+1) (10*C*V+(k+1)) 20 (max (q+1) (10^d)) (min (V-1) cap)

def candidate (v : ℕ) : Bool :=
  decide (v=2 ∨ v=3 ∨ v=5 ∨ (v%2≠0 ∧ v%3≠0 ∧ v%5≠0))

theorem candidate_of_prime {v : ℕ} (hp : v.Prime) : candidate v = true := by
  have cop {s : ℕ} (hs : 2 ≤ s) (hn : v ≠ s) : v%s ≠ 0 := by
    intro h
    exact hn ((Nat.dvd_prime_two_le hp hs).mp (Nat.dvd_of_mod_eq_zero h)).symm
  apply decide_eq_true
  by_cases h₂ : v=2
  · exact Or.inl h₂
  by_cases h₃ : v=3
  · exact Or.inr (Or.inl h₃)
  by_cases h₅ : v=5
  · exact Or.inr (Or.inr (Or.inl h₅))
  exact Or.inr (Or.inr (Or.inr ⟨cop (by decide) h₂,cop (by decide) h₃,cop (by decide) h₅⟩))

def scanQ (p i j k bound : ℕ) : ℕ → ℕ → Bool
  | 0, _ => true
  | fuel+1, q =>
    if bound < p^i*q^j*(q+1)^k then true else
      (if candidate q then nonlinearDigits p q i j k else true) && scanQ p i j k bound fuel (q+1)

theorem scan_use {p i j k bound q : ℕ} (hq : q.Prime) (fit : p^i*q^j*(q+1)^k ≤ bound)
    (fuel lo : ℕ) (hl : lo ≤ q) (hu : q < lo+fuel) (ok : scanQ p i j k bound fuel lo = true) :
    nonlinearDigits p q i j k = true := by
  induction fuel generalizing lo with
  | zero => omega
  | succ f ih =>
    have low : p^i*lo^j*(lo+1)^k ≤ bound :=
      (Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hl j))
        (Nat.pow_le_pow_left (by omega : lo+1 ≤ q+1) k)).trans fit
    simp only [scanQ,if_neg (Nat.not_lt.mpr low),Bool.and_eq_true] at ok
    rcases hl.eq_or_lt with rfl | hh
    · simpa [candidate_of_prime hq] using ok.1
    · exact ih (lo+1) hh (by omega) ok.2

def nonlinearAt (p k i : ℕ) : Bool :=
  if p<2 ∨ candidate p=false ∨ k=0 ∨ (k=1 ∧ p≠2) ∨ 111111*(i+1) < p^i then true else
    below 13 fun j =>
      let bound := 111111*(i+1)*(j+1)*(k+1)
      if (k=1 ∧ j=0) ∨ bound < p^i*(p+1)^j*(p+2)^k then true else
        scanQ p i j k bound 2000 (p+1)

def grid (start stride blocks : ℕ) : Bool :=
  below 9 fun k => below blocks fun b => below 22 fun i => below stride fun t =>
    nonlinearAt (start+stride*b+t) k i

end A067599Three.Check

/- # Kernel-checked intervals for repeated exponents in A067599 -/

namespace A067599Three.Check


private def perExponent (start stride k block i : ℕ) : Bool :=
  below stride fun t => nonlinearAt (start+stride*block+t) k i

private def perBlock (start stride k block : ℕ) : Bool :=
  below 22 (perExponent start stride k block)

private def perPower (start stride blocks k : ℕ) : Bool :=
  below blocks (perBlock start stride k)

private theorem grid_of_powers (start stride blocks : ℕ)
    (h : below 9 (perPower start stride blocks) = true) :
    grid start stride blocks = true := h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem small_blocks_0_8 : below 8 (perBlock 0 4 0) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem small_blocks_0 : below 16 (perBlock 0 4 0) = true :=
  below_extend 8 8 (perBlock 0 4 0)
    (small_blocks_0_8) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem small_exps_1_0_8 : below 8 (perExponent 0 4 1 0) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem small_exps_1_0_16 : below 16 (perExponent 0 4 1 0) = true :=
  below_extend 8 8 (perExponent 0 4 1 0)
    (small_exps_1_0_8) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem small_exps_1_0 : below 22 (perExponent 0 4 1 0) = true :=
  below_extend 16 6 (perExponent 0 4 1 0)
    (small_exps_1_0_16) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem small_exps_1_1_8 : below 8 (perExponent 0 4 1 1) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem small_exps_1_1_16 : below 16 (perExponent 0 4 1 1) = true :=
  below_extend 8 8 (perExponent 0 4 1 1)
    (small_exps_1_1_8) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem small_exps_1_1 : below 22 (perExponent 0 4 1 1) = true :=
  below_extend 16 6 (perExponent 0 4 1 1)
    (small_exps_1_1_16) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem small_exps_1_2_8 : below 8 (perExponent 0 4 1 2) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem small_exps_1_2_16 : below 16 (perExponent 0 4 1 2) = true :=
  below_extend 8 8 (perExponent 0 4 1 2)
    (small_exps_1_2_8) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem small_exps_1_2 : below 22 (perExponent 0 4 1 2) = true :=
  below_extend 16 6 (perExponent 0 4 1 2)
    (small_exps_1_2_16) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem small_blocks_1_8 : below 8 (perBlock 0 4 1) = true :=
  @below_succ 7 (perBlock 0 4 1) (@below_succ 6 (perBlock 0 4 1) (@below_succ 5 (perBlock 0 4 1) (@below_succ 4 (perBlock 0 4 1) (@below_succ 3 (perBlock 0 4 1) (@below_succ 2 (perBlock 0 4 1) (@below_succ 1 (perBlock 0 4 1) (@below_succ 0 (perBlock 0 4 1) (below_zero (perBlock 0 4 1)) (small_exps_1_0)) (small_exps_1_1)) (small_exps_1_2)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem small_blocks_1 : below 16 (perBlock 0 4 1) = true :=
  below_extend 8 8 (perBlock 0 4 1)
    (small_blocks_1_8) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem small_exps_2_0_8 : below 8 (perExponent 0 4 2 0) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem small_exps_2_0_16 : below 16 (perExponent 0 4 2 0) = true :=
  below_extend 8 8 (perExponent 0 4 2 0)
    (small_exps_2_0_8) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem small_exps_2_0 : below 22 (perExponent 0 4 2 0) = true :=
  below_extend 16 6 (perExponent 0 4 2 0)
    (small_exps_2_0_16) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem small_exps_2_1_8 : below 8 (perExponent 0 4 2 1) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem small_exps_2_1_16 : below 16 (perExponent 0 4 2 1) = true :=
  below_extend 8 8 (perExponent 0 4 2 1)
    (small_exps_2_1_8) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem small_exps_2_1 : below 22 (perExponent 0 4 2 1) = true :=
  below_extend 16 6 (perExponent 0 4 2 1)
    (small_exps_2_1_16) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem small_exps_2_2_8 : below 8 (perExponent 0 4 2 2) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem small_exps_2_2_16 : below 16 (perExponent 0 4 2 2) = true :=
  below_extend 8 8 (perExponent 0 4 2 2)
    (small_exps_2_2_8) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem small_exps_2_2 : below 22 (perExponent 0 4 2 2) = true :=
  below_extend 16 6 (perExponent 0 4 2 2)
    (small_exps_2_2_16) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem small_blocks_2_8 : below 8 (perBlock 0 4 2) = true :=
  @below_succ 7 (perBlock 0 4 2) (@below_succ 6 (perBlock 0 4 2) (@below_succ 5 (perBlock 0 4 2) (@below_succ 4 (perBlock 0 4 2) (@below_succ 3 (perBlock 0 4 2) (@below_succ 2 (perBlock 0 4 2) (@below_succ 1 (perBlock 0 4 2) (@below_succ 0 (perBlock 0 4 2) (below_zero (perBlock 0 4 2)) (small_exps_2_0)) (small_exps_2_1)) (small_exps_2_2)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem small_blocks_2 : below 16 (perBlock 0 4 2) = true :=
  below_extend 8 8 (perBlock 0 4 2)
    (small_blocks_2_8) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem small_exps_3_0_8 : below 8 (perExponent 0 4 3 0) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem small_exps_3_0_16 : below 16 (perExponent 0 4 3 0) = true :=
  below_extend 8 8 (perExponent 0 4 3 0)
    (small_exps_3_0_8) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem small_exps_3_0 : below 22 (perExponent 0 4 3 0) = true :=
  below_extend 16 6 (perExponent 0 4 3 0)
    (small_exps_3_0_16) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem small_exps_3_1_8 : below 8 (perExponent 0 4 3 1) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem small_exps_3_1_16 : below 16 (perExponent 0 4 3 1) = true :=
  below_extend 8 8 (perExponent 0 4 3 1)
    (small_exps_3_1_8) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem small_exps_3_1 : below 22 (perExponent 0 4 3 1) = true :=
  below_extend 16 6 (perExponent 0 4 3 1)
    (small_exps_3_1_16) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem small_exps_3_2_8 : below 8 (perExponent 0 4 3 2) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem small_exps_3_2_16 : below 16 (perExponent 0 4 3 2) = true :=
  below_extend 8 8 (perExponent 0 4 3 2)
    (small_exps_3_2_8) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem small_exps_3_2 : below 22 (perExponent 0 4 3 2) = true :=
  below_extend 16 6 (perExponent 0 4 3 2)
    (small_exps_3_2_16) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem small_blocks_3_8 : below 8 (perBlock 0 4 3) = true :=
  @below_succ 7 (perBlock 0 4 3) (@below_succ 6 (perBlock 0 4 3) (@below_succ 5 (perBlock 0 4 3) (@below_succ 4 (perBlock 0 4 3) (@below_succ 3 (perBlock 0 4 3) (@below_succ 2 (perBlock 0 4 3) (@below_succ 1 (perBlock 0 4 3) (@below_succ 0 (perBlock 0 4 3) (below_zero (perBlock 0 4 3)) (small_exps_3_0)) (small_exps_3_1)) (small_exps_3_2)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem small_blocks_3 : below 16 (perBlock 0 4 3) = true :=
  below_extend 8 8 (perBlock 0 4 3)
    (small_blocks_3_8) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem small_exps_4_0_8 : below 8 (perExponent 0 4 4 0) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem small_exps_4_0_16 : below 16 (perExponent 0 4 4 0) = true :=
  below_extend 8 8 (perExponent 0 4 4 0)
    (small_exps_4_0_8) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem small_exps_4_0 : below 22 (perExponent 0 4 4 0) = true :=
  below_extend 16 6 (perExponent 0 4 4 0)
    (small_exps_4_0_16) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem small_exps_4_1_8 : below 8 (perExponent 0 4 4 1) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem small_exps_4_1_16 : below 16 (perExponent 0 4 4 1) = true :=
  below_extend 8 8 (perExponent 0 4 4 1)
    (small_exps_4_1_8) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem small_exps_4_1 : below 22 (perExponent 0 4 4 1) = true :=
  below_extend 16 6 (perExponent 0 4 4 1)
    (small_exps_4_1_16) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem small_exps_4_2_8 : below 8 (perExponent 0 4 4 2) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem small_exps_4_2_16 : below 16 (perExponent 0 4 4 2) = true :=
  below_extend 8 8 (perExponent 0 4 4 2)
    (small_exps_4_2_8) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem small_exps_4_2 : below 22 (perExponent 0 4 4 2) = true :=
  below_extend 16 6 (perExponent 0 4 4 2)
    (small_exps_4_2_16) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem small_blocks_4_8 : below 8 (perBlock 0 4 4) = true :=
  @below_succ 7 (perBlock 0 4 4) (@below_succ 6 (perBlock 0 4 4) (@below_succ 5 (perBlock 0 4 4) (@below_succ 4 (perBlock 0 4 4) (@below_succ 3 (perBlock 0 4 4) (@below_succ 2 (perBlock 0 4 4) (@below_succ 1 (perBlock 0 4 4) (@below_succ 0 (perBlock 0 4 4) (below_zero (perBlock 0 4 4)) (small_exps_4_0)) (small_exps_4_1)) (small_exps_4_2)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem small_blocks_4 : below 16 (perBlock 0 4 4) = true :=
  below_extend 8 8 (perBlock 0 4 4)
    (small_blocks_4_8) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem small_exps_5_0_8 : below 8 (perExponent 0 4 5 0) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem small_exps_5_0_16 : below 16 (perExponent 0 4 5 0) = true :=
  below_extend 8 8 (perExponent 0 4 5 0)
    (small_exps_5_0_8) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem small_exps_5_0 : below 22 (perExponent 0 4 5 0) = true :=
  below_extend 16 6 (perExponent 0 4 5 0)
    (small_exps_5_0_16) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem small_exps_5_1_8 : below 8 (perExponent 0 4 5 1) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem small_exps_5_1_16 : below 16 (perExponent 0 4 5 1) = true :=
  below_extend 8 8 (perExponent 0 4 5 1)
    (small_exps_5_1_8) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem small_exps_5_1 : below 22 (perExponent 0 4 5 1) = true :=
  below_extend 16 6 (perExponent 0 4 5 1)
    (small_exps_5_1_16) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem small_exps_5_2_8 : below 8 (perExponent 0 4 5 2) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem small_exps_5_2_16 : below 16 (perExponent 0 4 5 2) = true :=
  below_extend 8 8 (perExponent 0 4 5 2)
    (small_exps_5_2_8) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem small_exps_5_2 : below 22 (perExponent 0 4 5 2) = true :=
  below_extend 16 6 (perExponent 0 4 5 2)
    (small_exps_5_2_16) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem small_blocks_5_8 : below 8 (perBlock 0 4 5) = true :=
  @below_succ 7 (perBlock 0 4 5) (@below_succ 6 (perBlock 0 4 5) (@below_succ 5 (perBlock 0 4 5) (@below_succ 4 (perBlock 0 4 5) (@below_succ 3 (perBlock 0 4 5) (@below_succ 2 (perBlock 0 4 5) (@below_succ 1 (perBlock 0 4 5) (@below_succ 0 (perBlock 0 4 5) (below_zero (perBlock 0 4 5)) (small_exps_5_0)) (small_exps_5_1)) (small_exps_5_2)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem small_blocks_5 : below 16 (perBlock 0 4 5) = true :=
  below_extend 8 8 (perBlock 0 4 5)
    (small_blocks_5_8) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem small_exps_6_0_8 : below 8 (perExponent 0 4 6 0) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem small_exps_6_0_16 : below 16 (perExponent 0 4 6 0) = true :=
  below_extend 8 8 (perExponent 0 4 6 0)
    (small_exps_6_0_8) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem small_exps_6_0 : below 22 (perExponent 0 4 6 0) = true :=
  below_extend 16 6 (perExponent 0 4 6 0)
    (small_exps_6_0_16) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem small_exps_6_1_8 : below 8 (perExponent 0 4 6 1) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem small_exps_6_1_16 : below 16 (perExponent 0 4 6 1) = true :=
  below_extend 8 8 (perExponent 0 4 6 1)
    (small_exps_6_1_8) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem small_exps_6_1 : below 22 (perExponent 0 4 6 1) = true :=
  below_extend 16 6 (perExponent 0 4 6 1)
    (small_exps_6_1_16) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem small_exps_6_2_8 : below 8 (perExponent 0 4 6 2) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem small_exps_6_2_16 : below 16 (perExponent 0 4 6 2) = true :=
  below_extend 8 8 (perExponent 0 4 6 2)
    (small_exps_6_2_8) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem small_exps_6_2 : below 22 (perExponent 0 4 6 2) = true :=
  below_extend 16 6 (perExponent 0 4 6 2)
    (small_exps_6_2_16) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem small_blocks_6_8 : below 8 (perBlock 0 4 6) = true :=
  @below_succ 7 (perBlock 0 4 6) (@below_succ 6 (perBlock 0 4 6) (@below_succ 5 (perBlock 0 4 6) (@below_succ 4 (perBlock 0 4 6) (@below_succ 3 (perBlock 0 4 6) (@below_succ 2 (perBlock 0 4 6) (@below_succ 1 (perBlock 0 4 6) (@below_succ 0 (perBlock 0 4 6) (below_zero (perBlock 0 4 6)) (small_exps_6_0)) (small_exps_6_1)) (small_exps_6_2)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem small_blocks_6 : below 16 (perBlock 0 4 6) = true :=
  below_extend 8 8 (perBlock 0 4 6)
    (small_blocks_6_8) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem small_exps_7_0_8 : below 8 (perExponent 0 4 7 0) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem small_exps_7_0_16 : below 16 (perExponent 0 4 7 0) = true :=
  below_extend 8 8 (perExponent 0 4 7 0)
    (small_exps_7_0_8) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem small_exps_7_0 : below 22 (perExponent 0 4 7 0) = true :=
  below_extend 16 6 (perExponent 0 4 7 0)
    (small_exps_7_0_16) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem small_exps_7_1_8 : below 8 (perExponent 0 4 7 1) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem small_exps_7_1_16 : below 16 (perExponent 0 4 7 1) = true :=
  below_extend 8 8 (perExponent 0 4 7 1)
    (small_exps_7_1_8) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem small_exps_7_1 : below 22 (perExponent 0 4 7 1) = true :=
  below_extend 16 6 (perExponent 0 4 7 1)
    (small_exps_7_1_16) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem small_exps_7_2_8 : below 8 (perExponent 0 4 7 2) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem small_exps_7_2_16 : below 16 (perExponent 0 4 7 2) = true :=
  below_extend 8 8 (perExponent 0 4 7 2)
    (small_exps_7_2_8) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem small_exps_7_2 : below 22 (perExponent 0 4 7 2) = true :=
  below_extend 16 6 (perExponent 0 4 7 2)
    (small_exps_7_2_16) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem small_blocks_7_8 : below 8 (perBlock 0 4 7) = true :=
  @below_succ 7 (perBlock 0 4 7) (@below_succ 6 (perBlock 0 4 7) (@below_succ 5 (perBlock 0 4 7) (@below_succ 4 (perBlock 0 4 7) (@below_succ 3 (perBlock 0 4 7) (@below_succ 2 (perBlock 0 4 7) (@below_succ 1 (perBlock 0 4 7) (@below_succ 0 (perBlock 0 4 7) (below_zero (perBlock 0 4 7)) (small_exps_7_0)) (small_exps_7_1)) (small_exps_7_2)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem small_blocks_7 : below 16 (perBlock 0 4 7) = true :=
  below_extend 8 8 (perBlock 0 4 7)
    (small_blocks_7_8) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem small_exps_8_0_8 : below 8 (perExponent 0 4 8 0) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem small_exps_8_0_16 : below 16 (perExponent 0 4 8 0) = true :=
  below_extend 8 8 (perExponent 0 4 8 0)
    (small_exps_8_0_8) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem small_exps_8_0 : below 22 (perExponent 0 4 8 0) = true :=
  below_extend 16 6 (perExponent 0 4 8 0)
    (small_exps_8_0_16) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem small_exps_8_1_8 : below 8 (perExponent 0 4 8 1) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem small_exps_8_1_16 : below 16 (perExponent 0 4 8 1) = true :=
  below_extend 8 8 (perExponent 0 4 8 1)
    (small_exps_8_1_8) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem small_exps_8_1 : below 22 (perExponent 0 4 8 1) = true :=
  below_extend 16 6 (perExponent 0 4 8 1)
    (small_exps_8_1_16) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem small_exps_8_2_8 : below 8 (perExponent 0 4 8 2) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem small_exps_8_2_16 : below 16 (perExponent 0 4 8 2) = true :=
  below_extend 8 8 (perExponent 0 4 8 2)
    (small_exps_8_2_8) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem small_exps_8_2 : below 22 (perExponent 0 4 8 2) = true :=
  below_extend 16 6 (perExponent 0 4 8 2)
    (small_exps_8_2_16) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem small_blocks_8_8 : below 8 (perBlock 0 4 8) = true :=
  @below_succ 7 (perBlock 0 4 8) (@below_succ 6 (perBlock 0 4 8) (@below_succ 5 (perBlock 0 4 8) (@below_succ 4 (perBlock 0 4 8) (@below_succ 3 (perBlock 0 4 8) (@below_succ 2 (perBlock 0 4 8) (@below_succ 1 (perBlock 0 4 8) (@below_succ 0 (perBlock 0 4 8) (below_zero (perBlock 0 4 8)) (small_exps_8_0)) (small_exps_8_1)) (small_exps_8_2)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem small_blocks_8 : below 16 (perBlock 0 4 8) = true :=
  below_extend 8 8 (perBlock 0 4 8)
    (small_blocks_8_8) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem small_all_8 : below 8 (perPower 0 4 16) = true :=
  @below_succ 7 (perPower 0 4 16) (@below_succ 6 (perPower 0 4 16) (@below_succ 5 (perPower 0 4 16) (@below_succ 4 (perPower 0 4 16) (@below_succ 3 (perPower 0 4 16) (@below_succ 2 (perPower 0 4 16) (@below_succ 1 (perPower 0 4 16) (@below_succ 0 (perPower 0 4 16) (below_zero (perPower 0 4 16)) (small_blocks_0)) (small_blocks_1)) (small_blocks_2)) (small_blocks_3)) (small_blocks_4)) (small_blocks_5)) (small_blocks_6)) (small_blocks_7)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem small_all : below 9 (perPower 0 4 16) = true :=
  @below_succ 8 (perPower 0 4 16) (small_all_8) (small_blocks_8)

private theorem small_grid : grid 0 4 16 = true := grid_of_powers 0 4 16 small_all
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_0_8 : below 8 (perBlock 64 8 0) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_0_16 : below 16 (perBlock 64 8 0) = true :=
  below_extend 8 8 (perBlock 64 8 0)
    (large_blocks_0_8) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_0_24 : below 24 (perBlock 64 8 0) = true :=
  below_extend 16 8 (perBlock 64 8 0)
    (large_blocks_0_16) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_0_32 : below 32 (perBlock 64 8 0) = true :=
  below_extend 24 8 (perBlock 64 8 0)
    (large_blocks_0_24) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_0_40 : below 40 (perBlock 64 8 0) = true :=
  below_extend 32 8 (perBlock 64 8 0)
    (large_blocks_0_32) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_0_48 : below 48 (perBlock 64 8 0) = true :=
  below_extend 40 8 (perBlock 64 8 0)
    (large_blocks_0_40) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_0_56 : below 56 (perBlock 64 8 0) = true :=
  below_extend 48 8 (perBlock 64 8 0)
    (large_blocks_0_48) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_0_64 : below 64 (perBlock 64 8 0) = true :=
  below_extend 56 8 (perBlock 64 8 0)
    (large_blocks_0_56) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_0_72 : below 72 (perBlock 64 8 0) = true :=
  below_extend 64 8 (perBlock 64 8 0)
    (large_blocks_0_64) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_0_80 : below 80 (perBlock 64 8 0) = true :=
  below_extend 72 8 (perBlock 64 8 0)
    (large_blocks_0_72) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_0_88 : below 88 (perBlock 64 8 0) = true :=
  below_extend 80 8 (perBlock 64 8 0)
    (large_blocks_0_80) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_0_96 : below 96 (perBlock 64 8 0) = true :=
  below_extend 88 8 (perBlock 64 8 0)
    (large_blocks_0_88) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_0_104 : below 104 (perBlock 64 8 0) = true :=
  below_extend 96 8 (perBlock 64 8 0)
    (large_blocks_0_96) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_0_112 : below 112 (perBlock 64 8 0) = true :=
  below_extend 104 8 (perBlock 64 8 0)
    (large_blocks_0_104) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_0 : below 117 (perBlock 64 8 0) = true :=
  below_extend 112 5 (perBlock 64 8 0)
    (large_blocks_0_112) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_1_8 : below 8 (perBlock 64 8 1) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_1_16 : below 16 (perBlock 64 8 1) = true :=
  below_extend 8 8 (perBlock 64 8 1)
    (large_blocks_1_8) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_1_24 : below 24 (perBlock 64 8 1) = true :=
  below_extend 16 8 (perBlock 64 8 1)
    (large_blocks_1_16) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_1_32 : below 32 (perBlock 64 8 1) = true :=
  below_extend 24 8 (perBlock 64 8 1)
    (large_blocks_1_24) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_1_40 : below 40 (perBlock 64 8 1) = true :=
  below_extend 32 8 (perBlock 64 8 1)
    (large_blocks_1_32) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_1_48 : below 48 (perBlock 64 8 1) = true :=
  below_extend 40 8 (perBlock 64 8 1)
    (large_blocks_1_40) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_1_56 : below 56 (perBlock 64 8 1) = true :=
  below_extend 48 8 (perBlock 64 8 1)
    (large_blocks_1_48) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_1_64 : below 64 (perBlock 64 8 1) = true :=
  below_extend 56 8 (perBlock 64 8 1)
    (large_blocks_1_56) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_1_72 : below 72 (perBlock 64 8 1) = true :=
  below_extend 64 8 (perBlock 64 8 1)
    (large_blocks_1_64) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_1_80 : below 80 (perBlock 64 8 1) = true :=
  below_extend 72 8 (perBlock 64 8 1)
    (large_blocks_1_72) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_1_88 : below 88 (perBlock 64 8 1) = true :=
  below_extend 80 8 (perBlock 64 8 1)
    (large_blocks_1_80) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_1_96 : below 96 (perBlock 64 8 1) = true :=
  below_extend 88 8 (perBlock 64 8 1)
    (large_blocks_1_88) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_1_104 : below 104 (perBlock 64 8 1) = true :=
  below_extend 96 8 (perBlock 64 8 1)
    (large_blocks_1_96) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_1_112 : below 112 (perBlock 64 8 1) = true :=
  below_extend 104 8 (perBlock 64 8 1)
    (large_blocks_1_104) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_1 : below 117 (perBlock 64 8 1) = true :=
  below_extend 112 5 (perBlock 64 8 1)
    (large_blocks_1_112) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_2_8 : below 8 (perBlock 64 8 2) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_2_16 : below 16 (perBlock 64 8 2) = true :=
  below_extend 8 8 (perBlock 64 8 2)
    (large_blocks_2_8) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_2_24 : below 24 (perBlock 64 8 2) = true :=
  below_extend 16 8 (perBlock 64 8 2)
    (large_blocks_2_16) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_2_32 : below 32 (perBlock 64 8 2) = true :=
  below_extend 24 8 (perBlock 64 8 2)
    (large_blocks_2_24) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_2_40 : below 40 (perBlock 64 8 2) = true :=
  below_extend 32 8 (perBlock 64 8 2)
    (large_blocks_2_32) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_2_48 : below 48 (perBlock 64 8 2) = true :=
  below_extend 40 8 (perBlock 64 8 2)
    (large_blocks_2_40) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_2_56 : below 56 (perBlock 64 8 2) = true :=
  below_extend 48 8 (perBlock 64 8 2)
    (large_blocks_2_48) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_2_64 : below 64 (perBlock 64 8 2) = true :=
  below_extend 56 8 (perBlock 64 8 2)
    (large_blocks_2_56) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_2_72 : below 72 (perBlock 64 8 2) = true :=
  below_extend 64 8 (perBlock 64 8 2)
    (large_blocks_2_64) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_2_80 : below 80 (perBlock 64 8 2) = true :=
  below_extend 72 8 (perBlock 64 8 2)
    (large_blocks_2_72) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_2_88 : below 88 (perBlock 64 8 2) = true :=
  below_extend 80 8 (perBlock 64 8 2)
    (large_blocks_2_80) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_2_96 : below 96 (perBlock 64 8 2) = true :=
  below_extend 88 8 (perBlock 64 8 2)
    (large_blocks_2_88) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_2_104 : below 104 (perBlock 64 8 2) = true :=
  below_extend 96 8 (perBlock 64 8 2)
    (large_blocks_2_96) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_2_112 : below 112 (perBlock 64 8 2) = true :=
  below_extend 104 8 (perBlock 64 8 2)
    (large_blocks_2_104) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_2 : below 117 (perBlock 64 8 2) = true :=
  below_extend 112 5 (perBlock 64 8 2)
    (large_blocks_2_112) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_3_8 : below 8 (perBlock 64 8 3) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_3_16 : below 16 (perBlock 64 8 3) = true :=
  below_extend 8 8 (perBlock 64 8 3)
    (large_blocks_3_8) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_3_24 : below 24 (perBlock 64 8 3) = true :=
  below_extend 16 8 (perBlock 64 8 3)
    (large_blocks_3_16) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_3_32 : below 32 (perBlock 64 8 3) = true :=
  below_extend 24 8 (perBlock 64 8 3)
    (large_blocks_3_24) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_3_40 : below 40 (perBlock 64 8 3) = true :=
  below_extend 32 8 (perBlock 64 8 3)
    (large_blocks_3_32) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_3_48 : below 48 (perBlock 64 8 3) = true :=
  below_extend 40 8 (perBlock 64 8 3)
    (large_blocks_3_40) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_3_56 : below 56 (perBlock 64 8 3) = true :=
  below_extend 48 8 (perBlock 64 8 3)
    (large_blocks_3_48) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_3_64 : below 64 (perBlock 64 8 3) = true :=
  below_extend 56 8 (perBlock 64 8 3)
    (large_blocks_3_56) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_3_72 : below 72 (perBlock 64 8 3) = true :=
  below_extend 64 8 (perBlock 64 8 3)
    (large_blocks_3_64) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_3_80 : below 80 (perBlock 64 8 3) = true :=
  below_extend 72 8 (perBlock 64 8 3)
    (large_blocks_3_72) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_3_88 : below 88 (perBlock 64 8 3) = true :=
  below_extend 80 8 (perBlock 64 8 3)
    (large_blocks_3_80) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_3_96 : below 96 (perBlock 64 8 3) = true :=
  below_extend 88 8 (perBlock 64 8 3)
    (large_blocks_3_88) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_3_104 : below 104 (perBlock 64 8 3) = true :=
  below_extend 96 8 (perBlock 64 8 3)
    (large_blocks_3_96) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_3_112 : below 112 (perBlock 64 8 3) = true :=
  below_extend 104 8 (perBlock 64 8 3)
    (large_blocks_3_104) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_3 : below 117 (perBlock 64 8 3) = true :=
  below_extend 112 5 (perBlock 64 8 3)
    (large_blocks_3_112) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_4_8 : below 8 (perBlock 64 8 4) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_4_16 : below 16 (perBlock 64 8 4) = true :=
  below_extend 8 8 (perBlock 64 8 4)
    (large_blocks_4_8) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_4_24 : below 24 (perBlock 64 8 4) = true :=
  below_extend 16 8 (perBlock 64 8 4)
    (large_blocks_4_16) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_4_32 : below 32 (perBlock 64 8 4) = true :=
  below_extend 24 8 (perBlock 64 8 4)
    (large_blocks_4_24) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_4_40 : below 40 (perBlock 64 8 4) = true :=
  below_extend 32 8 (perBlock 64 8 4)
    (large_blocks_4_32) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_4_48 : below 48 (perBlock 64 8 4) = true :=
  below_extend 40 8 (perBlock 64 8 4)
    (large_blocks_4_40) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_4_56 : below 56 (perBlock 64 8 4) = true :=
  below_extend 48 8 (perBlock 64 8 4)
    (large_blocks_4_48) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_4_64 : below 64 (perBlock 64 8 4) = true :=
  below_extend 56 8 (perBlock 64 8 4)
    (large_blocks_4_56) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_4_72 : below 72 (perBlock 64 8 4) = true :=
  below_extend 64 8 (perBlock 64 8 4)
    (large_blocks_4_64) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_4_80 : below 80 (perBlock 64 8 4) = true :=
  below_extend 72 8 (perBlock 64 8 4)
    (large_blocks_4_72) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_4_88 : below 88 (perBlock 64 8 4) = true :=
  below_extend 80 8 (perBlock 64 8 4)
    (large_blocks_4_80) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_4_96 : below 96 (perBlock 64 8 4) = true :=
  below_extend 88 8 (perBlock 64 8 4)
    (large_blocks_4_88) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_4_104 : below 104 (perBlock 64 8 4) = true :=
  below_extend 96 8 (perBlock 64 8 4)
    (large_blocks_4_96) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_4_112 : below 112 (perBlock 64 8 4) = true :=
  below_extend 104 8 (perBlock 64 8 4)
    (large_blocks_4_104) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_4 : below 117 (perBlock 64 8 4) = true :=
  below_extend 112 5 (perBlock 64 8 4)
    (large_blocks_4_112) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_5_8 : below 8 (perBlock 64 8 5) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_5_16 : below 16 (perBlock 64 8 5) = true :=
  below_extend 8 8 (perBlock 64 8 5)
    (large_blocks_5_8) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_5_24 : below 24 (perBlock 64 8 5) = true :=
  below_extend 16 8 (perBlock 64 8 5)
    (large_blocks_5_16) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_5_32 : below 32 (perBlock 64 8 5) = true :=
  below_extend 24 8 (perBlock 64 8 5)
    (large_blocks_5_24) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_5_40 : below 40 (perBlock 64 8 5) = true :=
  below_extend 32 8 (perBlock 64 8 5)
    (large_blocks_5_32) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_5_48 : below 48 (perBlock 64 8 5) = true :=
  below_extend 40 8 (perBlock 64 8 5)
    (large_blocks_5_40) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_5_56 : below 56 (perBlock 64 8 5) = true :=
  below_extend 48 8 (perBlock 64 8 5)
    (large_blocks_5_48) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_5_64 : below 64 (perBlock 64 8 5) = true :=
  below_extend 56 8 (perBlock 64 8 5)
    (large_blocks_5_56) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_5_72 : below 72 (perBlock 64 8 5) = true :=
  below_extend 64 8 (perBlock 64 8 5)
    (large_blocks_5_64) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_5_80 : below 80 (perBlock 64 8 5) = true :=
  below_extend 72 8 (perBlock 64 8 5)
    (large_blocks_5_72) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_5_88 : below 88 (perBlock 64 8 5) = true :=
  below_extend 80 8 (perBlock 64 8 5)
    (large_blocks_5_80) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_5_96 : below 96 (perBlock 64 8 5) = true :=
  below_extend 88 8 (perBlock 64 8 5)
    (large_blocks_5_88) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_5_104 : below 104 (perBlock 64 8 5) = true :=
  below_extend 96 8 (perBlock 64 8 5)
    (large_blocks_5_96) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_5_112 : below 112 (perBlock 64 8 5) = true :=
  below_extend 104 8 (perBlock 64 8 5)
    (large_blocks_5_104) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_5 : below 117 (perBlock 64 8 5) = true :=
  below_extend 112 5 (perBlock 64 8 5)
    (large_blocks_5_112) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_6_8 : below 8 (perBlock 64 8 6) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_6_16 : below 16 (perBlock 64 8 6) = true :=
  below_extend 8 8 (perBlock 64 8 6)
    (large_blocks_6_8) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_6_24 : below 24 (perBlock 64 8 6) = true :=
  below_extend 16 8 (perBlock 64 8 6)
    (large_blocks_6_16) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_6_32 : below 32 (perBlock 64 8 6) = true :=
  below_extend 24 8 (perBlock 64 8 6)
    (large_blocks_6_24) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_6_40 : below 40 (perBlock 64 8 6) = true :=
  below_extend 32 8 (perBlock 64 8 6)
    (large_blocks_6_32) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_6_48 : below 48 (perBlock 64 8 6) = true :=
  below_extend 40 8 (perBlock 64 8 6)
    (large_blocks_6_40) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_6_56 : below 56 (perBlock 64 8 6) = true :=
  below_extend 48 8 (perBlock 64 8 6)
    (large_blocks_6_48) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_6_64 : below 64 (perBlock 64 8 6) = true :=
  below_extend 56 8 (perBlock 64 8 6)
    (large_blocks_6_56) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_6_72 : below 72 (perBlock 64 8 6) = true :=
  below_extend 64 8 (perBlock 64 8 6)
    (large_blocks_6_64) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_6_80 : below 80 (perBlock 64 8 6) = true :=
  below_extend 72 8 (perBlock 64 8 6)
    (large_blocks_6_72) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_6_88 : below 88 (perBlock 64 8 6) = true :=
  below_extend 80 8 (perBlock 64 8 6)
    (large_blocks_6_80) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_6_96 : below 96 (perBlock 64 8 6) = true :=
  below_extend 88 8 (perBlock 64 8 6)
    (large_blocks_6_88) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_6_104 : below 104 (perBlock 64 8 6) = true :=
  below_extend 96 8 (perBlock 64 8 6)
    (large_blocks_6_96) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_6_112 : below 112 (perBlock 64 8 6) = true :=
  below_extend 104 8 (perBlock 64 8 6)
    (large_blocks_6_104) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_6 : below 117 (perBlock 64 8 6) = true :=
  below_extend 112 5 (perBlock 64 8 6)
    (large_blocks_6_112) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_7_8 : below 8 (perBlock 64 8 7) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_7_16 : below 16 (perBlock 64 8 7) = true :=
  below_extend 8 8 (perBlock 64 8 7)
    (large_blocks_7_8) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_7_24 : below 24 (perBlock 64 8 7) = true :=
  below_extend 16 8 (perBlock 64 8 7)
    (large_blocks_7_16) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_7_32 : below 32 (perBlock 64 8 7) = true :=
  below_extend 24 8 (perBlock 64 8 7)
    (large_blocks_7_24) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_7_40 : below 40 (perBlock 64 8 7) = true :=
  below_extend 32 8 (perBlock 64 8 7)
    (large_blocks_7_32) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_7_48 : below 48 (perBlock 64 8 7) = true :=
  below_extend 40 8 (perBlock 64 8 7)
    (large_blocks_7_40) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_7_56 : below 56 (perBlock 64 8 7) = true :=
  below_extend 48 8 (perBlock 64 8 7)
    (large_blocks_7_48) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_7_64 : below 64 (perBlock 64 8 7) = true :=
  below_extend 56 8 (perBlock 64 8 7)
    (large_blocks_7_56) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_7_72 : below 72 (perBlock 64 8 7) = true :=
  below_extend 64 8 (perBlock 64 8 7)
    (large_blocks_7_64) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_7_80 : below 80 (perBlock 64 8 7) = true :=
  below_extend 72 8 (perBlock 64 8 7)
    (large_blocks_7_72) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_7_88 : below 88 (perBlock 64 8 7) = true :=
  below_extend 80 8 (perBlock 64 8 7)
    (large_blocks_7_80) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_7_96 : below 96 (perBlock 64 8 7) = true :=
  below_extend 88 8 (perBlock 64 8 7)
    (large_blocks_7_88) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_7_104 : below 104 (perBlock 64 8 7) = true :=
  below_extend 96 8 (perBlock 64 8 7)
    (large_blocks_7_96) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_7_112 : below 112 (perBlock 64 8 7) = true :=
  below_extend 104 8 (perBlock 64 8 7)
    (large_blocks_7_104) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_7 : below 117 (perBlock 64 8 7) = true :=
  below_extend 112 5 (perBlock 64 8 7)
    (large_blocks_7_112) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_8_8 : below 8 (perBlock 64 8 8) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_8_16 : below 16 (perBlock 64 8 8) = true :=
  below_extend 8 8 (perBlock 64 8 8)
    (large_blocks_8_8) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_8_24 : below 24 (perBlock 64 8 8) = true :=
  below_extend 16 8 (perBlock 64 8 8)
    (large_blocks_8_16) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_8_32 : below 32 (perBlock 64 8 8) = true :=
  below_extend 24 8 (perBlock 64 8 8)
    (large_blocks_8_24) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_8_40 : below 40 (perBlock 64 8 8) = true :=
  below_extend 32 8 (perBlock 64 8 8)
    (large_blocks_8_32) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_8_48 : below 48 (perBlock 64 8 8) = true :=
  below_extend 40 8 (perBlock 64 8 8)
    (large_blocks_8_40) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_8_56 : below 56 (perBlock 64 8 8) = true :=
  below_extend 48 8 (perBlock 64 8 8)
    (large_blocks_8_48) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_8_64 : below 64 (perBlock 64 8 8) = true :=
  below_extend 56 8 (perBlock 64 8 8)
    (large_blocks_8_56) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_8_72 : below 72 (perBlock 64 8 8) = true :=
  below_extend 64 8 (perBlock 64 8 8)
    (large_blocks_8_64) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_8_80 : below 80 (perBlock 64 8 8) = true :=
  below_extend 72 8 (perBlock 64 8 8)
    (large_blocks_8_72) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_8_88 : below 88 (perBlock 64 8 8) = true :=
  below_extend 80 8 (perBlock 64 8 8)
    (large_blocks_8_80) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_8_96 : below 96 (perBlock 64 8 8) = true :=
  below_extend 88 8 (perBlock 64 8 8)
    (large_blocks_8_88) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_8_104 : below 104 (perBlock 64 8 8) = true :=
  below_extend 96 8 (perBlock 64 8 8)
    (large_blocks_8_96) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_8_112 : below 112 (perBlock 64 8 8) = true :=
  below_extend 104 8 (perBlock 64 8 8)
    (large_blocks_8_104) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_blocks_8 : below 117 (perBlock 64 8 8) = true :=
  below_extend 112 5 (perBlock 64 8 8)
    (large_blocks_8_112) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_all_8 : below 8 (perPower 64 8 117) = true :=
  @below_succ 7 (perPower 64 8 117) (@below_succ 6 (perPower 64 8 117) (@below_succ 5 (perPower 64 8 117) (@below_succ 4 (perPower 64 8 117) (@below_succ 3 (perPower 64 8 117) (@below_succ 2 (perPower 64 8 117) (@below_succ 1 (perPower 64 8 117) (@below_succ 0 (perPower 64 8 117) (below_zero (perPower 64 8 117)) (large_blocks_0)) (large_blocks_1)) (large_blocks_2)) (large_blocks_3)) (large_blocks_4)) (large_blocks_5)) (large_blocks_6)) (large_blocks_7)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem large_all : below 9 (perPower 64 8 117) = true :=
  @below_succ 8 (perPower 64 8 117) (large_all_8) (large_blocks_8)

private theorem large_grid : grid 64 8 117 = true := grid_of_powers 64 8 117 large_all

theorem nonlinear_checked {p k i : ℕ} (hp : p < 1000) (hk : k < 9) (hi : i < 22) :
    nonlinearAt p k i = true := by
  by_cases hs : p < 64
  · have H := use_below (use_below (use_below (use_below small_grid hk)
      (show p/4 < 16 by omega)) hi) (show p%4 < 4 by omega)
    have hp' : 0+4*(p/4)+p%4 = p := by omega
    simpa only [hp'] using H
  · have H := use_below (use_below (use_below (use_below large_grid hk)
      (show (p-64)/8 < 117 by omega)) hi) (show (p-64)%8 < 8 by omega)
    have hp' : 64+8*((p-64)/8)+(p-64)%8 = p := by omega
    simpa only [hp'] using H

end A067599Three.Check

/-
# Excluding a repeated largest prime

The finite checks below use kernel reduction. For a square with a linear middle
factor, integer division recovers that factor. In the remaining cases a monotone
comparison locates any root in each possible decimal interval.
-/

namespace A067599Three

open OeisA67599

open Check

private theorem width {x L : ℕ} (hx : 0 < x) (hu : x < 10^L) :
    ∃ u < L, place x = 10^(u+1) ∧ 10^u ≤ x ∧ x < 10^(u+1) := by
  have hl : 0 < (Nat.digits 10 x).length :=
    (Nat.lt_digits_length_iff (by decide : 1 < 10) x).2 (by simp; omega)
  obtain ⟨u, hu'⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hl)
  have hmax := (Nat.digits_length_le_iff (by decide : 1 < 10) x).2 hu
  refine ⟨u, by omega, by simp [place,hu'], ?_, ?_⟩
  · exact (Nat.lt_digits_length_iff (by decide : 1 < 10) x).1 (by omega)
  · simpa [hu'] using (Nat.lt_base_pow_length_digits (m:=x) (by decide : 1 < 10))

private theorem short_correct {x : ℕ} (hx : 0 < x) (hu : x < 10000) : place x = shortPlace x := by
  obtain ⟨v,hv,hh,hl,hr⟩ := width (L:=4) hx hu
  interval_cases v <;> norm_num [shortPlace] at * <;> split_ifs <;> omega

private theorem two_of_even {p q r i j k : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p < q) (hqr : q < r) (he : 2 ∣ p^(i+1)*q^(j+1)*r^(k+1)) : p = 2 := by
  have uniq {z v : ℕ} (hz : z.Prime) (hd : 2 ∣ z^v) : 2 = z :=
    (Nat.dvd_prime_two_le hz (by decide)).mp (Nat.prime_two.dvd_of_dvd_pow hd)
  have h2 := hp.two_le
  rcases Nat.prime_two.dvd_mul.mp he with h | h
  · rcases Nat.prime_two.dvd_mul.mp h with h | h
    · exact (uniq hp h).symm
    · have := uniq hq h; omega
  · have := uniq hr h; omega

private theorem square_excluded {q r i : ℕ} (hq : q.Prime) (hr : r.Prime) (hpq : 2 < q)
    (hqr : q < r) (hi : i < 22) (rcap : r ≤ 222222)
    (eqn : 2^(i+1)*q*r^2 = ((((2*place (i+1)+(i+1))*place q+q)*10+1)*place r+r)*10+2) :
    False := by
  let a := i+1
  let A := 2*shortPlace a+a
  have hs := short_correct (x:=i+1) (by omega) (by omega)
  change 2^a*q*r^2 = ((((2*place a+a)*place q+q)*10+1)*place r+r)*10+2 at eqn
  rw [hs] at eqn
  change 2^a*q*r^2 = (((A*place q+q)*10+1)*place r+r)*10+2 at eqn
  obtain ⟨d,hd, hv, rl, ru⟩ := width (L:=6) hr.pos (by norm_num; omega)
  obtain ⟨u,hu, hQ, ql, qu⟩ := width (L:=6) hq.pos (by norm_num; omega)
  let V := 10^(d+1)
  let Q := 10^(u+1)
  change place r = V at hv
  change place q = Q at hQ
  rw [hv,hQ] at eqn
  have hQle : Q ≤ 10*q := by dsimp [Q]; rw [pow_succ]; omega
  have vr : r < V := ru
  have vq : V ≤ q*V := by simpa using Nat.mul_le_mul_right V hq.pos
  have z : 2^a*r^2 ≤ (1000*A+122)*V := by
    apply Nat.le_of_mul_le_mul_right _ hq.pos
    have ht := Nat.mul_le_mul_right (100*A*V) hQle
    nlinarith only [ht,eqn,vr,vq]
  have rh : r ≤ (((1000*A+122)*V/2^a).sqrt) := by
    apply Nat.le_sqrt.mpr
    apply (Nat.le_div_iff_mul_le (by positivity : 0 < 2^a)).mpr
    nlinarith only [z]
  have checked := use_below (use_segment (use_below (use_below squares_checked hi) hd)
    rl (le_min (by omega : r ≤ V-1) rh)) hu
  change squareMiss a V r Q = true at checked
  let den := 2^a*r^2-100*V
  let num := (100*A*Q+10)*V+10*r+2
  have splitEq : 2^a*r^2*q = 100*V*q+num := by
    calc 2^a*r^2*q = 2^a*q*r^2 := by ring
         _ = _ := eqn.trans (by dsimp [num]; ring)
  have posNum : 0 < num := by dsimp [num]; omega
  have hden : 100*V < 2^a*r^2 := by
    exact Nat.lt_of_mul_lt_mul_right (show (100*V)*q < (2^a*r^2)*q by omega)
  have hdpos : 0 < den := by dsimp [den]; omega
  have hprod : den*q = num := by
    have T := congrArg (· * q) (Nat.sub_add_cancel hden.le)
    dsimp [den]
    nlinarith only [T,splitEq]
  have hdiv : num / den = q := by rw [←hprod, Nat.mul_div_cancel_left _ hdpos]
  change decide (¬(den*(num/den) = num ∧ 2 < num/den ∧ num/den < r ∧ Q/10 ≤ num/den ∧ num/den < Q)) = true at checked
  rw [hdiv] at checked
  apply (of_decide_eq_true checked) ⟨hprod,hpq,hqr,?_,qu⟩
  simpa [Q,pow_succ] using ql

private theorem scaled_power {m x y : ℕ} (k : ℕ) (h : x ≤ y) :
    m*x^(k+1)*y ≤ m*y^(k+1)*x := by
  have hh := Nat.mul_le_mul_left (m*x*y) (Nat.pow_le_pow_left h k)
  simp only [pow_succ]
  nlinarith only [hh]

private theorem compare_below {m z r t k : ℕ} (hz : 0 < z)
    (eqn : m*r^(k+1) = 10*r+z) (ht : t < r) : m*t^(k+1) < 10*t+z := by
  have hs := scaled_power (m:=m) k ht.le
  rw [eqn] at hs
  have hlt := Nat.mul_lt_mul_of_pos_left ht hz
  by_contra! h
  have hh := Nat.mul_le_mul_right r h
  nlinarith only [hs,hh,hlt]

private theorem compare_above {m z r t k : ℕ} (hz : 0 < z)
    (eqn : m*r^(k+1) = 10*r+z) (ht : r < t) : 10*t+z < m*t^(k+1) := by
  have hs := scaled_power (m:=m) k ht.le
  rw [eqn] at hs
  have hlt := Nat.mul_lt_mul_of_pos_left ht hz
  by_contra! h
  have hh := Nat.mul_le_mul_right r h
  nlinarith only [hs,hh,hlt]

private theorem root_present {m z r k : ℕ} (hz : 0 < z) (eqn : m*r^(k+1) = 10*r+z)
    (fuel lo hi : ℕ) (hl : lo ≤ r) (hu : r ≤ hi) : rootMiss m (k+1) z fuel lo hi = false := by
  have left {x : ℕ} (hx : x ≤ r) : m*x^(k+1) ≤ 10*x+z := by
    rcases hx.lt_or_eq with hh | rfl
    · exact (compare_below hz eqn hh).le
    · exact eqn.le
  have right {x : ℕ} (hx : r ≤ x) : 10*x+z ≤ m*x^(k+1) := by
    rcases hx.lt_or_eq with hh | rfl
    · exact (compare_above hz eqn hh).le
    · exact eqn.ge
  induction fuel generalizing lo hi with
  | zero => rfl
  | succ f ih =>
    have skip : ¬(hi < lo ∨ 10*lo+z < m*lo^(k+1) ∨ m*hi^(k+1) < 10*hi+z) := by
      have := left hl
      have := right hu
      omega
    simp only [rootMiss, if_neg skip]
    split_ifs with h₁ h₂
    · apply ih _ _ _ hu
      by_contra! hc
      have := right (show r ≤ (lo+hi)/2 by omega)
      omega
    · apply ih _ _ hl
      by_contra! hc
      have := left (show (lo+hi)/2 ≤ r by omega)
      omega
    · rfl

/-- In every fixed point with exactly three prime factors, the greatest one occurs once. -/
theorem largest_exponent_one {p q r a₁ b c : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p < q) (hqr : q < r) (ha : 0 < a₁) (hb : 0 < b) (hc : 0 < c)
    (h : a (p^a₁*q^b*r^c) = p^a₁*q^b*r^c) : c = 1 := by
  obtain ⟨i,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ha)
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hb)
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hc)
  by_contra! hne
  obtain ⟨full,bp,bq,br,hi,hj,hk⟩ := exponent_bounds hp hq hr hpq hqr h
  have eqn := h.symm.trans (three_encoding i j k hp hq hr hpq hqr)
  have hk1 : 0 < k := by omega
  have hplace : place (k+1) = 10 := by
    rw [short_correct (by omega) (by omega)]
    simp [shortPlace,show k+1<10 by omega]
  rw [hplace] at eqn
  have p2 : k=1 → p=2 := by
    rintro rfl
    apply two_of_even hp hq hr hpq hqr
    rw [eqn]
    omega
  have rsmall : 2 ≤ k → r < 1000 := by
    intro hk2
    have hh := Nat.pow_le_pow_right hr.pos hk2
    by_contra! hl
    have H := Nat.mul_le_mul hl hl
    nlinarith only [H,hh,br,show k+1≤9 by omega]
  have rcap : r ≤ if k=1 then 222222 else 999 := by
    split_ifs with hh
    · simpa [hh] using br
    · have := rsmall (by omega); omega
  by_cases sq : k=1 ∧ j=0
  · obtain ⟨rfl,rfl⟩ := sq
    have hh := p2 rfl
    subst p
    apply square_excluded hq hr hpq hqr hi (by simpa using rcap)
    simpa only [pow_one,show place (0+1) = 10 by decide +kernel] using eqn
  have pqcap : p < 1000 ∧ q < 2000 := by
    by_cases kk : k=1
    · have pp := p2 kk
      have jpos : 1 ≤ j := by omega
      have hqj := Nat.pow_le_pow_right hq.pos jpos
      simp only [pow_one] at hqj
      have hpi : i+1 ≤ p^i := le_trans (Nat.succ_le_of_lt (show i < 2^i from Nat.lt_two_pow_self))
        (Nat.pow_le_pow_left hp.two_le i)
      have bound : q^j*r ≤ 222222*(j+1) := by
        apply Nat.le_of_mul_le_mul_left (c:=i+1) _ (by omega)
        have X := Nat.mul_le_mul_right (q^j*r) hpi
        subst k
        simp only [pow_one] at full
        nlinarith only [X,full]
      have sqBound : q*q ≤ 222222*(j+1) := le_trans (Nat.mul_le_mul hqj hqr.le) bound
      constructor
      · omega
      · by_contra! hbig
        have H := Nat.mul_le_mul hbig hbig
        nlinarith only [H,sqBound,show j+1≤13 by omega]
    · have := rsmall (by omega); omega
  have smallP : p^i*(p+1)^j*(p+2)^k ≤ 111111*(i+1)*(j+1)*(k+1) :=
    (Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hpq j))
      (Nat.pow_le_pow_left (show p+2≤r by omega) k)).trans full
  have smallQ : p^i*q^j*(q+1)^k ≤ 111111*(i+1)*(j+1)*(k+1) :=
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hqr k)).trans full
  have U := nonlinear_checked pqcap.1 hk hi
  have noSkip : ¬(p<2 ∨ candidate p=false ∨ k=0 ∨ (k=1 ∧ p≠2) ∨ 111111*(i+1)<p^i) := by
    have hk0 : k≠0 := by omega
    have := Nat.not_lt.mpr hp.two_le
    have := Nat.not_lt.mpr bp
    have hcand : candidate p ≠ false := by simp [candidate_of_prime hp]
    tauto
  simp only [nonlinearAt, if_neg noSkip] at U
  have W := use_below U hj
  simp only [if_neg (show ¬((k=1 ∧ j=0) ∨ 111111*(i+1)*(j+1)*(k+1)<p^i*(p+1)^j*(p+2)^k) by omega)] at W
  have V := scan_use hq smallQ 2000 (p+1) hpq (by omega) W
  have rlim : r < 10^6 := by split_ifs at rcap <;> norm_num <;> omega
  obtain ⟨d,hd,hv,rl,ru⟩ := width hr.pos rlim
  have eqr : (p^(i+1)*q^(j+1))*r^(k+1) =
      10*r + (10*(((p*shortPlace (i+1)+(i+1))*shortPlace q+q)*shortPlace (j+1)+(j+1))*
        10^(d+1)+(k+1)) := by
    rw [short_correct (x:=i+1) (by omega) (by omega),
      short_correct hq.pos (by omega), short_correct (x:=j+1) (by omega) (by omega), hv] at eqn
    rw [eqn]
    ring
  have present := root_present (by positivity) eqr 20 (max (q+1) (10^d))
    (min (10^(d+1)-1) (if k=1 then 222222 else 999)) (max_le hqr rl) (le_min (by omega) rcap)
  have absent := use_below V hd
  exact Bool.noConfusion (absent.symm.trans present)

/-- All three-prime fixed points end in 1, and a repeated middle prime is bounded. -/
theorem three_prime_shape {p q r a₁ b c : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p < q) (hqr : q < r) (ha : 0 < a₁) (hb : 0 < b) (hc : 0 < c)
    (h : a (p^a₁*q^b*r^c) = p^a₁*q^b*r^c) :
    c=1 ∧ (p^a₁*q^b*r^c)%10=1 ∧ (b=1 ∨ q≤222222) := by
  obtain rfl := largest_exponent_one hp hq hr hpq hqr ha hb hc h
  obtain ⟨i,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ha)
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hb)
  have eqn := h.symm.trans (three_encoding i j 0 hp hq hr hpq hqr)
  obtain ⟨_,_,bq,_,_,hj,_⟩ := exponent_bounds (k:=0) hp hq hr hpq hqr h
  refine ⟨rfl,?_,?_⟩
  · rw [eqn]
    change (_*10+1)%10 = 1
    omega
  · by_cases h₀ : j=0
    · exact Or.inl (by omega)
    · right
      by_cases h₁ : j=1
      · simpa [h₁] using bq
      · have H := Nat.pow_le_pow_right hq.pos (show 2≤j by omega)
        by_contra! hbig
        have hb' := Nat.mul_le_mul hbig.le hbig.le
        nlinarith only [H,hb',bq,show j+1≤13 by omega]

/-- Exact arithmetic characterization for any prescribed three ordered primes and positive exponents. -/
theorem three_prime_iff {p q r a₁ b c : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p < q) (hqr : q < r) (ha : 0 < a₁) (hb : 0 < b) (hc : 0 < c) :
    a (p^a₁*q^b*r^c) = p^a₁*q^b*r^c ↔
      c=1 ∧ (p^a₁*q^b-10)*r = 10*head p a₁ q b*place r+1 := by
  constructor
  · intro h
    obtain rfl := largest_exponent_one hp hq hr hpq hqr ha hb hc h
    exact ⟨rfl,(last_prime_iff hp hq hr hpq hqr ha hb).mp (by simpa only [pow_one] using h)⟩
  · rintro ⟨rfl,eqn⟩
    simpa only [pow_one] using (last_prime_iff hp hq hr hpq hqr ha hb).mpr eqn

end A067599Three

theorem OMA.solution : OMA.R_OeisA67599_conjecture_R2.H2 := by
  intro p q r a b c hp hq hr hpq hqr ha hb hc
  exact A067599Three.three_prime_iff hp hq hr hpq hqr ha hb hc
