import OMAReductions.R_OeisA195441_conjecture_R2


/-
Credit: @VestigeClub.
If an odd n has no prime witness, every deficient base-p digit sum is at most p-2.
The recursion certifies those small digit sums in the residue class n = -1 modulo
previous primes. This forces the product of primes through31 to divide n+1,
leaving nine possible positive multiples below10^12, checked directly.
-/

namespace VestigeBernoulliDigit

def enough : ℕ → ℕ → ℕ → ℕ → Bool
  | 0, _, _, _ => false
  | f+1, p, n, need =>
    if need ≤ n%p then true else if n = 0 then false else enough f p (n/p) (need-n%p)

def test (n : ℕ) : Bool :=
  if n ≤ 100000000 ∨ 1000000000000 ≤ n ∨ n % 2 = 0 then true
  else [3,5,7,11,13,17,19,23,29,31,37].any fun p =>
    if (n+1)%p=0 then false else enough 30 p n p

def check : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Bool
  | 0, _, _, _, _, _, _, _ => false
  | f+1, p, m, a, b, off, scale, upper =>
    if b = 0 then (if a = 0 then test off else true) else
    if upper < m then
      if a ≤ upper ∧ (Nat.digits p a).sum ≤ b then test (off + scale*a) else true
    else (List.range p).all fun t =>
      let z := a+m*t
      if z%p ≤ b then check f p m (z/p) (b-z%p)
        (off+scale*(z%p)) (scale*p) (upper/p) else true


set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sum_digits_step (p n : ℕ) (hp : 1 < p) :
    (Nat.digits p n).sum = n%p + (Nat.digits p (n/p)).sum := by
  by_cases hn : n=0
  · simp [hn]
  · rw [Nat.digits_def' hp (Nat.pos_of_ne_zero hn)]
    rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem enough_sound (f p n need : ℕ) (hp : 1 < p)
    (h : enough f p n need = true) : need ≤ (Nat.digits p n).sum := by
  induction f generalizing n need with
  | zero => simp [enough] at h
  | succ f ih =>
    simp only [enough] at h
    have hd := sum_digits_step p n hp
    split at h
    · omega
    · split at h
      · contradiction
      · have hi := ih (n/p) (need-n%p) h
        omega

theorem digits_sum_zero (p n : ℕ) (h : (Nat.digits p n).sum = 0) : n = 0 := by
  have aux : ∀ l : List ℕ, l.sum = 0 → Nat.ofDigits p l = 0 := by
    intro l
    induction l with
    | nil => simp
    | cons a l ih =>
      intro h
      have ha : a = 0 := (Nat.add_eq_zero.mp h).1
      have hl : l.sum = 0 := by simpa [ha] using h
      simp [Nat.ofDigits, ha, ih hl]
  simpa only [Nat.ofDigits_digits] using aux (Nat.digits p n) h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check_sound (f p m a b off scale upper : ℕ)
    (hp : 1 < p) (hm : 0 < m) (ha : a < m)
    (hc : check f p m a b off scale upper = true) :
    ∀ n : ℕ, n ≤ upper → n%m=a → (Nat.digits p n).sum ≤ b →
      test (off+scale*n) = true := by
  induction f generalizing a b off scale upper with
  | zero => simp [check] at hc
  | succ f ih =>
    intro n hn hna hnb
    simp only [check] at hc
    by_cases hb : b = 0
    · have hn0 : n = 0 := digits_sum_zero p n (Nat.eq_zero_of_le_zero (by simpa [hb] using hnb))
      have ha0 : a = 0 := by simpa [hn0] using hna.symm
      simpa [hb, ha0, hn0] using hc
    rw [if_neg hb] at hc
    split at hc
    next hsmall =>
      have hnm : n < m := lt_of_le_of_lt hn hsmall
      have eq : n=a := by simpa [Nat.mod_eq_of_lt hnm] using hna
      have haU : a ≤ upper := by omega
      have haB : (Nat.digits p a).sum ≤ b := by simpa [eq] using hnb
      have hcond : a ≤ upper ∧ (Nat.digits p a).sum ≤ b := ⟨haU,haB⟩
      rw [if_pos hcond] at hc
      simpa only [eq] using hc
    next hlarge =>
      have hmod : n = a+m*(n/m) := by
        simpa only [hna] using (Nat.mod_add_div n m).symm
      let k := n/m
      let t := k%p
      let z := a+m*t
      have ht : t < p := Nat.mod_lt _ (by omega)
      have hz : z < m*p := by dsimp [z,t]; nlinarith [Nat.mod_lt k (by omega : 0<p)]
      have hzq : z/p < m := (Nat.div_lt_iff_lt_mul (by omega)).mpr (by simpa [Nat.mul_comm] using hz)
      have expand : n = z+p*(m*(k/p)) := by
        dsimp [z,t,k]
        have kk := Nat.mod_add_div (n/m) p
        nlinarith
      have nq : n/p = z/p+m*(k/p) := by
        rw [expand, Nat.add_mul_div_left _ _ (by omega)]
      have nr : n%p = z%p := by rw [expand]; simp
      have hnq : (n/p)%m=z/p := by rw [nq]; simp [Nat.mod_eq_of_lt hzq]
      have digit := sum_digits_step p n hp
      have hzb : z%p ≤ b := by omega
      have rest : (Nat.digits p (n/p)).sum ≤ b-z%p := by omega
      have one := List.all_eq_true.mp hc t (List.mem_range.mpr ht)
      have child : check f p m (z/p) (b-z%p) (off+scale*(z%p)) (scale*p) (upper/p) = true := by
        simpa only [show a+m*t=z from rfl, if_pos hzb] using one
      have got := ih (z/p) (b-z%p) (off+scale*(z%p)) (scale*p) (upper/p) hzq child
        (n/p) (Nat.div_le_div_right hn) hnq rest
      have ident : off+scale*(z%p)+scale*p*(n/p)=off+scale*n := by
        have eq := Nat.mod_add_div n p
        nlinarith
      simpa only [ident] using got

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem enough_complete (f p n need : ℕ) (hp : 1 < p) (hn : n < p^f)
    (hne : 0 < need) (h : need ≤ (Nat.digits p n).sum) :
    enough f p n need = true := by
  induction f generalizing n need with
  | zero =>
    simp only [pow_zero] at hn
    have hn0 : n=0 := by omega
    have hz : (Nat.digits p n).sum=0 := by simp [hn0]
    omega
  | succ f ih =>
    rw [enough]
    split
    · rfl
    · rename_i small
      have hn0 : n ≠ 0 := by
        intro hz
        simp [hz] at h
        omega
      rw [if_neg hn0]
      apply ih (n/p) (need-n%p)
      · exact (Nat.div_lt_iff_lt_mul (by omega)).mpr (by simpa [pow_succ] using hn)
      · omega
      · have hd := sum_digits_step p n hp
        omega

def primes : List ℕ := [3,5,7,11,13,17,19,23,29,31,37]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem primes_prime (p : ℕ) (h : p ∈ primes) : p.Prime := by
  simp only [primes, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem test_of_witness (p n : ℕ) (hp : p ∈ primes) (hn : n < 3^30)
    (hd : ¬ p ∣ n+1) (hs : p ≤ (Nat.digits p n).sum) : test n = true := by
  unfold test
  split
  · rfl
  · apply List.any_eq_true.mpr
    refine ⟨p, hp, ?_⟩
    have hp3 : 3 ≤ p := by
      simp only [primes, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    rw [if_neg (fun h => hd (Nat.dvd_of_mod_eq_zero h))]
    exact enough_complete 30 p n p (by omega) (hn.trans_le (Nat.pow_le_pow_left hp3 30)) (by omega) hs

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem test_witness (n : ℕ) (hlo : 100000000 < n) (hhi : n < 1000000000000)
    (ho : n%2=1) (ht : test n=true) :
    ∃ p : ℕ, p.Prime ∧ ¬ p ∣ n+1 ∧ p ≤ (Nat.digits p n).sum := by
  unfold test at ht
  rw [if_neg (by omega)] at ht
  obtain ⟨p,hp,ht⟩ := List.any_eq_true.mp ht
  have hprime := primes_prime p hp
  split at ht
  · contradiction
  · rename_i hd
    exact ⟨p,hprime, (fun h => hd (Nat.mod_eq_zero_of_dvd h)), enough_sound 30 p n p hprime.one_lt ht⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem force_divisor (p m n : ℕ) (hp : p ∈ primes) (hm : 0 < m)
    (hbound : n ≤ 999999999999) (hodd : n%2=1) (hnm : m ∣ n+1)
    (hcheck : check 30 p m (m-1) (p-2) 0 1 999999999999 = true)
    (hbad : test n ≠ true) : p ∣ n+1 := by
  have hprime := primes_prime p hp
  have hp3 : 3 ≤ p := by
    simp only [primes, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  by_contra hdiv
  have hs : (Nat.digits p n).sum < p := by
    by_contra! h
    exact hbad (test_of_witness p n hp (hbound.trans_lt (by norm_num)) hdiv h)
  have hpodd : p%2=1 := hprime.eq_two_or_odd.resolve_left (by omega)
  have hpar := Nat.modEq_digits_sum 2 p hpodd (n := n)
  have hpar' : (Nat.digits p n).sum % 2 = 1 := by
    change n%2 = (Nat.digits p n).sum%2 at hpar
    omega
  have sumle : (Nat.digits p n).sum ≤ p-2 := by omega
  have nmod : n%m=m-1 := by
    have h := Nat.mod_eq_zero_of_dvd hnm
    have hrem : (n%m+1)%m=0 := by simpa [Nat.add_mod] using h
    have hd : m ∣ n%m+1 := Nat.dvd_of_mod_eq_zero hrem
    have hlo := Nat.le_of_dvd (by omega : 0<n%m+1) hd
    have hlt := Nat.mod_lt n hm
    omega
  have ht := check_sound 30 p m (m-1) (p-2) 0 1 999999999999 hprime.one_lt hm (by omega) hcheck n hbound nmod sumle
  exact hbad (by simpa using ht)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem check_step (f p m a b off scale upper : ℕ) (hu : ¬ upper < m) (hb : b ≠ 0)
    (h : ∀ t : ℕ, t < p → (a+m*t)%p ≤ b →
      check f p m ((a+m*t)/p) (b-(a+m*t)%p)
        (off+scale*((a+m*t)%p)) (scale*p) (upper/p) = true) :
    check (f+1) p m a b off scale upper = true := by
  simp only [check, if_neg hb, if_neg hu, List.all_eq_true, List.mem_range]
  intro t ht
  split
  · exact h t ht ‹_›
  · rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem force_cert (p m a budget n : ℕ) (ha : a = m-1) (hb : budget = p-2)
    (hp : p ∈ primes) (hm : 0 < m) (hbound : n≤999999999999) (ho : n%2=1)
    (hd : m ∣ n+1) (hc : check 30 p m a budget 0 1 999999999999 = true)
    (hbad : test n ≠ true) : p ∣ n+1 := by
  apply force_divisor p m n hp hm hbound ho hd _ hbad
  simpa only [ha,hb] using hc

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem tail_check : ∀ k : Fin 10, test (100280245065*k.val-1)=true := by
  decide +kernel


set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem all_cases
    (c3 : check 30 3 2 1 1 0 1 999999999999 = true)
    (c5 : check 30 5 6 5 3 0 1 999999999999 = true)
    (c7 : check 30 7 30 29 5 0 1 999999999999 = true)
    (c11 : check 30 11 210 209 9 0 1 999999999999 = true)
    (c13 : check 30 13 2310 2309 11 0 1 999999999999 = true)
    (c17 : check 30 17 30030 30029 15 0 1 999999999999 = true)
    (c19 : check 30 19 510510 510509 17 0 1 999999999999 = true)
    (c23 : check 30 23 9699690 9699689 21 0 1 999999999999 = true)
    (c29 : check 30 29 223092870 223092869 27 0 1 999999999999 = true)
    (c31 : check 30 31 6469693230 6469693229 29 0 1 999999999999 = true)
    (n : ℕ) (hlo : 100000000 < n) (hhi : n < 1000000000000) (ho : n%2=1) :
    ∃ p : ℕ, p.Prime ∧ ¬ p ∣ n+1 ∧ p ≤ (Nat.digits p n).sum := by
  by_contra hn
  have hbad : test n ≠ true := fun ht => hn (test_witness n hlo hhi ho ht)
  have hbound : n ≤ 999999999999 := by omega
  have d2 : 2 ∣ n+1 := Nat.dvd_of_mod_eq_zero (by omega)
  have p3 := force_cert 3 2 1 1 n (by norm_num) (by norm_num) (by simp [primes]) (by norm_num) hbound ho d2 c3 hbad
  have d6 : 6 ∣ n+1 := by
    simpa only [Nat.reduceMul] using (show Nat.Coprime 2 3 by norm_num).mul_dvd_of_dvd_of_dvd d2 p3
  have p5 := force_cert 5 6 5 3 n (by norm_num) (by norm_num) (by simp [primes]) (by norm_num) hbound ho d6 c5 hbad
  have d30 : 30 ∣ n+1 := by
    simpa only [Nat.reduceMul] using (show Nat.Coprime 6 5 by norm_num).mul_dvd_of_dvd_of_dvd d6 p5
  have p7 := force_cert 7 30 29 5 n (by norm_num) (by norm_num) (by simp [primes]) (by norm_num) hbound ho d30 c7 hbad
  have d210 : 210 ∣ n+1 := by
    simpa only [Nat.reduceMul] using (show Nat.Coprime 30 7 by norm_num).mul_dvd_of_dvd_of_dvd d30 p7
  have p11 := force_cert 11 210 209 9 n (by norm_num) (by norm_num) (by simp [primes]) (by norm_num) hbound ho d210 c11 hbad
  have d2310 : 2310 ∣ n+1 := by
    simpa only [Nat.reduceMul] using (show Nat.Coprime 210 11 by norm_num).mul_dvd_of_dvd_of_dvd d210 p11
  have p13 := force_cert 13 2310 2309 11 n (by norm_num) (by norm_num) (by simp [primes]) (by norm_num) hbound ho d2310 c13 hbad
  have d30030 : 30030 ∣ n+1 := by
    simpa only [Nat.reduceMul] using (show Nat.Coprime 2310 13 by norm_num).mul_dvd_of_dvd_of_dvd d2310 p13
  have p17 := force_cert 17 30030 30029 15 n (by norm_num) (by norm_num) (by simp [primes]) (by norm_num) hbound ho d30030 c17 hbad
  have d510510 : 510510 ∣ n+1 := by
    simpa only [Nat.reduceMul] using (show Nat.Coprime 30030 17 by norm_num).mul_dvd_of_dvd_of_dvd d30030 p17
  have p19 := force_cert 19 510510 510509 17 n (by norm_num) (by norm_num) (by simp [primes]) (by norm_num) hbound ho d510510 c19 hbad
  have d9699690 : 9699690 ∣ n+1 := by
    simpa only [Nat.reduceMul] using (show Nat.Coprime 510510 19 by norm_num).mul_dvd_of_dvd_of_dvd d510510 p19
  have p23 := force_cert 23 9699690 9699689 21 n (by norm_num) (by norm_num) (by simp [primes]) (by norm_num) hbound ho d9699690 c23 hbad
  have d223092870 : 223092870 ∣ n+1 := by
    simpa only [Nat.reduceMul] using (show Nat.Coprime 9699690 23 by norm_num).mul_dvd_of_dvd_of_dvd d9699690 p23
  have p29 := force_cert 29 223092870 223092869 27 n (by norm_num) (by norm_num) (by simp [primes]) (by norm_num) hbound ho d223092870 c29 hbad
  have d6469693230 : 6469693230 ∣ n+1 := by
    simpa only [Nat.reduceMul] using (show Nat.Coprime 223092870 29 by norm_num).mul_dvd_of_dvd_of_dvd d223092870 p29
  have p31 := force_cert 31 6469693230 6469693229 29 n (by norm_num) (by norm_num) (by simp [primes]) (by norm_num) hbound ho d6469693230 c31 hbad
  have d200560490130 : 200560490130 ∣ n+1 := by
    simpa only [Nat.reduceMul] using (show Nat.Coprime 6469693230 31 by norm_num).mul_dvd_of_dvd_of_dvd d6469693230 p31
  have d100280245065 : 100280245065 ∣ n+1 := dvd_trans (by norm_num : 100280245065 ∣ 200560490130) d200560490130
  have ht : (n+1)/100280245065 < 10 := by
    apply (Nat.div_lt_iff_lt_mul (by norm_num : 0<100280245065)).mpr
    have small : n+1 ≤ 1000000000000 := Nat.succ_le_of_lt hhi
    exact small.trans_lt (by norm_num)
  have heq : 100280245065*((n+1)/100280245065)=n+1 := Nat.mul_div_cancel' d100280245065
  have hnrep : n=100280245065*((n+1)/100280245065)-1 := by simp only [heq, Nat.add_sub_cancel]
  apply hbad
  rw [hnrep]
  exact tail_check ⟨(n+1)/100280245065,ht⟩


end VestigeBernoulliDigit

open VestigeBernoulliDigit
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem OMA.solution : OMA.R_OeisA195441_conjecture_R2.H1 := by
  have check3 : check 30 3 2 1 1 0 1 999999999999 = true := by decide +kernel
  have check5 : check 30 5 6 5 3 0 1 999999999999 = true := by decide +kernel
  have check7 : check 30 7 30 29 5 0 1 999999999999 = true := by
    have check7_x0 : check 29 7 30 4 4 1 7 142857142857 = true := by decide +kernel
    have check7_x1 : check 29 7 30 8 2 3 7 142857142857 = true := by decide +kernel
    have check7_x2 : check 29 7 30 12 0 5 7 142857142857 = true := by decide +kernel
    have check7_x3x0 : check 28 7 30 2 2 21 49 20408163265 = true := by decide +kernel
    have check7_x3x1 : check 28 7 30 6 0 35 49 20408163265 = true := by decide +kernel
    have check7_x3x2x0 : check 27 7 30 1 1 196 343 2915451895 = true := by decide +kernel
    have check7_x3x2x2 : check 27 7 30 10 4 49 343 2915451895 = true := by decide +kernel
    have check7_x3x2x3 : check 27 7 30 14 2 147 343 2915451895 = true := by decide +kernel
    have check7_x3x2x4 : check 27 7 30 18 0 245 343 2915451895 = true := by decide +kernel
    have check7_x3x2x5x0 : check 26 7 30 3 3 686 2401 416493127 = true := by decide +kernel
    have check7_x3x2x5x1 : check 26 7 30 7 1 1372 2401 416493127 = true := by decide +kernel
    have check7_x3x2x5x3 : check 26 7 30 16 4 343 2401 416493127 = true := by decide +kernel
    have check7_x3x2x5x4 : check 26 7 30 20 2 1029 2401 416493127 = true := by decide +kernel
    have check7_x3x2x5x5 : check 26 7 30 24 0 1715 2401 416493127 = true := by decide +kernel
    have check7_x3x2x5x6 : check 26 7 30 29 5 0 2401 416493127 = true := by decide +kernel
    have check7_x3x2x5 : check 27 7 30 23 5 0 343 2915451895 = true := by
      apply check_step 26 7 30 23 5 0 343 2915451895 (by norm_num) (by norm_num)
      intro t ht hb
      interval_cases t
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check7_x3x2x5x0
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check7_x3x2x5x1
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check7_x3x2x5x3
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check7_x3x2x5x4
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check7_x3x2x5x5
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check7_x3x2x5x6
    have check7_x3x2x6 : check 27 7 30 27 3 98 343 2915451895 = true := by decide +kernel
    have check7_x3x2 : check 28 7 30 11 5 0 49 20408163265 = true := by
      apply check_step 27 7 30 11 5 0 49 20408163265 (by norm_num) (by norm_num)
      intro t ht hb
      interval_cases t
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check7_x3x2x0
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check7_x3x2x2
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check7_x3x2x3
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check7_x3x2x4
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check7_x3x2x5
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check7_x3x2x6
    have check7_x3x3 : check 28 7 30 15 3 14 49 20408163265 = true := by decide +kernel
    have check7_x3x4 : check 28 7 30 19 1 28 49 20408163265 = true := by decide +kernel
    have check7_x3x6 : check 28 7 30 28 4 7 49 20408163265 = true := by decide +kernel
    have check7_x3 : check 29 7 30 17 5 0 7 142857142857 = true := by
      apply check_step 28 7 30 17 5 0 7 142857142857 (by norm_num) (by norm_num)
      intro t ht hb
      interval_cases t
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check7_x3x0
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check7_x3x1
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check7_x3x2
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check7_x3x3
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check7_x3x4
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check7_x3x6
    have check7_x4 : check 29 7 30 21 3 2 7 142857142857 = true := by decide +kernel
    have check7_x5 : check 29 7 30 25 1 4 7 142857142857 = true := by decide +kernel
    apply check_step 29 7 30 29 5 0 1 999999999999 (by norm_num) (by norm_num)
    intro t ht hb
    interval_cases t
    · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check7_x0
    · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check7_x1
    · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check7_x2
    · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check7_x3
    · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check7_x4
    · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check7_x5
    · norm_num at hb
  have check11 : check 30 11 210 209 9 0 1 999999999999 = true := by
    have check11_x0x0 : check 28 11 210 1 1 88 121 8264462809 = true := by decide +kernel
    have check11_x0x1 : check 28 11 210 20 0 99 121 8264462809 = true := by decide +kernel
    have check11_x0x3x0 : check 27 11 210 5 5 484 1331 751314800 = true := by decide +kernel
    have check11_x0x3x1 : check 27 11 210 24 4 605 1331 751314800 = true := by decide +kernel
    have check11_x0x3x2 : check 27 11 210 43 3 726 1331 751314800 = true := by decide +kernel
    have check11_x0x3x3 : check 27 11 210 62 2 847 1331 751314800 = true := by decide +kernel
    have check11_x0x3x4 : check 27 11 210 81 1 968 1331 751314800 = true := by decide +kernel
    have check11_x0x3x5 : check 27 11 210 100 0 1089 1331 751314800 = true := by decide +kernel
    have check11_x0x3x7x0 : check 26 11 210 12 2 9317 14641 68301345 = true := by decide +kernel
    have check11_x0x3x7x1 : check 26 11 210 31 1 10648 14641 68301345 = true := by decide +kernel
    have check11_x0x3x7x2 : check 26 11 210 50 0 11979 14641 68301345 = true := by decide +kernel
    have check11_x0x3x7x4x0 : check 25 11 210 8 8 14641 161051 6209213 = true := by decide +kernel
    have check11_x0x3x7x4x1 : check 25 11 210 27 7 29282 161051 6209213 = true := by decide +kernel
    have check11_x0x3x7x4x2 : check 25 11 210 46 6 43923 161051 6209213 = true := by decide +kernel
    have check11_x0x3x7x4x3 : check 25 11 210 65 5 58564 161051 6209213 = true := by decide +kernel
    have check11_x0x3x7x4x4 : check 25 11 210 84 4 73205 161051 6209213 = true := by decide +kernel
    have check11_x0x3x7x4x5 : check 25 11 210 103 3 87846 161051 6209213 = true := by decide +kernel
    have check11_x0x3x7x4x6 : check 25 11 210 122 2 102487 161051 6209213 = true := by decide +kernel
    have check11_x0x3x7x4x7 : check 25 11 210 141 1 117128 161051 6209213 = true := by decide +kernel
    have check11_x0x3x7x4x8 : check 25 11 210 160 0 131769 161051 6209213 = true := by decide +kernel
    have check11_x0x3x7x4x10 : check 25 11 210 199 9 0 161051 6209213 = true := by decide +kernel
    have check11_x0x3x7x4 : check 26 11 210 89 9 0 14641 68301345 = true := by
      apply check_step 25 11 210 89 9 0 14641 68301345 (by norm_num) (by norm_num)
      intro t ht hb
      interval_cases t
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x3x7x4x0
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x3x7x4x1
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x3x7x4x2
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x3x7x4x3
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x3x7x4x4
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x3x7x4x5
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x3x7x4x6
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x3x7x4x7
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x3x7x4x8
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x3x7x4x10
    have check11_x0x3x7x5x2 : check 25 11 210 48 8 1331 161051 6209213 = true := by decide +kernel
    have check11_x0x3x7x5x3 : check 25 11 210 67 7 15972 161051 6209213 = true := by decide +kernel
    have check11_x0x3x7x5x4 : check 25 11 210 86 6 30613 161051 6209213 = true := by decide +kernel
    have check11_x0x3x7x5x5 : check 25 11 210 105 5 45254 161051 6209213 = true := by decide +kernel
    have check11_x0x3x7x5x6 : check 25 11 210 124 4 59895 161051 6209213 = true := by decide +kernel
    have check11_x0x3x7x5x7 : check 25 11 210 143 3 74536 161051 6209213 = true := by decide +kernel
    have check11_x0x3x7x5x8 : check 25 11 210 162 2 89177 161051 6209213 = true := by decide +kernel
    have check11_x0x3x7x5x9 : check 25 11 210 181 1 103818 161051 6209213 = true := by decide +kernel
    have check11_x0x3x7x5x10 : check 25 11 210 200 0 118459 161051 6209213 = true := by decide +kernel
    have check11_x0x3x7x5 : check 26 11 210 108 8 1331 14641 68301345 = true := by
      apply check_step 25 11 210 108 8 1331 14641 68301345 (by norm_num) (by norm_num)
      intro t ht hb
      interval_cases t
      · norm_num at hb
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x3x7x5x2
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x3x7x5x3
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x3x7x5x4
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x3x7x5x5
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x3x7x5x6
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x3x7x5x7
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x3x7x5x8
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x3x7x5x9
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x3x7x5x10
    have check11_x0x3x7x6 : check 26 11 210 127 7 2662 14641 68301345 = true := by decide +kernel
    have check11_x0x3x7x7 : check 26 11 210 146 6 3993 14641 68301345 = true := by decide +kernel
    have check11_x0x3x7x8 : check 26 11 210 165 5 5324 14641 68301345 = true := by decide +kernel
    have check11_x0x3x7x9 : check 26 11 210 184 4 6655 14641 68301345 = true := by decide +kernel
    have check11_x0x3x7x10 : check 26 11 210 203 3 7986 14641 68301345 = true := by decide +kernel
    have check11_x0x3x7 : check 27 11 210 139 9 0 1331 751314800 = true := by
      apply check_step 26 11 210 139 9 0 1331 751314800 (by norm_num) (by norm_num)
      intro t ht hb
      interval_cases t
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x3x7x0
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x3x7x1
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x3x7x2
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x3x7x4
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x3x7x5
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x3x7x6
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x3x7x7
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x3x7x8
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x3x7x9
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x3x7x10
    have check11_x0x3x8x0 : check 26 11 210 14 4 5445 14641 68301345 = true := by decide +kernel
    have check11_x0x3x8x1 : check 26 11 210 33 3 6776 14641 68301345 = true := by decide +kernel
    have check11_x0x3x8x2 : check 26 11 210 52 2 8107 14641 68301345 = true := by decide +kernel
    have check11_x0x3x8x3 : check 26 11 210 71 1 9438 14641 68301345 = true := by decide +kernel
    have check11_x0x3x8x4 : check 26 11 210 90 0 10769 14641 68301345 = true := by decide +kernel
    have check11_x0x3x8x7x0 : check 25 11 210 13 3 73326 161051 6209213 = true := by decide +kernel
    have check11_x0x3x8x7x1 : check 25 11 210 32 2 87967 161051 6209213 = true := by decide +kernel
    have check11_x0x3x8x7x2 : check 25 11 210 51 1 102608 161051 6209213 = true := by decide +kernel
    have check11_x0x3x8x7x3 : check 25 11 210 70 0 117249 161051 6209213 = true := by decide +kernel
    have check11_x0x3x8x7x6 : check 25 11 210 128 8 121 161051 6209213 = true := by decide +kernel
    have check11_x0x3x8x7x7 : check 25 11 210 147 7 14762 161051 6209213 = true := by decide +kernel
    have check11_x0x3x8x7x8 : check 25 11 210 166 6 29403 161051 6209213 = true := by decide +kernel
    have check11_x0x3x8x7x9 : check 25 11 210 185 5 44044 161051 6209213 = true := by decide +kernel
    have check11_x0x3x8x7x10 : check 25 11 210 204 4 58685 161051 6209213 = true := by decide +kernel
    have check11_x0x3x8x7 : check 26 11 210 148 8 121 14641 68301345 = true := by
      apply check_step 25 11 210 148 8 121 14641 68301345 (by norm_num) (by norm_num)
      intro t ht hb
      interval_cases t
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x3x8x7x0
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x3x8x7x1
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x3x8x7x2
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x3x8x7x3
      · norm_num at hb
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x3x8x7x6
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x3x8x7x7
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x3x8x7x8
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x3x8x7x9
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x3x8x7x10
    have check11_x0x3x8x8 : check 26 11 210 167 7 1452 14641 68301345 = true := by decide +kernel
    have check11_x0x3x8x9 : check 26 11 210 186 6 2783 14641 68301345 = true := by decide +kernel
    have check11_x0x3x8x10 : check 26 11 210 205 5 4114 14641 68301345 = true := by decide +kernel
    have check11_x0x3x8 : check 27 11 210 158 8 121 1331 751314800 = true := by
      apply check_step 26 11 210 158 8 121 1331 751314800 (by norm_num) (by norm_num)
      intro t ht hb
      interval_cases t
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x3x8x0
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x3x8x1
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x3x8x2
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x3x8x3
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x3x8x4
      · norm_num at hb
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x3x8x7
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x3x8x8
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x3x8x9
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x3x8x10
    have check11_x0x3x9x0 : check 26 11 210 16 6 1573 14641 68301345 = true := by decide +kernel
    have check11_x0x3x9x1 : check 26 11 210 35 5 2904 14641 68301345 = true := by decide +kernel
    have check11_x0x3x9x2 : check 26 11 210 54 4 4235 14641 68301345 = true := by decide +kernel
    have check11_x0x3x9x3 : check 26 11 210 73 3 5566 14641 68301345 = true := by decide +kernel
    have check11_x0x3x9x4 : check 26 11 210 92 2 6897 14641 68301345 = true := by decide +kernel
    have check11_x0x3x9x5 : check 26 11 210 111 1 8228 14641 68301345 = true := by decide +kernel
    have check11_x0x3x9x6 : check 26 11 210 130 0 9559 14641 68301345 = true := by decide +kernel
    have check11_x0x3x9x10 : check 26 11 210 207 7 242 14641 68301345 = true := by decide +kernel
    have check11_x0x3x9 : check 27 11 210 177 7 242 1331 751314800 = true := by
      apply check_step 26 11 210 177 7 242 1331 751314800 (by norm_num) (by norm_num)
      intro t ht hb
      interval_cases t
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x3x9x0
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x3x9x1
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x3x9x2
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x3x9x3
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x3x9x4
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x3x9x5
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x3x9x6
      · norm_num at hb
      · norm_num at hb
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x3x9x10
    have check11_x0x3x10 : check 27 11 210 196 6 363 1331 751314800 = true := by decide +kernel
    have check11_x0x3 : check 28 11 210 59 9 0 121 8264462809 = true := by
      apply check_step 27 11 210 59 9 0 121 8264462809 (by norm_num) (by norm_num)
      intro t ht hb
      interval_cases t
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x3x0
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x3x1
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x3x2
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x3x3
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x3x4
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x3x5
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x3x7
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x3x8
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x3x9
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x3x10
    have check11_x0x4x0x0 : check 26 11 210 0 0 9449 14641 68301345 = true := by decide +kernel
    have check11_x0x4x0x4 : check 26 11 210 77 7 132 14641 68301345 = true := by decide +kernel
    have check11_x0x4x0x5 : check 26 11 210 96 6 1463 14641 68301345 = true := by decide +kernel
    have check11_x0x4x0x6 : check 26 11 210 115 5 2794 14641 68301345 = true := by decide +kernel
    have check11_x0x4x0x7 : check 26 11 210 134 4 4125 14641 68301345 = true := by decide +kernel
    have check11_x0x4x0x8 : check 26 11 210 153 3 5456 14641 68301345 = true := by decide +kernel
    have check11_x0x4x0x9 : check 26 11 210 172 2 6787 14641 68301345 = true := by decide +kernel
    have check11_x0x4x0x10 : check 26 11 210 191 1 8118 14641 68301345 = true := by decide +kernel
    have check11_x0x4x0 : check 27 11 210 7 7 132 1331 751314800 = true := by
      apply check_step 26 11 210 7 7 132 1331 751314800 (by norm_num) (by norm_num)
      intro t ht hb
      interval_cases t
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x4x0x0
      · norm_num at hb
      · norm_num at hb
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x4x0x4
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x4x0x5
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x4x0x6
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x4x0x7
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x4x0x8
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x4x0x9
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x4x0x10
    have check11_x0x4x1 : check 27 11 210 26 6 253 1331 751314800 = true := by decide +kernel
    have check11_x0x4x2 : check 27 11 210 45 5 374 1331 751314800 = true := by decide +kernel
    have check11_x0x4x3 : check 27 11 210 64 4 495 1331 751314800 = true := by decide +kernel
    have check11_x0x4x4 : check 27 11 210 83 3 616 1331 751314800 = true := by decide +kernel
    have check11_x0x4x5 : check 27 11 210 102 2 737 1331 751314800 = true := by decide +kernel
    have check11_x0x4x6 : check 27 11 210 121 1 858 1331 751314800 = true := by decide +kernel
    have check11_x0x4x7 : check 27 11 210 140 0 979 1331 751314800 = true := by decide +kernel
    have check11_x0x4x10x0x0 : check 25 11 210 1 1 102498 161051 6209213 = true := by decide +kernel
    have check11_x0x4x10x0x1 : check 25 11 210 20 0 117139 161051 6209213 = true := by decide +kernel
    have check11_x0x4x10x0x4 : check 25 11 210 78 8 11 161051 6209213 = true := by decide +kernel
    have check11_x0x4x10x0x5 : check 25 11 210 97 7 14652 161051 6209213 = true := by decide +kernel
    have check11_x0x4x10x0x6 : check 25 11 210 116 6 29293 161051 6209213 = true := by decide +kernel
    have check11_x0x4x10x0x7 : check 25 11 210 135 5 43934 161051 6209213 = true := by decide +kernel
    have check11_x0x4x10x0x8 : check 25 11 210 154 4 58575 161051 6209213 = true := by decide +kernel
    have check11_x0x4x10x0x9 : check 25 11 210 173 3 73216 161051 6209213 = true := by decide +kernel
    have check11_x0x4x10x0x10 : check 25 11 210 192 2 87857 161051 6209213 = true := by decide +kernel
    have check11_x0x4x10x0 : check 26 11 210 18 8 11 14641 68301345 = true := by
      apply check_step 25 11 210 18 8 11 14641 68301345 (by norm_num) (by norm_num)
      intro t ht hb
      interval_cases t
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x4x10x0x0
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x4x10x0x1
      · norm_num at hb
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x4x10x0x4
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x4x10x0x5
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x4x10x0x6
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x4x10x0x7
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x4x10x0x8
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x4x10x0x9
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x4x10x0x10
    have check11_x0x4x10x1 : check 26 11 210 37 7 1342 14641 68301345 = true := by decide +kernel
    have check11_x0x4x10x2 : check 26 11 210 56 6 2673 14641 68301345 = true := by decide +kernel
    have check11_x0x4x10x3 : check 26 11 210 75 5 4004 14641 68301345 = true := by decide +kernel
    have check11_x0x4x10x4 : check 26 11 210 94 4 5335 14641 68301345 = true := by decide +kernel
    have check11_x0x4x10x5 : check 26 11 210 113 3 6666 14641 68301345 = true := by decide +kernel
    have check11_x0x4x10x6 : check 26 11 210 132 2 7997 14641 68301345 = true := by decide +kernel
    have check11_x0x4x10x7 : check 26 11 210 151 1 9328 14641 68301345 = true := by decide +kernel
    have check11_x0x4x10x8 : check 26 11 210 170 0 10659 14641 68301345 = true := by decide +kernel
    have check11_x0x4x10 : check 27 11 210 198 8 11 1331 751314800 = true := by
      apply check_step 26 11 210 198 8 11 1331 751314800 (by norm_num) (by norm_num)
      intro t ht hb
      interval_cases t
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x4x10x0
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x4x10x1
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x4x10x2
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x4x10x3
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x4x10x4
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x4x10x5
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x4x10x6
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x4x10x7
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x4x10x8
      · norm_num at hb
      · norm_num at hb
    have check11_x0x4 : check 28 11 210 78 8 11 121 8264462809 = true := by
      apply check_step 27 11 210 78 8 11 121 8264462809 (by norm_num) (by norm_num)
      intro t ht hb
      interval_cases t
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x4x0
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x4x1
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x4x2
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x4x3
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x4x4
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x4x5
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x4x6
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x4x7
      · norm_num at hb
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x4x10
    have check11_x0x5x2x0 : check 26 11 210 4 4 4015 14641 68301345 = true := by decide +kernel
    have check11_x0x5x2x1 : check 26 11 210 23 3 5346 14641 68301345 = true := by decide +kernel
    have check11_x0x5x2x2 : check 26 11 210 42 2 6677 14641 68301345 = true := by decide +kernel
    have check11_x0x5x2x3 : check 26 11 210 61 1 8008 14641 68301345 = true := by decide +kernel
    have check11_x0x5x2x4 : check 26 11 210 80 0 9339 14641 68301345 = true := by decide +kernel
    have check11_x0x5x2x8 : check 26 11 210 157 7 22 14641 68301345 = true := by decide +kernel
    have check11_x0x5x2x9 : check 26 11 210 176 6 1353 14641 68301345 = true := by decide +kernel
    have check11_x0x5x2x10 : check 26 11 210 195 5 2684 14641 68301345 = true := by decide +kernel
    have check11_x0x5x2 : check 27 11 210 47 7 22 1331 751314800 = true := by
      apply check_step 26 11 210 47 7 22 1331 751314800 (by norm_num) (by norm_num)
      intro t ht hb
      interval_cases t
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x5x2x0
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x5x2x1
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x5x2x2
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x5x2x3
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x5x2x4
      · norm_num at hb
      · norm_num at hb
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x5x2x8
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x5x2x9
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x5x2x10
    have check11_x0x5x3 : check 27 11 210 66 6 143 1331 751314800 = true := by decide +kernel
    have check11_x0x5x4 : check 27 11 210 85 5 264 1331 751314800 = true := by decide +kernel
    have check11_x0x5x5 : check 27 11 210 104 4 385 1331 751314800 = true := by decide +kernel
    have check11_x0x5x6 : check 27 11 210 123 3 506 1331 751314800 = true := by decide +kernel
    have check11_x0x5x7 : check 27 11 210 142 2 627 1331 751314800 = true := by decide +kernel
    have check11_x0x5x8 : check 27 11 210 161 1 748 1331 751314800 = true := by decide +kernel
    have check11_x0x5x9 : check 27 11 210 180 0 869 1331 751314800 = true := by decide +kernel
    have check11_x0x5 : check 28 11 210 97 7 22 121 8264462809 = true := by
      apply check_step 27 11 210 97 7 22 121 8264462809 (by norm_num) (by norm_num)
      intro t ht hb
      interval_cases t
      · norm_num at hb
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x5x2
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x5x3
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x5x4
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x5x5
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x5x6
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x5x7
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x5x8
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x5x9
      · norm_num at hb
    have check11_x0x6x0 : check 27 11 210 10 0 759 1331 751314800 = true := by decide +kernel
    have check11_x0x6x5 : check 27 11 210 106 6 33 1331 751314800 = true := by decide +kernel
    have check11_x0x6x6 : check 27 11 210 125 5 154 1331 751314800 = true := by decide +kernel
    have check11_x0x6x7 : check 27 11 210 144 4 275 1331 751314800 = true := by decide +kernel
    have check11_x0x6x8 : check 27 11 210 163 3 396 1331 751314800 = true := by decide +kernel
    have check11_x0x6x9 : check 27 11 210 182 2 517 1331 751314800 = true := by decide +kernel
    have check11_x0x6x10 : check 27 11 210 201 1 638 1331 751314800 = true := by decide +kernel
    have check11_x0x6 : check 28 11 210 116 6 33 121 8264462809 = true := by
      apply check_step 27 11 210 116 6 33 121 8264462809 (by norm_num) (by norm_num)
      intro t ht hb
      interval_cases t
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x6x0
      · norm_num at hb
      · norm_num at hb
      · norm_num at hb
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x6x5
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x6x6
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x6x7
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x6x8
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x6x9
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x6x10
    have check11_x0x7 : check 28 11 210 135 5 44 121 8264462809 = true := by decide +kernel
    have check11_x0x8 : check 28 11 210 154 4 55 121 8264462809 = true := by decide +kernel
    have check11_x0x9 : check 28 11 210 173 3 66 121 8264462809 = true := by decide +kernel
    have check11_x0x10 : check 28 11 210 192 2 77 121 8264462809 = true := by decide +kernel
    have check11_x0 : check 29 11 210 19 9 0 11 90909090909 = true := by
      apply check_step 28 11 210 19 9 0 11 90909090909 (by norm_num) (by norm_num)
      intro t ht hb
      interval_cases t
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x0
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x1
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x3
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x4
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x5
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x6
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x7
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x8
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x9
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0x10
    have check11_x1x0 : check 28 11 210 3 3 56 121 8264462809 = true := by decide +kernel
    have check11_x1x1 : check 28 11 210 22 2 67 121 8264462809 = true := by decide +kernel
    have check11_x1x2 : check 28 11 210 41 1 78 121 8264462809 = true := by decide +kernel
    have check11_x1x3 : check 28 11 210 60 0 89 121 8264462809 = true := by decide +kernel
    have check11_x1x6x0 : check 27 11 210 10 0 969 1331 751314800 = true := by decide +kernel
    have check11_x1x6x3x0 : check 26 11 210 6 6 2663 14641 68301345 = true := by decide +kernel
    have check11_x1x6x3x1 : check 26 11 210 25 5 3994 14641 68301345 = true := by decide +kernel
    have check11_x1x6x3x2 : check 26 11 210 44 4 5325 14641 68301345 = true := by decide +kernel
    have check11_x1x6x3x3 : check 26 11 210 63 3 6656 14641 68301345 = true := by decide +kernel
    have check11_x1x6x3x4 : check 26 11 210 82 2 7987 14641 68301345 = true := by decide +kernel
    have check11_x1x6x3x5 : check 26 11 210 101 1 9318 14641 68301345 = true := by decide +kernel
    have check11_x1x6x3x6 : check 26 11 210 120 0 10649 14641 68301345 = true := by decide +kernel
    have check11_x1x6x3x9x0 : check 25 11 210 16 6 29283 161051 6209213 = true := by decide +kernel
    have check11_x1x6x3x9x1 : check 25 11 210 35 5 43924 161051 6209213 = true := by decide +kernel
    have check11_x1x6x3x9x2 : check 25 11 210 54 4 58565 161051 6209213 = true := by decide +kernel
    have check11_x1x6x3x9x3 : check 25 11 210 73 3 73206 161051 6209213 = true := by decide +kernel
    have check11_x1x6x3x9x4 : check 25 11 210 92 2 87847 161051 6209213 = true := by decide +kernel
    have check11_x1x6x3x9x5 : check 25 11 210 111 1 102488 161051 6209213 = true := by decide +kernel
    have check11_x1x6x3x9x6 : check 25 11 210 130 0 117129 161051 6209213 = true := by decide +kernel
    have check11_x1x6x3x9x9 : check 25 11 210 188 8 1 161051 6209213 = true := by decide +kernel
    have check11_x1x6x3x9x10 : check 25 11 210 207 7 14642 161051 6209213 = true := by decide +kernel
    have check11_x1x6x3x9 : check 26 11 210 178 8 1 14641 68301345 = true := by
      apply check_step 25 11 210 178 8 1 14641 68301345 (by norm_num) (by norm_num)
      intro t ht hb
      interval_cases t
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x6x3x9x0
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x6x3x9x1
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x6x3x9x2
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x6x3x9x3
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x6x3x9x4
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x6x3x9x5
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x6x3x9x6
      · norm_num at hb
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x6x3x9x9
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x6x3x9x10
    have check11_x1x6x3x10 : check 26 11 210 197 7 1332 14641 68301345 = true := by decide +kernel
    have check11_x1x6x3 : check 27 11 210 68 8 1 1331 751314800 = true := by
      apply check_step 26 11 210 68 8 1 1331 751314800 (by norm_num) (by norm_num)
      intro t ht hb
      interval_cases t
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x6x3x0
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x6x3x1
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x6x3x2
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x6x3x3
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x6x3x4
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x6x3x5
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x6x3x6
      · norm_num at hb
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x6x3x9
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x6x3x10
    have check11_x1x6x4x1 : check 26 11 210 27 7 122 14641 68301345 = true := by decide +kernel
    have check11_x1x6x4x2 : check 26 11 210 46 6 1453 14641 68301345 = true := by decide +kernel
    have check11_x1x6x4x3 : check 26 11 210 65 5 2784 14641 68301345 = true := by decide +kernel
    have check11_x1x6x4x4 : check 26 11 210 84 4 4115 14641 68301345 = true := by decide +kernel
    have check11_x1x6x4x5 : check 26 11 210 103 3 5446 14641 68301345 = true := by decide +kernel
    have check11_x1x6x4x6 : check 26 11 210 122 2 6777 14641 68301345 = true := by decide +kernel
    have check11_x1x6x4x7 : check 26 11 210 141 1 8108 14641 68301345 = true := by decide +kernel
    have check11_x1x6x4x8 : check 26 11 210 160 0 9439 14641 68301345 = true := by decide +kernel
    have check11_x1x6x4 : check 27 11 210 87 7 122 1331 751314800 = true := by
      apply check_step 26 11 210 87 7 122 1331 751314800 (by norm_num) (by norm_num)
      intro t ht hb
      interval_cases t
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x6x4x1
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x6x4x2
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x6x4x3
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x6x4x4
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x6x4x5
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x6x4x6
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x6x4x7
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x6x4x8
      · norm_num at hb
      · norm_num at hb
    have check11_x1x6x5 : check 27 11 210 106 6 243 1331 751314800 = true := by decide +kernel
    have check11_x1x6x6 : check 27 11 210 125 5 364 1331 751314800 = true := by decide +kernel
    have check11_x1x6x7 : check 27 11 210 144 4 485 1331 751314800 = true := by decide +kernel
    have check11_x1x6x8 : check 27 11 210 163 3 606 1331 751314800 = true := by decide +kernel
    have check11_x1x6x9 : check 27 11 210 182 2 727 1331 751314800 = true := by decide +kernel
    have check11_x1x6x10 : check 27 11 210 201 1 848 1331 751314800 = true := by decide +kernel
    have check11_x1x6 : check 28 11 210 118 8 1 121 8264462809 = true := by
      apply check_step 27 11 210 118 8 1 121 8264462809 (by norm_num) (by norm_num)
      intro t ht hb
      interval_cases t
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x6x0
      · norm_num at hb
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x6x3
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x6x4
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x6x5
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x6x6
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x6x7
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x6x8
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x6x9
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x6x10
    have check11_x1x7x0 : check 27 11 210 12 2 617 1331 751314800 = true := by decide +kernel
    have check11_x1x7x1 : check 27 11 210 31 1 738 1331 751314800 = true := by decide +kernel
    have check11_x1x7x2 : check 27 11 210 50 0 859 1331 751314800 = true := by decide +kernel
    have check11_x1x7x6x0 : check 26 11 210 11 1 7998 14641 68301345 = true := by decide +kernel
    have check11_x1x7x6x1 : check 26 11 210 30 0 9329 14641 68301345 = true := by decide +kernel
    have check11_x1x7x6x5 : check 26 11 210 107 7 12 14641 68301345 = true := by decide +kernel
    have check11_x1x7x6x6 : check 26 11 210 126 6 1343 14641 68301345 = true := by decide +kernel
    have check11_x1x7x6x7 : check 26 11 210 145 5 2674 14641 68301345 = true := by decide +kernel
    have check11_x1x7x6x8 : check 26 11 210 164 4 4005 14641 68301345 = true := by decide +kernel
    have check11_x1x7x6x9 : check 26 11 210 183 3 5336 14641 68301345 = true := by decide +kernel
    have check11_x1x7x6x10 : check 26 11 210 202 2 6667 14641 68301345 = true := by decide +kernel
    have check11_x1x7x6 : check 27 11 210 127 7 12 1331 751314800 = true := by
      apply check_step 26 11 210 127 7 12 1331 751314800 (by norm_num) (by norm_num)
      intro t ht hb
      interval_cases t
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x7x6x0
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x7x6x1
      · norm_num at hb
      · norm_num at hb
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x7x6x5
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x7x6x6
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x7x6x7
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x7x6x8
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x7x6x9
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x7x6x10
    have check11_x1x7x7 : check 27 11 210 146 6 133 1331 751314800 = true := by decide +kernel
    have check11_x1x7x8 : check 27 11 210 165 5 254 1331 751314800 = true := by decide +kernel
    have check11_x1x7x9 : check 27 11 210 184 4 375 1331 751314800 = true := by decide +kernel
    have check11_x1x7x10 : check 27 11 210 203 3 496 1331 751314800 = true := by decide +kernel
    have check11_x1x7 : check 28 11 210 137 7 12 121 8264462809 = true := by
      apply check_step 27 11 210 137 7 12 121 8264462809 (by norm_num) (by norm_num)
      intro t ht hb
      interval_cases t
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x7x0
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x7x1
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x7x2
      · norm_num at hb
      · norm_num at hb
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x7x6
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x7x7
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x7x8
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x7x9
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x7x10
    have check11_x1x8x0 : check 27 11 210 14 4 265 1331 751314800 = true := by decide +kernel
    have check11_x1x8x1 : check 27 11 210 33 3 386 1331 751314800 = true := by decide +kernel
    have check11_x1x8x2 : check 27 11 210 52 2 507 1331 751314800 = true := by decide +kernel
    have check11_x1x8x3 : check 27 11 210 71 1 628 1331 751314800 = true := by decide +kernel
    have check11_x1x8x4 : check 27 11 210 90 0 749 1331 751314800 = true := by decide +kernel
    have check11_x1x8x9 : check 27 11 210 186 6 23 1331 751314800 = true := by decide +kernel
    have check11_x1x8x10 : check 27 11 210 205 5 144 1331 751314800 = true := by decide +kernel
    have check11_x1x8 : check 28 11 210 156 6 23 121 8264462809 = true := by
      apply check_step 27 11 210 156 6 23 121 8264462809 (by norm_num) (by norm_num)
      intro t ht hb
      interval_cases t
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x8x0
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x8x1
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x8x2
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x8x3
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x8x4
      · norm_num at hb
      · norm_num at hb
      · norm_num at hb
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x8x9
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x8x10
    have check11_x1x9 : check 28 11 210 175 5 34 121 8264462809 = true := by decide +kernel
    have check11_x1x10 : check 28 11 210 194 4 45 121 8264462809 = true := by decide +kernel
    have check11_x1 : check 29 11 210 38 8 1 11 90909090909 = true := by
      apply check_step 28 11 210 38 8 1 11 90909090909 (by norm_num) (by norm_num)
      intro t ht hb
      interval_cases t
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x0
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x1
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x2
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x3
      · norm_num at hb
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x6
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x7
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x8
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x9
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1x10
    have check11_x2x0 : check 28 11 210 5 5 24 121 8264462809 = true := by decide +kernel
    have check11_x2x1 : check 28 11 210 24 4 35 121 8264462809 = true := by decide +kernel
    have check11_x2x2 : check 28 11 210 43 3 46 121 8264462809 = true := by decide +kernel
    have check11_x2x3 : check 28 11 210 62 2 57 121 8264462809 = true := by decide +kernel
    have check11_x2x4 : check 28 11 210 81 1 68 121 8264462809 = true := by decide +kernel
    have check11_x2x5 : check 28 11 210 100 0 79 121 8264462809 = true := by decide +kernel
    have check11_x2x9x0 : check 27 11 210 16 6 123 1331 751314800 = true := by decide +kernel
    have check11_x2x9x1 : check 27 11 210 35 5 244 1331 751314800 = true := by decide +kernel
    have check11_x2x9x2 : check 27 11 210 54 4 365 1331 751314800 = true := by decide +kernel
    have check11_x2x9x3 : check 27 11 210 73 3 486 1331 751314800 = true := by decide +kernel
    have check11_x2x9x4 : check 27 11 210 92 2 607 1331 751314800 = true := by decide +kernel
    have check11_x2x9x5 : check 27 11 210 111 1 728 1331 751314800 = true := by decide +kernel
    have check11_x2x9x6 : check 27 11 210 130 0 849 1331 751314800 = true := by decide +kernel
    have check11_x2x9x10x2 : check 26 11 210 57 7 2 14641 68301345 = true := by decide +kernel
    have check11_x2x9x10x3 : check 26 11 210 76 6 1333 14641 68301345 = true := by decide +kernel
    have check11_x2x9x10x4 : check 26 11 210 95 5 2664 14641 68301345 = true := by decide +kernel
    have check11_x2x9x10x5 : check 26 11 210 114 4 3995 14641 68301345 = true := by decide +kernel
    have check11_x2x9x10x6 : check 26 11 210 133 3 5326 14641 68301345 = true := by decide +kernel
    have check11_x2x9x10x7 : check 26 11 210 152 2 6657 14641 68301345 = true := by decide +kernel
    have check11_x2x9x10x8 : check 26 11 210 171 1 7988 14641 68301345 = true := by decide +kernel
    have check11_x2x9x10x9 : check 26 11 210 190 0 9319 14641 68301345 = true := by decide +kernel
    have check11_x2x9x10 : check 27 11 210 207 7 2 1331 751314800 = true := by
      apply check_step 26 11 210 207 7 2 1331 751314800 (by norm_num) (by norm_num)
      intro t ht hb
      interval_cases t
      · norm_num at hb
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x2x9x10x2
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x2x9x10x3
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x2x9x10x4
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x2x9x10x5
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x2x9x10x6
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x2x9x10x7
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x2x9x10x8
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x2x9x10x9
      · norm_num at hb
    have check11_x2x9 : check 28 11 210 177 7 2 121 8264462809 = true := by
      apply check_step 27 11 210 177 7 2 121 8264462809 (by norm_num) (by norm_num)
      intro t ht hb
      interval_cases t
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x2x9x0
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x2x9x1
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x2x9x2
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x2x9x3
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x2x9x4
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x2x9x5
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x2x9x6
      · norm_num at hb
      · norm_num at hb
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x2x9x10
    have check11_x2x10x2 : check 27 11 210 56 6 13 1331 751314800 = true := by decide +kernel
    have check11_x2x10x3 : check 27 11 210 75 5 134 1331 751314800 = true := by decide +kernel
    have check11_x2x10x4 : check 27 11 210 94 4 255 1331 751314800 = true := by decide +kernel
    have check11_x2x10x5 : check 27 11 210 113 3 376 1331 751314800 = true := by decide +kernel
    have check11_x2x10x6 : check 27 11 210 132 2 497 1331 751314800 = true := by decide +kernel
    have check11_x2x10x7 : check 27 11 210 151 1 618 1331 751314800 = true := by decide +kernel
    have check11_x2x10x8 : check 27 11 210 170 0 739 1331 751314800 = true := by decide +kernel
    have check11_x2x10 : check 28 11 210 196 6 13 121 8264462809 = true := by
      apply check_step 27 11 210 196 6 13 121 8264462809 (by norm_num) (by norm_num)
      intro t ht hb
      interval_cases t
      · norm_num at hb
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x2x10x2
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x2x10x3
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x2x10x4
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x2x10x5
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x2x10x6
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x2x10x7
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x2x10x8
      · norm_num at hb
      · norm_num at hb
    have check11_x2 : check 29 11 210 57 7 2 11 90909090909 = true := by
      apply check_step 28 11 210 57 7 2 11 90909090909 (by norm_num) (by norm_num)
      intro t ht hb
      interval_cases t
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x2x0
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x2x1
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x2x2
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x2x3
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x2x4
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x2x5
      · norm_num at hb
      · norm_num at hb
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x2x9
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x2x10
    have check11_x3x1x0 : check 27 11 210 2 2 487 1331 751314800 = true := by decide +kernel
    have check11_x3x1x1 : check 27 11 210 21 1 608 1331 751314800 = true := by decide +kernel
    have check11_x3x1x2 : check 27 11 210 40 0 729 1331 751314800 = true := by decide +kernel
    have check11_x3x1x7 : check 27 11 210 136 6 3 1331 751314800 = true := by decide +kernel
    have check11_x3x1x8 : check 27 11 210 155 5 124 1331 751314800 = true := by decide +kernel
    have check11_x3x1x9 : check 27 11 210 174 4 245 1331 751314800 = true := by decide +kernel
    have check11_x3x1x10 : check 27 11 210 193 3 366 1331 751314800 = true := by decide +kernel
    have check11_x3x1 : check 28 11 210 26 6 3 121 8264462809 = true := by
      apply check_step 27 11 210 26 6 3 121 8264462809 (by norm_num) (by norm_num)
      intro t ht hb
      interval_cases t
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x3x1x0
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x3x1x1
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x3x1x2
      · norm_num at hb
      · norm_num at hb
      · norm_num at hb
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x3x1x7
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x3x1x8
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x3x1x9
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x3x1x10
    have check11_x3x2 : check 28 11 210 45 5 14 121 8264462809 = true := by decide +kernel
    have check11_x3x3 : check 28 11 210 64 4 25 121 8264462809 = true := by decide +kernel
    have check11_x3x4 : check 28 11 210 83 3 36 121 8264462809 = true := by decide +kernel
    have check11_x3x5 : check 28 11 210 102 2 47 121 8264462809 = true := by decide +kernel
    have check11_x3x6 : check 28 11 210 121 1 58 121 8264462809 = true := by decide +kernel
    have check11_x3x7 : check 28 11 210 140 0 69 121 8264462809 = true := by decide +kernel
    have check11_x3 : check 29 11 210 76 6 3 11 90909090909 = true := by
      apply check_step 28 11 210 76 6 3 11 90909090909 (by norm_num) (by norm_num)
      intro t ht hb
      interval_cases t
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x3x1
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x3x2
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x3x3
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x3x4
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x3x5
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x3x6
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x3x7
      · norm_num at hb
      · norm_num at hb
      · norm_num at hb
    have check11_x4 : check 29 11 210 95 5 4 11 90909090909 = true := by decide +kernel
    have check11_x5 : check 29 11 210 114 4 5 11 90909090909 = true := by decide +kernel
    have check11_x6 : check 29 11 210 133 3 6 11 90909090909 = true := by decide +kernel
    have check11_x7 : check 29 11 210 152 2 7 11 90909090909 = true := by decide +kernel
    have check11_x8 : check 29 11 210 171 1 8 11 90909090909 = true := by decide +kernel
    have check11_x9 : check 29 11 210 190 0 9 11 90909090909 = true := by decide +kernel
    apply check_step 29 11 210 209 9 0 1 999999999999 (by norm_num) (by norm_num)
    intro t ht hb
    interval_cases t
    · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x0
    · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x1
    · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x2
    · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x3
    · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x4
    · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x5
    · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x6
    · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x7
    · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x8
    · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check11_x9
    · norm_num at hb
  have check13 : check 30 13 2310 2309 11 0 1 999999999999 = true := by
    have check13_x0 : check 29 13 2310 177 3 8 13 76923076923 = true := by decide +kernel
    have check13_x1x0 : check 28 13 2310 27 3 56 169 5917159763 = true := by decide +kernel
    have check13_x1x1 : check 28 13 2310 205 7 4 169 5917159763 = true := by decide +kernel
    have check13_x1x3 : check 28 13 2310 560 2 69 169 5917159763 = true := by decide +kernel
    have check13_x1x4 : check 28 13 2310 738 6 17 169 5917159763 = true := by decide +kernel
    have check13_x1x6 : check 28 13 2310 1093 1 82 169 5917159763 = true := by decide +kernel
    have check13_x1x7 : check 28 13 2310 1271 5 30 169 5917159763 = true := by decide +kernel
    have check13_x1x9 : check 28 13 2310 1626 0 95 169 5917159763 = true := by decide +kernel
    have check13_x1x10 : check 28 13 2310 1804 4 43 169 5917159763 = true := by decide +kernel
    have check13_x1 : check 29 13 2310 355 7 4 13 76923076923 = true := by
      apply check_step 28 13 2310 355 7 4 13 76923076923 (by norm_num) (by norm_num)
      intro t ht hb
      interval_cases t
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x1x0
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x1x1
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x1x3
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x1x4
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x1x6
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x1x7
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x1x9
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x1x10
      · norm_num at hb
      · norm_num at hb
    have check13_x2x0x0 : check 27 13 2310 3 9 338 2197 455166135 = true := by decide +kernel
    have check13_x2x0x1 : check 27 13 2310 180 0 1859 2197 455166135 = true := by decide +kernel
    have check13_x2x0x2 : check 27 13 2310 358 4 1183 2197 455166135 = true := by decide +kernel
    have check13_x2x0x3 : check 27 13 2310 536 8 507 2197 455166135 = true := by decide +kernel
    have check13_x2x0x5 : check 27 13 2310 891 3 1352 2197 455166135 = true := by decide +kernel
    have check13_x2x0x6 : check 27 13 2310 1069 7 676 2197 455166135 = true := by decide +kernel
    have check13_x2x0x7x1 : check 26 13 2310 273 3 17576 28561 35012779 = true := by decide +kernel
    have check13_x2x0x7x2 : check 26 13 2310 451 7 8788 28561 35012779 = true := by decide +kernel
    have check13_x2x0x7x3 : check 26 13 2310 629 11 0 28561 35012779 = true := by decide +kernel
    have check13_x2x0x7x4 : check 26 13 2310 806 2 19773 28561 35012779 = true := by decide +kernel
    have check13_x2x0x7x5 : check 26 13 2310 984 6 10985 28561 35012779 = true := by decide +kernel
    have check13_x2x0x7x6 : check 26 13 2310 1162 10 2197 28561 35012779 = true := by decide +kernel
    have check13_x2x0x7x7 : check 26 13 2310 1339 1 21970 28561 35012779 = true := by decide +kernel
    have check13_x2x0x7x8 : check 26 13 2310 1517 5 13182 28561 35012779 = true := by decide +kernel
    have check13_x2x0x7x9 : check 26 13 2310 1695 9 4394 28561 35012779 = true := by decide +kernel
    have check13_x2x0x7x10 : check 26 13 2310 1872 0 24167 28561 35012779 = true := by decide +kernel
    have check13_x2x0x7x11 : check 26 13 2310 2050 4 15379 28561 35012779 = true := by decide +kernel
    have check13_x2x0x7x12 : check 26 13 2310 2228 8 6591 28561 35012779 = true := by decide +kernel
    have check13_x2x0x7 : check 27 13 2310 1247 11 0 2197 455166135 = true := by
      apply check_step 26 13 2310 1247 11 0 2197 455166135 (by norm_num) (by norm_num)
      intro t ht hb
      interval_cases t
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x2x0x7x1
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x2x0x7x2
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x2x0x7x3
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x2x0x7x4
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x2x0x7x5
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x2x0x7x6
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x2x0x7x7
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x2x0x7x8
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x2x0x7x9
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x2x0x7x10
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x2x0x7x11
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x2x0x7x12
    have check13_x2x0x8 : check 27 13 2310 1424 2 1521 2197 455166135 = true := by decide +kernel
    have check13_x2x0x9 : check 27 13 2310 1602 6 845 2197 455166135 = true := by decide +kernel
    have check13_x2x0x10x1 : check 26 13 2310 314 2 17745 28561 35012779 = true := by decide +kernel
    have check13_x2x0x10x2 : check 26 13 2310 492 6 8957 28561 35012779 = true := by decide +kernel
    have check13_x2x0x10x3 : check 26 13 2310 670 10 169 28561 35012779 = true := by decide +kernel
    have check13_x2x0x10x4 : check 26 13 2310 847 1 19942 28561 35012779 = true := by decide +kernel
    have check13_x2x0x10x5 : check 26 13 2310 1025 5 11154 28561 35012779 = true := by decide +kernel
    have check13_x2x0x10x6 : check 26 13 2310 1203 9 2366 28561 35012779 = true := by decide +kernel
    have check13_x2x0x10x7 : check 26 13 2310 1380 0 22139 28561 35012779 = true := by decide +kernel
    have check13_x2x0x10x8 : check 26 13 2310 1558 4 13351 28561 35012779 = true := by decide +kernel
    have check13_x2x0x10x9 : check 26 13 2310 1736 8 4563 28561 35012779 = true := by decide +kernel
    have check13_x2x0x10x11 : check 26 13 2310 2091 3 15548 28561 35012779 = true := by decide +kernel
    have check13_x2x0x10x12 : check 26 13 2310 2269 7 6760 28561 35012779 = true := by decide +kernel
    have check13_x2x0x10 : check 27 13 2310 1780 10 169 2197 455166135 = true := by
      apply check_step 26 13 2310 1780 10 169 2197 455166135 (by norm_num) (by norm_num)
      intro t ht hb
      interval_cases t
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x2x0x10x1
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x2x0x10x2
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x2x0x10x3
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x2x0x10x4
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x2x0x10x5
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x2x0x10x6
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x2x0x10x7
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x2x0x10x8
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x2x0x10x9
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x2x0x10x11
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x2x0x10x12
    have check13_x2x0x11 : check 27 13 2310 1957 1 1690 2197 455166135 = true := by decide +kernel
    have check13_x2x0x12 : check 27 13 2310 2135 5 1014 2197 455166135 = true := by decide +kernel
    have check13_x2x0 : check 28 13 2310 41 11 0 169 5917159763 = true := by
      apply check_step 27 13 2310 41 11 0 169 5917159763 (by norm_num) (by norm_num)
      intro t ht hb
      interval_cases t
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x2x0x0
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x2x0x1
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x2x0x2
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x2x0x3
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x2x0x5
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x2x0x6
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x2x0x7
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x2x0x8
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x2x0x9
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x2x0x10
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x2x0x11
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x2x0x12
    have check13_x2x1 : check 28 13 2310 218 2 117 169 5917159763 = true := by decide +kernel
    have check13_x2x2 : check 28 13 2310 396 6 65 169 5917159763 = true := by decide +kernel
    have check13_x2x3x0 : check 27 13 2310 44 8 351 2197 455166135 = true := by decide +kernel
    have check13_x2x3x2 : check 27 13 2310 399 3 1196 2197 455166135 = true := by decide +kernel
    have check13_x2x3x3 : check 27 13 2310 577 7 520 2197 455166135 = true := by decide +kernel
    have check13_x2x3x5 : check 27 13 2310 932 2 1365 2197 455166135 = true := by decide +kernel
    have check13_x2x3x6 : check 27 13 2310 1110 6 689 2197 455166135 = true := by decide +kernel
    have check13_x2x3x7x0 : check 26 13 2310 99 9 2210 28561 35012779 = true := by decide +kernel
    have check13_x2x3x7x1 : check 26 13 2310 276 0 21983 28561 35012779 = true := by decide +kernel
    have check13_x2x3x7x2 : check 26 13 2310 454 4 13195 28561 35012779 = true := by decide +kernel
    have check13_x2x3x7x3 : check 26 13 2310 632 8 4407 28561 35012779 = true := by decide +kernel
    have check13_x2x3x7x5 : check 26 13 2310 987 3 15392 28561 35012779 = true := by decide +kernel
    have check13_x2x3x7x6 : check 26 13 2310 1165 7 6604 28561 35012779 = true := by decide +kernel
    have check13_x2x3x7x8 : check 26 13 2310 1520 2 17589 28561 35012779 = true := by decide +kernel
    have check13_x2x3x7x9 : check 26 13 2310 1698 6 8801 28561 35012779 = true := by decide +kernel
    have check13_x2x3x7x10 : check 26 13 2310 1876 10 13 28561 35012779 = true := by decide +kernel
    have check13_x2x3x7x11 : check 26 13 2310 2053 1 19786 28561 35012779 = true := by decide +kernel
    have check13_x2x3x7x12 : check 26 13 2310 2231 5 10998 28561 35012779 = true := by decide +kernel
    have check13_x2x3x7 : check 27 13 2310 1288 10 13 2197 455166135 = true := by
      apply check_step 26 13 2310 1288 10 13 2197 455166135 (by norm_num) (by norm_num)
      intro t ht hb
      interval_cases t
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x2x3x7x0
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x2x3x7x1
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x2x3x7x2
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x2x3x7x3
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x2x3x7x5
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x2x3x7x6
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x2x3x7x8
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x2x3x7x9
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x2x3x7x10
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x2x3x7x11
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x2x3x7x12
    have check13_x2x3x8 : check 27 13 2310 1465 1 1534 2197 455166135 = true := by decide +kernel
    have check13_x2x3x9 : check 27 13 2310 1643 5 858 2197 455166135 = true := by decide +kernel
    have check13_x2x3x10 : check 27 13 2310 1821 9 182 2197 455166135 = true := by decide +kernel
    have check13_x2x3x11 : check 27 13 2310 1998 0 1703 2197 455166135 = true := by decide +kernel
    have check13_x2x3x12 : check 27 13 2310 2176 4 1027 2197 455166135 = true := by decide +kernel
    have check13_x2x3 : check 28 13 2310 574 10 13 169 5917159763 = true := by
      apply check_step 27 13 2310 574 10 13 169 5917159763 (by norm_num) (by norm_num)
      intro t ht hb
      interval_cases t
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x2x3x0
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x2x3x2
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x2x3x3
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x2x3x5
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x2x3x6
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x2x3x7
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x2x3x8
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x2x3x9
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x2x3x10
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x2x3x11
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x2x3x12
    have check13_x2x4 : check 28 13 2310 751 1 130 169 5917159763 = true := by decide +kernel
    have check13_x2x5 : check 28 13 2310 929 5 78 169 5917159763 = true := by decide +kernel
    have check13_x2x6x0 : check 27 13 2310 85 7 364 2197 455166135 = true := by decide +kernel
    have check13_x2x6x2 : check 27 13 2310 440 2 1209 2197 455166135 = true := by decide +kernel
    have check13_x2x6x3 : check 27 13 2310 618 6 533 2197 455166135 = true := by decide +kernel
    have check13_x2x6x5 : check 27 13 2310 973 1 1378 2197 455166135 = true := by decide +kernel
    have check13_x2x6x6 : check 27 13 2310 1151 5 702 2197 455166135 = true := by decide +kernel
    have check13_x2x6x7 : check 27 13 2310 1329 9 26 2197 455166135 = true := by decide +kernel
    have check13_x2x6x8 : check 27 13 2310 1506 0 1547 2197 455166135 = true := by decide +kernel
    have check13_x2x6x9 : check 27 13 2310 1684 4 871 2197 455166135 = true := by decide +kernel
    have check13_x2x6x10 : check 27 13 2310 1862 8 195 2197 455166135 = true := by decide +kernel
    have check13_x2x6x12 : check 27 13 2310 2217 3 1040 2197 455166135 = true := by decide +kernel
    have check13_x2x6 : check 28 13 2310 1107 9 26 169 5917159763 = true := by
      apply check_step 27 13 2310 1107 9 26 169 5917159763 (by norm_num) (by norm_num)
      intro t ht hb
      interval_cases t
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x2x6x0
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x2x6x2
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x2x6x3
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x2x6x5
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x2x6x6
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x2x6x7
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x2x6x8
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x2x6x9
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x2x6x10
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x2x6x12
    have check13_x2x7 : check 28 13 2310 1284 0 143 169 5917159763 = true := by decide +kernel
    have check13_x2x8 : check 28 13 2310 1462 4 91 169 5917159763 = true := by decide +kernel
    have check13_x2x9x0 : check 27 13 2310 126 6 377 2197 455166135 = true := by decide +kernel
    have check13_x2x9x2 : check 27 13 2310 481 1 1222 2197 455166135 = true := by decide +kernel
    have check13_x2x9x3 : check 27 13 2310 659 5 546 2197 455166135 = true := by decide +kernel
    have check13_x2x9x5 : check 27 13 2310 1014 0 1391 2197 455166135 = true := by decide +kernel
    have check13_x2x9x6 : check 27 13 2310 1192 4 715 2197 455166135 = true := by decide +kernel
    have check13_x2x9x7 : check 27 13 2310 1370 8 39 2197 455166135 = true := by decide +kernel
    have check13_x2x9x9 : check 27 13 2310 1725 3 884 2197 455166135 = true := by decide +kernel
    have check13_x2x9x10 : check 27 13 2310 1903 7 208 2197 455166135 = true := by decide +kernel
    have check13_x2x9x12 : check 27 13 2310 2258 2 1053 2197 455166135 = true := by decide +kernel
    have check13_x2x9 : check 28 13 2310 1640 8 39 169 5917159763 = true := by
      apply check_step 27 13 2310 1640 8 39 169 5917159763 (by norm_num) (by norm_num)
      intro t ht hb
      interval_cases t
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x2x9x0
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x2x9x2
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x2x9x3
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x2x9x5
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x2x9x6
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x2x9x7
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x2x9x9
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x2x9x10
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x2x9x12
    have check13_x2x11 : check 28 13 2310 1995 3 104 169 5917159763 = true := by decide +kernel
    have check13_x2x12 : check 28 13 2310 2173 7 52 169 5917159763 = true := by decide +kernel
    have check13_x2 : check 29 13 2310 533 11 0 13 76923076923 = true := by
      apply check_step 28 13 2310 533 11 0 13 76923076923 (by norm_num) (by norm_num)
      intro t ht hb
      interval_cases t
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x2x0
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x2x1
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x2x2
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x2x3
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x2x4
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x2x5
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x2x6
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x2x7
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x2x8
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x2x9
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x2x11
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x2x12
    have check13_x3 : check 29 13 2310 710 2 9 13 76923076923 = true := by decide +kernel
    have check13_x4 : check 29 13 2310 888 6 5 13 76923076923 = true := by decide +kernel
    have check13_x5x0x0 : check 27 13 2310 6 6 677 2197 455166135 = true := by decide +kernel
    have check13_x5x0x1x0 : check 26 13 2310 14 8 4395 28561 35012779 = true := by decide +kernel
    have check13_x5x0x1x2 : check 26 13 2310 369 3 15380 28561 35012779 = true := by decide +kernel
    have check13_x5x0x1x3 : check 26 13 2310 547 7 6592 28561 35012779 = true := by decide +kernel
    have check13_x5x0x1x5 : check 26 13 2310 902 2 17577 28561 35012779 = true := by decide +kernel
    have check13_x5x0x1x6 : check 26 13 2310 1080 6 8789 28561 35012779 = true := by decide +kernel
    have check13_x5x0x1x7 : check 26 13 2310 1258 10 1 28561 35012779 = true := by decide +kernel
    have check13_x5x0x1x8 : check 26 13 2310 1435 1 19774 28561 35012779 = true := by decide +kernel
    have check13_x5x0x1x9 : check 26 13 2310 1613 5 10986 28561 35012779 = true := by decide +kernel
    have check13_x5x0x1x10 : check 26 13 2310 1791 9 2198 28561 35012779 = true := by decide +kernel
    have check13_x5x0x1x11 : check 26 13 2310 1968 0 21971 28561 35012779 = true := by decide +kernel
    have check13_x5x0x1x12 : check 26 13 2310 2146 4 13183 28561 35012779 = true := by decide +kernel
    have check13_x5x0x1 : check 27 13 2310 184 10 1 2197 455166135 = true := by
      apply check_step 26 13 2310 184 10 1 2197 455166135 (by norm_num) (by norm_num)
      intro t ht hb
      interval_cases t
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x0x1x0
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x0x1x2
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x0x1x3
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x0x1x5
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x0x1x6
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x0x1x7
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x0x1x8
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x0x1x9
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x0x1x10
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x0x1x11
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x0x1x12
    have check13_x5x0x2 : check 27 13 2310 361 1 1522 2197 455166135 = true := by decide +kernel
    have check13_x5x0x3 : check 27 13 2310 539 5 846 2197 455166135 = true := by decide +kernel
    have check13_x5x0x4 : check 27 13 2310 717 9 170 2197 455166135 = true := by decide +kernel
    have check13_x5x0x5 : check 27 13 2310 894 0 1691 2197 455166135 = true := by decide +kernel
    have check13_x5x0x6 : check 27 13 2310 1072 4 1015 2197 455166135 = true := by decide +kernel
    have check13_x5x0x7 : check 27 13 2310 1250 8 339 2197 455166135 = true := by decide +kernel
    have check13_x5x0x9 : check 27 13 2310 1605 3 1184 2197 455166135 = true := by decide +kernel
    have check13_x5x0x10 : check 27 13 2310 1783 7 508 2197 455166135 = true := by decide +kernel
    have check13_x5x0x12 : check 27 13 2310 2138 2 1353 2197 455166135 = true := by decide +kernel
    have check13_x5x0 : check 28 13 2310 82 10 1 169 5917159763 = true := by
      apply check_step 27 13 2310 82 10 1 169 5917159763 (by norm_num) (by norm_num)
      intro t ht hb
      interval_cases t
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x0x0
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x0x1
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x0x2
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x0x3
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x0x4
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x0x5
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x0x6
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x0x7
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x0x9
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x0x10
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x0x12
    have check13_x5x1 : check 28 13 2310 259 1 118 169 5917159763 = true := by decide +kernel
    have check13_x5x2 : check 28 13 2310 437 5 66 169 5917159763 = true := by decide +kernel
    have check13_x5x3x0 : check 27 13 2310 47 5 690 2197 455166135 = true := by decide +kernel
    have check13_x5x3x1 : check 27 13 2310 225 9 14 2197 455166135 = true := by decide +kernel
    have check13_x5x3x2 : check 27 13 2310 402 0 1535 2197 455166135 = true := by decide +kernel
    have check13_x5x3x3 : check 27 13 2310 580 4 859 2197 455166135 = true := by decide +kernel
    have check13_x5x3x4 : check 27 13 2310 758 8 183 2197 455166135 = true := by decide +kernel
    have check13_x5x3x6 : check 27 13 2310 1113 3 1028 2197 455166135 = true := by decide +kernel
    have check13_x5x3x7 : check 27 13 2310 1291 7 352 2197 455166135 = true := by decide +kernel
    have check13_x5x3x9 : check 27 13 2310 1646 2 1197 2197 455166135 = true := by decide +kernel
    have check13_x5x3x10 : check 27 13 2310 1824 6 521 2197 455166135 = true := by decide +kernel
    have check13_x5x3x12 : check 27 13 2310 2179 1 1366 2197 455166135 = true := by decide +kernel
    have check13_x5x3 : check 28 13 2310 615 9 14 169 5917159763 = true := by
      apply check_step 27 13 2310 615 9 14 169 5917159763 (by norm_num) (by norm_num)
      intro t ht hb
      interval_cases t
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x3x0
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x3x1
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x3x2
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x3x3
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x3x4
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x3x6
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x3x7
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x3x9
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x3x10
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x3x12
    have check13_x5x4 : check 28 13 2310 792 0 131 169 5917159763 = true := by decide +kernel
    have check13_x5x5 : check 28 13 2310 970 4 79 169 5917159763 = true := by decide +kernel
    have check13_x5x6x0 : check 27 13 2310 88 4 703 2197 455166135 = true := by decide +kernel
    have check13_x5x6x1 : check 27 13 2310 266 8 27 2197 455166135 = true := by decide +kernel
    have check13_x5x6x3 : check 27 13 2310 621 3 872 2197 455166135 = true := by decide +kernel
    have check13_x5x6x4 : check 27 13 2310 799 7 196 2197 455166135 = true := by decide +kernel
    have check13_x5x6x6 : check 27 13 2310 1154 2 1041 2197 455166135 = true := by decide +kernel
    have check13_x5x6x7 : check 27 13 2310 1332 6 365 2197 455166135 = true := by decide +kernel
    have check13_x5x6x9 : check 27 13 2310 1687 1 1210 2197 455166135 = true := by decide +kernel
    have check13_x5x6x10 : check 27 13 2310 1865 5 534 2197 455166135 = true := by decide +kernel
    have check13_x5x6x12 : check 27 13 2310 2220 0 1379 2197 455166135 = true := by decide +kernel
    have check13_x5x6 : check 28 13 2310 1148 8 27 169 5917159763 = true := by
      apply check_step 27 13 2310 1148 8 27 169 5917159763 (by norm_num) (by norm_num)
      intro t ht hb
      interval_cases t
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x6x0
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x6x1
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x6x3
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x6x4
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x6x6
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x6x7
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x6x9
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x6x10
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x6x12
    have check13_x5x8 : check 28 13 2310 1503 3 92 169 5917159763 = true := by decide +kernel
    have check13_x5x9 : check 28 13 2310 1681 7 40 169 5917159763 = true := by decide +kernel
    have check13_x5x11 : check 28 13 2310 2036 2 105 169 5917159763 = true := by decide +kernel
    have check13_x5x12 : check 28 13 2310 2214 6 53 169 5917159763 = true := by decide +kernel
    have check13_x5 : check 29 13 2310 1066 10 1 13 76923076923 = true := by
      apply check_step 28 13 2310 1066 10 1 13 76923076923 (by norm_num) (by norm_num)
      intro t ht hb
      interval_cases t
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x0
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x1
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x2
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x3
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x4
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x5
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x6
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x8
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x9
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x11
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5x12
    have check13_x6 : check 29 13 2310 1243 1 10 13 76923076923 = true := by decide +kernel
    have check13_x7 : check 29 13 2310 1421 5 6 13 76923076923 = true := by decide +kernel
    have check13_x8x0x0 : check 27 13 2310 9 3 1016 2197 455166135 = true := by decide +kernel
    have check13_x8x0x1 : check 27 13 2310 187 7 340 2197 455166135 = true := by decide +kernel
    have check13_x8x0x3 : check 27 13 2310 542 2 1185 2197 455166135 = true := by decide +kernel
    have check13_x8x0x4 : check 27 13 2310 720 6 509 2197 455166135 = true := by decide +kernel
    have check13_x8x0x6 : check 27 13 2310 1075 1 1354 2197 455166135 = true := by decide +kernel
    have check13_x8x0x7 : check 27 13 2310 1253 5 678 2197 455166135 = true := by decide +kernel
    have check13_x8x0x8 : check 27 13 2310 1431 9 2 2197 455166135 = true := by decide +kernel
    have check13_x8x0x9 : check 27 13 2310 1608 0 1523 2197 455166135 = true := by decide +kernel
    have check13_x8x0x10 : check 27 13 2310 1786 4 847 2197 455166135 = true := by decide +kernel
    have check13_x8x0x11 : check 27 13 2310 1964 8 171 2197 455166135 = true := by decide +kernel
    have check13_x8x0 : check 28 13 2310 123 9 2 169 5917159763 = true := by
      apply check_step 27 13 2310 123 9 2 169 5917159763 (by norm_num) (by norm_num)
      intro t ht hb
      interval_cases t
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x8x0x0
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x8x0x1
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x8x0x3
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x8x0x4
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x8x0x6
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x8x0x7
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x8x0x8
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x8x0x9
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x8x0x10
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x8x0x11
      · norm_num at hb
    have check13_x8x1 : check 28 13 2310 300 0 119 169 5917159763 = true := by decide +kernel
    have check13_x8x2 : check 28 13 2310 478 4 67 169 5917159763 = true := by decide +kernel
    have check13_x8x3x0 : check 27 13 2310 50 2 1029 2197 455166135 = true := by decide +kernel
    have check13_x8x3x1 : check 27 13 2310 228 6 353 2197 455166135 = true := by decide +kernel
    have check13_x8x3x3 : check 27 13 2310 583 1 1198 2197 455166135 = true := by decide +kernel
    have check13_x8x3x4 : check 27 13 2310 761 5 522 2197 455166135 = true := by decide +kernel
    have check13_x8x3x6 : check 27 13 2310 1116 0 1367 2197 455166135 = true := by decide +kernel
    have check13_x8x3x7 : check 27 13 2310 1294 4 691 2197 455166135 = true := by decide +kernel
    have check13_x8x3x8 : check 27 13 2310 1472 8 15 2197 455166135 = true := by decide +kernel
    have check13_x8x3x10 : check 27 13 2310 1827 3 860 2197 455166135 = true := by decide +kernel
    have check13_x8x3x11 : check 27 13 2310 2005 7 184 2197 455166135 = true := by decide +kernel
    have check13_x8x3 : check 28 13 2310 656 8 15 169 5917159763 = true := by
      apply check_step 27 13 2310 656 8 15 169 5917159763 (by norm_num) (by norm_num)
      intro t ht hb
      interval_cases t
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x8x3x0
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x8x3x1
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x8x3x3
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x8x3x4
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x8x3x6
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x8x3x7
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x8x3x8
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x8x3x10
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x8x3x11
      · norm_num at hb
    have check13_x8x5 : check 28 13 2310 1011 3 80 169 5917159763 = true := by decide +kernel
    have check13_x8x6 : check 28 13 2310 1189 7 28 169 5917159763 = true := by decide +kernel
    have check13_x8x8 : check 28 13 2310 1544 2 93 169 5917159763 = true := by decide +kernel
    have check13_x8x9 : check 28 13 2310 1722 6 41 169 5917159763 = true := by decide +kernel
    have check13_x8x11 : check 28 13 2310 2077 1 106 169 5917159763 = true := by decide +kernel
    have check13_x8x12 : check 28 13 2310 2255 5 54 169 5917159763 = true := by decide +kernel
    have check13_x8 : check 29 13 2310 1599 9 2 13 76923076923 = true := by
      apply check_step 28 13 2310 1599 9 2 13 76923076923 (by norm_num) (by norm_num)
      intro t ht hb
      interval_cases t
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x8x0
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x8x1
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x8x2
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x8x3
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x8x5
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x8x6
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x8x8
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x8x9
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x8x11
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x8x12
    have check13_x9 : check 29 13 2310 1776 0 11 13 76923076923 = true := by decide +kernel
    have check13_x10 : check 29 13 2310 1954 4 7 13 76923076923 = true := by decide +kernel
    have check13_x11x0x0 : check 27 13 2310 12 0 1355 2197 455166135 = true := by decide +kernel
    have check13_x11x0x1 : check 27 13 2310 190 4 679 2197 455166135 = true := by decide +kernel
    have check13_x11x0x2 : check 27 13 2310 368 8 3 2197 455166135 = true := by decide +kernel
    have check13_x11x0x4 : check 27 13 2310 723 3 848 2197 455166135 = true := by decide +kernel
    have check13_x11x0x5 : check 27 13 2310 901 7 172 2197 455166135 = true := by decide +kernel
    have check13_x11x0x7 : check 27 13 2310 1256 2 1017 2197 455166135 = true := by decide +kernel
    have check13_x11x0x8 : check 27 13 2310 1434 6 341 2197 455166135 = true := by decide +kernel
    have check13_x11x0x10 : check 27 13 2310 1789 1 1186 2197 455166135 = true := by decide +kernel
    have check13_x11x0x11 : check 27 13 2310 1967 5 510 2197 455166135 = true := by decide +kernel
    have check13_x11x0 : check 28 13 2310 164 8 3 169 5917159763 = true := by
      apply check_step 27 13 2310 164 8 3 169 5917159763 (by norm_num) (by norm_num)
      intro t ht hb
      interval_cases t
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x0x0
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x0x1
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x0x2
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x0x4
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x0x5
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x0x7
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x0x8
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x0x10
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x0x11
      · norm_num at hb
    have check13_x11x2 : check 28 13 2310 519 3 68 169 5917159763 = true := by decide +kernel
    have check13_x11x3 : check 28 13 2310 697 7 16 169 5917159763 = true := by decide +kernel
    have check13_x11x5 : check 28 13 2310 1052 2 81 169 5917159763 = true := by decide +kernel
    have check13_x11x6 : check 28 13 2310 1230 6 29 169 5917159763 = true := by decide +kernel
    have check13_x11x8 : check 28 13 2310 1585 1 94 169 5917159763 = true := by decide +kernel
    have check13_x11x9 : check 28 13 2310 1763 5 42 169 5917159763 = true := by decide +kernel
    have check13_x11x11 : check 28 13 2310 2118 0 107 169 5917159763 = true := by decide +kernel
    have check13_x11x12 : check 28 13 2310 2296 4 55 169 5917159763 = true := by decide +kernel
    have check13_x11 : check 29 13 2310 2132 8 3 13 76923076923 = true := by
      apply check_step 28 13 2310 2132 8 3 13 76923076923 (by norm_num) (by norm_num)
      intro t ht hb
      interval_cases t
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x0
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x2
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x3
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x5
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x6
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x8
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x9
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x11
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11x12
    apply check_step 29 13 2310 2309 11 0 1 999999999999 (by norm_num) (by norm_num)
    intro t ht hb
    interval_cases t
    · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x0
    · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x1
    · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x2
    · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x3
    · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x4
    · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x5
    · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x6
    · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x7
    · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x8
    · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x9
    · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x10
    · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check13_x11
    · norm_num at hb
  have check17 : check 30 17 30030 30029 15 0 1 999999999999 = true := by
    have check17_x0x1 : check 28 17 30030 1870 2 109 289 3460207612 = true := by decide +kernel
    have check17_x0x3 : check 28 17 30030 5403 3 92 289 3460207612 = true := by decide +kernel
    have check17_x0x5 : check 28 17 30030 8936 4 75 289 3460207612 = true := by decide +kernel
    have check17_x0x7 : check 28 17 30030 12469 5 58 289 3460207612 = true := by decide +kernel
    have check17_x0x9 : check 28 17 30030 16002 6 41 289 3460207612 = true := by decide +kernel
    have check17_x0x11 : check 28 17 30030 19535 7 24 289 3460207612 = true := by decide +kernel
    have check17_x0x13 : check 28 17 30030 23068 8 7 289 3460207612 = true := by decide +kernel
    have check17_x0x14 : check 28 17 30030 24834 0 143 289 3460207612 = true := by decide +kernel
    have check17_x0x16 : check 28 17 30030 28367 1 126 289 3460207612 = true := by decide +kernel
    have check17_x0 : check 29 17 30030 1766 8 7 17 58823529411 = true := by
      apply check_step 28 17 30030 1766 8 7 17 58823529411 (by norm_num) (by norm_num)
      intro t ht hb
      interval_cases t
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x0x1
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x0x3
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x0x5
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x0x7
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x0x9
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x0x11
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x0x13
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x0x14
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x0x16
    have check17_x1 : check 29 17 30030 3532 0 15 17 58823529411 = true := by decide +kernel
    have check17_x2x1 : check 28 17 30030 2078 6 57 289 3460207612 = true := by decide +kernel
    have check17_x2x3 : check 28 17 30030 5611 7 40 289 3460207612 = true := by decide +kernel
    have check17_x2x5 : check 28 17 30030 9144 8 23 289 3460207612 = true := by decide +kernel
    have check17_x2x6 : check 28 17 30030 10910 0 159 289 3460207612 = true := by decide +kernel
    have check17_x2x7 : check 28 17 30030 12677 9 6 289 3460207612 = true := by decide +kernel
    have check17_x2x8 : check 28 17 30030 14443 1 142 289 3460207612 = true := by decide +kernel
    have check17_x2x10 : check 28 17 30030 17976 2 125 289 3460207612 = true := by decide +kernel
    have check17_x2x12 : check 28 17 30030 21509 3 108 289 3460207612 = true := by decide +kernel
    have check17_x2x14 : check 28 17 30030 25042 4 91 289 3460207612 = true := by decide +kernel
    have check17_x2x16 : check 28 17 30030 28575 5 74 289 3460207612 = true := by decide +kernel
    have check17_x2 : check 29 17 30030 5299 9 6 17 58823529411 = true := by
      apply check_step 28 17 30030 5299 9 6 17 58823529411 (by norm_num) (by norm_num)
      intro t ht hb
      interval_cases t
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x2x1
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x2x3
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x2x5
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x2x6
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x2x7
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x2x8
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x2x10
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x2x12
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x2x14
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x2x16
    have check17_x3 : check 29 17 30030 7065 1 14 17 58823529411 = true := by decide +kernel
    have check17_x4x0 : check 28 17 30030 519 1 158 289 3460207612 = true := by decide +kernel
    have check17_x4x1x0 : check 27 17 30030 134 2 2317 4913 203541624 = true := by decide +kernel
    have check17_x4x1x2 : check 27 17 30030 3667 3 2028 4913 203541624 = true := by decide +kernel
    have check17_x4x1x4 : check 27 17 30030 7200 4 1739 4913 203541624 = true := by decide +kernel
    have check17_x4x1x6 : check 27 17 30030 10733 5 1450 4913 203541624 = true := by decide +kernel
    have check17_x4x1x8 : check 27 17 30030 14266 6 1161 4913 203541624 = true := by decide +kernel
    have check17_x4x1x10 : check 27 17 30030 17799 7 872 4913 203541624 = true := by decide +kernel
    have check17_x4x1x12 : check 27 17 30030 21332 8 583 4913 203541624 = true := by decide +kernel
    have check17_x4x1x13 : check 27 17 30030 23098 0 2895 4913 203541624 = true := by decide +kernel
    have check17_x4x1x14 : check 27 17 30030 24865 9 294 4913 203541624 = true := by decide +kernel
    have check17_x4x1x15 : check 27 17 30030 26631 1 2606 4913 203541624 = true := by decide +kernel
    have check17_x4x1x16 : check 27 17 30030 28398 10 5 4913 203541624 = true := by decide +kernel
    have check17_x4x1 : check 28 17 30030 2286 10 5 289 3460207612 = true := by
      apply check_step 27 17 30030 2286 10 5 289 3460207612 (by norm_num) (by norm_num)
      intro t ht hb
      interval_cases t
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x4x1x0
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x4x1x2
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x4x1x4
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x4x1x6
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x4x1x8
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x4x1x10
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x4x1x12
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x4x1x13
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x4x1x14
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x4x1x15
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x4x1x16
    have check17_x4x2 : check 28 17 30030 4052 2 141 289 3460207612 = true := by decide +kernel
    have check17_x4x4 : check 28 17 30030 7585 3 124 289 3460207612 = true := by decide +kernel
    have check17_x4x6 : check 28 17 30030 11118 4 107 289 3460207612 = true := by decide +kernel
    have check17_x4x8 : check 28 17 30030 14651 5 90 289 3460207612 = true := by decide +kernel
    have check17_x4x10 : check 28 17 30030 18184 6 73 289 3460207612 = true := by decide +kernel
    have check17_x4x12 : check 28 17 30030 21717 7 56 289 3460207612 = true := by decide +kernel
    have check17_x4x14 : check 28 17 30030 25250 8 39 289 3460207612 = true := by decide +kernel
    have check17_x4x15 : check 28 17 30030 27016 0 175 289 3460207612 = true := by decide +kernel
    have check17_x4x16 : check 28 17 30030 28783 9 22 289 3460207612 = true := by decide +kernel
    have check17_x4 : check 29 17 30030 8832 10 5 17 58823529411 = true := by
      apply check_step 28 17 30030 8832 10 5 17 58823529411 (by norm_num) (by norm_num)
      intro t ht hb
      interval_cases t
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x4x0
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x4x1
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x4x2
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x4x4
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x4x6
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x4x8
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x4x10
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x4x12
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x4x14
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x4x15
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x4x16
    have check17_x5 : check 29 17 30030 10598 2 13 17 58823529411 = true := by decide +kernel
    have check17_x6x0 : check 28 17 30030 727 5 106 289 3460207612 = true := by decide +kernel
    have check17_x6x2 : check 28 17 30030 4260 6 89 289 3460207612 = true := by decide +kernel
    have check17_x6x4 : check 28 17 30030 7793 7 72 289 3460207612 = true := by decide +kernel
    have check17_x6x6 : check 28 17 30030 11326 8 55 289 3460207612 = true := by decide +kernel
    have check17_x6x7 : check 28 17 30030 13092 0 191 289 3460207612 = true := by decide +kernel
    have check17_x6x8 : check 28 17 30030 14859 9 38 289 3460207612 = true := by decide +kernel
    have check17_x6x9 : check 28 17 30030 16625 1 174 289 3460207612 = true := by decide +kernel
    have check17_x6x10x1 : check 27 17 30030 2848 4 1755 4913 203541624 = true := by decide +kernel
    have check17_x6x10x3 : check 27 17 30030 6381 5 1466 4913 203541624 = true := by decide +kernel
    have check17_x6x10x5 : check 27 17 30030 9914 6 1177 4913 203541624 = true := by decide +kernel
    have check17_x6x10x7 : check 27 17 30030 13447 7 888 4913 203541624 = true := by decide +kernel
    have check17_x6x10x9 : check 27 17 30030 16980 8 599 4913 203541624 = true := by decide +kernel
    have check17_x6x10x10 : check 27 17 30030 18746 0 2911 4913 203541624 = true := by decide +kernel
    have check17_x6x10x11 : check 27 17 30030 20513 9 310 4913 203541624 = true := by decide +kernel
    have check17_x6x10x12 : check 27 17 30030 22279 1 2622 4913 203541624 = true := by decide +kernel
    have check17_x6x10x13 : check 27 17 30030 24046 10 21 4913 203541624 = true := by decide +kernel
    have check17_x6x10x14 : check 27 17 30030 25812 2 2333 4913 203541624 = true := by decide +kernel
    have check17_x6x10x16 : check 27 17 30030 29345 3 2044 4913 203541624 = true := by decide +kernel
    have check17_x6x10 : check 28 17 30030 18392 10 21 289 3460207612 = true := by
      apply check_step 27 17 30030 18392 10 21 289 3460207612 (by norm_num) (by norm_num)
      intro t ht hb
      interval_cases t
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x6x10x1
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x6x10x3
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x6x10x5
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x6x10x7
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x6x10x9
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x6x10x10
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x6x10x11
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x6x10x12
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x6x10x13
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x6x10x14
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x6x10x16
    have check17_x6x11 : check 28 17 30030 20158 2 157 289 3460207612 = true := by decide +kernel
    have check17_x6x12x1 : check 27 17 30030 3056 8 871 4913 203541624 = true := by decide +kernel
    have check17_x6x12x2 : check 27 17 30030 4822 0 3183 4913 203541624 = true := by decide +kernel
    have check17_x6x12x3 : check 27 17 30030 6589 9 582 4913 203541624 = true := by decide +kernel
    have check17_x6x12x4 : check 27 17 30030 8355 1 2894 4913 203541624 = true := by decide +kernel
    have check17_x6x12x5 : check 27 17 30030 10122 10 293 4913 203541624 = true := by decide +kernel
    have check17_x6x12x6 : check 27 17 30030 11888 2 2605 4913 203541624 = true := by decide +kernel
    have check17_x6x12x7 : check 27 17 30030 13655 11 4 4913 203541624 = true := by decide +kernel
    have check17_x6x12x8 : check 27 17 30030 15421 3 2316 4913 203541624 = true := by decide +kernel
    have check17_x6x12x10 : check 27 17 30030 18954 4 2027 4913 203541624 = true := by decide +kernel
    have check17_x6x12x12 : check 27 17 30030 22487 5 1738 4913 203541624 = true := by decide +kernel
    have check17_x6x12x14 : check 27 17 30030 26020 6 1449 4913 203541624 = true := by decide +kernel
    have check17_x6x12x16 : check 27 17 30030 29553 7 1160 4913 203541624 = true := by decide +kernel
    have check17_x6x12 : check 28 17 30030 21925 11 4 289 3460207612 = true := by
      apply check_step 27 17 30030 21925 11 4 289 3460207612 (by norm_num) (by norm_num)
      intro t ht hb
      interval_cases t
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x6x12x1
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x6x12x2
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x6x12x3
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x6x12x4
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x6x12x5
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x6x12x6
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x6x12x7
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x6x12x8
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x6x12x10
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x6x12x12
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x6x12x14
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x6x12x16
    have check17_x6x13 : check 28 17 30030 23691 3 140 289 3460207612 = true := by decide +kernel
    have check17_x6x15 : check 28 17 30030 27224 4 123 289 3460207612 = true := by decide +kernel
    have check17_x6 : check 29 17 30030 12365 11 4 17 58823529411 = true := by
      apply check_step 28 17 30030 12365 11 4 17 58823529411 (by norm_num) (by norm_num)
      intro t ht hb
      interval_cases t
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x6x0
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x6x2
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x6x4
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x6x6
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x6x7
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x6x8
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x6x9
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x6x10
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x6x11
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x6x12
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x6x13
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x6x15
      · norm_num at hb
    have check17_x7 : check 29 17 30030 14131 3 12 17 58823529411 = true := by decide +kernel
    have check17_x8x0 : check 28 17 30030 935 9 54 289 3460207612 = true := by decide +kernel
    have check17_x8x1 : check 28 17 30030 2701 1 190 289 3460207612 = true := by decide +kernel
    have check17_x8x2x1 : check 27 17 30030 2029 5 1482 4913 203541624 = true := by decide +kernel
    have check17_x8x2x3 : check 27 17 30030 5562 6 1193 4913 203541624 = true := by decide +kernel
    have check17_x8x2x5 : check 27 17 30030 9095 7 904 4913 203541624 = true := by decide +kernel
    have check17_x8x2x7 : check 27 17 30030 12628 8 615 4913 203541624 = true := by decide +kernel
    have check17_x8x2x8 : check 27 17 30030 14394 0 2927 4913 203541624 = true := by decide +kernel
    have check17_x8x2x9 : check 27 17 30030 16161 9 326 4913 203541624 = true := by decide +kernel
    have check17_x8x2x10 : check 27 17 30030 17927 1 2638 4913 203541624 = true := by decide +kernel
    have check17_x8x2x11 : check 27 17 30030 19694 10 37 4913 203541624 = true := by decide +kernel
    have check17_x8x2x12 : check 27 17 30030 21460 2 2349 4913 203541624 = true := by decide +kernel
    have check17_x8x2x14 : check 27 17 30030 24993 3 2060 4913 203541624 = true := by decide +kernel
    have check17_x8x2x16 : check 27 17 30030 28526 4 1771 4913 203541624 = true := by decide +kernel
    have check17_x8x2 : check 28 17 30030 4468 10 37 289 3460207612 = true := by
      apply check_step 27 17 30030 4468 10 37 289 3460207612 (by norm_num) (by norm_num)
      intro t ht hb
      interval_cases t
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x2x1
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x2x3
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x2x5
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x2x7
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x2x8
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x2x9
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x2x10
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x2x11
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x2x12
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x2x14
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x2x16
    have check17_x8x3 : check 28 17 30030 6234 2 173 289 3460207612 = true := by decide +kernel
    have check17_x8x4x0 : check 27 17 30030 470 0 3199 4913 203541624 = true := by decide +kernel
    have check17_x8x4x1 : check 27 17 30030 2237 9 598 4913 203541624 = true := by decide +kernel
    have check17_x8x4x2 : check 27 17 30030 4003 1 2910 4913 203541624 = true := by decide +kernel
    have check17_x8x4x3 : check 27 17 30030 5770 10 309 4913 203541624 = true := by decide +kernel
    have check17_x8x4x4 : check 27 17 30030 7536 2 2621 4913 203541624 = true := by decide +kernel
    have check17_x8x4x5 : check 27 17 30030 9303 11 20 4913 203541624 = true := by decide +kernel
    have check17_x8x4x6 : check 27 17 30030 11069 3 2332 4913 203541624 = true := by decide +kernel
    have check17_x8x4x8 : check 27 17 30030 14602 4 2043 4913 203541624 = true := by decide +kernel
    have check17_x8x4x10 : check 27 17 30030 18135 5 1754 4913 203541624 = true := by decide +kernel
    have check17_x8x4x12 : check 27 17 30030 21668 6 1465 4913 203541624 = true := by decide +kernel
    have check17_x8x4x14 : check 27 17 30030 25201 7 1176 4913 203541624 = true := by decide +kernel
    have check17_x8x4x16 : check 27 17 30030 28734 8 887 4913 203541624 = true := by decide +kernel
    have check17_x8x4 : check 28 17 30030 8001 11 20 289 3460207612 = true := by
      apply check_step 27 17 30030 8001 11 20 289 3460207612 (by norm_num) (by norm_num)
      intro t ht hb
      interval_cases t
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x4x0
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x4x1
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x4x2
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x4x3
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x4x4
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x4x5
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x4x6
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x4x8
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x4x10
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x4x12
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x4x14
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x4x16
    have check17_x8x5 : check 28 17 30030 9767 3 156 289 3460207612 = true := by decide +kernel
    have check17_x8x6x0 : check 27 17 30030 678 4 2315 4913 203541624 = true := by decide +kernel
    have check17_x8x6x2 : check 27 17 30030 4211 5 2026 4913 203541624 = true := by decide +kernel
    have check17_x8x6x4 : check 27 17 30030 7744 6 1737 4913 203541624 = true := by decide +kernel
    have check17_x8x6x6 : check 27 17 30030 11277 7 1448 4913 203541624 = true := by decide +kernel
    have check17_x8x6x8 : check 27 17 30030 14810 8 1159 4913 203541624 = true := by decide +kernel
    have check17_x8x6x9 : check 27 17 30030 16576 0 3471 4913 203541624 = true := by decide +kernel
    have check17_x8x6x10 : check 27 17 30030 18343 9 870 4913 203541624 = true := by decide +kernel
    have check17_x8x6x11 : check 27 17 30030 20109 1 3182 4913 203541624 = true := by decide +kernel
    have check17_x8x6x12 : check 27 17 30030 21876 10 581 4913 203541624 = true := by decide +kernel
    have check17_x8x6x13 : check 27 17 30030 23642 2 2893 4913 203541624 = true := by decide +kernel
    have check17_x8x6x14 : check 27 17 30030 25409 11 292 4913 203541624 = true := by decide +kernel
    have check17_x8x6x15 : check 27 17 30030 27175 3 2604 4913 203541624 = true := by decide +kernel
    have check17_x8x6x16 : check 27 17 30030 28942 12 3 4913 203541624 = true := by decide +kernel
    have check17_x8x6 : check 28 17 30030 11534 12 3 289 3460207612 = true := by
      apply check_step 27 17 30030 11534 12 3 289 3460207612 (by norm_num) (by norm_num)
      intro t ht hb
      interval_cases t
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x6x0
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x6x2
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x6x4
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x6x6
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x6x8
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x6x9
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x6x10
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x6x11
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x6x12
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x6x13
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x6x14
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x6x15
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x6x16
    have check17_x8x7 : check 28 17 30030 13300 4 139 289 3460207612 = true := by decide +kernel
    have check17_x8x9 : check 28 17 30030 16833 5 122 289 3460207612 = true := by decide +kernel
    have check17_x8x11 : check 28 17 30030 20366 6 105 289 3460207612 = true := by decide +kernel
    have check17_x8x13 : check 28 17 30030 23899 7 88 289 3460207612 = true := by decide +kernel
    have check17_x8x15 : check 28 17 30030 27432 8 71 289 3460207612 = true := by decide +kernel
    have check17_x8x16 : check 28 17 30030 29198 0 207 289 3460207612 = true := by decide +kernel
    have check17_x8 : check 29 17 30030 15898 12 3 17 58823529411 = true := by
      apply check_step 28 17 30030 15898 12 3 17 58823529411 (by norm_num) (by norm_num)
      intro t ht hb
      interval_cases t
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x0
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x1
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x2
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x3
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x4
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x5
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x6
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x7
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x9
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x11
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x13
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x15
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8x16
    have check17_x9 : check 29 17 30030 17664 4 11 17 58823529411 = true := by decide +kernel
    have check17_x10x0x0 : check 27 17 30030 67 9 1158 4913 203541624 = true := by decide +kernel
    have check17_x10x0x1 : check 27 17 30030 1833 1 3470 4913 203541624 = true := by decide +kernel
    have check17_x10x0x2 : check 27 17 30030 3600 10 869 4913 203541624 = true := by decide +kernel
    have check17_x10x0x3 : check 27 17 30030 5366 2 3181 4913 203541624 = true := by decide +kernel
    have check17_x10x0x4 : check 27 17 30030 7133 11 580 4913 203541624 = true := by decide +kernel
    have check17_x10x0x5 : check 27 17 30030 8899 3 2892 4913 203541624 = true := by decide +kernel
    have check17_x10x0x6 : check 27 17 30030 10666 12 291 4913 203541624 = true := by decide +kernel
    have check17_x10x0x7 : check 27 17 30030 12432 4 2603 4913 203541624 = true := by decide +kernel
    have check17_x10x0x8 : check 27 17 30030 14199 13 2 4913 203541624 = true := by decide +kernel
    have check17_x10x0x9 : check 27 17 30030 15965 5 2314 4913 203541624 = true := by decide +kernel
    have check17_x10x0x11 : check 27 17 30030 19498 6 2025 4913 203541624 = true := by decide +kernel
    have check17_x10x0x13 : check 27 17 30030 23031 7 1736 4913 203541624 = true := by decide +kernel
    have check17_x10x0x15 : check 27 17 30030 26564 8 1447 4913 203541624 = true := by decide +kernel
    have check17_x10x0x16 : check 27 17 30030 28330 0 3759 4913 203541624 = true := by decide +kernel
    have check17_x10x0 : check 28 17 30030 1143 13 2 289 3460207612 = true := by
      apply check_step 27 17 30030 1143 13 2 289 3460207612 (by norm_num) (by norm_num)
      intro t ht hb
      interval_cases t
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x10x0x0
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x10x0x1
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x10x0x2
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x10x0x3
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x10x0x4
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x10x0x5
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x10x0x6
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x10x0x7
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x10x0x8
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x10x0x9
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x10x0x11
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x10x0x13
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x10x0x15
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x10x0x16
    have check17_x10x1 : check 28 17 30030 2909 5 138 289 3460207612 = true := by decide +kernel
    have check17_x10x3 : check 28 17 30030 6442 6 121 289 3460207612 = true := by decide +kernel
    have check17_x10x5 : check 28 17 30030 9975 7 104 289 3460207612 = true := by decide +kernel
    have check17_x10x7 : check 28 17 30030 13508 8 87 289 3460207612 = true := by decide +kernel
    have check17_x10x8 : check 28 17 30030 15274 0 223 289 3460207612 = true := by decide +kernel
    have check17_x10x9 : check 28 17 30030 17041 9 70 289 3460207612 = true := by decide +kernel
    have check17_x10x10 : check 28 17 30030 18807 1 206 289 3460207612 = true := by decide +kernel
    have check17_x10x11x0 : check 27 17 30030 1210 6 1209 4913 203541624 = true := by decide +kernel
    have check17_x10x11x2 : check 27 17 30030 4743 7 920 4913 203541624 = true := by decide +kernel
    have check17_x10x11x4 : check 27 17 30030 8276 8 631 4913 203541624 = true := by decide +kernel
    have check17_x10x11x5 : check 27 17 30030 10042 0 2943 4913 203541624 = true := by decide +kernel
    have check17_x10x11x6 : check 27 17 30030 11809 9 342 4913 203541624 = true := by decide +kernel
    have check17_x10x11x7 : check 27 17 30030 13575 1 2654 4913 203541624 = true := by decide +kernel
    have check17_x10x11x8 : check 27 17 30030 15342 10 53 4913 203541624 = true := by decide +kernel
    have check17_x10x11x9 : check 27 17 30030 17108 2 2365 4913 203541624 = true := by decide +kernel
    have check17_x10x11x11 : check 27 17 30030 20641 3 2076 4913 203541624 = true := by decide +kernel
    have check17_x10x11x13 : check 27 17 30030 24174 4 1787 4913 203541624 = true := by decide +kernel
    have check17_x10x11x15 : check 27 17 30030 27707 5 1498 4913 203541624 = true := by decide +kernel
    have check17_x10x11 : check 28 17 30030 20574 10 53 289 3460207612 = true := by
      apply check_step 27 17 30030 20574 10 53 289 3460207612 (by norm_num) (by norm_num)
      intro t ht hb
      interval_cases t
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x10x11x0
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x10x11x2
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x10x11x4
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x10x11x5
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x10x11x6
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x10x11x7
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x10x11x8
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x10x11x9
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x10x11x11
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x10x11x13
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x10x11x15
      · norm_num at hb
    have check17_x10x12 : check 28 17 30030 22340 2 189 289 3460207612 = true := by decide +kernel
    have check17_x10x13x0 : check 27 17 30030 1418 10 325 4913 203541624 = true := by decide +kernel
    have check17_x10x13x1 : check 27 17 30030 3184 2 2637 4913 203541624 = true := by decide +kernel
    have check17_x10x13x2 : check 27 17 30030 4951 11 36 4913 203541624 = true := by decide +kernel
    have check17_x10x13x3 : check 27 17 30030 6717 3 2348 4913 203541624 = true := by decide +kernel
    have check17_x10x13x5 : check 27 17 30030 10250 4 2059 4913 203541624 = true := by decide +kernel
    have check17_x10x13x7 : check 27 17 30030 13783 5 1770 4913 203541624 = true := by decide +kernel
    have check17_x10x13x9 : check 27 17 30030 17316 6 1481 4913 203541624 = true := by decide +kernel
    have check17_x10x13x11 : check 27 17 30030 20849 7 1192 4913 203541624 = true := by decide +kernel
    have check17_x10x13x13 : check 27 17 30030 24382 8 903 4913 203541624 = true := by decide +kernel
    have check17_x10x13x14 : check 27 17 30030 26148 0 3215 4913 203541624 = true := by decide +kernel
    have check17_x10x13x15 : check 27 17 30030 27915 9 614 4913 203541624 = true := by decide +kernel
    have check17_x10x13x16 : check 27 17 30030 29681 1 2926 4913 203541624 = true := by decide +kernel
    have check17_x10x13 : check 28 17 30030 24107 11 36 289 3460207612 = true := by
      apply check_step 27 17 30030 24107 11 36 289 3460207612 (by norm_num) (by norm_num)
      intro t ht hb
      interval_cases t
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x10x13x0
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x10x13x1
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x10x13x2
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x10x13x3
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x10x13x5
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x10x13x7
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x10x13x9
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x10x13x11
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x10x13x13
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x10x13x14
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x10x13x15
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x10x13x16
    have check17_x10x14 : check 28 17 30030 25873 3 172 289 3460207612 = true := by decide +kernel
    have check17_x10x15x1 : check 27 17 30030 3392 6 1753 4913 203541624 = true := by decide +kernel
    have check17_x10x15x3 : check 27 17 30030 6925 7 1464 4913 203541624 = true := by decide +kernel
    have check17_x10x15x5 : check 27 17 30030 10458 8 1175 4913 203541624 = true := by decide +kernel
    have check17_x10x15x6 : check 27 17 30030 12224 0 3487 4913 203541624 = true := by decide +kernel
    have check17_x10x15x7 : check 27 17 30030 13991 9 886 4913 203541624 = true := by decide +kernel
    have check17_x10x15x8 : check 27 17 30030 15757 1 3198 4913 203541624 = true := by decide +kernel
    have check17_x10x15x9 : check 27 17 30030 17524 10 597 4913 203541624 = true := by decide +kernel
    have check17_x10x15x10 : check 27 17 30030 19290 2 2909 4913 203541624 = true := by decide +kernel
    have check17_x10x15x11 : check 27 17 30030 21057 11 308 4913 203541624 = true := by decide +kernel
    have check17_x10x15x12 : check 27 17 30030 22823 3 2620 4913 203541624 = true := by decide +kernel
    have check17_x10x15x13 : check 27 17 30030 24590 12 19 4913 203541624 = true := by decide +kernel
    have check17_x10x15x14 : check 27 17 30030 26356 4 2331 4913 203541624 = true := by decide +kernel
    have check17_x10x15x16 : check 27 17 30030 29889 5 2042 4913 203541624 = true := by decide +kernel
    have check17_x10x15 : check 28 17 30030 27640 12 19 289 3460207612 = true := by
      apply check_step 27 17 30030 27640 12 19 289 3460207612 (by norm_num) (by norm_num)
      intro t ht hb
      interval_cases t
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x10x15x1
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x10x15x3
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x10x15x5
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x10x15x6
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x10x15x7
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x10x15x8
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x10x15x9
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x10x15x10
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x10x15x11
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x10x15x12
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x10x15x13
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x10x15x14
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x10x15x16
    have check17_x10x16 : check 28 17 30030 29406 4 155 289 3460207612 = true := by decide +kernel
    have check17_x10 : check 29 17 30030 19431 13 2 17 58823529411 = true := by
      apply check_step 28 17 30030 19431 13 2 17 58823529411 (by norm_num) (by norm_num)
      intro t ht hb
      interval_cases t
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x10x0
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x10x1
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x10x3
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x10x5
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x10x7
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x10x8
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x10x9
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x10x10
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x10x11
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x10x12
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x10x13
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x10x14
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x10x15
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x10x16
    have check17_x11 : check 29 17 30030 21197 5 10 17 58823529411 = true := by decide +kernel
    have check17_x12x0 : check 28 17 30030 1350 0 239 289 3460207612 = true := by decide +kernel
    have check17_x12x1 : check 28 17 30030 3117 9 86 289 3460207612 = true := by decide +kernel
    have check17_x12x2 : check 28 17 30030 4883 1 222 289 3460207612 = true := by decide +kernel
    have check17_x12x3x0 : check 27 17 30030 391 7 936 4913 203541624 = true := by decide +kernel
    have check17_x12x3x2 : check 27 17 30030 3924 8 647 4913 203541624 = true := by decide +kernel
    have check17_x12x3x3 : check 27 17 30030 5690 0 2959 4913 203541624 = true := by decide +kernel
    have check17_x12x3x4 : check 27 17 30030 7457 9 358 4913 203541624 = true := by decide +kernel
    have check17_x12x3x5 : check 27 17 30030 9223 1 2670 4913 203541624 = true := by decide +kernel
    have check17_x12x3x6 : check 27 17 30030 10990 10 69 4913 203541624 = true := by decide +kernel
    have check17_x12x3x7 : check 27 17 30030 12756 2 2381 4913 203541624 = true := by decide +kernel
    have check17_x12x3x9 : check 27 17 30030 16289 3 2092 4913 203541624 = true := by decide +kernel
    have check17_x12x3x11 : check 27 17 30030 19822 4 1803 4913 203541624 = true := by decide +kernel
    have check17_x12x3x13 : check 27 17 30030 23355 5 1514 4913 203541624 = true := by decide +kernel
    have check17_x12x3x15 : check 27 17 30030 26888 6 1225 4913 203541624 = true := by decide +kernel
    have check17_x12x3 : check 28 17 30030 6650 10 69 289 3460207612 = true := by
      apply check_step 27 17 30030 6650 10 69 289 3460207612 (by norm_num) (by norm_num)
      intro t ht hb
      interval_cases t
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x3x0
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x3x2
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x3x3
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x3x4
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x3x5
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x3x6
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x3x7
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x3x9
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x3x11
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x3x13
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x3x15
      · norm_num at hb
    have check17_x12x4 : check 28 17 30030 8416 2 205 289 3460207612 = true := by decide +kernel
    have check17_x12x5x0 : check 27 17 30030 599 11 52 4913 203541624 = true := by decide +kernel
    have check17_x12x5x1 : check 27 17 30030 2365 3 2364 4913 203541624 = true := by decide +kernel
    have check17_x12x5x3 : check 27 17 30030 5898 4 2075 4913 203541624 = true := by decide +kernel
    have check17_x12x5x5 : check 27 17 30030 9431 5 1786 4913 203541624 = true := by decide +kernel
    have check17_x12x5x7 : check 27 17 30030 12964 6 1497 4913 203541624 = true := by decide +kernel
    have check17_x12x5x9 : check 27 17 30030 16497 7 1208 4913 203541624 = true := by decide +kernel
    have check17_x12x5x11 : check 27 17 30030 20030 8 919 4913 203541624 = true := by decide +kernel
    have check17_x12x5x12 : check 27 17 30030 21796 0 3231 4913 203541624 = true := by decide +kernel
    have check17_x12x5x13 : check 27 17 30030 23563 9 630 4913 203541624 = true := by decide +kernel
    have check17_x12x5x14 : check 27 17 30030 25329 1 2942 4913 203541624 = true := by decide +kernel
    have check17_x12x5x15 : check 27 17 30030 27096 10 341 4913 203541624 = true := by decide +kernel
    have check17_x12x5x16 : check 27 17 30030 28862 2 2653 4913 203541624 = true := by decide +kernel
    have check17_x12x5 : check 28 17 30030 10183 11 52 289 3460207612 = true := by
      apply check_step 27 17 30030 10183 11 52 289 3460207612 (by norm_num) (by norm_num)
      intro t ht hb
      interval_cases t
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x5x0
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x5x1
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x5x3
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x5x5
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x5x7
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x5x9
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x5x11
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x5x12
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x5x13
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x5x14
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x5x15
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x5x16
    have check17_x12x6 : check 28 17 30030 11949 3 188 289 3460207612 = true := by decide +kernel
    have check17_x12x7x1 : check 27 17 30030 2573 7 1480 4913 203541624 = true := by decide +kernel
    have check17_x12x7x3 : check 27 17 30030 6106 8 1191 4913 203541624 = true := by decide +kernel
    have check17_x12x7x4 : check 27 17 30030 7872 0 3503 4913 203541624 = true := by decide +kernel
    have check17_x12x7x5 : check 27 17 30030 9639 9 902 4913 203541624 = true := by decide +kernel
    have check17_x12x7x6 : check 27 17 30030 11405 1 3214 4913 203541624 = true := by decide +kernel
    have check17_x12x7x7 : check 27 17 30030 13172 10 613 4913 203541624 = true := by decide +kernel
    have check17_x12x7x8 : check 27 17 30030 14938 2 2925 4913 203541624 = true := by decide +kernel
    have check17_x12x7x9 : check 27 17 30030 16705 11 324 4913 203541624 = true := by decide +kernel
    have check17_x12x7x10 : check 27 17 30030 18471 3 2636 4913 203541624 = true := by decide +kernel
    have check17_x12x7x11 : check 27 17 30030 20238 12 35 4913 203541624 = true := by decide +kernel
    have check17_x12x7x12 : check 27 17 30030 22004 4 2347 4913 203541624 = true := by decide +kernel
    have check17_x12x7x14 : check 27 17 30030 25537 5 2058 4913 203541624 = true := by decide +kernel
    have check17_x12x7x16 : check 27 17 30030 29070 6 1769 4913 203541624 = true := by decide +kernel
    have check17_x12x7 : check 28 17 30030 13716 12 35 289 3460207612 = true := by
      apply check_step 27 17 30030 13716 12 35 289 3460207612 (by norm_num) (by norm_num)
      intro t ht hb
      interval_cases t
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x7x1
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x7x3
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x7x4
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x7x5
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x7x6
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x7x7
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x7x8
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x7x9
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x7x10
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x7x11
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x7x12
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x7x14
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x7x16
    have check17_x12x8 : check 28 17 30030 15482 4 171 289 3460207612 = true := by decide +kernel
    have check17_x12x9x0 : check 27 17 30030 1014 2 3197 4913 203541624 = true := by decide +kernel
    have check17_x12x9x1 : check 27 17 30030 2781 11 596 4913 203541624 = true := by decide +kernel
    have check17_x12x9x2 : check 27 17 30030 4547 3 2908 4913 203541624 = true := by decide +kernel
    have check17_x12x9x3 : check 27 17 30030 6314 12 307 4913 203541624 = true := by decide +kernel
    have check17_x12x9x4 : check 27 17 30030 8080 4 2619 4913 203541624 = true := by decide +kernel
    have check17_x12x9x5 : check 27 17 30030 9847 13 18 4913 203541624 = true := by decide +kernel
    have check17_x12x9x6 : check 27 17 30030 11613 5 2330 4913 203541624 = true := by decide +kernel
    have check17_x12x9x8 : check 27 17 30030 15146 6 2041 4913 203541624 = true := by decide +kernel
    have check17_x12x9x10 : check 27 17 30030 18679 7 1752 4913 203541624 = true := by decide +kernel
    have check17_x12x9x12 : check 27 17 30030 22212 8 1463 4913 203541624 = true := by decide +kernel
    have check17_x12x9x13 : check 27 17 30030 23978 0 3775 4913 203541624 = true := by decide +kernel
    have check17_x12x9x14 : check 27 17 30030 25745 9 1174 4913 203541624 = true := by decide +kernel
    have check17_x12x9x15 : check 27 17 30030 27511 1 3486 4913 203541624 = true := by decide +kernel
    have check17_x12x9x16 : check 27 17 30030 29278 10 885 4913 203541624 = true := by decide +kernel
    have check17_x12x9 : check 28 17 30030 17249 13 18 289 3460207612 = true := by
      apply check_step 27 17 30030 17249 13 18 289 3460207612 (by norm_num) (by norm_num)
      intro t ht hb
      interval_cases t
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x9x0
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x9x1
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x9x2
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x9x3
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x9x4
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x9x5
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x9x6
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x9x8
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x9x10
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x9x12
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x9x13
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x9x14
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x9x15
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x9x16
    have check17_x12x10 : check 28 17 30030 19015 5 154 289 3460207612 = true := by decide +kernel
    have check17_x12x11x0 : check 27 17 30030 1222 6 2313 4913 203541624 = true := by decide +kernel
    have check17_x12x11x2 : check 27 17 30030 4755 7 2024 4913 203541624 = true := by decide +kernel
    have check17_x12x11x4 : check 27 17 30030 8288 8 1735 4913 203541624 = true := by decide +kernel
    have check17_x12x11x5 : check 27 17 30030 10054 0 4047 4913 203541624 = true := by decide +kernel
    have check17_x12x11x6 : check 27 17 30030 11821 9 1446 4913 203541624 = true := by decide +kernel
    have check17_x12x11x7 : check 27 17 30030 13587 1 3758 4913 203541624 = true := by decide +kernel
    have check17_x12x11x8 : check 27 17 30030 15354 10 1157 4913 203541624 = true := by decide +kernel
    have check17_x12x11x9 : check 27 17 30030 17120 2 3469 4913 203541624 = true := by decide +kernel
    have check17_x12x11x10 : check 27 17 30030 18887 11 868 4913 203541624 = true := by decide +kernel
    have check17_x12x11x11 : check 27 17 30030 20653 3 3180 4913 203541624 = true := by decide +kernel
    have check17_x12x11x12 : check 27 17 30030 22420 12 579 4913 203541624 = true := by decide +kernel
    have check17_x12x11x13 : check 27 17 30030 24186 4 2891 4913 203541624 = true := by decide +kernel
    have check17_x12x11x14 : check 27 17 30030 25953 13 290 4913 203541624 = true := by decide +kernel
    have check17_x12x11x15 : check 27 17 30030 27719 5 2602 4913 203541624 = true := by decide +kernel
    have check17_x12x11x16x0 : check 26 17 30030 1734 6 39305 83521 11973036 = true := by decide +kernel
    have check17_x12x11x16x2 : check 26 17 30030 5267 7 34392 83521 11973036 = true := by decide +kernel
    have check17_x12x11x16x4 : check 26 17 30030 8800 8 29479 83521 11973036 = true := by decide +kernel
    have check17_x12x11x16x5 : check 26 17 30030 10566 0 68783 83521 11973036 = true := by decide +kernel
    have check17_x12x11x16x6 : check 26 17 30030 12333 9 24566 83521 11973036 = true := by decide +kernel
    have check17_x12x11x16x7 : check 26 17 30030 14099 1 63870 83521 11973036 = true := by decide +kernel
    have check17_x12x11x16x8 : check 26 17 30030 15866 10 19653 83521 11973036 = true := by decide +kernel
    have check17_x12x11x16x9 : check 26 17 30030 17632 2 58957 83521 11973036 = true := by decide +kernel
    have check17_x12x11x16x10 : check 26 17 30030 19399 11 14740 83521 11973036 = true := by decide +kernel
    have check17_x12x11x16x11 : check 26 17 30030 21165 3 54044 83521 11973036 = true := by decide +kernel
    have check17_x12x11x16x12 : check 26 17 30030 22932 12 9827 83521 11973036 = true := by decide +kernel
    have check17_x12x11x16x13 : check 26 17 30030 24698 4 49131 83521 11973036 = true := by decide +kernel
    have check17_x12x11x16x14 : check 26 17 30030 26465 13 4914 83521 11973036 = true := by decide +kernel
    have check17_x12x11x16x15 : check 26 17 30030 28231 5 44218 83521 11973036 = true := by decide +kernel
    have check17_x12x11x16x16 : check 26 17 30030 29998 14 1 83521 11973036 = true := by decide +kernel
    have check17_x12x11x16 : check 27 17 30030 29486 14 1 4913 203541624 = true := by
      apply check_step 26 17 30030 29486 14 1 4913 203541624 (by norm_num) (by norm_num)
      intro t ht hb
      interval_cases t
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x11x16x0
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x11x16x2
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x11x16x4
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x11x16x5
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x11x16x6
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x11x16x7
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x11x16x8
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x11x16x9
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x11x16x10
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x11x16x11
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x11x16x12
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x11x16x13
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x11x16x14
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x11x16x15
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x11x16x16
    have check17_x12x11 : check 28 17 30030 20782 14 1 289 3460207612 = true := by
      apply check_step 27 17 30030 20782 14 1 289 3460207612 (by norm_num) (by norm_num)
      intro t ht hb
      interval_cases t
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x11x0
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x11x2
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x11x4
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x11x5
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x11x6
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x11x7
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x11x8
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x11x9
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x11x10
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x11x11
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x11x12
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x11x13
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x11x14
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x11x15
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x11x16
    have check17_x12x12 : check 28 17 30030 22548 6 137 289 3460207612 = true := by decide +kernel
    have check17_x12x14 : check 28 17 30030 26081 7 120 289 3460207612 = true := by decide +kernel
    have check17_x12x16 : check 28 17 30030 29614 8 103 289 3460207612 = true := by decide +kernel
    have check17_x12 : check 29 17 30030 22964 14 1 17 58823529411 = true := by
      apply check_step 28 17 30030 22964 14 1 17 58823529411 (by norm_num) (by norm_num)
      intro t ht hb
      interval_cases t
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x0
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x1
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x2
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x3
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x4
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x5
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x6
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x7
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x8
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x9
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x10
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x11
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x12
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x14
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12x16
    have check17_x13 : check 29 17 30030 24730 6 9 17 58823529411 = true := by decide +kernel
    have check17_x14x0 : check 28 17 30030 1558 4 187 289 3460207612 = true := by decide +kernel
    have check17_x14x1x0 : check 27 17 30030 195 3 2924 4913 203541624 = true := by decide +kernel
    have check17_x14x1x1 : check 27 17 30030 1962 12 323 4913 203541624 = true := by decide +kernel
    have check17_x14x1x2 : check 27 17 30030 3728 4 2635 4913 203541624 = true := by decide +kernel
    have check17_x14x1x3 : check 27 17 30030 5495 13 34 4913 203541624 = true := by decide +kernel
    have check17_x14x1x4 : check 27 17 30030 7261 5 2346 4913 203541624 = true := by decide +kernel
    have check17_x14x1x6 : check 27 17 30030 10794 6 2057 4913 203541624 = true := by decide +kernel
    have check17_x14x1x8 : check 27 17 30030 14327 7 1768 4913 203541624 = true := by decide +kernel
    have check17_x14x1x10 : check 27 17 30030 17860 8 1479 4913 203541624 = true := by decide +kernel
    have check17_x14x1x11 : check 27 17 30030 19626 0 3791 4913 203541624 = true := by decide +kernel
    have check17_x14x1x12 : check 27 17 30030 21393 9 1190 4913 203541624 = true := by decide +kernel
    have check17_x14x1x13 : check 27 17 30030 23159 1 3502 4913 203541624 = true := by decide +kernel
    have check17_x14x1x14 : check 27 17 30030 24926 10 901 4913 203541624 = true := by decide +kernel
    have check17_x14x1x15 : check 27 17 30030 26692 2 3213 4913 203541624 = true := by decide +kernel
    have check17_x14x1x16 : check 27 17 30030 28459 11 612 4913 203541624 = true := by decide +kernel
    have check17_x14x1 : check 28 17 30030 3325 13 34 289 3460207612 = true := by
      apply check_step 27 17 30030 3325 13 34 289 3460207612 (by norm_num) (by norm_num)
      intro t ht hb
      interval_cases t
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x1x0
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x1x1
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x1x2
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x1x3
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x1x4
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x1x6
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x1x8
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x1x10
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x1x11
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x1x12
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x1x13
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x1x14
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x1x15
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x1x16
    have check17_x14x2 : check 28 17 30030 5091 5 170 289 3460207612 = true := by decide +kernel
    have check17_x14x3x0 : check 27 17 30030 403 7 2040 4913 203541624 = true := by decide +kernel
    have check17_x14x3x2 : check 27 17 30030 3936 8 1751 4913 203541624 = true := by decide +kernel
    have check17_x14x3x3 : check 27 17 30030 5702 0 4063 4913 203541624 = true := by decide +kernel
    have check17_x14x3x4 : check 27 17 30030 7469 9 1462 4913 203541624 = true := by decide +kernel
    have check17_x14x3x5 : check 27 17 30030 9235 1 3774 4913 203541624 = true := by decide +kernel
    have check17_x14x3x6 : check 27 17 30030 11002 10 1173 4913 203541624 = true := by decide +kernel
    have check17_x14x3x7 : check 27 17 30030 12768 2 3485 4913 203541624 = true := by decide +kernel
    have check17_x14x3x8 : check 27 17 30030 14535 11 884 4913 203541624 = true := by decide +kernel
    have check17_x14x3x9 : check 27 17 30030 16301 3 3196 4913 203541624 = true := by decide +kernel
    have check17_x14x3x10 : check 27 17 30030 18068 12 595 4913 203541624 = true := by decide +kernel
    have check17_x14x3x11 : check 27 17 30030 19834 4 2907 4913 203541624 = true := by decide +kernel
    have check17_x14x3x12 : check 27 17 30030 21601 13 306 4913 203541624 = true := by decide +kernel
    have check17_x14x3x13 : check 27 17 30030 23367 5 2618 4913 203541624 = true := by decide +kernel
    have check17_x14x3x14x0 : check 26 17 30030 1478 6 39321 83521 11973036 = true := by decide +kernel
    have check17_x14x3x14x2 : check 26 17 30030 5011 7 34408 83521 11973036 = true := by decide +kernel
    have check17_x14x3x14x4 : check 26 17 30030 8544 8 29495 83521 11973036 = true := by decide +kernel
    have check17_x14x3x14x5 : check 26 17 30030 10310 0 68799 83521 11973036 = true := by decide +kernel
    have check17_x14x3x14x6 : check 26 17 30030 12077 9 24582 83521 11973036 = true := by decide +kernel
    have check17_x14x3x14x7 : check 26 17 30030 13843 1 63886 83521 11973036 = true := by decide +kernel
    have check17_x14x3x14x8 : check 26 17 30030 15610 10 19669 83521 11973036 = true := by decide +kernel
    have check17_x14x3x14x9 : check 26 17 30030 17376 2 58973 83521 11973036 = true := by decide +kernel
    have check17_x14x3x14x10 : check 26 17 30030 19143 11 14756 83521 11973036 = true := by decide +kernel
    have check17_x14x3x14x11 : check 26 17 30030 20909 3 54060 83521 11973036 = true := by decide +kernel
    have check17_x14x3x14x12 : check 26 17 30030 22676 12 9843 83521 11973036 = true := by decide +kernel
    have check17_x14x3x14x13 : check 26 17 30030 24442 4 49147 83521 11973036 = true := by decide +kernel
    have check17_x14x3x14x14 : check 26 17 30030 26209 13 4930 83521 11973036 = true := by decide +kernel
    have check17_x14x3x14x15 : check 26 17 30030 27975 5 44234 83521 11973036 = true := by decide +kernel
    have check17_x14x3x14x16 : check 26 17 30030 29742 14 17 83521 11973036 = true := by decide +kernel
    have check17_x14x3x14 : check 27 17 30030 25134 14 17 4913 203541624 = true := by
      apply check_step 26 17 30030 25134 14 17 4913 203541624 (by norm_num) (by norm_num)
      intro t ht hb
      interval_cases t
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x3x14x0
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x3x14x2
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x3x14x4
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x3x14x5
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x3x14x6
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x3x14x7
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x3x14x8
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x3x14x9
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x3x14x10
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x3x14x11
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x3x14x12
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x3x14x13
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x3x14x14
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x3x14x15
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x3x14x16
    have check17_x14x3x15 : check 27 17 30030 26900 6 2329 4913 203541624 = true := by decide +kernel
    have check17_x14x3 : check 28 17 30030 6858 14 17 289 3460207612 = true := by
      apply check_step 27 17 30030 6858 14 17 289 3460207612 (by norm_num) (by norm_num)
      intro t ht hb
      interval_cases t
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x3x0
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x3x2
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x3x3
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x3x4
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x3x5
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x3x6
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x3x7
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x3x8
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x3x9
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x3x10
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x3x11
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x3x12
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x3x13
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x3x14
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x3x15
      · norm_num at hb
    have check17_x14x4 : check 28 17 30030 8624 6 153 289 3460207612 = true := by decide +kernel
    have check17_x14x5x0 : check 27 17 30030 611 11 1156 4913 203541624 = true := by decide +kernel
    have check17_x14x5x1 : check 27 17 30030 2377 3 3468 4913 203541624 = true := by decide +kernel
    have check17_x14x5x2 : check 27 17 30030 4144 12 867 4913 203541624 = true := by decide +kernel
    have check17_x14x5x3 : check 27 17 30030 5910 4 3179 4913 203541624 = true := by decide +kernel
    have check17_x14x5x4 : check 27 17 30030 7677 13 578 4913 203541624 = true := by decide +kernel
    have check17_x14x5x5 : check 27 17 30030 9443 5 2890 4913 203541624 = true := by decide +kernel
    have check17_x14x5x6x0 : check 26 17 30030 659 7 34680 83521 11973036 = true := by decide +kernel
    have check17_x14x5x6x2 : check 26 17 30030 4192 8 29767 83521 11973036 = true := by decide +kernel
    have check17_x14x5x6x3 : check 26 17 30030 5958 0 69071 83521 11973036 = true := by decide +kernel
    have check17_x14x5x6x4 : check 26 17 30030 7725 9 24854 83521 11973036 = true := by decide +kernel
    have check17_x14x5x6x5 : check 26 17 30030 9491 1 64158 83521 11973036 = true := by decide +kernel
    have check17_x14x5x6x6 : check 26 17 30030 11258 10 19941 83521 11973036 = true := by decide +kernel
    have check17_x14x5x6x7 : check 26 17 30030 13024 2 59245 83521 11973036 = true := by decide +kernel
    have check17_x14x5x6x8 : check 26 17 30030 14791 11 15028 83521 11973036 = true := by decide +kernel
    have check17_x14x5x6x9 : check 26 17 30030 16557 3 54332 83521 11973036 = true := by decide +kernel
    have check17_x14x5x6x10 : check 26 17 30030 18324 12 10115 83521 11973036 = true := by decide +kernel
    have check17_x14x5x6x11 : check 26 17 30030 20090 4 49419 83521 11973036 = true := by decide +kernel
    have check17_x14x5x6x12 : check 26 17 30030 21857 13 5202 83521 11973036 = true := by decide +kernel
    have check17_x14x5x6x13 : check 26 17 30030 23623 5 44506 83521 11973036 = true := by decide +kernel
    have check17_x14x5x6x14 : check 26 17 30030 25390 14 289 83521 11973036 = true := by decide +kernel
    have check17_x14x5x6x15 : check 26 17 30030 27156 6 39593 83521 11973036 = true := by decide +kernel
    have check17_x14x5x6 : check 27 17 30030 11210 14 289 4913 203541624 = true := by
      apply check_step 26 17 30030 11210 14 289 4913 203541624 (by norm_num) (by norm_num)
      intro t ht hb
      interval_cases t
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x5x6x0
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x5x6x2
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x5x6x3
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x5x6x4
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x5x6x5
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x5x6x6
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x5x6x7
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x5x6x8
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x5x6x9
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x5x6x10
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x5x6x11
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x5x6x12
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x5x6x13
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x5x6x14
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x5x6x15
      · norm_num at hb
    have check17_x14x5x7 : check 27 17 30030 12976 6 2601 4913 203541624 = true := by decide +kernel
    have check17_x14x5x8x0 : check 26 17 30030 867 11 19652 83521 11973036 = true := by decide +kernel
    have check17_x14x5x8x1 : check 26 17 30030 2633 3 58956 83521 11973036 = true := by decide +kernel
    have check17_x14x5x8x2 : check 26 17 30030 4400 12 14739 83521 11973036 = true := by decide +kernel
    have check17_x14x5x8x3 : check 26 17 30030 6166 4 54043 83521 11973036 = true := by decide +kernel
    have check17_x14x5x8x4 : check 26 17 30030 7933 13 9826 83521 11973036 = true := by decide +kernel
    have check17_x14x5x8x5 : check 26 17 30030 9699 5 49130 83521 11973036 = true := by decide +kernel
    have check17_x14x5x8x6 : check 26 17 30030 11466 14 4913 83521 11973036 = true := by decide +kernel
    have check17_x14x5x8x7 : check 26 17 30030 13232 6 44217 83521 11973036 = true := by decide +kernel
    have check17_x14x5x8x8 : check 26 17 30030 14999 15 0 83521 11973036 = true := by decide +kernel
    have check17_x14x5x8x9 : check 26 17 30030 16765 7 39304 83521 11973036 = true := by decide +kernel
    have check17_x14x5x8x11 : check 26 17 30030 20298 8 34391 83521 11973036 = true := by decide +kernel
    have check17_x14x5x8x12 : check 26 17 30030 22064 0 73695 83521 11973036 = true := by decide +kernel
    have check17_x14x5x8x13 : check 26 17 30030 23831 9 29478 83521 11973036 = true := by decide +kernel
    have check17_x14x5x8x14 : check 26 17 30030 25597 1 68782 83521 11973036 = true := by decide +kernel
    have check17_x14x5x8x15 : check 26 17 30030 27364 10 24565 83521 11973036 = true := by decide +kernel
    have check17_x14x5x8x16 : check 26 17 30030 29130 2 63869 83521 11973036 = true := by decide +kernel
    have check17_x14x5x8 : check 27 17 30030 14743 15 0 4913 203541624 = true := by
      apply check_step 26 17 30030 14743 15 0 4913 203541624 (by norm_num) (by norm_num)
      intro t ht hb
      interval_cases t
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x5x8x0
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x5x8x1
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x5x8x2
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x5x8x3
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x5x8x4
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x5x8x5
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x5x8x6
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x5x8x7
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x5x8x8
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x5x8x9
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x5x8x11
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x5x8x12
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x5x8x13
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x5x8x14
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x5x8x15
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x5x8x16
    have check17_x14x5x9 : check 27 17 30030 16509 7 2312 4913 203541624 = true := by decide +kernel
    have check17_x14x5x11 : check 27 17 30030 20042 8 2023 4913 203541624 = true := by decide +kernel
    have check17_x14x5x12 : check 27 17 30030 21808 0 4335 4913 203541624 = true := by decide +kernel
    have check17_x14x5x13 : check 27 17 30030 23575 9 1734 4913 203541624 = true := by decide +kernel
    have check17_x14x5x14 : check 27 17 30030 25341 1 4046 4913 203541624 = true := by decide +kernel
    have check17_x14x5x15 : check 27 17 30030 27108 10 1445 4913 203541624 = true := by decide +kernel
    have check17_x14x5x16 : check 27 17 30030 28874 2 3757 4913 203541624 = true := by decide +kernel
    have check17_x14x5 : check 28 17 30030 10391 15 0 289 3460207612 = true := by
      apply check_step 27 17 30030 10391 15 0 289 3460207612 (by norm_num) (by norm_num)
      intro t ht hb
      interval_cases t
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x5x0
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x5x1
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x5x2
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x5x3
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x5x4
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x5x5
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x5x6
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x5x7
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x5x8
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x5x9
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x5x11
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x5x12
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x5x13
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x5x14
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x5x15
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x5x16
    have check17_x14x6 : check 28 17 30030 12157 7 136 289 3460207612 = true := by decide +kernel
    have check17_x14x8 : check 28 17 30030 15690 8 119 289 3460207612 = true := by decide +kernel
    have check17_x14x9 : check 28 17 30030 17456 0 255 289 3460207612 = true := by decide +kernel
    have check17_x14x10 : check 28 17 30030 19223 9 102 289 3460207612 = true := by decide +kernel
    have check17_x14x11 : check 28 17 30030 20989 1 238 289 3460207612 = true := by decide +kernel
    have check17_x14x12x0 : check 27 17 30030 1338 0 2975 4913 203541624 = true := by decide +kernel
    have check17_x14x12x1 : check 27 17 30030 3105 9 374 4913 203541624 = true := by decide +kernel
    have check17_x14x12x2 : check 27 17 30030 4871 1 2686 4913 203541624 = true := by decide +kernel
    have check17_x14x12x3 : check 27 17 30030 6638 10 85 4913 203541624 = true := by decide +kernel
    have check17_x14x12x4 : check 27 17 30030 8404 2 2397 4913 203541624 = true := by decide +kernel
    have check17_x14x12x6 : check 27 17 30030 11937 3 2108 4913 203541624 = true := by decide +kernel
    have check17_x14x12x8 : check 27 17 30030 15470 4 1819 4913 203541624 = true := by decide +kernel
    have check17_x14x12x10 : check 27 17 30030 19003 5 1530 4913 203541624 = true := by decide +kernel
    have check17_x14x12x12 : check 27 17 30030 22536 6 1241 4913 203541624 = true := by decide +kernel
    have check17_x14x12x14 : check 27 17 30030 26069 7 952 4913 203541624 = true := by decide +kernel
    have check17_x14x12x16 : check 27 17 30030 29602 8 663 4913 203541624 = true := by decide +kernel
    have check17_x14x12 : check 28 17 30030 22756 10 85 289 3460207612 = true := by
      apply check_step 27 17 30030 22756 10 85 289 3460207612 (by norm_num) (by norm_num)
      intro t ht hb
      interval_cases t
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x12x0
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x12x1
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x12x2
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x12x3
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x12x4
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x12x6
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x12x8
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x12x10
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x12x12
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x12x14
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x12x16
    have check17_x14x13 : check 28 17 30030 24522 2 221 289 3460207612 = true := by decide +kernel
    have check17_x14x14x0 : check 27 17 30030 1546 4 2091 4913 203541624 = true := by decide +kernel
    have check17_x14x14x2 : check 27 17 30030 5079 5 1802 4913 203541624 = true := by decide +kernel
    have check17_x14x14x4 : check 27 17 30030 8612 6 1513 4913 203541624 = true := by decide +kernel
    have check17_x14x14x6 : check 27 17 30030 12145 7 1224 4913 203541624 = true := by decide +kernel
    have check17_x14x14x8 : check 27 17 30030 15678 8 935 4913 203541624 = true := by decide +kernel
    have check17_x14x14x9 : check 27 17 30030 17444 0 3247 4913 203541624 = true := by decide +kernel
    have check17_x14x14x10 : check 27 17 30030 19211 9 646 4913 203541624 = true := by decide +kernel
    have check17_x14x14x11 : check 27 17 30030 20977 1 2958 4913 203541624 = true := by decide +kernel
    have check17_x14x14x12 : check 27 17 30030 22744 10 357 4913 203541624 = true := by decide +kernel
    have check17_x14x14x13 : check 27 17 30030 24510 2 2669 4913 203541624 = true := by decide +kernel
    have check17_x14x14x14 : check 27 17 30030 26277 11 68 4913 203541624 = true := by decide +kernel
    have check17_x14x14x15 : check 27 17 30030 28043 3 2380 4913 203541624 = true := by decide +kernel
    have check17_x14x14 : check 28 17 30030 26289 11 68 289 3460207612 = true := by
      apply check_step 27 17 30030 26289 11 68 289 3460207612 (by norm_num) (by norm_num)
      intro t ht hb
      interval_cases t
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x14x0
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x14x2
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x14x4
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x14x6
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x14x8
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x14x9
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x14x10
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x14x11
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x14x12
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x14x13
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x14x14
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x14x15
      · norm_num at hb
    have check17_x14x15 : check 28 17 30030 28055 3 204 289 3460207612 = true := by decide +kernel
    have check17_x14x16x0 : check 27 17 30030 1754 8 1207 4913 203541624 = true := by decide +kernel
    have check17_x14x16x1 : check 27 17 30030 3520 0 3519 4913 203541624 = true := by decide +kernel
    have check17_x14x16x2 : check 27 17 30030 5287 9 918 4913 203541624 = true := by decide +kernel
    have check17_x14x16x3 : check 27 17 30030 7053 1 3230 4913 203541624 = true := by decide +kernel
    have check17_x14x16x4 : check 27 17 30030 8820 10 629 4913 203541624 = true := by decide +kernel
    have check17_x14x16x5 : check 27 17 30030 10586 2 2941 4913 203541624 = true := by decide +kernel
    have check17_x14x16x6 : check 27 17 30030 12353 11 340 4913 203541624 = true := by decide +kernel
    have check17_x14x16x7 : check 27 17 30030 14119 3 2652 4913 203541624 = true := by decide +kernel
    have check17_x14x16x8 : check 27 17 30030 15886 12 51 4913 203541624 = true := by decide +kernel
    have check17_x14x16x9 : check 27 17 30030 17652 4 2363 4913 203541624 = true := by decide +kernel
    have check17_x14x16x11 : check 27 17 30030 21185 5 2074 4913 203541624 = true := by decide +kernel
    have check17_x14x16x13 : check 27 17 30030 24718 6 1785 4913 203541624 = true := by decide +kernel
    have check17_x14x16x15 : check 27 17 30030 28251 7 1496 4913 203541624 = true := by decide +kernel
    have check17_x14x16 : check 28 17 30030 29822 12 51 289 3460207612 = true := by
      apply check_step 27 17 30030 29822 12 51 289 3460207612 (by norm_num) (by norm_num)
      intro t ht hb
      interval_cases t
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x16x0
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x16x1
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x16x2
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x16x3
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x16x4
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x16x5
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x16x6
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x16x7
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x16x8
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x16x9
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x16x11
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x16x13
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x16x15
      · norm_num at hb
    have check17_x14 : check 29 17 30030 26497 15 0 17 58823529411 = true := by
      apply check_step 28 17 30030 26497 15 0 17 58823529411 (by norm_num) (by norm_num)
      intro t ht hb
      interval_cases t
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x0
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x1
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x2
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x3
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x4
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x5
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x6
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x8
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x9
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x10
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x11
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x12
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x13
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x14
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x15
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14x16
    have check17_x15 : check 29 17 30030 28263 7 8 17 58823529411 = true := by decide +kernel
    apply check_step 29 17 30030 30029 15 0 1 999999999999 (by norm_num) (by norm_num)
    intro t ht hb
    interval_cases t
    · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x0
    · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x1
    · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x2
    · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x3
    · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x4
    · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x5
    · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x6
    · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x7
    · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x8
    · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x9
    · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x10
    · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x11
    · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x12
    · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x13
    · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x14
    · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check17_x15
    · norm_num at hb
  have check19 : check 30 19 510510 510509 17 0 1 999999999999 = true := by
    have check19_x0 : check 29 19 510510 26868 0 17 19 52631578947 = true := by decide +kernel
    have check19_x1 : check 29 19 510510 53737 1 16 19 52631578947 = true := by decide +kernel
    have check19_x2 : check 29 19 510510 80606 2 15 19 52631578947 = true := by decide +kernel
    have check19_x3 : check 29 19 510510 107475 3 14 19 52631578947 = true := by decide +kernel
    have check19_x4 : check 29 19 510510 134344 4 13 19 52631578947 = true := by decide +kernel
    have check19_x5 : check 29 19 510510 161213 5 12 19 52631578947 = true := by decide +kernel
    have check19_x6 : check 29 19 510510 188082 6 11 19 52631578947 = true := by decide +kernel
    have check19_x7 : check 29 19 510510 214951 7 10 19 52631578947 = true := by decide +kernel
    have check19_x8 : check 29 19 510510 241820 8 9 19 52631578947 = true := by decide +kernel
    have check19_x9 : check 29 19 510510 268689 9 8 19 52631578947 = true := by decide +kernel
    have check19_x10 : check 29 19 510510 295558 10 7 19 52631578947 = true := by decide +kernel
    have check19_x11 : check 29 19 510510 322427 11 6 19 52631578947 = true := by decide +kernel
    have check19_x12 : check 29 19 510510 349296 12 5 19 52631578947 = true := by decide +kernel
    have check19_x13 : check 29 19 510510 376165 13 4 19 52631578947 = true := by decide +kernel
    have check19_x14x0 : check 28 19 510510 21212 8 117 361 2770083102 = true := by decide +kernel
    have check19_x14x1 : check 28 19 510510 48081 9 98 361 2770083102 = true := by decide +kernel
    have check19_x14x2 : check 28 19 510510 74950 10 79 361 2770083102 = true := by decide +kernel
    have check19_x14x3 : check 28 19 510510 101819 11 60 361 2770083102 = true := by decide +kernel
    have check19_x14x4 : check 28 19 510510 128688 12 41 361 2770083102 = true := by decide +kernel
    have check19_x14x5 : check 28 19 510510 155557 13 22 361 2770083102 = true := by decide +kernel
    have check19_x14x6 : check 28 19 510510 182426 14 3 361 2770083102 = true := by decide +kernel
    have check19_x14x11 : check 28 19 510510 316770 0 269 361 2770083102 = true := by decide +kernel
    have check19_x14x12 : check 28 19 510510 343639 1 250 361 2770083102 = true := by decide +kernel
    have check19_x14x13 : check 28 19 510510 370508 2 231 361 2770083102 = true := by decide +kernel
    have check19_x14x14 : check 28 19 510510 397377 3 212 361 2770083102 = true := by decide +kernel
    have check19_x14x15 : check 28 19 510510 424246 4 193 361 2770083102 = true := by decide +kernel
    have check19_x14x16 : check 28 19 510510 451115 5 174 361 2770083102 = true := by decide +kernel
    have check19_x14x17 : check 28 19 510510 477984 6 155 361 2770083102 = true := by decide +kernel
    have check19_x14x18 : check 28 19 510510 504853 7 136 361 2770083102 = true := by decide +kernel
    have check19_x14 : check 29 19 510510 403034 14 3 19 52631578947 = true := by
      apply check_step 28 19 510510 403034 14 3 19 52631578947 (by norm_num) (by norm_num)
      intro t ht hb
      interval_cases t
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x14x0
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x14x1
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x14x2
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x14x3
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x14x4
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x14x5
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x14x6
      · norm_num at hb
      · norm_num at hb
      · norm_num at hb
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x14x11
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x14x12
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x14x13
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x14x14
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x14x15
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x14x16
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x14x17
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x14x18
    have check19_x15x0 : check 28 19 510510 22626 6 173 361 2770083102 = true := by decide +kernel
    have check19_x15x1 : check 28 19 510510 49495 7 154 361 2770083102 = true := by decide +kernel
    have check19_x15x2 : check 28 19 510510 76364 8 135 361 2770083102 = true := by decide +kernel
    have check19_x15x3 : check 28 19 510510 103233 9 116 361 2770083102 = true := by decide +kernel
    have check19_x15x4 : check 28 19 510510 130102 10 97 361 2770083102 = true := by decide +kernel
    have check19_x15x5 : check 28 19 510510 156971 11 78 361 2770083102 = true := by decide +kernel
    have check19_x15x6 : check 28 19 510510 183840 12 59 361 2770083102 = true := by decide +kernel
    have check19_x15x7 : check 28 19 510510 210709 13 40 361 2770083102 = true := by decide +kernel
    have check19_x15x8 : check 28 19 510510 237578 14 21 361 2770083102 = true := by decide +kernel
    have check19_x15x9 : check 28 19 510510 264447 15 2 361 2770083102 = true := by decide +kernel
    have check19_x15x13 : check 28 19 510510 371922 0 287 361 2770083102 = true := by decide +kernel
    have check19_x15x14 : check 28 19 510510 398791 1 268 361 2770083102 = true := by decide +kernel
    have check19_x15x15 : check 28 19 510510 425660 2 249 361 2770083102 = true := by decide +kernel
    have check19_x15x16 : check 28 19 510510 452529 3 230 361 2770083102 = true := by decide +kernel
    have check19_x15x17 : check 28 19 510510 479398 4 211 361 2770083102 = true := by decide +kernel
    have check19_x15x18 : check 28 19 510510 506267 5 192 361 2770083102 = true := by decide +kernel
    have check19_x15 : check 29 19 510510 429903 15 2 19 52631578947 = true := by
      apply check_step 28 19 510510 429903 15 2 19 52631578947 (by norm_num) (by norm_num)
      intro t ht hb
      interval_cases t
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x15x0
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x15x1
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x15x2
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x15x3
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x15x4
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x15x5
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x15x6
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x15x7
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x15x8
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x15x9
      · norm_num at hb
      · norm_num at hb
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x15x13
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x15x14
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x15x15
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x15x16
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x15x17
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x15x18
    have check19_x16x0 : check 28 19 510510 24040 4 229 361 2770083102 = true := by decide +kernel
    have check19_x16x1 : check 28 19 510510 50909 5 210 361 2770083102 = true := by decide +kernel
    have check19_x16x2 : check 28 19 510510 77778 6 191 361 2770083102 = true := by decide +kernel
    have check19_x16x3 : check 28 19 510510 104647 7 172 361 2770083102 = true := by decide +kernel
    have check19_x16x4 : check 28 19 510510 131516 8 153 361 2770083102 = true := by decide +kernel
    have check19_x16x5 : check 28 19 510510 158385 9 134 361 2770083102 = true := by decide +kernel
    have check19_x16x6 : check 28 19 510510 185254 10 115 361 2770083102 = true := by decide +kernel
    have check19_x16x7 : check 28 19 510510 212123 11 96 361 2770083102 = true := by decide +kernel
    have check19_x16x8 : check 28 19 510510 238992 12 77 361 2770083102 = true := by decide +kernel
    have check19_x16x9 : check 28 19 510510 265861 13 58 361 2770083102 = true := by decide +kernel
    have check19_x16x10 : check 28 19 510510 292730 14 39 361 2770083102 = true := by decide +kernel
    have check19_x16x11 : check 28 19 510510 319599 15 20 361 2770083102 = true := by decide +kernel
    have check19_x16x12 : check 28 19 510510 346468 16 1 361 2770083102 = true := by decide +kernel
    have check19_x16x15 : check 28 19 510510 427074 0 305 361 2770083102 = true := by decide +kernel
    have check19_x16x16 : check 28 19 510510 453943 1 286 361 2770083102 = true := by decide +kernel
    have check19_x16x17 : check 28 19 510510 480812 2 267 361 2770083102 = true := by decide +kernel
    have check19_x16x18 : check 28 19 510510 507681 3 248 361 2770083102 = true := by decide +kernel
    have check19_x16 : check 29 19 510510 456772 16 1 19 52631578947 = true := by
      apply check_step 28 19 510510 456772 16 1 19 52631578947 (by norm_num) (by norm_num)
      intro t ht hb
      interval_cases t
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x16x0
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x16x1
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x16x2
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x16x3
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x16x4
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x16x5
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x16x6
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x16x7
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x16x8
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x16x9
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x16x10
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x16x11
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x16x12
      · norm_num at hb
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x16x15
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x16x16
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x16x17
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x16x18
    have check19_x17x0 : check 28 19 510510 25454 2 285 361 2770083102 = true := by decide +kernel
    have check19_x17x1 : check 28 19 510510 52323 3 266 361 2770083102 = true := by decide +kernel
    have check19_x17x2 : check 28 19 510510 79192 4 247 361 2770083102 = true := by decide +kernel
    have check19_x17x3 : check 28 19 510510 106061 5 228 361 2770083102 = true := by decide +kernel
    have check19_x17x4 : check 28 19 510510 132930 6 209 361 2770083102 = true := by decide +kernel
    have check19_x17x5 : check 28 19 510510 159799 7 190 361 2770083102 = true := by decide +kernel
    have check19_x17x6 : check 28 19 510510 186668 8 171 361 2770083102 = true := by decide +kernel
    have check19_x17x7 : check 28 19 510510 213537 9 152 361 2770083102 = true := by decide +kernel
    have check19_x17x8 : check 28 19 510510 240406 10 133 361 2770083102 = true := by decide +kernel
    have check19_x17x9 : check 28 19 510510 267275 11 114 361 2770083102 = true := by decide +kernel
    have check19_x17x10 : check 28 19 510510 294144 12 95 361 2770083102 = true := by decide +kernel
    have check19_x17x11 : check 28 19 510510 321013 13 76 361 2770083102 = true := by decide +kernel
    have check19_x17x12 : check 28 19 510510 347882 14 57 361 2770083102 = true := by decide +kernel
    have check19_x17x13 : check 28 19 510510 374751 15 38 361 2770083102 = true := by decide +kernel
    have check19_x17x14 : check 28 19 510510 401620 16 19 361 2770083102 = true := by decide +kernel
    have check19_x17x15 : check 28 19 510510 428489 17 0 361 2770083102 = true := by decide +kernel
    have check19_x17x17 : check 28 19 510510 482226 0 323 361 2770083102 = true := by decide +kernel
    have check19_x17x18 : check 28 19 510510 509095 1 304 361 2770083102 = true := by decide +kernel
    have check19_x17 : check 29 19 510510 483641 17 0 19 52631578947 = true := by
      apply check_step 28 19 510510 483641 17 0 19 52631578947 (by norm_num) (by norm_num)
      intro t ht hb
      interval_cases t
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x17x0
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x17x1
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x17x2
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x17x3
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x17x4
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x17x5
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x17x6
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x17x7
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x17x8
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x17x9
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x17x10
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x17x11
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x17x12
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x17x13
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x17x14
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x17x15
      · norm_num at hb
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x17x17
      · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x17x18
    apply check_step 29 19 510510 510509 17 0 1 999999999999 (by norm_num) (by norm_num)
    intro t ht hb
    interval_cases t
    · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x0
    · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x1
    · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x2
    · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x3
    · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x4
    · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x5
    · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x6
    · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x7
    · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x8
    · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x9
    · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x10
    · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x11
    · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x12
    · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x13
    · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x14
    · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x15
    · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x16
    · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check19_x17
    · norm_num at hb
  have check23 : check 30 23 9699690 9699689 21 0 1 999999999999 = true := by
    have check23_x0 : check 29 23 9699690 421725 7 14 23 43478260869 = true := by decide +kernel
    have check23_x1 : check 29 23 9699690 843451 15 6 23 43478260869 = true := by decide +kernel
    have check23_x2 : check 29 23 9699690 1265176 0 21 23 43478260869 = true := by decide +kernel
    have check23_x3 : check 29 23 9699690 1686902 8 13 23 43478260869 = true := by decide +kernel
    have check23_x4 : check 29 23 9699690 2108628 16 5 23 43478260869 = true := by decide +kernel
    have check23_x5 : check 29 23 9699690 2530353 1 20 23 43478260869 = true := by decide +kernel
    have check23_x6 : check 29 23 9699690 2952079 9 12 23 43478260869 = true := by decide +kernel
    have check23_x7 : check 29 23 9699690 3373805 17 4 23 43478260869 = true := by decide +kernel
    have check23_x8 : check 29 23 9699690 3795530 2 19 23 43478260869 = true := by decide +kernel
    have check23_x9 : check 29 23 9699690 4217256 10 11 23 43478260869 = true := by decide +kernel
    have check23_x10 : check 29 23 9699690 4638982 18 3 23 43478260869 = true := by decide +kernel
    have check23_x11 : check 29 23 9699690 5060707 3 18 23 43478260869 = true := by decide +kernel
    have check23_x12 : check 29 23 9699690 5482433 11 10 23 43478260869 = true := by decide +kernel
    have check23_x13 : check 29 23 9699690 5904159 19 2 23 43478260869 = true := by decide +kernel
    have check23_x14 : check 29 23 9699690 6325884 4 17 23 43478260869 = true := by decide +kernel
    have check23_x15 : check 29 23 9699690 6747610 12 9 23 43478260869 = true := by decide +kernel
    have check23_x16 : check 29 23 9699690 7169336 20 1 23 43478260869 = true := by decide +kernel
    have check23_x17 : check 29 23 9699690 7591061 5 16 23 43478260869 = true := by decide +kernel
    have check23_x18 : check 29 23 9699690 8012787 13 8 23 43478260869 = true := by decide +kernel
    have check23_x19 : check 29 23 9699690 8434513 21 0 23 43478260869 = true := by decide +kernel
    have check23_x20 : check 29 23 9699690 8856238 6 15 23 43478260869 = true := by decide +kernel
    have check23_x21 : check 29 23 9699690 9277964 14 7 23 43478260869 = true := by decide +kernel
    apply check_step 29 23 9699690 9699689 21 0 1 999999999999 (by norm_num) (by norm_num)
    intro t ht hb
    interval_cases t
    · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check23_x0
    · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check23_x1
    · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check23_x2
    · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check23_x3
    · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check23_x4
    · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check23_x5
    · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check23_x6
    · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check23_x7
    · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check23_x8
    · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check23_x9
    · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check23_x10
    · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check23_x11
    · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check23_x12
    · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check23_x13
    · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check23_x14
    · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check23_x15
    · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check23_x16
    · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check23_x17
    · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check23_x18
    · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check23_x19
    · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check23_x20
    · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check23_x21
    · norm_num at hb
  have check29 : check 30 29 223092870 223092869 27 0 1 999999999999 = true := by
    have check29_x0 : check 29 29 223092870 7692857 11 16 29 34482758620 = true := by decide +kernel
    have check29_x1 : check 29 29 223092870 15385715 23 4 29 34482758620 = true := by decide +kernel
    have check29_x2 : check 29 29 223092870 23078572 6 21 29 34482758620 = true := by decide +kernel
    have check29_x3 : check 29 29 223092870 30771430 18 9 29 34482758620 = true := by decide +kernel
    have check29_x4 : check 29 29 223092870 38464287 1 26 29 34482758620 = true := by decide +kernel
    have check29_x5 : check 29 29 223092870 46157145 13 14 29 34482758620 = true := by decide +kernel
    have check29_x6 : check 29 29 223092870 53850003 25 2 29 34482758620 = true := by decide +kernel
    have check29_x7 : check 29 29 223092870 61542860 8 19 29 34482758620 = true := by decide +kernel
    have check29_x8 : check 29 29 223092870 69235718 20 7 29 34482758620 = true := by decide +kernel
    have check29_x9 : check 29 29 223092870 76928575 3 24 29 34482758620 = true := by decide +kernel
    have check29_x10 : check 29 29 223092870 84621433 15 12 29 34482758620 = true := by decide +kernel
    have check29_x11 : check 29 29 223092870 92314291 27 0 29 34482758620 = true := by decide +kernel
    have check29_x12 : check 29 29 223092870 100007148 10 17 29 34482758620 = true := by decide +kernel
    have check29_x13 : check 29 29 223092870 107700006 22 5 29 34482758620 = true := by decide +kernel
    have check29_x14 : check 29 29 223092870 115392863 5 22 29 34482758620 = true := by decide +kernel
    have check29_x15 : check 29 29 223092870 123085721 17 10 29 34482758620 = true := by decide +kernel
    have check29_x16 : check 29 29 223092870 130778578 0 27 29 34482758620 = true := by decide +kernel
    have check29_x17 : check 29 29 223092870 138471436 12 15 29 34482758620 = true := by decide +kernel
    have check29_x18 : check 29 29 223092870 146164294 24 3 29 34482758620 = true := by decide +kernel
    have check29_x19 : check 29 29 223092870 153857151 7 20 29 34482758620 = true := by decide +kernel
    have check29_x20 : check 29 29 223092870 161550009 19 8 29 34482758620 = true := by decide +kernel
    have check29_x21 : check 29 29 223092870 169242866 2 25 29 34482758620 = true := by decide +kernel
    have check29_x22 : check 29 29 223092870 176935724 14 13 29 34482758620 = true := by decide +kernel
    have check29_x23 : check 29 29 223092870 184628582 26 1 29 34482758620 = true := by decide +kernel
    have check29_x24 : check 29 29 223092870 192321439 9 18 29 34482758620 = true := by decide +kernel
    have check29_x25 : check 29 29 223092870 200014297 21 6 29 34482758620 = true := by decide +kernel
    have check29_x26 : check 29 29 223092870 207707154 4 23 29 34482758620 = true := by decide +kernel
    have check29_x27 : check 29 29 223092870 215400012 16 11 29 34482758620 = true := by decide +kernel
    apply check_step 29 29 223092870 223092869 27 0 1 999999999999 (by norm_num) (by norm_num)
    intro t ht hb
    interval_cases t
    · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check29_x0
    · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check29_x1
    · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check29_x2
    · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check29_x3
    · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check29_x4
    · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check29_x5
    · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check29_x6
    · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check29_x7
    · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check29_x8
    · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check29_x9
    · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check29_x10
    · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check29_x11
    · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check29_x12
    · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check29_x13
    · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check29_x14
    · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check29_x15
    · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check29_x16
    · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check29_x17
    · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check29_x18
    · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check29_x19
    · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check29_x20
    · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check29_x21
    · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check29_x22
    · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check29_x23
    · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check29_x24
    · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check29_x25
    · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check29_x26
    · simpa only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub] using check29_x27
    · norm_num at hb
  have check31 : check 30 31 6469693230 6469693229 29 0 1 999999999999 = true := by decide +kernel
  intro n hlo hhi hodd
  apply VestigeBernoulliDigit.all_cases check3 check5 check7 check11 check13 check17 check19 check23 check29 check31 n hlo _ hodd
  simpa only [show 10000^3 = 1000000000000 by norm_num] using hhi
