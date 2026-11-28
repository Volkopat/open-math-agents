import OMAReductions.R_OeisA215926_conjecture_2_R1

/-! Reduce the dyadic obstruction to two tests on odd roots. The divisor-sum
shape and the central identity are classical. A finite certificate and the exact
quotient remove small roots and the search over the two-adic exponent. -/

namespace OMA.R_OeisA215926_conjecture_2_R1_H1_R1
open Finset ArithmeticFunction OeisA215926
open scoped ArithmeticFunction.sigma

private theorem geom_parity (p e : ℕ) (ho : Odd p) :
    (∑ j ∈ range (e+1), p^j)%2 = (e+1)%2 := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [sum_range_succ, Nat.add_mod, ih, Nat.odd_iff.mp (show Odd (p^(e+1)) from ho.pow)]
    omega

theorem shape (n : ℕ) (hn : Odd (σ 1 n)) :
    ∃ a b : ℕ, Odd b ∧ n = 2^a*b^2 := by
  induction n using Nat.recOnPrimeCoprime with
  | zero => simp at hn
  | prime_pow p e hp =>
    by_cases htwo : p=2
    · subst p
      exact ⟨e,1,by decide,by simp⟩
    · have oddp := hp.odd_of_ne_two htwo
      rw [sigma_one_apply_prime_pow hp] at hn
      have h := Nat.odd_iff.mp hn
      rw [geom_parity p e oddp] at h
      have two : e/2*2=e := by omega
      exact ⟨0,p^(e/2),oddp.pow,by rw [←pow_mul,two]; simp⟩
  | coprime x y hx hy hc ihx ihy =>
    rw [isMultiplicative_sigma.map_mul_of_coprime hc, Nat.odd_mul] at hn
    obtain ⟨a,b,hb,ex⟩ := ihx hn.1
    obtain ⟨c,d,hd,ey⟩ := ihy hn.2
    exact ⟨a+c,b*d,hb.mul hd,by rw [ex,ey,pow_add,mul_pow]; ring⟩

private theorem two_sigma (a : ℕ) : σ 1 (2^a)+1 = 2^(a+1) := by
  rw [sigma_one_apply_prime_pow Nat.prime_two]
  induction a with
  | zero => norm_num
  | succ a ih =>
    rw [Finset.sum_range_succ,pow_succ _ (a+1)]
    omega

theorem odd_core_identity (a b : ℕ) (ho : Odd b)
    (h : σ 1 (2^a*b^2)+1 = 2*(2^a*b^2)) :
    2*(2^a)*(σ 1 (b^2))+1 = 2*(2^a)*b^2 + σ 1 (b^2) := by
  have co := (Nat.coprime_two_left.mpr ho).pow_left a |>.pow_right 2
  rw [isMultiplicative_sigma.map_mul_of_coprime co] at h
  have eq := two_sigma a
  rw [pow_succ] at eq
  have add := congrArg (· * σ 1 (b^2)) eq
  nlinarith only [add,h]

private theorem geom_shift (p e : ℕ) :
    p*(∑ j ∈ range (e+1),p^j)+1 = p*p^e+(∑ j ∈ range (e+1),p^j) := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [sum_range_succ,pow_succ p e]
    nlinarith only [ih]

theorem odd_prime_power_excluded (a p t : ℕ) (hp : p.Prime) (ho : Odd p) (ht : 0<t) :
    σ 1 (2^a*(p^t)^2)+1 ≠ 2*(2^a*(p^t)^2) := by
  intro bad
  have h := odd_core_identity a (p^t) ho.pow bad
  rw [←pow_mul, sigma_one_apply_prime_pow hp] at h
  have gg := geom_shift p (t*2)
  have pos : 0 < ∑ j ∈ range (t*2),p^j := by
    apply sum_pos' (fun j hj => Nat.zero_le _)
    exact ⟨0,mem_range.mpr (by omega),by simp⟩
  rw [sum_range_succ] at gg h
  have fac : (2*(2^a))*(∑ j ∈ range (t*2),p^j) =
      p*(∑ j ∈ range (t*2),p^j) := by nlinarith only [h,gg]
  have eq := Nat.eq_of_mul_eq_mul_right pos fac
  have := Nat.odd_iff.mp ho
  omega
private theorem coreSigma_eq (b : ℕ) (hb : b ≠ 0) : (∏ p ∈ b.primeFactors, ∑ i ∈ range (2*b.factorization p+1),p^i) = σ 1 (b^2) := by
  rw [sigma_one_apply,Nat.sum_divisors (pow_ne_zero _ hb),Nat.primeFactors_pow _ (by decide : 2≠0)]
  simp [Nat.factorization_pow,Finsupp.smul_apply]

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 8000 in
private theorem finite_table (j : ℕ) (hj : j < 127) :
    let b := 2*j+3
    let s := (∏ p ∈ b.primeFactors, ∑ i ∈ range (2*b.factorization p+1),p^i)
    (s-1) % (2*(s-b^2)) ≠ 0 := by
  interval_cases j  <;> decide +kernel

theorem bounded_root (a b : ℕ) (ho : Odd b) (nontrivial : 1 < b) (bound : b < 256) :
    σ 1 (2^a*b^2)+1 ≠ 2*(2^a*b^2) := by
  intro bad
  have ident := odd_core_identity a b ho bad
  let j := (b-3)/2
  have parity := Nat.odd_iff.mp ho
  have beq : 2*j+3=b := by dsimp [j]; omega
  have cap : j < 127 := by dsimp [j]; omega
  have cert := finite_table j cap
  dsimp only at cert
  rw [beq,coreSigma_eq b (by omega)] at cert
  apply cert
  apply Nat.mod_eq_zero_of_dvd
  refine ⟨2^a,?_⟩
  calc
    σ 1 (b^2)-1 = 2*2^a*(σ 1 (b^2)) - 2*2^a*b^2 := by omega
    _ = _ := by rw [←Nat.mul_sub_left_distrib]; ring


private theorem pair_bound (b : ℕ) (hb : 1 < b) : b+1+b^2 ≤ σ 1 (b^2) := by
  have pos : 0 < b^2 := by positivity
  have strict : b < b^2 := by nlinarith
  have inside : ({1,b,b^2}:Finset ℕ) ⊆ (b^2).divisors := by
    intro z hz
    simp only [mem_insert,mem_singleton] at hz
    rcases hz with h|h|h
    · rw [h]
      exact Nat.mem_divisors.mpr ⟨one_dvd _,pos.ne'⟩
    · rw [h]
      exact Nat.mem_divisors.mpr ⟨dvd_pow_self b (by decide : 2≠0),pos.ne'⟩
    · rw [h]
      exact Nat.mem_divisors.mpr ⟨dvd_rfl,pos.ne'⟩
  have small := Finset.sum_le_sum_of_subset (f:=fun d : ℕ => d) inside
  have h1 : 1 ∉ ({b,b^2}:Finset ℕ) := by simp; omega
  have h2 : b ∉ ({b^2}:Finset ℕ) := by simp; omega
  rw [sum_insert h1,sum_insert h2,sum_singleton] at small
  rw [sigma_one_apply]
  omega

private theorem exact_factor (a b : ℕ) (odd : Odd b) (hb : 1 < b)
    (bad : σ 1 (2^a*b^2)+1=2*(2^a*b^2)) :
    let s := σ 1 (b^2)
    let d := s-b^2
    0 < d ∧ d ∣ s-1 ∧ (s-1)/d = 2*2^a ∧ 2*2^a < b := by
  dsimp only
  let s := σ 1 (b^2)
  let d := s-b^2
  change 0 < d ∧ d ∣ s-1 ∧ (s-1)/d = 2*2^a ∧ 2*2^a < b
  have fl := odd_core_identity a b odd bad
  change 2*2^a*s+1=2*2^a*b^2+s at fl
  have lo : b+1+b^2 ≤ s := pair_bound b hb
  have hd : b+1 ≤ d := by dsimp [d]; omega
  have ds : d+b^2=s := Nat.sub_add_cancel (by omega)
  have exact_d : s-1=(2*2^a)*d := by
    calc
      s-1 = 2*2^a*s-2*2^a*b^2 := by omega
      _ = _ := (Nat.mul_sub_left_distrib ..).symm
  have pos : 0 < d := by omega
  refine ⟨pos,⟨2*2^a,exact_d.trans (mul_comm ..)⟩,?_,?_⟩
  · rw [exact_d,Nat.mul_div_cancel _ pos]
  · have bound : 2*2^a ≤ b := by
      by_contra! bh
      have step := Nat.mul_le_mul_right d (show b+1 ≤ 2*2^a by omega)
      have other := Nat.mul_le_mul_left b hd
      have keep : s=(2*2^a)*d+1 := by omega
      nlinarith only [step,other,keep,ds]
    have parity := Nat.odd_iff.mp odd
    omega

private theorem gap_index (m k : ℕ) (hm : 1 ≤ m) (hk : k < 2^m) (large : 2^m < 2*k) :
    k.log2+1=m := by
  obtain ⟨t,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m≠0)
  have half : 2^t ≤ k := by rw [pow_succ] at large; omega
  have kpos : k ≠ 0 := by have := Nat.two_pow_pos t; omega
  have idx := (Nat.log2_eq_iff kpos).mpr ⟨half,hk⟩
  omega

/-- A prime beyond the next dyadic boundary cannot intervene for a nontrivial odd
almost-perfect square. The finite and prime-power roots are already excluded. -/
def H1 : Prop :=
  ∀ b : ℕ, Odd b → 257 ≤ b → (∀ p e : ℕ, p.Prime → 0 < e → b ≠ p^e) →
    σ 1 (b^2)+1 = 2*b^2 →
    ∀ q : ℕ, q.Prime → 2^((b^2).log2+1) < q → 2*b^2 ≤ q

/-- For the even case the root determines the only possible power of two.
An exact quotient that is a power of two gives one interval to test. -/
def H2 : Prop :=
  ∀ b : ℕ, Odd b → 257 ≤ b → (∀ p e : ℕ, p.Prime → 0 < e → b ≠ p^e) →
    let s := σ 1 (b^2)
    let d := s-b^2
    let N := (s-1)/d
    d ∣ s-1 → 4 ≤ N → N < b → N=2^N.log2 →
    ∀ q : ℕ, q.Prime → 2^(((N/2)*b^2).log2+1) < q → N*b^2 ≤ q

theorem main : H1 → H2 → OMA.R_OeisA215926_conjecture_2_R1.H1 := by
  intro hodd heven m k hm hk interval bad
  have sig : σ 1 k+1=2*k := by rwa [sigma_one_apply]
  have odd : Odd (σ 1 k) := Nat.odd_iff.mpr (by omega)
  obtain ⟨a,b,ho,eq⟩ := shape k odd
  have sb : σ 1 (2^a*b^2)+1=2*(2^a*b^2) := eq ▸ sig
  let q := nextPrimeTwoPow m
  obtain ⟨r,hr,rp⟩ := Nat.exists_infinite_primes (2^m+1)
  have first : 2^m < q ∧ q.Prime := Nat.sInf_mem
    (show {p : ℕ | 2^m < p ∧ p.Prime}.Nonempty from ⟨r,hr,rp⟩)
  change q+1 ≤ 2*k at interval
  have idx := gap_index m k hm hk (by omega)
  have bne : b ≠ 1 := by
    intro eb
    have ek : k=2^a := by simpa only [eb,one_pow,mul_one] using eq
    have em : a+1=m := by simpa only [ek,Nat.log2_two_pow] using idx
    have eg : 2^m=2*k := by rw [←em,ek,pow_succ,mul_comm]
    omega
  have nontriv : 1 < b := by have := ho.pos; omega
  have large : 257 ≤ b := by
    have par := Nat.odd_iff.mp ho
    by_contra! small
    exact bounded_root a b ho nontriv (by omega) sb
  have notpow : ∀ p e : ℕ, p.Prime → 0 < e → b ≠ p^e := by
    intro p e hp he eb
    have pd : p ∣ b := eb ▸ dvd_pow_self p he.ne'
    have oddp := ho.of_dvd_nat pd
    exact odd_prime_power_excluded a p e hp oddp he (eb ▸ sb)
  by_cases az : a=0
  · subst a
    have bk : k=b^2 := by simpa using eq
    have base : σ 1 (b^2)+1=2*b^2 := by simpa using sb
    have exclude := hodd b ho large notpow base q first.2 (by rw [←bk,idx]; exact first.1)
    omega
  · let s := σ 1 (b^2)
    let d := s-b^2
    let N := (s-1)/d
    obtain ⟨_,divides,nq,limit⟩ := exact_factor a b ho nontriv sb
    change N=2*2^a at nq
    have poweq : N=2^(a+1) := by rw [nq,pow_succ,mul_comm]
    have logeq : N=2^N.log2 := by rw [poweq,Nat.log2_two_pow]
    have four : 4 ≤ N := by
      have lt := Nat.pow_le_pow_right (by decide : 0<2) (show 1 ≤ a by omega)
      omega
    have key : (N/2)*b^2=k := by rw [nq,Nat.mul_div_cancel_left _ (by decide : 0<2),←eq]
    have below : N < b := by rw [nq]; exact limit
    have excl := heven b ho large notpow divides four below logeq q first.2
      (by change 2^(((N/2)*b^2).log2+1) < q; rw [key,idx]; exact first.1)
    change N*b^2 ≤ q at excl
    have twice : N*b^2=2*k := by rw [nq,eq]; ring
    omega

end OMA.R_OeisA215926_conjecture_2_R1_H1_R1
