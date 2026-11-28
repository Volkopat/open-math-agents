import OMAStatements.S_oeis_a321727
import Mathlib

section
/-! A signed Legendre sieve. The weights are arbitrary completely multiplicative
integer-valued weights, so the same recurrence works for ordinary prime counts. -/
namespace SunPrimePermutation
open Finset

def roughNumbers (d x : ℕ) : Finset ℕ :=
  (Icc 1 x).filter (fun n => d.Coprime n)

def roughSum (w : ℕ → ℤ) (d x : ℕ) : ℤ := ∑ n ∈ roughNumbers d x, w n

theorem rough_split (w : ℕ → ℤ) (hmul : ∀ a b, w (a*b) = w a * w b)
    {p d : ℕ} (hp : p.Prime) (hd : d.Coprime p) (x : ℕ) :
    roughSum w (d*p) x = roughSum w d x - w p * roughSum w d (x/p) := by
  classical
  let S := roughNumbers d x
  have same : S.filter (fun n => ¬ p ∣ n) = roughNumbers (d*p) x := by
    ext n
    simp [S, roughNumbers, Nat.coprime_mul_iff_left, hp.coprime_iff_not_dvd, and_assoc]
  have removed : S.filter (fun n => p ∣ n) =
      (roughNumbers d (x/p)).image (fun n => p*n) := by
    ext n
    constructor
    · intro hn
      obtain ⟨hnS, ⟨k, rfl⟩⟩ := mem_filter.mp hn
      obtain ⟨hb, hcop⟩ := mem_filter.mp hnS
      obtain ⟨hl, hu⟩ := mem_Icc.mp hb
      apply mem_image.mpr
      refine ⟨k, mem_filter.mpr ⟨mem_Icc.mpr ⟨?_, ?_⟩, ?_⟩, rfl⟩
      · cases k <;> simp_all
      · exact (Nat.le_div_iff_mul_le hp.pos).mpr (by simpa [Nat.mul_comm] using hu)
      · exact (Nat.coprime_mul_iff_right.mp hcop).2
    · intro hn
      obtain ⟨k, hk, rfl⟩ := mem_image.mp hn
      obtain ⟨hb, hcop⟩ := mem_filter.mp hk
      obtain ⟨hl, hu⟩ := mem_Icc.mp hb
      apply mem_filter.mpr
      refine ⟨mem_filter.mpr ⟨mem_Icc.mpr ⟨?_, ?_⟩,
        Nat.coprime_mul_iff_right.mpr ⟨hd, hcop⟩⟩, dvd_mul_right _ _⟩
      · exact Nat.mul_pos hp.pos hl
      · simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hp.pos).mp hu
  have parts := Finset.sum_filter_add_sum_filter_not S (fun n => p ∣ n) w
  rw [same, removed, Finset.sum_image (fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hp.pos h)] at parts
  simp only [hmul, ← Finset.mul_sum] at parts
  change roughSum w (d*p) x = roughSum w d x - w p * roughSum w d (x/p)
  unfold roughSum
  change _ + _ = ∑ n ∈ roughNumbers d x, w n at parts
  omega

def chi3 (n : ℕ) : ℤ := if n % 3 = 1 then 1 else if n % 3 = 2 then -1 else 0

theorem chi3_mul (a b : ℕ) : chi3 (a*b) = chi3 a * chi3 b := by
  have ha := Nat.mod_lt a (by decide : 0 < 3)
  have hb := Nat.mod_lt b (by decide : 0 < 3)
  simp only [chi3, Nat.mul_mod a b 3]
  have h₁ : a % 3 = 0 ∨ a % 3 = 1 ∨ a % 3 = 2 := by omega
  have h₂ : b % 3 = 0 ∨ b % 3 = 1 ∨ b % 3 = 2 := by omega
  rcases h₁ with h | h | h <;> rcases h₂ with k | k | k <;> simp [h,k]

theorem rough_terminal_set {x b : ℕ} (hx : 1 ≤ x) (hs : x < (b+1)^2) :
    roughNumbers (primorial b) x = insert 1 ((Nat.primesLE x).filter (fun n => b < n)) := by
  classical
  ext n
  simp only [roughNumbers, mem_filter, mem_Icc, mem_insert, Nat.mem_primesLE]
  constructor
  · rintro ⟨⟨hn, hnx⟩, hcop⟩
    by_cases h1 : n = 1
    · exact Or.inl h1
    · right
      have hp := Nat.minFac_prime h1
      have hb : b < n.minFac := by
        by_contra! h
        have hd := Nat.dvd_gcd (hp.dvd_primorial_iff.mpr h) (Nat.minFac_dvd n)
        rw [hcop.gcd_eq_one] at hd
        exact hp.not_dvd_one hd
      have prime : n.Prime := by
        by_contra h
        have hsq := Nat.minFac_sq_le_self hn h
        exact (not_le_of_gt hs) (((Nat.pow_le_pow_left hb 2).trans hsq).trans hnx)
      exact ⟨⟨hnx, prime⟩, by simpa [prime.minFac_eq] using hb⟩
  · rintro (rfl | ⟨⟨hnx, prime⟩, hb⟩)
    · exact ⟨⟨le_rfl, hx⟩, Nat.coprime_one_right _⟩
    · exact ⟨⟨prime.pos, hnx⟩, (prime.coprime_iff_not_dvd.mpr
          (fun h => (not_le_of_gt hb) (prime.dvd_primorial_iff.mp h))).symm⟩

theorem rough_terminal (w : ℕ → ℤ) {x b : ℕ} (hx : 1 ≤ x) (hb : b ≤ x)
    (hs : x < (b+1)^2) :
    roughSum w (primorial b) x + ∑ p ∈ Nat.primesLE b, w p =
      w 1 + ∑ p ∈ Nat.primesLE x, w p := by
  classical
  have complement : (Nat.primesLE x).filter (fun n => ¬ b < n) = Nat.primesLE b := by
    ext n
    simp only [mem_filter, Nat.mem_primesLE, not_lt]
    exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨h.1.trans hb, h.2⟩, h.1⟩⟩
  have one : 1 ∉ (Nat.primesLE x).filter (fun n => b < n) := by
    simp [Nat.mem_primesLE, Nat.not_prime_one]
  have parts := Finset.sum_filter_add_sum_filter_not (Nat.primesLE x) (fun n => b < n) w
  rw [complement] at parts
  rw [roughSum, rough_terminal_set hx hs, sum_insert one, add_assoc, parts]

end SunPrimePermutation


namespace SunPrimePermutation
open Finset

theorem chi3_prefix (x : ℕ) : roughSum chi3 1 x = if x%3 = 1 then 1 else 0 := by
  have num (n : ℕ) : roughNumbers 1 n = Icc 1 n := by ext; simp [roughNumbers]
  simp only [roughSum, num]
  induction x with
  | zero => decide
  | succ x ih =>
    have interval : insert (x+1) (Icc 1 x) = Icc 1 (x+1) := by
      apply Finset.insert_Icc_right_eq_Icc_succ
      exact Nat.succ_le_succ (Nat.zero_le _)
    rw [← interval, sum_insert (by simp), ih]
    simp only [chi3]
    split_ifs <;> omega

def phiEval (w initial : ℕ → ℤ) : ℕ → ℕ → ℤ
  | 0, x => initial x
  | b+1, x =>
    let total := phiEval w initial b x
    if (b+1).Prime then total - w (b+1) * phiEval w initial b (x/(b+1)) else total

theorem phiEval_eq (w initial : ℕ → ℤ) (hm : ∀ a b, w (a*b) = w a*w b)
    (hbase : ∀ x, roughSum w 1 x = initial x) (b x : ℕ) :
    phiEval w initial b x = roughSum w (primorial b) x := by
  induction b generalizing x with
  | zero => simpa [phiEval, primorial_zero] using (hbase x).symm
  | succ b ih =>
    simp only [phiEval, ih]
    by_cases hp : (b+1).Prime
    · have inc : primorial (b+1) = primorial b * (b+1) := by
        simp only [primorial_eq_prod_primesLE, Nat.primesLE_succ, if_pos hp,
          Finset.prod_insert (Nat.notMem_primesLE b)]
        exact mul_comm _ _
      have hd : (primorial b).Coprime (b+1) := by
        apply Nat.Coprime.symm
        exact hp.coprime_iff_not_dvd.mpr (fun h => (Nat.not_succ_le_self b) (hp.dvd_primorial_iff.mp h))
      rw [if_pos hp, inc, rough_split w hm hp hd]
    · have inc : primorial (b+1) = primorial b := by
        simp only [primorial_eq_prod_primesLE, Nat.primesLE_succ, if_neg hp]
      rw [if_neg hp, inc]

theorem character_prime_sum {x b : ℕ} (hx : 1 ≤ x) (hb : b ≤ x) (hs : x < (b+1)^2) :
    ∑ p ∈ Nat.primesLE x, chi3 p =
      phiEval chi3 (fun n => if n%3 = 1 then 1 else 0) b x +
        ∑ p ∈ Nat.primesLE b, chi3 p - 1 := by
  rw [phiEval_eq _ _ chi3_mul chi3_prefix]
  have h := rough_terminal chi3 hx hb hs
  have one : chi3 1 = 1 := by decide
  rw [one] at h
  omega

end SunPrimePermutation


namespace SunPrimePermutation
open Finset

def primeWeight (x : ℕ) : ℤ := ∑ p ∈ Nat.primesLE x, chi3 p

def signedPhi := phiEval chi3 (fun n => if n%3 = 1 then 1 else 0)

theorem signedPhi_terminal {x b : ℕ} (hx : 1 ≤ x) (hb : b ≤ x) (hs : x < (b+1)^2) :
    signedPhi b x = 1 + primeWeight x - primeWeight b := by
  have h := character_prime_sum hx hb hs
  change primeWeight x = signedPhi b x + primeWeight b - 1 at h
  omega

theorem signedPhi_between (x b r : ℕ) (hbr : b ≤ r) :
    signedPhi b x = signedPhi r x +
      ∑ p ∈ Ioc b r, if p.Prime then chi3 p * signedPhi (p-1) (x/p) else 0 := by
  induction r, hbr using Nat.le_induction with
  | base => simp
  | succ r hbr ih =>
    have combine : Ioc b (r+1) = insert (r+1) (Ioc b r) := by
      ext p
      simp only [mem_Ioc, mem_insert]
      omega
    rw [combine, sum_insert (by simp)]
    simp only [show r+1-1 = r by omega]
    change _ = (if (r+1).Prime then signedPhi r x - chi3 (r+1) * signedPhi r (x/(r+1))
                else signedPhi r x) + _
    split_ifs <;> omega

/-- Meissel's signed prime-count formula. All other prime sums need arguments at
most x/(b+1) or r. Choosing b near the cube root of x shortens the sieve. -/
theorem signed_meissel {x b r : ℕ} (hx : 1 ≤ x) (hbr : b ≤ r) (hr : r ≤ x)
    (hlo : r^2 ≤ x) (hhi : x < (r+1)^2) (hc : x < (b+1)^3) :
    primeWeight x = signedPhi b x + primeWeight r - 1 -
      ∑ p ∈ Ioc b r, if p.Prime then chi3 p * (1 + primeWeight (x/p) - primeWeight (p-1))
        else 0 := by
  have split := signedPhi_between x b r hbr
  have finish := signedPhi_terminal hx hr hhi
  have sumEq :
      (∑ p ∈ Ioc b r, if p.Prime then chi3 p * signedPhi (p-1) (x/p) else 0) =
      ∑ p ∈ Ioc b r, if p.Prime then chi3 p * (1+primeWeight (x/p)-primeWeight (p-1))
        else 0 := by
    apply sum_congr rfl
    intro p hp
    obtain ⟨hbp,hpr⟩ := mem_Ioc.mp hp
    by_cases pr : p.Prime
    · have hp2 : p * p ≤ x := by
        simpa [pow_two] using (Nat.pow_le_pow_left hpr 2).trans hlo
      have hdiv : p ≤ x/p := (Nat.le_div_iff_mul_le pr.pos).mpr hp2
      have hp3 : x < p^2*p := by
        simpa [pow_succ] using hc.trans_le (Nat.pow_le_pow_left hbp 3)
      have hlast : x/p < (p-1+1)^2 := by
        rw [Nat.sub_add_cancel pr.pos]
        exact (Nat.div_lt_iff_lt_mul pr.pos).mpr hp3
      simp only [if_pos pr, signedPhi_terminal (pr.pos.trans_le hdiv) (by omega : p-1 ≤ x/p) hlast]
    · simp [pr]
  rw [sumEq] at split
  omega

def semiprimeCorrection (x b r : ℕ) : ℤ :=
  ∑ p ∈ Ioc b r, if p.Prime then chi3 p * (primeWeight (x/p) - primeWeight (p-1)) else 0

theorem meissel_correction {x b r : ℕ} (hx : 1 ≤ x) (hbr : b ≤ r) (hr : r ≤ x)
    (hlo : r^2 ≤ x) (hhi : x < (r+1)^2) (hc : x < (b+1)^3) :
    primeWeight x = signedPhi b x + primeWeight b - 1 - semiprimeCorrection x b r := by
  have h := signed_meissel hx hbr hr hlo hhi hc
  have heq : (∑ p ∈ Ioc b r, if p.Prime then chi3 p * (1+primeWeight (x/p)-primeWeight (p-1))
      else 0) =
      (∑ p ∈ Ioc b r, if p.Prime then chi3 p else 0) + semiprimeCorrection x b r := by
    rw [semiprimeCorrection, ← sum_add_distrib]
    apply sum_congr rfl
    intro p _
    split_ifs <;> ring
  have hweight : (∑ p ∈ Ioc b r, if p.Prime then chi3 p else 0) =
      primeWeight r - primeWeight b := by
    rw [← sum_filter]
    have hset : (Ioc b r).filter Nat.Prime = (Nat.primesLE r).filter (fun p => b < p) := by
      ext p
      simp only [mem_filter, mem_Ioc, Nat.mem_primesLE]
      tauto
    have hcomp : (Nat.primesLE r).filter (fun p => ¬ b < p) = Nat.primesLE b := by
      ext p
      simp only [mem_filter, Nat.mem_primesLE, not_lt]
      exact ⟨fun v => ⟨v.2, v.1.2⟩, fun v => ⟨⟨v.1.trans hbr, v.2⟩, v.1⟩⟩
    have hs := Finset.sum_filter_add_sum_filter_not (Nat.primesLE r) (fun p => b < p) chi3
    rw [hcomp] at hs
    rw [hset]
    unfold primeWeight
    omega
  rw [heq, hweight] at h
  omega

end SunPrimePermutation


namespace SunPrimePermutation
open Finset

theorem primeWeight_succ (k : ℕ) :
    primeWeight (k+1) = primeWeight k + if (k+1).Prime then chi3 (k+1) else 0 := by
  simp only [primeWeight, Nat.primesLE_succ]
  split_ifs
  · rw [sum_insert (Nat.notMem_primesLE k), add_comm]
  · simp

theorem primeCount_succ_cast (k : ℕ) :
    ((k+1).primeCounting : ℤ) = k.primeCounting + if (k+1).Prime then (1:ℤ) else 0 := by
  rw [← Nat.primesLE_card_eq_primeCounting, ← Nat.primesLE_card_eq_primeCounting, Nat.primesLE_succ]
  split_ifs
  · simp [Nat.notMem_primesLE k]
  · simp

theorem chi3_sq {p : ℕ} (hp : p.Prime) (hlt : 3 < p) : (chi3 p)^2 = 1 := by
  have h0 : p%3 ≠ 0 := by
    intro h
    have eqn := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp (Nat.dvd_of_mod_eq_zero h)
    omega
  have hm := Nat.mod_lt p (by decide : 0 < 3)
  have h : p%3 = 1 ∨ p%3 = 2 := by omega
  rcases h with h | h <;> norm_num [chi3,h]

def lowerWeighted (b r : ℕ) : ℤ :=
  ∑ p ∈ Ioc b r, if p.Prime then chi3 p * primeWeight (p-1) else 0

theorem twice_lowerWeighted {b r : ℕ} (hb : 3 ≤ b) (hr : b ≤ r) :
    2 * lowerWeighted b r = (primeWeight r)^2 - (primeWeight b)^2 -
      ((r.primeCounting : ℤ) - (b.primeCounting : ℤ)) := by
  induction r, hr using Nat.le_induction with
  | base => simp [lowerWeighted]
  | succ r hbr ih =>
    have combine : Ioc b (r+1) = insert (r+1) (Ioc b r) := by
      ext p
      simp only [mem_Ioc, mem_insert]
      omega
    unfold lowerWeighted at ih ⊢
    rw [combine, sum_insert (by simp), primeWeight_succ, primeCount_succ_cast]
    by_cases pr : (r+1).Prime
    · simp only [if_pos pr, Nat.add_sub_cancel] 
      have square := chi3_sq pr (by omega)
      nlinarith [ih]
    · simp only [if_neg pr, add_zero, zero_add]
      exact ih

def upperWeighted (x b r : ℕ) : ℤ :=
  ∑ p ∈ Ioc b r, if p.Prime then chi3 p * primeWeight (x/p) else 0

theorem semis_eq_weighted (x b r : ℕ) :
    semiprimeCorrection x b r = upperWeighted x b r - lowerWeighted b r := by
  rw [semiprimeCorrection, upperWeighted, lowerWeighted, ← sum_sub_distrib]
  apply sum_congr rfl
  intro p _
  split_ifs <;> ring

theorem semis_explicit
    (hb : primeWeight 8477 = -12) (hr : primeWeight 780372 = -132)
    (hn : (Nat.primeCounting 780372 : ℤ) - (Nat.primeCounting 8477 : ℤ) = 61432)
    (hu : upperWeighted 608981813029 8477 780372 = -4474) :
    semiprimeCorrection 608981813029 8477 780372 = 17602 := by
  have h := twice_lowerWeighted (b := 8477) (r := 780372) (by decide) (by decide)
  rw [hb,hr,hn] at h
  rw [semis_eq_weighted,hu]
  norm_num at h ⊢
  omega

end SunPrimePermutation


/-! Packed Eratosthenes masks. A doubling step copies the old mask, so only
log₂(width/p)+O(1) shifts build the entire block of multiples of p. -/
namespace SunPrimePermutation

def stripe (p : ℕ) : ℕ → ℕ
  | 0 => 1
  | t+1 => let old := stripe p t; old ||| (old <<< (p*2^t))

theorem stripe_bit (p t i : ℕ) :
    (stripe p t).testBit i = true ↔ ∃ k < 2^t, i = p*k := by
  induction t generalizing i with
  | zero =>
    simp only [stripe, Nat.testBit_one_eq_true_iff_self_eq_zero, pow_zero, Nat.lt_one_iff]
    simp
  | succ t ih =>
    simp only [stripe, Nat.testBit_or, Nat.testBit_shiftLeft, Bool.or_eq_true,
      Bool.and_eq_true, decide_eq_true_eq, ih]
    rw [pow_succ]
    constructor
    · rintro (⟨k,hk,hi⟩ | ⟨hle,k,hk,hi⟩)
      · exact ⟨k, by omega, hi⟩
      · refine ⟨2^t+k, by omega, ?_⟩
        rw [Nat.mul_add]
        omega
    · rintro ⟨k,hk,rfl⟩
      by_cases hsmall : k < 2^t
      · exact Or.inl ⟨k, hsmall, rfl⟩
      · right
        have hle : 2^t ≤ k := Nat.le_of_not_gt hsmall
        exact ⟨Nat.mul_le_mul_left p hle, k-2^t, by omega, (Nat.mul_sub p k (2^t)).symm⟩

def divMask (start p width : ℕ) : ℕ :=
  let offset := start % p
  let depth := ((width+offset)/p).log2+1
  ((stripe p depth) >>> offset) % 2^width

theorem divMask_bit (start p width j : ℕ) (_hp : 0 < p) (hj : j < width) :
    (divMask start p width).testBit j = true ↔ p ∣ start+j := by
  let offset := start % p
  let n := (width+offset)/p
  have hn : n < 2^(n.log2+1) := by
    by_cases h0 : n = 0
    · simp [h0]
    · exact (Nat.log2_lt h0).mp (by omega)
  have modEq : (offset+j) % p = (start+j) % p := by
    dsimp [offset]
    rw [Nat.add_mod, Nat.mod_mod]
    exact (Nat.add_mod start j p).symm
  unfold divMask
  simp only [Nat.testBit_mod_two_pow, hj, decide_true, Bool.true_and, Nat.testBit_shiftRight,
    stripe_bit]
  change (∃ k < 2^(n.log2+1), offset+j = p*k) ↔ p ∣ start+j
  constructor
  · rintro ⟨k, _, he⟩
    apply Nat.dvd_of_mod_eq_zero
    rw [← modEq, he]
    simp
  · intro h
    have hd : p ∣ offset+j := Nat.dvd_of_mod_eq_zero (modEq.trans (Nat.mod_eq_zero_of_dvd h))
    refine ⟨(offset+j)/p, ?_, (Nat.mul_div_cancel' hd).symm⟩
    exact lt_of_le_of_lt (Nat.div_le_div_right (by omega : offset+j ≤ width+offset)) hn

def blockedMask (start width : ℕ) : List ℕ → ℕ
  | [] => 0
  | p :: rest => divMask start p width ||| blockedMask start width rest

theorem blockedMask_bit (start width j : ℕ) (hj : j < width) (ds : List ℕ)
    (hds : ∀ p ∈ ds, 0 < p) :
    (blockedMask start width ds).testBit j = true ↔ ∃ p ∈ ds, p ∣ start+j := by
  induction ds with
  | nil => simp [blockedMask]
  | cons p rest ih =>
    simp only [blockedMask, Nat.testBit_or, Bool.or_eq_true]
    rw [divMask_bit _ _ _ _ (hds _ (.head _)) hj, ih (fun q h => hds q (.tail _ h))]
    simp

def roughMask (start width : ℕ) (ds : List ℕ) : ℕ :=
  (2^width-1) ^^^ blockedMask start width ds

theorem roughMask_bit (start width j : ℕ) (hj : j < width) (ds : List ℕ)
    (hds : ∀ p ∈ ds, 0 < p) :
    (roughMask start width ds).testBit j = true ↔ ∀ p ∈ ds, ¬p ∣ start+j := by
  have h := blockedMask_bit start width j hj ds hds
  simp only [roughMask, Nat.testBit_xor, Nat.testBit_two_pow_sub_one, hj, decide_true]
  cases he : (blockedMask start width ds).testBit j <;> simp_all

end SunPrimePermutation


namespace SunPrimeNumeric
open Finset

/-- One bit every 16 places, for 2^t successive lanes. -/
abbrev spaced := SunPrimePermutation.stripe 16

theorem test_spaced (t i : ℕ) :
    (spaced t).testBit i = true ↔ i%16=0 ∧ i<16*2^t := by
  rw [SunPrimePermutation.stripe_bit]
  constructor
  · rintro ⟨k,hk,rfl⟩
    exact ⟨by simp,by omega⟩
  · rintro ⟨hm,hi⟩
    exact ⟨i/16,by omega,by omega⟩

def lane (t n j : ℕ) := (n >>> j) &&& spaced t

def selected (t n j : ℕ) : Finset ℕ :=
  (range (2^t)).filter (fun i => n.testBit (16*i+j))

theorem indices_lane (t n j : ℕ) : (lane t n j).bitIndices.toFinset =
    (selected t n j).image (fun i => 16*i) := by
  ext i
  simp only [List.mem_toFinset,Nat.mem_bitIndices,lane,Nat.testBit_and,
    Bool.and_eq_true,Nat.testBit_shiftRight,test_spaced,Finset.mem_image,
    selected,Finset.mem_filter,Finset.mem_range]
  constructor
  · rintro ⟨hh,hm,hl⟩
    have he : 16*(i/16)=i := by omega
    exact ⟨i/16,⟨by omega,by simpa [he,Nat.add_comm] using hh⟩,he⟩
  · rintro ⟨k,⟨hk,hm⟩,rfl⟩
    exact ⟨by simpa [Nat.add_comm] using hm,by simp,by omega⟩

private theorem residue_length (xs : List ℕ) (h : ∀ i∈xs,16∣i) :
    (xs.map (fun i => 2^i)).sum ≡ xs.length [MOD 65535] := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    obtain ⟨k,hk⟩ := h a (by simp)
    have hz : 2^a ≡ 1 [MOD 65535] := by
      rw [hk,pow_mul]
      simpa using (show 2^16 ≡ 1 [MOD 65535] by decide).pow k
    simpa [Nat.add_comm] using hz.add (ih (fun i hi=>h i (by simp [hi])))

def countLane (t n j : ℕ) := lane t n j % 65535

theorem countLane_eq (t n j : ℕ) (ht : 2^t<65535) :
    countLane t n j=(selected t n j).card := by
  let b := lane t n j
  have he := indices_lane t n j
  have hi : ∀ i∈b.bitIndices,16∣i := by
    intro i h
    have hm : i∈(lane t n j).bitIndices.toFinset := List.mem_toFinset.mpr h
    rw [he] at hm
    obtain ⟨k,hk,he⟩:=Finset.mem_image.mp hm
    exact ⟨k,he.symm⟩
  have hc : b.bitIndices.length = (selected t n j).card := by
    rw [← List.toFinset_card_of_nodup b.bitIndices_nodup,he,Finset.card_image_of_injective]
    intro x y h; change 16*x=16*y at h; omega
  have hs : (selected t n j).card≤2^t := by
    simpa [selected] using Finset.card_le_card (Finset.filter_subset _ (range (2^t)))
  have hh := residue_length b.bitIndices hi
  rw [Nat.sum_map_two_pow_bitIndices,hc] at hh
  change b % 65535 = (selected t n j).card % 65535 at hh
  exact Eq.trans hh (Nat.mod_eq_of_lt (lt_of_le_of_lt hs ht))

def wordCount (t n : ℕ) : ℕ := ∑ j ∈ range 16, countLane t n j

theorem wordCount_eq (t n : ℕ) (ht : 2^t<65535) :
    wordCount t n = ((range (16*2^t)).filter (fun i => n.testBit i)).card := by
  let s := (range (16*2^t)).filter (fun i => n.testBit i)
  change _ = s.card
  rw [Finset.card_eq_sum_card_fiberwise (t:=range 16) (f:=fun i : ℕ=>i%16)
    (fun i _=>mem_range.mpr (Nat.mod_lt _ (by decide)))]
  unfold wordCount
  apply sum_congr rfl; intro j hj
  have hj' : j<16:=mem_range.mp hj
  rw [countLane_eq _ _ _ ht]
  apply Finset.card_bij (fun i _=>16*i+j)
  · intro i hi
    obtain ⟨hk,hh⟩ := Finset.mem_filter.mp hi
    have hk' := mem_range.mp hk
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_filter.mpr ⟨mem_range.mpr (by omega),hh⟩,by omega⟩
  · intro a ha b hb hab
    omega
  · intro i hi
    obtain ⟨hb,hm⟩:=Finset.mem_filter.mp hi
    obtain ⟨hlim,hh⟩:=Finset.mem_filter.mp hb
    have he := mem_range.mp hlim
    have eq : 16*(i/16)+j=i := by omega
    exact ⟨i/16,Finset.mem_filter.mpr ⟨mem_range.mpr (by omega),by rwa [eq]⟩,eq⟩

/-- Signed character sum of bits strictly before offset k, inside one fixed-width block. -/
def signedPrefix (t start mask k : ℕ) : ℤ :=
  let w := 16*2^t
  let pos := mask &&& SunPrimePermutation.divMask (start+2) 3 w
  let neg := mask &&& SunPrimePermutation.divMask (start+1) 3 w
  (wordCount t (pos%2^k) : ℤ) - (wordCount t (neg%2^k) : ℤ)

end SunPrimeNumeric


namespace SunPrimeNumeric
open SunPrimePermutation

abbrev x0 : ℕ := 608981813029
abbrev cutB : ℕ := 8477
abbrev cutR : ℕ := 780372

/-- One half-open q block covers smaller-prime summands in (cut(s+w),cut(s)]. -/
def cut (s : ℕ) := min cutR (max cutB (x0/s))

def scanBits (f : ℕ → ℤ) : ℕ → ℕ → ℕ → ℤ
  | 0, _, _ => 0
  | count+1, start, mask =>
    (if mask%2=1 then f start else 0) + scanBits f count (start+1) (mask/2)

def cellEval (allDs : List ℕ) (smallBits t s : ℕ) (base : ℤ) : ℤ × ℤ :=
  let w := 16*2^t
  let ds := allDs.filter (fun p=>p*p<s+w)
  let mask := roughMask s w ds
  let hi := cut s
  let lo := cut (s+w)
  let bits := (smallBits >>> (lo-cutB)) % 2^(hi-lo)
  let f := fun p => chi3 p * (base + signedPrefix t s mask (x0/p-s+1))
  (base + signedPrefix t s mask w, scanBits f (hi-lo) (lo+1) bits)

open Finset in
theorem scanBits_eq (f : ℕ → ℤ) (count start mask : ℕ) :
    scanBits f count start mask =
    ∑ j ∈ range count, if mask.testBit j then f (start+j) else 0 := by
  induction count generalizing start mask with
  | zero => simp [scanBits]
  | succ count ih =>
    rw [scanBits,ih,Finset.sum_range_succ']
    simp only [Nat.add_zero,Nat.testBit_zero,decide_eq_true_eq]
    have he (i : ℕ) : (mask/2).testBit i=mask.testBit (i+1) := by
      simpa using (Nat.testBit_div_two_pow (n:=1) mask i)
    simp only [he]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    have hh : start+1+j = start+(j+1) := by omega
    rw [hh]

end SunPrimeNumeric


namespace SunPrimeBare

def ds : List Nat := [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113,127,131,137,139,149,151,157,163,167,173,179,181,191,193,197,199,211,223,227,229,233,239,241,251,257,263,269,271,277,281,283,293,307,311,313,317,331,337,347,349,353,359,367,373,379,383,389,397,401,409,419,421,431,433,439,443,449,457,461,463,467,479,487,491,499,503,509,521,523,541,547,557,563,569,571,577,587,593,599,601,607,613,617,619,631,641,643,647,653,659,661,673,677,683,691,701,709,719,727,733,739,743,751,757,761,769,773,787,797,809,811,821,823,827,829,839,853,857,859,863,877,881,883,887,907,911,919,929,937,941,947,953,967,971,977,983,991,997,1009,1013,1019,1021,1031,1033,1039,1049,1051,1061,1063,1069,1087,1091,1093,1097,1103,1109,1117,1123,1129,1151,1153,1163,1171,1181,1187,1193,1201,1213,1217,1223,1229,1231,1237,1249,1259,1277,1279,1283,1289,1291,1297,1301,1303,1307,1319,1321,1327,1361,1367,1373,1381,1399,1409,1423,1427,1429,1433,1439,1447,1451,1453,1459,1471,1481,1483,1487,1489,1493,1499,1511,1523,1531,1543,1549,1553,1559,1567,1571,1579,1583,1597,1601,1607,1609,1613,1619,1621,1627,1637,1657,1663,1667,1669,1693,1697,1699,1709,1721,1723,1733,1741,1747,1753,1759,1777,1783,1787,1789,1801,1811,1823,1831,1847,1861,1867,1871,1873,1877,1879,1889,1901,1907,1913,1931,1933,1949,1951,1973,1979,1987,1993,1997,1999,2003,2011,2017,2027,2029,2039,2053,2063,2069,2081,2083,2087,2089,2099,2111,2113,2129,2131,2137,2141,2143,2153,2161,2179,2203,2207,2213,2221,2237,2239,2243,2251,2267,2269,2273,2281,2287,2293,2297,2309,2311,2333,2339,2341,2347,2351,2357,2371,2377,2381,2383,2389,2393,2399,2411,2417,2423,2437,2441,2447,2459,2467,2473,2477,2503,2521,2531,2539,2543,2549,2551,2557,2579,2591,2593,2609,2617,2621,2633,2647,2657,2659,2663,2671,2677,2683,2687,2689,2693,2699,2707,2711,2713,2719,2729,2731,2741,2749,2753,2767,2777,2789,2791,2797,2801,2803,2819,2833,2837,2843,2851,2857,2861,2879,2887,2897,2903,2909,2917,2927,2939,2953,2957,2963,2969,2971,2999,3001,3011,3019,3023,3037,3041,3049,3061,3067,3079,3083,3089,3109,3119,3121,3137,3163,3167,3169,3181,3187,3191,3203,3209,3217,3221,3229,3251,3253,3257,3259,3271,3299,3301,3307,3313,3319,3323,3329,3331,3343,3347,3359,3361,3371,3373,3389,3391,3407,3413,3433,3449,3457,3461,3463,3467,3469,3491,3499,3511,3517,3527,3529,3533,3539,3541,3547,3557,3559,3571,3581,3583,3593,3607,3613,3617,3623,3631,3637,3643,3659,3671,3673,3677,3691,3697,3701,3709,3719,3727,3733,3739,3761,3767,3769,3779,3793,3797,3803,3821,3823,3833,3847,3851,3853,3863,3877,3881,3889,3907,3911,3917,3919,3923,3929,3931,3943,3947,3967,3989,4001,4003,4007,4013,4019,4021,4027,4049,4051,4057,4073,4079,4091,4093,4099,4111,4127,4129,4133,4139,4153,4157,4159,4177,4201,4211,4217,4219,4229,4231,4241,4243,4253,4259,4261,4271,4273,4283,4289,4297,4327,4337,4339,4349,4357,4363,4373,4391,4397,4409,4421,4423,4441,4447,4451,4457,4463,4481,4483,4493,4507,4513,4517,4519,4523,4547,4549,4561,4567,4583,4591,4597,4603,4621,4637,4639,4643,4649,4651,4657,4663,4673,4679,4691,4703,4721,4723,4729,4733,4751,4759,4783,4787,4789,4793,4799,4801,4813,4817,4831,4861,4871,4877,4889,4903,4909,4919,4931,4933,4937,4943,4951,4957,4967,4969,4973,4987,4993,4999,5003,5009,5011,5021,5023,5039,5051,5059,5077,5081,5087,5099,5101,5107,5113,5119,5147,5153,5167,5171,5179,5189,5197,5209,5227,5231,5233,5237,5261,5273,5279,5281,5297,5303,5309,5323,5333,5347,5351,5381,5387,5393,5399,5407,5413,5417,5419,5431,5437,5441,5443,5449,5471,5477,5479,5483,5501,5503,5507,5519,5521,5527,5531,5557,5563,5569,5573,5581,5591,5623,5639,5641,5647,5651,5653,5657,5659,5669,5683,5689,5693,5701,5711,5717,5737,5741,5743,5749,5779,5783,5791,5801,5807,5813,5821,5827,5839,5843,5849,5851,5857,5861,5867,5869,5879,5881,5897,5903,5923,5927,5939,5953,5981,5987,6007,6011,6029,6037,6043,6047,6053,6067,6073,6079,6089,6091,6101,6113,6121,6131,6133,6143,6151,6163,6173,6197,6199,6203,6211,6217,6221,6229,6247,6257,6263,6269,6271,6277,6287,6299,6301,6311,6317,6323,6329,6337,6343,6353,6359,6361,6367,6373,6379,6389,6397,6421,6427,6449,6451,6469,6473,6481,6491,6521,6529,6547,6551,6553,6563,6569,6571,6577,6581,6599,6607,6619,6637,6653,6659,6661,6673,6679,6689,6691,6701,6703,6709,6719,6733,6737,6761,6763,6779,6781,6791,6793,6803,6823,6827,6829,6833,6841,6857,6863,6869,6871,6883,6899,6907,6911,6917,6947,6949,6959,6961,6967,6971,6977,6983,6991,6997,7001,7013,7019,7027,7039,7043,7057,7069,7079,7103,7109,7121,7127,7129,7151,7159,7177,7187,7193,7207,7211,7213,7219,7229,7237,7243,7247,7253,7283,7297,7307,7309,7321,7331,7333,7349,7351,7369,7393,7411,7417,7433,7451,7457,7459,7477,7481,7487,7489,7499,7507,7517,7523,7529,7537,7541,7547,7549,7559,7561,7573,7577,7583,7589,7591,7603,7607,7621,7639,7643,7649,7669,7673,7681,7687,7691,7699,7703,7717,7723,7727,7741,7753,7757,7759,7789,7793,7817,7823,7829,7841,7853,7867,7873,7877,7879,7883,7901,7907,7919,7927,7933,7937,7949,7951,7963,7993,8009,8011,8017,8039,8053,8059,8069,8081,8087,8089,8093,8101,8111,8117,8123,8147,8161,8167,8171,8179,8191,8209,8219,8221,8231,8233,8237,8243,8263,8269,8273,8287,8291,8293,8297,8311,8317,8329,8353,8363,8369,8377,8387,8389,8419,8423,8429,8431,8443,8447,8461,8467]

def stripe (p : Nat) : Nat → Nat
  | 0 => 1
  | t+1 => let old := stripe p t; old ||| (old <<< (p*2^t))

def divMask (s p w : Nat) : Nat :=
  let off := s%p
  ((stripe p (((w+off)/p).log2+1)) >>> off) % 2^w

def blocked (s w : Nat) : List Nat → Nat
  | [] => 0
  | p::ps => divMask s p w ||| blocked s w ps

def rough (s w : Nat) (ps : List Nat) : Nat := (2^w-1) ^^^ blocked s w ps

def sumN (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | k+1 => sumN f k + f k

def count (t n : Nat) : Nat :=
  sumN (fun j => ((n >>> j) &&& stripe 16 t) % 65535) 16

def chi (p : Nat) : Int := if p%3=1 then 1 else if p%3=2 then -1 else 0

def scan (f : Nat → Int) (s : Nat) : Nat → Nat → Int
  | 0, _ => 0
  | t+1, m => if m=0 then 0 else f (s+m.log2) + scan f s t (m%2^m.log2)

def cut (s : Nat) : Nat := min 780372 (max 8477 (608981813029/s))

def window (lo hi : Nat) : Nat :=
  rough (lo+1) (hi-lo) (ds.filter (fun p => p*p ≤ 780372)) % 2^(hi-lo)

def cell (t s : Nat) (a : Int) : Int × Int :=
  let w := 16*2^t
  let m := rough s w (ds.filter (fun p => p*p < s+w))
  let hi := cut s
  let lo := cut (s+w)
  let pos := m &&& divMask (s+2) 3 w
  let neg := m &&& divMask (s+1) 3 w
  let rank := fun k => (count t (pos%2^k) : Int) - count t (neg%2^k)
  (a+rank w, scan (fun p => chi p * (a + rank (608981813029/p-s+1))) (lo+1) (hi-lo) (window lo hi))

def checkRun (t s : Nat) (a : Int) : List (Int×Int) → Bool
  | [] => true
  | (b,n)::xs => (cell t s a == (b,n)) && checkRun t (s+16*2^t) b xs

end SunPrimeBare


namespace SunPrimeBare.Binary

def locate (m : Nat) : Nat → Nat → Nat
  | 0, lo => lo
  | d+1, lo =>
    let pivot := lo + 2^d
    if 2^pivot ≤ m then locate m d pivot else locate m d lo

def highest (d m : Nat) :=
  if m < 2^(2^d) then locate m d 0 else m.log2

def visit (d : Nat) (f : Nat → Int) (s : Nat) : Nat → Nat → Int
  | 0, _ => 0
  | t+1, m => if m=0 then 0 else
      let j := highest d m
      f (s+j) + visit d f s t (m%2^j)

def cell (t s : Nat) (a : Int) : Int × Int :=
  let w := 16*2^t
  let m := rough s w (ds.filter (fun p => p*p < s+w))
  let hi := cut s
  let lo := cut (s+w)
  let pos := m &&& divMask (s+2) 3 w
  let neg := m &&& divMask (s+1) 3 w
  let rank := fun k => (count t (pos%2^k) : Int) - count t (neg%2^k)
  (a+rank w, visit ((hi-lo).log2+1) (fun p => chi p * (a+rank (608981813029/p-s+1)))
    (lo+1) (hi-lo) (window lo hi))

def checkRun (t s : Nat) (a : Int) : List (Int×Int) → Bool
  | [] => true
  | (b,n)::xs => (cell t s a == (b,n)) && checkRun t (s+16*2^t) b xs

end SunPrimeBare.Binary


namespace SunPrimeNumeric

def ds8500 : List ℕ := SunPrimeBare.ds

def expandSix (bits : ℕ) : ℕ :=
  (List.range 17).reverse.foldl (fun x i =>
    let k := 2^i
    let low := (2^k-1)*SunPrimePermutation.stripe (12*k) (16-i)
    (x &&& low) ||| (((x >>> k) &&& low) <<< (6*k))) bits
def laneOne : ℕ := 0x1000214841002a01400520431a4404098408000208e80012020c2000485311814090269082508c00080620002280850844040123408680002443420014a12208218169038012984052400021040010f088480a002108a0619025204460020108290a1c4204c208884020c2020c0118020052020502215640b825011400188c03920300800a08003024501844050820c80104225050800004030440b044024000380130802480a06098110140080062880a2002c41d0651082481440202c008240258b604080910018000184433100a08181081c1500a078144110021200c110434100063442428a5101460898440400285c1100052242000808211204818870088200000b8402a042118415a00400106300041842902902404e0300001050801423201ca280a30080100121024c851024100886080010108401c40a52943c0512c40709080010c034c54800100022204880340868d021890408480410626208113828410620912520140301a3110000804001c484000a70102284400802b19800030886048901400280061284001444481800108170c043110c208205ad0a31400088e3010ea21000280000010652c83025c401882000a0030a0010024842870440114c102901094090102442044408252a081131005008160480410c00286410c0408401011001810022100530c818420010a4205093010050804009004300910940008894208a2840b0098421843000a84942000407005422248c0092020948110856884440c005058108501430404116830040020407050158809080ae00064000a8110092110079406028442104a0a140201c3020c8520003140718c8213064108600900022848085602048210800000800300728802404246140c68022680420006d090444080a1380400464280295a80f1218e1008128040400885100020925401092a424001804104861c6109106411024008a021004210323803600042390020488100cf10060199a161082000e140028314030000a0008d0a022004c00200043c005802a101412040b000a420140100044204608485404090000100000088000342c79c08501a002c000b1074980142dc0000a930004680830280930086500600a560000602280821804220c4181251a004200000288160120380a00050c10041090006940b0202020d04600a4420c00018d1108009483524640890a10422080040304452825621a011c050a004000081080a301040a8842290120080394044050c788c1190440002240900000011a16e0018c0014121542429272202160888004080052130c45104ea420e4485a1120040184070002009850a048010a6014801082448148300a0105010810a401c168082028654000e1100a0a9080308108020201002040502c6a20980000052a56458984014c0430002210050c89200803818802146438c00308530800501044880200001020a5415c3000400012e38d0120c04304210094040082404e94a508014a05000318002010022a0092048010820605041094b000a00802540109108e80b1040102d0000028441009004a1001380150c680002e42c04310880104002c01200400010a00526200080a18308080411023184c0056a3058078080034404008760022320e043100580201a1882052948901400aa3304d01c004808302880005244a141028a35080032102114010a40c01000110220800000065284647092b10c07094a2120840182050440081063812c2a4813040052161201a16248d4010a21000608800814653121085000080038166008a440080214620900001400304005010408c010094102109010420040942001734000818a42848014c142024005082300040800298000010c131cc0a88048d2052808298024100e02584130010314028061404804880a190000a0041110d400a200022010c0018002050c22c40120c9181c1020424002152406500033a4042844e128024910241400204203088a52c8312508038064104a0004041064288084ad0b11501400840910a1148c03c246082000108210261a125028282140c08d403082108183080a600803418c0410012104009102288040900403104424291108d128421000f30004100431112060003014012254008802080c8020a6080400080a02c40391224058c329050a06d00005201006006c000425002c10985230480198248580108a918028400005a4800842043822018aa420814180008c09584821a04d00026081810088030840281003200f02581428840058050040100000900108501224a012984699284086840008114842080b0a102081c328801430c441102084085884019400018822280900429230407110928c4b200821980440060600a028002584026050931500000062098102c014010838005401c03916111060080213308908848214860850010046088c46b081200200216040002481090312a481a00344012c4c2b9000040850943001c1030420048b1208500062700a01a0041a180190034218270c205840c3002e208040100a119224100a214204904818020480413a4c05a1210a0094080009c062010c38401204080012422841030c90140200109088c2080a0130a1201c21000140044510820010a22446480800a161020610302200880104cb0810b400602186a0286129402314826280808141110440a420130400850200126488860144a010054a0a172c412100228c01004850118a001822200a234080a44c40008401c60202900981628a8408090082469d002a0080a18b1000600140224c062808008061a40211005518a000da020000011221882640c000310518001200004280c408020050d10c0039402510e00300a434840906410081320043844c1880162001104684a50a0880c120400144843005088e06100c08046401ab22d46100e04a18608d200182c22908514851058003065430064800b108a0694281100822d0a21022011c0008415080410044600a000405001c0101c20a4e01342010442000022000000444409004044942c086040a4982140004181a109801001813004522940008a800cc01a526100052002940440431402840540801085020804002108720805a52050c801800b23100138a501d620104400800601004200d030a91198440463304014102010022200450908452880084004284501848008092214201049101042992b008484050001ca070044201ea10800094814002d180203840802148024250898301d2072000100400002c400081214409062480a0508000a562098052a0840042c0802040829034093084e10129201c40002202040425c1610c400804281824280e1110040101605a04048832c002050c02c01330a64a8414802a00084008264000b7884021044020210b46a0100802524080041080b180e24018221189108015040c180841844403044520c14298800820010240008640880180430b002600482202020d4a300245a1482000d5280308922018e02906249000080892240c488c24048240420208225140c00883110800918162042308011b1204018702c002040008080010281300c6250408088000c018528029060018902865001401010012c4d010200018201040120081000630c024844920143000e440001120a51140a2092050900284a840162030600304c1004048828680020b0c059884414a1000010800e010840010a2b00b001e440c693304032c2a485261208219182010a22848830848000021810208409110a85384440483034e04802001124001082814a0a0404004140c280894c29c0200d803006501020085a0010643b10208c09480040200950000080814140c42d20209a0500822052801100488c313000085202100808480104a21298700400120082390021400424c203140401446086a000455142801c086808a100800004000c4a608054b802104213298e00405099a000943214683200a101880000c28580100402200801085210085852a20c4320108400802004a108442800039d07281082010c090e50a0a0010210854260402501461142e000862048200c2013020404060040c21169400804214a0284020002419030ac4330581088406042b0040c10d042090010108020601004300542030804800051000620810140f4284621589510085ac040840800006105020282448881600e04202c015a618c80220a4039062002800c486090430029221c231406021000000851420101621840e3050508000101e2009200000519c06011a340048215001304040841200412054228c2508d00210861300209880024cc40c680002c2a0c011064420870800222cc5621424048800480001061016109000220003390c2848102140120ad1004402808408047182c21c8802448094210900401880434804a02049180584010800211106000617340021c2029120485402a0e64016108081420210080c40480001ca1008a0a0a403d2060004028660050120080004085202342800418690104e00009001432040911882280005204c1a04c1882212401005834a1046084b1384c2a504111072880408003090a04b0280004149842101282080c031240a186011012000c0290c0040a008850010a49901410200044001828498006080530049120602140911008004622990b005c208000021600a849704a13a8242980300004031a012103008cb40084591000110642d40011200a821221000000901502108091854a100400a1c0081212288108542605012280c0302e02102409e8404c018024504ab0244602144021814a120108002004451888620410104141002294402302541c0c110022080020000510a1081aa01028301604048a220411802600945628a0400081000a39c051010e230810810022560438a82206e00880101c5000410804300848420042180000ca10048a2854e09020485805102012800501044000409003400c240023020807a42210027688ce2810400144028e051c0013822604a0188010b5404200108408024816a026600240a040224010180643028600c82900619180124022808c1210020080400a0190200850b008c030008401400a981238042804c009a1300810100240062481894040c40002084084240e024000380002de0708a840140300ac1080102104008002140021c48101206108a100810812109823028e24180412028018897854212401010400140262c415a040201206a40e09001118810880a134a41894c18808024840112042804401a00340100500715a008401030000116421440038091ac00008281014c210204212460c02100286102a00986229040048d1a06120008300890182a41d2452841215c8010204002220c4841104700275008418023100404218020425614601912e3a90408408030814a94200c05428665008508487014020080043500100481a04040d8818084204c8431054a0c0418ac001642912a0844c220cb0b0224000850840208201800342488081844282500129400a4105600110c4018a001805818000003138040340000d0308080290a01118308109404412004210c8572105010600280300400210c94040a29086080020a109089a642540110c022c0241905708c2204201b00063c60208216b80a68025200cc110214204402482220cd10c0a0018e381023840448842200011088d00904000af4040703009109c2401c20208000940080041000020428031a00b88002c240192050801405ca324c0120202ac00600a41840c0802142cc9001001102240043210e00382a314240090318484108a521142238291a0285040630143311c00a083008224140169000280803a04602006080862142a404c84040640100201000050608964401285006423840584834040d104021a022429c9100000014020c852014530108408c50b0881300c0004a5900a2088c221614018001c810000968124218210000a114a3011810850200c0420d022000c600002a025508620106a030840292049100484843002512846405820040538c084100a300040200110020080e1020446216008d2a4000d0a5804884069008610e00b9224088440403201284916108041620011a920680202084e280c95102560000208204250c290003250a204854192020921400040340a08807305440940111004428480200128044011831ac80020c34b8070a481000e9180087050010102000600884120c4100ca110962608074800720045000c06a46a114000a44820404004061214c0a0e0210a213c01029026090100080031441000401809300e10200431828204481a42801000011c101048689001100202582184440280122181634a1409224090320c8108048000222944002040210401018800108310c20212003d2040828330461892c2880101502000a3681e1628cc138004000930840101830a0844000a00805698046840260c80020ea09024010284286001148290004a440100004180449401004012802c00c080a002000004896240468420a4305486098648101181e44090422460104012300040c2202004101210a8622000002c8400904701a750442084081104141842630885080a00c24288ca02140580412b0c110c0d02108104a460c0100084580c303008030852a0064002548880114010810300008314896006a41024100410a082410c040889430252a00201c280058918009021402280b0104843806008016044c120c308025405805208c48c0268080224c10a143030022902010444011600100c4010302009400e009148108a52854e0848a004003002019900480204242561044000013a00c28401038414814b6104122400189013888e00408009040940803004119223050640440030a3021000018001c0c4002a1002f684c8011221808001040420c869846408204004500023081840014360860084046940212505211c11000300d016280043c441082c4204b080a810040080630102901d0060923020813306500862481200004049102090822a000231080a04522080100e810040580000ac0500422581810150223848081462040100186384e8431a20104000004614400802a305421a4ce0290563103000842256c10885380c5020204190240128014200304820008001412108650104400800348c085004082b18c8900104100642a5000048c725003082800981080a00200022482018411200a205a1000480b400131a408c283080030068011a0620ca0012319180000c3224400880001c002200c291040384102c82314a068100700040a1882044e018000896270000700643880440589014a2100822108a004c53000601504025c10010112085200881180410c04290280a40c020210112620000508c00840c6900120087020030092208cc0214246b06000c0922102134404a88100828528081142a2098b680803818610004295606384401464001800a800220e01282602181300481104008d2a0a90621108408432082070808200200910522446011a2080a6021092080c42502101a20000c1a009130414802371c000890a48400789401902e0804220142400a812000114ae42d002000d0102201548008c82144440884508c1220641288108c43030812100c59808004402a0c1020214018940ca450920100a10004b0010e020e140da00106c138081800562447124821a18442022628a10a1063118f104080002e1090428822204444000008c05200c12300808000610c1410610a52009580229022200c4884628c29018010a02850d890000908142101c60000a030412a90a4002658085080a8098444208112400108205040462cc508005020c562142308413092628c85109800154811881024006308809c044850138902181e9121410108210c087102e080082210a39164028212104b0304002400200205248b000841088620508100a8489640002200cc112404400200a0a80088543108010297000b2140c1218520528000480b400205a510008100404090123980208a05250a581032810f004c111823209401006150044008044284810063490a00b14902c6541040315850000133102100c200c0220800080205040a52483030600a080480220042039902104080a808014020880121448110010384269007688c518109001830204012085220225098a701c40a00a119004804b330a102144410041a0400312a411e028c404006060504218042210f1942140024010a022808425002092b400430a5a8020040a9020088018d0400c08220411a008420036012061c010000401500304020214b0014262501008a00986a085216204600102400040bd831084448804311a21ac01100660b08040880308492086070400101892050d4894520060500252012e08081480051102e0010020000010603180440c8220d42204a05182000ca840400128044808b1840a01420010416390060880420481910300884090a11198020581204883094819804088023202448140200e34302808c0041080580cb111ce0b1000040020c854302208c040804b13064010206180160c21030400082a089460b10108083424c0110a46142600924600c000429100c002902034410100818ca06a14110040008000012a0140850c08510041848f0004100844224433280c408244808a10808124045082100462410443154c480885200238544090c440021028044216e3808068580024a8108440180910ce43042c509002004000020010a241449730000000a2042c60480081a20a020031a8228a140c025112900c000b1041092528069004446040468d0148084324095310120080114085800240c87021080808242004004816280913404019a450540001405804240080118684b00239903129882a122020040a82930884501602840002c401044b020404146040081419480940d1008e0048d509800910050c0031904418813084730028000844a00300021121022900200588220a80210501c420346138828098885248018505000a6688c0404a010160190014250830181480a422142414485a40e4008a40508080c610840090200240d09142500a0420083008c4882043c6060800615200010b281432a148488a06a0c0238890ac4211d830048a2010a0012400803028004884e00404788040900a490e409480120c800420081204810d0002c0308060d034044d20160710a60080c3200010842481426140109c0221d08104c4084e9100e3210c042ca47014449c2b72000200840082108000708c412c686802828c4100120039c021c02100040004a201280814630106429810112060c690140420c01008c809402008c0008410244159500088841a804014095000403062218a1030281040330d4a010030012402588200081880600103601003006001002220011242800040405a4601402b08250825420230040c109083058e40d4c120040908102422328a0490480882450102105a7580a2030c012000304080840c009050004c410e4208430180161120011a90a4ca11102030470858000420500281092220080030840282220429024406880408808221c108406088406b983014c44b8284010008440031081990022d03030845ad401040c08008384251b02241988110404a528004a23000b2200e00082400c15304c2a44600588501c418020100c208500000450b0081092120845090664b8820100200420095480050050c802014049001291403048010008210a00a08421063400002800800400124604088230842300044892001020120a05082648c804000a120ce1302403049200611a104190a26a4010a4284204520043720e0290641800a48c4401127128c04008860c28101043040618c40020cc008c20a5410184170046400240a140120ca1a184031a121028284062802912805034490a1644042011028014680058c30100301014a0224118001424090085888232088280630a00640109000a16940820408089c408008011022a042728c02a000310010288700586000014802a304610244640902025810044018046220c85080d6212a41da80854603046110614300202844089640910c504840a123138c520029500c002424000202094c095c0020e12218b02468180267048448440101a01802322901408812382208104488c7190491b8860044140c20281080080912c0520046129620ada0430e441004410802048221140000402880921c6821800301a5020491304a1a00749c2052004108004148a004070200f4308008080404603b8041908b40108220070802340082138293210e200020a102205894814642c23010a0120600052022484014a01290142d01400a028004280844080a0848202065400004346c40c08301022290103001400e50004a200450a4047102d10848081600b9440004a420003bc64680056a8460a0680002700101108811010c008ae0a0400040119023409a8000256182041180129442808a101006052a0040020400489221a5c1280840188208188200650102001106104cc0900a0800108000700e07a06e6140040886000015102349180528081244a08404004853840d019a520c0040c05008683080252040185a2081024308001c847a100099001204b0158f001a04910a1244c1104a10020000812a5e112101020890008c0bd0410d8010c8218486489020282960005130404098c22043380240008061482110892004041409104020154d1880000440610886a4444858110904091015b14223808020284880068482100493908840880024214384100c20291a64898423100021c122d612088d2090a610070a00930462008804b0e2410800884c0140710080020c4488050bc081040840d46608a1000c0001401b00209943518a542904510a9000821200a40081684e0110205204011c0620043120210292403140108a85010021002385020048a099200044060081000027082942004024231818002cab200690100a18025128040004c520644012001805030005180f40c012912b10004494c2210006040e001821014821049020c1400801046910008681a2228041100a0018508c02400010a82048c2e100043248840881200ea5044429c246818d40007080250094502822118a0004040042a424c0100e5100400318263425488481018c100831310842003018020108061c4201d0500000231434886400040620205092201525085801040412923004202240d1180430401209c8110ec009226014a40080420682048e104080808c4110208521700005a84a01c221040428421180620b9813100d20c4c1880012588010c6030404b5a8034a060540495a00a0832014040900281c10048940902018291800e020255908000080710a13104801583028440a4e5001032b0804200c7012208000520403a00c1b00421d022280160c203010f4000d000830190348c083008020124181012080821086000c0201490200112800105080058a1a4480800329408410c02b5041880050807014200192360d210088118568005a81a940281c81880320c80428401a0041142a700c32016809026021a31000441442380004044008020410e60b500600e4388482102052140020070104102402120250380068882408831012c1810021128210280182249c0a0a106000c00b00621020018095240640401581841300a0080469082624a04894820080128441818a12124018826046049504211004800e2b0851000040001104484a800219a618400004c811802208014040c38c0258108509cc204270098100c03014c04912e5042008142030c51018508c01300047100e19c0c4288830102081a6280420002402142701042280c1a16d030220188222820180287008650c813140001004610235280d62062300050840a1008b090000806a2042802c02409000084002500031a148cc1414050200000d82281043100e08807095400002030140088af480820a081430a20008012008085243042820940300414888521808300814840400104300c20204e520020214942c0151426285202000a0a0a55a004020e2300686a44039801100430118a010c240da871801690280050b6200c0844a121e06080020c0060948008800a580081c2528600188151c80294402142802040120290a103004004282c091067908300d0300066418a10140003040021280808d50cc0280a509840600801308412044114000a4401840718102611012208462060218280000a02021009210084b030ec0040a1000902400185a00816442108528854100811820089c103160010c50a003204055a80010d84681800240210084438e0710686150200020021050a5084318102948320240ac20100042214c0000151002218a201009624404188602489221e40880448820004017194a6800612105110644008003521208e17002c48c871800b02082108022a402100840a12a210046a8003040142043604a1000804300c4952a320ca080050a8210058052405304640000a02843090284380328923034605a40c10d02028c409007008402880140848020247100b6818a01004501470156a0140011c00685010290c0040e42026015c011ca01004078824008050b108500206044102044620060812a50dca3940148004614c90000142d40090203a9880b02018063005024084821c0a7018618c431140040041420a0620404812231823021052254000900004c023c28380042080560c01284001014149408014a033066408a018400020091810220d80100c00a4206190408440000aa011c101560230205b84a08424000453a0c54000448902738084a8043088160102320e8488620900b018410104008d091018b2b002000802044811441594480010020d052844440024008a93306433406189000090a014e2001200a5c80180820408505206a0800a122080210318a1104d20c084100628040315270b101000a2208a801108280025008801064480202a4ca120c400c2401d82684040a0c0130c42082103c006282220001000ca085c10200220dc212c05200404180942040184055300009c08020e0000021142548080205020a804488812140c439281110860009315e04904201042610c00992410000021c8004891a900618624086041004680070284321081480426a8891102c6002008c0a22880105a141180024223140c20c08214005000923102480e04158b630a801d4a1048430100190640b0006086040ca44194a0008400c04031a4011c348428318cc280420188270400220094a0802946b4242910526208a24200e025470812001d01008c100004400061004019120020c461d200048002c262010d4840811440020c1229a0428015002e2040120d090a028139032a12140cc002046105a8101cc02483100a5405a11008050404680090a80a22108431e4284a01080940048581011010e28543581020914a228404214c09ca1005000a10400804029a95242011000195041094221421009c641403404840384a4000b124030152049982490a0104612300448c046a880104841a8440240141c052214a284282a080111a0138422308200440481400912810c4018108419c0288c2400e82a90801823421061b04300161288c8500c81800c51c0008102131844b082024420348c2ad0008085100000a065038866000b600805056c600062080008048100614a469210411006851006204870000b1806000c02214280004201d242a8851008b490820a5037200c50c48280a0080491a442011072100002860088084148500101325c80180101120400e40a448200890218732024510240282b01820124207008a6840800442009240b100004a5289087888808008015a013820219493240c1140a0882a42c8601100000804b1aa00c49408201150c604c823028588c50084340c8873d2000c8150000120e5000040000a50061310002018030845221c10a841404295302421046419a400d423840a01142684e9030016914211522120c50208411820088000342521808581804a50b18103408c062d8000820489043842040086005085102228580710211044828482104003a0041a92700008100092096841429000c2325840006703182008c0524200080518c81031a74090061001100804ac46204024808d0818342100421e3010880000c401070098a1952a110442b020610453202240900000c1200090382062041000882a14a58983200402a40f480a502049010602a862400222280118428401400890032c01209080100630504021651886341c82728844114200088089c4195430080602522028042100a2182802c8c22429411a3604c2218012092801d08680c40a0c418120020281080011c2000429024020140a010600ad817284050160100812ac811048901186604a82000c004080100a42801090260a8e52018203ca00102c0010148509120024898403c68410c15a04030821220c12a40449002020a330420121086012810408010401110360449200c81000801d2002d0038149020c02a00211c004a5443098718904390275200140082004c110400210067a9060050b481470a8c0004015980c510084200912184118010210a71ca50842200800004401a08018043080481102901c2601d02200c8020c9031010a98001c0022060119065248402404029a121800514240a1641182448082020825010021902120610050e5002f0804030102091a0094284240443440184047008302067018052004940009290022000628c462a082511a0000405280428002008801208d200e2100e40b50311008089044002460008111ea538454040062428519681048c20d062202d02087201a1008080086438c804810402141498c021420418410b80628883080c4104014a1a409800500a16382208c28504080b1881a82463d482000020d604000000c421248403004080e2024245816e280272a58520063429c06080a01cc0411221012f1814008508081802a1200080c73042084a17004b000205908541920600a91002e200270a509024ce4080748988110050342c0040870401310a14b06408802104002940609004329491012f11022028005106428c62111a84054909023000c1024402000011142488874880c015c0408210b0081002521120218092808312069500606000a030094080811c8020042294060896400c40624604a0006990440089121011004429c83300005202420d062840212061420c023803004c900400418861848139120080422082241081284045050c5800d0908c001004204a208a028142580062214a22407528000a080708a03880c50d29528c5204805108200422338084880a48105381c9021404a8220858831c601186808084001800900442982038001244013120098090018e210af4010229462308890886221400704c7001c4118a7430014008d00042308a038000010280900000140000c400c4031001604041900013022411e21000022d6031902004003256242964080c8220a11a406608045890b08182401802050b2048d40520000ac42108090205200040dc800ce84202630805021050b10b198c128888038214942000105220c4380825300242c082244503002408a6201c11218618041035a361c2440968100ac20409021680308523882120a511020400020a48102405110026048a528012a54860c080084228124400a5490e01140111506198882a084394281182222442110846a40c7000112402000a042105400094208c1084820c0440c89094425a02103048114805090021800489020a14c08941205030180c48462385206810a3002640024204815044010008695a700807004c4410422a000628e068004111281080c3000811042208011040823044410210098c180080208500d0342c0c58440105283808022469418000950140ce04904411027084000108c0890302002504ec20520290850004400420488a14b0a31208040c26210001248a0840419123491000202532548290885240b090080214148928010c0791043040540149030a1089e40386a508244180a60d83681410a140411810a06a2248428044080a47a183200024890702c6800c600152051828228402204201141224a8208c150c0048c81104882040001004638a0038280240420022000410b02c510400b50942029288026900c60840230480980622162008490b0020180602c0c104ec08102405aa024a11850c4900f001c1080a0030400b02041484500085140950586091c00010468081600045a80810185120c4120a000042209c3610604282028003085ce2002750000619a01344059000618811050b30504028640182841c0913146181087084e01488080a20184821c014a4641098a0a9020b5011a1224a400100c103c4610028220080044218000681080244d62000580030a8c5301224a0630112810c84284226010840c02314220118061cc21080860844098240218a0010349002000c0404491352c01d0408544001250280662868134ac23120501011800a22084080030a948338a060d44400060a44100027000c200162410802814c1840002008305c00a86529902210600800860c016088821500190e021400420054800458025081061a0ca5280341d8a10c28111605102c20809085c3438e46000902084304061010850849001a8480c022521320694080e304021050c0a1a4420670b8881146008148581a2200871006442000090811006071060494af40006100a7001020110001cc4029462990250842284290b08060481400a120140290031814218520000052004072cc102828380806880c00029410a7200e82000001d6028100008ca2016112101080e2524054900851022689481306a020e0028436040400840104854808b134084a0024048900048000661942c20841004000b9002a081718a8128241002c32d020806010080081a2118204bc0820082224880314b028a24908052c8520540300047008e181094810043561628a40882e410801018300402598024b122620400150008d0318587305c40086162c000002122840011036a0861900c0280343148120c5700281810520c8403106521a500883404a02242401006220c0190e2100240b0c020c0d4a40e70d2200843294c84100121141420c029c0630889400c52204b0010522ce8200a04844029909100000a4061118342981618410004a4882c10148214421a0a26190220c246114e211a10a8412314950064410a1038c15016220004304871a107480024184002c451a8240000152582204c3098c04108242c2d0a04c0000f4818632108490000a40341025724460180a70546220a2128460818b7044008504400a01ac0b0018a0110700881324c81000a188092a5810208318904631430300402c2200c05505022b16c50001004420008870d24600a0689c0030c5020a000188504685a422114822290b2210c028a040140018846902419104020451058100140000610100148c4858420008841a0c6400e043909410a430922110021a08c3914c0a0416b881700802816e18ca818881300291102222120530cc09444405000a081380e84092401c0012404738045080b400820a5030b8616b0ca40061480083988442c8601184510a0211003048033460000280a10501462421040918b214001a80010c084800a085685080600540610c55290040c81001402100902800611e8200481812219886281480950308904604c0220680080a0158620982015aa0a144000012000c0150c1048058c483a0681800343880234e06114250020120432240703880289c11042d001085800c409092300d018a000028008850812449c89004023048112046204835100840006094800840e3002b02023221c3118400206c110242284e18001029870188253040490600842602d000b0c00a1a50380353480124202110a080812812811066219680100d60c204058922089014e012020424a8000e03900600c851a00c0044a010662086873041534080888e60d010100a020000250011c450a100694044850c1902010824090a0128017082821120320851b565400442904202005191223808840c01205cc488c1024a0438240a9000118a0098020124090050a40010c251000c50528220c809083129012084320440021404918e02485195855282008c00510a009920315014a80130020081406a8035202050000314aa20549201aa4a0a421c024240d189041082030888120c44a02161020418496954421181188430208b08806600081200d528684198350001200c00a1e040da9100010b904600245280130106000060a808438082140a3840e6ac4703022411862a4a000c495816c100080880813506001406102011c8900c600848160145124880300529c0040c2412d02291a260402384e001045231c862ca5025604110c184c40102202900605c8530a03146218c0b0050c2240540881038a22088013126108245800a1314640127280024144c2192050d8418084034a3499200104070800030283840c12807020400382108548420497900c410a320cc0080e34110222889130646800819902008c0200ac418c20250140809318202002a10803031054090108c41224880294a68009481060016609122081e003808231426840e42cc33808c580020b063110012016848423281c80904b00824430c863cc008804000a01080c0a1845012200d43224c42290c18026401001106102045018c0610c000406211a00050b0150a021c5009282088120c2420d2532981330a212801628c0408804a1621882a3a501030cd12127084a10000c5204610d0000446000e001006085a0338410800a701a400085280070288201100108411912029082125801a000408074a9635206d4212c184841a10b030084816060102434e108c200090b2040320424030a14946a100841100878da04048e1150c011600944052c64109202808e200051208a429044808a030c81882a09524008801a006421050a0eb22861109242018030001080ce500430b80b420403110408c2852004084801b080410236140129062788a2028410b50110943681285102501c4448801528001148952022025e0228610280041d82620801908b5200543c09214c410022604002284230063490c2609c260048428081840918488121c009120205023380c0a0444140c324002a4850a04402001100a9404603800b3a44002404091220194b13c044a420508010004302506111a609d480148c0a54a2082b60c0f2100042101600c16046c1000011ca5480421a0a40300123548008886244028c816080e084471b18440c2b400402854049084320060218d080c70054800080604260052822901104e818064215ab11c202180608081421041b10a0908640822300ac5012a0052c28cc0304000110242982000c52b0404000a4a504110024084201528100c83b40c09c015a0051052011824210604200451d2a300891200222181121212884200800301482082122c401b40d0284649020024001b06e31503401050a4a0081044184001c8d520220112a50941290460994008561010011b046001895200f004aa419204102911cc05212230424089412818118124020c8008440244a0092b2008609060091c06b86101c2028c0609da47200c10082110c502809304c87802a4000278d022250000803405c30244469066410811058001045181806a1c8700ad01046280045ac013a005011c22040301c2472000104834a48c001c4101444848a108206a920491256880a03182029202852031048419643802e2a1c8001621000008060620290292450c8620d42330880280508063438c02a16410d0c1210b1200a4902063100200c97200860c8808004205c45284642c604102018c401012c22c09104084a0206b0681100120d0208126604401114e418640a08232c0000c0841522009042a54f0a80520ce0028285016469003109850146d001812108a42c443042629486181011a4a0580834188a528a900444410021818c39040009442a14961800081206182958845190ab01161698c3024e4611460800b4a0c2384810012120080614e803c0e011a84808a00460190c0039014104d4a1066008910944180c15b906401aa50009605043840d2040a2204c009e508889018e47a46809c090008101400580220080a22005294022048148d0d231e7080e400882214612900a2010c02c001110a0214062460224a53390a49c8602d00230074000302162024803242c21806281403806958181404c100c890210449821021c01352418060010010288128928288060080f1b021428e40082b51024414022010c40c891a445000c140163534a80052c31d24309081104a401c20192823444011260080d6a08f0108c4a8a702502104881006a115a93204300140410e428800728e84ac000158222181081c1111004012a2106008c0c11ca310140100664a0864810911808611022958858c4f1a5014194603101108201b8040008348c820040649941090482102d3014c4810750c84200e00b10041ca1000051084a21ca8221022012c12862485c0214411a008618873080e1b4231090140848414006840a080076084d13406020200110a22c6d41804701ac209402a020508c323408434854146258028081c11008d11186621ea31889191084152b0854c0108a1196022868430a11a80a198274050f004025200442c2000000699444088050085120e1480424902113884404204848e024090814808081690c2704445b9244040050c0a32508400a1620a8008a42350e2800568804084ac418042982100008030420100848548085e2129674890a704843290470129224091850801042210e95008c20120311030248409082020e0291a013c481a9207112b18c8218500119c103408024412942460824608c0090454008101d0130c60321266000e18c4c091450882660c21000a840c40099a8404863112b1a0002084221c094180871402204081108b4104142c22428c450920091aa121c6234040a80102421708047380228c8c0a007124c94084121020720e11294a08508308423242549084408820302d2086870ca142508331c7099014310a524a0280403980e70003091ac40020085216040c7844200c2862142021411a1c1099626202c18502008a56840a28106588012050023c8911102589844a1822a0aa10927011223104100148590282004c0844a0b8c00ac69220c1628480858330803181600b0440a98b220250a40c209a030045101e15182001929110600052231182584051b0610b1c602c0242c8c6092018c060a88d2004d51963201a8424241900a00881500c60a588008430a80b418a06312c38c0152082324200b900488822006150444191813204b18521121a2414e060460430002980700cc1220a4081c4099485002058020315823050a200241984420c08034002b824405296a84d204400b983024cb6100008500084221a90221404598206a0c11384c02c0051c8f62c44010ea400a4611e1314080890058c8048544220204b8e44b48211c8071948685006014b0154543043000032288d71108408261a10833141500214050a310a00a9266190440d86005a5128c32248a0002900c0a5810212184304c70092121042618817a86c1900e4a0840a50610926615a3100e04ac061152c22c80211c20a841028e2318054350e00403008883a42a5808708c600204c610244080c5014830405039a502029118e12156c0098218c090240b491026a8483284d03428115210048a2142312186421c03044c21d4428da440c852110e42026004880042c518403148a000c23804b439c40b58002c016a8261182f0098a22045101c16946863c002314209484080050a568100860b0411242970c22418003a1463258d1386762882124c102900490055ac42191241198560c81010281884a1880768400134e5001c0291a000ca4180024090b104422144c081c42a929610c848562209ac48801314024b026434c3108805114a581a422c01004424a12160800130292bc2c58c0b728c03910b031a642881004012244e314016ac84080201182242520334243802801580025cd215470980148943500a82a90e7808340186104ce48061691485080823540085852a105121e4120802b0e91348410464689825800e0146f1b860220cb710201a40860180400c200522010a628dc2500e823d283882c22d0d095410a8c44112942c4d4b9226090d108423a4e4191050016860c843810230c2c600c90302113881209ea418407016c59121205412a5cb489c0484a12104c1246250c84220872112b5a064284222304502504291811210d3a0c31088208d2052c4841d406108c701482b126498026b8e310ca96102a284060288e105a4111e04152a008c111c460108b50d022a585500c2434630248d11d42104a26210a290c400921621083246542c686892d68041011a703906081633344c3842c3112448dca1b124580
def laneFive : ℕ := 0x11104220580400682814060801101860a5a51280000c40124084042c4910030440230ca110006b40843c20780641102b4a08a004064002701c220040060d0c208090a4c60042112020489a06208110020314880084012126409020100a4240510900080a0208010006c0012021823418404200629d8000408204011000200800600ad514465058a52c02010a203162080c23100022440708a658408301c0008270a5010088141548200080a1432812108944020000008c1204c28c284018832104000412844a318a90800e40d824014210009080460340a508a440400485802810a3804c080004214002401201442902b000c0004ac0100548d2b7300409c601812800c0811484520202180a224044892841000304810004618803239204080468442480a02884d1304b52005201a3100c810104181a61880c220c31300700160620050280c0180210400085404a1602a00900421090463910510d00221a4410a2034081040400800314a8409800a526001c0419014006902002700000808221142480420042821c6503d2a69c030a0c6220490382028460020000294020502200c40a0291300441040734a028800481a64a80510423420c4001c9220c8138001090c2a540201a0480a12190071c28485000180600009214480804620862230055056008c0810101010684008043028210c011100010a11054908085020044808940824108600102070c883008110062225c3108090850c0000600005181c60b027088a83180458000490865294312042088042a00200c24000042008518509101215100063140004052006e00c8022804284a45114109c8003024001445890268584080660280603c08700a040028209a420440031a34190020149010401a400000040048c2050252905220a91008003c0e010050088809164001270940342081001022880c700072004151822020620104041020300800ad05210c21100000821118090100c1140722908200810010200cca224200280000d061804018084108a248c802046018920401040044b200014910221c00100a1029021048a0258810044011a260002434081044c2000200802201404810242000138a96044020c000a00a330000182063009704a0180003000348c81025070202000ce1014282180c10424408092914008045001c85040002c202148c60d83190a2510240840a2180550c043080408108010240880400880114894a0622912032846004c319005005494004452400400a202446300214004200408230600094018023088c4200000a00142182008817950848404420843140000882429c1428c41004e00c0d080053004b400420948a4146c20c020010040c00324811b820028c210001414043002922082000ab1a000015c262c000882c488a8004400a4214184109040030c01b12c08802200842a08548840409096004908800018825090102002180010852a6240012c46200894208a01484001242206131c8113160501a202c060a08418040020481180800846490853008a081411200422461028204a10c29d80429001a16d400e200583000400840a184046810b1806801044419035004468864200285050202468080c00a4a00142430968210012090110020400624188341c200000611401700c0200ce1a0606a488010a4021440100c6000202103030a1218807108c10d20011002018e0858312121409025100c4b108418851014a005c40188302043000c040522089800a18408404000a021920608c001060204821080e2000612087484600000508000584863050f005201312003048018410180041180285c103180098800042822041184020810c180c42840d099c1404214200101844214a442907001404108301102408a02a10c20c0822501104e9528804080003c2c41002080021000430008189452844130024108000880348c081900f52800480e023060081020042100580320014a000428a81004453100400093808a0110a408012294002085020261048c32882000841b0a16112040460281480002112440284c64210562048100092a00a1140300d02010084118241000020606304260801724c908123400e70ad80224a831c08300a408108000204a10260d00100a47106831c8c4848011164110822908820c8812128001043810222000000a1088080088802c6260083600821a1671006601148108e06082c4118e28c481340c11000010a96140040104001090880f2216000084000e9130851940450d06004c03b42a411832880303c0400904085281a109120c24080140102508002200a51c01084042100301100204615082d4004c5002030004004604002208960038240114008c00629800010502000030080044511442301022a00500401481c220800108c521824214220298000503088e042188020c1320064018f0208700080418264000851880401407102300044190e0008610204a0104108d680990048408090200210149462124e860d04200014810800021121050b908020c400c20618020014a02020038c00000922c0508446201a4500ca220001890502d8950c285116a08c0c201052200e0202068428408202204840000420090008912142090a8200044210019c25704490118009820001212282958920080a428100124004188248c00004012190000886101823048201880421ca110642842029c8c48d0020121190262300341828030484000060086011a0100220894353480101002818242c801848010062484404200c2052a0100a024c1210425a84021140124c84840060082009882954e501e101c4023cc008c0420420420400904408001015826084010404580a2129480040042827001006208142844019220214108483081422206130000684044002320841120a3500630288a43020510205110c284890004000845230a04080c028401080948000221e9401e169080408e50a10009500088440004100084008625002500564108a800482104220816741108014e44a0280108c1a48a021a30000409c4243024508042000b2a500021c018105489a1214081080450c8948d880100209000218202240c4190200524000033a000139802214b11c082046460829201062000c11144000a8308202100209c8112047101284a1a400c02228212340248c02029040a128490e44140140885091402018648cc20210c000076010202c291104e404001a90100440409a342440000c03280c4110470080181400214520402000042102068489224080110a0a04323402700441816001029080450018c420020808a114404084018c0022008214c44202428022010ac1100021488180481a404500e229c09408c800040609015818d024001910142481604a919106400aa18802211805b900008414002c434680048040d0211109000a2404432180002d481840208404090290380402022600c038820480a4001821012f0a104099c122401411026182c020021212110843404c841400235044908a4ac0128084000c040c0b4000c00d247142200404030e81004021548408c1521404102452484121045018208903204841152a208012244a205010010528063038204150c000a7308013a0044002429140008400382458c00401830b02d08824018a0018005914c0840d3014900081010822a468120cd234444052a004c10812258000019203104020c0220c0720481101c01006248181000a54102a00020401010002e4b041030621000c28820110a3485040040a100c028080400081244e41800100410808c001200040210c087250a095824a54a191201180200c006006120c440110142c8a01008028070888a4048058168114090880d390c512101028aa418e40812810d2a60502231040882001d030100029900185806a804300800808361002210694806611504320022010b01825404881182c32848008097204109043080206b8030242843140084070a10c3108e490800800250020294023012822d0209004098c000140400202080820c010a00b311881002060108604a1100404808002083000cc581c0200c11248c02106080001014c215680b14448403600016ac4041081000010250e000460108160080081200090c280400a184000440002351825000020102a1844900060021040a10a41c084190270024308050a0a9400800318020040600460000a105060a109528a202400410405142411589520401004349106085a22084c4300209580088c5380655a807484802100021c400008c420023a066408460a820000803010201082109081242009140294623040839860005032a1c200580511864204a024201054c18da00808008584118026a900300203000020124008401800e111672914011440024422100b08500030030002003882208215882860004101c0105804a00220142028803040000c880010320001420062208b10c014b5221102008805094c41a80042800210800806a5080522904214010100209c080280102844510805a08c000460080143c03110006012a511201240123408420400188050001439282840300806304654800100002038440a00028408009c3120a0008432886010c8d3310409088281080842b000602950970800500042110a4888802483408864116950028214060882540d01211400002121100000cc0040000c81208c01a100581410a00a200005040038028008c21344a100a1410a80140061122419a300103004c9131c022c083204150c2400c28728042100813024624603280d0a9046000108048380ed008064092b62ca80810820022180c009048030006a8c26202501802100a35010632085000400302a01080388424118d58042020c84b0020a0c31300802c02604010000200067088040008a3142562d6460820220820902d011a120082400c81042a300006084e191a4181046900a424010a40a7180000408034400b10409022600cc09840400083a18c38440500062150840088224004150d22906200c21394020461030040206610104008800800b5808049c4b138614010660407001801a1660308409501000812192a300a87a808000404388500c01220880a802118094a8891110d180c20a188528203092c6090400000204e8119a128429420240382411428004021348908845404093042062c40598042a881004aa50020285e26002c0300401402004480804340900611603004059c04500a2304000a124028000206140c886904008481601c101404481a601c22608085002c21480308480b0c1018a240061030810804658100100083144042040031083106002d0068522209442000c4a00300180110c0484080808c20182120044300169400508a81a06c008020008c00083110210018060cc8089022180a62d0218088000a2034a012020425601112250044324840000600401318817804858023284c508421010c140880210400b02a1080d0044612006409a02a100400e41050c00185480080144208840200232208411020101812880a120c60200041868510612b10038800009492140001064020a142009020201910802002384a0501c6010600202c0080c50482404c121001520c302089304c8291086012a180061012801847281a040421320005042b081862106848800001203080820d264050e00c803a40419884088090000970c24694026200a011841b0210044b708044a0042812630c02001a0020c220582014a80bc42080080a140005c5001410a0e3428041140800101009011b0e2410030802921000221464088800149224840882700108008006a500318812044222040021a5081001308040424100a902182380a9131a620040204654090071087408000910a0a0c00b882038a04104a1008400884081034800248d20108a85380610809105002240211042001200040d0bd420858828402081c0191614a028118241280231d89005802202a020040b582230443204830102400c41150012080600c0130000b848084022a14502422400400284a608050a9040092458040231cc510e200543628c840406508a400046000cd1008000ce1404286002c08000228010000d4188002d20400615800641d001214b181c842000284a131c68009460958152c04031801004602020138a848c2209500308841040941102090a060448020203148b02100101260016242180020c01206e0100602104181815110040000418a06004e000aa30000204a4000020098252000320401888d60c0d1052643160010480208c41920109202848220083129616110b30c88021225008200c8211006000240a04300c4002104209214a9cd0842009125204ca008805b02a395002a00501144118004286020000404200810a50001004a0091c0021032080520008488250ad4120002038c1418a0404c0399204810c724071b40908844609030088012020100ac1040101009511a3604a000041039482108a18045084285a884604c2430040212c28020600ca38045011276b04b400e44004001085224890800411840280021006411c002082108104000c30a044418a802441038087050c70881000c20000400849038410142048001028c41306c0282660000008892810631885009402a4091090108041200202880440102321c9094c80b0a0238810080c4300419122005400218c518a200121018a548c422800a50102030210b1402a042004046004a790241248c034000102209068024050184e09c05200c2005444a1a661409010a821908410000a4861304809126421c0008a00842c001a608842100ac0000141c025200858000298046098a084c20018021008514050a10c018081000110488088c6201224380028860104a000841010c0009044018a004e10244210c80325032050e00044685603102d2000a585a120c05110c00114243060000000894c29ca4184400a102490600848b134084042809402280820a068000050318022809509080880e10009211c84802020022038040344468080180400052c189416a4804300500c2e4152a0200823462008410914041c6062120081000008c0000152042000a01006828c040042d4008912023029412a021200e440800711881854b004c64010120c4a608491356000428400082a4840898101003500001054a08001204410b400010c2289486306840c22114802008c001c0410660a98a02405230085008508d8900160130014958931820710000802e00406380010a0050a422000047016441884084060200209840284880384938048201865a806020c5181a0004490040922902108000800c38528088660384112424285005010d00049001a40290400c43100a03802a011082a10031400120e1680c1208404312e00807205880918c529250050000cc0134046092032804310c84208160c206008118402601020a4460800a4b9a0204280002820400500891240809529011660080a108482100030c03284c431008100000200a02448500625002a529040202242085018217046021142680064858a2108a01042414486380811422200054a044220a01102542449120013212830020204043150911824018022104118568000856004a100215300108080104e05a902089040044b100410a841631020044948806001a00098b3056a010c60282b024017900250400480002a0875112002c434108132120008862240029087080e548900508080ac0040c002044000048021e422d8003801031002012422c48100444a0a201920400694102020088605413840a410c3091e2400650310018c060ad8710008000a002040100800ac2000101308050040449046424220200523408081a808000110c0118030a4000202400540311020a8400112851824091e02148c2082a210020000011044100a568063400480990640901600c90850c1000720901208005b904600206080708425528000080a60c08610042980402144024831810628dc1000a5100000012850c0509049011e0414a80204069800189033a40c320830884001c02610606800a615080a80c000430314040103208040a00c090a40a506124c051000410a2410681a00401480209410a00008942080a0410a130404191015810621004001240894223c8102808008a9284420b1800114049502230a002c022040a0218401080181016a861410a041c280188908dc01000a1102221568020c140c621802000002120444a08063800304a10a40421922180070050f4800328c89008086ac220108400404005e0500042310931040601447118118c883804b138410a8ab510080802860422101c42300c411c14a460404201a040108801a089001c340983200a801044090262180028803221e8130a000480400215056a114011048a001a310000219ca024003090c10009704030b00e009c2681a1420204144a209080208209503481a40804021c64024260052a48449214240298000d00424480210640d20280812802a4800043c41710c020122481ac0a4412000b0b98402009228cd028680002e10c083104110080620c3130086884021ca20214d0304a0b0a009100404a420008005022280203044400470140000061010240800000088134c5010c2000c2408a00910828401589012200c520e04040901c051104a118216a14000402008022890860c4438800790247040801488019816880001040124223010b0000822184180014888a310284a420510ab30040130ec0a1040a940030443854600d0d4808720000400242202810848114283002010447284851314240c09010a139404005a04290010022181264ac4100c0420d02080044a8800a00900843080210240460020615007080c0b400439040046052c801292421423429840340a191410b4080240d2080649d0242102105480a8874188850404008064890a58540180080b0002090970ca10846040120588001a002111426142b014004900a084094a0c0215c410100430800140841d22201ac1004820120021a20a020608c510d040040d1a9012a4cb40086411e0200604810050825328012248c0a04240941010a82206000c04201c9090a2410e468c492000961000404823050901046500840212b3040d10c424008208885190240b800601801048022900308010208101040081216910a128c02a824081011840000144009a0020e052c216154a411a3381440942a0114008449408a10a028290885200c190004308001403200046104008804004043056510080609a80280111922004044840920020008a109120008c05302010021280ca20045100810258a704283002a21909000050318a0a0430884160080030000140800c45200285100628882220402204c39823421481200d480c509800418c8001480100e521042240a409026904170c082984050ca800503030a0411200a442010e51890408002220802004850044620a00240c00c601198322400281a90892341180214c55214441028608021800102121208c94040848406010012080211522420400800312c88528265008c00800204c0400402090b4008021002400a140040320620810460009508203912040827288000800e00081029e043860508225988460486005c25202229c091142040044481a40a44c00123490a40b021228810180011588220c61044000001089c0200207292030484000801050c098230206813020214062898258081024a90010060802038280086251088684080b4600304701cc8420050250c0810430000114085280700521220cc2144028c24029402b020180e0021c122048501087080360440034640a0840300123c097380640da04000e0b0a5001230094a408404140a28d2a08541210405080220040138404b0004002700500380a9101040244021c290014e184206018408047400c0424a8410855900a184a6484841a04802082418800004c281483002018405024e0511220a060210050004a000081a901220e1000044840011c206192068480201c0224a1009402204113024500043108208c4308084110a240101000e42300400921408460852510120099e8324c400900008a008501110061b82008c604204503942180046804300008480a2405a8304006a00c4108a2080e2010012945428a8418611106e00184200851046242086098402006c4b102109803810508108110654250b0202920d40300044290020121081c122d6110c81499005942e1248812020108224900200c002106248086601410240902106224021008071c4861900184c0001000b80369100110600a404710a108884001a710021014400006c20440208210280110104489a400020034084a4263108b6084811002518602202b0284858022500a12080520444539254096a0004801508300021880e08488191632a58001080120425800860402180ca0018023129134040a54e00884300400014f09040408882282920020090a4429020a1030310701c0062c24501042988c0840800068400e02042a204c103d622190e004070a42d1804300820034017152810c20604801048f021004a808614447812c4808340406080094090700c81514a06200601800220000008008185289227008103120700000010b0800450023294426180812504404801008a2848343182231c3118a9001241848c124080b10119882084005204460420009020080b00000110644a4e83204c081002010010909000e60080402881308c830d60190002a106110230384563001104412084469421400040016c5884108020728813010041401088c4020640a0260a089000080390420d0a0250211020010416140a030846a9040118348c88184050388300c21220004906c1990b681c00b4000282122142200000000011103001022a4065092001829204c002000308885088e100494b92140063208e01914858104024490a4000390400180008013300c588293208a011210a1000a80a108244a04230500604010a0a0090864b8201102d018600000038444011054a104488031248c3890c180810040910042508032802841c200004a4080d00584001244116041022024013084250c081040c2854100021428421084120028200245888b18504020a400181424a81a40c00d26229043a1c102844600801000941c222100818888301a20b187084402088530060200006004c090c8438822158841880500280002b220000804218806201880002c2942858488500450000b101e021d23030200204040525128002214a120060092821c0938d20600a60054203426019020b84042c404910c0000d42804015a2580a260548200601204600d814858020041019c3090424148432508600890a406104c008145429c871024024207980048847121040114508561310404a8062050908d02114230810428843200000a12001480689811b0881000320c024040c119241040c028010a02c118a203c423106100002110810a00e0a4090b186429006288140c44189032010808449400a021d010200460148400a00800118182480254808a6084440942110843200a13409008c2630a3320884310a60027181013012900120414400344c0b42c2848610481004a8010042882a00c000042a30108020c8191af110406a04000c4100c08519022200308400011e6010c9104681a800009012298310464520410810160c045380051886200c22a0880a120214082248c12060208084014a0b425490002142900c602002620d0032143005051310108009020e5328284040e1240c0008011020400c20202501102201a410044230c8130c148423330086910a3810c4294d2a0684100309060404a10010a41c8c4200600104008200a480208440012c0800978c412214108820638805288900102290a32058c001cb1010448d4221c000010c700a8204c2101a5028822814a10008414002000068581124855808000062620a51800450881384010014008901001402008c00c0640c0c009002002c0280122901304c143040614092ad0008008030a4085a0228805800a10c0030908091620216429829004002980060022589041a0c8580e0008880208400800501085044332425028c7024a05200c49926410880050101065091012018a22424300446040a58c40220e1419010bc8300c214280a001a84014212446100206988220020001082998d00882101a9111e448c0073040438020952d2a08a2042700001000aa7000d19108000812040a08040018c22084002484180020080430006280280982200843514413240c1118118949220c7108e108140100892a80c0880c6040e000004214203d813340c20c0a700a440901110404a0c0005000008408568080a0504c0091010b08040042200e141022410014a90610125100012014822c4520428605060a8401858049027238030200c0006601123501c610562190410a589000a0008201192a08489110a20090108968014a40b0680840a2808a2304142045019891008051406408a4584ca00100009e5090010100d1a50608028001cd0840002980404c061049704283000a10808221800398720021500a84104801c01701010040a1104009d68210484a408018833ac81220a1528010a5206200100002000260a10f210240080021520120687200868cab00906121834108021068014891a14048480684800240418004020631382821160600a0480440108e0106123ccb20c00488042800e520481a42c52820205823208063040289090210c29420001c062062120895812261d0518d402144040083020600180418944009a420101090461010362901308080b126480210280201001020646ac40400445802810582009411008809006400a210404600481000230848021c5008050212a50cc568000300885858228423080440ac421086c29806000230248e02546110e003480714e50090020805580042812840802410c1120ac225405098b080002a0c1018232a481028003046019900184c01910942040408c0034084b4020950268044091874210409148328211842c304a42080002540000e022c636000c2016450928428c6134200a1030008a314010044a5992200040014840094248449430a5138080048c5244031049000e262c013002803c4651c0042400300aa110620142012021490481802810908004204898501c000006c19844298295290212048488016116010c0503100005076050430400080e62286a00020024080010978146000040b8000a40b31441088444810c5840a19080411262808842484120623080722d000a181421256a08110cc44092840d0100d4a104200a18023060010c01380048d000a848024cd4100423808404482210a708a410401281041004322008130854b40059004008c20014019000481ca1242021c02101053098028026520c34900b018c16006a185087040422105020c20ac2000c242200e29ca80a8043154211160235a210804138240040f0ac850a40003181414e0500094104409422501c2220070a8070018841484085242018a30c02001a30110408c02624601a84a0002b0010001141008c4400c31148111c0c200a440d00191884280409d2903088011604898d20800020851a021014c800c090a146401860880609448000e520429238201b44c09c02100401046003062000c0200054080e215003a8090b00c080e20100370424609202100c1a0410310a021030090330c0c401244880140c89000c311101405c0020a001024488825a045000cd021802a8a11100040506000810040e03421028620b9801302550500381821a0081a0801108560d4a52004424480102d400c03a005488046980003c250350211d00104882812e1904009d080140069c2260489081872344112084408005104923042385032040b091c200004420894206d21c2051424029c03110b40002680890140002d0c388202040423126000c4030294006108040600822208b0a12c410442a80300480119006840a420062248d09043015200104028c4221880080811014410006000e2408895046c400011208c110451280003489204a0229005112e0808c100034080720420210041a028015212a0cd105205282003000638a442900100ae08cc01244400021288006000061d405000062848314c80b0a100168014085840438c89101490018c40800084000382169004111a040d00080e2131e008180000202004c7842208888100444902408881408050114a205040a8400312d01903401c2024c43a82071002488000040e1880102468624400312c08002780c2025e0010e00184a4040c4082c410a02a54c1252812001610c1030c0005401808c408821350202884001a0320ac100280090a08000300e340900489c20108000100014a620188381ca188400a000410042b12620000500c910029429a22000200861185206840402842005c65b023204a01384c1280019c2062c830112a001026302200c65284440180002801291a24006240c29328c031c0241000080ce00560480440a581200e0128461080d1a1090000c09963630486082c209482150302406200cc18145020820088c5012608ca208006001611212020c00414c022c08091874004c0800d531e0288415242c0a100310204894211445000204314830c0501822101801808108146038022004222808781401040c788441b0295108342482210615b122008840a50b0058d021c4609280006472040510a5024cb1050a58004028030102809d0451124081410a12219880400aa0246420000414282000931148480c4400c3408810904a108874a4801242d0808043040400a912004009012090502040028a30b04a510802110028c2a4a1803154809841035484244500508181034000409005009a460028304c000d2e0880e4098221027088a0098c0128c0410040148140081030804a1c621c0a60c493ac22405a8289003104500002608eb108204046421008028430a4830800662da113020014601890c001c1184811100220c6023c0140842401a05050d0010048040018016100c081422958800cc813100430030ace26200d52004300a5024040200a098800818a03004284082040b20482305ec4204740860004a030020398081044833021000400ad03524206a040318010208c030a351100004e9004200344e1002c0848311506109010890000c0903c20001274084013106109070b561038c822900208a578004380245880400c42504204a140485222210b09188010410a800408200900a089880040a380015b0a04250b1184941044201a210404311850200142d8a11c8431040604063a104100024204002001420c0180005900a5848513484488e0200a87006c100480088c02085005e81016320023000880352449080220840800a0210649408000044a0646980a30003085234096721148424a87056c211040010123024181804200923cc9114263090a00d40211a6029060ac4220005121021800d5808c210025a9060186000c091142a0890728c042a0c94a103020e0320056a4060812c20000304611b10063081330214294a2000102801030c1400030900a0200d794205842068c03001214800702040608040a920180a51090c320a701140280c2408290100820c074200018444101e068c20004047386a4880140040301c81202069400410e060808690211208a0218151847281415102840c0c0842620588020405a880601a800804589245040d6080138046038812a163418806344420500209450202e1088221c21100681044c419a80804d2200012125408a13004c09c0c40d23424030844a1b000090081002000042211a6024812800b500c5031201208850c0858182085402244c089404ac013040068062690804080a1202148001010ca5088d2340c211885014038404098e041c69030082212048802500cc0a408028060084250424488080802258cc500408010410114362440101021000d620c0110805a1004880141484495005198800801100a2421812a1410208400860184803294d20088018240112a000604b54400cac3214823084010c6489c00080c6346800883308433812849104685232180120804204002200802185138634a580710041054a704a010406384064200303c2130445329423102242084000ee080004a148034090a04c48405381461806c428042242b0048142d08215002800c0144d180232200a300004002c088025080a120ac41063619eb004840a942380064058130140108c00890813c880082a3012d50c09224c0138020904a02cc16004408121400c8080815a921208283008862408094a018002034000018768c214286913848500851084b204a100004415a2330002310401c2310509201c6098004208100c68091021810c281c319102409064a862704ac438200002010d0101525400e202408004211280420188704040816801021210e000081115426840a6a00429045000442108311081304484892f6048001101010810144a320603840220125409811a04442064030894000c5a00e3182200009301a0180c50200201044099224090d0290308041091054018a310886146a704023a0400340a530a160500408c11886051906224852848110140089a9008484894c40d20288c0120a85100448c2112800501223040a2258e225424188600120328213900828804404882342b410230a0ca50c002002a2058a401c400101518044b8414240562806210297a44a210460102408148620c438c005008510c86015041184209c08500245182809c0362501200a6181444202a210490000e105090010a39528420c408803400c91292640c8058882020a00302402800100681a420314a03ac450908d48803228a84206123040580011004d190490110242d802100009c0220c2760844230610288140522608244114201186220412840c028036a101700204a1646008548882110230898001042038e900c40685010a8c0100a40a102690405180423420584824254809084091004010310c403a10021003020cc024270090068142410e86a4200182302ccc09081181810386002404114000000810000080ca1110601d6161c44421624808d201c2090400918021483018402044e0080b189020844619805604a8200c84200408c241098a18123501e00010202c0809102789002a40d33008120c6030000344129400080220040e120610084428482600097086a304034000800023409c109420224e02b10041102024852a009500000808111c043142008c005000c221ea00807291c13300050808000a41a4c81a4004090200d00504287042430c0622588315a108045418280304d1100e2110f188482810c000e40244361c44020020052158880214c14082002820310013a04e6880e0290401440421644a8e010088104625112a424861018a490224b502128456240011d2010140211024a82009881608000852040000009890804e031872098110c646812200c844ad0e021e0008c321588414a92ac600908000503280811298268803010a140068418281a1441244510820228c040c240084400180304041100a420c128001004e40214a3850102c8b12102028e4098e0630650852a401890884922420011a42142800809000045808842881080ea00182420c1114c8125260880e08c422a08b181460a149000ad090080080b3214e081604808001d88104282314c2880078085311064a842424201382d11020705aa00101320240a98521161008cc00860218a248408331020106023440534c8095260940662106024891a04421082120a4711224840252142001cd010276080a400c102000310ac108040340c100016802352404388060142c281081a082409616a1c9404e448104515a108042030084a14002c0001484180422010878083124c04380400cc0210a0031605100000c09020041800120c4811829524241088340d80095e108082698a00086823042101056a44808109108204850921c2d2184020188400cf0a0044018342820604452a800504a5105811118c10820490c0628401182a08d0a0290428120038c46008203001625220050a605821940e0312520c48104c0325606010628048130035010628cc25200821c04094280a000034011a824621a052801410023000810dcb090cc0a9c1081402080851d2420121109013200a1000142521000210a026199861a10208084580c500521200681340601c24520c111189010c0420802084908842790203a4400000c4a025018a803841600680040232d002810a4190623822408414812e290021258c114a451042094625208431c402190120d06020e003821020c8420a830d441010310486204e6031404b801138a1221283880142c0011125421276848a020846054a38c292018a29061100000080a410610800860d016808200024101a40244a00c0402122385841a90213049100a1039620002843004608060a00b22080089872a4490000c4082c4982a10c452042813180201a901c4408940405834850923102480c409500010e00040048008604c002549020c26b800108810b002484840018810421508822016872008394004040722c021a54148805210e152c8c1050a090816040e2a121180240010b10c804a8245100800887095a2028434140a02444194001012e08109104c24286428020520a9500024198c088010106a5b0020a0690140142d0438da0608c83240301100608c2518c07312460126308400058c03121025c90206059424099a6408462118011082025c10000548446680825a408320220a8814a90a404283084a2812842c0032402431c1011c3220e060148408810a08b22405481a14150a41ca01282e20089324c7200281a045000c100805121462008220540021c90a80740440504245a860098261248102404020800012b12000035083180a4214e101a54006061001608c00100a50428381cb0b120180e40a800630053a50468d801088e094084380160561208a8705002898120902091cd438640a0e0010850ac620198440c080100350024610a1004012900049c023008510065010e20008a20cc958c00104ac50104095640888401500500c46a124610220a0803004e08840681a21002c2944429403588802844542162094084340421902019211a10a28085029200ac807106070560109297884b030801106208c43710c84914c215080ad00181e21a9052014a22c6413d04204a5001802204000863290210248551142304082204a01023118044214a700c13800050d092810d02086020a4009c1030400980a40d2162981085020110601c892202943440484a62a0c412108180664010b11445184006102a4810012101099852bcc040ca9311080802748105014c0581a008000328ac225226000070143025280986423820038ad0190641802084422a082098404008b71ca55894068900508010102f400200182b020e449126185026008e385c1001a5681ab114001980c1040c40088025e8421c322421038c40892000121288040200d4002661168204202810c1882920d4120089421a6228a1538ec194201080010886080a2500c421521120254844631802189c00b000100a000d08610250110a2812a10d84185640a9000804130cc9508021902c00587221040006009080018cd128684900d500c610404500814242843ca14092e205026a04a01444110402bd40620211200401186224030a4085200200001530642242000820088c131586088404298121c2818d045192160849190a4110a32b809410807004448c251a007300cd520842208051c8801524204002240c031090302062060720050944200423108032048b430a66914a3286002c0c588a45018912062000c003022020e54156810000220c731504009c00912012c4420068604831890b004001884249522230ac2814a0018210801201ac118012982911428221407858a204c41b0281206528048020845a0047890d100880242842045094c1120204900809807401470306740101239c030c601a428219aa50040121005b8820190a20401238640002508885204070a186208c101088615624010b10c442900900962400c0208616002451c88125870110b121046002a31c60689027900428c882104b0b8024108360020190481118c109020a125020004096240c68218444942c1090921044419a308108514212a5400988522480101a1088a44ac030302500c0810401020ca284851916301849500212014c600ad0a8021000a1202368188004ac13c6a1090448507021c3121a521082008044ad2200d06409003154200884038002304179860001a1421ce080a8180262110030cc122108400aa1ac49034c800021601a06188149c660108a0250e1006b1904222448130086044238401489c41a06f02803004a8400a13094a49128385840140a0a0c243d02300842210a5082018c00215c20812242480120a4115600848c22c42025015b8a1280a80142c714480888272440084e40914403180018054042c08008288c5131ab009e440c6a33008520680102b000872940152940028e1124a1098024052a40181180a41194400c68618cd338002812100900080e14998261488008405a446004861840428049180e00a8c0710885b84a085842080a01489511c00a8013202840d0a688a4220081014d02063401802242c49920581204a5023a16200884209033042d0880669c0c400092104f4018302548608451b84040400481c118540001650908801c884056a515a03a40c124431a9246b002510050ac082908a320891248650080485a21346829c6011c0a02943221064004428848100851b5043180248c8329008580a220101610804940610c09109c202006430a64254b500e03110a30d2000909201081a166281202104071c081990600446201e90a122415680040008c0431c84704cc0310501085024210146021948081a2421470016a0308420883020681b82a48c20400013318d18060204e272c80211444908d0ad463a000118c0484a000421515422040b624083b4821192043483620a0308441008c120490958d5296061c2b210c41046420c054a8822208012841011e0438490a40e710a3385081a44a400872010a0104c6a02448829201c02004e09126039a3114c90004009101305430a586409a262c08100a10804850429128c9010c24b102028eb304052ac02205202a18409064100030a1885184861140695246adc41a046418030054022c093200a290011040c20127110a128442734c92840640c8510942100805312522441108856292c01d083000a0a16100845211c3628c528520489014000e0b5840194208d2242404381221950e40848134c3008004a88b02c4543128415034000a18408580852a009600cc3814210920528870008a0a8a420d2341880111485110b2a5432810f5908208c00720694344018ca422080380210a0c20896311c0161404004841298823104488c64b8210288939840411a25a9010b4064a846430a3420691b90c7008158c80014ae08823400a8010ec1150a00806421c030024038a02344000c8d2204e58528405040b42c09105498817242072064200a5380041358943064081c0204e428d2e2000840c40124c1480010314912c840292230886481020a180131422a56821c88514427000c2818d02423110036348240c217200001c871004429141500216ad291002861c6009924724cc0054a490626918300840085000948712cc82006e5b0a44808272c40015287148c729880142d008c02b1a31002d0b06e0888c4890f1348011142624601306418c2800d0250dc42852140187084a94308032c002090b1240819088018226254900060709086980c200c30908d511c601460330043a12808502204060b5415898463008538090940a0052438881135ce0a0c30854842c400212040d0410903384654a0a643de830ca02a1067092a1a80f285000980562060610847102e0900e424cc180c80306220c8b218010a04801d05204c8211c1428214190231c0c28808605a83804c3306b00142429e34002840966590a618d831256b419810842822c4c11d482088970c82024a5490c2290435382510166198081850c1a1070912662049708a45000c11821628c20a5261380508daa620a02154a080076800e395804a1010992060ca050d084188d6840230124090a12a44b2040d429601892d0084c1202a1298043c02304e10044c41980381070b40d110052a540320e1380284808e30147380614106003ceb014680a442390a64214c300ab1988202d03514857990a7842e42045120640304260063228413992849c2b421822114f088432012a1146c0386469d800a404225e102147608a21302d5182c784211a1ce104ee0092228908434456242069083408ca1118a031c048189104e842146304072a5c52b585588400b0436144c4280c105a378d83094a25b0a200129434801ad44381ac1288628
def pBits : ℕ := (expandSix laneOne <<< 1) ||| (expandSix laneFive <<< 5)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pBits_eq : SunPrimePermutation.roughMask (cutB+1) (cutR-cutB) (ds8500.filter (fun p=>p*p≤cutR)) = pBits := by decide +kernel


end SunPrimeNumeric

namespace SunPrimeNumeric
open Finset SunPrimePermutation

theorem roughMask_prime_iff {ds : List ℕ} {d start w j : ℕ}
    (hds : ∀ p : ℕ, p ∈ ds ↔ p.Prime ∧ p ≤ d)
    (hstart : 1 < start) (hcut : d < start) (hmax : start+w ≤ (d+1)^2) (hj : j < w) :
    (roughMask start w ds).testBit j = true ↔ (start+j).Prime := by
  rw [roughMask_bit _ _ _ hj ds (fun p hp => ((hds p).mp hp).1.pos)]
  constructor
  · intro h
    by_contra hn
    have pm := Nat.minFac_prime (show start+j ≠ 1 by omega)
    have hsq := Nat.minFac_sq_le_self (by omega : 0 < start+j) hn
    have hle : (start+j).minFac ≤ d := by
      by_contra! hu
      have he := Nat.pow_le_pow_left (show d+1 ≤ (start+j).minFac by omega) 2
      omega
    exact h _ ((hds _).mpr ⟨pm,hle⟩) (Nat.minFac_dvd _)
  · intro hp q hq hh
    rcases hp.eq_one_or_self_of_dvd q hh with he|he
    · exact ((hds q).mp hq).1.ne_one he
    · have hd := ((hds q).mp hq).2
      omega

private theorem residue_count {t start mask k : ℕ} (shift : ℕ) (hk : k ≤ 16*2^t)
    (ht : 2^t < 65535) (hm : ∀ j < k, mask.testBit j = true ↔ (start+j).Prime) :
    (wordCount t ((mask &&& divMask (start+shift) 3 (16*2^t)) % 2^k) : ℤ) =
      ∑ j ∈ range k, if (start+j).Prime ∧ 3 ∣ start+shift+j then 1 else 0 := by
  rw [wordCount_eq _ _ ht, Finset.sum_boole]
  congr 2
  ext i
  simp only [mem_filter,mem_range,Nat.testBit_mod_two_pow,Nat.testBit_and,
    Bool.and_eq_true,decide_eq_true_eq]
  constructor
  · rintro ⟨hi,hk',hx,hd⟩
    exact ⟨hk',(hm _ hk').mp hx,(divMask_bit _ _ _ i (by decide) hi).mp hd⟩
  · rintro ⟨hi,hx,hd⟩
    have hw := hi.trans_le hk
    exact ⟨hw,hi,(hm _ hi).mpr hx,(divMask_bit _ _ _ i (by decide) hw).mpr hd⟩

private theorem chi_formula (n : ℕ) :
    (if n.Prime ∧ 3 ∣ n+2 then (1 : ℤ) else 0) -
    (if n.Prime ∧ 3 ∣ n+1 then (1 : ℤ) else 0) =
    if n.Prime then chi3 n else 0 := by
  by_cases hp : n.Prime
  · simp only [hp,true_and,if_true,chi3]
    split_ifs <;> omega
  · simp [hp]

theorem signedPrefix_primeWeight {t start mask k : ℕ} (hs : 0 < start) (hk : k ≤ 16*2^t)
    (ht : 2^t < 65535) (hm : ∀ j < k, mask.testBit j = true ↔ (start+j).Prime) :
    signedPrefix t start mask k = primeWeight (start+k-1) - primeWeight (start-1) := by
  rw [signedPrefix,residue_count 2 hk ht hm,residue_count 1 hk ht hm,← sum_sub_distrib]
  have ident : (∑ j ∈ range k, ((if (start+j).Prime ∧ 3 ∣ start+2+j then (1 : ℤ) else 0) -
      (if (start+j).Prime ∧ 3 ∣ start+1+j then (1 : ℤ) else 0))) =
      ∑ j ∈ range k, if (start+j).Prime then chi3 (start+j) else 0 := by
    apply sum_congr rfl
    intro j _
    rw [show start+2+j = start+j+2 by omega,show start+1+j = start+j+1 by omega]
    exact chi_formula _
  rw [ident]
  unfold primeWeight
  simp only [Nat.primesLE_eq_filter_range,Finset.sum_filter]
  rw [show start+k-1+1 = start+k by omega,show start-1+1 = start by omega,
    Finset.sum_range_add]
  omega

theorem primeCounting_sub_eq_wordCount {t start mask k : ℕ} (hs : 0 < start)
    (hk : k ≤ 16*2^t) (ht : 2^t < 65535)
    (hm : ∀ j < k, mask.testBit j = true ↔ (start+j).Prime) :
    Nat.primeCounting (start+k-1) - Nat.primeCounting (start-1) = wordCount t (mask%2^k) := by
  rw [wordCount_eq _ _ ht]
  have he : (range (16*2^t)).filter (fun j => (mask%2^k).testBit j) =
      (range k).filter (fun j => (start+j).Prime) := by
    ext j
    simp only [mem_filter,mem_range,Nat.testBit_mod_two_pow,Bool.and_eq_true,decide_eq_true_eq]
    exact ⟨fun h => ⟨h.2.1,(hm _ h.2.1).mp h.2.2⟩,
      fun h => ⟨h.1.trans_le hk,h.1,(hm _ h.1).mpr h.2⟩⟩
  rw [he,← Nat.primesLE_card_eq_primeCounting,← Nat.primesLE_card_eq_primeCounting]
  simp only [Nat.primesLE_eq_filter_range,Finset.card_filter]
  rw [show start+k-1+1 = start+k by omega,show start-1+1 = start by omega,Finset.sum_range_add]
  omega

end SunPrimeNumeric


namespace SunPrimeNumeric
open SunPrimePermutation

private def smallPrimeTest (p : ℕ) : Bool :=
  if p≤92 then decide p.Prime else p≤8500 && p.gcd (Nat.factorial 92)==1

private theorem smallPrimeTest_iff (p : ℕ) :
    smallPrimeTest p=true ↔ p.Prime ∧ p≤8500 := by
  unfold smallPrimeTest
  split_ifs with h
  · simp [show p≤8500 by omega]
  · simp only [Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq]
    constructor
    · rintro ⟨hb,hg⟩
      refine ⟨?_,hb⟩
      by_contra hn
      have hp := Nat.minFac_prime (show p≠1 by omega)
      have hq := Nat.minFac_sq_le_self (show p>0 by omega) hn
      have hd : p.minFac≤92 := by
        by_contra! hf
        have := Nat.pow_le_pow_left (show 93≤p.minFac by omega) 2
        omega
      have := Nat.dvd_gcd (Nat.minFac_dvd p) (Nat.dvd_factorial hp.pos hd)
      exact hp.not_dvd_one (hg ▸ this)
    · rintro ⟨hp,hb⟩
      refine ⟨hb,hp.coprime_iff_not_dvd.mpr ?_⟩
      exact fun hd=>h ((hp.dvd_factorial).mp hd)

private theorem ds_checked : (List.range 8501).filter smallPrimeTest = ds8500 := by
  set_option maxRecDepth 100000 in
  set_option maxHeartbeats 0 in
    decide +kernel

theorem ds8500_correct (p : ℕ) : p∈ds8500 ↔ p.Prime ∧ p≤8500 := by
  rw [← ds_checked,List.mem_filter,List.mem_range,smallPrimeTest_iff]
  exact ⟨fun h=>h.2, fun h=>⟨by omega,h⟩⟩

theorem pBits_correct {p : ℕ} (hb : cutB<p) (hr : p≤cutR) :
    pBits.testBit (p-cutB-1)=true ↔ p.Prime := by
  have hd : ∀ q : ℕ, q ∈ ds8500.filter (fun k=>k*k≤cutR) ↔ q.Prime ∧ q≤883 := by
    intro q
    simp only [List.mem_filter,ds8500_correct,decide_eq_true_eq,cutR]
    constructor
    · rintro ⟨⟨hq,_⟩,hs⟩
      refine ⟨hq,?_⟩
      by_contra! bad
      have := Nat.mul_self_le_mul_self bad
      omega
    · rintro ⟨hq,hs⟩
      exact ⟨⟨hq,by omega⟩,le_trans (Nat.mul_self_le_mul_self hs) (by decide)⟩
  have hc := roughMask_prime_iff hd (start:=cutB+1) (w:=cutR-cutB)
    (by decide) (by decide) (by decide) (j:=p-cutB-1) (by omega)
  rwa [pBits_eq,show cutB+1+(p-cutB-1)=p by omega] at hc

end SunPrimeNumeric


namespace SunPrimeNumeric
open SunPrimePermutation Finset

private def smallPrimes := ds8500.filter (fun p => decide (p ≤ 8477))

private theorem smallPrimes_eq : smallPrimes.toFinset = Nat.primesLE 8477 := by
  ext p
  simp only [smallPrimes, List.mem_toFinset, List.mem_filter, decide_eq_true_eq,
    ds8500_correct, Nat.mem_primesLE]
  exact ⟨fun h => ⟨h.2,h.1.1⟩, fun h => ⟨⟨h.2,by omega⟩,h.1⟩⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ds_chain : ds8500.IsChain (· < ·) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem signed_list : (smallPrimes.map chi3).sum = -12 := by decide +kernel

theorem weight_8477_from_list : (Nat.primesLE 8477).sum chi3 = -12 := by
  have hn : ds8500.Nodup := (List.isChain_iff_pairwise.mp ds_chain).imp (fun h => Nat.ne_of_lt h)
  have hsmall : smallPrimes.Nodup := hn.filter _
  rw [← smallPrimes_eq, List.sum_toFinset chi3 hsmall, signed_list]

end SunPrimeNumeric


namespace SunPrimeNumeric
open SunPrimePermutation Finset

theorem cut_anti {s e : ℕ} (hs : 0<s) (he : s≤e) : cut e≤cut s := by
  unfold cut
  exact min_le_min_left _ (max_le_max_left _ (Nat.div_le_div_left he hs))

theorem cut_bounds (s : ℕ) : cutB≤cut s ∧ cut s≤cutR := by
  unfold cut cutR cutB; omega

theorem cut_window {s e p : ℕ} (hs : 0<s) (he : s≤e)
    (h1 : cut e<p) (h2 : p≤cut s) : s≤x0/p ∧ x0/p<e := by
  have hb:=cut_bounds e
  have hr:=cut_bounds s
  have hlow : x0/e < p := by unfold cut at h1; omega
  have hhi : p≤x0/s := by unfold cut at h2; omega
  have hp : 0<p := by omega
  have he' : 0<e := by omega
  exact ⟨(Nat.le_div_iff_mul_le hp).mpr (by simpa [mul_comm] using (Nat.le_div_iff_mul_le hs).mp hhi),
    (Nat.div_lt_iff_lt_mul hp).mpr (by simpa [mul_comm] using (Nat.div_lt_iff_lt_mul he').mp hlow)⟩

def Segment (s e : ℕ) (prev next total : ℤ) : Prop :=
  primeWeight (s-1)=prev →
    primeWeight (e-1)=next ∧ upperWeighted x0 (cut e) (cut s)=total

theorem segment_join {s e f : ℕ} {a b c t u : ℤ}
    (hs : 0<s) (he : s≤e) (hf : e≤f)
    (h1 : Segment s e a b t) (h2 : Segment e f b c u) : Segment s f a c (t+u) := by
  intro h
  obtain ⟨hd,ht⟩:=h1 h
  obtain ⟨hc,hu⟩:=h2 hd
  refine ⟨hc,?_⟩
  unfold upperWeighted at *
  rw [← Finset.sum_Ioc_consecutive _ (cut_anti (by omega) hf) (cut_anti hs he),hu,ht,add_comm]

theorem cell_segment {t s : ℕ} {prev next total : ℤ}
    (ht : 2^t<65535) (hs : 8500<s) (hmax : s+16*2^t≤8501^2)
    (hc : cellEval ds8500 pBits t s prev = (next,total)) :
    Segment s (s+16*2^t) prev next total := by
  let w:=16*2^t
  let e:=s+w
  let d:=(e-1).sqrt
  let ds:=ds8500.filter (fun p=>p*p<e)
  let mask:=roughMask s w ds
  let lo:=cut e
  let hi:=cut s
  let bits:=(pBits >>> (lo-cutB))%2^(hi-lo)
  have hw : 0<w:=Nat.mul_pos (by decide) (pow_pos (by decide) _)
  have he : s≤e := by dsimp [e]; omega
  have hm : d≤8500 := by
    have hh : e-1<8501*8501 := by change s+w≤_ at hmax; dsimp [e]; omega
    exact Nat.le_of_lt_succ (Nat.sqrt_lt'.mpr hh)
  have hd : ∀ p : ℕ,p∈ds ↔ p.Prime ∧ p≤d := by
    intro p
    simp only [ds,List.mem_filter,ds8500_correct,decide_eq_true_eq]
    have eq : p*p<e ↔ p≤d := by
      rw [show p≤d ↔ p*p≤e-1 from Nat.le_sqrt]
      omega
    exact ⟨fun h=>⟨h.1.1,eq.mp h.2⟩,fun h=>⟨⟨h.1,h.2.trans hm⟩,eq.mpr h.2⟩⟩
  have hcap : e≤(d+1)^2 := by
    have h : e-1<(d+1)*(d+1) := Nat.lt_succ_sqrt (e-1)
    rw [pow_two]; omega
  have mask_ok (j : ℕ) (hj : j<w) : mask.testBit j=true ↔ (s+j).Prime :=
    roughMask_prime_iff hd (by omega) (by omega) hcap hj
  have hcut : lo≤hi := cut_anti (by omega) he
  have hlo : cutB≤lo := (cut_bounds e).1
  have hhi : hi≤cutR := (cut_bounds s).2
  intro hp0
  have hprefix (k : ℕ) (hk : k≤w) :
      signedPrefix t s mask k = primeWeight (s+k-1)-prev := by
    rw [signedPrefix_primeWeight (by omega) hk ht (fun j hj=>mask_ok j (by omega)),hp0]
  have hcomp : (prev+signedPrefix t s mask w,scanBits (fun p=>
      chi3 p * (prev+signedPrefix t s mask (x0/p-s+1))) (hi-lo) (lo+1) bits) = (next,total) := hc
  obtain ⟨hc1,hc2⟩:=Prod.mk.inj hcomp
  constructor
  · rw [hprefix _ le_rfl] at hc1
    change primeWeight (s+w-1)=next
    omega
  · change upperWeighted x0 lo hi = total
    rw [←hc2,scanBits_eq]
    unfold upperWeighted
    symm
    apply Finset.sum_bij (fun j _=>lo+1+j)
    · intro j hj; have hh:=mem_range.mp hj; exact mem_Ioc.mpr (by omega)
    · intro i _ j _ h; omega
    · intro p hp; obtain ⟨hl,hh⟩:=mem_Ioc.mp hp
      exact ⟨p-(lo+1),mem_range.mpr (by omega),by omega⟩
    · intro j hj
      have jlt:=mem_range.mp hj
      let p:=lo+1+j
      have hp1 : lo<p := by dsimp [p]; omega
      have hp2 : p≤hi := by dsimp [p]; omega
      have hbit : bits.testBit j=true ↔ p.Prime := by
        simp only [bits,Nat.testBit_mod_two_pow,jlt,decide_true,Bool.true_and,Nat.testBit_shiftRight]
        have hh : lo-cutB+j=p-cutB-1 := by dsimp [p]; omega
        rw [hh,pBits_correct (by omega) (by omega)]
      obtain ⟨h1,h2⟩:=cut_window (by omega) he hp1 hp2
      have hk : x0/p-s+1≤w := by dsimp [e] at h2; omega
      change (if bits.testBit j=true then chi3 p * (prev+signedPrefix t s mask (x0/p-s+1)) else 0) =
        if p.Prime then chi3 p * primeWeight (x0/p) else 0
      by_cases hp : p.Prime
      · simp only [if_pos hp,if_pos (hbit.mpr hp),hprefix _ hk,
          show s+(x0/p-s+1)-1=x0/p by omega]
        ring
      · simp [hp,show ¬bits.testBit j=true from fun hh=>hp (hbit.mp hh)]

end SunPrimeNumeric


namespace SunPrimeNumeric
open SunPrimePermutation

private theorem p1 : ∀ j<524288, pBits.testBit j=true ↔ (8478+j).Prime := by
  intro j hj
  have h:=pBits_correct (p:=8478+j) (by unfold cutB; omega) (by unfold cutR; omega)
  have e : 8478+j-cutB-1=j := by unfold cutB; omega
  rwa [e] at h

private theorem p2 : ∀ j<247607, (pBits >>> 524288).testBit j=true ↔ (532766+j).Prime := by
  intro j hj
  have h:=pBits_correct (p:=532766+j) (by unfold cutB; omega) (by unfold cutR; omega)
  have he : 532766+j-cutB-1=524288+j := by unfold cutB; omega
  rw [he] at h
  simpa only [Nat.testBit_shiftRight] using h

private theorem count1 : wordCount 15 (pBits%2^524288)=42976 := by decide +kernel
private theorem count2 : wordCount 15 ((pBits>>>524288)%2^247607)=18456 := by decide +kernel
private theorem weight1 : signedPrefix 15 8478 pBits 524288 = -30 := by decide +kernel
private theorem weight2 : signedPrefix 15 532766 (pBits>>>524288) 247607 = -90 := by decide +kernel

theorem primeWeight_r : primeWeight 780372 = -132 := by
  have h1:=signedPrefix_primeWeight (t:=15) (by decide) (by decide) (by decide) p1
  have h2:=signedPrefix_primeWeight (t:=15) (by decide) (by decide) (by decide) p2
  change signedPrefix _ _ _ _ = primeWeight 532765 - primeWeight 8477 at h1
  change signedPrefix _ _ _ _ = primeWeight 780372 - primeWeight 532765 at h2
  rw [weight1] at h1
  rw [weight2] at h2
  have hb : primeWeight 8477 = -12 := weight_8477_from_list
  omega

theorem primeCounting_r_b : (Nat.primeCounting 780372 : ℤ) - (Nat.primeCounting 8477 : ℤ) = 61432 := by
  have h1:=primeCounting_sub_eq_wordCount (t:=15) (by decide) (by decide) (by decide) p1
  have h2:=primeCounting_sub_eq_wordCount (t:=15) (by decide) (by decide) (by decide) p2
  rw [show 8478+524288-1=532765 by decide,show 8478-1=8477 by decide] at h1
  rw [show 532766+247607-1=780372 by decide,show 532766-1=532765 by decide] at h2
  rw [count1] at h1
  rw [count2] at h2
  omega

end SunPrimeNumeric


namespace SunPrimeNumeric
open SunPrimePermutation

def windowBits (lo hi : ℕ) : ℕ :=
  (roughMask (lo+1) (hi-lo) (ds8500.filter (fun p=>p*p≤cutR))) % 2^(hi-lo)

theorem windowBits_eq {lo hi : ℕ} (hb : cutB≤lo) (hr : hi≤cutR) :
    windowBits lo hi = (pBits >>> (lo-cutB)) % 2^(hi-lo) := by
  let ds:=ds8500.filter (fun p=>p*p≤cutR)
  have hp (p : ℕ) (hh : p∈ds) : 0<p :=
    ((ds8500_correct p).mp (List.mem_filter.mp hh).1).1.pos
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j<hi-lo
  · apply Bool.eq_iff_iff.mpr
    simp only [windowBits,Nat.testBit_mod_two_pow,hj,decide_true,Bool.true_and,Nat.testBit_shiftRight]
    rw [← pBits_eq]
    have hbig : lo-cutB+j<cutR-cutB := by omega
    rw [roughMask_bit _ _ _ hj ds hp,roughMask_bit _ _ _ hbig ds hp]
    have he : cutB+1+(lo-cutB+j)=lo+1+j := by omega
    rw [he]
  · simp [windowBits,Nat.testBit_mod_two_pow,hj]

def cellCompact (t s : ℕ) (base : ℤ) : ℤ × ℤ :=
  let w := 16*2^t
  let mask := roughMask s w (ds8500.filter (fun p=>p*p<s+w))
  let hi := cut s
  let lo := cut (s+w)
  let f := fun p => chi3 p * (base + signedPrefix t s mask (x0/p-s+1))
  (base + signedPrefix t s mask w, scanBits f (hi-lo) (lo+1) (windowBits lo hi))

theorem cellCompact_eq (t s : ℕ) (base : ℤ) :
    cellCompact t s base = cellEval ds8500 pBits t s base := by
  simp only [cellCompact,cellEval,
    windowBits_eq (cut_bounds (s+16*2^t)).1 (cut_bounds s).2]

theorem compactSegment {t s : ℕ} {a b n : ℤ} (h : cellCompact t s a = (b,n))
    (hc : 2^t<65535 ∧ 8500<s ∧ s+16*2^t≤8501^2 := by decide) :
    Segment s (s+16*2^t) a b n :=
  cell_segment hc.1 hc.2.1 hc.2.2 ((cellCompact_eq t s a).symm.trans h)

end SunPrimeNumeric


namespace SunPrimeNumeric
open SunPrimePermutation

def checkCellRun (t : ℕ) (s : ℕ) (a : ℤ) : List (ℤ × ℤ) → Bool
  | [] => true
  | (b,n)::xs => (cellCompact t s a == (b,n)) && checkCellRun t (s+16*2^t) b xs

def lastWeight (a : ℤ) : List (ℤ × ℤ) → ℤ
  | [] => a
  | e::xs => lastWeight e.1 xs

theorem checkedRun (t s : ℕ) (a : ℤ) (xs : List (ℤ × ℤ))
    (ht : 2^t < 65535) (hs : 8500 < s)
    (hmax : s+xs.length*(16*2^t) ≤ 8501^2) (hx : checkCellRun t s a xs = true) :
    Segment s (s+xs.length*(16*2^t)) a (lastWeight a xs) (xs.map Prod.snd).sum := by
  induction xs generalizing s a with
  | nil => simp [lastWeight, Segment, upperWeighted]
  | cons z xs ih =>
    rcases z with ⟨b,n⟩
    have step := Bool.and_eq_true_iff.mp hx
    set w := 16*2^t with hw
    have he : s+(xs.length+1)*w = s+w+xs.length*w := by rw [Nat.add_mul, Nat.one_mul]; omega
    have bound : s+w+xs.length*w ≤ 8501^2 := by simpa only [List.length_cons, he] using hmax
    have first : Segment s (s+w) a b n :=
      compactSegment (eq_of_beq step.1) ⟨ht,hs,by omega⟩
    have rest := ih (s+w) b (by omega) bound step.2
    have joined := segment_join (by omega : 0<s) (by omega : s ≤ s+w)
      (by omega : s+w ≤ s+w+xs.length*w) first rest
    simpa only [List.length_cons, he, List.map_cons, List.sum_cons, lastWeight] using joined

end SunPrimeNumeric


namespace SunPrimeNumeric
open SunPrimePermutation Finset

/-- Remove the highest marked position. Empty intervals stop immediately. -/
def sparseScan (f : ℕ → ℤ) (start : ℕ) : ℕ → ℕ → ℤ
  | 0, _ => 0
  | t+1, m => if m=0 then 0 else
      f (start+m.log2) + sparseScan f start t (m % 2^m.log2)

private theorem top_insert {m : ℕ} (hm : m ≠ 0) :
    m.bitIndices.toFinset = insert m.log2 (m%2^m.log2).bitIndices.toFinset := by
  ext j
  simp only [List.mem_toFinset, Nat.mem_bitIndices, mem_insert, Nat.testBit_mod_two_pow,
    Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · intro hj
    by_cases h : j = m.log2
    · exact Or.inl h
    · have hle := (Nat.le_log2 hm).2 (Nat.ge_two_pow_of_testBit hj)
      exact Or.inr ⟨by omega,hj⟩
  · rintro (rfl | ⟨_,hh⟩)
    · exact Nat.testBit_log2 hm
    · exact hh

theorem sparseScan_sum (f : ℕ → ℤ) (s fuel m : ℕ) (hm : m < 2^fuel) :
    sparseScan f s fuel m = ∑ j ∈ m.bitIndices.toFinset, f (s+j) := by
  induction fuel generalizing m with
  | zero =>
    have hz : m=0 := by simpa using hm
    simp [hz,sparseScan]
  | succ t ih =>
    by_cases hz : m=0
    · simp [hz,sparseScan]
    · have he : m.log2 ≤ t := by have := (Nat.log2_lt hz).mpr hm; omega
      have hl : m%2^m.log2 < 2^t :=
        (Nat.mod_lt _ (by positivity)).trans_le (Nat.pow_le_pow_right (by decide) he)
      have ha : m.log2 ∉ (m%2^m.log2).bitIndices.toFinset := by
        simp [Nat.testBit_mod_two_pow]
      rw [sparseScan, if_neg hz, ih _ hl, top_insert hz, sum_insert ha]

theorem sparseScan_eq (f : ℕ → ℤ) (s n m : ℕ) (hm : m < 2^n) :
    sparseScan f s n m = scanBits f n s m := by
  rw [sparseScan_sum f s n m hm, scanBits_eq, ← sum_filter]
  congr 1
  ext j
  simp only [List.mem_toFinset,Nat.mem_bitIndices,mem_filter,mem_range]
  constructor
  · intro hj
    have ht := Nat.ge_two_pow_of_testBit hj
    exact ⟨(Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp (ht.trans_lt hm),hj⟩
  · exact And.right

def cellSparse (t s : ℕ) (a : ℤ) : ℤ × ℤ :=
  let w := 16*2^t
  let m := roughMask s w (ds8500.filter (fun p=>p*p<s+w))
  let hi := cut s
  let lo := cut (s+w)
  let pos := m &&& divMask (s+2) 3 w
  let neg := m &&& divMask (s+1) 3 w
  let rank := fun k => (wordCount t (pos%2^k) : ℤ) - wordCount t (neg%2^k)
  (a+rank w, sparseScan (fun p=>chi3 p*(a+rank (x0/p-s+1))) (lo+1) (hi-lo) (windowBits lo hi))

theorem cellSparse_eq (t s : ℕ) (a : ℤ) : cellSparse t s a = cellCompact t s a := by
  unfold cellSparse cellCompact signedPrefix
  dsimp only
  rw [sparseScan_eq]
  apply Nat.mod_lt
  positivity

def checkSparse (t s : ℕ) (a : ℤ) : List (ℤ × ℤ) → Bool
  | [] => true
  | (b,n)::xs => (cellSparse t s a == (b,n)) && checkSparse t (s+16*2^t) b xs

theorem checkSparse_eq (t s : ℕ) (a : ℤ) (xs : List (ℤ×ℤ)) :
    checkSparse t s a xs = checkCellRun t s a xs := by
  induction xs generalizing s a with
  | nil => rfl
  | cons z xs ih =>
    rcases z with ⟨b,n⟩
    simp only [checkSparse,checkCellRun,cellSparse_eq,ih]

theorem sparseRun (t s : ℕ) (a : ℤ) (xs : List (ℤ × ℤ))
    (ht : 2^t < 65535) (hs : 8500 < s)
    (hmax : s+xs.length*(16*2^t) ≤ 8501^2) (hx : checkSparse t s a xs = true) :
    Segment s (s+xs.length*(16*2^t)) a (lastWeight a xs) (xs.map Prod.snd).sum :=
  checkedRun t s a xs ht hs hmax ((checkSparse_eq t s a xs).symm.trans hx)

end SunPrimeNumeric


namespace SunPrimeNumeric
open SunPrimePermutation Finset

private theorem bare_stripe (p t : ℕ) : SunPrimeBare.stripe p t = stripe p t := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [SunPrimeBare.stripe,stripe,ih]

private theorem bare_div (s p w : ℕ) : SunPrimeBare.divMask s p w = divMask s p w := by
  simp only [SunPrimeBare.divMask,divMask,bare_stripe]

private theorem bare_blocked (s w : ℕ) (ps : List ℕ) :
    SunPrimeBare.blocked s w ps = blockedMask s w ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp only [SunPrimeBare.blocked,blockedMask,bare_div,ih]

private theorem bare_rough (s w : ℕ) (ps : List ℕ) :
    SunPrimeBare.rough s w ps = roughMask s w ps := by
  simp only [SunPrimeBare.rough,roughMask,bare_blocked]

private theorem sumN_eq (f : ℕ → ℕ) (k : ℕ) :
    SunPrimeBare.sumN f k = ∑ i ∈ range k, f i := by
  induction k with
  | zero => simp [SunPrimeBare.sumN]
  | succ k ih => rw [SunPrimeBare.sumN,ih,sum_range_succ]

private theorem bare_count (t n : ℕ) : SunPrimeBare.count t n = wordCount t n := by
  simp only [SunPrimeBare.count,wordCount,countLane,lane,spaced,bare_stripe,sumN_eq]

private theorem bare_scan (f : ℕ → ℤ) (s t m : ℕ) :
    SunPrimeBare.scan f s t m = sparseScan f s t m := by
  induction t generalizing m with
  | zero => rfl
  | succ t ih => simp only [SunPrimeBare.scan,sparseScan,ih]

private theorem bare_window (s w : ℕ) : SunPrimeBare.window s w = windowBits s w := by
  simp only [SunPrimeBare.window,windowBits,bare_rough]
  rfl

private theorem bare_cell (t s : ℕ) (a : ℤ) : SunPrimeBare.cell t s a = cellSparse t s a := by
  have ds_eq : SunPrimeBare.ds = ds8500 := rfl
  have cut_eq : SunPrimeBare.cut = cut := rfl
  have chi_eq : SunPrimeBare.chi = chi3 := rfl
  simp only [SunPrimeBare.cell,cellSparse,bare_rough,bare_div,bare_count,bare_scan,
    bare_window,ds_eq,cut_eq,chi_eq,x0]

theorem bareRun_eq (t s : ℕ) (a : ℤ) (xs : List (ℤ×ℤ)) :
    SunPrimeBare.checkRun t s a xs = checkSparse t s a xs := by
  induction xs generalizing s a with
  | nil => rfl
  | cons z xs ih =>
    rcases z with ⟨b,n⟩
    simp only [SunPrimeBare.checkRun,checkSparse,bare_cell,ih]

theorem bareRun (t s : ℕ) (a : ℤ) (xs : List (ℤ×ℤ)) (ht : 2^t < 65535)
    (hs : 8500 < s) (hmax : s+xs.length*(16*2^t) ≤ 8501^2)
    (hx : SunPrimeBare.checkRun t s a xs = true) :
    Segment s (s+xs.length*(16*2^t)) a (lastWeight a xs) (xs.map Prod.snd).sum :=
  sparseRun t s a xs ht hs hmax ((bareRun_eq t s a xs).symm.trans hx)

end SunPrimeNumeric


namespace SunPrimeBare.Binary

private theorem locate_eq {m : ℕ} (hm : m≠0) (d lo : ℕ) (h₁ : lo ≤ m.log2)
    (h₂ : m.log2 < lo+2^d) : locate m d lo = m.log2 := by
  induction d generalizing lo with
  | zero => simp only [pow_zero] at h₂; simp only [locate]; omega
  | succ d ih =>
    simp only [pow_succ] at h₂
    rw [locate]
    split
    · rename_i h; exact ih _ ((Nat.le_log2 hm).mpr h) (by omega)
    · rename_i h
      have hn : ¬ lo+2^d ≤ m.log2 := fun hh => h ((Nat.le_log2 hm).mp hh)
      exact ih _ h₁ (by omega)

private theorem highest_eq {m : ℕ} (hm : m≠0) (d : ℕ) : highest d m = m.log2 := by
  unfold highest
  split
  · rename_i h
    exact locate_eq hm _ _ (Nat.zero_le _) (by simpa using (Nat.log2_lt hm).mpr h)
  · rfl

private theorem visit_eq (d : ℕ) (f : ℕ → ℤ) (s t m : ℕ) :
    visit d f s t m = SunPrimeBare.scan f s t m := by
  induction t generalizing m with
  | zero => rfl
  | succ t ih =>
    by_cases h : m=0
    · simp [visit,SunPrimeBare.scan,h]
    · simp only [visit,SunPrimeBare.scan,h,if_false,highest_eq h,ih]

private theorem cell_eq (t s : ℕ) (a : ℤ) : cell t s a = SunPrimeBare.cell t s a := by
  simp only [cell,SunPrimeBare.cell,visit_eq]

theorem check_eq (t s : ℕ) (a : ℤ) (xs : List (ℤ×ℤ)) :
    checkRun t s a xs = SunPrimeBare.checkRun t s a xs := by
  induction xs generalizing s a with
  | nil => rfl
  | cons z zs ih =>
    rcases z with ⟨b,n⟩
    simp only [checkRun,SunPrimeBare.checkRun,cell_eq,ih]

end SunPrimeBare.Binary

namespace SunPrimeNumeric

theorem binaryRun (t s : ℕ) (a : ℤ) (xs : List (ℤ×ℤ)) (ht : 2^t < 65535)
    (hs : 8500 < s) (hmax : s+xs.length*(16*2^t) ≤ 8501^2)
    (hx : SunPrimeBare.Binary.checkRun t s a xs = true) :
    Segment s (s+xs.length*(16*2^t)) a (lastWeight a xs) (xs.map Prod.snd).sum :=
  bareRun t s a xs ht hs hmax ((SunPrimeBare.Binary.check_eq t s a xs).symm.trans hx)

end SunPrimeNumeric


namespace SunPrimeNumeric

structure Frame where
  first : ℕ
  stop : ℕ
  before : ℤ
  after : ℤ
  total : ℤ
  start_pos : 0 < first
  ordered : first ≤ stop
  valid : Segment first stop before after total

def frame (t s : ℕ) (a : ℤ) (xs : List (ℤ×ℤ))
    (ht : 2^t < 65535) (hs : 8500 < s) (hm : s+xs.length*(16*2^t) ≤ 8501^2)
    (hx : SunPrimeBare.Binary.checkRun t s a xs = true) : Frame :=
  ⟨s, s+xs.length*(16*2^t), a, lastWeight a xs, (xs.map Prod.snd).sum,
    by omega, by omega, binaryRun t s a xs ht hs hm hx⟩

def mergeFrame (u v : Frame) : Frame :=
  if h : u.stop = v.first ∧ u.after = v.before then
    ⟨u.first, v.stop, u.before, v.after, u.total+v.total,
     u.start_pos, u.ordered.trans (h.1.le.trans v.ordered), by
       have second : Segment u.stop v.stop u.after v.after v.total := by
         rw [h.1,h.2]
         exact v.valid
       exact segment_join u.start_pos u.ordered (h.1.le.trans v.ordered) u.valid second⟩
  else u

def firstFrame : Frame :=
  ⟨780373,780373,-132,-132,0,by decide,le_rfl,by simp [Segment,SunPrimePermutation.upperWeighted]⟩

def frameData (u : Frame) : ℕ × ℕ × ℤ × ℤ × ℤ :=
  (u.first,u.stop,u.before,u.after,u.total)

theorem frame_matches {f : Frame} {s e : ℕ} {a b n : ℤ}
    (h : frameData f = (s,e,a,b,n)) : Segment s e a b n := by
  cases f with
  | mk first stop before after total hpos hle valid =>
    simp only [frameData,Prod.mk.injEq] at h
    obtain ⟨rfl,rfl,rfl,rfl,rfl⟩ := h
    exact valid

end SunPrimeNumeric

namespace SunPrimeNumeric.Slim
open SunPrimePermutation SunPrimeNumeric
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def frames : List Frame := [
  frame 8 780373 (-132) [(-131,2091),(-121,395),(-134,427),(-125,1492)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 8 796757 (-125) [(-112,15),(-119,1719),(-114,12),(-110,57)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 8 813141 (-110) [(-106,-1533),(-108,-222),(-97,763),(-81,-981)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 8 829525 (-81) [(-74,-92),(-81,500),(-82,689),(-87,-209)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 8 845909 (-87) [(-80,409),(-97,452),(-93,-1546),(-78,1403)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 8 862293 (-78) [(-77,-744),(-65,591),(-55,-813),(-55,-488)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 8 878677 (-55) [(-65,404),(-87,-360),(-75,339),(-71,-358)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 8 895061 (-71) [(-77,-1077),(-71,820),(-55,400),(-49,64)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 8 911445 (-49) [(-59,-209),(-65,145),(-65,87),(-60,739)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 8 927829 (-60) [(-75,756),(-73,-1249),(-88,344),(-85,1689)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 8 944213 (-85) [(-75,-58),(-80,-562),(-87,-240),(-84,298)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 8 960597 (-84) [(-65,-774),(-65,121),(-81,-249),(-68,-1102)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 8 976981 (-68) [(-69,535),(-52,-485),(-46,405),(-35,394)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 8 993365 (-35) [(-27,129),(-42,210),(-28,300),(-41,515)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 8 1009749 (-41) [(-39,-31),(-60,157),(-59,-676),(-58,-466)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 8 1026133 (-58) [(-64,-462),(-62,229),(-60,-454),(-58,407)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 8 1042517 (-58) [(-56,61),(-56,-745),(-69,274),(-56,321)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 8 1058901 (-56) [(-72,422),(-61,-539),(-71,573),(-67,-635)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 8 1075285 (-67) [(-78,632),(-89,461),(-83,-1081),(-79,1011)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 8 1091669 (-79) [(-67,749),(-79,-499),(-64,85),(-68,242)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 8 1108053 (-68) [(-75,620),(-68,-473),(-77,-369),(-80,685)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 8 1124437 (-80) [(-86,-400),(-83,-38),(-73,-323),(-81,446)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 8 1140821 (-81) [(-73,673),(-70,278),(-53,-185),(-54,497)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 8 1157205 (-54) [(-86,-588),(-91,-237),(-91,-142),(-82,-268)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 8 1173589 (-82) [(-86,350),(-85,-315),(-73,-650),(-71,-101)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 8 1189973 (-71) [(-55,-1264),(-43,160),(-57,-72),(-64,214)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 8 1206357 (-64) [(-81,-76),(-79,46),(-75,-446),(-75,-170)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 8 1222741 (-75) [(-76,551),(-63,1035),(-72,-412),(-82,462)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 8 1239125 (-82) [(-95,879),(-118,-74),(-117,586),(-127,-1107)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 8 1255509 (-127) [(-135,-40),(-122,113),(-114,-279),(-103,330)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 8 1271893 (-103) [(-81,260),(-96,-405),(-91,885),(-69,148)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 8 1288277 (-69) [(-90,-778),(-89,676),(-87,219),(-90,-421)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 8 1304661 (-90) [(-98,-622),(-113,597),(-120,-1849),(-117,-928)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 8 1321045 (-117) [(-103,368),(-107,529),(-100,1345),(-112,-1395)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 8 1337429 (-112) [(-120,688),(-114,-351),(-119,-933),(-143,-164)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 8 1353813 (-143) [(-160,-173),(-151,443),(-144,2377),(-143,131)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 8 1370197 (-143) [(-137,-381),(-146,448),(-158,-1025),(-175,897)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 8 1386581 (-175) [(-175,-1400),(-165,195),(-161,-1735),(-156,-312)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 8 1402965 (-156) [(-180,-563),(-171,-423),(-178,-13),(-187,717)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 8 1419349 (-187) [(-181,2),(-162,-1075),(-160,-169),(-155,1437)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 8 1435733 (-155) [(-152,-487),(-160,146),(-156,683),(-146,729)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 8 1452117 (-146) [(-143,588),(-138,543),(-116,-2012),(-125,632)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 8 1468501 (-125) [(-120,-568),(-129,96),(-138,-145),(-147,-883)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 8 1484885 (-147) [(-130,-1643),(-129,617),(-135,-648),(-121,365)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 10 1501269 (-121) [(-119,1008),(-115,-183),(-113,-647),(-104,890)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 10 1566805 (-104) [(-144,-1067),(-120,1716),(-121,411),(-95,-711)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 10 1632341 (-95) [(-81,569),(-91,-1614),(-83,928),(-88,805)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 10 1697877 (-88) [(-97,-555),(-67,480),(-93,-602),(-83,-296)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 10 1763413 (-83) [(-118,1837),(-68,-1521),(-69,648),(-91,994)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 10 1828949 (-91) [(-85,519),(-77,-467),(-107,-551),(-110,706)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 10 1894485 (-110) [(-151,-441),(-157,1257),(-150,-1192),(-127,2)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 10 1960021 (-127) [(-133,-162),(-112,914),(-147,-608),(-135,-652)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 10 2025557 (-135) [(-165,-1320),(-166,248),(-121,-1056),(-122,-205)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 10 2091093 (-122) [(-162,-717),(-146,-1265),(-121,443),(-101,999)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 10 2156629 (-101) [(-87,-38),(-64,568),(-68,185),(-84,687)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 10 2222165 (-84) [(-71,174),(-77,-317),(-89,-440),(-108,-278)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 10 2287701 (-108) [(-109,-922),(-106,-611),(-88,727),(-92,122)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 10 2353237 (-92) [(-113,804),(-79,-292),(-85,-1177),(-84,-107)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 10 2418773 (-84) [(-89,1208),(-102,1024),(-117,289),(-133,-724)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 10 2484309 (-133) [(-156,-1739),(-152,239),(-146,49),(-109,1656)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 10 2549845 (-109) [(-114,-932),(-99,1079),(-106,91),(-101,518)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 10 2615381 (-101) [(-102,-967),(-127,-1185),(-105,248),(-106,209)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 10 2680917 (-106) [(-96,1257),(-128,246),(-131,311),(-115,854)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 10 2746453 (-115) [(-122,-464),(-128,-708),(-151,-316),(-152,1032)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 10 2811989 (-152) [(-184,-1182),(-144,114),(-164,-120),(-183,-226)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 10 2877525 (-183) [(-175,2749),(-141,-1324),(-145,204),(-108,-80)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 10 2943061 (-108) [(-154,1050),(-158,-142),(-125,932),(-132,630)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 12 3008597 (-132) [(-179,832),(-158,-2980),(-190,-1616),(-128,-4169)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 12 3270741 (-128) [(-120,318),(-127,1073),(-95,-1448),(-128,947)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 12 3532885 (-128) [(-159,2107),(-197,983),(-211,-1834),(-190,828)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 12 3795029 (-190) [(-141,1281),(-196,-1433),(-255,-437),(-224,1809)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 12 4057173 (-224) [(-250,-2736),(-205,-1969),(-205,-1111),(-137,1365)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 12 4319317 (-137) [(-100,-953),(-129,1181),(-106,-890),(-81,1824)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 12 4581461 (-81) [(-124,-435),(-150,-578),(-165,1690),(-185,-2567)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 12 4843605 (-185) [(-162,68),(-118,681),(-132,2157),(-109,-808)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 12 5105749 (-109) [(-107,85),(-131,194),(-104,-134),(-109,1171)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 12 5367893 (-109) [(-88,75),(-119,1432),(-76,-755),(-71,302)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 12 5630037 (-71) [(-83,188),(-121,-766),(-163,533),(-178,-1034)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 12 5892181 (-178) [(-160,-675),(-195,-164),(-212,1068),(-259,318)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 12 6154325 (-259) [(-277,634),(-239,-137),(-244,-732),(-176,335)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 12 6416469 (-176) [(-208,-1698),(-165,530),(-241,-1905),(-274,-274)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 12 6678613 (-274) [(-283,-662),(-280,73),(-282,-1304),(-272,2462)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 12 6940757 (-272) [(-240,-626),(-302,-1256),(-292,112),(-297,-469)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 12 7202901 (-297) [(-316,3721),(-312,-2164),(-250,1722),(-236,-1952)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 12 7465045 (-236) [(-255,-221),(-232,-896),(-244,210),(-208,1682)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 12 7727189 (-208) [(-203,-88),(-179,-1424),(-196,1613),(-210,-221)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 12 7989333 (-210) [(-206,-103)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 14 8054869 (-206) [(-248,55),(-262,-2107),(-191,398),(-186,1188)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 14 9103445 (-186) [(-175,270),(-154,138),(-204,-100),(-170,282)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 14 10152021 (-170) [(-194,-50),(-154,1079),(-155,-931),(-116,341)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 14 11200597 (-116) [(-291,-758),(-269,-315),(-262,805),(-216,647)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 14 12249173 (-216) [(-230,-2217),(-188,1323),(-329,535),(-343,-442)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 14 13297749 (-343) [(-291,102),(-245,2666),(-262,311),(-251,-467)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 14 14346325 (-251) [(-286,193),(-235,372),(-306,-766),(-417,-435)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 14 15394901 (-417) [(-446,-113),(-326,555),(-383,-1270),(-358,-1802)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 14 16443477 (-358) [(-348,-565),(-248,-282),(-252,-665),(-256,1128)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 14 17492053 (-256) [(-281,1442),(-231,-1625),(-281,357),(-318,1096)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 14 18540629 (-318) [(-299,-226),(-273,905),(-219,1019),(-291,10)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 14 19589205 (-291) [(-330,-473),(-362,-1301),(-347,-1953),(-345,446)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 14 20637781 (-345) [(-331,886),(-354,-1058),(-340,-1508),(-349,263)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 14 21686357 (-349) [(-287,-444),(-224,944),(-399,-1482),(-352,752)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 14 22734933 (-352) [(-359,3723),(-437,1376),(-366,-1333),(-402,-1443)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 14 23783509 (-402) [(-444,2247),(-322,-2287),(-213,-197),(-255,921)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 14 24832085 (-255) [(-221,98),(-282,-755),(-275,-1202),(-221,-90)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 14 25880661 (-221) [(-226,976),(-168,-498),(-120,659),(-239,813)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 14 26929237 (-239) [(-237,-408),(-150,1134),(-106,-546),(-160,453)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 14 27977813 (-160) [(-185,-59),(-164,-192),(-201,114),(-210,-476)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 14 29026389 (-210) [(-242,480),(-239,762),(-321,-1042),(-387,293)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 14 30074965 (-387) [(-373,116),(-491,1453),(-486,-1373),(-522,229)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 14 31123541 (-522) [(-580,-2291),(-494,624),(-539,-911),(-597,1176)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 14 32172117 (-597) [(-652,1291),(-604,1869),(-582,-511),(-605,-560)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 14 33220693 (-605) [(-417,-765),(-420,-3),(-481,-893),(-525,136)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 14 34269269 (-525) [(-547,-1138),(-476,-472),(-505,-2178),(-508,-514)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 14 35317845 (-508) [(-506,485),(-559,-1537),(-582,532),(-546,510)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 14 36366421 (-546) [(-543,-598),(-493,58),(-454,917),(-389,-388)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 14 37414997 (-389) [(-302,128),(-444,684),(-397,452),(-407,-2149)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 14 38463573 (-407) [(-377,1496),(-375,-37),(-422,-768),(-373,352)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 14 39512149 (-373) [(-401,-817),(-454,-395),(-512,235),(-478,1012)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 14 40560725 (-478) [(-514,-491),(-531,987),(-423,331),(-489,1216)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 14 41609301 (-489) [(-408,576),(-481,-74),(-501,-1028),(-531,-1038)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 14 42657877 (-531) [(-454,31),(-450,-554),(-535,924),(-454,-19)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 14 43706453 (-454) [(-552,1038),(-553,540),(-499,972),(-516,-487)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 14 44755029 (-516) [(-576,-992),(-522,2864),(-474,-1505),(-538,-96)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 14 45803605 (-538) [(-447,-176),(-392,-771),(-369,676),(-377,398)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 14 46852181 (-377) [(-291,270),(-271,528),(-336,-543),(-408,-1453)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 14 47900757 (-408) [(-369,1349),(-307,-1547),(-321,-613),(-239,526)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 14 48949333 (-239) [(-214,-235),(-277,329),(-353,119),(-167,497)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 14 49997909 (-167) [(-250,503),(-282,260),(-243,-553),(-285,324)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 14 51046485 (-285) [(-219,674),(-254,-396),(-264,1163),(-265,-505)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 14 52095061 (-265) [(-123,49),(-178,70),(-244,-8),(-249,-408)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 14 53143637 (-249) [(-171,199),(-172,399),(-294,-666),(-252,91)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 14 54192213 (-252) [(-383,2),(-382,-374),(-460,26),(-388,-54)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 14 55240789 (-388) [(-436,395),(-592,-17),(-483,-736),(-486,-391)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 14 56289365 (-486) [(-458,65),(-469,-429),(-445,-3),(-565,-1566)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 14 57337941 (-565) [(-592,1740),(-537,-29),(-461,-53),(-396,-18)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 14 58386517 (-396) [(-372,-17),(-411,-452),(-359,346),(-311,1051)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 14 59435093 (-311) [(-392,377),(-366,734),(-403,742),(-449,-543)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 14 60483669 (-449) [(-381,952),(-389,9),(-364,-735),(-445,-468)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 14 61532245 (-445) [(-455,-433),(-472,566),(-352,-398),(-349,-86)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 14 62580821 (-349) [(-427,-392),(-425,-9),(-429,-1264),(-436,39)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 14 63629397 (-436) [(-445,897),(-495,472),(-539,1881),(-574,63)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 14 64677973 (-574) [(-604,-1249),(-684,566),(-759,58),(-754,-6)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 14 65726549 (-754) [(-836,745),(-827,2425),(-945,-874),(-910,-1918)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 14 66775125 (-910) [(-830,-2643),(-842,-876),(-821,750),(-807,-788)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 14 67823701 (-807) [(-784,1634),(-722,-1588),(-823,-1519),(-683,1439)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 14 68872277 (-683) [(-731,757),(-725,36),(-717,712),(-674,-2091)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 14 69920853 (-674) [(-621,695),(-602,11),(-545,-1151),(-548,-36)] (by decide) (by decide) (by decide) (by decide +kernel),
  frame 14 70969429 (-548) [(-551,30),(-685,-715),(-632,1319),(-747,0)] (by decide) (by decide) (by decide) (by decide +kernel)]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem joined : Segment 780373 72018005 (-132) (-747) (-4474) :=
  frame_matches (f := frames.foldl mergeFrame firstFrame) (by decide +kernel)
theorem weighted_rank_exact : upperWeighted x0 cutB cutR = -4474 := by
  have hh := (joined primeWeight_r).2
  rwa [show cut 72018005=cutB by decide, show cut 780373=cutR by decide] at hh
theorem semiprime_exact : semiprimeCorrection 608981813029 8477 780372 = 17602 :=
  semis_explicit weight_8477_from_list primeWeight_r primeCounting_r_b weighted_rank_exact
end SunPrimeNumeric.Slim
end

section
/-! The residue class 1 modulo 3 cannot outnumber the residue class 2 in a permutable prefix. -/
namespace SunPrimePermutation

private theorem partner {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hr : p%3 = 1) (hs : (p+q+1).Prime) : q ≠ 2 ∧ (q = 3 ∨ q%3 = 2) := by
  have hp2 := hp.two_le
  have hq2 := hq.two_le
  have hpodd := hp.eq_two_or_odd
  have hsodd := hs.eq_two_or_odd
  constructor
  · omega
  · by_cases h0 : q%3 = 0
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hq).mp
        (Nat.dvd_of_mod_eq_zero h0)).symm
    · right
      by_contra! he
      have h3 : 3 ∣ p+q+1 := Nat.dvd_of_mod_eq_zero (by omega)
      have h := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hs).mp h3
      omega

theorem residue_count_le {x : ℕ} (hx : 2 ≤ x) (f : Equiv.Perm (Fin (Nat.primeCounting x)))
    (hf : ∀ k : Fin (Nat.primeCounting x), (Nat.nth Nat.Prime k + Nat.nth Nat.Prime (f k) + 1).Prime) :
    ((Nat.primesLE x).filter (fun p => p%3 = 1)).card ≤
      ((Nat.primesLE x).filter (fun p => p%3 = 2)).card := by
  classical
  let A := (Nat.primesLE x).filter (fun p => p%3 = 1)
  let B := (Nat.primesLE x).filter (fun p => p%3 = 2)
  have key (p : A) : p.val ≤ x ∧ p.val.Prime ∧ p.val%3 = 1 := by
    obtain ⟨h,hmod⟩ := Finset.mem_filter.mp p.property
    exact ⟨(Nat.mem_primesLE.mp h).1,(Nat.mem_primesLE.mp h).2,hmod⟩
  let index (p : A) : Fin (Nat.primeCounting x) :=
    ⟨Nat.count Nat.Prime p.val,Nat.count_strict_mono (key p).2.1 (Nat.lt_succ_of_le (key p).1)⟩
  have undo (p : A) : Nat.nth Nat.Prime (index p) = p.val := Nat.nth_count (key p).2.1
  let q (p : A) := Nat.nth Nat.Prime (f (index p))
  have bounds (p : A) : q p ≤ x ∧ (q p).Prime := by
    have hlt := Nat.nth_lt_of_lt_count (p := Nat.Prime) (n := x+1) (f (index p)).isLt
    exact ⟨Nat.le_of_lt_succ hlt,Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime _⟩
  have restrict (p : A) : q p ≠ 2 ∧ (q p = 3 ∨ q p%3 = 2) := by
    apply partner (key p).2.1 (bounds p).2 (key p).2.2
    simpa only [← undo p] using hf (index p)
  let image (p : A) : B := ⟨if q p = 3 then 2 else q p, by
    obtain ⟨hnot,hmod⟩ := restrict p
    by_cases h : q p = 3
    · rw [if_pos h]
      exact Finset.mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨hx,Nat.prime_two⟩,by decide⟩
    · rw [if_neg h]
      exact Finset.mem_filter.mpr ⟨Nat.mem_primesLE.mpr (bounds p),hmod.resolve_left h⟩⟩
  have inject : Function.Injective image := by
    intro p s he
    have same := congrArg Subtype.val he
    change (if q p = 3 then 2 else q p) = (if q s = 3 then 2 else q s) at same
    have hp := (restrict p).1
    have hs := (restrict s).1
    have eq : q p = q s := by split at same <;> split at same <;> omega
    have ei := (Nat.nth_strictMono Nat.infinite_setOfPred_prime).injective eq
    have e := f.injective (Fin.ext ei)
    apply Subtype.ext
    rw [← undo p,← undo s,e]
  exact Finset.card_le_card_of_injective inject

theorem no_permutation_of_race {x : ℕ} (hx : 2 ≤ x)
    (hr : ((Nat.primesLE x).filter (fun p => p%3 = 2)).card <
      ((Nat.primesLE x).filter (fun p => p%3 = 1)).card) :
    ¬ (∀ n : ℕ, 0 < n → ∃ f : Equiv.Perm (Fin n),
      ∀ k : Fin n, (Nat.nth Nat.Prime k + Nat.nth Nat.Prime (f k) + 1).Prime) := by
  intro h
  have hn : 0 < Nat.primeCounting x := by
    rw [← Nat.primesLE_card_eq_primeCounting]
    exact Finset.card_pos.mpr ⟨2,Nat.mem_primesLE.mpr ⟨hx,Nat.prime_two⟩⟩
  obtain ⟨f,hf⟩ := h (Nat.primeCounting x) hn
  exact hr.not_ge (residue_count_le hx f hf)

theorem signed_prime_race (x : ℕ) :
    (∑ p ∈ Nat.primesLE x, if p%3 = 1 then (1:ℤ) else if p%3 = 2 then -1 else 0) =
      (((Nat.primesLE x).filter (fun p => p%3 = 1)).card :ℤ) -
      (((Nat.primesLE x).filter (fun p => p%3 = 2)).card :ℤ) := by
  calc
    _ = ∑ p ∈ Nat.primesLE x,
        ((if p%3 = 1 then (1:ℤ) else 0) - (if p%3 = 2 then (1:ℤ) else 0)) := by
      apply Finset.sum_congr rfl
      intro p _
      split_ifs <;> omega
    _ = _ := by
      rw [Finset.sum_sub_distrib]
      simp only [← Finset.sum_filter,Finset.sum_const, nsmul_eq_mul,mul_one]

end SunPrimePermutation
end

section
namespace SunPrimePermutation

theorem frozen_disproof_of_signed_race {x : ℕ} (hx : 2 ≤ x)
    (hr : 0 < ∑ p ∈ Nat.primesLE x,
      if p%3 = 1 then (1:ℤ) else if p%3 = 2 then -1 else 0) :
    ¬ (type_of% @OMA.S_oeis_a321727.main) := by
  apply no_permutation_of_race hx
  rw [signed_prime_race] at hr
  exact_mod_cast (sub_pos.mp hr)

end SunPrimePermutation
end

section
namespace SunPrimePermutation

theorem disproof_of_meissel_certificates
    (rough : signedPhi 8477 608981813029 = 17616)
    (semis : semiprimeCorrection 608981813029 8477 780372 = 17602) :
    ¬ (type_of% @OMA.S_oeis_a321727.main) := by
  have h := meissel_correction (x := 608981813029) (b := 8477) (r := 780372)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have small : primeWeight 8477 = -12 := SunPrimeNumeric.weight_8477_from_list
  rw [rough, small, semis] at h
  apply frozen_disproof_of_signed_race (x := 608981813029) (by decide)
  change 0 < primeWeight 608981813029
  omega

end SunPrimePermutation
end

section
namespace SunPrimePermutation
open Finset

theorem listProduct_coprime (ps : List ℕ) (hs : ∀ p ∈ ps, p.Prime) (n : ℕ) :
    ps.prod.Coprime n ↔ ∀ p ∈ ps, ¬p ∣ n := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    simp only [List.prod_cons, Nat.coprime_mul_iff_left, (hs p (.head _)).coprime_iff_not_dvd,
      ih (fun q h => hs q (.tail _ h))]
    simp

theorem rough_succ (w : ℕ → ℤ) (d n : ℕ) :
    roughSum w d (n+1) = roughSum w d n + if d.Coprime (n+1) then w (n+1) else 0 := by
  have h : insert (n+1) (Icc 1 n) = Icc 1 (n+1) := by
    apply insert_Icc_right_eq_Icc_succ
    exact Nat.succ_le_succ (Nat.zero_le _)
  simp only [roughSum, roughNumbers, ← h, filter_insert]
  split_ifs
  · rw [sum_insert (by simp), add_comm]
  · simp

def packedWeight (w : ℕ → ℤ) (start width bits : ℕ) : ℤ :=
  ∑ j ∈ range width, if bits.testBit j then w (start+j) else 0

theorem mask_rough_sum (w : ℕ → ℤ) (ps : List ℕ) (hs : ∀ p ∈ ps, p.Prime)
    (start width : ℕ) :
    packedWeight w (start+1) width (roughMask (start+1) width ps) =
      roughSum w ps.prod (start+width) - roughSum w ps.prod start := by
  unfold packedWeight
  have replace : (∑ j ∈ range width,
      if (roughMask (start+1) width ps).testBit j then w (start+1+j) else 0) =
      ∑ j ∈ range width, if ps.prod.Coprime (start+1+j) then w (start+1+j) else 0 := by
    apply sum_congr rfl
    intro j hj
    have h := (roughMask_bit (start+1) width j (mem_range.mp hj) ps (fun p hp => (hs p hp).pos)).trans
      (listProduct_coprime ps hs _).symm
    by_cases hc : ps.prod.Coprime (start+1+j)
    · rw [if_pos (h.mpr hc), if_pos hc]
    · rw [if_neg (mt h.mp hc), if_neg hc]
  rw [replace]
  clear replace
  induction width with
  | zero => simp
  | succ width ih =>
    rw [sum_range_succ, ih, show start+(width+1) = (start+width)+1 by omega, rough_succ]
    rw [show start+1+width = start+width+1 by omega]
    omega

end SunPrimePermutation
end

section
namespace SunPrimePermutation

/-! Cut inclusion-exclusion as soon as the product of the chosen sieve primes
exceeds a fixed threshold. The remaining computation at that branch is an
ordinary partial sieve at floor(x / product). -/
def sieveStages (a : ℕ) : ℕ → List ℕ
  | 0 => []
  | k+1 => if a < k+1 ∧ (k+1).Prime then (k+1) :: sieveStages a k else sieveStages a k

theorem sieveStages_empty {a k : ℕ} (h : k ≤ a) : sieveStages a k = [] := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [sieveStages, if_neg (fun h' => (Nat.not_lt_of_ge h) h'.1), ih (by omega)]

def cutPhi (w ordinary : ℕ → ℤ) (special : ℕ → ℕ → ℤ) (x cut : ℕ) :
    List ℕ → ℕ → ℤ
  | [], d => ordinary (x/d)
  | p :: ps, d =>
    let excluded := if cut < d*p then special p (x/(d*p)) else cutPhi w ordinary special x cut ps (d*p)
    cutPhi w ordinary special x cut ps d - w p * excluded

theorem cutPhi_eq (w initial : ℕ → ℤ) (x cut a b d : ℕ) (h : a ≤ b) :
    cutPhi w (phiEval w initial a) (fun p => phiEval w initial (p-1)) x cut (sieveStages a b) d =
      phiEval w initial b (x/d) := by
  induction b, h using Nat.le_induction generalizing d with
  | base => rw [sieveStages_empty (le_refl a), cutPhi]
  | succ b h ih =>
    by_cases hp : (b+1).Prime
    · have isStage : a < b+1 ∧ (b+1).Prime := ⟨by omega, hp⟩
      rw [sieveStages, if_pos isStage, cutPhi, phiEval, if_pos hp]
      simp only [ih, Nat.add_sub_cancel, Nat.div_div_eq_div_mul]
      split_ifs <;> rfl
    · rw [sieveStages, if_neg (fun cond => hp cond.2), phiEval, if_neg hp, ih]

theorem signed_leaf_formula (x cut a b : ℕ) (h : a ≤ b) :
    signedPhi b x =
      cutPhi chi3 (signedPhi a) (fun p => signedPhi (p-1)) x cut (sieveStages a b) 1 := by
  simpa [signedPhi] using
    (cutPhi_eq chi3 (fun n => if n%3 = 1 then 1 else 0) x cut a b 1 h).symm

/-! For the branch at p the remaining sieve contains exactly the primes below p.
When (x/(d*p)) < p², prime counts determine its value. -/
theorem easy_leaf {p v : ℕ} (hp : p.Prime) (hv : 1 ≤ v) (hv2 : v < p^2) :
    signedPhi (p-1) v = 1 + primeWeight v - primeWeight (min (p-1) v) := by
  by_cases h : p-1 ≤ v
  · rw [min_eq_left h]
    apply signedPhi_terminal hv h
    simpa [Nat.sub_add_cancel hp.pos] using hv2
  · have he : (roughNumbers (primorial (p-1)) v) = {1} := by
      ext n
      simp only [roughNumbers, Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton]
      constructor
      · rintro ⟨⟨hn,hnv⟩,hc⟩
        by_contra hu
        have hq := Nat.minFac_prime hu
        have hl : n.minFac ≤ p-1 := (Nat.minFac_le hn).trans (hnv.trans (by omega))
        have hd := Nat.dvd_gcd (hq.dvd_primorial_iff.mpr hl) (Nat.minFac_dvd n)
        rw [hc.gcd_eq_one] at hd
        exact hq.not_dvd_one hd
      · rintro rfl
        exact ⟨⟨le_rfl, hv⟩, Nat.coprime_one_right _⟩
    rw [min_eq_right (by omega)]
    unfold signedPhi
    rw [phiEval_eq _ _ chi3_mul chi3_prefix, roughSum, he, Finset.sum_singleton]
    have hu : chi3 1 = 1 := by decide
    omega

end SunPrimePermutation
end

section
namespace SunPrimePermutation

abbrev SignedProduct := ℕ × ℤ

def weighFront (terms : List SignedProduct) (f : ℕ → ℤ) : ℤ :=
  (terms.map (fun dc => dc.2 * f dc.1)).sum

def addPrime (w : ℕ → ℤ) (p : ℕ) (dc : SignedProduct) : SignedProduct :=
  (dc.1*p, -(dc.2*w p))

def keptProducts (w : ℕ → ℤ) (cut p : ℕ) (terms : List SignedProduct) : List SignedProduct :=
  ((terms.map (addPrime w p)).filter (fun dc => decide (dc.1 ≤ cut)))

def finishedProducts (w : ℕ → ℤ) (cut p : ℕ) (terms : List SignedProduct) : List SignedProduct :=
  ((terms.map (addPrime w p)).filter (fun dc => decide (cut < dc.1)))

theorem weighFront_append (a b : List SignedProduct) (f : ℕ → ℤ) :
    weighFront (a++b) f = weighFront a f + weighFront b f := by
  simp [weighFront]

theorem expand_front (w k g : ℕ → ℤ) (cut p : ℕ) (terms : List SignedProduct) :
    weighFront terms (fun d => k d - w p * (if cut < d*p then g (d*p) else k (d*p))) =
      weighFront (terms ++ keptProducts w cut p terms) k + weighFront (finishedProducts w cut p terms) g := by
  rw [weighFront_append]
  induction terms with
  | nil => simp [weighFront, keptProducts, finishedProducts]
  | cons dc rest ih =>
    simp only [weighFront, List.map_cons, List.sum_cons] at ih ⊢
    by_cases h : cut < dc.1*p
    · have hn : ¬dc.1*p ≤ cut := Nat.not_le_of_gt h
      simp only [keptProducts, finishedProducts, List.map_cons, List.filter_cons,
        addPrime, h, hn, decide_true, decide_false, Bool.false_eq_true,
        if_false, if_true, List.map_cons, List.sum_cons] at ih ⊢
      linear_combination ih
    · have hn : dc.1*p ≤ cut := Nat.le_of_not_gt h
      simp only [keptProducts, finishedProducts, List.map_cons, List.filter_cons,
        addPrime, h, hn, decide_true, decide_false, Bool.false_eq_true,
        if_false, if_true, List.map_cons, List.sum_cons] at ih ⊢
      linear_combination ih

def batchPhi (w ordinary : ℕ → ℤ) (special : ℕ → ℕ → ℤ) (x cut : ℕ) :
    List ℕ → List SignedProduct → ℤ
  | [], terms => weighFront terms (fun d => ordinary (x/d))
  | p::ps, terms =>
    batchPhi w ordinary special x cut ps (terms ++ keptProducts w cut p terms) +
      weighFront (finishedProducts w cut p terms) (fun d => special p (x/d))

theorem batchPhi_eq (w ordinary : ℕ → ℤ) (special : ℕ → ℕ → ℤ) (x cut : ℕ)
    (ps : List ℕ) (terms : List SignedProduct) :
    batchPhi w ordinary special x cut ps terms =
      weighFront terms (cutPhi w ordinary special x cut ps) := by
  induction ps generalizing terms with
  | nil => rfl
  | cons p ps ih =>
    rw [batchPhi, ih]
    exact (expand_front w _ _ cut p terms).symm

theorem signed_batch_formula (x cut a b : ℕ) (h : a ≤ b) :
    signedPhi b x =
      batchPhi chi3 (signedPhi a) (fun p => signedPhi (p-1)) x cut (sieveStages a b) [(1,1)] := by
  rw [signed_leaf_formula x cut a b h, batchPhi_eq]
  simp [weighFront]

end SunPrimePermutation
end

section
namespace SunPrimePermutation

theorem rough_shift (d : ℕ) (hd : 3 ∣ d) (s : ℕ) :
    roughSum chi3 d (d+s) = roughSum chi3 d d + roughSum chi3 d s := by
  have hmod := Nat.mod_eq_zero_of_dvd hd
  induction s with
  | zero => simp [roughSum, roughNumbers]
  | succ s ih =>
    rw [show d+(s+1) = (d+s)+1 by omega, rough_succ, ih, rough_succ]
    have shift : d.Coprime (d+s+1) ↔ d.Coprime (s+1) := by
      rw [Nat.add_assoc, Nat.coprime_self_add_right]
    have character : chi3 (d+s+1) = chi3 (s+1) := by
      simp only [chi3, Nat.add_assoc]
      rw [Nat.add_mod d (s+1) 3, hmod, Nat.zero_add, Nat.mod_mod]
    by_cases cop : d.Coprime (s+1)
    · rw [if_pos cop, if_pos (shift.mpr cop), character, add_assoc]
    · rw [if_neg cop, if_neg (mt shift.mp cop)]
      simp

theorem rough_mod_period (d : ℕ) (hd : 3 ∣ d) (zero : roughSum chi3 d d = 0) (x : ℕ) :
    roughSum chi3 d x = roughSum chi3 d (x%d) := by
  have periodic (q v : ℕ) : roughSum chi3 d (d*q+v) = roughSum chi3 d v := by
    induction q with
    | zero => simp
    | succ q ih =>
      rw [Nat.mul_succ, show d*q+d+v = d+(d*q+v) by omega, rough_shift d hd, zero, zero_add, ih]
  simpa only [Nat.div_add_mod] using periodic (x/d) (x%d)

theorem wheel17 : primorial 17 = 510510 := by decide +kernel

theorem signedPhi_wheel (x : ℕ) : signedPhi 17 x = signedPhi 17 (x%510510) := by
  have z : signedPhi 17 510510 = 0 := by decide +kernel
  unfold signedPhi at z ⊢
  rw [phiEval_eq _ _ chi3_mul chi3_prefix, wheel17] at z
  rw [phiEval_eq _ _ chi3_mul chi3_prefix, phiEval_eq _ _ chi3_mul chi3_prefix, wheel17]
  exact rough_mod_period 510510 (by decide) z x

end SunPrimePermutation
end

section
namespace SunPrimePermutation
open Finset

theorem stages_append {a k b : ℕ} (ha : a ≤ k) (hk : k ≤ b) :
    sieveStages a b = sieveStages k b ++ sieveStages a k := by
  induction b, hk using Nat.le_induction with
  | base => simp [sieveStages_empty (le_refl k)]
  | succ b h ih =>
    by_cases hp : (b+1).Prime
    · simp only [sieveStages, show a < b+1 by omega, show k < b+1 by omega, hp,
        and_self, ↓reduceIte, ih, List.cons_append]
    · simp only [sieveStages, hp, and_false, ↓reduceIte, ih]

def advanceTerms (cut : ℕ) (terms : List SignedProduct) (p : ℕ) : List SignedProduct :=
  terms ++ keptProducts chi3 cut p terms

def termsBefore (cut b p : ℕ) : List SignedProduct :=
  (sieveStages p b).foldl (advanceTerms cut) [(1,1)]

theorem termsBefore_succ {b k : ℕ} (h : k+1 ≤ b) (cut : ℕ) :
    termsBefore cut b k =
      if (k+1).Prime then advanceTerms cut (termsBefore cut b (k+1)) (k+1)
      else termsBefore cut b (k+1) := by
  unfold termsBefore
  rw [stages_append (a := k) (k := k+1) (by omega) h, List.foldl_append]
  rw [sieveStages, sieveStages_empty (le_refl k)]
  split_ifs <;> simp_all

def rowTerms (xcut b p : ℕ) : List SignedProduct :=
  finishedProducts chi3 xcut p (termsBefore xcut b p)

def easyValue (p v : ℕ) : ℤ :=
  if v = 0 then 0 else 1 + primeWeight v - primeWeight (min (p-1) v)

theorem easyValue_eq {p v : ℕ} (hp : p.Prime) (hv : v < p^2) :
    easyValue p v = signedPhi (p-1) v := by
  by_cases hz : v = 0
  · subst v
    unfold signedPhi
    rw [phiEval_eq _ _ chi3_mul chi3_prefix]
    simp [easyValue, roughSum, roughNumbers]
  · simpa [easyValue, hz] using (easy_leaf hp (by omega) hv).symm

def easyRow (x cut b p : ℕ) : ℤ := weighFront
  ((rowTerms cut b p).filter (fun dc => decide (x/dc.1 < p^2)))
  (fun d => easyValue p (x/d))

def hardRow (x cut b p : ℕ) : ℤ := weighFront
  ((rowTerms cut b p).filter (fun dc => decide (p^2 ≤ x/dc.1)))
  (fun d => signedPhi (p-1) (x/d))

theorem row_split (x cut b p : ℕ) (hp : p.Prime) :
    weighFront (rowTerms cut b p) (fun d => signedPhi (p-1) (x/d)) =
    easyRow x cut b p + hardRow x cut b p := by
  unfold easyRow hardRow
  generalize rowTerms cut b p = terms
  induction terms with
  | nil => simp [weighFront]
  | cons dc ds ih =>
    simp only [weighFront, List.map_cons, List.sum_cons] at ih ⊢
    by_cases h : x/dc.1 < p^2
    · simp only [List.filter_cons, h, Nat.not_le_of_gt h, decide_false, decide_true,
        Bool.false_eq_true, if_true, if_false, List.map_cons, List.sum_cons, easyValue_eq hp h]
      omega
    · simp only [List.filter_cons, h, Nat.le_of_not_gt h, decide_false, decide_true,
        Bool.false_eq_true, if_true, if_false, List.map_cons, List.sum_cons]
      omega

def easyTotal (x cut a b : ℕ) : ℤ :=
  ∑ p ∈ Ioc a b, if p.Prime then easyRow x cut b p else 0

def hardTotal (x cut a b : ℕ) : ℤ :=
  ∑ p ∈ Ioc a b, if p.Prime then hardRow x cut b p else 0

def ordinaryTotal (x cut a b : ℕ) : ℤ :=
  weighFront (termsBefore cut b a) (fun d => signedPhi a (x/d))

theorem phi_three_classes {x cut a b : ℕ} (hb : a ≤ b) :
    signedPhi b x = ordinaryTotal x cut a b + easyTotal x cut a b + hardTotal x cut a b := by
  let B (k : ℕ) := batchPhi chi3 (signedPhi a) (fun p => signedPhi (p-1)) x cut
    (sieveStages a k) (termsBefore cut b k)
  have through (k : ℕ) (hak : a ≤ k) (hkb : k ≤ b) : B k = ordinaryTotal x cut a b +
      (∑ p ∈ Ioc a k, if p.Prime then easyRow x cut b p else 0) +
      (∑ p ∈ Ioc a k, if p.Prime then hardRow x cut b p else 0) := by
    induction k, hak using Nat.le_induction with
    | base => simp [B, sieveStages_empty (le_refl a), batchPhi, ordinaryTotal]
    | succ k hak ih =>
      have prior := ih (by omega)
      have intv : Ioc a (k+1) = insert (k+1) (Ioc a k) := by
        ext n
        simp only [mem_Ioc, mem_insert]
        omega
      rw [intv, sum_insert (by simp), sum_insert (by simp)]
      dsimp only [B] at prior ⊢
      rw [sieveStages]
      by_cases hp : (k+1).Prime
      · have hs : a < k+1 ∧ (k+1).Prime := ⟨by omega, hp⟩
        rw [if_pos hs, batchPhi, if_pos hp, if_pos hp]
        have frontier := termsBefore_succ hkb cut
        rw [if_pos hp] at frontier
        change _ = advanceTerms cut _ _ at frontier
        rw [show termsBefore cut b (k+1) ++ keptProducts chi3 cut (k+1)
             (termsBefore cut b (k+1)) = termsBefore cut b k from frontier.symm, prior]
        have h := row_split x cut b (k+1) hp
        unfold rowTerms at h
        omega
      · rw [if_neg (fun q => hp q.2), if_neg hp, if_neg hp, zero_add, zero_add]
        have hf := termsBefore_succ hkb cut
        rw [if_neg hp] at hf
        rwa [← hf]
  have doneAt := through b hb (le_refl b)
  have start : termsBefore cut b b = [(1,1)] := by simp [termsBefore, sieveStages_empty]
  dsimp only [B] at doneAt
  rw [start, ← signed_batch_formula x cut a b hb] at doneAt
  exact doneAt

end SunPrimePermutation
end

section
namespace SunPrimePermutation

theorem disproof_of_one_exact_sum (h : signedPhi 8477 608981813029 = 17616) :
    ¬ (type_of% @OMA.S_oeis_a321727.main) :=
  disproof_of_meissel_certificates h SunPrimeNumeric.Slim.semiprime_exact

theorem disproof_of_leaf_totals
    (ho : ordinaryTotal 608981813029 8477 17 8477 = 57)
    (he : easyTotal 608981813029 8477 17 8477 = 9618)
    (hh : hardTotal 608981813029 8477 17 8477 = 7941) :
    ¬ (type_of% @OMA.S_oeis_a321727.main) := by
  apply disproof_of_one_exact_sum
  rw [phi_three_classes (a := 17) (cut := 8477) (by decide), ho, he, hh]
  decide

end SunPrimePermutation
end

section
namespace SunPrimePermutation

theorem mem_stages {a b q : ℕ} :
    q ∈ sieveStages a b ↔ a < q ∧ q ≤ b ∧ q.Prime := by
  induction b with
  | zero => simp [sieveStages]; omega
  | succ b ih =>
    rw [sieveStages]
    split_ifs with h
    · simp only [List.mem_cons, ih]
      constructor
      · rintro (rfl | ⟨h₁,h₂,h₃⟩)
        · exact ⟨h.1, le_rfl, h.2⟩
        · exact ⟨h₁, by omega, h₃⟩
      · rintro ⟨ha,hb,hp⟩
        by_cases e : q = b+1
        · exact Or.inl e
        · exact Or.inr ⟨ha, by omega, hp⟩
    · rw [ih]
      constructor
      · rintro ⟨h₁,h₂,h₃⟩
        exact ⟨h₁, by omega, h₃⟩
      · rintro ⟨h₁,h₂,h₃⟩
        have hn : q ≠ b+1 := by intro e; subst q; exact h ⟨h₁,h₃⟩
        exact ⟨h₁, by omega, h₃⟩

theorem stages_nodup (a b : ℕ) : (sieveStages a b).Nodup := by
  induction b with
  | zero => simp [sieveStages]
  | succ b ih =>
    rw [sieveStages]
    split_ifs <;> simp [ih, mem_stages]

def singles (qs : List ℕ) : List SignedProduct :=
  (1,1) :: qs.map (fun q => (q, -chi3 q))

theorem kept_singles {cut p : ℕ} (qs : List ℕ) (hp : p ≤ cut)
    (hall : ∀ q ∈ qs, cut < q*p) :
    keptProducts chi3 cut p (singles qs) = [(p,-chi3 p)] := by
  have noMore :
      List.filter (fun dc : SignedProduct => decide (dc.1 ≤ cut))
        ((qs.map (fun q => (q, -chi3 q))).map (addPrime chi3 p)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro dc hd
    obtain ⟨old, hOld, rfl⟩ := List.mem_map.mp hd
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hOld
    simp [addPrime, Nat.not_le_of_gt (hall q hq)]
  have unit : addPrime chi3 p (1,1) = (p,-chi3 p) := by simp [addPrime]
  simp only [keptProducts, singles, List.map_cons, unit, List.filter_cons, hp,
    decide_true, if_true, noMore]

theorem products_gt {z cut p q : ℕ} (hz : cut < z*z) (hp : z ≤ p) (hq : z ≤ q) :
    cut < q*p := hz.trans_le (Nat.mul_le_mul hq hp)

theorem fold_singles {z cut : ℕ} (hz : cut < z*z) (prior ps : List ℕ)
    (hprior : ∀ q ∈ prior, z ≤ q) (hps : ∀ q ∈ ps, z ≤ q ∧ q ≤ cut) :
    ps.foldl (advanceTerms cut) (singles prior) = singles (prior++ps) := by
  induction ps generalizing prior with
  | nil => simp
  | cons p ps ih =>
    obtain ⟨hpz, hpc⟩ := hps p (.head _)
    have hk := kept_singles prior hpc (fun q hq => products_gt hz hpz (hprior q hq))
    rw [List.foldl_cons]
    change ps.foldl (advanceTerms cut) (singles prior ++ keptProducts chi3 cut p (singles prior)) = _
    rw [hk]
    have concat : singles prior ++ [(p, -chi3 p)] = singles (prior++[p]) := by simp [singles]
    rw [concat, ih]
    · simp
    · intro q hq
      simp only [List.mem_append, List.mem_singleton] at hq
      rcases hq with h | rfl
      · exact hprior q h
      · exact hpz
    · exact fun q h => hps q (.tail _ h)

theorem before_high {cut b p : ℕ} (hcut : b ≤ cut) (hp : cut < p*p) :
    termsBefore cut b p = singles (sieveStages p b) := by
  apply fold_singles (z := p) hp [] (sieveStages p b) (by simp)
  intro q hq
  obtain ⟨hl,hr,_⟩ := mem_stages.mp hq
  exact ⟨hl.le, hr.trans hcut⟩

theorem all_finished_singles {cut b p : ℕ} (hb : b ≤ cut) (hp : p ≤ cut)
    (hcut : cut < p*p) : rowTerms cut b p =
      (sieveStages p b).map (fun q => (q*p, chi3 q*chi3 p)) := by
  unfold rowTerms
  rw [before_high hb hcut]
  unfold finishedProducts singles
  simp only [List.map_cons, addPrime, one_mul, List.filter_cons,
    Nat.not_lt_of_ge hp, decide_false, Bool.false_eq_true, if_false, List.map_map]
  have hm : (addPrime chi3 p ∘ (fun q => (q, -chi3 q))) =
       (fun q => (q*p, chi3 q*chi3 p)) := by funext q; simp [Function.comp_def, addPrime]
  rw [hm]
  apply List.filter_eq_self.mpr
  intro dc hd
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hd
  have hqp := (mem_stages.mp hq).1.le
  simpa [Function.comp_def, addPrime] using (products_gt hcut (le_refl p) hqp)

end SunPrimePermutation
end

section
namespace SunPrimePermutation
open Finset

theorem weighFront_zero (terms : List SignedProduct) :
    weighFront terms (fun _ => 0) = 0 := by induction terms <;> simp_all [weighFront]

theorem ordinary_fold (f : ℕ → ℤ) (x cut : ℕ) (ps : List ℕ) (terms : List SignedProduct) :
    batchPhi chi3 f (fun _ _ => 0) x cut ps terms =
      weighFront (ps.foldl (advanceTerms cut) terms) (fun d => f (x/d)) := by
  induction ps generalizing terms with
  | nil => rfl
  | cons p ps ih => rw [batchPhi, weighFront_zero, add_zero, ih]; rfl

theorem stage_sum (f : ℕ → ℤ) {a b : ℕ} (h : a ≤ b) :
    ((sieveStages a b).map f).sum = ∑ p ∈ Ioc a b, if p.Prime then f p else 0 := by
  induction b, h using Nat.le_induction with
  | base => simp [sieveStages_empty]
  | succ b h ih =>
    have hi : Ioc a (b+1) = insert (b+1) (Ioc a b) := by
      ext p
      simp only [mem_Ioc, mem_insert]
      omega
    rw [hi, sum_insert (by simp), sieveStages]
    by_cases hp : (b+1).Prime
    · have hh : a < b+1 ∧ (b+1).Prime := ⟨by omega, hp⟩
      simp [hh, ih]
    · simp [hp, ih]

def lowOrd (x cut a k d : ℕ) : ℤ :=
  cutPhi chi3 (signedPhi a) (fun _ _ => 0) x cut (sieveStages a k) d

theorem ordinary_high {x cut a k b : ℕ} (hak : a ≤ k) (hkb : k ≤ b)
    (hbc : b ≤ cut) (hk : cut < k*k) :
    ordinaryTotal x cut a b = lowOrd x cut a k 1 +
      ∑ p ∈ Ioc k b, if p.Prime then (-chi3 p) * lowOrd x cut a k p else 0 := by
  have init := before_high (b := b) (p := k) hbc hk
  unfold termsBefore at init
  unfold ordinaryTotal termsBefore
  rw [stages_append hak hkb, List.foldl_append, init, ← ordinary_fold, batchPhi_eq]
  simp only [singles, weighFront, List.map_cons, List.sum_cons, List.map_map, one_mul]
  change _ + ((sieveStages k b).map (fun p => (-chi3 p) * lowOrd x cut a k p)).sum = _
  rw [stage_sum _ hkb]
  rfl

end SunPrimePermutation
end

section
namespace SunPrimePermutation
open Finset

def tinyPrimes : List ℕ := [89,83,79,73,71,67,61,59,53,47,43,41,37,31,29,23,19]

theorem tinyPrimes_eq : sieveStages 17 93 = tinyPrimes := by decide +kernel

theorem cutPhi_pruned (w f : ℕ → ℤ) (x cap d : ℕ) (ps : List ℕ)
    (exceed : ∀ p ∈ ps, cap < d*p) :
    cutPhi w f (fun _ _ => 0) x cap ps d = f (x/d) := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    rw [cutPhi, if_pos (exceed _ (.head _)), ih (fun q h => exceed q (.tail _ h))]
    simp

def fastOrd (d : ℕ) : ℤ :=
  let f := fun n => signedPhi 17 (n%510510)
  if 8477 < d*19 then f (608981813029/d)
  else cutPhi chi3 f (fun _ _ => 0) 608981813029 8477 tinyPrimes d

theorem fastOrd_eq (d : ℕ) : fastOrd d = lowOrd 608981813029 8477 17 93 d := by
  have wheel : (fun n => signedPhi 17 (n%510510)) = signedPhi 17 := by
    funext n
    exact (signedPhi_wheel n).symm
  unfold fastOrd lowOrd
  rw [wheel, tinyPrimes_eq]
  split_ifs with high
  · apply Eq.symm
    apply cutPhi_pruned
    intro q hq
    have bound : ∀ i ∈ tinyPrimes, 19 ≤ i := by decide
    exact high.trans_le (Nat.mul_le_mul_left d (bound q hq))
  · rfl

end SunPrimePermutation
end

section
namespace SunPrimePermutation

def fastStages (a b : ℕ) : List ℕ :=
  SunPrimeNumeric.ds8500.reverse.filter (fun q => decide (a < q ∧ q ≤ b))

theorem stages_desc (a b : ℕ) : (sieveStages a b).Pairwise (· > ·) := by
  induction b with
  | zero => simp [sieveStages]
  | succ b ih =>
    rw [sieveStages]
    split_ifs
    · apply List.pairwise_cons.mpr
      exact ⟨fun q h => Nat.lt_succ_of_le (mem_stages.mp h).2.1, ih⟩
    · exact ih

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem primeList_chain : SunPrimeNumeric.ds8500.IsChain (· < ·) := by decide +kernel

theorem fastStages_eq {a b : ℕ} (hb : b ≤ 8500) : sieveStages a b = fastStages a b := by
  apply List.Pairwise.eq_of_mem_iff (stages_desc a b)
  · apply List.Pairwise.filter
    apply List.pairwise_reverse.mpr
    exact List.isChain_iff_pairwise.mp primeList_chain
  · intro q
    simp only [mem_stages, fastStages, List.mem_filter, List.mem_reverse,
      SunPrimeNumeric.ds8500_correct, decide_eq_true_eq]
    exact ⟨fun h => ⟨⟨h.2.2, h.2.1.trans hb⟩, h.1, h.2.1⟩,
      fun h => ⟨h.2.1, h.2.2, h.1.1⟩⟩

end SunPrimePermutation
end

section
namespace SunPrimePermutation

def packedWheel7 : ℕ := 0x899999999998899998899998888887788888899998899998888887777776677777788887788888899998888887777777788887788887788887777777788888899998888887788887777776677777788888899998899998888887788888899998899998899999999998

def lookup7 (x : ℕ) : ℤ := (((packedWheel7 >>> (4*(x%210))) % 16 : ℕ) : ℤ) - 8

set_option maxRecDepth 8192 in
private theorem all7 : (List.range 210).all (fun x => decide (lookup7 x = signedPhi 7 x)) = true := by
  decide +kernel

theorem lookup7_eq (x : ℕ) : lookup7 x = signedPhi 7 x := by
  have certified := of_decide_eq_true (List.all_eq_true.mp all7 (x%210)
    (List.mem_range.mpr (Nat.mod_lt _ (by decide))))
  have per : signedPhi 7 x = signedPhi 7 (x%210) := by
    have zero : signedPhi 7 210 = 0 := by decide +kernel
    have cap : primorial 7 = 210 := by decide +kernel
    unfold signedPhi at zero ⊢
    rw [phiEval_eq _ _ chi3_mul chi3_prefix, cap] at zero
    rw [phiEval_eq _ _ chi3_mul chi3_prefix, phiEval_eq _ _ chi3_mul chi3_prefix, cap]
    exact rough_mod_period _ (by decide) zero x
  rw [per]
  simpa only [lookup7, Nat.mod_mod] using certified

def liftPhi (p : ℕ) (f : ℕ → ℤ) (x : ℕ) := f x - chi3 p * f (x/p)

def lookup17 := liftPhi 17 (liftPhi 13 (liftPhi 11 lookup7))

theorem lookup17_eq : lookup17 = signedPhi 17 := by
  have rep : lookup7 = signedPhi 7 := funext lookup7_eq
  unfold lookup17
  rw [rep]
  rfl

def compactOrd (d : ℕ) : ℤ :=
  if 8477 < d*19 then lookup17 (608981813029/d)
  else cutPhi chi3 lookup17 (fun _ _ => 0) 608981813029 8477 tinyPrimes d

theorem compactOrd_eq (d : ℕ) : compactOrd d = fastOrd d := by
  have rem : (fun n => signedPhi 17 (n%510510)) = signedPhi 17 :=
    funext (fun n => (signedPhi_wheel n).symm)
  unfold compactOrd fastOrd
  rw [lookup17_eq, rem]

def compactOrdSum : ℤ := compactOrd 1 +
  ((fastStages 93 8477).map (fun q => (-chi3 q)*compactOrd q)).sum

theorem compactOrdSum_eq : compactOrdSum = ordinaryTotal 608981813029 8477 17 8477 := by
  rw [ordinary_high (a := 17) (k := 93) (by decide) (by decide) (by decide) (by decide),
    ← stage_sum _ (by decide : 93 ≤ 8477), fastStages_eq (by decide : 8477 ≤ 8500)]
  unfold compactOrdSum
  simp only [compactOrd_eq, fastOrd_eq]

end SunPrimePermutation
end

section
namespace SunPrimePermutation
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ordinary_compact_exact : ordinaryTotal 608981813029 8477 17 8477 = 57 :=
  compactOrdSum_eq.symm.trans (by decide +kernel)
end SunPrimePermutation
end

section
namespace SunPrimePermutation
open Finset

theorem term_bound {cut b p : ℕ} (hcap : 1 ≤ cut) (dc : SignedProduct)
    (hd : dc ∈ termsBefore cut b p) : dc.1 ≤ cut := by
  have foldBound (ps : List ℕ) (terms : List SignedProduct)
      (ht : ∀ e ∈ terms, e.1 ≤ cut) :
      ∀ e ∈ ps.foldl (advanceTerms cut) terms, e.1 ≤ cut := by
    induction ps generalizing terms with
    | nil => exact ht
    | cons s ps ih =>
      apply ih
      intro e he
      rcases List.mem_append.mp he with old | next
      · exact ht e old
      · exact of_decide_eq_true (List.mem_filter.mp next).2
  apply foldBound _ [(1,1)] _ dc hd
  simpa using hcap

theorem row_product_bounds {cut b p : ℕ} (hc : 1 ≤ cut) {dc : SignedProduct}
    (hd : dc ∈ rowTerms cut b p) : cut < dc.1 ∧ dc.1 ≤ cut*p := by
  obtain ⟨hm,hf⟩ := List.mem_filter.mp hd
  obtain ⟨old,ho,rfl⟩ := List.mem_map.mp hm
  exact ⟨of_decide_eq_true hf, Nat.mul_le_mul_right p (term_bound hc old ho)⟩

private theorem no_easy_small {p m : ℕ} (hp : p ≤ 415) (hm : 0 < m) (hm' : m ≤ 8477*p) :
    p^2 ≤ 608981813029/m := by
  apply (Nat.le_div_iff_mul_le hm).mpr
  have u := Nat.mul_le_mul (Nat.pow_le_pow_left hp 2) (hm'.trans (Nat.mul_le_mul_left 8477 hp))
  exact u.trans (by decide)

theorem easyRow_small (p : ℕ) (hp : p ≤ 415) :
    easyRow 608981813029 8477 8477 p = 0 := by
  have empty : ((rowTerms 8477 8477 p).filter (fun dc => decide (608981813029/dc.1 < p^2))) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro dc hd
    obtain ⟨hl,hu⟩ := row_product_bounds (by decide : 1 ≤ 8477) hd
    simp [Nat.not_lt_of_ge (no_easy_small hp (by omega) hu)]
  simp [easyRow, empty, weighFront]

theorem prime_le_8467 {p : ℕ} (hp : p.Prime) (hi : p ≤ 8477) : p ≤ 8467 := by
  by_contra! gt
  interval_cases p <;> norm_num at hp

def pairContribution (p q : ℕ) : ℤ := if p < q ∧ 608981813029/(p*q) < p^2 then
  chi3 p * chi3 q * (1 + primeWeight (608981813029/(p*q)) - primeWeight (p-1)) else 0

theorem sum_stages_primes (f : ℕ → ℤ) {p b : ℕ} (hp : p ≤ b) :
    ((sieveStages p b).map f).sum =
      ∑ q ∈ Nat.primesLE b, if p < q then f q else 0 := by
  rw [stage_sum _ hp, ← sum_filter, ← sum_filter]
  apply sum_congr _ (fun _ _ => rfl)
  ext q
  simp only [mem_filter, mem_Ioc, Nat.mem_primesLE]
  tauto

private theorem filtered_pairs (p : ℕ) (hp : p.Prime) (ps : List ℕ)
    (hq : ∀ q ∈ ps, p < q ∧ q ≤ 8477) (bound : p ≤ 8477) :
    weighFront (((ps.map (fun q => (q*p, chi3 q*chi3 p))).filter
      (fun dc => decide (608981813029/dc.1 < p^2)))) (fun d => easyValue p (608981813029/d)) =
      (ps.map (pairContribution p)).sum := by
  induction ps with
  | nil => simp [weighFront]
  | cons q ps ih =>
    obtain ⟨hpq,hqb⟩ := hq q (.head _)
    have rest := ih (fun t h => hq t (.tail _ h))
    have hpos : 0 < p*q := Nat.mul_pos hp.pos (hp.pos.trans hpq)
    have hbound := prime_le_8467 hp bound
    have prod_le : p*(p*q) ≤ 608981813029 :=
      (Nat.mul_le_mul hbound (Nat.mul_le_mul hbound hqb)).trans (by decide)
    have hdiv : p ≤ 608981813029/(p*q) := (Nat.le_div_iff_mul_le hpos).mpr prod_le
    have hn : 608981813029/(p*q) ≠ 0 := by have := hp.pos; omega
    have hmin : min (p-1) (608981813029/(p*q)) = p-1 := min_eq_left (by omega)
    simp only [List.map_cons, List.filter_cons, List.sum_cons]
    by_cases he : 608981813029/(p*q) < p^2
    · simp only [Nat.mul_comm q p, he, decide_true, if_true]
      have consFormula (dc : SignedProduct) (ds : List SignedProduct) (f : ℕ → ℤ) :
          weighFront (dc::ds) f = dc.2*f dc.1 + weighFront ds f := rfl
      rw [consFormula, rest]
      simp [pairContribution, hpq, he, easyValue, hn, hmin, mul_comm (chi3 q) (chi3 p)]
    · simp only [Nat.mul_comm q p, he, decide_false, Bool.false_eq_true, if_false]
      rw [rest]
      simp [pairContribution, he]

theorem easyRow_as_pairs {p : ℕ} (pr : p.Prime) (bound : p ≤ 8477) :
    easyRow 608981813029 8477 8477 p = ∑ q ∈ Nat.primesLE 8477, pairContribution p q := by
  by_cases small : p ≤ 415
  · rw [easyRow_small p small]
    symm
    apply sum_eq_zero
    intro q hq
    obtain ⟨hqb,qp⟩ := Nat.mem_primesLE.mp hq
    have hv := no_easy_small (p := p) (m := p*q) small (Nat.mul_pos pr.pos qp.pos)
      (by simpa [Nat.mul_comm] using Nat.mul_le_mul_left p hqb)
    simp [pairContribution, Nat.not_lt_of_ge hv]
  · have h0 : 8477 < p*p :=
      lt_of_lt_of_le (by decide : 8477 < 416*416) (Nat.mul_le_mul (by omega) (by omega))
    unfold easyRow
    rw [all_finished_singles (le_refl _) bound h0, filtered_pairs p pr _ _ bound, sum_stages_primes _ bound]
    · apply sum_congr rfl
      intro q _
      by_cases h : p < q <;> simp [pairContribution,h]
    · intro q hq
      have h := mem_stages.mp hq
      exact ⟨h.1,h.2.1⟩

theorem easy_as_double_sum :
    easyTotal 608981813029 8477 17 8477 =
    ∑ p ∈ Nat.primesLE 8477, ∑ q ∈ Nat.primesLE 8477, pairContribution p q := by
  unfold easyTotal
  rw [← stage_sum _ (by decide : 17 ≤ 8477), sum_stages_primes _ (by decide : 17 ≤ 8477)]
  apply sum_congr rfl
  intro p hp
  obtain ⟨bound,pr⟩ := Nat.mem_primesLE.mp hp
  by_cases h : 17 < p
  · rw [if_pos h, easyRow_as_pairs pr bound]
  · rw [if_neg h, ← easyRow_as_pairs pr bound, easyRow_small p (by omega)]

end SunPrimePermutation
end

section
namespace SunPrimeRaceEasy
open Finset SunPrimePermutation

/-- One bit every 6 places, for 2^t successive lanes. -/
abbrev spaced := SunPrimePermutation.stripe 6

theorem test_spaced (t i : ℕ) :
    (spaced t).testBit i = true ↔ i%6=0 ∧ i<6*2^t := by
  rw [SunPrimePermutation.stripe_bit]
  constructor
  · rintro ⟨k,hk,rfl⟩
    exact ⟨by simp,by omega⟩
  · rintro ⟨hm,hi⟩
    exact ⟨i/6,by omega,by omega⟩

def lane (t n j : ℕ) := (n >>> j) &&& spaced t

def selected (t n j : ℕ) : Finset ℕ :=
  (range (2^t)).filter (fun i => n.testBit (6*i+j))

theorem indices_lane (t n j : ℕ) : (lane t n j).bitIndices.toFinset =
    (selected t n j).image (fun i => 6*i) := by
  ext i
  simp only [List.mem_toFinset,Nat.mem_bitIndices,lane,Nat.testBit_and,
    Bool.and_eq_true,Nat.testBit_shiftRight,test_spaced,Finset.mem_image,
    selected,Finset.mem_filter,Finset.mem_range]
  constructor
  · rintro ⟨hh,hm,hl⟩
    have he : 6*(i/6)=i := by omega
    exact ⟨i/6,⟨by omega,by simpa [he,Nat.add_comm] using hh⟩,he⟩
  · rintro ⟨k,⟨hk,hm⟩,rfl⟩
    exact ⟨by simpa [Nat.add_comm] using hm,by simp,by omega⟩

private theorem residue_length (xs : List ℕ) (h : ∀ i∈xs,6∣i) :
    (xs.map (fun i => 2^i)).sum ≡ xs.length [MOD 63] := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    obtain ⟨k,hk⟩ := h a (by simp)
    have hz : 2^a ≡ 1 [MOD 63] := by
      rw [hk,pow_mul]
      simpa using (show 2^6 ≡ 1 [MOD 63] by decide).pow k
    simpa [Nat.add_comm] using hz.add (ih (fun i hi=>h i (by simp [hi])))

def countLane (t n j : ℕ) := lane t n j % 63

theorem countLane_eq (t n j : ℕ) (ht : 2^t<63) :
    countLane t n j=(selected t n j).card := by
  let b := lane t n j
  have he := indices_lane t n j
  have hi : ∀ i∈b.bitIndices,6∣i := by
    intro i h
    have hm : i∈(lane t n j).bitIndices.toFinset := List.mem_toFinset.mpr h
    rw [he] at hm
    obtain ⟨k,hk,he⟩:=Finset.mem_image.mp hm
    exact ⟨k,he.symm⟩
  have hc : b.bitIndices.length = (selected t n j).card := by
    rw [← List.toFinset_card_of_nodup b.bitIndices_nodup,he,Finset.card_image_of_injective]
    intro x y h; change 6*x=6*y at h; omega
  have hs : (selected t n j).card≤2^t := by
    simpa [selected] using Finset.card_le_card (Finset.filter_subset _ (range (2^t)))
  have hh := residue_length b.bitIndices hi
  rw [Nat.sum_map_two_pow_bitIndices,hc] at hh
  change b % 63 = (selected t n j).card % 63 at hh
  exact Eq.trans hh (Nat.mod_eq_of_lt (lt_of_le_of_lt hs ht))

theorem partial_card {n k r : ℕ} (hk : k ≤ 192) (hr : r < 6) :
    countLane 5 (n % 2^k) r = ((range k).filter (fun i => i % 6 = r ∧ n.testBit i)).card := by
  rw [countLane_eq _ _ _ (by decide)]
  apply Finset.card_bij (fun i _ => 6*i+r)
  · intro i hi
    obtain ⟨hi,hbit⟩ := Finset.mem_filter.mp hi
    simp only [Nat.testBit_mod_two_pow, Bool.and_eq_true, decide_eq_true_eq] at hbit
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hbit.1, by omega, hbit.2⟩
  · intro a ha b hb he; omega
  · intro i hi
    obtain ⟨hib,hir,hbit⟩ := Finset.mem_filter.mp hi
    have hlt := Finset.mem_range.mp hib
    have he : 6*(i/6)+r=i := by omega
    refine ⟨i/6, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by norm_num; omega), ?_⟩, he⟩
    simp only [he,Nat.testBit_mod_two_pow,Bool.and_eq_true,decide_eq_true_eq]
    exact ⟨hlt,hbit⟩

def subrank (mask k : ℕ) : ℤ :=
  (countLane 5 (mask % 2^k) 1 : ℤ) - countLane 5 (mask % 2^k) 5

theorem subrank_eq {start mask k : ℕ} (hs : 2 < start) (hs6 : start % 6 = 0)
    (hk : k ≤ 192) (hm : ∀ j < k, mask.testBit j = true ↔ (start+j).Prime) :
    subrank mask k = primeWeight (start+k-1) - primeWeight (start-1) := by
  have hcard (r : ℕ) (hr : r < 6) :
      (countLane 5 (mask % 2^k) r : ℤ) =
        ∑ j ∈ range k, (if j%6=r ∧ (start+j).Prime then (1 : ℤ) else 0) := by
    rw [partial_card hk hr, Finset.sum_boole]
    congr 2
    ext j
    simp only [mem_filter, mem_range]
    by_cases hj : j < k
    · simp [hj, hm j hj]
    · simp [hj]
  rw [subrank, hcard 1 (by decide), hcard 5 (by decide), ← Finset.sum_sub_distrib]
  have heq : (∑ j ∈ range k, ((if j%6=1 ∧ (start+j).Prime then (1:ℤ) else 0) -
      (if j%6=5 ∧ (start+j).Prime then (1:ℤ) else 0))) =
      ∑ j ∈ range k, if (start+j).Prime then chi3 (start+j) else 0 := by
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hp : (start+j).Prime
    · have ho := hp.mod_two_eq_one_iff_ne_two.mpr (by omega)
      simp only [hp, and_true, if_true, chi3]
      split_ifs <;> omega
    · simp [hp]
  rw [heq]
  unfold primeWeight
  simp only [Nat.primesLE_eq_filter_range,Finset.sum_filter]
  rw [show start+k-1+1 = start+k by omega,show start-1+1 = start by omega,
    Finset.sum_range_add]
  omega

def easyPairs (x b : ℕ) : ℤ :=
  ∑ p ∈ Nat.primesLE b, ∑ q ∈ Nat.primesLE b,
    if p < q ∧ x/(p*q) < p^2 then chi3 p * chi3 q *
      (1 + primeWeight (x/(p*q)) - primeWeight (p-1)) else 0

end SunPrimeRaceEasy

namespace SunPrimeRaceEasy
open SunPrimeNumeric SunPrimePermutation

def lowBits : ℕ := 0x820008800a08800000028020208020000020020800228800220800008228028020000800808820008000008208020228200200820008000020a00020000000800a00220808008200008a20800200200208200000220000000a20020008820008808820220000208800020008800a08220028028220208200808028220000a08000200020800020000020000a00028020028020008000000208820200828800208020000808000028200208000008020020008800808200220808208828028000000208808000800a08200020228800008028028000a00000220008020a00a00820028200020000800808000220a08028800020200000008020220000a00000820000020200820828200820208208028008020a08200800020220808a00000200800808028020200200a00820800208820200008800008200000020008008800008200028028220a08800820208200808800000020a20000208020220800200a28828000800000008020220820000008828008a00008a08000020a20800a20808208200000008800200800208200028200200000228800020020200808800208000000820828008220000808008000a00a08820800228020808228008020800200208020000000800220028228800000808000220a00008008008200820a08a00020000820808000820028000008a20800200a00008208820000a00200208000200820200a00800000020208028028200a00a00a08020000020000a20008228000800828008200020a00000828208a00200000800008800a08a08800020220008028800200a00008220008028200000820808020220800228008000820808220800200a00800a00828228020800808000028a20200020000208000a00028028008800a08820828000000800a28000020220208008820028800000200028020000208800820020220008808028000000a08220008008020208200808000220808220008000a20a00200800220200a00828808228820808a00800200220200028008000020a08808020000800000220808008220008208008220a20800208828200000a00220820228000808a00020208800000800020200a20a00028008028a00208020008028020808a20808200000a00028000208200200a28820008000808008020028820000820820200a00200a20000028820000200828228220008808808220800808008008228a00800828808228800200800020208200000000828008a20a08a00008020020a08220020208200808028000020820208228800020a00a00828028220020808208800208220200808800008a20008a20008028a00a00200800220220808820808020200808220028208a00800a20828208020a08200820000a00208808808008a20208828028020220208820808228020800228800200a20a08208028228800800a28028208820a00a08800228a20208828828208a20a08a28ac
def rankBank : ℕ := 0x82817f847f807e7c7e817976727471737374767173747475767a7b7b79767d81837e7979757870706c6e6f6b6b71717072726d6c6d6e6e6c6c6f737675756f6c6b696b6b67696c6667686262605e5b5b606065615f64605f606365676060636363665f5858565a5f5f62605b5c5b5a555657555154555652514f4d505053515050505053504f51534f50514c4f4e5152514f535254515153535150514b4a494e5052504d5056565252545353565754555a59575e5f5f5f5e5c5b5a5d5b595959535057575e61605f6163615f6361605c5d5c5d5a5d5a565a58575a5f605a585756565e5a595c5d5e6564616569686664656460626461626565625e615b65636260636365626163666664646365635e5c5d5f5e5b5d5e59575252565751504a4a4c4b4e4e4e51515351555355565859575555504d4e515150505554595b5a5a5f595d5d5b575556545054545455514f4b4e505250504d4e4d4e524c4a4e504b4c4d5255545359595a585a5b5a5a5d5c5e5b5f5d5f6061605a585652535754554e4e484a4a4e525354545450524e47484b4b504d514c474a453f3e3d4044444345494746474b4c4c4f515454555453555255545656535556565456565d58595a5b57595b5e5e5e5e60646162655f5c5a575959595c5f5c5d58585b59585a5d61646364615e5d5c605d5f616260605f626366656562636262615a585a5b5b58595a5c5d5e5f5f5e616060615e63636b6a6d6d706c6d6f7274726e6e716f696360636363656260605d5f6060605f5f5c5b5c6361605f61605e5c5e575957545758575557545a57575b5b5c575956585858595c5e5e5e605f615f5c5b5e60615c5d5b57595759595c5d5a5d5f5c5b5958545657595a5c58585a585a59585857595451524d4e504f4b4b49464846464345454547443f3d4143403e3f45474a5051514c4c4f50555054535757544f50555452515251514a4946414143424240444442403b3b3b414042413e3d36393b3c39393c413f424244484545434544413f3f4647464846464b464749504f4a4b4a4c515455515653544f4c504d474247494944474d4d4d4b49494c4a4c45474545484c4a464b494b4d4d4c4b4b4e5256595854535254565350525454515452565355595f5f5f5c606163625f5d595c5a5358565652545551565c5f5f5f616365625e5f5e5f5a5a5b5a5a5b585b59595155545554544e4d5051504f504b4f55555852514f4d4c4e4e4e4a46474548454d484c4e4d4c47484a4a4b4a4a47474142403b3c3e403b3937333235333232312b2b29252629232a2b292c2b2a2d3131312f2e292c28282b29292b2b2c2b2c2c2e3437333533363737393e393e3d40403d3f3d3b3a3d40414543434041434645484745433e3f424243474541444243464647464945494b4a4b4f5050494c4c494c4b44404140413c43454240464142474447494d5052535153524f4c4f4a494a4c4b4d4e4e4a4b4c4f524f51504d4c47494947434648484948494b4a4944403c3d41414444454b484a4a4a4a4644434544404342413f43474849474644494b4c4c5453504e4c504e4c4947454444454645424242423f3d3c3e3e4040424a44484a4646403d3f454543413f3e3d3637342f2f2e323233353332373333343236373a3c3c3e3e3b3b3b3f423d37393b3a38383637363637333538393a373832312f2e2e30322f2f312e322e343334363634353636363539383434302e2c2d312d2f302e2f303231313432323331332d2d2a2b292a272e3430303337383a3b3736332e2d2e2d2f333133322f302d292928292a24272928292526272a2728262626252c282824252626262523211f1e1b1a1a1c1c1c1c1d21211f22242322232127222928262728282724222725272727232526232526262829292727282a2928242623282d2b2a302f2e2c272c2a292b2e2d302f32302e29292c292d2d323136373a3b3e3e4244494645434c4d4946464544494543414345454440424541414344434443403c41464847464642434444454440404140454342404646484a48454a4947454e4b4a4c4c484545444747423f3d3a353a393536383b3e393a3a3c3c3d403c3b38363838373232333132312e2f2e3131302e312e2e322d2b2c2b2c2a2a2a27282b2d2e2d2e3436303130303032312f2f323331313130363538393c3731302d2c292a2e30302e2d2d3031312e2f2d2c2f30332f2d2d32312d2f2e2928252728282929292b2b2525252125292b292d2b29292526282a282426272526212126282c2a2d2a29292d2c32302a2c2e302f2d28272929292f32373c3b393b3c3b413d3d3e41423f3d3e3a3c3f403e40403f3d3a383a36322e2d2f2f2e2b34353638373838352f2c313130363838363432333536393a3d423e3e4144423e3f3d3d3f3e3b3c403e403e3d3f4540403d3d3c3a3a38362c2f30312d2c2a2d2d2d2e2f2f33302d302e2d2e2b2c322e3032353533363634352e302f3234322f333532333933363235343632353b3e41403c3c404744413f4046444847494343464a484745444c4a45464545403f3f454342444444454346434944474a4b4a4c4e4e4d484745454644413e4242443b454847484343404244444543413d3f4140403a3a323339363437363032363333363b393c3c4143423e44403b3e3c3e3d3e4042453f4143414345444642413f4440414448474a514e4f5451504a4c4a5044444a5053535353575453514c4b4c4b4b4948494b4b484c46474b4d4e4a454948494b4a4a474947494c4e545152534c4c48494f4d4f49494a4b4c46464b4d4c504b50514b4f4d4d4f4e4b4c4d4d4c4e4d4e5453524e4f4d4f4c494b4a4b4948444647484c494a49474745413d40413f3f3e3d3f3f4448494a484a4c4c46443f4044454140403f41433d3d413f413e3e3f3d3c3f3d3d3d3d3e403d39373c38353a35383c3f434244433f403d3b393b3a4042444742424245403c3c3e373738363a3b3a383b393c3b3d3c40423e3b393b3d403e3f3c44434141474d4d4d45444248474645433e3d403f403d3f40433c3a39353638363536373a3a3a3c3d3a3b37353737363d393334373c3839383a3b3e3e3d3f3e3e3c3d42403b3a3b3c393c383a393838383836393f3d3c3b3b3a3c3f3f3e40404340413c38393c454145454441404244434345444545443f413e3b3b3c39383936322f31373539383938393f3c3c3c3d3e413f434044434341433d403d3b3b38393c3e3a353537363937373a36333436322f34322c2e2827282c272d2d2c29282a262625262827272d2a2f2825272a2c2c2c2c30302e333436313235373536322e2a272b2a2c2b28292b292c2f2e2d32353432333732322d323333352f2b2a292927292a2a292b2c2a2a2a2b2c2c31312e2d2c2d2d2e2e3233332f3332332f2d323136342f333131322f2d2e3031333837373432333935333032333332342e2f2f2f2d2b2d2d2e272a2b2c2d2e34302d28282926292b2c2f3332343738363338363b403e3b3c3b3d3d3a3d3a3e3e3b3c3e393b3c3b4041403e3c3a3d3e45423f3e3b4341444646464744423c3d444a474648474545464747494b4b4948474848494b4d4c4c4d4a4c4c4f4e4d4c4c4a4d494a4846474843404443404446494340414244434440424647413f3a3a3c3b3b39393c3e3d40413d37353635312f2f302e2d2d2a2c282a2728292c2a272b282e30333732353131312f303233353434343434333431323132353336383532333433363337393d41413f403f3b3b3f3d414446403c3d3f3e423e3d403c3c3e3b3c3b3e3f3d3f363935353734363133343739343232343333323a383a3d40403f41403f3c3b3d3a40454648484b45423c3c37322f2d2d292e2b302d30312d2a2c2828262825292d2f302c2e2f2f31302e34353538383b33363537383638343737393a3c393632302d3031302e2a2b2e2c2f2b282a313031302f2e2d29272726252a2624272524252322272623232a282a28292c2d2d2e2b30313137373a36383732353434343638353330302e2c262424272928252625212621262b2e2b262122222124211e1a1e191e1f1d1e1e22252221222024242526252827221f1d161f1f1f222322262626212021242321262a28262528272525252923232823211f1f1b1919181f1e1d1f211f1f1f1a1e1c1e1e201e21201e1d1e1a19191a1a1c1a181815101315131112110c0d0f1412110f0e0a0e0d0d090e07070a090a0706090607060b0a08090d0e0b090f0c101314120c0f0d0e11161e1d18141516171e1c1d1b1d1e1c1d1f221b1d1f1d2124252a282e2e302c32303333353935353837373c3b3d3a3c3a3a36373539373b3d3c3a3d383a3c39373736393a363b3d3d3636333132312b313233373938363a3a3f403f423f40433e41403f4042404043403d3c393c3a363536363536332f30332f2c2d2f30302e2b2b2b2b292928232a27282b2525242722212023262626272c2a282c333231302c2a2c2d2b302e322c2a2b2a2b272628262a292b2b2b2a2927232521212226241e23262421242421262324262729272525262b2b2c2a2d2f2b2e2b2c2b25252526282a2c292927262323221e211f1e22282b292c30343230313132353632383436363331302f3338393b3a3c3b3f3e3c3c3b383635343437373b3d3c3c3d3f3d423d3a3c3d40383536322f2f312d2e2f2e333536373835343030302d2e2d2825232021282b2e2c2d2d2a2a302e3435313636363131342f2c2e2f2c29292828252728292e2f31322e2d2e313030333534312e3231303130322e2e29282322211e211f191c202323242326232323252625272c2828242422202124272221211f242225201d1c1c191b19171817171915120f0c0c110c080e10100e101213100a090e0f10100f0f0f0f0f0e0f0f1412131a1414131515121013111515151b181d191c191a1818151a171211131617191b1d1f1d19181014171617151616171418161313181917191817181c1a1c1f1e201c1f191b1c1e2222262622262522222627232527242425242a2a2825262326292725232322262a2c272527252a292824251e1f1d1f21241f232023242a25282623272727262b2524292523211f2220222324272b2728231f2222262a25211d201f2020212424221b1e211c202221242523202327292a2c2d30312e2d2929252828242424262b2524221d211f1f1f181214191c1c1c191c1d1b191a1a1d1d1f1b1c1b1a191c1d1c1e1e1d1f1d1e1f191b1b181a1916191b1a19181a1a1d151216171d1d1c1917151917181b18191c1816191b1c1d181616191d1b18151818171d1b1617171c1b1a1b1f201c181b191b1d1b191918191c1e1c1a1b1b19191614100f1112171211101312101412140e0c0b0f13101416141612141411121615131011131619181a1f1c1d1d1c1d1c1d1f1f1d1a1518171c1a1b1a1b1717181816171412111011121316141a1b1b1b171516191d1d1b201f1d1b1d1f1d17120f0d12131410141217141411171a1a1b1518110c0d0c0c0c0b0c0a0e0e090b0b090a0b0d0d110e0b080b090d0e101015141918171816141317151a18161013141310100d11100b1112140d0d0c0c0a0c0c0f10100a06090f06050a0b0c0e120e10100d100d0a080c110e0d0a0d0d090a0b080b070807050b0c0c0a090a05090608090605070406030400
def allBits : ℕ := lowBits ||| (pBits <<< 8478)
def checkpoint (i : ℕ) : ℤ := -(((rankBank >>> (8*i)) % 256 : ℕ) : ℤ)
def startMask (i : ℕ) : ℕ := allBits >>> (192*i)
def weightAt (n : ℕ) : ℤ :=
  checkpoint (n/192) + subrank (startMask (n/192)) (n%192+1)

def smallList : List ℕ := ds8500.filter (fun p=>p≤8477)
def numericRow (p : ℕ) : ℤ :=
  let a := chi3 p
  let b := 1-weightAt (p-1)
  (smallList.map (fun q =>
    if p<q ∧ 608981813029/(p*q)<p^2 then
      a*chi3 q*(b+weightAt (608981813029/(p*q))) else 0)).sum

end SunPrimeRaceEasy


namespace SunPrimeRaceEasy
open SunPrimeNumeric SunPrimePermutation

private def maskOf : List ℕ → ℕ
  | [] => 0
  | a::as => 2^a ||| maskOf as

private theorem maskOf_iff (l : List ℕ) (n : ℕ) : (maskOf l).testBit n = true ↔ n ∈ l := by
  induction l with
  | nil => simp [maskOf]
  | cons a xs ih =>
    simp only [maskOf,Nat.testBit_or,Nat.testBit_two_pow,Bool.or_eq_true,
      decide_eq_true_eq,ih,List.mem_cons]
    tauto

private theorem lowBits_eq : lowBits = maskOf smallList := by decide +kernel

theorem smallList_iff {p : ℕ} : p ∈ smallList ↔ p.Prime ∧ p ≤ 8477 := by
  simp only [smallList, List.mem_filter, ds8500_correct, decide_eq_true_eq]
  exact ⟨fun h => ⟨h.1.1,h.2⟩,fun h => ⟨⟨h.1,by omega⟩,h.2⟩⟩

theorem allBits_correct {p : ℕ} (hr : p ≤ 780372) : allBits.testBit p = true ↔ p.Prime := by
  rw [allBits,Nat.testBit_or,Nat.testBit_shiftLeft,Bool.or_eq_true,Bool.and_eq_true,
    decide_eq_true_eq,lowBits_eq,maskOf_iff,smallList_iff]
  by_cases hb : p ≤ 8477
  · simp [hb,show ¬8478≤p by omega]
  · have hl : 8478 ≤ p := by omega
    have he : p-8478=p-cutB-1 := by unfold cutB; omega
    simp [hb,hl,he,pBits_correct (p:=p) (by exact Nat.lt_of_not_ge hb) hr]

private theorem block_subrank {i k : ℕ} (hi : 1 ≤ i) (hk : k ≤ 192)
    (hu : 192*i+k-1 ≤ 780372) :
    subrank (startMask i) k = primeWeight (192*i+k-1) - primeWeight (192*i-1) := by
  apply subrank_eq (by omega) (by omega) hk
  intro j hj
  rw [startMask,Nat.testBit_shiftRight]
  exact allBits_correct (by omega)

private def deltaOK (i : ℕ) : Bool :=
  decide (checkpoint (i+1) = checkpoint i + subrank (startMask i) 192)

private theorem checked_deltas : ∀ i : Fin 4064, 1 ≤ i.val →
    checkpoint (i.val+1) = checkpoint i.val + subrank (startMask i.val) 192 := by
  have ha : (List.range' 1 4063).all deltaOK = true := by
    set_option maxRecDepth 200000 in
      set_option maxHeartbeats 0 in decide +kernel
  intro i h
  have hm : i.val ∈ List.range' 1 4063 := by
    apply List.mem_range'.mpr
    exact ⟨i.val-1,by have := i.isLt; omega,by simp; omega⟩
  exact of_decide_eq_true (List.all_eq_true.mp ha i.val hm)

private theorem checkpoint_one : checkpoint 1 = primeWeight 191 := by
  decide +kernel

theorem checkpoint_eq {i : ℕ} (hi : 1 ≤ i) (hu : i ≤ 4064) :
    checkpoint i = primeWeight (192*i-1) := by
  induction i with
  | zero => omega
  | succ i ih =>
    by_cases hz : i=0
    · subst i; exact checkpoint_one
    · have hi' : 1 ≤ i := by omega
      have hd := checked_deltas ⟨i,by omega⟩ hi'
      change checkpoint (i+1) = checkpoint i + subrank (startMask i) 192 at hd
      rw [hd,ih hi' (by omega),block_subrank hi' (by decide) (by omega)]
      rw [show 192*(i+1)-1=192*i+192-1 by omega]
      omega

theorem weightAt_eq {n : ℕ} (hl : 192 ≤ n) (hu : n ≤ 780372) :
    weightAt n = primeWeight n := by
  have hi : 1≤n/192 := by omega
  rw [weightAt, checkpoint_eq hi (by omega), block_subrank hi (by omega) (by omega)]
  rw [show 192*(n/192)+(n%192+1)-1=n by omega]
  omega

end SunPrimeRaceEasy


namespace SunPrimeRaceEasy

def block (offset count : ℕ) : ℤ :=
  (((smallList.drop offset).take count).map numericRow).sum

def remaining (offset : ℕ) : ℤ := ((smallList.drop offset).map numericRow).sum

theorem split_remaining (i n : ℕ) : remaining i = block i n + remaining (i+n) := by
  have h := congrArg (fun l : List ℕ => (l.map numericRow).sum)
    (List.take_append_drop n (smallList.drop i))
  simpa only [block,remaining,List.map_append,List.sum_append,List.drop_drop] using h.symm

end SunPrimeRaceEasy


namespace SunPrimeRaceEasy
open Finset SunPrimePermutation

private theorem nd : smallList.Nodup := by
  have h : (List.range 8478).filter (fun d => lowBits.testBit d) = smallList := by
    set_option maxRecDepth 100000 in decide +kernel
  rw [←h]
  exact List.Nodup.filter _ List.nodup_range

private theorem small_sum (f : ℕ → ℤ) : (Nat.primesLE 8477).sum f = (smallList.map f).sum := by
  have he : Nat.primesLE 8477 = smallList.toFinset := by
    ext p
    simp only [Nat.mem_primesLE, List.mem_toFinset,smallList_iff]
    tauto
  rw [he]
  exact List.sum_toFinset f nd

private theorem bounds {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hq' : q ≤ 8477)
    (hpq : p<q) (hv : 608981813029/(p*q) < p^2) :
    192 ≤ p-1 ∧ 192 ≤ 608981813029/(p*q) ∧ 608981813029/(p*q) ≤ 780372 := by
  have hpos := Nat.mul_pos hp.pos hq.pos
  have hp' : p ≤ 8477 := by omega
  have hp192 : 192 < p := by
    by_contra! hle
    have hm := Nat.mul_le_mul hle hq'
    have hs := Nat.pow_le_pow_left hle 2
    have hl : 36864 ≤ 608981813029/(p*q) := (Nat.le_div_iff_mul_le hpos).mpr
      ((Nat.mul_le_mul_left 36864 hm).trans (by decide))
    norm_num at hs
    omega
  refine ⟨by omega, (Nat.le_div_iff_mul_le hpos).mpr
    ((Nat.mul_le_mul_left 192 (Nat.mul_le_mul hp' hq')).trans (by decide)), ?_⟩
  by_cases hle : p ≤ 883
  · have hs := Nat.pow_le_pow_left hle 2
    norm_num at hs
    omega
  · have hm := Nat.mul_le_mul (show 884 ≤ p by omega) (show 885 ≤ q by omega)
    have hlt : 608981813029/(p*q)<780373 := (Nat.div_lt_iff_lt_mul hpos).mpr
      ((by decide : 608981813029 < 780373*(884*885)).trans_le (Nat.mul_le_mul_left _ hm))
    omega

theorem easyPairs_numeric : easyPairs 608981813029 8477 = remaining 0 := by
  unfold easyPairs
  rw [small_sum]
  change _ = ((smallList.drop 0).map numericRow).sum
  rw [List.drop_zero]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  have hpp := smallList_iff.mp hp
  rw [small_sum]
  unfold numericRow
  apply congrArg List.sum
  apply List.map_congr_left
  intro q hq
  have hqq := smallList_iff.mp hq
  by_cases h : p<q ∧ 608981813029/(p*q)<p^2
  · rw [if_pos h,if_pos h]
    obtain ⟨h1,h2,h3⟩ := bounds hpp.1 hqq.1 hqq.2 h.1 h.2
    rw [weightAt_eq h1 (by have := hpp.2; omega),weightAt_eq h2 h3]
    ring
  · rw [if_neg h,if_neg h]

end SunPrimeRaceEasy

namespace SunPrimeRaceEasy

end SunPrimeRaceEasy
end

section
namespace SunPrimeRaceEasy.Walk

open SunPrimePermutation

def ones : List ℕ := smallList.reverse.filter (fun q => q%3 = 1)
def twos : List ℕ := smallList.reverse.filter (fun q => q%3 = 2)

def visit (f : ℕ → ℤ) (lo : ℕ) (acc : ℤ) : List ℕ → ℤ
  | [] => acc
  | q::qs => if lo < q then visit f lo (acc + f q) qs else acc

def row (p : ℕ) : ℤ :=
  let y := 608981813029/p
  let lo := max p (y/p^2)
  if 8477 ≤ lo then 0 else
    let b := 1 - weightAt (p-1)
    let f := fun q => b + weightAt (y/q)
    chi3 p * (visit f lo 0 ones - visit f lo 0 twos)

def block (i n : ℕ) : ℤ := (((smallList.drop i).take n).map row).sum

def remaining (i : ℕ) : ℤ := ((smallList.drop i).map row).sum

theorem split_remaining (i n : ℕ) : remaining i = block i n + remaining (i+n) := by
  have h := congrArg (fun l : List ℕ => (l.map row).sum)
    (List.take_append_drop n (smallList.drop i))
  simpa only [block, remaining, List.map_append, List.sum_append, List.drop_drop] using h.symm

end SunPrimeRaceEasy.Walk
end

section
namespace SunPrimeRaceEasy.Walk

open SunPrimePermutation

private def gated (f : ℕ → ℤ) (lo : ℕ) (qs : List ℕ) : ℤ :=
  (qs.map (fun q => if lo < q then f q else 0)).sum

private theorem gate_zero (f : ℕ → ℤ) (lo : ℕ) (qs : List ℕ)
    (h : ∀ q ∈ qs, q ≤ lo) : gated f lo qs = 0 := by
  induction qs with
  | nil => rfl
  | cons q qs ih =>
    have hq := h q (by simp)
    have ht := ih (fun t ht => h t (by simp [ht]))
    simpa [gated, Nat.not_lt.mpr hq] using ht

private theorem visit_sound (f : ℕ → ℤ) (lo : ℕ) (qs : List ℕ)
    (hs : qs.Pairwise (· > ·)) (acc : ℤ) : visit f lo acc qs = acc + gated f lo qs := by
  induction qs generalizing acc with
  | nil => simp [visit,gated]
  | cons q qs ih =>
    obtain ⟨hq,ht⟩ := List.pairwise_cons.mp hs
    by_cases h : lo < q
    · simp [visit, h, ih ht, gated, add_assoc]
    · have hz := gate_zero f lo qs (fun t hm => (hq t hm).le.trans (Nat.not_lt.mp h))
      simpa [visit, gated, h, hz, gated] using congrArg (acc + ·) hz.symm

private theorem ordered_one : ones.Pairwise (· > ·) := by
  apply List.isChain_iff_pairwise.mp
  set_option maxRecDepth 100000 in decide +kernel

private theorem ordered_two : twos.Pairwise (· > ·) := by
  apply List.isChain_iff_pairwise.mp
  set_option maxRecDepth 100000 in decide +kernel

private theorem split_classes (f : ℕ → ℤ) (lo : ℕ) (l : List ℕ) :
    gated f lo (l.filter (fun q => q%3=1)) - gated f lo (l.filter (fun q => q%3=2)) =
      (l.map (fun q => if lo < q then chi3 q * f q else 0)).sum := by
  induction l with
  | nil => rfl
  | cons q qs ih =>
    by_cases h1 : q%3=1 <;> by_cases h2 : q%3=2 <;> by_cases h : lo < q <;>
      simp [gated,chi3,h1,h2,h] at ih ⊢ <;> omega

private theorem distribute (a : ℤ) (f : ℕ → ℤ) (l : List ℕ) :
    a * (l.map f).sum = (l.map (fun q => a * f q)).sum := by
  induction l with
  | nil => simp
  | cons q qs ih => simp [mul_add,ih]

theorem row_eq {p : ℕ} (hpp : p ∈ smallList) : row p = numericRow p := by
  have hp := (smallList_iff.mp hpp).1.pos
  let y := 608981813029/p
  let lo := max p (y/p^2)
  let f := fun q => (1 - weightAt (p-1)) + weightAt (y/q)
  have cutoff (q : ℕ) (hq : 0 < q) :
      lo < q ↔ p < q ∧ 608981813029/(p*q) < p^2 := by
    dsimp only [lo, y]
    rw [max_lt_iff, Nat.div_lt_iff_lt_mul (pow_pos hp 2), ← Nat.div_div_eq_div_mul,
      Nat.div_lt_iff_lt_mul hq, Nat.mul_comm q]
  have collect : row p = (smallList.map (fun q => chi3 p * (if lo < q then chi3 q*f q else 0))).sum := by
    rw [← distribute]
    have h1 := visit_sound f lo ones ordered_one 0
    have h2 := visit_sound f lo twos ordered_two 0
    have hr := split_classes f lo smallList.reverse
    simp only [List.map_reverse, List.sum_reverse] at hr
    change _ = chi3 p * _
    unfold row
    change (if 8477 ≤ lo then 0 else chi3 p * (visit f lo 0 ones - visit f lo 0 twos)) = _
    by_cases h : 8477 ≤ lo
    · have hz := gate_zero (fun q => chi3 q * f q) lo smallList
        (fun q hq => (smallList_iff.mp hq).2.trans h)
      rw [if_pos h]; dsimp [gated] at hz; rw [hz, mul_zero]
    · rw [if_neg h, h1, h2, zero_add, zero_add]
      exact congrArg (chi3 p * ·) hr
  rw [collect]
  unfold numericRow
  apply congrArg List.sum
  apply List.map_congr_left
  intro q hq
  have hcut := cutoff q (smallList_iff.mp hq).1.pos
  by_cases h : lo < q
  · rw [if_pos h, if_pos (hcut.mp h)]
    simp [f, y, Nat.div_div_eq_div_mul, mul_assoc]
  · rw [if_neg h, if_neg (fun hh => h (hcut.mpr hh)), mul_zero]

theorem total : easyPairs 608981813029 8477 = remaining 0 := by
  rw [easyPairs_numeric]
  unfold SunPrimeRaceEasy.remaining remaining
  simp only [List.drop_zero]
  apply congrArg List.sum
  exact List.map_congr_left (fun p hp => (row_eq hp).symm)

end SunPrimeRaceEasy.Walk
end

section
namespace SunPrimeRaceEasy.Walk

private def Scores : ℕ → List ℤ → Prop
  | _, [] => True
  | i, v::vs => block i 8 = v ∧ Scores (i+8) vs

private theorem fold_scores (i : ℕ) (vs : List ℤ) (h : Scores i vs) :
    remaining i = vs.sum + remaining (i + 8*vs.length) := by
  induction vs generalizing i with
  | nil => simp
  | cons v vs ih =>
    obtain ⟨ha,hb⟩ := h
    calc
      remaining i = block i 8 + remaining (i+8) := split_remaining i 8
      _ = v + (vs.sum + remaining ((i+8)+8*vs.length)) := by rw [ha, ih (i+8) hb]
      _ = (v::vs).sum + remaining (i+8*(v::vs).length) := by
        simp only [List.sum_cons,List.length_cons]
        rw [← add_assoc]
        congr 2 <;> omega

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
private theorem g0 : Scores 0 [0,0,0,0,0,0,0,0,0,0,107,-305] := by
  simp only [Scores]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
private theorem g1 : Scores 96 [367,715,-105,494,960,-75,-163,606,72,47,-292,-5] := by
  simp only [Scores]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
private theorem g2 : Scores 192 [178,442,-134,216,288,98,78,-115,1595,-212,2158,142] := by
  simp only [Scores]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
private theorem g3 : Scores 288 [-211,-47,433,108,125,-14,306,48,-312,-13,91,44] := by
  simp only [Scores]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
private theorem g4 : Scores 384 [65,208,66,251,58,157,-86,108,-111,202,-16,59] := by
  simp only [Scores]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
private theorem g5 : Scores 480 [102,25,241,144,233,31,-131,16,-8,104,146,143] := by
  simp only [Scores]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
private theorem g6 : Scores 576 [-65,-13,16,-13,90,51,66,91,49,109,-176,113] := by
  simp only [Scores]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
private theorem g7 : Scores 672 [-53,178,81,-337,-300,198,-37,-68,-7,-18,-21,-4] := by
  simp only [Scores]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
private theorem g8 : Scores 768 [-5,21,55,-40,49,32,-44,17,30,31,-33,43] := by
  simp only [Scores]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
private theorem g9 : Scores 864 [37,7,-12,2,-12,42,25,-28,-5,52,7,-21] := by
  simp only [Scores]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
private theorem g10 : Scores 960 [-20,-3,-6,-221,-126,100,-14,-133,105,-10,44,-3] := by
  simp only [Scores]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
private theorem g11 : Scores 1056 [3] := by
  simp only [Scores]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem subtotal : remaining 0 = 9618 := by
  have hz : smallList.drop 1064 = [] := by decide +kernel
  have h1064 : remaining 1064 = 0 := by simp [remaining,hz]
  have h1056 : remaining 1056 = (3 : ℤ) := by
    rw [fold_scores _ _ g11]
    change (3 : ℤ) + remaining 1064 = _
    rw [h1064] <;> decide
  have h960 : remaining 960 = (-284 : ℤ) := by
    rw [fold_scores _ _ g10]
    change (-287 : ℤ) + remaining 1056 = _
    rw [h1056] <;> decide
  have h864 : remaining 864 = (-190 : ℤ) := by
    rw [fold_scores _ _ g9]
    change (94 : ℤ) + remaining 960 = _
    rw [h960] <;> decide
  have h768 : remaining 768 = (-34 : ℤ) := by
    rw [fold_scores _ _ g8]
    change (156 : ℤ) + remaining 864 = _
    rw [h864] <;> decide
  have h672 : remaining 672 = (-422 : ℤ) := by
    rw [fold_scores _ _ g7]
    change (-388 : ℤ) + remaining 768 = _
    rw [h768] <;> decide
  have h576 : remaining 576 = (-104 : ℤ) := by
    rw [fold_scores _ _ g6]
    change (318 : ℤ) + remaining 672 = _
    rw [h672] <;> decide
  have h480 : remaining 480 = (942 : ℤ) := by
    rw [fold_scores _ _ g5]
    change (1046 : ℤ) + remaining 576 = _
    rw [h576] <;> decide
  have h384 : remaining 384 = (1903 : ℤ) := by
    rw [fold_scores _ _ g4]
    change (961 : ℤ) + remaining 480 = _
    rw [h480] <;> decide
  have h288 : remaining 288 = (2461 : ℤ) := by
    rw [fold_scores _ _ g3]
    change (558 : ℤ) + remaining 384 = _
    rw [h384] <;> decide
  have h192 : remaining 192 = (7195 : ℤ) := by
    rw [fold_scores _ _ g2]
    change (4734 : ℤ) + remaining 288 = _
    rw [h288] <;> decide
  have h96 : remaining 96 = (9816 : ℤ) := by
    rw [fold_scores _ _ g1]
    change (2621 : ℤ) + remaining 192 = _
    rw [h192] <;> decide
  have h0 : remaining 0 = (9618 : ℤ) := by
    rw [fold_scores _ _ g0]
    change (-198 : ℤ) + remaining 96 = _
    rw [h96] <;> decide
  exact h0
end SunPrimeRaceEasy.Walk
end

section
namespace SunPrimeRaceEasy

theorem easyPairs_value : easyPairs 608981813029 8477 = 9618 :=
  Walk.total.trans Walk.subtotal

end SunPrimeRaceEasy
end

section
namespace SunPrimePermutation

theorem easy_exact : easyTotal 608981813029 8477 17 8477 = 9618 :=
  easy_as_double_sum.trans SunPrimeRaceEasy.easyPairs_value

theorem disproof_of_hard_sum (h : hardTotal 608981813029 8477 17 8477 = 7941) :
    ¬ (type_of% @OMA.S_oeis_a321727.main) :=
  disproof_of_leaf_totals ordinary_compact_exact easy_exact h

end SunPrimePermutation
end

section
namespace SunHardRank
open SunPrimePermutation

abbrev originalQueries (p : ℕ) : List (ℕ × ℤ) :=
  (((rowTerms 8477 8477 p).filter (fun dc => decide (p^2 ≤ 608981813029/dc.1))).map
    (fun dc => (608981813029/dc.1,dc.2)))

theorem zero_queries_above {p : ℕ} (hp : p.Prime) (hlo : 881 < p) (hhi : p ≤ 8477) :
    originalQueries p = [] := by
  obtain ⟨a,ha⟩ := hp.odd_of_ne_two (by omega)
  have h883 : 883 ≤ p := by omega
  have hcut : 8477 < p*p := by
    have h := Nat.mul_le_mul h883 h883
    omega
  unfold originalQueries
  rw [all_finished_singles (le_refl 8477) hhi hcut]
  suffices none : (((sieveStages p 8477).map (fun q => (q*p, chi3 q*chi3 p))).filter
        (fun dc => decide (p^2 ≤ 608981813029/dc.1))) = [] by rw [none]; rfl
  apply List.filter_eq_nil_iff.mpr
  intro dc hd
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hd
  obtain ⟨hpq,_,hprime⟩ := mem_stages.mp hq
  obtain ⟨b,hb⟩ := hprime.odd_of_ne_two (by omega)
  have h885 : 885 ≤ q := by omega
  have hprod := Nat.mul_le_mul (Nat.pow_le_pow_left h883 2) (Nat.mul_le_mul h885 h883)
  have hpos : 0 < q*p := Nat.mul_pos (by omega) (by omega)
  have hno : ¬p^2 ≤ 608981813029/(q*p) := by
    intro h
    have ht := (Nat.le_div_iff_mul_le hpos).mp h
    omega
  simp [hno]

end SunHardRank
end

section
namespace SunHardRank
open SunPrimePermutation

/-- At this cutoff any frontier product made out of primes above 93 has at most
one prime factor. The remaining stages reconstruct the exact small frontier. -/
def lowFront (p : ℕ) : List SignedProduct :=
  (fastStages p 93).foldl (advanceTerms 8477) (singles (fastStages 93 8477))

theorem lowFront_eq {p : ℕ} (hp : p ≤ 93) :
    termsBefore 8477 8477 p = lowFront p := by
  have initial := before_high (cut := 8477) (b := 8477) (p := 93) (by decide) (by decide)
  unfold termsBefore at initial ⊢
  rw [stages_append hp (by decide : 93 ≤ 8477), List.foldl_append, initial,
    fastStages_eq (by decide : 8477 ≤ 8500), fastStages_eq (by decide : 93 ≤ 8500)]
  rfl

def lowHardPairs (p : ℕ) : List SignedProduct :=
  (finishedProducts chi3 8477 p (lowFront p)).filter
    (fun dc => decide (p^2 ≤ 608981813029/dc.1))

/-- Stable radix passes use structural recursion, including during kernel reduction. -/
def radixPairs : ℕ → List SignedProduct → List SignedProduct
  | 0, xs => xs
  | t+1, xs =>
    let src := radixPairs t xs
    let bit := fun dc : SignedProduct => dc.1.testBit t
    src.filter bit ++ src.filter (fun dc => !bit dc)

theorem radixPairs_perm (t : ℕ) (xs : List SignedProduct) : (radixPairs t xs).Perm xs := by
  induction t with
  | zero => rfl
  | succ t ih => exact (List.filter_append_perm _ _).trans ih

/-- Adjacent equal quotients retain the ordering of their underlying products. -/
def orderedLow (p : ℕ) : List (ℕ × ℤ) :=
  (radixPairs 20 (lowHardPairs p)).map
    (fun dc => (608981813029/dc.1, dc.2))

theorem originalQueries_perm_orderedLow {p : ℕ} (hp : p ≤ 93) :
    (originalQueries p).Perm (orderedLow p) := by
  unfold originalQueries rowTerms
  rw [lowFront_eq hp]
  exact (radixPairs_perm 20 (lowHardPairs p)).symm.map _

theorem low_cases {p : ℕ} (hp : p.Prime) (ha : 17 < p) (hb : p ≤ 93) :
    p ∈ [19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89] := by
  have test : ∀ n : Fin 94, n.val.Prime → 17 < n.val →
      n.val ∈ [19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89] := by decide +kernel
  exact test ⟨p, by omega⟩ hp ha

end SunHardRank
end

section
namespace SunHardRank
open Finset SunPrimePermutation SunPrimeNumeric

def rankBits (t pos neg k : ℕ) : ℤ :=
  (wordCount t (pos%2^k) : ℤ) - wordCount t (neg%2^k)

private theorem count_residue (t start mask k shift : ℕ) (hk : k ≤ 16*2^t) (ht : 2^t < 65535) :
    (wordCount t ((mask &&& divMask (start+shift) 3 (16*2^t))%2^k) : ℤ) =
      ∑ j ∈ range k, if mask.testBit j = true ∧ 3 ∣ start+shift+j then 1 else 0 := by
  rw [wordCount_eq _ _ ht,Finset.sum_boole]
  congr 2
  ext i
  simp only [mem_filter,mem_range,Nat.testBit_mod_two_pow,Nat.testBit_and,
    Bool.and_eq_true,decide_eq_true_eq]
  constructor
  · rintro ⟨hw,hi,hx,hd⟩
    exact ⟨hi,hx,(divMask_bit _ _ _ i (by decide) hw).mp hd⟩
  · rintro ⟨hi,hx,hd⟩
    have hw := hi.trans_le hk
    exact ⟨hw,hi,hx,(divMask_bit _ _ _ i (by decide) hw).mpr hd⟩

theorem rankBits_sum (t start mask k : ℕ) (hk : k ≤ 16*2^t) (ht : 2^t < 65535) :
    rankBits t (mask &&& divMask (start+2) 3 (16*2^t)) (mask &&& divMask (start+1) 3 (16*2^t)) k =
      packedWeight chi3 start k mask := by
  rw [rankBits,count_residue _ _ _ _ _ hk ht,count_residue _ _ _ _ _ hk ht,←sum_sub_distrib]
  apply sum_congr rfl
  intro j _
  unfold chi3
  by_cases h : mask.testBit j
  · simp only [h, true_and, if_true]
    split_ifs <;> omega
  · simp [h]

theorem rankBits_rough (t s k : ℕ) (ds : List ℕ) (hd : ∀ q ∈ ds, q.Prime)
    (hk : k ≤ 16*2^t) (ht : 2^t < 65535) :
    let m := roughMask (s+1) (16*2^t) ds
    rankBits t (m &&& divMask (s+1+2) 3 (16*2^t)) (m &&& divMask (s+1+1) 3 (16*2^t)) k =
      roughSum chi3 ds.prod (s+k) - roughSum chi3 ds.prod s := by
  dsimp only
  rw [rankBits_sum _ _ _ _ hk ht, ←mask_rough_sum chi3 ds hd s k]
  unfold packedWeight
  apply sum_congr rfl
  intro j hj
  have h := mem_range.mp hj
  have hp := fun q hq => (hd q hq).pos
  have e := (roughMask_bit (s+1) _ j (h.trans_le hk) ds hp).trans
    (roughMask_bit (s+1) k j h ds hp).symm
  by_cases hbit : (roughMask (s+1) k ds).testBit j
  · rw [if_pos hbit,if_pos (e.mpr hbit)]
  · rw [if_neg hbit,if_neg (mt e.mp hbit)]

def cell (t s : ℕ) (ds : List ℕ) (base : ℤ) (qs : List (ℕ × ℤ)) : ℤ × ℤ :=
  let w := 16*2^t
  let m := roughMask (s+1) w ds
  let pos := m &&& divMask (s+1+2) 3 w
  let neg := m &&& divMask (s+1+1) 3 w
  let val := fun k => base + rankBits t pos neg k
  (val w,(qs.map (fun z => z.2*val z.1)).sum)

theorem cell_eq (t s cut : ℕ) (ds : List ℕ) (base : ℤ) (qs : List (ℕ × ℤ))
    (hd : ∀ q ∈ ds, q.Prime) (hprod : ds.prod = primorial cut)
    (hbase : signedPhi cut s = base) (ht : 2^t < 65535)
    (hq : ∀ z ∈ qs, z.1 ≤ 16*2^t) :
    cell t s ds base qs = (signedPhi cut (s+16*2^t),
      (qs.map (fun z => z.2*signedPhi cut (s+z.1))).sum) := by
  have he (k : ℕ) (hk : k ≤ 16*2^t) :
      let w := 16*2^t
      let m := roughMask (s+1) w ds
      base + rankBits t (m &&& divMask (s+1+2) 3 w) (m &&& divMask (s+1+1) 3 w) k =
        signedPhi cut (s+k) := by
    dsimp only
    rw [rankBits_rough _ _ _ _ hd hk ht,hprod,←hbase]
    unfold signedPhi
    rw [phiEval_eq _ _ chi3_mul chi3_prefix,phiEval_eq _ _ chi3_mul chi3_prefix]
    omega
  unfold cell
  dsimp only
  congr 1
  · exact he _ (le_refl _)
  · apply congrArg List.sum
    apply List.map_congr_left
    intro r hr
    rw [he _ (hq r hr)]

end SunHardRank
end

section
namespace SunHardRank
open SunPrimePermutation SunPrimeNumeric

def evalPairs (cut : ℕ) (xs : List (ℕ × ℤ)) : ℤ :=
  (xs.map (fun z => z.2 * signedPhi cut z.1)).sum

def Span (cut lo hi : ℕ) (base stop : ℤ) (xs : List (ℕ × ℤ)) (total : ℤ) : Prop :=
  signedPhi cut lo = base → signedPhi cut hi = stop ∧ evalPairs cut xs = total

theorem segment {cut t s : ℕ} {ds : List ℕ} {base stop total : ℤ} {xs : List (ℕ × ℤ)}
    (hd : ∀ q ∈ ds, q.Prime) (hprod : ds.prod = primorial cut) (ht : 2^t < 65535)
    (hxs : ∀ z ∈ xs, s < z.1 ∧ z.1 ≤ s+16*2^t)
    (hnum : cell t s ds base (xs.map (fun z => (z.1-s,z.2))) = (stop,total)) :
    Span cut s (s+16*2^t) base stop xs total := by
  intro hbase
  have hoff : ∀ z ∈ xs.map (fun z => (z.1-s,z.2)), z.1 ≤ 16*2^t := by
    intro z hz
    obtain ⟨y,hy,rfl⟩:=List.mem_map.mp hz
    have h :=hxs y hy
    dsimp only
    omega
  have he := cell_eq t s cut ds base _ hd hprod hbase ht hoff
  rw [hnum] at he
  have he' : ((xs.map (fun z => (z.1-s,z.2))).map
      (fun z => z.2 * signedPhi cut (s+z.1))).sum = evalPairs cut xs := by
    unfold evalPairs
    rw [List.map_map]
    apply congrArg List.sum
    apply List.map_congr_left
    intro z hz
    dsimp only [Function.comp_apply]
    rw [Nat.add_sub_of_le (hxs z hz).1.le]
  rw [he'] at he
  exact ⟨(congrArg Prod.fst he).symm,(congrArg Prod.snd he).symm⟩

theorem span_join {cut s m e : ℕ} {a b c h k : ℤ} {xs ys : List (ℕ × ℤ)}
    (left : Span cut s m a b xs h) (right : Span cut m e b c ys k) :
    Span cut s e a c (xs++ys) (h+k) := by
  intro ha
  obtain ⟨hb,hx⟩ := left ha
  obtain ⟨hc,hy⟩ := right hb
  exact ⟨hc,by unfold evalPairs at *; simp [hx,hy]⟩

theorem phi_zero (cut : ℕ) : signedPhi cut 0 = 0 := by
  unfold signedPhi
  rw [phiEval_eq _ _ chi3_mul chi3_prefix]
  simp [roughSum,roughNumbers]

theorem eval_of_span {cut stop : ℕ} {last value : ℤ} {xs : List (ℕ × ℤ)}
    (h : Span cut 0 stop 0 last xs value) : evalPairs cut xs = value :=
  (h (phi_zero _)).2

theorem hardRow_of_perm {x cut b p : ℕ} {xs : List (ℕ × ℤ)} {total : ℤ}
    (he : ((rowTerms cut b p).filter (fun dc => decide (p^2 ≤ x/dc.1)) |>.map
      (fun dc => (x/dc.1,dc.2))).Perm xs)
    (hf : evalPairs (p-1) xs = total) : hardRow x cut b p = total := by
  rw [← hf]
  unfold hardRow weighFront evalPairs
  have hz := (he.map (fun z => z.2*signedPhi (p-1) z.1)).sum_eq
  simpa [List.map_map,Function.comp_def] using hz

end SunHardRank
end

section
namespace SunHardRank
open Finset

def smallPrime (n : ℕ) : Bool :=
  if n ≤ 30 then decide n.Prime else n.gcd (Nat.factorial 30) == 1

theorem smallPrime_iff (n : ℕ) (h : n ≤ 900) : smallPrime n = true ↔ n.Prime := by
  unfold smallPrime
  split
  · simp
  · rename_i hn
    rw [beq_iff_eq]
    constructor
    · intro hg
      by_contra hc
      have pr := Nat.minFac_prime (by omega : n ≠ 1)
      have hs := Nat.minFac_sq_le_self (by omega : 0 < n) hc
      have h30 : n.minFac ≤ 30 := by
        by_contra! he
        have z := Nat.pow_le_pow_left (show 31 ≤ n.minFac by omega) 2
        norm_num at z
        omega
      have hd := Nat.dvd_gcd (Nat.minFac_dvd n) (Nat.dvd_factorial pr.pos h30)
      rw [hg] at hd
      exact pr.not_dvd_one hd
    · intro hp
      exact (hp.coprime_factorial_of_lt (by omega : 30 < n)).gcd_eq_one

def trialList (cut : ℕ) := (List.range (cut+1)).filter smallPrime

theorem trial_spec (cut : ℕ) (hc : cut ≤ 900) :
    (∀ q ∈ trialList cut, q.Prime) ∧ (trialList cut).prod = primorial cut := by
  have mem (q : ℕ) : q ∈ trialList cut ↔ q ∈ Nat.primesLE cut := by
    simp only [trialList,List.mem_filter,List.mem_range,Nat.mem_primesLE]
    constructor
    · rintro ⟨hl,hp⟩
      exact ⟨by omega,(smallPrime_iff q (by omega)).mp hp⟩
    · rintro ⟨hl,hp⟩
      exact ⟨by omega,(smallPrime_iff q (by omega)).mpr hp⟩
  constructor
  · intro q hq
    exact (Nat.mem_primesLE.mp ((mem q).mp hq)).2
  · have he : (trialList cut).toFinset = Nat.primesLE cut := by ext q; simpa using mem q
    have hnod : (trialList cut).Nodup := List.Nodup.filter _ List.nodup_range
    have hx := List.prod_toFinset id hnod
    rw [he] at hx
    rw [primorial_eq_prod_primesLE]
    simpa using hx.symm

end SunHardRank
end

section
namespace SunHardCompact
open SunPrimePermutation SunHardRank SunPrimeRaceEasy

def descending (lo hi : ℕ) : List ℕ := (List.range' (lo+1) (hi-lo)).reverse

theorem mem_descending {lo hi d : ℕ} :
    d ∈ descending lo hi ↔ lo < d ∧ d ≤ hi := by
  simp only [descending,List.mem_reverse,List.mem_range',Nat.one_mul]
  constructor
  · rintro ⟨i,hi,rfl⟩
    omega
  · rintro ⟨h1,h2⟩
    exact ⟨d-(lo+1),by omega,by omega⟩

theorem descending_join {a b c : ℕ} (ha : a ≤ b) (hb : b ≤ c) :
    descending b c ++ descending a b = descending a c := by
  unfold descending
  rw [←List.reverse_append]
  congr 1
  simpa only [show a+1+(b-a)=b+1 by omega,show b-a+(c-b)=c-a by omega] using
    (List.range'_append_1 (s := a+1) (m := b-a) (n := c-b))

def boundary (lo hi t s : ℕ) := max lo (min hi (t/(s+1)))

theorem boundary_anti {lo hi t s e : ℕ} (h : s ≤ e) :
    boundary lo hi t e ≤ boundary lo hi t s :=
  max_le_max_left _ (min_le_min_left _ (Nat.div_le_div_left (Nat.succ_le_succ h) (Nat.succ_pos _)))

private theorem reciprocal {t d s : ℕ} (hd : 0 < d) :
    t/(s+1) < d ↔ t/d ≤ s := by
  rw [Nat.div_lt_iff_lt_mul (Nat.succ_pos _), ←Nat.lt_succ_iff,Nat.div_lt_iff_lt_mul hd]
  rw [Nat.mul_comm]

theorem cell_iff {lo hi t s e d : ℕ} (hd : 0 < d) :
    d ∈ descending (boundary lo hi t e) (boundary lo hi t s) ↔
    lo < d ∧ d ≤ hi ∧ s < t/d ∧ t/d ≤ e := by
  have hs := reciprocal (t:=t) (s:=s) hd
  have he := reciprocal (t:=t) (s:=e) hd
  rw [mem_descending]
  unfold boundary
  omega

def queryList (code : ℕ → Option (ℕ × ℤ)) (lo hi : ℕ) :=
  (descending lo hi).filterMap code

theorem queryList_join (code : ℕ → Option (ℕ × ℤ)) {a b c : ℕ} (ha : a ≤ b) (hb : b ≤ c) :
    queryList code b c ++ queryList code a b = queryList code a c := by
  simp only [queryList, ← List.filterMap_append, descending_join ha hb]

end SunHardCompact
end

section
namespace SunHardCompact
open SunPrimeRaceEasy SunPrimePermutation

private def semiBank : ℕ := 0x25560000000027800000b800000000000002f000001f4a00000014c00000000000001e8000000003e000000001a80000000000ac00000000000000000000001700964800000000000000000015803a01d800000000000000000000005200f9d000004f00bc000005c0000000000000000000ec02900000000000000a6000000000e802f1c00000000006a000007a000179e000003e00049000000000000000000000000148000000350000000000000000000003a0002f000000000a40000000000929401d000000000acf80000000000000002ef40008e0003b00000000000000000158000000000000000013d7800000000000000000740000000b800000047000000000000008600000000000000000000000000012400000000000001d800000000007c000000001d0000000560000000014800000f800000000014c0005e024806a94000000000000a400000000000002380010c000005d280007400000000350000000000000000000003e0000000000002e000000001580011e18000000170000025000000000000000000000007d7a9000004900000004a00b8000000000000f809e00000000002b00bc0000000e8000000000000000000000000d40000074000000001f00000430001e808e000000000000000000000a4000000000000000000000000000000000000000000000860001d00ac000005c0006a00000000000000000250000000520000000ec000000003d0000e8000000004a0000000000000000000007400000000000002780000001f00017807a000000000b80010e4ab000000000000003a5c000000000000bd480760000000000005601280000000000000002e00000000000000000000000000011c03b0000000000000000f40000000000000000000000000000b80000000000000000000000525c0004a0001f0001eaf0000000000000000000003a000293e0000000000000001d800000000920001700000000094000000000000000000000035007c02b000178086ec000000000000000000000fbd005c00000000475600000000000000000000000000000000000000000000025000000000000000001a973b24000000000000000000000000760001d00000005200000000000000d40000000000000000000015800000029007e3800000e800094000000000000021800000f802e7400000000000001280000001700000000000000000002b6a0000000000000001e80000000000000000000000000000000a40003e5c03500000000000000000000000bc0000000043000000000000002e0000000ece80000000000000170000000520000000740008e00f80000000000000000095a800000b805e0000000000000000000000000000012807a0001f0000000000002f000001d000000000000000000000000000000000000000000000000000000000000000000003b010c0000000000007c0005600b804a75780000000000f40000000000000000000000000000000000218000bc00000000003a000350000000009400000ac01f00000000001d800000000000002900000003e00000000158000000000000b8000000005e00e800000000005c00000000000000000000000000000000001480000003d00000002e0002b0000000000000000d401700a40003a000000000000000000056000007a0001d000001f760000000000000000000000000000000003e00000000000052000000000000000003b6abd28000ac0002e000000000029000000000000170000000000000000f400000000000000f80000000000000253a00000000000000000000000000005d49d00000004a01d80000001f00000000000000000002f000000000000000001a800000000000001700000005600000009400000740000000000000000000d40000000b80000128000000000001780000000000000003a00000000000000000290000000000000000000002e0000076000250000000000158000000006a000000000000000000000000003e0000000000000000b800000000000000000000005e5c000000000000a402b0000000007c00000000000000000000002f00000000000f8000000000001280000001d0000000000000000000005201a80000000000000000000b9f000000000000000000e80005d78000ac0003ed400000000000074000000000000000004a000000001580000000000000000000017007c00000014803a00000000000000000000000000000001d0094b8000a40000000000000002b00000005e000000000000000000000000000000e8000000000000000000002f00000003e0000052000000000000000000000000250000000000000000000000000000000000000000004aac0000000000005c000000001d0000f80000000000000000001580000000000000002e0148000bc00000940000000017000001f0000000000000000a40000074000000000000000000000b80000000000000000000000005c000000000000000003a000005600000007c025000000000000002e0000000000000000f8000000004a0002900000000000000000000000000000000e8000000000000000000001f00000000074000005c000000000000015800000000000000000000000000000000128000000003a0000000a400000000170000000007c00000000000000000000000000000000000f800000b800000000000000000000000000e80520000000000004a0000000000000074000000000000000002e00000000000000000003e0001700000000000000000000000940000000000000000000000000000b9d0000000000128000000000000000000000000000000000f8000000000000000000000000000002e000000000000000000000740170000000000001f000000000000000000000000000000000003e0000000000003a000000000000005c0000000000000001d000000000000000000000007c000000000000000000000000000000000000170000e800000000000000000000000000000000000000000000000b80000000000000000000000005c0000000000000000000000003a000000000000000000000000002e0000000000000000000000000000000000000000000000000000000000000000000000000000000b80000000000000000000000005c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

-- Entries at 6k+1 and 6k+5 use successive seven-bit fields.
def semiLeast (d : ℕ) : ℕ :=
  if d%6 = 1 ∨ d%6 = 5 then (semiBank >>> (7*(d/3))) % 128 else 0

def bottom (p : ℕ) : ℕ := max p (8477/p)
def top (p : ℕ) : ℕ := min 8477 ((608981813029/p)/(p*p))
def mark (p s : ℕ) := boundary (bottom p) (top p) (608981813029/p) s

def queryAt (p d : ℕ) : Option (ℕ × ℤ) :=
  let n := (608981813029/p)/d
  let c := chi3 p * chi3 d
  if lowBits.testBit d then some (n,c)
  else if p < semiLeast d then some (n,-c) else none

def rowInterval (p s e : ℕ) := queryList (queryAt p) (mark p e) (mark p s)
def cellRows (p s : ℕ) := rowInterval p s (s+262144)

theorem queryAt_value {p d : ℕ} {z : ℕ × ℤ} (h : queryAt p d = some z) :
    z.1 = (608981813029/p)/d := by
  unfold queryAt at h
  split at h
  · cases h
    rfl
  · split at h
    · cases h
      rfl
    · contradiction

theorem cellRows_bounds {p s : ℕ} {z : ℕ × ℤ} (hz : z ∈ cellRows p s) :
    s < z.1 ∧ z.1 ≤ s+262144 := by
  obtain ⟨d,hd,he⟩ := List.mem_filterMap.mp hz
  have hd0 : 0 < d := Nat.zero_le _ |>.trans_lt (mem_descending.mp hd).1
  have h := (cell_iff hd0).mp hd
  rw [queryAt_value he]
  exact ⟨h.2.2.1,h.2.2.2⟩

theorem rowInterval_join {p s m e : ℕ} (hsm : s ≤ m) (hme : m ≤ e) :
    rowInterval p s m ++ rowInterval p m e = rowInterval p s e :=
  queryList_join _ (boundary_anti hme) (boundary_anti hsm)

end SunHardCompact
end

section
namespace SunHardCompact
open SunHardRank SunPrimePermutation

def computedFront (p : ℕ) : List (ℕ × ℤ) :=
  if p ≤ 93 then orderedLow p else
    let terms := (fastStages p 8477).map (fun q => (q*p,chi3 q*chi3 p))
    (terms.filter (fun dc => decide (p^2 ≤ 608981813029/dc.1))).map
      (fun dc => (608981813029/dc.1,dc.2))

theorem front_perm {p : ℕ} (hp : p ≤ 881) : (originalQueries p).Perm (computedFront p) := by
  unfold computedFront
  split_ifs with lo
  · exact originalQueries_perm_orderedLow lo
  · have h := Nat.mul_le_mul (show 94 ≤ p by omega) (show 94 ≤ p by omega)
    unfold originalQueries
    rw [all_finished_singles (le_refl 8477) (by omega) (by omega),
      fastStages_eq (by decide : 8477 ≤ 8500)]

def matchesFront (p : ℕ) : Bool :=
  !smallPrime p || decide (computedFront p = rowInterval p 0 608981813029)

def matchBand (start len : ℕ) := (List.range' start len).all matchesFront

theorem matchBand_join {a n m : ℕ} (h : matchBand a n = true)
    (j : matchBand (a+n) m = true) : matchBand a (n+m) = true := by
  unfold matchBand at *
  rw [← List.range'_append_1, List.all_append, h, j]
  rfl

theorem canonical_of_band (h : matchBand 18 864 = true) {p : ℕ}
    (hm : p ∈ Finset.Ioc 17 881) (hp : p.Prime) :
    (originalQueries p).Perm (rowInterval p 0 608981813029) := by
  obtain ⟨lo, hi⟩ := Finset.mem_Ioc.mp hm
  apply (front_perm hi).trans
  have range : p ∈ List.range' 18 864 := by
    apply List.mem_range'_1.mpr
    omega
  have ok := List.all_eq_true.mp h p range
  have prime := (smallPrime_iff p (by omega)).mpr hp
  have same : computedFront p = rowInterval p 0 608981813029 := by
    simpa [matchesFront, prime] using ok
  rw [same]

end SunHardCompact
end

section
namespace SunHardCompact
open SunHardRank SunPrimePermutation SunPrimeRaceEasy

private abbrev X := 608981813029

private theorem lowBit_prime {q : ℕ} (hq : q ≤ 8477) : lowBits.testBit q = true ↔ q.Prime := by
  have h := allBits_correct (p := q) (by omega : q ≤ 780372)
  simpa only [allBits, Nat.testBit_or, Nat.testBit_shiftLeft, show ¬8478 ≤ q by omega,
    decide_false, Bool.false_and, Bool.or_false] using h

set_option maxRecDepth 20000 in
private theorem semiBound : (List.range 8478).all (fun d => decide (semiLeast d ≤ 89)) = true := by
  decide +kernel

private theorem bottom_high {p : ℕ} (hp : 93 < p) : bottom p = p := by
  apply max_eq_left
  apply Nat.le_of_lt
  apply (Nat.div_lt_iff_lt_mul (by omega : 0 < p)).mpr
  have h := Nat.mul_le_mul (show 94 ≤ p by omega) (show 94 ≤ p by omega)
  omega

private def cofPair (p q : ℕ) : ℕ × ℤ := ((X/p)/q, chi3 p*chi3 q)

private theorem project_cofs {p : ℕ} (hp : 93 < p) (ds : List ℕ) (hc : ∀ d ∈ ds, d ≤ 8477) :
    ds.filterMap (queryAt p) = (ds.filter lowBits.testBit).map (cofPair p) := by
  induction ds with
  | nil => rfl
  | cons d rest ih =>
    have bound : semiLeast d ≤ 89 := of_decide_eq_true (List.all_eq_true.mp semiBound d
      (List.mem_range.mpr (by have := hc d (.head _); omega)))
    have tail := ih (fun u h => hc u (.tail _ h))
    cases h : lowBits.testBit d <;>
      simp only [List.filterMap_cons, List.filter_cons, queryAt, cofPair, h, tail,
        show ¬p < semiLeast d by omega] <;> simp [cofPair]

private theorem den_mem {p q : ℕ} (hp : 93 < p) (hq : 0 < q) :
    q ∈ descending (mark p X) (mark p 0) ↔ p < q ∧ q ≤ 8477 ∧ p^2 ≤ X/(q*p) := by
  have pp : 0 < p := by omega
  have pos := Nat.mul_pos pp pp
  have z : X/(q*p) = (X/p)/q := by rw [Nat.div_div_eq_div_mul, Nat.mul_comm q p]
  have flip : p^2 ≤ X/(q*p) ↔ q ≤ (X/p)/(p*p) := by
    rw [z, Nat.le_div_iff_mul_le hq, Nat.le_div_iff_mul_le pos, pow_two, Nat.mul_comm q (p*p)]
  have upper : (X/p)/q ≤ X := (Nat.div_le_self ..).trans (Nat.div_le_self ..)
  unfold mark
  rw [cell_iff hq, bottom_high hp]
  simp only [top, le_min_iff]
  constructor
  · exact fun h => ⟨h.1,h.2.1.1,flip.mpr h.2.1.2⟩
  · rintro ⟨hl,hu,hv⟩
    exact ⟨hl,⟨hu,flip.mp hv⟩,lt_of_lt_of_le (Nat.pow_pos pp) (z ▸ hv),upper⟩

theorem high_cofactor_eq {p : ℕ} (hp : 93 < p) (hmax : p ≤ 8477) :
    originalQueries p = rowInterval p 0 X := by
  let ds := descending (mark p X) (mark p 0)
  have dspos {q : ℕ} (h : q ∈ ds) : 0 < q := (Nat.zero_le _).trans_lt (mem_descending.mp h).1
  have rightbound (q : ℕ) (h : q ∈ ds) : q ≤ 8477 := ((den_mem hp (dspos h)).mp h).2.1
  have equal :
      (sieveStages p 8477).filter (fun q => decide (p^2 ≤ X/(q*p))) =
        ds.filter lowBits.testBit := by
    apply List.Pairwise.eq_of_mem_iff ((stages_desc p 8477).filter _)
    · apply List.Pairwise.filter
      exact List.pairwise_reverse.mpr (List.pairwise_lt_range' (step := 1) (by decide))
    · intro q
      simp only [List.mem_filter, mem_stages, decide_eq_true_eq]
      constructor
      · rintro ⟨⟨hl,hu,hq⟩,hv⟩
        exact ⟨(den_mem hp hq.pos).mpr ⟨hl,hu,hv⟩,(lowBit_prime hu).mpr hq⟩
      · rintro ⟨hd,hb⟩
        obtain ⟨hl,hu,hv⟩ := (den_mem hp (dspos hd)).mp hd
        exact ⟨⟨hl,hu,(lowBit_prime hu).mp hb⟩,hv⟩
  have prod : 8477 < p*p := by
    have := Nat.mul_le_mul (show 94 ≤ p by omega) (show 94 ≤ p by omega)
    omega
  unfold originalQueries
  rw [all_finished_singles (le_refl _) hmax prod, List.filter_map, List.map_map]
  change ((sieveStages p 8477).filter (fun q => decide (p^2 ≤ X/(q*p)))).map
    (fun q => (X/(q*p), chi3 q*chi3 p)) = ds.filterMap (queryAt p)
  rw [equal, project_cofs hp ds rightbound]
  apply List.map_congr_left
  intro q _
  simp only [cofPair, Nat.div_div_eq_div_mul, Nat.mul_comm p q, mul_comm (chi3 p) (chi3 q)]

end SunHardCompact
end

section
namespace SunHardCompact
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem match_18 : matchBand 18 4 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem match_22 : matchBand 22 4 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem match_26 : matchBand 26 4 = true := by decide +kernel
end SunHardCompact
end

section
namespace SunHardCompact
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem match_30 : matchBand 30 4 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem match_34 : matchBand 34 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem match_39 : matchBand 39 3 = true := by decide +kernel
end SunHardCompact
end

section
namespace SunHardCompact
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem match_42 : matchBand 42 4 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem match_46 : matchBand 46 6 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem match_52 : matchBand 52 6 = true := by decide +kernel
end SunHardCompact
end

section
namespace SunHardCompact
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem match_58 : matchBand 58 2 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem match_60 : matchBand 60 6 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem match_66 : matchBand 66 4 = true := by decide +kernel
end SunHardCompact
end

section
namespace SunHardCompact
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem match_70 : matchBand 70 2 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem match_72 : matchBand 72 6 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem match_78 : matchBand 78 4 = true := by decide +kernel
end SunHardCompact
end

section
namespace SunHardCompact
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem match_82 : matchBand 82 5 = true := by decide +kernel
end SunHardCompact
end

section
namespace SunHardCompact
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem match_87 : matchBand 87 7 = true := by decide +kernel
end SunHardCompact
end

section
namespace SunHardCompact
open SunHardRank
private theorem low_matches : matchBand 18 76 = true :=
  (matchBand_join (a := 18) (n := 34) (m := 42) (matchBand_join (a := 18) (n := 16) (m := 18) (matchBand_join (a := 18) (n := 8) (m := 8) (matchBand_join (a := 18) (n := 4) (m := 4) match_18 match_22) (matchBand_join (a := 26) (n := 4) (m := 4) match_26 match_30)) (matchBand_join (a := 34) (n := 8) (m := 10) (matchBand_join (a := 34) (n := 5) (m := 3) match_34 match_39) (matchBand_join (a := 42) (n := 4) (m := 6) match_42 match_46))) (matchBand_join (a := 52) (n := 18) (m := 24) (matchBand_join (a := 52) (n := 8) (m := 10) (matchBand_join (a := 52) (n := 6) (m := 2) match_52 match_58) (matchBand_join (a := 60) (n := 6) (m := 4) match_60 match_66)) (matchBand_join (a := 70) (n := 8) (m := 16) (matchBand_join (a := 70) (n := 2) (m := 6) match_70 match_72) (matchBand_join (a := 78) (n := 4) (m := 12) match_78 (matchBand_join (a := 82) (n := 5) (m := 7) match_82 match_87)))))

theorem all_compact_permutations (p : ℕ) (hm : p ∈ Finset.Ioc 17 881) (hp : p.Prime) :
    (originalQueries p).Perm (rowInterval p 0 608981813029) := by
  obtain ⟨lo, hi⟩ := Finset.mem_Ioc.mp hm
  by_cases low : p ≤ 93
  · apply (front_perm hi).trans
    have member : p ∈ List.range' 18 76 := List.mem_range'_1.mpr (by omega)
    have ok := List.all_eq_true.mp low_matches p member
    have isPrime := (smallPrime_iff p (by omega)).mpr hp
    have same : computedFront p = rowInterval p 0 608981813029 := by
      simpa [matchesFront, isPrime] using ok
    rw [same]
  · rw [high_cofactor_eq (by omega) (by omega)]

end SunHardCompact
end

section
namespace SunHardRank

def traceDelta (u : ℕ) : ℤ := (u % 256 : ℕ) - (128 : ℤ)
def traceWeight (u : ℕ) : ℤ := ((u / 256) % 1024 : ℕ) - (480 : ℤ)

def traceTotals : ℕ → ℕ → ℤ × ℤ
  | 0, _ => (0,0)
  | len+1, packed =>
    let more := traceTotals len (packed/262144)
    (traceDelta packed+more.1,traceWeight packed+more.2)

def traceQueries (rows : ℕ → List (ℕ × ℤ)) (w : ℕ) : ℕ → ℕ → List (ℕ × ℤ)
  | _, 0 => []
  | start, len+1 => rows start ++ traceQueries rows w (start+w) len

def traceOK (rows : ℕ → List (ℕ × ℤ)) (t : ℕ) (ds : List ℕ) :
    ℕ → ℤ → ℕ → ℕ → Bool
  | _, _, 0, _ => true
  | s, base, len+1, packed =>
    let qs := rows s
    let w := 16*2^t
    (qs.all (fun z => decide (s < z.1 ∧ z.1 ≤ s+w)) &&
      decide (cell t s ds base (qs.map fun z => (z.1-s,z.2)) =
        (base+traceDelta packed,traceWeight packed))) &&
      traceOK rows t ds (s+w) (base+traceDelta packed) len (packed/262144)

theorem trace_span {rows : ℕ → List (ℕ × ℤ)} {ds : List ℕ} {t cut : ℕ}
    (hds : ∀ q ∈ ds, q.Prime) (hprod : ds.prod = primorial cut) (ht : 2^t < 65535)
    {len s packed : ℕ} {base : ℤ} (h : traceOK rows t ds s base len packed = true) :
    Span cut s (s+len*(16*2^t)) base (base+(traceTotals len packed).1)
      (traceQueries rows (16*2^t) s len) (traceTotals len packed).2 := by
  induction len generalizing s base packed with
  | zero => simp [Span,traceQueries,traceTotals,evalPairs]
  | succ n ih =>
    rw [traceOK,Bool.and_eq_true,Bool.and_eq_true] at h
    obtain ⟨⟨hb,hcell⟩,hrest⟩ := h
    have hb' : ∀ z ∈ rows s, s < z.1 ∧ z.1 ≤ s+16*2^t := by
      intro z hz
      exact of_decide_eq_true (List.all_eq_true.mp hb z hz)
    have here := segment (cut := cut) (s := s) (base := base)
      (xs := rows s) (total := traceWeight packed) (stop := base+traceDelta packed)
      hds hprod ht hb' (of_decide_eq_true hcell)
    have tail := ih hrest
    have hjoin := span_join here tail
    simpa [traceQueries,traceTotals,Nat.add_mul,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,
      Int.add_assoc] using hjoin

end SunHardRank
end

section
namespace SunHardCompact
open SunHardRank

theorem traceQueries_eq (p s len : ℕ) :
    traceQueries (cellRows p) 262144 s len = rowInterval p s (s+len*262144) := by
  induction len generalizing s with
  | zero =>
    simp [traceQueries,rowInterval,queryList,descending]
  | succ len ih =>
    rw [traceQueries,ih]
    change rowInterval p s (s+262144) ++ rowInterval p (s+262144) _ = _
    rw [rowInterval_join (by omega) (by omega)]
    congr 1 <;> omega

end SunHardCompact
end

section
namespace SunHardRank
abbrev TraceChunk := ℕ × ℕ

def chunkLen (cs : List TraceChunk) : ℕ := (cs.map Prod.fst).sum

def chunkTotals : List TraceChunk → ℤ × ℤ
  | [] => (0,0)
  | c::cs =>
    let h := traceTotals c.1 c.2
    let t := chunkTotals cs
    (h.1 + t.1,h.2 + t.2)

def RunOK (rows : ℕ → List (ℕ × ℤ)) (t : ℕ) (ds : List ℕ) :
    ℕ → ℤ → List TraceChunk → Prop
  | _, _, [] => True
  | s, b, c::cs =>
    traceOK rows t ds s b c.1 c.2 = true ∧
      RunOK rows t ds (s+c.1*(16*2^t)) (b+(traceTotals c.1 c.2).1) cs

theorem traceQueries_append (rows : ℕ → List (ℕ × ℤ)) (w s a b : ℕ) :
    traceQueries rows w s (a+b) =
    traceQueries rows w s a ++ traceQueries rows w (s+a*w) b := by
  induction a generalizing s with
  | zero => simp [traceQueries]
  | succ n ih =>
    rw [Nat.succ_add,traceQueries,traceQueries,ih]
    simp only [Nat.succ_mul,List.append_assoc,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]

theorem run_span {rows : ℕ → List (ℕ × ℤ)} {ds : List ℕ} {t cut : ℕ}
    (hds : ∀ q ∈ ds, q.Prime) (hprod : ds.prod = primorial cut) (ht : 2^t < 65535)
    {cs : List TraceChunk} {s : ℕ} {base : ℤ} (h : RunOK rows t ds s base cs) :
    Span cut s (s+chunkLen cs*(16*2^t)) base (base+(chunkTotals cs).1)
      (traceQueries rows (16*2^t) s (chunkLen cs)) (chunkTotals cs).2 := by
  induction cs generalizing s base with
  | nil => simp [Span,chunkLen,traceQueries,chunkTotals,evalPairs]
  | cons c cs ih =>
    have here := trace_span hds hprod ht h.1
    have tail := ih h.2
    have joined := span_join here tail
    change Span cut s (s+(c.1+chunkLen cs)*(16*2^t)) base
      (base+((traceTotals c.1 c.2).1+(chunkTotals cs).1))
      (traceQueries rows (16*2^t) s (c.1+chunkLen cs))
      ((traceTotals c.1 c.2).2+(chunkTotals cs).2)
    rw [traceQueries_append]
    simpa only [Nat.add_mul,Nat.add_assoc,Int.add_assoc] using joined

theorem eval_run {rows : ℕ → List (ℕ × ℤ)} {ds : List ℕ} {t cut : ℕ}
    (hds : ∀ q ∈ ds, q.Prime) (hprod : ds.prod = primorial cut) (ht : 2^t < 65535)
    {cs : List TraceChunk} (h : RunOK rows t ds 0 0 cs) :
    evalPairs cut (traceQueries rows (16*2^t) 0 (chunkLen cs)) = (chunkTotals cs).2 :=
  eval_of_span (run_span hds hprod ht h)

end SunHardRank
end

section
namespace SunHardCompact
open SunHardRank

def fullRow (p : ℕ) : List (ℕ × ℤ) := rowInterval p 0 608981813029

theorem checked_row {p : ℕ} {cs : List TraceChunk} {z : ℤ}
    (hp : p-1 ≤ 900)
    (hc : RunOK (cellRows p) 14 (trialList (p-1)) 0 0 cs)
    (hn : chunkLen cs * 262144 ≤ 608981813029)
    (hlast : rowInterval p (chunkLen cs*262144) 608981813029 = [])
    (hz : (chunkTotals cs).2 = z) : evalPairs (p-1) (fullRow p) = z := by
  obtain ⟨hd, hprod⟩ := trial_spec (p-1) hp
  have val := eval_run hd hprod (by decide : 2^14 < 65535) hc
  change evalPairs (p-1) (traceQueries (cellRows p) 262144 0 (chunkLen cs)) = _ at val
  rw [traceQueries_eq,Nat.zero_add] at val
  have sum := rowInterval_join (p := p) (Nat.zero_le _) hn
  rw [hlast,List.append_nil] at sum
  rw [fullRow,← sum,val,hz]

end SunHardCompact
end

section
namespace SunHardRank
open SunPrimePermutation Finset

abbrev Query := ℕ × ℤ
abbrev Entry := ℕ × List Query × ℤ

def getRow (p : ℕ) : List Entry → List Query × ℤ
  | [] => ([], 0)
  | e :: es => if p = e.1 then e.2 else getRow p es

def Ready (es : List Entry) : Prop :=
  ∀ e ∈ es, evalPairs (e.1 - 1) e.2.1 = e.2.2

theorem ready_nil : Ready [] := by simp [Ready]

theorem ready_cons {p : ℕ} {qs : List Query} {s : ℤ} {es : List Entry}
    (h : evalPairs (p-1) qs = s) (he : Ready es) : Ready ((p,qs,s) :: es) := by
  intro e he'
  rcases List.mem_cons.mp he' with rfl | hmem
  · exact h
  · exact he e hmem

theorem ready_append {es fs : List Entry} (he : Ready es) (hf : Ready fs) :
    Ready (es ++ fs) := by
  intro e hm
  rcases List.mem_append.mp hm with h | h
  · exact he e h
  · exact hf e h

theorem ready_get {es : List Entry} (h : Ready es) (p : ℕ) :
    evalPairs (p-1) (getRow p es).1 = (getRow p es).2 := by
  induction es with
  | nil => simp [getRow,evalPairs]
  | cons e es ih =>
    by_cases he : p = e.1
    · subst p
      simpa [getRow] using h e (List.mem_cons_self)
    · simpa [getRow,he] using ih (fun x hx => h x (List.mem_cons_of_mem _ hx))

def weightAt (p : ℕ) : List (ℕ × ℤ) → ℤ
  | [] => 0
  | e :: es => if p = e.1 then e.2 else weightAt p es

theorem weight_get (es : List Entry) (p : ℕ) :
    (getRow p es).2 = weightAt p (es.map (fun e => (e.1,e.2.2))) := by
  induction es with
  | nil => rfl
  | cons e es ih => by_cases h : p=e.1 <;> simp [getRow,weightAt,h,ih]

theorem weight_zero {es : List (ℕ × ℤ)} {p : ℕ} (h : p ∉ es.map Prod.fst) :
    weightAt p es = 0 := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    have hs : p ≠ e.1 ∧ p ∉ es.map Prod.fst := by simpa using h
    simp [weightAt,hs.1,ih hs.2]

theorem sum_weights {es : List (ℕ × ℤ)} {s : Finset ℕ}
    (hn : (es.map Prod.fst).Nodup) (hs : ∀ p ∈ es.map Prod.fst, p ∈ s) :
    ∑ p ∈ s, weightAt p es = (es.map Prod.snd).sum := by
  induction es with
  | nil => simp [weightAt]
  | cons e es ih =>
    have hn' := List.nodup_cons.mp hn
    have he := hs e.1 List.mem_cons_self
    have htail := ih hn'.2 (fun p hp => hs p (List.mem_cons_of_mem _ hp))
    calc
      (∑ p ∈ s, weightAt p (e::es)) =
          ∑ p ∈ s, ((if p=e.1 then e.2 else 0) + weightAt p es) := by
            apply Finset.sum_congr rfl
            intro p _
            by_cases hp : p=e.1
            · subst p
              simp [weightAt, weight_zero hn'.1]
            · simp [weightAt,hp]
      _ = ((e::es).map Prod.snd).sum := by
        rw [Finset.sum_add_distrib, htail]
        simp [he]

theorem hard_total_with_catalog {es : List Entry} {ws : List (ℕ × ℤ)} {x cut a b : ℕ}
    (hr : Ready es) (hw : es.map (fun e => (e.1,e.2.2)) = ws)
    (hn : (ws.map Prod.fst).Nodup)
    (hs : ∀ p ∈ ws.map Prod.fst, p ∈ (Ioc a b).filter Nat.Prime)
    (h : ∀ p ∈ Ioc a b, p.Prime →
      (((rowTerms cut b p).filter (fun dc => decide (p^2 ≤ x/dc.1))).map
        (fun dc => (x/dc.1,dc.2))).Perm (getRow p es).1) :
    hardTotal x cut a b = (ws.map Prod.snd).sum := by
  unfold hardTotal
  rw [← Finset.sum_filter]
  trans ∑ p ∈ (Ioc a b).filter Nat.Prime, weightAt p ws
  · apply Finset.sum_congr rfl
    intro p hp
    obtain ⟨hp1,hp2⟩ := Finset.mem_filter.mp hp
    rw [hardRow_of_perm (h p hp1 hp2) (ready_get hr p), weight_get, hw]
  · exact sum_weights hn hs

end SunHardRank
end

section
namespace SunHardCompact
open SunHardRank SunPrimePermutation Finset

def Lifted (ws : List (ℕ × ℤ)) : List Entry :=
  ws.map fun e => (e.1, fullRow e.1, e.2)

def Scored (ws : List (ℕ × ℤ)) : Prop :=
  ∀ e ∈ ws, evalPairs (e.1-1) (fullRow e.1) = e.2

theorem scores_cons {p : ℕ} {z : ℤ} {ws : List (ℕ × ℤ)}
    (hv : evalPairs (p-1) (fullRow p) = z) (ht : Scored ws) : Scored ((p,z)::ws) := by
  intro e he
  rcases List.mem_cons.mp he with rfl | he
  · exact hv
  · exact ht e he

theorem scores_nil : Scored [] := by simp [Scored]

theorem scores_append {ws vs : List (ℕ × ℤ)} (hw : Scored ws) (hv : Scored vs) :
    Scored (ws++vs) := by
  intro e h
  rcases List.mem_append.mp h with hl | hr
  · exact hw e hl
  · exact hv e hr

theorem lifted_ready {ws : List (ℕ × ℤ)} (h : Scored ws) : Ready (Lifted ws) := by
  intro e he
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp he
  exact h x hx

theorem lookup_lifted (ws : List (ℕ × ℤ)) (p : ℕ) :
    (getRow p (Lifted ws)).1 = if p ∈ ws.map Prod.fst then fullRow p else [] := by
  induction ws with
  | nil => simp [Lifted,getRow]
  | cons e es ih =>
    by_cases h : p=e.1
    · simp [Lifted,getRow,h]
    · by_cases hm : p ∈ es.map Prod.fst
      · have tall : p ∈ (e::es).map Prod.fst := List.mem_cons_of_mem _ hm
        rw [if_pos tall]
        simpa [Lifted,getRow,h,hm] using ih
      · have tall : p ∉ (e::es).map Prod.fst := fun ha => (List.mem_cons.mp ha).elim h hm
        rw [if_neg tall]
        simpa [Lifted,getRow,h,hm] using ih

theorem aggregate_rows {ws : List (ℕ × ℤ)} (scores : Scored ws)
    (hkeys : ws.map Prod.fst = (trialList 881).filter (fun q => decide (17 < q)))
    (hnd : (ws.map Prod.fst).Nodup) (hsum : (ws.map Prod.snd).sum = 7941)
    (h : ∀ p ∈ Ioc 17 881, p.Prime → (originalQueries p).Perm (fullRow p)) :
    hardTotal 608981813029 8477 17 8477 = 7941 := by
  have keys (p : ℕ) : p ∈ ws.map Prod.fst ↔ 17 < p ∧ p ≤ 881 ∧ p.Prime := by
    rw [hkeys]
    simp only [trialList,List.mem_filter,List.mem_range,decide_eq_true_eq]
    constructor
    · rintro ⟨⟨hl,hs⟩,hlo⟩
      exact ⟨hlo,by omega,(smallPrime_iff p (by omega)).mp hs⟩
    · rintro ⟨hl,hr,hs⟩
      exact ⟨⟨by omega,(smallPrime_iff p (by omega)).mpr hs⟩,hl⟩
  have supp : ∀ p ∈ ws.map Prod.fst, p ∈ (Ioc 17 8477).filter Nat.Prime := by
    intro p hp
    obtain ⟨ha,hb,hc⟩ := (keys p).mp hp
    exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨ha,by omega⟩,hc⟩
  have arr : (Lifted ws).map (fun e => (e.1,e.2.2)) = ws := by
    simp [Lifted,List.map_map,Function.comp_def]
  apply (hard_total_with_catalog (cut := 8477) (x := 608981813029)
    (a := 17) (b := 8477) (es := Lifted ws) (ws := ws)
    (lifted_ready scores) arr hnd supp ?_).trans hsum
  intro p hp hprime
  obtain ⟨hlo,hhi⟩ := mem_Ioc.mp hp
  change (originalQueries p).Perm _
  rw [lookup_lifted]
  by_cases hb : p ≤ 881
  · rw [if_pos ((keys p).mpr ⟨hlo,hb,hprime⟩)]
    exact h p (mem_Ioc.mpr ⟨hlo,hb⟩) hprime
  · rw [if_neg (fun hm => hb ((keys p).mp hm).2.1),zero_queries_above hprime (by omega) hhi]

end SunHardCompact
end

section
namespace SunPrimeRaceEasy.RaceLookup.Sweep
open SunPrimePermutation SunPrimeNumeric SunHardCompact SunHardRank

def radix : ℕ := 134217728
def code (u : ℕ) : ℕ := (u-1)%262144
def initial (u : ℕ) : ℤ := (((u-1)/262144 : ℕ) : ℤ) - 128
def extract (col i : ℕ) : ℕ := col / radix^i % radix

def evaluate (s mask : ℕ) (base : ℤ) (qs : List (ℕ × ℤ)) : ℤ × ℤ :=
  let pos := mask &&& divMask (s+3) 3 262144
  let neg := mask &&& divMask (s+2) 3 262144
  let val := fun k => base + rankBits 14 pos neg k
  (val 262144,(qs.map (fun z => z.2*val (z.1-s))).sum)

def test (s p mask u : ℕ) : Bool :=
  let b := initial u
  decide (evaluate s mask b (cellRows p s) = (b+traceDelta (code u),traceWeight (code u)))

/-- Move across all prime cutoffs at the same number interval. -/
def scan (s : ℕ) : ℕ → List ℕ → ℕ → Bool
  | _, [], _ => true
  | col, p::ps, blocked =>
    if col=0 then true else
      (col%radix==0 || test s p ((2^262144-1) ^^^ blocked) (col%radix)) &&
        scan s (col/radix) ps (divMask (s+1) p 262144 ||| blocked)

def columnOK (i col : ℕ) : Bool := scan (i*262144) col (trialList 881) 0

end SunPrimeRaceEasy.RaceLookup.Sweep
end

section
namespace SunPrimeRaceEasy.RaceLookup.Sweep
open SunPrimePermutation SunPrimeNumeric SunHardRank SunHardCompact

theorem extract_succ (col i : ℕ) : extract (col/radix) i = extract col (i+1) := by
  simp only [extract,Nat.div_div_eq_div_mul,pow_succ']

theorem scan_one {s col p blocked : ℕ} {pre post : List ℕ}
    (h : scan s col (pre++p::post) blocked=true)
    (hu : extract col pre.length ≠ 0) :
    test s p ((2^262144-1) ^^^ (blockedMask (s+1) 262144 pre ||| blocked))
      (extract col pre.length)=true := by
  induction pre generalizing col blocked with
  | nil =>
    have hc : col≠0 := by rintro rfl; simp [extract] at hu
    simp only [List.nil_append,scan,if_neg hc,Bool.and_eq_true] at h
    simpa [extract,blockedMask,show col%radix≠0 by simpa [extract] using hu] using h.1
  | cons d ds ih =>
    have hc : col≠0 := by rintro rfl; simp [extract] at hu
    simp only [List.cons_append,scan,if_neg hc,Bool.and_eq_true] at h
    have uh : extract (col/radix) ds.length ≠ 0 := by
      simpa only [extract_succ,List.length_cons] using hu
    have here := ih h.2 uh
    simpa only [List.length_cons,extract_succ,blockedMask,Nat.or_assoc,Nat.or_comm,
      Nat.or_left_comm] using here

private theorem evaluate_exact (s : ℕ) (ds : List ℕ) (b : ℤ) (qs : List (ℕ × ℤ)) :
    evaluate s (roughMask (s+1) 262144 ds) b qs =
      SunHardRank.cell 14 s ds b (qs.map (fun z => (z.1-s,z.2))) := by
  simp only [evaluate,SunHardRank.cell,List.map_map,Function.comp_def]
  rfl

theorem column_cell {table : ℕ → ℕ} {i p : ℕ} {after : List ℕ}
    (ht : columnOK i (table i)=true)
    (hs : trialList 881=trialList (p-1)++p::after)
    (hu : extract (table i) (trialList (p-1)).length ≠ 0) :
    let u := extract (table i) (trialList (p-1)).length
    let s := i*262144
    SunHardRank.cell 14 s (trialList (p-1)) (initial u)
      ((cellRows p s).map (fun z => (z.1-s,z.2))) =
      (initial u+traceDelta (code u),traceWeight (code u)) := by
  unfold columnOK at ht
  rw [hs] at ht
  have hh := scan_one ht hu
  unfold test at hh
  rw [decide_eq_true_eq,Nat.or_zero] at hh
  dsimp only
  rw [← evaluate_exact]
  exact hh

def traceBy (table : ℕ → ℕ) (j : ℕ) : ℕ → ℤ → ℕ → ℕ → Bool
  | _, _, 0, _ => true
  | i,b,len+1,packed =>
    let u := extract (table i) j
    decide (u≠0 ∧ initial u=b ∧ code u=packed%262144) &&
      traceBy table j (i+1) (b+traceDelta packed) len (packed/262144)

def runBy (table : ℕ → ℕ) (j : ℕ) : ℕ → ℤ → List TraceChunk → Prop
  | _,_,[] => True
  | i,b,c::cs => traceBy table j i b c.1 c.2=true ∧
    runBy table j (i+c.1) (b+(traceTotals c.1 c.2).1) cs

private theorem delta_mod (u : ℕ) : traceDelta (u%262144)=traceDelta u := by
  simp [traceDelta,Nat.mod_mod_of_dvd _ (by decide : 256 ∣ 262144)]

private theorem weight_mod (u : ℕ) : traceWeight (u%262144)=traceWeight u := by
  unfold traceWeight
  rw [show 262144=256*1024 by decide,Nat.mod_mul_right_div_self, Nat.mod_mod]

theorem traceBy_sound {table : ℕ → ℕ} {p : ℕ} {after : List ℕ}
    (hT : ∀ i, columnOK i (table i)=true)
    (hs : trialList 881=trialList (p-1)++p::after)
    {i len z : ℕ} {b : ℤ} (h : traceBy table (trialList (p-1)).length i b len z=true) :
    traceOK (cellRows p) 14 (trialList (p-1)) (i*262144) b len z=true := by
  induction len generalizing i b z with
  | zero => rfl
  | succ n ih =>
    rw [traceBy,Bool.and_eq_true,decide_eq_true_eq] at h
    obtain ⟨⟨hu,hb,hc⟩,ht⟩ := h
    have row := column_cell (hT i) hs hu
    dsimp only at row
    rw [hb,hc,delta_mod,weight_mod] at row
    rw [traceOK,Bool.and_eq_true,Bool.and_eq_true]
    refine ⟨⟨List.all_eq_true.mpr (fun z hz => decide_eq_true (cellRows_bounds hz)),
      decide_eq_true row⟩,?_⟩
    simpa only [Nat.add_mul,Nat.one_mul,show 16*2^14=262144 by decide] using ih ht

theorem runBy_sound {table : ℕ → ℕ} {p : ℕ} {after : List ℕ}
    (hT : ∀ i, columnOK i (table i)=true)
    (hs : trialList 881=trialList (p-1)++p::after)
    {i : ℕ} {b : ℤ} {cs : List TraceChunk}
    (h : runBy table (trialList (p-1)).length i b cs) :
    RunOK (cellRows p) 14 (trialList (p-1)) (i*262144) b cs := by
  induction cs generalizing i b with
  | nil => trivial
  | cons c cs ih =>
    exact ⟨traceBy_sound hT hs h.1,by
      simpa only [Nat.add_mul,show 16*2^14=262144 by decide] using ih h.2⟩

end SunPrimeRaceEasy.RaceLookup.Sweep
end

section
namespace SunPrimeRaceEasy.RaceLookup.Sweep
open SunPrimePermutation SunHardRank SunHardCompact

private theorem scan_zero (s b : ℕ) (ps : List ℕ) : scan s 0 ps b=true := by
  cases ps <;> simp [scan]

private theorem blocks_append (s : ℕ) (a b : List ℕ) :
    blockedMask s 262144 (a++b) = blockedMask s 262144 a ||| blockedMask s 262144 b := by
  induction a with
  | nil => simp [blockedMask]
  | cons p ps ih => simp only [List.cons_append,blockedMask,ih,Nat.or_assoc]

private theorem scan_append (s col blocked : ℕ) (a b : List ℕ) :
    scan s col (a++b) blocked =
      (scan s col a blocked && scan s (col/radix^a.length) b
        (blockedMask (s+1) 262144 a ||| blocked)) := by
  induction a generalizing col blocked with
  | nil => simp [scan,blockedMask]
  | cons d ds ih =>
    by_cases hz : col=0
    · subst col; simp [scan_zero]
    · simp only [List.cons_append,scan,if_neg hz]
      rw [ih]
      simp only [List.length_cons,blockedMask,Nat.div_div_eq_div_mul,pow_succ' radix ds.length,
        Bool.and_assoc,Nat.or_assoc,Nat.or_comm,Nat.or_left_comm]

def chunkOK (i col lo len : ℕ) : Bool :=
  let s := i*262144
  let ps := trialList 881
  scan s (col/radix^lo) ((ps.drop lo).take len) (blockedMask (s+1) 262144 (ps.take lo))

theorem chunk_join {i col lo n m : ℕ} (hn : lo+n≤(trialList 881).length)
    (ha : chunkOK i col lo n=true) (hb : chunkOK i col (lo+n) m=true) :
    chunkOK i col lo (n+m)=true := by
  let ps := trialList 881
  have hlen : ((ps.drop lo).take n).length=n := by
    rw [List.length_take,List.length_drop,Nat.min_eq_left]
    change lo+n≤ps.length at hn
    omega
  dsimp only [chunkOK] at ha hb ⊢
  rw [List.take_add,scan_append,Bool.and_eq_true]
  refine ⟨ha,?_⟩
  rw [hlen,Nat.div_div_eq_div_mul,← pow_add,List.drop_drop]
  rw [List.take_add,blocks_append] at hb
  simpa only [Nat.or_comm] using hb

theorem chunk_whole {i col : ℕ} (h : chunkOK i col 0 (trialList 881).length=true) :
    columnOK i col=true := by
  simpa only [chunkOK,columnOK,List.drop_zero,List.take_length,List.take_zero,blockedMask,
    pow_zero,Nat.div_one] using h

theorem no_columns (i : ℕ) : columnOK i 0=true := scan_zero _ _ _

def PiecesOK (i col : ℕ) : ℕ → List ℕ → Prop
  | _,[] => True
  | a,n::ns => chunkOK i col a n=true ∧ PiecesOK i col (a+n) ns

private theorem pieces_join {i col a : ℕ} {ns : List ℕ}
    (hs : a+ns.sum≤(trialList 881).length) (h : PiecesOK i col a ns) :
    chunkOK i col a ns.sum=true := by
  induction ns generalizing a with
  | nil => simp [chunkOK,scan]
  | cons n ns ih =>
    simp only [List.sum_cons] at hs ⊢
    exact chunk_join (by omega) h.1 (ih (by omega) h.2)

def BatchOK (table : ℕ → ℕ) : ℕ → List (List ℕ) → Prop
  | _,[] => True
  | i,ns::ls => (ns.sum=(trialList 881).length ∧ PiecesOK i (table i) 0 ns) ∧
    BatchOK table (i+1) ls

theorem batch_range {table : ℕ → ℕ} {i j : ℕ} {ls : List (List ℕ)}
    (h : BatchOK table i ls) (hj : i ≤ j) (ht : j < i+ls.length) : columnOK j (table j)=true := by
  induction ls generalizing i with
  | nil => simp at ht; omega
  | cons ns ls ih =>
    by_cases he : i=j
    · subst j
      apply chunk_whole
      rw [← h.1.1]
      exact pieces_join (by rw [h.1.1]; omega) h.1.2
    · simp only [List.length_cons] at ht
      exact ih h.2 (by omega) (by omega)

def cellsAt (table : ℕ → ℕ) (j : ℕ) : ℕ → ℕ → List TraceChunk
  | _,0 => []
  | i,n+1 => (1,code (extract (table i) j)) :: cellsAt table j (i+1) n

def carryOK (table : ℕ → ℕ) (j : ℕ) : ℕ → ℤ → ℕ → Bool
  | _,_,0 => true
  | i,b,n+1 =>
    let u := extract (table i) j
    decide (u≠0 ∧ initial u=b) && carryOK table j (i+1) (b+traceDelta (code u)) n

private theorem carry_sound {table : ℕ → ℕ} {j i n : ℕ} {b : ℤ}
    (h : carryOK table j i b n=true) : runBy table j i b (cellsAt table j i n) := by
  induction n generalizing i b with
  | zero => trivial
  | succ n ih =>
    rw [carryOK,Bool.and_eq_true,decide_eq_true_eq] at h
    refine ⟨?_,?_⟩
    · simp only [traceBy,Bool.and_true,decide_eq_true_eq]
      exact ⟨h.1.1,h.1.2,(Nat.mod_eq_of_lt (Nat.mod_lt _ (by decide))).symm⟩
    · simpa only [traceTotals,Int.add_zero] using ih h.2

theorem row_from_table {table : ℕ → ℕ} (ht : ∀ i, columnOK i (table i)=true)
    {p n : ℕ} {z : ℤ} (hp : p-1≤900)
    (hs : trialList 881 = trialList (p-1) ++ p :: (trialList 881).drop ((trialList (p-1)).length+1))
    (ch : carryOK table (trialList (p-1)).length 0 0 n=true)
    (hn : chunkLen (cellsAt table (trialList (p-1)).length 0 n)*262144≤608981813029)
    (hl : rowInterval p (chunkLen (cellsAt table (trialList (p-1)).length 0 n)*262144)
      608981813029 = [])
    (hz : (chunkTotals (cellsAt table (trialList (p-1)).length 0 n)).2=z) :
    evalPairs (p-1) (fullRow p)=z := by
  apply checked_row hp _ hn hl hz
  exact runBy_sound ht hs (carry_sound ch)

end SunPrimeRaceEasy.RaceLookup.Sweep
end

section
namespace SunPrimeRaceEasy.RaceLookup.SweepData
open SunPrimeRaceEasy.RaceLookup.Sweep

def table (i : ℕ) : ℕ :=
  if i<274 then (if i<137 then (if i<68 then (if i<34 then (if i<17 then (if i<8 then (if i<4 then (if i<2 then (if i<1 then (0x403c082807810900f020a01e042403c082807810900f020a01e042403c082807810900f020a01e042403c082807810100f020a01e040403c082807810100f020a01e042403c082807810900f021a01e044403c086807811100f021a01e044403c086807810900f021a01e044403c086807810900f020a01e042403c082807810900f021a01e042403c086807811100f022a01e044403c086807810900f021a01e044403c086807810900f020a01e042403c086807811100f021a028443403848a809711500ed23201a446401bc8a807c119011722a015c474052a8c806851d009c252022f47403ce8a809891d0129a3a01ab484034a92807652d00d624a02b94a404a09c8056d3100fa25200e34a402be96803952d011226201674c406249a8076541011627a02405140314a2808854d016c29a014555404ecaa806595900f02ba01e058403c0b6807817d00f031201e062403c0c6807819900f032a01e067403c0cc807819100f031201e064403c0c6807819d00f032201e067403c0da80781cd00f036201e068403c0c8807819500f034201e06a403c0da80781ad00f036a01e06b403c0e480781b500f039a01e06d403c0ee807820900f03e201e079403c0f880781e900f03c201e07e403c106807822500f041a01e086403c10880781fd00f03fa01e07e403c0fe00000000000000000000000000000000000000000000000) else (0x203c146417828c80f051905e0a3203c146417828c80f051905e0a3203c146417828c80f051905e0a3203c1463f7828c80f0518fde0a3203c1463f7828c80f051905e0a3203c146417828c84f05190de0a3213bd46435a298855ad290cc7a92154b4e419de9884cd5410e4bac212c1524176ea08079d490654aa2029d5441dbeac854fd610484ac216bb5c43886c089195990d73b1211fb5e4107ebc858a5890ea0b32123b624136ec480d8d9105f8b0213b560437e2c08484d8908fcb22240b624496ac08ac6d8116e1b12240b62456dac888a55a11abeb222aa56846a62d0936859919e7b3223af684687ecc8d7d5911d18b224503604a476c49129d812562b126bd5644b772c0931bd8126d4ae253375e4a412c4976bd692d65b1263af5a4f7d29c9c505694211a9282955852cfea4a487539534da72a11d4a558ce9cad6a5395d78a72d3634a5e7aa8cc2f352985dea23134d486599698c925d299930a732cc94a6355684c338ce98e14a1313eb3c666827cc6d04f19a22a33649752727cab8d6ec5599da9aa31b2b526483eb0ceeb551a5e0aa363c1586a782a8d8f0561a9e0a838bc1526c7829ce4f0541b1e0a13b3c13c817827cf6f04f1e1e0983dbc13e7978264eef04c1f5e096413c126887823d04f047a15e08a41bc1107e78218fcf0441f5e0883f3c10800000000000000000000000000000000000000000000000)) else (if i<3 then (0x313b2506377ca0c4ca9498e7929313965463cf0acc44b1598e0e2a313d25863a84a8c4cd1698d6f2c314fc5e619f0d4c42319185a536313d86661560dcc5149a18d5933314986a6358cd0c9049a9966d37321886a68c58c8cc79999ae5232341dc6666598ccd36e191bb452f350ce66683d0d4d11f1a9a9ad3234c2c6a6b344ccdafd191b19c3337be6627272cbcece9969ce372f3839e646fb5ccce53d181d6882c392c26071c98cce33d1b1c1813538bf066729fcc8e4a6199ce5e343a52c6e73618d4e9859c1d550333a52a7276810eceed11b9ddf43a3c4086c798a4e0f6fc1c1e20f3c3bdac7e782d4f8ef24211e1623f3bf987e7a710f8ef359f1e5c13d3f172747ab48ecf17c9d1da973a3c3f6727a570e4ef2b9d9ec96393c67476759ccf8f4e69f1e1fb3d3dbbc7a7a844f0f164a09e9fd3c3c2fc827b630ecf8f11b9f5fb3b3f42e86809ed2d0b0c27a09784a42b3a9e8a8c94510f7a6231ce5044c8a9c83ac94cfb202ba0def543fc18aa846f14d00e72a2215a514a2ee9c9f4352d2aada7242604d45bce9c8f8d9412114a4249474d4bad0a6938f9392f02a9a45ed4e4ccc0a4927c139330ca8231ce5149bc0a49f7812930f026a3de0504cbc09a91781451cf02ba49e0564a3c0b8967818520f034a39e06c453c0e483781e50af03da11e07b40bc0fa00000000000000000000000000000000000000000000000) else (0xa9374814f2e902e58d105bbba60d72b3c1922680320cd006b85a00c693441cef6883b20d0081a3a01533f3827fa6785923ce0a5d79c17637402b3fe7856bfcd0b3419e1673b3431066586de6c70c44596196933030ebe68721cc80d57998189334034fc6687195ca0e471981c82f3c388f6a86e1ed30eb31aa1d953483ce768879b3d20fc7ba0206e73c45086708590ce10bf5982157b2442cbe6881ced310c6d9c2354f244cd7e18928ac511d438e234c3204951e309932c3151cb82277df0856b06089e8cc3162b97e306daf85ae4600c1aec016b6b883093b0c651fe28ccc7c31a9f77c35d170c706d5d8da3fc31a9b7823756f146933e10d5bbc61bcaf923470b1c632ce38be4ec71835398328cb546341e68cd6fd5193019e32973206e8d640d2ccc81ba9d9435aa31c70a6e30d5d8c91c2a38c358432864e9668dde4c8201f5804a3f2eca6f95b12e1fb929c2d6c5a99ae8a6addd16e03b82b3556e5564ec8a6fed8159adb629b8f605665edca6f35b161a0b630af772698d6ecc522dd17281bb2c293725e8faf0aee95c97a57be34c2d80607a2ecd32adb17a29b9352a5665f546e4d0f8dd9725fc0324917a6874ef8c8e9de17a1eb732aa37c61782e4c8f05599de0aa37bc14a767826cf0f0491e5e0913dbc10e7b78210fef0431f9e0843ebc10400000000000000000000000000000000000000000000000))) else (if i<6 then (if i<5 then (0xc706b3185c0663243ac66275598c4c8349858670314d2d664599b4c913b418db56e32c8ad667891a4ccd2b5995066c33d48d46a991a0e0e3b11b5616638c86c66e72d94dcd7321bdc56537434cc6e92d98df28b41b98567362aed069421acdb2cb41ca4c6737334d26b671acd0d9379a1fd7034b82dc6a745b0d2e7379a15d7235416e8687a1c8d6d23a9a557753545aee6d951e0d8a73a9be2978383c4e672819e0ecf23f1d65e7539362dc7793dd0e53cb91e1a2743ad94e07b6a1c8eb04b91ea71723fb68ea7a9f1d0eef1b99d612743db2edc8669190fb12b7a1d896540328d6797a1c4fd15379edb17140456dc7b561c4fae2bb1f5f5753ec24ec7e5e5c8fcd4381fa42733fb10f084861ed10de3e20def7844462fc934fdf5190e3da49f67d46410f886751e50548bba2dd274414b6f28c741d110dd37a35fc744cb08e6a3689dd370439259e46d48390da99751a91ee23926e1070544cecc9a7d9a13cf036259d86a4e4b8e297865ad44dfb4a6da86650370e0a56e9e53eeeb9251867b514c2da998cdd91d02bea41997849bc0f8907821512f045a25e08440bc1087e7821108f040a05e07f3f3c10a00000000000000000000000000000000000000000000000) else (0x4f67994a121b29423168283fccc5179d94a2b23494af66529a40d25296598a301b314e096829b14ce5371d94ad13b11520a6629d8cd453bf1b4a88ab5960e9662b580d455a99b8ad4ab895d6e6d2b332d45585d94af0a3596570702eb4ce6598c9c0beb738976ad6d30330e0645a9c4c174b89990d71315eae069341bce6a6b51a610702fbecf06a795b8c6e4bb1ada86d3223ce46c9d1b0ccc4381addd6f39cc4d86d681b4d2f8379a2746d3427ae069515d4d6e4b59adb97335544e669871bcd8b6b89ae296f36acae66b885cce4da3a1c6916d39348e86f769c4db22381c1c0713b42ee47e9fdd10746bc9e8af7a42cf6ee8f619cd0d0cbaa39c17643d0ee67e8b9d0f0fc371fa3f753d3bad47f751c4ed293a201637045b96d69960d89190a33a0a396f3e3e8d682661c100ffb6a29d66b46bf8e881435c512c53c9fdff754635cec81825b914d83aa01f37247c10d69d7ad9520baba239d07047384dc8e639891498b3a1ded6f47464de946e5a926f033231e070423c0f281781f908f03e1fde081413c0fe00000000000000000000000000000000000000000000000)) else (if i<7 then (0xea2fab1cb354a375aa806ec8cd8e68c9e1e3fd423f5fa907d1d500f6149c1fb9b404270a8c8d1c5290e1ea51fb3f4e39616ac82ffd21228f9f27c3930487c2789ee94b125969d27baf30548425ca0cacc959e59528bb52c576c654b8e6cb16190972b3e72e5765e68b0e94b15e189b2abd92c5762e68ab23cd1659f9c2f3ed3a5971e74aef54d151d89b2bbf53a5d7ba70ab28d09757e9f2e35b305775e50b8faca16618932fba7265d8263ccabbc71763c9232b1d205f63a48b9084a181f59333c43267186a50f6eacb1ce27923dc152e8184e78f4fd4c20dde9d3cbb1347186668cb0ad29c9a59d31b8f4a6f74e8cd310d31bda7a93abe5607a6ead8e4ec5b9c1e9b0334055c7177ec4d8dfd61d21eae404176471692d1030f5b9ce1bb240b256a6e92afcfc96da1c5f5bb3ccb760817aaa506d74e9f60c9c3dc6f406f81278e100ca1d5c6913e40f1c7d9ea30f0f1c91ed858f3e3c1187e7821cfef0421fde084403c10200000000000000000000000000000000000000000000000) else (0x161b9682f44cc46472970d4c02a99e455732be8b2637016cc919ae19a5b5b33390bc657357cc8f5b2196016033442c46a69598d114309a94f6733536ca6b70d88e30b319b97e603628cbc7095978da8b2d9c6745c352bac07087574dcc1ad1d1e45f3d304c6757d574e10cad1ba535739baeac787bd68eb042a9ede05839d8ab06a9bd58dedbab9ae635938b56ac6b8d168e5202f1b9665c3a522ba7065560df23291c96e553cb98b4846317d20e02ea11a76048bd4b49e6415d22dcb1a7dc25a493dec88a80da11341afa39b56743b60ca91721951ca630a5e6d60523c6beaf6a58d510db127dd86149c80c0a17fd892ecfad286116358b74caa47b1816f2228291dc5b5ab689eac6415d62ddaa2adb55554298caa9689a13f0236261fb624d358da8c731dd06f9bba15ca8144b53028871dfd12d13da26497643b46ec84781cd04f03ba09e078403c0f600000000000000000000000000000000000000000000000)))) else (if i<12 then (if i<10 then (if i<9 then (0x3d62af47f066010151c021c498043616f08ee1de91237bd23b297e4f8c2f890cddf94211bc252c97a4c7aefca6cce093620be24c25744d82efc8f2cde931f1c024bbd7c4c663048eb35f149f9be2e44f7c5179f0092f85e9117abd244137e516a6e892e65f949e4ba253bd783f6a6f48adade90dabb7233817e44846e09eed5c12603b6283d3704771ee480d15d11a26b829345666281694d8db4f98df2a43539d467485678e6d2c91e20e9b3abcf247189238ced4c89d2308d35c6314757f640dce8479d9bf9241455249183255130b489fe6388393530c826d228e121c420e10874ac3efa837ba390cf9c89f9f19241bdd24826ba1d08e3ca9fd6690463e7169066e5d1538499e63e9f433d93a8268e48f2e64a216018e44d0118867122d0702c61f9fa8d3e3231e7679240f0f0459e5e0853d3c10a00000000000000000000000000000000000000000000000) else (0x41398fe7e7be0506f2c2201fd7f42a9f048c7ee110ceec222dd486433b5088a9061926fc43229eb874148b0a8b5d61106dcc222dfb8343421008c85e0508d04123e167b4cc24ec90841e50b003e201f77843378f88a71df90eee3d22dc38142bab007b599f502db411e5cf81423a9007b75a090ce2bd9f9ec8143b68f87f79e0cf2fcc31f5ae85423e50086682151522c7219ca894636d18917c64508e84aa49ae90433df2a7e80e3ceee445a02258c3a39118846e21cf8e54321db48949b9726a58224d32f747219ba8d3bbd7188b73a0ceed9c8a26008a48c0b14907e6292d2649a3de48e4a3c52c887da653104c7a39bb864b35916a69d6013903c025e0a7651320e2938a5dd18de3e249b97a4a37cfc9070e051d20c1a2a1a85453cafe8571df904fc429f5e0883f3c10c00000000000000000000000000000000000000000000000)) else (if i<11 then (0x8f760fd13131ea41ea3d44bc6788f6e8f930f69ea42213e43426848e6c0fd0d05a2235a14342b7e868c7dd1d0ae0a2225e447473349a888a91d00e0231ddb04440bca888783d3100cc2322e0748423b28e7788d3904e3a39e5d15141b94947c6953d0110a79f9ca4d413eaa68179d2cfceaa2205e64a41be69e8a6f9412ee8a6a39b04d4bc049ca19415530d5a9285f1574d386a88c7c95902d62ba2dda5a3fc4caa8a8357103082b23dcd5a52bb8b0b7925654cf3ae249f86841344de8d789b10ee7b7a49d66b4d2a4d2997ed8d5100b0a71c86554b82d4a0721714cf23424dc16d5053ad4a5651b93698b72319f78492e6ea898a9f10eec3e22e027f48be4f2907d1e520a839239de7c44395008284e050cf33e211e07b41bc0f600000000000000000000000000000000000000000000000) else (0x2241b104c7ba20a8e1c4936218523b69024c7ca1c92fac193d8a8523c3306527ba1091094013dc0852d36b0e4e7a6188ae4c30e97e8b223850c52699fc8b12c394a0481253f10a4478a14910c42125d78326325044a899f89ceb41929c8802a476fa4b6d20c82c34492a448628ba30e5962638c6d44a16a0591323d7287583a48d2ebc99ddd99436c0518616f614aefc3d992067e29b4cfc657cdf4aceebe9a206763e42ed68f7618502dcb31e5dc67383bcd478699b0eaca351f21c744141af87b751d5109f40a0195774941ee67b759fd1b04399fdb17444b78ee92835c910f7bba0db57843472ee847c1c104fcb7225ca6744b90d688915c902e73d225de7143c64ee82751f102d53e1f9f3813ebc10c00000000000000000000000000000000000000000000000))) else (if i<14 then (if i<13 then (0x23bcb3a5272a7c96e94d14dc2a124c054455656788efe5294daca030397365381a849505d511220af24b7d605093ac096cb5814a2dad274215e487c2b096e1d992dc7ab26c2f604764eb8a0aed59263da92833f584d7e68c92cdce13dcba02bc45446689e80ed014f1a9e19a3bb7d3c8674274f705caa2a0b9b3c3d532657e268a323ce1858a9d2849544617aa70a4c0d297601a633355486f85294ccf35217e15a32cbbb46637029cbd19cf9bdde9b3ebb3266f7b64110f9c39d9df964232d1e797fa34fed6499ca1c923fb7b1e8371220fcf8459e9d3893e3d51c7373e58decfc99bdff9639bdd26796f634f4fec71e5d78d3eb590c7d73a24f8f9431f9b987413c10600000000000000000000000000000000000000000000000) else (0x1cdde71353dae8727ddb4d702b91c9f96e3d3a2e27371dc8e6ed371c9b06f3c3f4e07f6d9d4f4ddb81f9ee773e3b4de737d5c4fb0eb69d59c6f3e40ede747c5bcf4e0bb1c5bf763dba0ee6f629e4c8e93d9ba0c7a3c388fc858520526eac020e157c4a3b8f8a25c6011f0e40a91548048411047e6ce10d8e4491f5bb8538c39107c78224ecd9c4209de8444be708936b2111317c1a0607763dbbae089819d0f8f23b225f77d47c25207e752491cddc822e0982493cb04857e20922c3c0a0def8946c08fe8a7ce0910ffbea09a07a44bbaf6887a9d1030339a11b47342ba4f48580dd90ee93a215dd79413bcfc858f1ed03003fa11c977423c0f200000000000000000000000000000000000000000000000)) else (if i<15 then (0x5e87978b8ee2e97dd15e353f0be6467568c0f22a181ff4b33be2987379520d301261d1a24635450906372124d2c52898de84c353e49a6284938deea24199d34538b8c906795910bce32319e4b463abe292858013524ffa89f9d65247b80a8a16e5611ef9aba8d955548bc6b48179998faf932a05eb673c418d48488990fafb31a15b963463fcd0969bdd916d8b89d9e476353c6f87c765d4e2e5b4a157e6b4f41aca8f7fdad3ad3b5a31fe7049bdaea86769f922f33ca2de87845b44f68b845e908fa3c9ee0a7c41bb6ee7b7f5dce6d1bc9d9d1843f39f047a7f21cf4fcc49f602863fbdb167f83214feec429e9d3883e3e10a00000000000000000000000000000000000000000000000) else (if i<16 then (0xf2249624389283d8d25866b5cc8a9c49b193e9363a72a6c68e64b8e5fb9b18b992c2b9124472c2470ba62911b2e7262f8a2406cbacb8a925931c4fd2c2a5fa4846fe448b19d911eacd1c5169638c4e44913d6996313bf207875614caeb491ddbe87353c9186678e34c2dfc619e098c30b8b16676ce38befc4199dc39139bc3288b72638f6fdc71ae178c32b4ef4707e610b2f8459bdb783413f4f8797a1e10f013b1edd77943bdae2836fdbd12e735209e76c42bc8e4846a5e4f8f7c01d9c97e3cbbd0a7177a20d727401e5e2843fbdd0480742010506c2209dc7c44b7ef0837a9ed06f6be205d87c403d6fe00000000000000000000000000000000000000000000000) else (0x527fae0971bda911f6b3263ab7254832e894d75d94deeba233777a3b7d2fc8cf3620f9c7bf243d9883e81f1898ffe58f24fce26b3d9e3b7df5056f56a8f1dfd62545dba5e6836ce70569191d3dd38c39a87c8af58ecffe91f58dd33ac8da47276b2cd8f0e49c9e6cb35c097e7468720c2dd651ddb9c24349f82988c30d10e0dd1d9e6b12f4216e7378edcc6f4df1c5e9bc3eba57e706cef8f8eb5c9cdaebc3bb9d767174aece5055f1b5e3b63b37f687c686b8f732d29cd75a93ec23487874670d4f3501f1bb99403a12e7f7fa510af2c69f5da8e4037b167d7ca30fcec411f1d5833f3950400000000000000000000000000000000000000000000000)))))) else (if i<25 then (if i<21 then (if i<19 then (if i<18 then (0x42397188d60a39091d46231e58f413cb16796e21912e7439f1e08545be11683826152d06c1a25ed7e4dbd8fa8e789e0fee73da45bf735344aceb880d7588eb2c301db54623dab0d1769558ed42d33e155a63358b2bc7456968f7a6af1fc5754bcab4bb839715506b2ae18c6463328deda8fdd182d83f29a0b854a3c322a97322140bdc02b229805dab706ad82209691ac1ab9cd8258bad06ab745f15ecac0a89a98154cb2f6a98b9f53f0741a6e02855045310937b61112ef3fa51d27e4b369009285dfd230841229b680453f2ec88785ecfee1c21f9c7813fbbd0000000000000000000000000000000000000000000000000) else (0x9a72df51ef63ca69ec7c46392f47e771e11eeb3b201e5764ac0ee28770db530e93721a09774bb98e0856d1f0f2f74220da57c463a4f6947bdf537013da4de27e4dbf4fca5705f940e4bd2a1d37e4f3ff009577dd100dc3d249f17541430f0967a9b51d143026e086d5a3e8d2cd4e59d7d17332a9c5705241cdab08cdc93ef7372adec735ed12d2ae7c1c96ccc372bdef6a59c98e0a6819d55f03bc289f67e51b810aa58ce0d42ddbf27dfa6f53a6ce69673df90edac0245c8814ac14fc90769e124dabc225e17d3fbc50e827921d04df429f9d0883f3b50c00000000000000000000000000000000000000000000000)) else (if i<20 then (0x255b77e42b6af8756f9e908d8be9d6157d42ba2fe737460d0af5bc9f1ba8143404f280779e0f8f8bb9f9ca7a43404ea90735cd2af23ba41ca754c424f2a2859e932e1b9295e27c4ec3edc88721ccf2fb3b219d17a3cbbcde82709f4dae5c121de8774e430e8b37519d470433266005d483c8aea17557518fbb4a75e36452beed29f691ad46bd3aa61d775513aaf09a701d94d0d3927dd57453c7ceca7745ed3cecbda35dc7c4cbb8f0938e1cd0ce9bc2460275493b6e887789cd12ee3a215d77a42beef688755e10cfb3f215d77e41bd6fe00000000000000000000000000000000000000000000000) else (0x6e79e8101124f1c5b0a441bb13c758c694fafb511f22f9d3f3a5467771aa4e504549ddeea93d3575c827a2c1173259a1193ad484516a9b97b0514fe5fa826ab9453d5707a82f00dcd2599fdf1bc33bc9747e916dcdd15dc1f59fb747c67689977ee110ce5b1d611b733471707d752d0e8ddd8a01d7ae46b4b5289792912edd52a31f7a34caa5388f6ba712f014e2497f984e38128a17f66130ebc9221ca95483dd388584678fae94c2161f9842b832a797127cf8e0c79f9e18b3fbcf1c7f73e1506f241209d48040be10200000000000000000000000000000000000000000000000))) else (if i<23 then (if i<22 then (0x13af73f251cf81503eeee99741e53cc23ca61ca7a50458f09f6d1d134f7baa7db37753b92f0b179de97ab841ac1ea7e624c6f4db7e9e190cfbdb62397c60b2708b9661cd41093dae9d5715035aeab484dd54ae8baacdca79612b8fcd0a4e057af03d2adbb7a4eb9902b0561f148eec1ab606855abff0aac6edfd77403c2b9f97c5a31efeaa879fd64b63eaa60d7557c3ce8b8775cd52d23ca71b17d55bf8f6a2775f12931c3271dc7a4cc08e697759e114eabfa21f681463cafe837461108ef40205d78140bf30000000000000000000000000000000000000000000000000) else (0x134e8a3a51e4464b3a0989173d352cf4a6a45f94e4bbd6a092749451ce229255f1544f3ceb6aa7359d7eea31ab5f2655eb7ac6d28a57184b82fb4ddd5d623a09cab7a52d34fda5aa9e64c4a3ecb4a86cd4932f6a72adfc525fc14a8d04f1656cedaf291a3634ebd6b6ab829694d132a2c5ce525cbf0b2aa6f57564e92faa5b161594b2caa87f9815ce1322760a6f513e2f2aa7ddf543033c261c87c52bbeea9d775cd3302392556f7545c28f88e729ed10dcbd221da76453caea867bde906dfbd205d77f403bd0400000000000000000000000000000000000000000000000)) else (if i<24 then (0x166146b30bb8d25d82d9cc51d3597a106c3332ed66292d9cbef1ad9a207653c414ce907c58142f8b0245e5674fbc8ccad7a5d94102362bdd07848b3cfa756ba0cc8eb439d6028636c18fc7975e0ccce1409f214864935910a88ce092714c3a19f2833bbdf128472220f2f1c2a09ce8c48b711a868022d21014422609804b3c0fe877160922eb4122ddf7e4d394fca6759e930fa3da4ddc7a4cbf0fa8f7aa0d14ebc0a25c77d433f0fe88805f902e5c41f5d5873f3ed167f7662cf8f7c29fdf08340bbf0000000000000000000000000000000000000000000000000) else (0x4371f1898f06312582b7283f980486e6d07316dc9318fb52f3c7606f87ab900f7d31de0394423cd3aa27565d16edca299e58d46bb924777ae68d5004c9e9ee9e353632a7b6f654cceec9a05f78d4cbb506a98360132f3c1221eb883fba50a8b7560cfadf42a35d5824ebf4f890771e92eec3f221e47f4a3ecfc887660d24fc41221d17f4bb82f09f771d524e5bc231ef704abdad691769cd14fa3fa15c682423c5168579a2110f54320db083443aaec897b1d900e33f205ea7b403b90000000000000000000000000000000000000000000000000)))) else (if i<29 then (if i<27 then (if i<26 then (0x12301331fe116847bc0ca7b6a1a8e2aa33a02066246bb4c29c75d854af639229b075503b6f6b8749d93ceebcac9c27b4f390fa90751e504e9bb25def733f43ae28f76de0f0f440235d7784db90f0a8749d934d3bba3de07541ba6e88d805e102f2bba39c8734c39eec89775f9290140a19e78148baaf88a7b5e526f33ca1a05734737ef093839d912ea3d9ede1863fbbb02837c9e510e5bc219c978473b0e88c7d9b91af7b9a15de783eb9afe7e745f8faf7bf9ede4833fbad0000000000000000000000000000000000000000000000000) else (0x199cd5839c00b2648cd68aef031185fd6236bf8dc7c7b9d92d03ba9f9e37a4d356e4ad6adc92ceabdab244724d39eee88761d0eedf36a25f172373daec86769cceef1bd211cd7a49424ec9d785dd2108bc20dbb7b3b3a4f8847e9f4eef03e201ff8146bdafc86751f528e6bea19e27d463c30082791ed16f5c09e1e28842ba118886fa3906f444a01bd8e3fbbf187b78e58fef0c69f5ed9140b871c7977e34fee9c61f1fa8b3dbdb187b75634f6f4459f5e6873f3a70a00000000000000000000000000000000000000000000000)) else (if i<28 then (0xf5e08825bc1003d6320c70e6381099d7b2d380f8718020514dabd9ddfa7d45bfaf09e6f9cd2101372758c78483d2e87b755c4c6f3b89e9d76f31bbaf4787d9cce0f4b91f5e26e43bb4dc93795ad0ef8371f5d76b38c80c2806f988e4e2b2202185e453b2cc827298120f02ea09e05d45bf6c47c7bd6d16f02d1fdd3594839aa6957dd6116e633236006545392cc9073981170db1a35d06f473b2e8857b9d914fbbc219c681433d3068778df50aefbea0ddc7d413bf0000000000000000000000000000000000000000000000000) else (0x112048f253cf483f8066c4ef04d8f1fd9c2abff2a7178e4108f0479cdfd94413b328908e26cfac7caa52439441c1b1a6b71a28a6e9cb9a1ed932e3c9226a77644c2eec89aa0b913a3dd287d7f668e8e74c99df59628b67406176a70ab03ce175f09c37b73326179668d8ebcd979fc99363a3365679a88c8f14f15dd6a231399386c80e54e0f9cb1c5b79737bc5206f7c640daeac29edfe8540bbb0a7a79a2502f43ea19cd77443b0f4837b1ed02ea3f9fddc8040bd8fe00000000000000000000000000000000000000000000000))) else (if i<31 then (if i<30 then (0x36beb3c5978a6c830dd215dad9d34bc1428076e6d2505cb219f38f4ab8b22aa6a24d22f64c29dc79847bbf28747b268d2eb4b9e9ca96363c9347a73248e2e3491e9d49543c2132968925118e2481f1dc95383ed307c79270e0ee4c9e1e59f43c0d3c7a7928d0cf3541d9deaa43305427781a8902e9cf9e1db9c3ebe5428077a610afd4aa1df9983f4292e7e79244e2f1c81fdd28b42c030e826ee1cfaecc51f1f18740bc30a7d76e20fef4c41f9ec863fbcb0600000000000000000000000000000000000000000000000) else (0xc8ca2e9cdd16244bcab09a78d554ee12e251ee5852c08bebc669895110adaf987625135ac88d735a4fee3b5a3de06442bb8c48b765a104fab2a39d56d4fbc6d8a9709d536db3ca41ec7443b9ae297805c510ecb825a0c72523d4da9c83dad5b05b627ded705340cf298855ed3ee54024ddd814ebd0fa97759f132d13e27a14794a3510e8e88e1500f4c5225f48e45bc712887ae010d0742209e68042bb7008476dfd0cf0bf20dda7d40bb2fe00000000000000000000000000000000000000000000000)) else (if i<32 then (0x1521b7b303b2fa6e7d20d04f8c31ade38641bc90e9d79e2904f04627de08a42bef247578a4cd2f4491c9d896333cf2e7282a60ccf4c91e9ce8f45391229d75e2d26e944a0dcc8b3bbdb128779a30eef14721dd68e4845b1e8680e3d311044239c3804f3cef2927e1dd3cd4bba4de2774cc1ce092775d528ec3fa59e6744d3bae492749bd12eeb5a59ea6c49bdcdc87789f912f440a05dd834239b08827ae1506f2c11fde5813fbdd0800000000000000000000000000000000000000000000000) else (if i<33 then (0x2e3ad3870806810ef64f9c1e59d44bc13ca67865d1af0d0aa22c944b369288779a5cf4f4cba1dc0963e42726896826ceef1cda21f2984d3bb22a77224936ee47235b48f3fb651c9274e2d08e047a51dc8e4f3291a9468a1d3eebc6235b88d4b39f268879e5d28f14c225f996443fb288678a3924f0c2225dd8545b9f128080a1ce707c1a05f778403bafc847adf112f53da0dc47d43b9efe8677e0108ef401fdde81413cefa00000000000000000000000000000000000000000000000) else (0x8f7c68d4adbd3a31e0a9533f34abc7827d5b0bceaedaf9f54c273c9d82e6920f14ba720aa24737f3ca37da6522f14ba7e3d96553cf2eb875a5d50f64d26de29a464052a9c8625924e8c92860790553332c9a9324954c146a66058c54487169e6ce21570745279eb894db831c937d2312aecc6235b58649bff1c8679648eafa4b9e1de9c3ebc32a7f7563506ed451fddc8442ba6f485741f906ef3f9fdec843f3d10a00000000000000000000000000000000000000000000000))))))) else (if i<51 then (if i<42 then (if i<38 then (if i<36 then (if i<35 then (0xb182d9196edb1ad2016d653acccda8ed9d92e0b1b662b66633c0dcb66f9b54cf7b42f5bf6155b74c2bb7919d4efe36ad17c6b6044edece739b582e233ad1d95f50350c0b17457946ebb02c1ed635fca4d0ab7e5b96d00ba291fe795934ef6a5659e168e13aa99df8354385049e745f540eebea49bf7b50426e897791c516ebb8a4dcd7448bfce08b791b918f3b9209da7a3f3cf04827ae0102f3bf209da81413c0fe00000000000000000000000000000000000000000000000) else (0x15b04c4281de8857b2712c066e2d57044aaf9e08d59b6f0aa2842191afb43a75b88b45bdb18a180e2526e8c3279b78c573811aba792394ee448a49e0933fbd5348e7926d04e849a4a0f95533ab1a986a23d52f0c72721d8d563031a9c7e245511b45aa1b58a54b66f29a7b21138e53e231f38749beb0a876ea00f6f240219e67c403bf067875e14fae1409edde823fbe9008174600fcefc2209d97f403bf0800000000000000000000000000000000000000000000000)) else (if i<37 then (0x169033a29dbd735bcb4e8ca655bd7ee0b4b29a66d5bc46daa77819526e7b1a9de0654b3e6c8a95d98930f9b1aa650615d2f2c8c7739ad6edb33291f06a4c388d2a87e99d28fe30a9a1364593d2cea6795896d28b32a1d3685c452ccac835bd64d8332c5b96750b9ce29d771d92ee537249ea6e4bbb4ea86771e4f4f03b205e97b413a4fe7c791e0faf6bd9f1e47a3f3b8f680789e902f7bca01d87e41bbafa00000000000000000000000000000000000000000000000) else (0x265a47b55424ecb893de14ef63aad99e7551bf8ee8b66de4eaedc1a2dea823cbcb008a781fcf4f03f225f77e4ec46f6b14f9e138f8bf236297e403f5008e7a210e8ddc5225f2854c4550a8774e2936d542a3dc2864eb70fc9a82e1d2ed2c4a5de58548bcf0e926e60d08f6c49fdd18545bcf0c7e76a44df02489edd987403cf027370a14eeefc39d5de893c3bf0e797c630f2edc51f5ee853fbb90800000000000000000000000000000000000000000000000))) else (if i<40 then (if i<39 then (0x24db19d4fbf944af87a8536dad2aaa5baa4cbc748837fe88eeefd0a31c19f3c3d53c887527ceeecd0219bda24bbaf4ea88169d3312d3229c0a63fb7336917b668faec4ea35df9b4e3a92e90722513edf4b251db9d4d47b2aa06460d3ef94126dda8f4bc1f30947229d18f5d4a0dec9f483f3368e7ca40fef348205e293403ab22777c254faec491f5e1883f3bd16847aa1504f4c1205ec85413bb0200000000000000000000000000000000000000000000000) else (0x603c0fccf892157edf3f34e1b845e35f0aa475a312ef2c32a9e0874abb914a67a2312cf04429dcc845eb810cce7aa0d7cdb422be42824cba904aa7262d32f046a9dd3915942d30a372e6968fac52c205915736d22a28166d40efcdaa62591574351cba7a20d6907c1a85d185553bf0e9d7ae151ce2c6a4d968f483ef148b74a111ce8c0a11e78244382f888761e906f1bf215d17d413c4fe00000000000000000000000000000000000000000000000)) else (if i<41 then (0x5eb2324d37826178d14bb5a43976033f32af7626138f04a2c212934f3c12ab1782653adf4caaa13a1613312cd08765982f64e2c2109b4d3c934b4902394af9c3adde38364b3f02bc749e17b17ba301f2725f358e0bc5d1d174f2b62e582715dc24e4bc7a9d16d0837295f572583b2d2a17cdb934e3b3a86026f4cba0e88e789e91cf5bea15e28141bd70a817aa1900f944a05dd84403b2fe00000000000000000000000000000000000000000000000) else (0xea79e0da4f0413b1e0856c31504c6696095ee9c4b09e78c5937316c9846256b09c3b29e4826bbc108e5615fdb8c23ab298c6d59c02eac160df156e23eae5b07e64c3ef4b37ba0160e6c12c5b88156bc506af86e014af9c3aa6227f5637316af6e62d46f443259af884c395208e7722d00ebc0a3e1b7a463ccfa87759d914efbc215d97743bc2f286751d910ecbba11e37c3f3bf0600000000000000000000000000000000000000000000000)))) else (if i<46 then (if i<44 then (if i<43 then (0x1a6e4bb3c1c66f6cbc0dec768db96f00b6335a26d5e3deced16b1a576f03632dad726d3ccf0e360a0da10fc12d9e98953b6f14bc67a154ee441ad9df80613dd0ab27621162ffc42c5df8657c02feae781ed56ca3c29d8e775b36cd4b9815b150feb7a75f07353bf4e29879de500f43fa21e87d443a2f47c78a1902f0419ede4823fbcefc7b711f8fceebf1fdd57f403c30000000000000000000000000000000000000000000000000) else (0x190d0a6b7a184e63bcc9eb47193544e524ae5cf445141c88b983d114ce7242f1e04468bf288e589d19a315a22f9ff46583b47ec08752152f8a5ad5f65063350a4b58294970f0272d9b95556baeb2a87217544e835a75ef6e4fb7af0a4815f92cddc223e09814bb69069071230fcf549a11d58a40b8f148177a1906f2c21f1e5843e3c5047878a2cf6f4c41f5e5843fbc50000000000000000000000000000000000000000000000000)) else (if i<45 then (0x2ad91a54ab45488078288d4f6519f1fca532bc14c7c72e90daf04f1fdd3944a3c130aa79a7528dc51a0e1da6373ad4e8778e7ce6ec4ea11c69f4bb7d308684a950adc51229c29e42ba13e846e25518f9caa29e78d4b44d18a16ca2d32e7c823de7894cb7f069b785e120e73e235e476453def8867b9ed0cefc11fde1843ebd3128275a0504eebfa01cd7d3f3cafc00000000000000000000000000000000000000000000000) else (0x5c3cafea17d9fd18e8bca82037c45392fc9f7d1ed14e5bea49a98e55c3924c668e296cefc12a1e0804a3eefaa5782091ef9c3289b6885742f0aaa6d6214d07c229dbc8751c051e9871a354117c5259d58050bb700ab6b60d50cfbf25dc18f4dbd9129280a0916efc6209db9542bed288072e410ee2c8a09e98842bad048277a1500eb431f1df863dbb71000000000000000000000000000000000000000000000000))) else (if i<48 then (if i<47 then (0x9f6d9f508fbc326dfb8343bc70c997b2210cf0c3a7df4845e3c0fecf7820d6f154629dc18b483c918a67120d28f13faa5af7b593ececb1839dd52fcbf2b5dd7358bc0eaa47f5e952e63fa55e0875043d1ead712254b01c3a95ee8451bc310937fa392cf042259e38d4c3d70a8f77e192efa40a25e287433a716867ce190aecc0a05e782413b4fe00000000000000000000000000000000000000000000000) else (0x9b7328912f04f275e09c4639b32a07ce3d18eac5289c9965d3a722d18861584f0412c5c77d4dbc108a87223124f14728e058f53b9714a76d2054cf1bfa7dcf8152be70e9d729f54edbc026dcd7857378f0b58b5bd5702372a1cf6d553a6e6a0849d932e13e289e3794e3bef494781dd2ef3bc23df679483c4ec8b7add50af43c209de7c403ad0000000000000000000000000000000000000000000000000)) else (if i<49 then (0xbc7e1bd4cf5b8ae1b374523c0ecae8a2112ae142ade217965338eed5781f586cb3eab600794f36eeeb3781d13ee5bd2c61e715835ee0a7825d148d54027de97b55c24ee99745e54d063c249d47c52b7ceca36f5dd3107bd251d8754e3d4ec95749e128f9b8a69da6e4abc8ea8a745e51cf5bca1ddf7b42ba6fc7f74a0cf8efc29f5e2853fba90a00000000000000000000000000000000000000000000000) else (if i<50 then (0xaa805152cf0272adf84f4cb928eb17811132f4a52bdf94a603a29ed1749397ef028295e0584a3dcaaa67616130f6b0a85e0614fbd0d09a831a9470732265e76950bbce2917b9c93af2baa35ed724d3b0e699805dd22d8be221c37348be6dc8c749dd08e9bf21ddb8144ba30282766050cf041a05db80413ad028173e0100f0bf205d67f41bc0fa00000000000000000000000000000000000000000000000) else (0xc6f2481e600962fbc52a747768cc4f0509e1ec9c473c13c9e6ae851cf1d01f1d39f34399347d7be6cf0f7cda05db96433db22836d6510cea4c205f98d48bd71a826b62d22df451f9e086463e8f68f7f60518f13f1e9ef843f3e9008280e0d02f34121de17c44bbef282775e910f2b7a01e977413bafc8077e00faf5419fdde7d3fbb8fc00000000000000000000000000000000000000000000000)))))) else (if i<59 then (if i<55 then (if i<53 then (if i<52 then (0xe4f2d6a39f2a839b874a967826504e5d0a4e0ea455c4b38be7f66d5b094d269e09940bc134977824124f049259b7944b41730966aa6d3aefcda35e09c4ebd1308c7aa5d35134ca0dd997433ff388f6c65112eecb1f5e8963ebc1248479a3504fbc6209d78f40b9b1c7b7be30ecf5489d9db8c3fbc9127f79a1cfeec421ede1873e3c50c00000000000000000000000000000000000000000000000) else (0x13cfdbfad5b0864bbe11cae8522d44f0432d9e0876346714d88c2158cec42ac9fb804d38910a67821546e2402a5e07d56b98e4b07c1a56f0a3caa2027c5a3c102a279a0164d642266038350b6702a2782093ce1be24a0684473b4fa907ade11af939a41d574473dee88676dd50cebbb205e17b43bd0ee85755e904f1bda05dd7d40bbcfe00000000000000000000000000000000000000000000000)) else (if i<54 then (0x138f035ae9e0665238ad4b8759ad4ee3b42f1b86467c6ed0dc781c194f0362c6107150bc0eaaa7c5b944f5b9a961e734f368f498782095f143ea8de4775a33ee6a17e1c56af1b9a6dad7d50ba700a3715e133063e25587814539efc87711f0fef54220dce8b40bc70e7a73208f6f8401ede1803ebdd0a7e79218f8ee429f5de843fbbd0400000000000000000000000000000000000000000000000) else (0x10cf04b27de09546bc128a268a451cf048a7e28955b3c11acb90a096acbc1a860a854abe91a9778225290846a5dee884bbc11099821ed56d7bc265c479533a6f691781d94eecbc25dee7d5042afe9a80e1d28fb44255d09543bcf32827ce8104eecca35ea8e43bfd227b78a50f4f5499e9d29040bd9108376e1500ebc3201e384403d90600000000000000000000000000000000000000000000000))) else (if i<57 then (if i<56 then (0x136e9372cdd269503c0d2b27819d3ce1322ce066161378d0cc895c16eda39295be7750c04f29f785f140f03da79d97a4f3f502937861144ddc3245c4855040710867ae153cf040a4dce844f3f6f2a0831f936f03f2a61f794fc36f2a1781dd34fb3a269c67c4bbaaf88e77e1118edbfa25d87e443bef88775df90aeec020de082413b30800000000000000000000000000000000000000000000000) else (0x26de071443c0d298781b902ecbb24dc97454c18d8bb781a950dfb926dac7d4cbf0ea9a709d934f03b25de07d4f35efe96781e54edc3ba56107653c26f68a70a153cd5c0259f77d4b39b0a9d6ee1130f2c5a85b9884bb7914977ee351ae9c8255e08d493c5169172e0d14e644219dc8741bbd0a84791f908f3bf211e98042baaf800000000000000000000000000000000000000000000000)) else (if i<58 then (0x22de0643839edc85741ccecf439a19e4774a40efea4659fd32f041a5da98446bab1a8f772391eeec3a4e10874e35f0a8e6c6213b00c5229ea8250b6afe8e731f93aeabc249d67a4d3a0dea0779b944d837aa1c766503bcd8a3791a538ef37285f46c4e3d0e493791d522f6be231e77a43bdf04817961902ef40a0ddf7c403c70400000000000000000000000000000000000000000000000) else (0x1b9e08b2ebc10c7778214d0f0419f1e27f493ecfca2815c136f03ba69ce764cbc2da9c781ad2af037a65e073503c0ee95711cd4ce8bca2df27c4fb84f68b6f61928f04222df87f44427128d772152101c7236369045c231c8b7663112e543231d98646bdb12877b21118eb41215e282443c4fa8673e0502f8429f9ea8440bc10000000000000000000000000000000000000000000000000)))) else (if i<63 then (if i<61 then (if i<60 then (0x1e1f490313c1267b78220d4f0419e9e08b47be90e918222122e8c223de07e42bb10e867662506f840a2dc9854b3c1108778a013cf942219ef874cb8b0290776052ef340225e07f483a502917c6053adcc2a71e0814c382fe96725ed1cf63e245db734ab9ade8a76ded1af63ba19e075423b3008679ded0af03d205e37c403c4fe00000000000000000000000000000000000000000000000) else (0x3a3a5248278250d8fe48211e08c4ab7304986f20d28f041231e08645bc1148e7ba1906f74323df7894ebef0c867822942f042a31d7894cbf504907b1fd2cf83ca1de886483bb149175df942fc3b272057a4b39ef8907f5f112f33d20df47c41bc2f684779fd06ef411e9de8941bb914807aa14fcf1441f1e08a3f3b50c00000000000000000000000000000000000000000000000)) else (if i<62 then (0x42b96d895745b8f6f03623de06d4b3c0e09a7f9b92ae636245ca6d4a3a2ca93781ad10e83325dc361513c0dc8f781cd4adbba251e57b4d3f0f88e7d6051ce344231c6844cbc1008e75de12ce5be255cd7948bc0f88b74de904eac11f9ec853ebbefe82781d908ed3d209e47d463d6e884785fd0aed3da15e67a41bc70000000000000000000000000000000000000000000000000) else (0x827824cccf04c1ede09042bc1168779a4100e8499f5e0933c3c1207d7c644daf5491ddd28e47b950a817b20530e33f239e07c4abd6f88e71de92ae43ba3dc1774c3b8ea8579dc922f7b2235d56546394c484785b106e835209e96c3db98f2777c1d4faecba1f9e1753fba8f682795ecfee83f1f9e484413befe00000000000000000000000000000000000000000000000))) else (if i<65 then (if i<64 then (0x9472a9cfaf05b229e0b547b5f609678299250153a3da4a943c01568d782ccfcdb5ba11ebc149bf97c81782ed2af059a25fcb0483c158876eaa516f052a15f4a4463853c76752a4e8f6d61c5dba036bc1506f78688d8ee529b5d5a739bb93c6b76e74e0f94b9c9ee913cbb71a7c7be24f8f144205d382403cd0400000000000000000000000000000000000000000000000) else (0x164fd2d2f9e0525f3c0a4bb7816170f02eade0b5c58b5ababf69d6d68f02b3120a5f68330c0bb899a98f0d32ae2276f5db64e6af791f95efebaaa20d7154bc0de9e77da93eff35241d5784a402fc907a9ed20deb924daf7d483d4f68774de10cf33da09ec7b42ba4f284761f106f43ca09e28040bc50200000000000000000000000000000000000000000000000)) else (if i<66 then (0x116e4c6a3da88f47bc12e926ca4d28f04a2499a9246bc11c998b22512ec41a8a017557b90faa46a9c556dc3b299e07356b60eaac781c546f83fa62097d4bbeeea87781f510e5c321dea7d48bc8ec8a781d902f03a23de372453a8f07e79de900edb91f1eb763ebc0fc7f779fcf6efc1205e27f40bc70200000000000000000000000000000000000000000000000) else (if i<67 then (0x12f1155a75e0ad52bc158a4782b54ef055a8e1aa44d39346a18a6ad16c95aa59e0be55bc162947e6a540e0d5261e0a450bc1429c8128d4305d7251a7ac45bc13c83776751af64a20dd690433d5167f77a2ce8f6c3a01db8740bcf0e7777a28e2f1cb1c5dd8e3d3d3167d7461cf8f1c51fde58640bc30200000000000000000000000000000000000000000000000) else (0x182ca3c326037c682eafcd0781d9a325b8b19e06d5e406d6cb781b97ef032b4e39646dc78e0bc7ddcd92f0332edb96660bc0c0be7815d9cf02d2fdb45c5441ed09f7819d40f734249e06f48374f48978218f4efc1a19e37843bc2f480789f10cedbe9f9dc7a423c4e483785ed0af33f211e37e40bc30200000000000000000000000000000000000000000000000)))))))) else (if i<102 then (if i<85 then (if i<76 then (if i<72 then (if i<70 then (if i<69 then (0x311e06a66c44c4c57819582f032ac9e068533d2c8b87917146f02d2d9e05e653c0d4ae781b15cf03b281ee7e5040cf6947b5cd4edf37269f87447bc6f08576de10ee638201ef7244bbce88e759c4f8f0be9f5e97b403c0fc7b77df504efbd1ddeb7e3abb9047d765f504f5bda05e27e40bbf0200000000000000000000000000000000000000000000000) else (0x2b5e06f5735cd2a9711b54af033a65e06044bc0ca93759ccf909b7a4de06859c38c6996e59546f036a76086d4d38cf286781f928d9be235bc7d433bf007c7b5f8ecf5c31c5de7c3e3c0f27e7a9ecf0f03c9ddeb823ebb4fa777ae00f6f33e9d1d67d3b3c9027978210f8f4421f9da8240bcafe00000000000000000000000000000000000000000000000)) else (if i<71 then (0x26de0894b3e71a957ca2d16f0449e1c69036bc10885781fcd4f0441e9f48e4ac090e7d7822d1eecbf225e0804938f14837821d1ef044a25e08c42bc1227976640f6fac81b1f0943a3a1227878e24e0edc79e1e68e3cbcf127677e38eee5cb9c1d2903b3c5207c78218fef0c21fde2843fbb50400000000000000000000000000000000000000000000000) else (0x28dc078513c0fc9f7820927004021de081383c10883781e8e2f3b921de0794dbc0f8877921518f040221e0734dbc0e889799e12ef039251fc7d4aba0f0887820914ecbe1fdde7f423baea8077db8fcf037215fc6940becd88377dbd1aec369fdf17c42bcafe8176df904f1c1a09dd83403bb0600000000000000000000000000000000000000000000000))) else (if i<74 then (if i<73 then (0x4fbc0fea07ba0d24e6c0a1de07e39bc10e7c7824cc4e4459fde98b4b3c1148b70e3116dcc71e9da88473c1028074e1510f9c2241ff8e464111c897822d0af0429f5ed853c3c3086d78e1cd6edc19b5e18e363d91c7177618f2e9c39e9e07f41bcefa7e7621108f440a11e17e413cf0200000000000000000000000000000000000000000000000) else (0x4ebc138a278275250ecea11e0923cbc1188e72e30d8e145225e0874fb410496781f9310942205e089473c110847ce2d16e6bfa75e07a4cbf4f693785d512e5bfa05dd8e3dbc91c7378234dafb481e9e0863cbb90076741f4feed3e9e1de7e3fbe70281785f508f0bb205e37c413b0fa00000000000000000000000000000000000000000000000)) else (if i<75 then (0x5c308aabe781615ccaaea562161423c0b89978188eae43523ddc6e5044ac6937819936d33a225e0764ac16f28e781fd12e9bc259e06c49b6ada87781c50ef9b6239e06944396da7f759b8f8eb371fde0773c3d9087276e14f6f3c49d5e08c3fba5127d79e14f2eec51f1e0863f3b50600000000000000000000000000000000000000000000000) else (0x463ef22957826114f0489d5d3982fbc1227a7822cbcf0449f1e087413c10e787c6291cdc451f9e18946bc1108c7824900f045205c7923fbfb287774e68e4e44d9d9ec9b3a3cd3a6c7ca58d2f1c69d5e8873dbbb0e7677e2106efc2201d88143bc302817ce1d04ef41a05e182403ad0200000000000000000000000000000000000000000000000)))) else (if i<80 then (if i<78 then (if i<77 then (0xac69e8934f04d231e59737bc1408478284ccf04fa09d59e443df50817369d2f044d21a089a4a38d269d6d65112f04c249e78b493c10a907821518eb43241e080483c10e8178258eae9c79ede08f40bb7127d76a210cf644201ea8543bb910877560108f1bf209dc7f403bb0200000000000000000000000000000000000000000000000) else (0xcd8de5d66f04ca89bc90473b120a47824508f04b27de08657b80faa7781d960f03ca7de079533d6e6b0781ed40f042271c9894b38326948062122f6c423df5864b3af129675a1d06ee45225e98b44bd3048479a191ae9c0a11e384473c900867860102ef40201ea81403befe00000000000000000000000000000000000000000000000)) else (if i<79 then (0xe3781dd9721c1ac5e0844eb8d08b46264132f051a91e0a455c05429c6be895107d2a5e12ae4c35f4aaa78271470b4d29205955435b0e9b78225310643a51e0814f3f2fe9c781fd18fb40a4de679453db0c8972e051af93b21de97a46ba6f085751f500f142201db813f3c50a00000000000000000000000000000000000000000000000) else (0xd9781e59ad4b92d1e0785040ad8c38459577032eb1de05e65b3ccebd851c9990a39311ab7d5e3c0f4c58a1d178f03d2e1e075573c0f2a37b9f93cf045251d38c4e387109a7820d18ea4422de08947bc1188975e1104e8c6201e083423bf028178a0506f43e201e17e413cb0000000000000000000000000000000000000000000000000))) else (if i<82 then (if i<81 then (0xd18c2557cf046aade08745bbd18a7732292ef044291bc8758bc114ae69e297af043b01e08d5ab7304b868e0d6af0412b1e088533c11ea0702294f15c1a7e1a8851bc1089c7922526f04324dee854d3610a8c7da191afbc4209e082423c10e8176208fced411f5db8540bc2fc00000000000000000000000000000000000000000000000) else (0x194f03c2c5ef764b3c0eab0845c93cf03aaa9e0715d3c0dcb7781b186fe2fb31a3685b3c0eaba889b16cf035acdb96a5a3c0e0a9781e952dd40299c37b5340efca4781fd30e5c225de0864f3a10491771f528f0bf20ddb81453caf88279204fef2c2a05e07e3f3c50200000000000000000000000000000000000000000000000)) else (if i<83 then (0x182d24ea99bb9b453c136a17827124f052a69e0a553bc132a27e64d42f0482cdb68b553eb14a57822940f047a71e09251beb1ca27823950f046281e08a51b9d0aa2785dd36f1b8a71f4724fbc0da8d78dd522ebb9a0ddb7c42bacfc8279dfd06efc09f9dd833f3bd0400000000000000000000000000000000000000000000000) else (if i<84 then (0x1baf047301e08a523c10cbc782216d0f44af9e08e5fbc11cb47821560f040af5e07a59bc0ecae801c95cddb82b5e06c58392d8af6f98966df2f2a5ca6a53bc0d698781d916ecbd235e08145bbf0481765fd06f1439f9d282413b50c807822506f041a01e0833fbbf0400000000000000000000000000000000000000000000000) else (0x1d4f049b25e09a54c4734c37822d7ccf41b2de08b6634118b87822160f0402d9a07f5440b169f782313ad5c9a62108f4dbc122907124920e5c6a49e08a48bbf268d7ba3d08e9c7a35ee89463cf0e7f7622d12f3c69fddd8a43bbf0088781f90af1bf209de7f403bd0400000000000000000000000000000000000000000000000)))))) else (if i<93 then (if i<89 then (if i<87 then (if i<86 then (0x1f8c5323899a5e61348e6cd781c980f035355a4636bbc0d4bf781cd5ef2baad1e073593c0e6aa721d95ef9b7299cb7855b82f6a1781e138f039a6dde6c51bbcc49b7818524f62fa55d664493c0cc897a5b52af138a21e277433aaf685761f904f03f201df8040bc50400000000000000000000000000000000000000000000000) else (0x2fde0915a3c116be6ca45530949ade0083603c11cb187a3547014ba99e090523ff2a9f7825538f04d276069952bc11e98782451cf047219f487423c1087b78220e0ecc41e1ee8b3bba1127579a150af0401f9e77d403b2f882781f0fef2401fde083413c10000000000000000000000000000000000000000000000000)) else (if i<88 then (0x33de05e5f3c0b4ce86d5176d42f2e5af6566bc0cabd7818572f02fad5e05e5c3c0c0b36c9816b0e332d5e06359bc0dea8781d1370cbaa31e07c43b8b168280630eef1c4209f0873fb8f147979e1508efc11e9e5863dbab0a7d79e00fcf0bda05e27940bc2f800000000000000000000000000000000000000000000000) else (0x2b1ab9b4bb1742a17827530f04e2761da158bc1389d782652efc4c249f0934bbc120927824534f04625dfc8450bc1089b7fa2d1efdc821dc98c48bc1068d781f8fcf042221e982443c1007d77e050af4431fdd5873fbab0e7c78214f0f1469e5e28d3e3c51200000000000000000000000000000000000000000000000))) else (if i<91 then (if i<90 then (0x319e0845bbc116bd7822166f0442f5e08d6636912b57822d5cd7cc291c39a533c134a26ee454b0ac6a69ce89523ecfca5782013cf044a49e08b49ba9128a76e3d02f045225d18f43bcd027d781fd14fa3ca15da7342bb2de8078dd908f03d215e479423c8f800000000000000000000000000000000000000000000000) else (0x325f35b60bc0b0c486d9974f031325e06a6a45adabf781c58b02372f5e0725fb9adeb2781e562f03c289e07e50bc106a47820d4cf042a71ca884dbc1289878a3914ee4725dc78f43bb32a7b78e5104e2c59dde08d39bbf207576230faec449f5e1863fbbf0400000000000000000000000000000000000000000000000)) else (if i<92 then (0x4c3c126a97825536f0462c9e08a603211caf8865964f04aab9b39656bc138aa7828d5106d127dce9d51bc12aa66d64954f047a8dda915740d14a583a3d2ef04829604884dbef108e77a1918edc920de58d413bf0a8077e0d0aef3ea09de7f403c50200000000000000000000000000000000000000000000000) else (0x553ab0ebd782154cfbc12ede07f66c5b02c46662d8cccc830de088643c118cc7820992f045aede0845bbcd06b77821970cfc12cde0785bc32f2b3839dd4cf03aab1e072513c0f693781e53ae63a23de07b433c7068277e0902f141201df81403c50400000000000000000000000000000000000000000000000)))) else (if i<97 then (if i<95 then (if i<94 then (0x583c136c187e314edf47ae5a68e66bc104ce78201aaf03d32a047d69c68fccd8a1f5a6f03eaf989845cbc118bc78231730844aa9e08c57b6314a97822d34ff45a75cb8d4e3eb068b781f920f140a25d983443bcfe837821d04f5c1201e08440bbb0200000000000000000000000000000000000000000000000) else (0x65442dacc781bd6af03ab1a1d79673c0e6cd885f19cf03eb19e07b68368dac9685ad9ef034305e06c6233ad8c77819d82d8322d604655c3fcc8b38197148e9b1aa5e0684f3a4ce8876dc120f1b722dda72433baf68976de906f03ea0de17f40bc30600000000000000000000000000000000000000000000000)) else (if i<96 then (0x5b3c138ba68a8952f04caf9e09a603c120c86865d94f04cb02349a5e43d2eb37824d6ccaca2b1948a57bc120ad872354904c7a65e0954dbc11e8e782450cf9c9241e0954239f2c7778258fae54a1f1f38d403a512827b1fcfef33fa05e07d41bc0f800000000000000000000000000000000000000000000000) else (0x68bc09edb7813182e4a9b5de05367bc0b0de78131c4f027365e056693c0b6c56f9819313b42d5e0685f362d8b9781b564f03aab60b6e54bc0ea9e721d92ef038291b76b4cbc0dc8c781cd20e93aa21e776443a4f080785ecfaf13e1f5e2803f3c10200000000000000000000000000000000000000000000000))) else (if i<99 then (if i<98 then (0x4fc0308a67823526f0462a5e08853368fca9781fd5ed8402b9e07e5637712a47822160f043271e09054c1b28a57824d4cf043269e08a4eb82f8937820d0ce7bfa39e082433dd187e7b21d08f0431f5e0873fbbf147a75e2cf0f3c61f1e18a3f3c10c00000000000000000000000000000000000000000000000) else (0xb2782113cf03f2c2087951bc0e6a7781d55cf03baade0765a3c0eeab7e9b96af8b3aade0695e3c0d0b76cdcd56f040a8de0834c3731c956f21d08f04623dfb8248bdefa847c5fd12f43da0de081443c100847920106ee3e215df7641bc6f600000000000000000000000000000000000000000000000)) else (if i<100 then (0xb56ae3936f04c2a1e08e4abf1289b7824548f042281e07f553c104987121d36f04724dfa8d51c050aa989df956f040a95e08152bc0fe9b7d5f51ee6bea41c87446bbcec8276ddd06efbfa0de27e43bccfc8378a08fcf0c19e9dc873ebb70a00000000000000000000000000000000000000000000000) else (if i<101 then (0xc27820d64d346ad5e087543c118ab782114ef042279e07f55bc0f89e7820550d5c2a7db98553bc106a67822156dd3c295bf7d51bc0fe977821116f7c320de08c413c116787963902f044201e586423c104847820900f2c1a01e08340bbb0200000000000000000000000000000000000000000000000) else (0xc47820d7cf0432ee2e8759bc102ae8721554f0482720495533c1209e8422559103f28de08154c34f8ad68dbd44f037a85f17150bc0de9a781a920f038239f470463a8dc85775b910f036215da7842bd102857821904eec2a09e48040bbf0200000000000000000000000000000000000000000000000))))))) else (if i<119 then (if i<110 then (if i<106 then (if i<104 then (if i<103 then (0xc678215871ac3b05e07f59c310ab266e1572f03f2c1e07b5ab50fea6781e952f03ea8dc87c523c0f29b7822520f049245c39047bc11a837fa3cfefa481f5e5873cbc0f272781dce6f03d1f1e07042bbae68a79ddd0cf03d205e07c40bc0fc00000000000000000000000000000000000000000000000) else (0xca61e3992f04bafde0945bbc130b6782616cd4cdaa9e09e59bc13a9f782994ad452a79e09f4e43f42a36f63d430948281fe894dc151691782291cf8c5a0dc69438bc13e6875694d8ebcf1ade39c3bbdb2e807a624fef0429f1df883f3c90800000000000000000000000000000000000000000000000)) else (if i<105 then (0x1bef047b498498673c130cd78255a129cf31de09667bc124c47823592f0462f237845e3c10ab18761d60c7412a1e08452b451a9a84a4930f049259e08e47bbd108c7820512f040219d87b46bdcf28875a0506f1c2a0de18040bc10400000000000000000000000000000000000000000000000) else (0x1daf023ba5e04872bc098e16d92ddaf024371e051703c0acd078175a8f02bafdbc57603c0c0b7781b162f0392ade07558bf8f6ab781ed52f03da8dd07a4b3c0e68c759c110f039201e07e42be0e68877de50ef23b209db7e413c30200000000000000000000000000000000000000000000000))) else (if i<108 then (if i<107 then (0x16716cdac1e0975843f30ab7825968da4cab1e0995abc13eac8ca8154f052255e0a24fbc140a283e89450b51a7de09a55b5524a57823946ddc3271e085443c1107b7622cf2f2411f5e07c3bbc5148078a14f8f0429fde082413bcfc00000000000000000000000000000000000000000000000) else (0x19af02c319e06063bc0c6c07819998fe32312135e69bc0accb781699af030ad9fd605f3c0b8c37815d88f0292e1e0535e3c0a8b27814150e92ea81ca6147bbad48576dc4f4f7bc9e1e07b403c0f884781fd00efc0201df833fbc10400000000000000000000000000000000000000000000000)) else (if i<109 then (0x148f04c295bd9c54b2f32a5782515ef049a85bf8b543c120a4782355af048255e0984cb8726998263d2b01ce229c68f47bc12c817826108f04a201e09c3c3c1307579258e4eecc9c9e6953dbe714827ae30feedc5a09de82403bf0400000000000000000000000000000000000000000000000) else (0x176f03f301e07c60bc106b864e0982f03faade0855bb5cfcb0781ed78d63d2b1e07855c32fca7781e560cdb9a61e07e523c0f0986aded2ef1be26df97d47c00fe8a781f114f03e219e07b423c2fa8d769d912eebca0ddd7d40bbd0000000000000000000000000000000000000000000000000)))) else (if i<114 then (if i<112 then (if i<111 then (0x17119c12ede08561bc10ab9782117ef0412be0d7f5a430f6aa781e96af04028de087543c1069f7822144f043a55e0854dbc104928061124f04225de08346b8b1085792250af441a01e07f403c8f482781fd02edc09fde080403c0fe00000000000000000000000000000000000000000000000) else (0x172f048afde09163bc126bc7826980f0512b59da7573c150a37829568f04daa5e0a1553c134a685a5550e2c9a65e08d4e3eb0e956ea312af03fa65eb784a3c0f68d7a5f90ef0401f9da873cbc516807961102f3c11f9e1863f3c10c00000000000000000000000000000000000000000000000)) else (if i<113 then (0x192ceb633da6706cb5edad58bdc5c2f03cb4de0826ab3f12c7782019cf03f325e07b61c3d02ba781fd74f03c295ef7d513c108a08221d26f045a41c286473e3068a76e110ce841211dc7c41bc6fc83781f504ef3ea0ddd7e41bbaf800000000000000000000000000000000000000000000000) else (0x2f9fa5f62bc0ccc57819db2ceb0351e0626ec22c0c6831b196f033b0dff6561b54e4b8781cd62f03ba85c07d52bc108a6782193b0343a55fa90483c11a8d782390ef0481fde48f403c11a7f77e1cfcf044201dc823f3c10800000000000000000000000000000000000000000000000))) else (if i<116 then (if i<115 then (0x271e098553c12eab782517107c82d5e08a5e3c124b16ea3162f04529de08a5a44918aa7823d4ee745276028f543c110ab7822146f044291e07a4e3d6f69a7b5e92cf041a35e080463baf68576a090af1c0205e08540bc10200000000000000000000000000000000000000000000000) else (0x2cde094603c112be781f98ef03f2f9e07866bc0e6bc781dd74d739ac1e0735fbc0c8b87818160f0312ade05b57b8eb0b278175550033275e06d4b3c4e293781bd30ef36231df75433c0ee8676ded08f3bca15df7b40bc70000000000000000000000000000000000000000000000000)) else (if i<117 then (0x319e07b643c0f0bb835f188f03aad5e06a5fbc0dab27bdbd590439289e072513c0ea97739e922f03ea15e07e433d4fa8e782091ef03fa25e077433c0f081781f106f3bda01e1793e3aafa807a1e4f8f03f9fde07f403c10200000000000000000000000000000000000000000000000) else (if i<118 then (0x301e09d5faeb48b67826d70f04c27a1e9e55bc140a0782893af05324de09f4b37934907fe6d1ae3c8a09f993413c1368f782451af0491fde08e3ebad107c78208faf5bf9e1e0853c3c1107878238f4ef429f5d786403c50200000000000000000000000000000000000000000000000) else (0x371e04f713c0a6d0781659f05aeaede05b653c0b4c16456584f02eac5e06657bc0d4aa781b13af03aa51d5734e374c89f745913cf037231da70423c0e07d781c8f6eec19f1df7d3fbc0fa85771d4fcf13ea09e17d403befe00000000000000000000000000000000000000000000000)))))) else (if i<128 then (if i<123 then (if i<121 then (if i<120 then (0x2a9e09d5a43f4ca87829556f053255c5a651b4b4099782853ce4d0a59e09f4c3c12c957825922f04ba19e0943fbc124827825116f0491ede08e39bd7186e7822cfaf0421e1e0853dbc1187978220f4f5409f9e07f3f3c0fe00000000000000000000000000000000000000000000000) else (0x319e0476cbc082cc78119a0f0282e9e058613c0acb9781417d0b292d20b5856bc0baaa819854ef030265e064483d0d295781a538e835a21e0783f3c0f8787aa0500f33f1f1e085433bd028078210f4f0459f1dd893e3c70e00000000000000000000000000000000000000000000000)) else (if i<122 then (0x231e56a4cbc0d6917e5893ef032a45e0664bbead088781b51ef03422ddb7144bc0e28a781ad0cf0381f1e5733c3aee67d781c50cf23b1fde0703cbc0e478781ccfaf33b201e27c433c10083785f508efbf211df7c413c2fe00000000000000000000000000000000000000000000000) else (0x41bc12c7275e6d06f04e1d9e09d3f3c1267478238ecf0499ede0913cbc1127475624eaee431b9e08b353c1086d701e0f6fb3b1b9e07d353b0f06a781f4e4f03c9edd27742bc0ee7f769e502f13d9fde280403c30400000000000000000000000000000000000000000000000))) else (if i<125 then (if i<124 then (0x4c3c0f08c7820d3d00bfa49c07e483c100817820d10f03ca2de06a40bdaec7c7b208f4ee459e1df8d36bc10c6477e50e0f04a1a9e09730bc132667625cd4e8cc9c5dd923dbad147778e30f6ee439f9dd8340bbcfe00000000000000000000000000000000000000000000000) else (0x47bc0fe8e781d138f03923de07547bc0f48378df100f0419d1c1843b3c1067d781f108f03ba11e06e393cef477781c506eeb7a01cf7c3cbaafc7c7a1d104edb9209e073423bef88277de102f0bc201e07a3fbc6f800000000000000000000000000000000000000000000000)) else (if i<126 then (0x46bc0de81781b11af036a0de0734440ef27e781f104f03b1dddd793c3c0fe78765f8f4f03a9c5e07435bc0e06773dd8e2f0399edf9663b3c2d26f781a4e6f4389d1e0713fbbcec79791f8f0f0401e5e0893d3c10e00000000000000000000000000000000000000000000000) else (if i<127 then (0x3dbc1926c78308f2e85e1d5e0bb403c16479796c0eef0539bde0a23b3c13e7578280dcf34c991eaa52d3c1525c782acc6f055981e6ae2f39950577828cc6f049991ce943a3c10c767be1ceef441205dc7a403bcfc00000000000000000000000000000000000000000000000) else (0x61b3710ad7822968f046abdb18958bc114a8781f13aea40a41e08c4a3c11294782050cf044221e080413c2fa8679e011af03e235e07942bc0fe7974214eaf0409ddd8803cbaf167c76614f0f0441e9e0893ebc10800000000000000000000000000000000000000000000000))))) else (if i<132 then (if i<130 then (if i<129 then (0x653c0b0b67818180f02eadde0615d3c0c0a3781d93af5c0a6de0824e3c10c94782211aec4121de08c3f3c1188576e2510f040215d68441bc1087d78214eaf0c29d9e08341bc5048078204fef03e209e27d403c4fc00000000000000000000000000000000000000000000000) else (0x50c051e957823538f041a5de07b4cbc10098781f13af03ca71e07550bc0ec9b781cd1cf23d249e07a44bc0fe8d782110ee943221e086433c10c81775ccf2f03f1e1e37a423c0ee80781f0f4ee411f9e0803ebbd0600000000000000000000000000000000000000000000000)) else (if i<131 then (0xa1782613cdc4d245ec954c401169378a192af046a41e0914b3c1088d7820d0ef042a2de08943bc50c907821d18f042235e07f45bb50e737c240ecf0459c5e28a3d3c1167b78218f6f2c39f5dd863fbc10400000000000000000000000000000000000000000000000) else (0xb87cd596ef02da95e063513c0ce987819542f032a81e05e4cbb0ca8f781a916e93924de06f463c0dc96795c11ef03822de07048bc0ce82781ad00f0399e9df73423baee80781e902f2bc209dd7d403c2fe00000000000000000000000000000000000000000000000))) else (if i<134 then (if i<133 then (0x8d781bd22f039a1de06d443c0ee7c781dd0aecb71f5cb763ebcf10787b220f8f044a05e08b3cbc11a8578228fcf0479e9e0893bba91a6c7863ce4ed461b1e0853d3c1087978218f0f0431f9e5823f3c10400000000000000000000000000000000000000000000000) else (0x7b7867506f04c1cde0a13f3c124727824ce4f0489c9f496423c11a7f7823908f04ba2dd48b42bc10e8e7823d18f046209e09041bc11c7a78224faf0431c1e0893ebc10a7e78e10faf1c21fde1833fbc30600000000000000000000000000000000000000000000000)) else (if i<135 then (0x97782ad34f057a4de0a147bc13c847828104f052a1de09c483c1328c7826934f047a55e09445bc11c9c6f6192efbc3245f087483c116827465104ec471e1df8e40bcb0a8177a1500f042a05e08540bc10600000000000000000000000000000000000000000000000) else (if i<136 then (0xc17817590f02eacdef65563c0d8a3741b54cf035289e06954388d4a5781a150f033aa1e0664c3c4cea1781b138e4b925de0724d3c0e695781a91ef039215dc6b42ba6dc85781c108ec39a15e17541bc0f200000000000000000000000000000000000000000000000) else (0x9d7817d48e4ae25de06c4bbc0e28f781cd1ef039a29e06d48bccda8c781b91cf03b235e3763f3c8f48c781d91af03f221e07d463c10a7e7823100efc61bde08f393d3227478634eced441e5e7863dbc10a00000000000000000000000000000000000000000000000))))))))) else (if i<205 then (if i<171 then (if i<154 then (if i<145 then (if i<141 then (if i<139 then (if i<138 then (0x7b781d8fee6bc209e07343bc0e881781c902ef3b9d9e07b3ebc0f279781d506f03da09e0823bbc0ec81781d514fe3ca11e079483c0e489751c516f03b1f5e079413c8ec8078218faf0421f9e1843fbbd0600000000000000000000000000000000000000000000000) else (0x7078298ecf04f1d1e0933d3951e727ae48eef0451c1e3843abc10c6d78204faf03b20dd972363c0e675761c104f0361f1e07340bd4f2797820500eac41d5e4823bbc1028577ddd00f0bf205e77e40bbd0000000000000000000000000000000000000000000000000)) else (if i<140 then (0x957197126f034219e069443c0de83781c500f03d9cde07d3d3c0f86d781e8e4e6c31d1e08a2f3c1146478230daf0449b9dc8c3cbc11479782550ef0471d9e08e3bbbd187b78228faf0421f9e080403c10000000000000000000000000000000000000000000000000) else (0xf4f0591b9e0b43b3c16873782b4f4f0561bde0ab3abc14c667a688eef04b9f5da9533baf326f78260eaecc59e5e38d413b2fe8d7b9f928f04220de086413c110847822100eec59f5e18a3fbc10a00000000000000000000000000000000000000000000000))) else (if i<143 then (if i<142 then (0x156f038a86016d54bc0d09f781cd4adbbb265e0754d3c0f287782091af041a45e08a3fbc10686781e0fee943215e082403c10a8a761e12ee7bba21f17844bc2f68b781f114f03d219e07c41bc2fc00000000000000000000000000000000000000000000000) else (0x136f03ca35e07a483c0f891781c134f038235e077493c0fa88782011ef041269f98040bb90a7d7822508f03da19e87d423daf881765f51af3c39fddb8141bc0f886781d906ee3ca05e180403bb0800000000000000000000000000000000000000000000000)) else (if i<144 then (0x126f04d219da9a45b712c808066112f04e20dc999473c11c877821d20f045265e08942bc1068577604fcf03f209e07e3fbc0fe7d7820126f03e1fde0813f3c2fe7b75210f6ee41201e07f41bbef600000000000000000000000000000000000000000000000) else (0x158f05927de0b6503c16097782c948f05626de09c4db993c8d7826532f047a85e08b43be9208578238f6efc71fde0893ebc10c7c7820d1cf7c11fde0893e3c10e7e7821cf8f0429f9e2863ebc10c00000000000000000000000000000000000000000000000)))) else (if i<149 then (if i<147 then (if i<146 then (0x1baf025351e04767c06a6c8781399ef028ad9e05e5c3e2c0a56d9954ef034aade0744b3c0e092759b910f037a1dd47d413c0f07e781f91ef03e21deb7f413c704847820900f042a0de07e413bafc00000000000000000000000000000000000000000000000) else (0x14cf04aa69e09950bc122957824d3ee34b24e09944bbc1248977a291ef043279e08542bb30e7f78234ecf04820dee8a3cbc10a7b79a0914f043215e07e41bc0f8857820908f0be201e57f3fbc10400000000000000000000000000000000000000000000000)) else (if i<148 then (0x174db3eac9e07d58bc0faa77820968f03f299e077543c0e692781ed2900bea89e08345bc10e8b782190af03e231e07d3ebc1007c782051efbc0209e0823f3c10e8675a08fef0431f9e282403bf0200000000000000000000000000000000000000000000000) else (0x16cf03aab9e07656bc0f6a8781dd62f039a71e07c4d3c0f48c781cd20f03aa91e06648bc0d690749c900edbc221e07b3e3c0f87c781e11cf03b20de082423c0fc87765f108edbf1fde083403cb0400000000000000000000000000000000000000000000000))) else (if i<151 then (if i<150 then (0x154f03228de06a53bc0d89e7d9a946f035a5de06749bc0ca7e781a508f1b6a25e0703dbc0f281781e0eef03f209d1833bbab0e7379e0d06f044a11db7f40bcb0082781fd02f040a05df7f40bc0fa00000000000000000000000000000000000000000000000) else (0x11af9d0231e097493c12687782511af0509f5e0a73bbd746667826ce0f04f9e1e2a339bc13e7878284e8f04ca11e08b3ebc110757822916efc1a09e085403c116807663102f0471fddf893ebc11200000000000000000000000000000000000000000000000)) else (if i<152 then (0x158f031a89e05c523c0c69a73d9d5af02ea8de0644cbc0ea80781f51cf03c269e07848bc0ec98801dd18edbd239e07f423c10c7e781ed1af03ba19e37c453c0f68b781fd1cf03da1de07f42bc0f600000000000000000000000000000000000000000000000) else (if i<153 then (0x11cf04a1f5e098433c12c807823912eb46219e88846bc1107c782090af6c3a45e081433c10e8e73e090af042231e08144bc0fc787821106f040a05e07f423c10089771e910f03ea15df7b3fbc10200000000000000000000000000000000000000000000000) else (0x142f03e251e67b4dbc0ec8d781c128f03ba35e0784a3c0d27d781b916f2b7a45e070463c0ec8f781e510f039231de74433c0fc7b781ed06eec01fde07e41bb500827860508f23e9fde4813fbbd0400000000000000000000000000000000000000000000000)))))) else (if i<162 then (if i<158 then (if i<156 then (if i<155 then (0x138f050239e0a3483c1467c782a114f554a11e0a13e3c1406a79294f2f053201e09d40bc1368778234f2f0471fde09341ba916757820104f23e1f1e17f413c108827821500f0421fde584403c10000000000000000000000000000000000000000000000000) else (0x176f03aac1a971593c0f8a3781f564f03b291e0744dbc0f88e781e93cf03ca71e0744db84f0937fa090cf047a45e09346c052c7479658faf0479e9e08b42bc0fe86781f106f03f209e07e3fbc10200000000000000000000000000000000000000000000000)) else (if i<157 then (0x15f13ca281e09856b853a9f782654ef04c25de09c4b3e92a877b24d2cf04ca3de099493c12c947822d28f041a8ded77513c0f6897820116f03c211e07841bbef08177df500f0409fde2803fbc10000000000000000000000000000000000000000000000000) else (0x184f03a2dde07564bc0deb7781c57cf036ac9e071553c0dc99781bd5cf03929de07153bc0c49e781812cf02fa65e05d4e3c0d08877dcd04f03b9edda803d3c10e7d7821900efbf1f9dc853f3c10800000000000000000000000000000000000000000000000))) else (if i<160 then (if i<159 then (0x16af0492ade08f5bc1918a77823554f046289e28b4bbc11487781f93ef03ea5de07c443c0fe7d781f8e8edc29d5e08641ba1127a76210f0f0429e9e081403cb028278204faf044209e07d40bc0fe00000000000000000000000000000000000000000000000) else (0x18cf0402e5e078613c106b3782156af0422b1e088503c11a847825d36f050a4a16a7433c1507a782bcf0eecf1e9e09a45bc1227d78220f8f0431e9e084403c10c827820d08f23f9f9e0823fbc10800000000000000000000000000000000000000000000000)) else (if i<161 then (0x18af04aac1e09c623c12cb77826d70f04eacd999956349249a7824576f0422e1e07656bc0e4a8781cd2af03924de07a4dbc0e884781e902efc39f5e38a42bc10c8478a0904f0421fdde85413c50200000000000000000000000000000000000000000000000) else (0x1b2cf36b2de06f6cbc0d8d178199a8f035b2de0765ebc0ecaa829c97cf0362b5d47a4f3c0fc9a781fd0cf042a31e0834739f007d792110ef03da19e073453acf0857a1e50af03da0de07d413c4fc00000000000000000000000000000000000000000000000)))) else (if i<166 then (if i<164 then (if i<163 then (0x2e5bf77623c0feb682a1d7cf046b01e081593c1109b78219530046299e08e4dbc110987821514f049239e08346bd708807820902f0419e1e68740bc1127d77630fef0439fde0873fbbf0a00000000000000000000000000000000000000000000000) else (0x2bde08e613c106bc781fd94f03b301e0805cbc0f4a0781f568f03cacde079513c10e9c7822d36e842a41e984483c10e81781f506ea411f9d87e44bcaf688781f10af240215e37941bc0fc00000000000000000000000000000000000000000000000)) else (if i<165 then (0x2f1e05f623c0b8ba721597ef02a2fde059593c0ba9c7815d58f0adaade865543b4c6a6789993ef035a4ddd704b3c0e27d781f508f03e9ede08441bc106837820108f0be9f5e082403c2fc00000000000000000000000000000000000000000000000) else (0x269e07d4fc4b0c8f7821924d547a5de080473c10672782010cf03da3de079453c0f88b781c512f035209e070433c0e279781d100f0379f9e07142bc6ec82781dd00f03f1f9e0813ebc10600000000000000000000000000000000000000000000000))) else (if i<168 then (if i<167 then (0x259e0a6523c13e94782a540f04ca59e09b483833a717827d00f04ea1dbf9542bdd3c7b78270e4eecc9c5e0993b3e1286c7825cdcf04b9b9e08e3d3c1107878a0cfaf0421f9df843fbbb0800000000000000000000000000000000000000000000000) else (0x2ee0c7f613c0f0bc781d57106b7ac1e079563c0ee8f781d538f03826de073513c0e896781e514e942225e08444bc10c827821108f0441ede08640bc1087a7821d00f0c3205e084413c10400000000000000000000000000000000000000000000000)) else (if i<169 then (0x2e5e0715cbc0e0b0781c94cf03daa1e078513c0f283781f916f03e235e0734abc0de8e781991af036a31e171473c0e485769a916f035201e57c423caf880781f90af03f211df7c41bc0fa00000000000000000000000000000000000000000000000) else (if i<170 then (0x2a5e09d543c148a17829940f051a7de0a14d3c13c80782890ce74d9fde09f41b9d3a7378298f2f04f9f1e09a3fbc1226e78270e8f04f9ede08f3fbc1107d78e1104f0421fde0863fbc10c00000000000000000000000000000000000000000000000) else (0x315e06765b4cd4c6781a184f032afde0695bbc0d2a1781a540f031a75e0594fbc0b298781812ef6ae255e06147bdebc897819924e833225e068433c0d880765e50af03ca11e67e423bef800000000000000000000000000000000000000000000000))))))) else (if i<188 then (if i<179 then (if i<175 then (if i<173 then (if i<172 then (0x2ade0805a3c108ad782454cf04aa9de0984fbc136897326104f04d9d5e0983bbd532777824ce4f04c1d5c89d363c1306e7824ceef0499c1ea9138bbd247878244faf045a05e0853fbb90600000000000000000000000000000000000000000000000) else (0x2a9e0815bbc0fabd6adc974f03eafa14795cb6cd8a0781bd38f039a31e07747bc0f289781e112f03ca45e07641bc0f080781f512efbb201e079413c0ee88781cd0ef03aa15e27740bc6f800000000000000000000000000000000000000000000000)) else (if i<174 then (0x2a9e07a59bc0eaae781f16cf03e2d9e083523c10a8e782191cf042209e08343bc0ea80781e102f03a219e87a3d3c0e47c781c8fcef3c1e1e07b3c3c0fc7a7920cf6f2419ede0863e3c10a00000000000000000000000000000000000000000000000) else (0x28de08e53bc11ca97823562f03fae19e74543c0f093781d522f03da11e0803dbc10c7779600e8f03c1fde07f35bad026d78a14eaf0421c9e0813abc3187c7820cfaf041201e083403c10400000000000000000000000000000000000000000000000))) else (if i<177 then (if i<176 then (0x2c1e0805a3c10cb5781dd5f12baaade07b4fbf6f4877821116f04620e058e403c1407678270d6f04f1f5e0a835bc1407178638f0f2c89c9e08d403c1107e7821cfcf1c1209e07d40bc10000000000000000000000000000000000000000000000000) else (0x2bde09c5cbc124ab7824546f04c295e0994c3c1208a782392ce146a41e0894fbc106917460110f042a91c182453c10a7e7821d10f0421f9e08543bc10484781ecfef03e9f9db81403c2fe00000000000000000000000000000000000000000000000)) else (if i<178 then (0x329e080653c0f4bb8b20174f03f2f5e07153bc0e897781e944f03d261bb7c50bc0ea90781d518f039a95e06e473c0ee84781fd16f041a09e08c443ab0a7e7821cf6f0439f9de843f3c10400000000000000000000000000000000000000000000000) else (0x325e06c61bc0deba781b96ef033ab5e0724d3c0ea9073dcd36f03f24de0844abc1128478260fcf04aa49e090423c11c8276a051af040235d67a463c100847ae0d02f2c1a05e0813fbc10400000000000000000000000000000000000000000000000)))) else (if i<183 then (if i<181 then (if i<180 then (0x2d1e08a58bc110a7782393af04aa79e093473c120827825530f046259e08a4ebc1169b7de0124f03d285e07448bc0de82781d918f03c219e07245bcede86781cd06f03da05de7d403bd0600000000000000000000000000000000000000000000000) else (0x2f5e0a85c3c144b47828962f04eac1e0994ebc1309678249470c4b27de08a53b6b109a7824916fd44251e08d3fbc122777823906f0459dde08f3cbb9167878220faefc29f5e084413bcf800000000000000000000000000000000000000000000000)) else (if i<182 then (0x391e0926cbc134d57826d9ac9cf321e09d5a3c14ca77827d70f04aaa1e09c573c132ab6ee7124f048a81e08f47b972484782611af047215d98c41bc1167f7823902f043a01e0843ebc50c00000000000000000000000000000000000000000000000) else (0x3d5e04e793c0b6ef78189d4f030b9198616cbc0b6c57819598f03130de0646342ed2c67817d44f033ab9e06c503c0da9b741a534f038241eb7446bc0f88c781ed0ef03fa0de080413c10000000000000000000000000000000000000000000000000))) else (if i<185 then (if i<184 then (0x309e092663c126d07825d94f049311e09059bc120a97822d5af044299ba84573c100a47822110f046265e085463dcfc837a5f512f03ea0de07e443c0f4867a5dd0af03aa09e07f40bc50400000000000000000000000000000000000000000000000) else (0x34de0686f3c0cee67818db6f036b4de074613c0eab3781d168f036aa5e07056bc0d8ab781cd26f03ca75e07c44bc1067f782190aeb43a01de8740bc1147c78228f2f044a01de83413bf0200000000000000000000000000000000000000000000000)) else (if i<186 then (0x2e9e098623c128c8782518ef046b19e08c5b3c11ca66ba3d40f046261e08e4c3c1349d7826d16f04ba61e09045bc128847823116f042219e085453c0fe857820902f341209e07d413bcfc00000000000000000000000000000000000000000000000) else (if i<187 then (0x345e0796bbc0e4db781bda6f038345e07261bc0e6b4781b556f03b295e07a58bc0f2b7781c942f03da9dbf7a4f3c0f68f782151cf042a29e088443cd108678a1904f0409f9e0853fbc10400000000000000000000000000000000000000000000000) else (0x325e08f643c11ec97824184f04bb09e0995ab1738a08725540fec9279e08b54bc10ea87822936f040281e07c4c3c0f893761c524f03aa45e07247bc0e08b781e104f03ea09e080403bd0200000000000000000000000000000000000000000000000)))))) else (if i<196 then (if i<192 then (if i<190 then (if i<189 then (0x35d858d6b3c10ed8781edb0f03c36a357d683c0f4b4781ed62f03d2a1e07257bc0dab1781a934f035a6de06d49bd6d283781c90cf03b209e07c3f3c1068279a00fcf043a05e086403c70400000000000000000000000000000000000000000000000) else (0x6e3c0d4d2781c99ef03eb59e07d64bc104ae7822954f045a65e0944dc0d189a7824108f04a21de08c3dbc11a7478224f6f0431f5e082403bd02817821508f03ea19e07b40bc10600000000000000000000000000000000000000000000000)) else (if i<191 then (0x62bc11ac37824196f042b49e0856547716b77822568f045ab1b186533c112a9782212ef044249e08743bc1107c7821500efc39f9e086403c10e857821100f1c1a01e08241bc30200000000000000000000000000000000000000000000000) else (0x68bc118d2782119ef044b59e0876a3c100bf7822d7cf044ac5e08a573c11ab0892213d0945a61e08d4738b1c80782610cf047a0de091433c118887820504efc1a05e08041bc0f600000000000000000000000000000000000000000000000))) else (if i<194 then (if i<193 then (0x6e486f0d5781d9aef038371e07c69bc10cc9781fd8cf040ae9e07f5d3c0f0b7781f150f03ea91e07b4dbc108977be0128ea40a4de07c48bc10088765f908f041201e0843ebc10c00000000000000000000000000000000000000000000000) else (0x69bc0ecca781c18cf03735de0696c3c0c4c77819d8cf0372e1e07258bc0fab2739f948e63fa79e07b4f40af496781f128f03ea39db74483c0ec85782010af03d20dd97f413befe00000000000000000000000000000000000000000000000)) else (if i<195 then (0x643c0f0b9781f166f03e2fde0795cbc0f2ad7821966fec1aa5e08c56bc108af781dd44f03ba61e06f4bbc0e091781c520f039205e07342bc0ee8478204fcf041a05e084403c10600000000000000000000000000000000000000000000000) else (0x5fbc11eb4782415cf0492dde09458bc12eb27824d6af0432d216835841cfca57823130f045219e088433c106817820102efbf9cde0863dbc10484771f900f0bfa11e07c413c0fc00000000000000000000000000000000000000000000000)))) else (if i<200 then (if i<198 then (if i<197 then (0x66bc0cac3781c97ef035b29e06963bc0d2c4781b174f038ad9e07856bc0eab0781b142f03f235e085443b5188078614fef0451e1e08a3e3c10a8178210fcf0401fde0813fbc10800000000000000000000000000000000000000000000000) else (0x58bc126b47824152f0472c9e08757bc0faaf781cd54debb2b5e07e50bc1069b781f53cfc3f245d38049bc0ee847820110f03b205e073403c0f08478df4faf0411fde080413c0f800000000000000000000000000000000000000000000000)) else (if i<199 then (0x61bc122c3782396cf0462e1e08e55bc12aa1782553ef047aa9e08451bc10697781d936f038a41e07444bc0e283781ccfaf03c1cde0803bbcb0280781f4fcf03f9f9e2803ebc10600000000000000000000000000000000000000000000000) else (0x69b251cd05fa4182f045315e08c5fc5518b57823d5af04aab5e09452bc1388c7825516eacd20dfb953cbc126757822ce8f0479c9e08e3bbc10e7c7821cf8f2439f5e0873fbc10a00000000000000000000000000000000000000000000000))) else (if i<202 then (if i<201 then (0xdf7824994f048b41e090653c110c3781fd82f03c301e07e6037cf6a0739f148f03e25de08045bc1027f7820504f1c11fde97c3ebc3028277e0504f03ea0ddd7b41bc0fc00000000000000000000000000000000000000000000000) else (0xf07813db4f02637de04b68bc094c16a54570f02e2f5e0655d3c0c49b781bd3ef03c259e07945bc0f47f7821106f0439e9d38a3ebbb0e827821cfcf1c41f5e085403c50200000000000000000000000000000000000000000000000)) else (if i<203 then (0xbe782b14af058aa5e0a74d3c158917829526f04fa8611944dbc12289782492cf046a39e08b423c112827821512f04320de08041bc0fc88781fd0af040205dc80403c10200000000000000000000000000000000000000000000000) else (if i<204 then (0xe9781bdab0f38b3de07c62bc0f2b5781cd62f0382d1e06c55bc0e09a781b144f035261e06c463c0d486781c91cf03b209e07b403c0fe86781f108f041201e083403c30600000000000000000000000000000000000000000000000) else (0xd7782218af042b29e0825ebc110a781a4540f04827de0904d3c12a857826516f04820de78c3abc120777822906f0459f1e1863f3c10e817961d0af040209e07f413c2fa00000000000000000000000000000000000000000000000)))))))) else (if i<239 then (if i<222 then (if i<213 then (if i<209 then (if i<207 then (if i<206 then (0xde7813d92f02b32de0576233ab6b7781b55ef038ab9e06e573c0d89d781b534f033239e06e423c0dc807a9b91af335205e070423c0ea87781ed08efbd201df7f3f3c10400000000000000000000000000000000000000000000000) else (0xac8ceb93cf057a85e0ad4f3c152a3782653ef046a6de0904cbc12c8978250fef0519ede0a038bc13c6d79260ecf04a1c1e08a3c3c10e8178210faf0419f9e0853fbc30800000000000000000000000000000000000000000000000)) else (if i<208 then (0xd97820d98f043b35e081633c10ebb7822156f044aa9e08a573c10a9c7360142f03ba69e075473ccea84781e512f03c9e5e07f3f3c10484781f0fef03e209e27f413c0fe00000000000000000000000000000000000000000000000) else (0xdb781a1a4f02fb35e05c663c0c2c2781a166f037acde0685938cde9b781e12ef03b239e07c413c0fa7c781ed02f03d9dde07f3fbc0f67f78e18f4f044a01e085403c30400000000000000000000000000000000000000000000000))) else (if i<211 then (if i<210 then (0xc2781e160f03d2a1e073563c0f0a9781d142f03d269e07c503c114927820d18f044a25e0843f3c10a7678208f6f0431d5ed7f3cbc0fe84781e104f1bda11e07840bc0fc00000000000000000000000000000000000000000000000) else (0xb970d4952f02aa69e05c51bc0ae9c7819134f038255f37254bc0e894781f92901c2231e087413c0fc777822100f1c21cdd3873bbc1047b78208f8f0419edde823f3c10000000000000000000000000000000000000000000000000)) else (if i<212 then (0xfaf7d01d5b7aa3cbc1467f7825d12ffca219e0934e3c12a91782552ef04c249e0913fbc1227e7821906f0459e5e0883c3c10c7c78228fcef431f1e0893ebc10e00000000000000000000000000000000000000000000000) else (0x138f034279e0674dbc0e295781e538f03ba61e075583c0f0a57d9f15cdb38289e07547bc0fe83792011af041201e0883ebc10a857720106f040211e07941bc0f800000000000000000000000000000000000000000000000)))) else (if i<217 then (if i<215 then (if i<214 then (0x106f047a11e08d45bc1128d7b20924f041a31df7d53bc0daa0781a93af037a59e07046bc0d282781ad1cf03421de06b40bc0e684781e904f0409f1e0853f3c10400000000000000000000000000000000000000000000000) else (0x122f843a41e08649bc10c8e7823928e845221e08649bc106897821916f042a15e08e3abc11c6c7823ceaf04c9c5e09139bd9187d7722104ef42201e0843fbbd0200000000000000000000000000000000000000000000000)) else (if i<216 then (0x12ef03e255e07d4c3c1009b781e53af03ba35e0754abc0f48e782251ef045249e086413c10c7a7861d1aee3e205d67b3f3c0fa847a1d90af03c20de0803fbc10600000000000000000000000000000000000000000000000) else (0x124f047245e0884bbc104937822926f046205e082473a502967820130f03ca5de07c43bc10080781f910f0431ede08a3d3c1107978234f8f042a09dd7e40bc10600000000000000000000000000000000000000000000000))) else (if i<219 then (if i<218 then (0x13ef03c261e07d4c3c0ec9c781e93cf040209e07e473c100957820120f042a49bc7f433c10c7d77a151af03fa11e08440bc114857821900f0421fde08241bbef800000000000000000000000000000000000000000000000) else (0x12cf03ba51e08246bc0fc95781f93af0409fde07d46bc0f694781e528f03f241e08545bc10e817821516f04221de081453c0fa8a781f506eec0a01e3843f3c10a00000000000000000000000000000000000000000000000)) else (if i<220 then (0x118f03aa55df77453c10692781ed3af03a1ede08243bc30a8c7822922f045a52008548bc10885782111cf04221de07a433c0f486781f506f03f20dde81413c10200000000000000000000000000000000000000000000000) else (if i<221 then (0x100f039a2de071463c0f88c799d120f0379f1e07445bc0e4957e5ed36e739261e06a4a3b4d0887819d22f035a01d7723fbc0f482781fd00f03ea0de07e413c10000000000000000000000000000000000000000000000000) else (0xe4f0549ede0a343bc1327f78244fcf0489bde08e3e3c1188f7823d18f044205e0883dbc1106e7ae10f6f0401c5e0863c3baf680781ecf8f040201de7f40bc0fc00000000000000000000000000000000000000000000000)))))) else (if i<230 then (if i<226 then (if i<224 then (if i<223 then (0x134f045275e08e4fbc1268f782751cf04c9f1e09a43bc12e9d7823126f043221e081413dd127178220f4f0441d9e086393c1127a77e04f6f0409f9e0853f3c10c00000000000000000000000000000000000000000000000) else (0x146d7432a9b18158bc106ab781e54cf040255e0804ebc0f0a8781dd30f03ca21e079453c0fa78781e902f03e9ede0803d3cf0a7a7821cf6f142a09e07f41bc2f600000000000000000000000000000000000000000000000)) else (if i<225 then (0x2a9e06d59bc0d4a3781b14ad9b6a51e06b4a3c0dc9e781a520f039201e073433c0e671781dcfaefbc9e9e07f3f3c1028078204fef042201e3833ebc10800000000000000000000000000000000000000000000000) else (0x259e08f4e3c1228e7825122f04a9f9e09240bc128867823502f0459c9e0913c3c1146778230eaf0459e1d7873f3c114807821d04f042209e085403c10600000000000000000000000000000000000000000000000))) else (if i<228 then (if i<227 then (0x291e07b563c0fca1782154af04323de08c4a3c112927824516f046a09e08d40bc1207278214fef2be9f9e07a43bc6f086769ed0aedbea19e07a413bf0200000000000000000000000000000000000000000000000) else (0x279e08254bc0faa5781ed54f03a269e0784e3c0f2a2781d12ef03ca39e27f483acf67678214f6f0459dde0863f3c0fa80781f502f0411fde082413c10200000000000000000000000000000000000000000000000)) else (if i<229 then (0x27de09452bc13e9f782713af04fa4613984a3c11a95782351ee5c8231e08d453c11c7a782450af0429f1e08e3d3c1147c7821504f040a01e083413c0fc00000000000000000000000000000000000000000000000) else (0x2c9e08061bc104ba781f976f03e2a1e089503c108a17e2013cf043261e0804bc01048a7820512f047225e08541bc104807821104ef42a09e0813fbc10400000000000000000000000000000000000000000000000)))) else (if i<234 then (if i<232 then (if i<231 then (0x2c5e06a62400c6b7781996cf0382c1e06c51bc0daa0781cd46f036a5de06d4c3c0dc8a781d92cf039235e077423c0f883781e90cf03d209e27d403c0fe00000000000000000000000000000000000000000000000) else (0x269e07a533c0e89c781dd4af93726de06d47bc0e092781d51ef03fa0de08242bc1007f781d90ef639a0de0763fbb6ee7c781e8fef03f9f9e0823f3c10200000000000000000000000000000000000000000000000)) else (if i<233 then (0x24dcf964cbc140927828124f04c21ddc9b3f3c12c8673a691af04a211e08b423c10274781f8f2f0401e1e07a3abc10e7578228faf0421fde0813f3c10600000000000000000000000000000000000000000000000) else (0x2a1e0605c3c0c4b1781a152f034285e06849bc0d49f781a540f6b7239e076423c0fe7178200f0f03f1c5e0873dbcf0e7e7820100f0401fde382403c30400000000000000000000000000000000000000000000000))) else (if i<236 then (if i<235 then (0x21de0b84cbc16e98782e920f053a21e0a83e3c13687782691af048a0de093413c11a707ae2ceaf0419dde08c40bc1167d7822cfef042201e78240bbf0000000000000000000000000000000000000000000000000) else (0x2f9e06d67bc0d4d1781a16cf035abde0794b39300a0782153af040a55ec79473c0ee7a78218eeedc1a09e47945bc0ea87781e904f03fa05e080403c10400000000000000000000000000000000000000000000000)) else (if i<237 then (0x2a9e0885c3c0f6b8781d540f038a9de0774abc0f6a4781dd3af03e235e082423c10a7f78200f2f0421e9e0813fbc0fe8077a0d00f042a01e08340bc10400000000000000000000000000000000000000000000000) else (if i<238 then (0x2c5a776593c0d6ac781b520f03da75e07747bc0ea9a781bd30f03ba39e075443c0f47e781ecf8f4bf9e9d1853ebc11482781f908edbda09e07d413c0fa00000000000000000000000000000000000000000000000) else (0x4e3c10898781f914f042a4de07f41bc90a887823d1cf046209e08c40bc10078781fcf4f0429f9e082433bb027f78210fcf0411f9e0813f3c10000000000000000000000000000000000000000000000000))))))) else (if i<256 then (if i<247 then (if i<243 then (if i<241 then (if i<240 then (0x4fb652095782311cf043245e08c43bc120967823d32f047235e08b403c11a7678234fcf0429fde086433c10a8278e00fef0409f9df823ebc10600000000000000000000000000000000000000000000000) else (0x573c0eca0781dd26f03da71e0754b3c0daa4781b94cf03e25de08a463c112827823104f045211e085453c1088178218fef0421fde0823fbc70400000000000000000000000000000000000000000000000)) else (if i<242 then (0x51bc10296782251af045241e09b413c142917827d42f04a281ca8b4a3c10c8d7820d16f040a21e08246bc100867821104f042201dd83403c10200000000000000000000000000000000000000000000000) else (0x51bc0e89e781bd2cf0392a9ea63513c0ccaf7818168f52faa9e0694cba6e68f781cd16ebbd225e07a463c0ec89781d90aecbea09e07f403c10600000000000000000000000000000000000000000000000))) else (if i<245 then (if i<244 then (0x4b3dadc8c781d10ef036a31e06c43bc0da8e7819524f037a49e06a45bc0e481781e908f03b209d87840bc1027e7820d02f041a01e082413c6fe00000000000000000000000000000000000000000000000) else (0x41bc12c7f78274e6f04c9dde09b39bc124727823900f0441ede08c3e3db027a78200f2f0409e5e07e40baefe807760106f040205e081403c10200000000000000000000000000000000000000000000000)) else (if i<246 then (0x4c3c1209b7825516f04ca45e094423c1207f7824d0ef04c219e0913e3c11a7978218f2f0411d9e08a3fbc1187f7822104f042a05e087403bf0600000000000000000000000000000000000000000000000) else (0x53bc0f6af7821946f046291e08749bc10c91782213cf042259e085443c1067e781f4f4f03d9fde079453c0e686781cd0cf03a21de774413c0fa00000000000000000000000000000000000000000000000)))) else (if i<251 then (if i<249 then (if i<248 then (0x50bc0dab47d1c55cf036aa9e0714c3c0e098781cd42f03da69e07f453c0f87a78214e8f0459ddeb8b3e3c1167878214f2f0421e9e0833f3c10000000000000000000000000000000000000000000000000) else (0x46bc13aa47827934f052a69e0a643bc1528a7828536f048261e09542bc1327e79658fcf047a05e088433c1087c7822cf8f0459f1e08a3ebc11000000000000000000000000000000000000000000000000)) else (if i<250 then (0x54bc0d2c1781717cf02dafde05e57beaaeaa7b97d54f033ab1e06d4ebc0d693781b918f039a21df7444bc0e886781d90cf03a215e077423bef800000000000000000000000000000000000000000000000) else (0x48bc1789c782d530f05827202b042bc15e88782cd20f055a61b49943bc11c807d640fcf0469ede0853e3a90a7b78214f2f0419ede0853fbc10200000000000000000000000000000000000000000000000))) else (if i<253 then (if i<252 then (0x663c0b6d0781798ef030800000059bc0d4ba781a174f035ac1e07a4a3c1088f781dd14f03d9fde07c403c1087f78220f6f0429fde7803fbbefe00000000000000000000000000000000000000000000000) else (0x533c0eead781f94ef03b80000004e3c0f0a1781ed490dbdaa5e0734bbc0f0857820908f0411e9e08941bc10c8678204feeec01f9e0833ebc10800000000000000000000000000000000000000000000000)) else (if i<254 then (0x4e3b8baaa781653af032800000049bc0da9b6fdc53cf03ba6de078473cef486781f90af03d209e081443c0fa86781e8fcf03f201e07d403c10200000000000000000000000000000000000000000000000) else (if i<255 then (0x3c3c0ee82781c902f03a80000003fbc0e28b781e128f03ca49e07e43bc0f683781e8fcf03e209dd80423c10a7f78220f6f0419f1df83403c0fc00000000000000000000000000000000000000000000000) else (0x373c13a737826ceaf051800000037bc148827825d18e6caa3de09540bc1247c78230f2f047a05e082443c10e8678614faf3441f9e0893ebc10e00000000000000000000000000000000000000000000000)))))) else (if i<265 then (if i<260 then (if i<258 then (if i<257 then (0x453c0a08d7ed592ef02b8000000493c0c298781a940f03128de061493c0d087785d50ef13a209e072473c0e88a781d508f03da19e07a41bc0f800000000000000000000000000000000000000000000000) else (0x2cbc1566278290daf04f0000000393bb3a817825d02f048a0de0913cbc12e7b78270f4f04a9cde08e40bc1047e78208fcefbd9fde07f3f3c10200000000000000000000000000000000000000000000000)) else (if i<259 then (0x41baf0685781f114f04200000000000000977821d22f04424de08547bc10296771dd1cf03e201e080413c10a7f78214f0f0441f5e0833f3c10400000000000000000000000000000000000000000000000) else (0x42bc0ea80781ed1af03d800000000000009d781e530f03ea5de07e47bc0fc8c781f112f03e1fde080433c1028378200fef0419fddc813fbc10400000000000000000000000000000000000000000000000))) else (if i<262 then (if i<261 then (0x3cbc10a7a781fd0eea3f0000000000000095781f528f03da51c57c463c10087781f108f0409f9e07d433d6fa82781f902f23e9fde080403c0fa00000000000000000000000000000000000000000000000) else (0x3ebc1327876e4908f04f00000000000000917824d1cf04723de08445bc0fc827820108f0421e9e083413c1027f78210faf0421f9e0853e3bf0a00000000000000000000000000000000000000000000000)) else (if i<263 then (0x4abc0c889781ad42f02f00000000000000a3781b536f038a49e07b443def681782050ef0441f1e085413a910827820900f040a09e082403c10400000000000000000000000000000000000000000000000) else (if i<264 then (0x3c3c1107378224fcf045800000000000008f7821d16f03fa31e07a413c0ee81781d91cf039a01e07644bc0ea83781f500f03da0de27a40bc0f800000000000000000000000000000000000000000000000) else (0x3fbc1047b7821110f04300000000000000957323112f048215e48a3c3c112767822500f0401d5e07d3ebc1047f77200f4f03f9f1e0843e3c30a00000000000000000000000000000000000000000000000))))) else (if i<269 then (if i<267 then (if i<266 then (0x403c1347e782691af04700000000000000a0781fd30f0420000000403c1167e7822cfef0449c5e0903f3c1107e7820cf0f0429fde085403bf0000000000000000000000000000000000000000000000000) else (0x4cbc128977824d34f049800000000000009e7822536f0450000000453c114887821d0ef043201e08342bc0fc8078210f8f042a0ddf7d3fbc10000000000000000000000000000000000000000000000000)) else (if i<268 then (0x563c0a6a97812558f02a00000000000000a67816948f032800000049bc0d68e781b518f039a09e078413c0fa837820100f0411fde0843f3c30800000000000000000000000000000000000000000000000) else (0x3f3c110717820cfef03f800000000000007f7822910f03c00000003ebc8fe7a78224fcf0451e5ea883f3c104827820d02f03ea09e07e40bc10000000000000000000000000000000000000000000000000))) else (if i<271 then (if i<270 then (0x42b912c7378258faf4cb00000000000000887820cfef0420000000000000082781cd0ef03a00000003fbc0fe84781f0faf0419fde07f403c10000000000000000000000000000000000000000000000000) else (0x8878234000000000000000000008a781f904f043000000000000007478244f4f048800000000000007f77a18fef03f1f5e2823fbc10400000000000000000000000000000000000000000000000)) else (if i<272 then (0x94789d40000000000000000000087782210ef0440000000000000084781f914f5c0800000000000000000000f8f0410000000403c0fe00000000000000000000000000000000000000000000000) else (if i<273 then (0x8e781cd1cf03c0000000000000081781ec000000000000000000000000000faf03e80000003f3c30000000000000000000000000000000000000000000000000) else (0x80766490af9cb000000000000007b79240000000000000000000000000000f2eec48000000000000000000000000000000000000000000000000000000000000)))))))))) else 0
end SunPrimeRaceEasy.RaceLookup.SweepData
end

section
namespace SunPrimePermutation.WordRank

private def rep (b : ℕ) : ℕ → ℕ
  | 0 => 0
  | n+1 => 1 + b*rep b n

private theorem rep_key {b : ℕ} (hb : 1 ≤ b) (n : ℕ) : (b-1)*rep b n+1 = b^n := by
  induction n with
  | zero => simp [rep]
  | succ n h =>
    rw [rep, pow_succ, ← h]
    calc
      _ = ((b-1)*rep b n)*b + ((b-1)+1) := by ring
      _ = _ := by rw [Nat.sub_add_cancel hb]; ring

def mask (w n m : ℕ) : ℕ := m*((2^(w*n)-1)/(2^w-1))

private theorem mask_rep {w : ℕ} (hw : 0 < w) (n m : ℕ) :
    mask w n m = m*rep (2^w) n := by
  have h : 1 < 2^w := Nat.one_lt_two_pow hw.ne'
  unfold mask
  rw [pow_mul, ← rep_key h.le, Nat.add_sub_cancel, Nat.mul_div_cancel_left _ (by omega)]

theorem mask_succ {w : ℕ} (hw : 0 < w) (n m : ℕ) :
    mask w (n+1) m = 2^w*mask w n m + m := by
  rw [mask_rep hw, mask_rep hw, rep]
  ring

def extract (k n m : ℕ) := (n >>> k) &&& m

theorem extract_split {w a b k x y : ℕ} (ha : a < 2^w) (hb : b < 2^(w-k)) (hk : k ≤ w) :
    extract k (2^w*x+a) (2^w*y+b) = 2^w*extract k x y + extract k a b := by
  have hb' : b < 2^w := hb.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  have lowBound : extract k a b < 2^w := (Nat.and_le_right ..).trans_lt hb'
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_two_pow_mul_add _ lowBound]
  simp only [extract, Nat.testBit_and, Nat.testBit_shiftRight,
    Nat.testBit_two_pow_mul_add _ ha, Nat.testBit_two_pow_mul_add _ hb']
  by_cases hj : j < w
  · by_cases h : k+j < w
    · simp [hj, h]
    · have zero : b.testBit j = false := Nat.testBit_lt_two_pow
        (hb.trans_le (Nat.pow_le_pow_right (by decide) (by omega)))
      simp [hj,zero]
  · have high : ¬ k+j < w := by omega
    simp [hj, high, show k+j-w=k+(j-w) by omega]

def step (k n m : ℕ) := extract 0 n m + extract k n m

theorem step_split {w a b k x y : ℕ} (ha : a < 2^w) (hb : b < 2^(w-k)) (hk : k ≤ w) :
    step k (2^w*x+a) (2^w*y+b) = 2^w*step k x y + step k a b := by
  have hb' : b < 2^(w-0) := hb.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  simp only [step, extract_split ha hb' (Nat.zero_le w), extract_split ha hb hk]
  ring

def pack (w : ℕ) : ℕ → (ℕ → ℕ) → ℕ
  | 0, _ => 0
  | g+1, f => 2^w * pack w g (fun i => f (i+1)) + f 0

theorem step_pair {w a b : ℕ} (ha : a < 2^w) (hb : b < 2^w) :
    step w (2^w*b+a) (2^w-1) = a+b := by
  simp only [step, extract, Nat.and_two_pow_sub_one_eq_mod,
    Nat.shiftRight_eq_div_pow, Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt ha,
    Nat.mul_add_div (Nat.two_pow_pos w), Nat.div_eq_of_lt ha, Nat.add_zero, Nat.mod_eq_of_lt hb,
    pow_zero, Nat.div_one]

theorem merge_pairs {w : ℕ} (hw : 0 < w) (g : ℕ) (f : ℕ → ℕ) (hf : ∀ i, f i < 2^w) :
    step w (pack w (2*g) f) (mask (w+w) g (2^w-1)) =
      pack (w+w) g (fun i => f (2*i) + f (2*i+1)) := by
  induction g generalizing f with
  | zero => simp [pack, mask, step, extract]
  | succ g ih =>
    let f' := fun i => f (i+2)
    have unpack : pack w (2*(g+1)) f =
        2^(w+w)*pack w (2*g) f' + (2^w*f 1 + f 0) := by
      rw [show 2*(g+1) = (2*g+1)+1 by omega, pack, pack, pow_add]
      dsimp [f']
      ring
    have hv : 2^w*f 1 + f 0 < 2^(w+w) := by
      rw [pow_add]
      have h := Nat.mul_le_mul_left (2^w) (show f 1+1 ≤ 2^w from hf 1)
      rw [Nat.mul_succ] at h
      have := hf 0
      omega
    have hm : 2^w-1 < 2^(w+w-w) := by rw [Nat.add_sub_cancel]; exact Nat.sub_lt (Nat.two_pow_pos w) (by decide)
    rw [unpack, mask_succ (by omega), step_split hv hm (by omega), step_pair (hf 0) (hf 1),
      ih f' (fun i => hf (i+2)), pack]
    congr 2

def sums (f : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, i => f i
  | s+1, i => sums f s (2*i) + sums f s (2*i+1)

theorem sums_bound {f : ℕ → ℕ} (hf : ∀ i, f i ≤ 1) (s i : ℕ) : sums f s i ≤ 2^s := by
  induction s generalizing i with
  | zero => exact hf i
  | succ s ih =>
    rw [sums, pow_succ]
    have h := Nat.add_le_add (ih (2*i)) (ih (2*i+1))
    omega

def packedPop : ℕ → ℕ → ℕ → ℕ
  | 0, g, x => x % 2^g
  | s+1, g, x => step (2^s) (packedPop s (2*g) x) (mask (2^s+2^s) g (2^(2^s)-1))

def bits (x i : ℕ) := (x.testBit i).toNat

theorem pack_bits (g x : ℕ) : pack 1 g (bits x) = x%2^g := by
  induction g generalizing x with
  | zero => simp [pack, Nat.mod_one]
  | succ g ih =>
    have hf : (fun i => bits x (i+1)) = bits (x/2) := by
      funext i
      simp [bits, Nat.testBit_add_one]
    rw [pack, hf, ih, show 2^(g+1) = 2*2^g by rw [pow_succ, Nat.mul_comm], Nat.mod_mul]
    simp only [bits, pow_one, Nat.testBit_zero]
    have hm := Nat.mod_lt x (by decide : 0 < 2)
    rcases (show x%2 = 0 ∨ x%2 = 1 by omega) with hx | hx <;> simp [hx, Nat.add_comm]

theorem packedPop_eq (s g x : ℕ) :
    packedPop s g x = pack (2^s) g (sums (bits x) s) := by
  induction s generalizing g with
  | zero => exact (pack_bits g x).symm
  | succ s ih =>
    rw [packedPop, ih, merge_pairs (Nat.two_pow_pos _), pow_succ, Nat.mul_two]
    · rfl
    · intro i
      apply lt_of_le_of_lt (sums_bound (fun j => Bool.toNat_le _) _ _)
      exact Nat.lt_two_pow_self


open Finset

theorem pack_mod (g : ℕ) (f : ℕ → ℕ) :
    pack 32 g f ≡ ∑ i ∈ range g, f i [MOD 4294967295] := by
  induction g generalizing f with
  | zero => simp only [pack, range_zero, sum_empty]; rfl
  | succ g ih =>
    rw [pack, sum_range_succ' f g]
    have b : 2^32 ≡ 1 [MOD 4294967295] := by decide
    simpa only [one_mul] using (b.mul (ih (fun i => f (i+1)))).add (Nat.ModEq.refl (f 0))

theorem sum_pairs (f : ℕ → ℕ) (g : ℕ) :
    (∑ i ∈ range g, (f (2*i)+f (2*i+1))) = ∑ i ∈ range (2*g), f i := by
  induction g with
  | zero => simp
  | succ g ih =>
    rw [sum_range_succ, ih, show 2*(g+1) = (2*g+1)+1 by omega,
      sum_range_succ f (2*g+1), sum_range_succ f (2*g)]
    omega

theorem total_sums (f : ℕ → ℕ) (s g : ℕ) :
    (∑ i ∈ range g, sums f s i) = ∑ i ∈ range (2^s*g), f i := by
  induction s generalizing g with
  | zero => simp [sums]
  | succ s ih =>
    simp only [sums, sum_pairs, ih]
    rw [pow_succ, Nat.mul_assoc]

def fastCount (g x : ℕ) : ℕ := packedPop 5 g x % 4294967295

theorem bits_card (x n : ℕ) : (∑ i ∈ range n, bits x i) =
    ((range n).filter (fun i => x.testBit i)).card := by
  calc
    _ = ∑ i ∈ range n, if x.testBit i then 1 else 0 := by
      apply sum_congr rfl
      intro i _
      cases h : x.testBit i <;> simp [bits, h]
    _ = _ := by simpa using (sum_boole (R := ℕ) (fun i => x.testBit i = true) (range n))

theorem fastCount_eq (g x : ℕ) (hg : 32*g < 4294967295) :
    fastCount g x = ((range (32*g)).filter (fun i => x.testBit i)).card := by
  unfold fastCount
  rw [packedPop_eq]
  change pack 32 g (sums (bits x) 5) % 4294967295 = _
  rw [show pack 32 g (sums (bits x) 5) % 4294967295 =
      (∑ i ∈ range g, sums (bits x) 5 i) % 4294967295 from pack_mod .., total_sums]
  change (∑ i ∈ range (32*g), bits x i) % 4294967295 = _
  rw [bits_card]
  apply Nat.mod_eq_of_lt
  exact lt_of_le_of_lt ((card_le_card (filter_subset _ _)).trans_eq (card_range _)) hg

theorem fastCount_reference (x : ℕ) :
    fastCount 8192 x = SunPrimeNumeric.wordCount 14 x := by
  rw [fastCount_eq _ _ (by decide), SunPrimeNumeric.wordCount_eq _ _ (by decide)]
  rfl

end SunPrimePermutation.WordRank
end

section
namespace SunPrimePermutation.WordRank
open Finset

theorem pack_append (w l r : ℕ) (f : ℕ → ℕ) :
    pack w (l+r) f = 2^(w*l) * pack w r (fun i => f (i+l)) + pack w l f := by
  induction l generalizing f with
  | zero => simp [pack]
  | succ l ih =>
    rw [Nat.succ_add, pack, ih, pack, Nat.mul_succ, pow_add]
    simp only [Nat.add_assoc]
    ring

theorem pack_bound (w l : ℕ) (f : ℕ → ℕ) (hf : ∀ i, f i < 2^w) :
    pack w l f < 2^(w*l) := by
  induction l generalizing f with
  | zero => simp [pack]
  | succ l ih =>
    rw [pack, Nat.mul_succ, pow_add, Nat.mul_comm (2^(w*l))]
    have h := Nat.mul_le_mul_left (2^w) (ih (fun i => f (i+1)) (fun i => hf _) :
      pack w l (fun i => f (i+1))+1 ≤ 2^(w*l))
    rw [Nat.mul_succ] at h
    have := hf 0
    omega

theorem bank_prefix {q g : ℕ} (x : ℕ) (hq : q ≤ g) :
    packedPop 5 g x % 2^(32*q) = packedPop 5 q x := by
  simp only [packedPop_eq]
  change pack 32 g _ % _ = pack 32 q _
  rw [show g = q + (g-q) by omega, pack_append, Nat.mul_add_mod_self_left]
  apply Nat.mod_eq_of_lt
  apply pack_bound
  intro i
  apply lt_of_le_of_lt (sums_bound (fun j => Bool.toNat_le _) _ _)
  decide

def prefixFromBank (bank x k : ℕ) : ℕ :=
  let q := k/32
  let r := k%32
  let w := (x >>> (32*q)) % 4294967296
  bank % 2^(32*q) % 4294967295 + ∑ i ∈ range r, bits w i

theorem prefix_sound (x k : ℕ) (hk : k ≤ 262144) :
    prefixFromBank (packedPop 5 8192 x) x k = SunPrimeNumeric.wordCount 14 (x%2^k) := by
  have hq : k/32 ≤ 8192 := by omega
  have hg : 32*(k/32) < 4294967295 := by omega
  unfold prefixFromBank
  dsimp only
  rw [bank_prefix x hq]
  change fastCount (k/32) x + _ = _
  rw [fastCount_eq _ _ hg, ← bits_card, SunPrimeNumeric.wordCount_eq _ _ (by decide)]
  have split : 32*(k/32)+k%32 = k := by omega
  have hi : (∑ i ∈ range (k%32), bits ((x >>> (32*(k/32))) % 4294967296) i) =
      ∑ i ∈ range (k%32), bits x (32*(k/32)+i) := by
    apply sum_congr rfl
    intro i hm
    have lt : i < 32 := by have := mem_range.mp hm; omega
    apply congrArg Bool.toNat
    exact (Nat.testBit_mod_two_pow (x >>> (32*(k/32))) 32 i).trans
      (by simp only [lt, decide_true, Bool.true_and, Nat.testBit_shiftRight])
  have eqSets : (range k).filter (fun i => x.testBit i) =
      (range 262144).filter (fun i => (x%2^k).testBit i) := by
    ext i
    simp only [mem_filter, mem_range, Nat.testBit_mod_two_pow, Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨hl,hb⟩
      exact ⟨hl.trans_le hk,hl,hb⟩
    · exact fun h => h.2
  exact ((congrArg (fun y => _ + y) hi).trans
    ((sum_range_add (f := bits x) (32*(k/32)) (k%32)).symm.trans
      (by rw [split]; exact bits_card x k))).trans (congrArg Finset.card eqSets)

def fastCell (s : ℕ) (ds : List ℕ) (base : ℤ) (qs : List (ℕ × ℤ)) : ℤ × ℤ :=
  let m := roughMask (s+1) 262144 ds
  let pos := m &&& divMask (s+1+2) 3 262144
  let neg := m &&& divMask (s+1+1) 3 262144
  let bp := packedPop 5 8192 pos
  let bn := packedPop 5 8192 neg
  let val := fun k => base + (((prefixFromBank bp pos k : ℕ) : ℤ) - prefixFromBank bn neg k)
  (val 262144, (qs.map (fun z => z.2*val z.1)).sum)

theorem fastCell_eq (s : ℕ) (ds : List ℕ) (base : ℤ) (qs : List (ℕ × ℤ))
    (h : ∀ z ∈ qs, z.1 ≤ 262144) : fastCell s ds base qs = SunHardRank.cell 14 s ds base qs := by
  let m := roughMask (s+1) 262144 ds
  let pos := m &&& divMask (s+1+2) 3 262144
  let neg := m &&& divMask (s+1+1) 3 262144
  let val := fun k => base + (((prefixFromBank (packedPop 5 8192 pos) pos k : ℕ) : ℤ) -
    prefixFromBank (packedPop 5 8192 neg) neg k)
  let refValue := fun k => base + SunHardRank.rankBits 14 pos neg k
  have equal (k : ℕ) (hk : k ≤ 262144) : val k = refValue k :=
    congrArg (fun d : ℤ => base+d)
      (congrArg₂ (fun (a b : ℕ) => (a : ℤ) - b) (prefix_sound pos k hk) (prefix_sound neg k hk))
  change (val 262144, (qs.map (fun z => z.2*val z.1)).sum) =
    (refValue 262144, (qs.map (fun z => z.2*refValue z.1)).sum)
  apply Prod.ext
  · exact equal 262144 (le_refl _)
  · apply congrArg List.sum
    apply List.map_congr_left
    intro z hz
    exact congrArg (fun a => z.2*a) (equal z.1 (h z hz))

end SunPrimePermutation.WordRank
end

section
namespace SunPrimeRaceEasy.RaceLookup.Cached
open SunPrimePermutation SunHardCompact SunHardRank
open SunPrimePermutation.WordRank

/-- In base 2^32 the j-th digit is the cumulative count through word j. -/
def cumulative (x : ℕ) : ℕ :=
  let b := packedPop 5 8192 x
  ((((b%4294967295) <<< 262144)-b)/4294967295)

def pop32 (v : ℕ) : ℕ :=
  let a := (v &&& 1431655765) + ((v>>>1) &&& 1431655765)
  let b := (a &&& 858993459) + ((a>>>2) &&& 858993459)
  let c := (b &&& 252645135) + ((b>>>4) &&& 252645135)
  let d := (c &&& 16711935) + ((c>>>8) &&& 16711935)
  (d &&& 65535)+((d>>>16) &&& 65535)

def lookup (bank bits k : ℕ) : ℕ :=
  let q := k/32
  let r := k%32
  let a := if q=0 then 0 else (bank >>> (32*(q-1)))%4294967296
  let w := (bits >>> (32*q)) &&& (2^r-1)
  a+pop32 w

def evaluate (s mask : ℕ) (base : ℤ) (qs : List (ℕ × ℤ)) : ℤ × ℤ :=
  let pos := mask &&& divMask (s+3) 3 262144
  let neg := mask &&& divMask (s+2) 3 262144
  let bp := cumulative pos
  let bn := cumulative neg
  let val := fun k => base+((lookup bp pos k : ℤ)-lookup bn neg k)
  (val 262144,(qs.map fun z => z.2*val (z.1-s)).sum)

def check (s : ℕ) : ℕ → List ℕ → ℕ → Bool
  | _,[],_ => true
  | col,p::ps,blocked => if col=0 then true else
    let u := col%Sweep.radix
    let b := Sweep.initial u
    (u==0 || decide (evaluate s ((2^262144-1) ^^^ blocked) b (cellRows p s) =
      (b+traceDelta (Sweep.code u),traceWeight (Sweep.code u)))) &&
    check s (col/Sweep.radix) ps (divMask (s+1) p 262144 ||| blocked)

end SunPrimeRaceEasy.RaceLookup.Cached
end

section
namespace SunPrimeRaceEasy.RaceLookup.Cached
open Finset SunPrimePermutation.WordRank

private theorem pack_snoc (f : ℕ → ℕ) (n : ℕ) :
    pack 32 (n+1) f = 2^(32*n)*f n+pack 32 n f := by
  calc
    _ = 2^(32*n)*pack 32 1 (fun i => f (i+n))+pack 32 n f := pack_append 32 n 1 f
    _ = _ := by simp [pack]

private theorem telescoping (f : ℕ → ℕ) (g : ℕ) :
    4294967295*pack 32 g (fun j => ∑ i ∈ range (j+1), f i) + pack 32 g f =
    2^(32*g)*(∑ i ∈ range g, f i) := by
  induction g with
  | zero => simp [pack]
  | succ g ih =>
    rw [pack_snoc,pack_snoc,Finset.sum_range_succ,Nat.mul_succ,pow_add]
    simp only [Finset.sum_range_succ]
    let a := 2^(32*g)
    let total := ∑ i ∈ range g, f i
    let pp := pack 32 g (fun j => ∑ i ∈ range (j+1), f i)
    let bb := pack 32 g f
    change 4294967295*pp+bb=a*total at ih
    change 4294967295*(a*(total+f g)+_)+(a*f g+bb)=(a*4294967296)*(total+f g)
    have hpp : (pack 32 g (fun j => (∑ i ∈ range j, f i)+f j)) = pp := by
      simp only [pp,Finset.sum_range_succ]
    rw [hpp]
    calc
      _ = a*(4294967295*(total+f g)+f g)+(4294967295*pp+bb) := by ring
      _ = _ := by rw [ih]; ring

private theorem sum_bound {f : ℕ → ℕ} (hf : ∀ i, f i≤32) (g : ℕ) :
    (∑ i ∈ range g, f i)≤g*32 := by
  simpa using
    (Finset.sum_le_sum (s := range g) (f := f) (g := fun _ => 32) (fun i _ => hf i))

private theorem prefix_formula (g : ℕ) (f : ℕ → ℕ) (ht : (∑ i ∈ range g,f i)<4294967295) :
    ((((pack 32 g f%4294967295) <<< (32*g))-pack 32 g f)/4294967295) =
    pack 32 g (fun j => ∑ i ∈ range (j+1),f i) := by
  have hmod := pack_mod g f
  change (pack 32 g f)%4294967295 = (∑ i ∈ range g,f i)%4294967295 at hmod
  rw [Nat.mod_eq_of_lt ht] at hmod
  rw [hmod,Nat.shiftLeft_eq,Nat.mul_comm _ (2^(32*g)),← telescoping f g,
    Nat.add_sub_cancel,Nat.mul_div_cancel_left _ (by decide)]

theorem cumulative_eq (x : ℕ) :
    cumulative x = pack 32 8192 (fun j => ∑ i ∈ range (j+1), sums (bits x) 5 i) := by
  let f := sums (bits x) 5
  have hsmall (i : ℕ) : f i≤32 := sums_bound (fun j => Bool.toNat_le _) 5 i
  have ht : (∑ i ∈ range 8192,f i) < 4294967295 :=
    (sum_bound hsmall 8192).trans_lt (by decide)
  simpa only [cumulative,packedPop_eq,show 2^5=32 by decide,show 32*8192=262144 by decide] using
    prefix_formula 8192 f ht

private theorem pack_digit {g i : ℕ} {f : ℕ → ℕ} (hi : i<g) (hf : ∀ j<g, f j<4294967296) :
    ((pack 32 g f >>> (32*i)) % 4294967296) = f i := by
  induction g generalizing i f with
  | zero => omega
  | succ g ih =>
    cases i with
    | zero =>
      simp only [pack,Nat.mul_zero,Nat.shiftRight_zero]
      change (4294967296*pack 32 g (fun i => f (i+1))+f 0)%4294967296=f 0
      rw [Nat.mul_add_mod_self_left,Nat.mod_eq_of_lt (hf 0 (by omega))]
    | succ i =>
      have h := ih (f := fun j => f (j+1)) (i := i) (by omega) (fun j hj => hf _ (by omega))
      rw [pack,show 32*(i+1)=32+32*i by omega,Nat.shiftRight_add]
      have low := hf 0 (by omega)
      have hsplit : (2^32*pack 32 g (fun j => f (j+1))+f 0) >>> 32 =
          pack 32 g (fun j => f (j+1)) := by
        rw [Nat.shiftRight_eq_div_pow,Nat.mul_add_div (by decide),show 2^32=4294967296 by decide,
          Nat.div_eq_of_lt low,Nat.add_zero]
      rw [hsplit]
      exact h

theorem cumulative_prefix (x q : ℕ) (hq : q≤8192) :
    (if q=0 then 0 else (cumulative x >>> (32*(q-1)))%4294967296) =
    (packedPop 5 8192 x)%2^(32*q)%4294967295 := by
  cases q with
  | zero => simp [Nat.mod_one]
  | succ q =>
    let f := sums (bits x) 5
    have hf (i : ℕ) : f i≤32 := sums_bound (fun j => Bool.toNat_le _) 5 i
    have hbound (j : ℕ) (hj : j<8192) : (∑ i ∈ range (j+1),f i)<4294967296 :=
      (sum_bound hf (j+1)).trans_lt (by omega)
    rw [if_neg (by omega),Nat.add_one_sub_one,cumulative_eq,pack_digit (by omega) hbound,
      bank_prefix x hq,packedPop_eq]
    have hm := pack_mod (q+1) f
    change (pack 32 (q+1) f)%4294967295 = (∑ i ∈ range (q+1),f i)%4294967295 at hm
    rw [Nat.mod_eq_of_lt ((sum_bound hf (q+1)).trans_lt (by omega))] at hm
    exact hm.symm

end SunPrimeRaceEasy.RaceLookup.Cached
end

section
namespace SunPrimeRaceEasy.RaceLookup.Cached
open Finset SunPrimePermutation SunPrimePermutation.WordRank SunPrimeNumeric SunHardRank SunHardCompact

private theorem pop32_eq {v : ℕ} (hv : v<4294967296) : pop32 v = fastCount 1 v := by
  have hb : packedPop 5 1 v < 4294967295 := by
    rw [packedPop_eq]
    simpa only [pack,Nat.zero_add,Nat.mul_zero] using
      ((sums_bound (f := bits v) (fun j => Bool.toNat_le _) 5 0).trans_lt
        (show 2^5<4294967295 by decide))
  rw [fastCount,Nat.mod_eq_of_lt hb]
  norm_num [pop32,packedPop,step,extract,mask,Nat.mod_eq_of_lt hv]

private theorem tail_eq (x q r : ℕ) (hr : r<32) :
    pop32 ((x >>> (32*q)) &&& (2^r-1)) =
    ∑ i ∈ range r, bits ((x >>> (32*q))%4294967296) i := by
  let v := x >>> (32*q)
  have h32 : 2^r ≤ 4294967296 := Nat.pow_le_pow_right (by decide : 0<2) (show r≤32 by omega)
  rw [Nat.and_two_pow_sub_one_eq_mod,pop32_eq ((Nat.mod_lt _ (by positivity)).trans_le h32),
    fastCount_eq _ _ (by decide),bits_card]
  change ((range 32).filter (fun i => (v%2^r).testBit i)).card =
    ((range r).filter (fun i => (v%2^32).testBit i)).card
  congr 1
  ext i
  by_cases hi : i < r
  · have hi' : i < 32 := by omega
    simp [Nat.testBit_mod_two_pow,hi,hi']
    change v.testBit i = (v % 2^32).testBit i
    rw [Nat.testBit_mod_two_pow]
    simp [hi']
  · simp [Nat.testBit_mod_two_pow,hi]

theorem lookup_eq (x k : ℕ) (hk : k ≤ 262144) :
    lookup (cumulative x) x k = wordCount 14 (x%2^k) := by
  rw [← prefix_sound x k hk]
  unfold lookup prefixFromBank
  dsimp only
  rw [cumulative_prefix x _ (by omega),tail_eq x _ _ (Nat.mod_lt _ (by decide))]

theorem evaluate_eq (s mask : ℕ) (base : ℤ) (qs : List (ℕ × ℤ))
    (hq : ∀ z∈qs, z.1 ≤ s+262144) :
    evaluate s mask base qs = Sweep.evaluate s mask base qs := by
  let pos := mask &&& divMask (s+3) 3 262144
  let neg := mask &&& divMask (s+2) 3 262144
  let val := fun k => base + ((lookup (cumulative pos) pos k : ℤ) - lookup (cumulative neg) neg k)
  let refValue := fun k => base + rankBits 14 pos neg k
  have equal (k : ℕ) (hk : k ≤ 262144) : val k = refValue k :=
    congrArg (fun d : ℤ => base+d)
      (congrArg₂ (fun (a b : ℕ) => (a : ℤ) - b) (lookup_eq pos k hk) (lookup_eq neg k hk))
  change (val 262144, (qs.map (fun z => z.2*val (z.1-s))).sum) =
    (refValue 262144, (qs.map (fun z => z.2*refValue (z.1-s))).sum)
  apply Prod.ext
  · exact equal 262144 (le_refl _)
  · apply congrArg List.sum
    apply List.map_congr_left
    intro z hz
    exact congrArg (fun a => z.2*a) (equal _ (by have := hq z hz; omega))

theorem check_sound (s col blocked : ℕ) (ps : List ℕ) (h : check s col ps blocked=true) :
    Sweep.scan s col ps blocked=true := by
  induction ps generalizing col blocked with
  | nil => rfl
  | cons p ps ih =>
    by_cases hc : col=0
    · simp [Sweep.scan,hc]
    · simp only [check,if_neg hc,Bool.and_eq_true] at h
      simp only [Sweep.scan,if_neg hc,Bool.and_eq_true]
      refine ⟨?_,ih _ _ h.2⟩
      unfold Sweep.test
      simpa only [evaluate_eq _ _ _ _ (fun z hz => (cellRows_bounds hz).2)] using h.1

end SunPrimeRaceEasy.RaceLookup.Cached
end

section
namespace SunPrimeRaceEasy.RaceLookup.Cached
open SunHardRank SunPrimePermutation

def fastChunk (i col lo len : ℕ) : Bool :=
  let s := i*262144
  let ps := trialList 881
  check s (col/Sweep.radix^lo) ((ps.drop lo).take len) (blockedMask (s+1) 262144 (ps.take lo))

theorem chunk_sound {i col lo len : ℕ} (h : fastChunk i col lo len=true) :
    Sweep.chunkOK i col lo len=true := check_sound _ _ _ _ h

end SunPrimeRaceEasy.RaceLookup.Cached
end

section
namespace SunPrimeRaceEasy.RaceLookup.SweepData
open SunPrimeRaceEasy.RaceLookup.Sweep
def chunks0 : List (List ℕ) := [[24,24,16,3,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,3,24,24,13]]
def chunks1 : List (List ℕ) := [[24,14,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,3,4,6,24,10]]
def chunks2 : List (List ℕ) := [[24,4,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,2,2,2,2,2,2,3,3,3,3,3,3,4,4,4,4,4,5,5,5,5,6,8,15]]
def chunks3 : List (List ℕ) := [[23,2,2,2,2,2,2,3,3,3,3,4,4,4,5,6,6,7,7,8,9,10,10,13,12]]
def chunks4 : List (List ℕ) := [[19,2,2,3,3,4,4,5,6,7,8,9,11,12,15,20,22]]
def chunks5 : List (List ℕ) := [[17,3,3,4,5,7,8,10,12,15,20,24,24]]
def chunks6 : List (List ℕ) := [[16,4,5,7,10,13,18,24,24,31]]
def chunks7 : List (List ℕ) := [[14,4,7,10,15,22,24,24,32]]
def chunks8 : List (List ℕ) := [[14,6,10,17,24,24,24,33]]
def chunks9 : List (List ℕ) := [[13,7,14,24,24,24,46]]
def chunks10 : List (List ℕ) := [[14,11,23,24,24,56]]
def chunks11 : List (List ℕ) := [[15,16,24,24,24,49]]
def chunks12 : List (List ℕ) := [[15,22,24,24,67]]
def chunks13 : List (List ℕ) := [[16,24,24,24,64],[17,24,24,24,63]]
def chunks15 : List (List ℕ) := [[19,24,24,24,61],[21,24,24,24,59]]
def chunks17 : List (List ℕ) := [[24,24,24,80],[24,24,24,80]]
def chunks19 : List (List ℕ) := [[24,24,24,80],[24,24,24,80],[24,24,24,80]]
def chunks22 : List (List ℕ) := [[24,24,24,80],[24,24,24,80],[24,24,24,80]]
def chunks25 : List (List ℕ) := [[24,24,24,80],[24,24,24,80],[24,24,24,80],[24,24,24,80]]
def chunks29 : List (List ℕ) := [[24,24,24,80],[24,24,24,80],[24,24,24,80],[24,24,24,80],[24,24,24,80]]
def chunks34 : List (List ℕ) := [[24,24,24,80],[24,24,24,80],[24,24,24,80],[24,24,24,80],[24,24,24,80]]
def chunks39 : List (List ℕ) := [[24,24,24,80],[24,24,24,80],[24,24,24,80],[24,24,24,80],[24,24,24,80],[24,24,24,80]]
def chunks45 : List (List ℕ) := [[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104]]
def chunks52 : List (List ℕ) := [[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104]]
def chunks59 : List (List ℕ) := [[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104]]
def chunks67 : List (List ℕ) := [[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104]]
def chunks76 : List (List ℕ) := [[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104]]
def chunks86 : List (List ℕ) := [[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104]]
def chunks96 : List (List ℕ) := [[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104]]
def chunks107 : List (List ℕ) := [[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104]]
def chunks119 : List (List ℕ) := [[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104]]
def chunks132 : List (List ℕ) := [[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104]]
def chunks145 : List (List ℕ) := [[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104]]
def chunks159 : List (List ℕ) := [[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104]]
def chunks173 : List (List ℕ) := [[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104]]
def chunks188 : List (List ℕ) := [[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104]]
def chunks204 : List (List ℕ) := [[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104]]
def chunks221 : List (List ℕ) := [[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,24,104],[24,128]]
def chunks239 : List (List ℕ) := [[24,128],[24,128],[24,128],[24,128],[24,128],[24,128],[24,128],[24,128],[24,128],[24,128],[24,128],[24,128],[24,128],[24,128],[24,128],[24,128],[24,128],[24,128],[24,128],[24,128]]
def chunks259 : List (List ℕ) := [[24,128],[24,128],[24,128],[24,128],[24,128],[24,128],[24,128],[24,128],[24,128],[24,128],[24,128],[24,128],[24,128],[24,128],[24,128]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem numeric_regions : (BatchOK table 0 chunks0) ∧ (BatchOK table 1 chunks1) ∧ (BatchOK table 2 chunks2) ∧ (BatchOK table 3 chunks3) ∧ (BatchOK table 4 chunks4) ∧ (BatchOK table 5 chunks5) ∧ (BatchOK table 6 chunks6) ∧ (BatchOK table 7 chunks7) ∧ (BatchOK table 8 chunks8) ∧ (BatchOK table 9 chunks9) ∧ (BatchOK table 10 chunks10) ∧ (BatchOK table 11 chunks11) ∧ (BatchOK table 12 chunks12) ∧ (BatchOK table 13 chunks13) ∧ (BatchOK table 15 chunks15) ∧ (BatchOK table 17 chunks17) ∧ (BatchOK table 19 chunks19) ∧ (BatchOK table 22 chunks22) ∧ (BatchOK table 25 chunks25) ∧ (BatchOK table 29 chunks29) ∧ (BatchOK table 34 chunks34) ∧ (BatchOK table 39 chunks39) ∧ (BatchOK table 45 chunks45) ∧ (BatchOK table 52 chunks52) ∧ (BatchOK table 59 chunks59) ∧ (BatchOK table 67 chunks67) ∧ (BatchOK table 76 chunks76) ∧ (BatchOK table 86 chunks86) ∧ (BatchOK table 96 chunks96) ∧ (BatchOK table 107 chunks107) ∧ (BatchOK table 119 chunks119) ∧ (BatchOK table 132 chunks132) ∧ (BatchOK table 145 chunks145) ∧ (BatchOK table 159 chunks159) ∧ (BatchOK table 173 chunks173) ∧ (BatchOK table 188 chunks188) ∧ (BatchOK table 204 chunks204) ∧ (BatchOK table 221 chunks221) ∧ (BatchOK table 239 chunks239) ∧ (BatchOK table 259 chunks259) := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simp only [chunks0, BatchOK, PiecesOK]
    repeat' apply And.intro
    all_goals first | apply SunPrimeRaceEasy.RaceLookup.Cached.chunk_sound; decide +kernel | exact True.intro | decide +kernel
  · simp only [chunks1, BatchOK, PiecesOK]
    repeat' apply And.intro
    all_goals first | apply SunPrimeRaceEasy.RaceLookup.Cached.chunk_sound; decide +kernel | exact True.intro | decide +kernel
  · simp only [chunks2, BatchOK, PiecesOK]
    repeat' apply And.intro
    all_goals first | apply SunPrimeRaceEasy.RaceLookup.Cached.chunk_sound; decide +kernel | exact True.intro | decide +kernel
  · simp only [chunks3, BatchOK, PiecesOK]
    repeat' apply And.intro
    all_goals first | apply SunPrimeRaceEasy.RaceLookup.Cached.chunk_sound; decide +kernel | exact True.intro | decide +kernel
  · simp only [chunks4, BatchOK, PiecesOK]
    repeat' apply And.intro
    all_goals first | apply SunPrimeRaceEasy.RaceLookup.Cached.chunk_sound; decide +kernel | exact True.intro | decide +kernel
  · simp only [chunks5, BatchOK, PiecesOK]
    repeat' apply And.intro
    all_goals first | apply SunPrimeRaceEasy.RaceLookup.Cached.chunk_sound; decide +kernel | exact True.intro | decide +kernel
  · simp only [chunks6, BatchOK, PiecesOK]
    repeat' apply And.intro
    all_goals first | apply SunPrimeRaceEasy.RaceLookup.Cached.chunk_sound; decide +kernel | exact True.intro | decide +kernel
  · simp only [chunks7, BatchOK, PiecesOK]
    repeat' apply And.intro
    all_goals first | apply SunPrimeRaceEasy.RaceLookup.Cached.chunk_sound; decide +kernel | exact True.intro | decide +kernel
  · simp only [chunks8, BatchOK, PiecesOK]
    repeat' apply And.intro
    all_goals first | apply SunPrimeRaceEasy.RaceLookup.Cached.chunk_sound; decide +kernel | exact True.intro | decide +kernel
  · simp only [chunks9, BatchOK, PiecesOK]
    repeat' apply And.intro
    all_goals first | apply SunPrimeRaceEasy.RaceLookup.Cached.chunk_sound; decide +kernel | exact True.intro | decide +kernel
  · simp only [chunks10, BatchOK, PiecesOK]
    repeat' apply And.intro
    all_goals first | apply SunPrimeRaceEasy.RaceLookup.Cached.chunk_sound; decide +kernel | exact True.intro | decide +kernel
  · simp only [chunks11, BatchOK, PiecesOK]
    repeat' apply And.intro
    all_goals first | apply SunPrimeRaceEasy.RaceLookup.Cached.chunk_sound; decide +kernel | exact True.intro | decide +kernel
  · simp only [chunks12, BatchOK, PiecesOK]
    repeat' apply And.intro
    all_goals first | apply SunPrimeRaceEasy.RaceLookup.Cached.chunk_sound; decide +kernel | exact True.intro | decide +kernel
  · simp only [chunks13, BatchOK, PiecesOK]
    repeat' apply And.intro
    all_goals first | apply SunPrimeRaceEasy.RaceLookup.Cached.chunk_sound; decide +kernel | exact True.intro | decide +kernel
  · simp only [chunks15, BatchOK, PiecesOK]
    repeat' apply And.intro
    all_goals first | apply SunPrimeRaceEasy.RaceLookup.Cached.chunk_sound; decide +kernel | exact True.intro | decide +kernel
  · simp only [chunks17, BatchOK, PiecesOK]
    repeat' apply And.intro
    all_goals first | apply SunPrimeRaceEasy.RaceLookup.Cached.chunk_sound; decide +kernel | exact True.intro | decide +kernel
  · simp only [chunks19, BatchOK, PiecesOK]
    repeat' apply And.intro
    all_goals first | apply SunPrimeRaceEasy.RaceLookup.Cached.chunk_sound; decide +kernel | exact True.intro | decide +kernel
  · simp only [chunks22, BatchOK, PiecesOK]
    repeat' apply And.intro
    all_goals first | apply SunPrimeRaceEasy.RaceLookup.Cached.chunk_sound; decide +kernel | exact True.intro | decide +kernel
  · simp only [chunks25, BatchOK, PiecesOK]
    repeat' apply And.intro
    all_goals first | apply SunPrimeRaceEasy.RaceLookup.Cached.chunk_sound; decide +kernel | exact True.intro | decide +kernel
  · simp only [chunks29, BatchOK, PiecesOK]
    repeat' apply And.intro
    all_goals first | apply SunPrimeRaceEasy.RaceLookup.Cached.chunk_sound; decide +kernel | exact True.intro | decide +kernel
  · simp only [chunks34, BatchOK, PiecesOK]
    repeat' apply And.intro
    all_goals first | apply SunPrimeRaceEasy.RaceLookup.Cached.chunk_sound; decide +kernel | exact True.intro | decide +kernel
  · simp only [chunks39, BatchOK, PiecesOK]
    repeat' apply And.intro
    all_goals first | apply SunPrimeRaceEasy.RaceLookup.Cached.chunk_sound; decide +kernel | exact True.intro | decide +kernel
  · simp only [chunks45, BatchOK, PiecesOK]
    repeat' apply And.intro
    all_goals first | apply SunPrimeRaceEasy.RaceLookup.Cached.chunk_sound; decide +kernel | exact True.intro | decide +kernel
  · simp only [chunks52, BatchOK, PiecesOK]
    repeat' apply And.intro
    all_goals first | apply SunPrimeRaceEasy.RaceLookup.Cached.chunk_sound; decide +kernel | exact True.intro | decide +kernel
  · simp only [chunks59, BatchOK, PiecesOK]
    repeat' apply And.intro
    all_goals first | apply SunPrimeRaceEasy.RaceLookup.Cached.chunk_sound; decide +kernel | exact True.intro | decide +kernel
  · simp only [chunks67, BatchOK, PiecesOK]
    repeat' apply And.intro
    all_goals first | apply SunPrimeRaceEasy.RaceLookup.Cached.chunk_sound; decide +kernel | exact True.intro | decide +kernel
  · simp only [chunks76, BatchOK, PiecesOK]
    repeat' apply And.intro
    all_goals first | apply SunPrimeRaceEasy.RaceLookup.Cached.chunk_sound; decide +kernel | exact True.intro | decide +kernel
  · simp only [chunks86, BatchOK, PiecesOK]
    repeat' apply And.intro
    all_goals first | apply SunPrimeRaceEasy.RaceLookup.Cached.chunk_sound; decide +kernel | exact True.intro | decide +kernel
  · simp only [chunks96, BatchOK, PiecesOK]
    repeat' apply And.intro
    all_goals first | apply SunPrimeRaceEasy.RaceLookup.Cached.chunk_sound; decide +kernel | exact True.intro | decide +kernel
  · simp only [chunks107, BatchOK, PiecesOK]
    repeat' apply And.intro
    all_goals first | apply SunPrimeRaceEasy.RaceLookup.Cached.chunk_sound; decide +kernel | exact True.intro | decide +kernel
  · simp only [chunks119, BatchOK, PiecesOK]
    repeat' apply And.intro
    all_goals first | apply SunPrimeRaceEasy.RaceLookup.Cached.chunk_sound; decide +kernel | exact True.intro | decide +kernel
  · simp only [chunks132, BatchOK, PiecesOK]
    repeat' apply And.intro
    all_goals first | apply SunPrimeRaceEasy.RaceLookup.Cached.chunk_sound; decide +kernel | exact True.intro | decide +kernel
  · simp only [chunks145, BatchOK, PiecesOK]
    repeat' apply And.intro
    all_goals first | apply SunPrimeRaceEasy.RaceLookup.Cached.chunk_sound; decide +kernel | exact True.intro | decide +kernel
  · simp only [chunks159, BatchOK, PiecesOK]
    repeat' apply And.intro
    all_goals first | apply SunPrimeRaceEasy.RaceLookup.Cached.chunk_sound; decide +kernel | exact True.intro | decide +kernel
  · simp only [chunks173, BatchOK, PiecesOK]
    repeat' apply And.intro
    all_goals first | apply SunPrimeRaceEasy.RaceLookup.Cached.chunk_sound; decide +kernel | exact True.intro | decide +kernel
  · simp only [chunks188, BatchOK, PiecesOK]
    repeat' apply And.intro
    all_goals first | apply SunPrimeRaceEasy.RaceLookup.Cached.chunk_sound; decide +kernel | exact True.intro | decide +kernel
  · simp only [chunks204, BatchOK, PiecesOK]
    repeat' apply And.intro
    all_goals first | apply SunPrimeRaceEasy.RaceLookup.Cached.chunk_sound; decide +kernel | exact True.intro | decide +kernel
  · simp only [chunks221, BatchOK, PiecesOK]
    repeat' apply And.intro
    all_goals first | apply SunPrimeRaceEasy.RaceLookup.Cached.chunk_sound; decide +kernel | exact True.intro | decide +kernel
  · simp only [chunks239, BatchOK, PiecesOK]
    repeat' apply And.intro
    all_goals first | apply SunPrimeRaceEasy.RaceLookup.Cached.chunk_sound; decide +kernel | exact True.intro | decide +kernel
  · simp only [chunks259, BatchOK, PiecesOK]
    repeat' apply And.intro
    all_goals first | apply SunPrimeRaceEasy.RaceLookup.Cached.chunk_sound; decide +kernel | exact True.intro | decide +kernel
theorem checked0 : (BatchOK table 0 chunks0) := numeric_regions.1
theorem checked1 : (BatchOK table 1 chunks1) := numeric_regions.2.1
theorem checked2 : (BatchOK table 2 chunks2) := numeric_regions.2.2.1
theorem checked3 : (BatchOK table 3 chunks3) := numeric_regions.2.2.2.1
theorem checked4 : (BatchOK table 4 chunks4) := numeric_regions.2.2.2.2.1
theorem checked5 : (BatchOK table 5 chunks5) := numeric_regions.2.2.2.2.2.1
theorem checked6 : (BatchOK table 6 chunks6) := numeric_regions.2.2.2.2.2.2.1
theorem checked7 : (BatchOK table 7 chunks7) := numeric_regions.2.2.2.2.2.2.2.1
theorem checked8 : (BatchOK table 8 chunks8) := numeric_regions.2.2.2.2.2.2.2.2.1
theorem checked9 : (BatchOK table 9 chunks9) := numeric_regions.2.2.2.2.2.2.2.2.2.1
theorem checked10 : (BatchOK table 10 chunks10) := numeric_regions.2.2.2.2.2.2.2.2.2.2.1
theorem checked11 : (BatchOK table 11 chunks11) := numeric_regions.2.2.2.2.2.2.2.2.2.2.2.1
theorem checked12 : (BatchOK table 12 chunks12) := numeric_regions.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem checked13 : (BatchOK table 13 chunks13) := numeric_regions.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem checked15 : (BatchOK table 15 chunks15) := numeric_regions.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem checked17 : (BatchOK table 17 chunks17) := numeric_regions.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem checked19 : (BatchOK table 19 chunks19) := numeric_regions.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem checked22 : (BatchOK table 22 chunks22) := numeric_regions.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem checked25 : (BatchOK table 25 chunks25) := numeric_regions.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem checked29 : (BatchOK table 29 chunks29) := numeric_regions.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem checked34 : (BatchOK table 34 chunks34) := numeric_regions.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem checked39 : (BatchOK table 39 chunks39) := numeric_regions.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem checked45 : (BatchOK table 45 chunks45) := numeric_regions.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem checked52 : (BatchOK table 52 chunks52) := numeric_regions.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem checked59 : (BatchOK table 59 chunks59) := numeric_regions.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem checked67 : (BatchOK table 67 chunks67) := numeric_regions.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem checked76 : (BatchOK table 76 chunks76) := numeric_regions.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem checked86 : (BatchOK table 86 chunks86) := numeric_regions.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem checked96 : (BatchOK table 96 chunks96) := numeric_regions.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem checked107 : (BatchOK table 107 chunks107) := numeric_regions.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem checked119 : (BatchOK table 119 chunks119) := numeric_regions.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem checked132 : (BatchOK table 132 chunks132) := numeric_regions.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem checked145 : (BatchOK table 145 chunks145) := numeric_regions.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem checked159 : (BatchOK table 159 chunks159) := numeric_regions.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem checked173 : (BatchOK table 173 chunks173) := numeric_regions.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem checked188 : (BatchOK table 188 chunks188) := numeric_regions.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem checked204 : (BatchOK table 204 chunks204) := numeric_regions.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem checked221 : (BatchOK table 221 chunks221) := numeric_regions.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem checked239 : (BatchOK table 239 chunks239) := numeric_regions.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem checked259 : (BatchOK table 259 chunks259) := numeric_regions.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
end SunPrimeRaceEasy.RaceLookup.SweepData
end

section
namespace SunPrimeRaceEasy.RaceLookup.SweepData
open SunPrimeRaceEasy.RaceLookup.Sweep

theorem table_ok (i : ℕ) : columnOK i (table i)=true := by
  by_cases ht : i<274
  ·
    by_cases split34 : i < 34
    ·
      by_cases split10 : i < 10
      ·
        by_cases split5 : i < 5
        ·
          by_cases split2 : i < 2
          ·
            by_cases split1 : i < 1
            ·
              exact batch_range checked0 (by omega) (by change i < 1; omega)
            ·
              exact batch_range checked1 (by omega) (by change i < 2; omega)
          ·
            by_cases split3 : i < 3
            ·
              exact batch_range checked2 (by omega) (by change i < 3; omega)
            ·
              by_cases split4 : i < 4
              ·
                exact batch_range checked3 (by omega) (by change i < 4; omega)
              ·
                exact batch_range checked4 (by omega) (by change i < 5; omega)
        ·
          by_cases split7 : i < 7
          ·
            by_cases split6 : i < 6
            ·
              exact batch_range checked5 (by omega) (by change i < 6; omega)
            ·
              exact batch_range checked6 (by omega) (by change i < 7; omega)
          ·
            by_cases split8 : i < 8
            ·
              exact batch_range checked7 (by omega) (by change i < 8; omega)
            ·
              by_cases split9 : i < 9
              ·
                exact batch_range checked8 (by omega) (by change i < 9; omega)
              ·
                exact batch_range checked9 (by omega) (by change i < 10; omega)
      ·
        by_cases split17 : i < 17
        ·
          by_cases split12 : i < 12
          ·
            by_cases split11 : i < 11
            ·
              exact batch_range checked10 (by omega) (by change i < 11; omega)
            ·
              exact batch_range checked11 (by omega) (by change i < 12; omega)
          ·
            by_cases split13 : i < 13
            ·
              exact batch_range checked12 (by omega) (by change i < 13; omega)
            ·
              by_cases split15 : i < 15
              ·
                exact batch_range checked13 (by omega) (by change i < 15; omega)
              ·
                exact batch_range checked15 (by omega) (by change i < 17; omega)
        ·
          by_cases split22 : i < 22
          ·
            by_cases split19 : i < 19
            ·
              exact batch_range checked17 (by omega) (by change i < 19; omega)
            ·
              exact batch_range checked19 (by omega) (by change i < 22; omega)
          ·
            by_cases split25 : i < 25
            ·
              exact batch_range checked22 (by omega) (by change i < 25; omega)
            ·
              by_cases split29 : i < 29
              ·
                exact batch_range checked25 (by omega) (by change i < 29; omega)
              ·
                exact batch_range checked29 (by omega) (by change i < 34; omega)
    ·
      by_cases split119 : i < 119
      ·
        by_cases split67 : i < 67
        ·
          by_cases split45 : i < 45
          ·
            by_cases split39 : i < 39
            ·
              exact batch_range checked34 (by omega) (by change i < 39; omega)
            ·
              exact batch_range checked39 (by omega) (by change i < 45; omega)
          ·
            by_cases split52 : i < 52
            ·
              exact batch_range checked45 (by omega) (by change i < 52; omega)
            ·
              by_cases split59 : i < 59
              ·
                exact batch_range checked52 (by omega) (by change i < 59; omega)
              ·
                exact batch_range checked59 (by omega) (by change i < 67; omega)
        ·
          by_cases split86 : i < 86
          ·
            by_cases split76 : i < 76
            ·
              exact batch_range checked67 (by omega) (by change i < 76; omega)
            ·
              exact batch_range checked76 (by omega) (by change i < 86; omega)
          ·
            by_cases split96 : i < 96
            ·
              exact batch_range checked86 (by omega) (by change i < 96; omega)
            ·
              by_cases split107 : i < 107
              ·
                exact batch_range checked96 (by omega) (by change i < 107; omega)
              ·
                exact batch_range checked107 (by omega) (by change i < 119; omega)
      ·
        by_cases split188 : i < 188
        ·
          by_cases split145 : i < 145
          ·
            by_cases split132 : i < 132
            ·
              exact batch_range checked119 (by omega) (by change i < 132; omega)
            ·
              exact batch_range checked132 (by omega) (by change i < 145; omega)
          ·
            by_cases split159 : i < 159
            ·
              exact batch_range checked145 (by omega) (by change i < 159; omega)
            ·
              by_cases split173 : i < 173
              ·
                exact batch_range checked159 (by omega) (by change i < 173; omega)
              ·
                exact batch_range checked173 (by omega) (by change i < 188; omega)
        ·
          by_cases split221 : i < 221
          ·
            by_cases split204 : i < 204
            ·
              exact batch_range checked188 (by omega) (by change i < 204; omega)
            ·
              exact batch_range checked204 (by omega) (by change i < 221; omega)
          ·
            by_cases split239 : i < 239
            ·
              exact batch_range checked221 (by omega) (by change i < 239; omega)
            ·
              by_cases split259 : i < 259
              ·
                exact batch_range checked239 (by omega) (by change i < 259; omega)
              ·
                exact batch_range checked259 (by omega) (by change i < 274; omega)
  · rw [show table i=0 by simp only [table,if_neg ht]]
    exact no_columns i
end SunPrimeRaceEasy.RaceLookup.SweepData
end

section
namespace SunHardCompact.Proof
open SunHardRank SunHardCompact SunPrimeRaceEasy.RaceLookup.Sweep
open SunPrimeRaceEasy.RaceLookup.SweepData
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v881 : evalPairs 880 (fullRow 881) = (-7) := by
  apply row_from_table table_ok (p := 881) (n := 3)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v877 : evalPairs 876 (fullRow 877) = (108) := by
  apply row_from_table table_ok (p := 877) (n := 4)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v863 : evalPairs 862 (fullRow 863) = (-70) := by
  apply row_from_table table_ok (p := 863) (n := 4)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v859 : evalPairs 858 (fullRow 859) = (273) := by
  apply row_from_table table_ok (p := 859) (n := 4)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v857 : evalPairs 856 (fullRow 857) = (-24) := by
  apply row_from_table table_ok (p := 857) (n := 4)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v853 : evalPairs 852 (fullRow 853) = (326) := by
  apply row_from_table table_ok (p := 853) (n := 4)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v839 : evalPairs 838 (fullRow 839) = (-230) := by
  apply row_from_table table_ok (p := 839) (n := 4)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v829 : evalPairs 828 (fullRow 829) = (90) := by
  apply row_from_table table_ok (p := 829) (n := 4)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v827 : evalPairs 826 (fullRow 827) = (-21) := by
  apply row_from_table table_ok (p := 827) (n := 4)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v823 : evalPairs 822 (fullRow 823) = (133) := by
  apply row_from_table table_ok (p := 823) (n := 4)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v821 : evalPairs 820 (fullRow 821) = (-72) := by
  apply row_from_table table_ok (p := 821) (n := 4)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v811 : evalPairs 810 (fullRow 811) = (207) := by
  apply row_from_table table_ok (p := 811) (n := 4)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v809 : evalPairs 808 (fullRow 809) = (-113) := by
  apply row_from_table table_ok (p := 809) (n := 4)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v797 : evalPairs 796 (fullRow 797) = (-117) := by
  apply row_from_table table_ok (p := 797) (n := 4)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v787 : evalPairs 786 (fullRow 787) = (122) := by
  apply row_from_table table_ok (p := 787) (n := 4)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v773 : evalPairs 772 (fullRow 773) = (-248) := by
  apply row_from_table table_ok (p := 773) (n := 4)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v769 : evalPairs 768 (fullRow 769) = (279) := by
  apply row_from_table table_ok (p := 769) (n := 4)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v761 : evalPairs 760 (fullRow 761) = (-219) := by
  apply row_from_table table_ok (p := 761) (n := 4)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v757 : evalPairs 756 (fullRow 757) = (277) := by
  apply row_from_table table_ok (p := 757) (n := 5)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v751 : evalPairs 750 (fullRow 751) = (56) := by
  apply row_from_table table_ok (p := 751) (n := 5)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v743 : evalPairs 742 (fullRow 743) = (105) := by
  apply row_from_table table_ok (p := 743) (n := 5)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v739 : evalPairs 738 (fullRow 739) = (-154) := by
  apply row_from_table table_ok (p := 739) (n := 5)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v733 : evalPairs 732 (fullRow 733) = (5) := by
  apply row_from_table table_ok (p := 733) (n := 5)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v727 : evalPairs 726 (fullRow 727) = (57) := by
  apply row_from_table table_ok (p := 727) (n := 5)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v719 : evalPairs 718 (fullRow 719) = (-83) := by
  apply row_from_table table_ok (p := 719) (n := 5)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v709 : evalPairs 708 (fullRow 709) = (8) := by
  apply row_from_table table_ok (p := 709) (n := 5)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v701 : evalPairs 700 (fullRow 701) = (38) := by
  apply row_from_table table_ok (p := 701) (n := 5)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v691 : evalPairs 690 (fullRow 691) = (-150) := by
  apply row_from_table table_ok (p := 691) (n := 5)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v683 : evalPairs 682 (fullRow 683) = (276) := by
  apply row_from_table table_ok (p := 683) (n := 5)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v677 : evalPairs 676 (fullRow 677) = (139) := by
  apply row_from_table table_ok (p := 677) (n := 6)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v673 : evalPairs 672 (fullRow 673) = (246) := by
  apply row_from_table table_ok (p := 673) (n := 6)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v661 : evalPairs 660 (fullRow 661) = (252) := by
  apply row_from_table table_ok (p := 661) (n := 6)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v659 : evalPairs 658 (fullRow 659) = (-191) := by
  apply row_from_table table_ok (p := 659) (n := 6)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v653 : evalPairs 652 (fullRow 653) = (-59) := by
  apply row_from_table table_ok (p := 653) (n := 6)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v647 : evalPairs 646 (fullRow 647) = (-486) := by
  apply row_from_table table_ok (p := 647) (n := 6)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v643 : evalPairs 642 (fullRow 643) = (278) := by
  apply row_from_table table_ok (p := 643) (n := 6)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v641 : evalPairs 640 (fullRow 641) = (-257) := by
  apply row_from_table table_ok (p := 641) (n := 6)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v631 : evalPairs 630 (fullRow 631) = (344) := by
  apply row_from_table table_ok (p := 631) (n := 6)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v619 : evalPairs 618 (fullRow 619) = (184) := by
  apply row_from_table table_ok (p := 619) (n := 6)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v617 : evalPairs 616 (fullRow 617) = (-368) := by
  apply row_from_table table_ok (p := 617) (n := 7)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v613 : evalPairs 612 (fullRow 613) = (395) := by
  apply row_from_table table_ok (p := 613) (n := 7)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v607 : evalPairs 606 (fullRow 607) = (-31) := by
  apply row_from_table table_ok (p := 607) (n := 7)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v601 : evalPairs 600 (fullRow 601) = (222) := by
  apply row_from_table table_ok (p := 601) (n := 7)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v599 : evalPairs 598 (fullRow 599) = (21) := by
  apply row_from_table table_ok (p := 599) (n := 7)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v593 : evalPairs 592 (fullRow 593) = (-95) := by
  apply row_from_table table_ok (p := 593) (n := 7)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v587 : evalPairs 586 (fullRow 587) = (-362) := by
  apply row_from_table table_ok (p := 587) (n := 7)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v577 : evalPairs 576 (fullRow 577) = (397) := by
  apply row_from_table table_ok (p := 577) (n := 7)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v571 : evalPairs 570 (fullRow 571) = (216) := by
  apply row_from_table table_ok (p := 571) (n := 8)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v569 : evalPairs 568 (fullRow 569) = (-31) := by
  apply row_from_table table_ok (p := 569) (n := 8)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v563 : evalPairs 562 (fullRow 563) = (2) := by
  apply row_from_table table_ok (p := 563) (n := 8)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v557 : evalPairs 556 (fullRow 557) = (185) := by
  apply row_from_table table_ok (p := 557) (n := 8)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v547 : evalPairs 546 (fullRow 547) = (177) := by
  apply row_from_table table_ok (p := 547) (n := 8)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v541 : evalPairs 540 (fullRow 541) = (64) := by
  apply row_from_table table_ok (p := 541) (n := 8)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v523 : evalPairs 522 (fullRow 523) = (-162) := by
  apply row_from_table table_ok (p := 523) (n := 9)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v521 : evalPairs 520 (fullRow 521) = (24) := by
  apply row_from_table table_ok (p := 521) (n := 9)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v509 : evalPairs 508 (fullRow 509) = (-200) := by
  apply row_from_table table_ok (p := 509) (n := 9)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v503 : evalPairs 502 (fullRow 503) = (7) := by
  apply row_from_table table_ok (p := 503) (n := 10)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v499 : evalPairs 498 (fullRow 499) = (190) := by
  apply row_from_table table_ok (p := 499) (n := 10)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v491 : evalPairs 490 (fullRow 491) = (-119) := by
  apply row_from_table table_ok (p := 491) (n := 10)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v487 : evalPairs 486 (fullRow 487) = (368) := by
  apply row_from_table table_ok (p := 487) (n := 10)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v479 : evalPairs 478 (fullRow 479) = (-332) := by
  apply row_from_table table_ok (p := 479) (n := 10)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v467 : evalPairs 466 (fullRow 467) = (54) := by
  apply row_from_table table_ok (p := 467) (n := 11)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v463 : evalPairs 462 (fullRow 463) = (-44) := by
  apply row_from_table table_ok (p := 463) (n := 11)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v461 : evalPairs 460 (fullRow 461) = (-171) := by
  apply row_from_table table_ok (p := 461) (n := 11)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v457 : evalPairs 456 (fullRow 457) = (410) := by
  apply row_from_table table_ok (p := 457) (n := 12)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v449 : evalPairs 448 (fullRow 449) = (78) := by
  apply row_from_table table_ok (p := 449) (n := 12)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v443 : evalPairs 442 (fullRow 443) = (20) := by
  apply row_from_table table_ok (p := 443) (n := 12)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v439 : evalPairs 438 (fullRow 439) = (53) := by
  apply row_from_table table_ok (p := 439) (n := 12)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v433 : evalPairs 432 (fullRow 433) = (18) := by
  apply row_from_table table_ok (p := 433) (n := 13)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v431 : evalPairs 430 (fullRow 431) = (296) := by
  apply row_from_table table_ok (p := 431) (n := 13)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v421 : evalPairs 420 (fullRow 421) = (285) := by
  apply row_from_table table_ok (p := 421) (n := 13)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v419 : evalPairs 418 (fullRow 419) = (-335) := by
  apply row_from_table table_ok (p := 419) (n := 14)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v409 : evalPairs 408 (fullRow 409) = (371) := by
  apply row_from_table table_ok (p := 409) (n := 14)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v401 : evalPairs 400 (fullRow 401) = (-265) := by
  apply row_from_table table_ok (p := 401) (n := 15)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v397 : evalPairs 396 (fullRow 397) = (194) := by
  apply row_from_table table_ok (p := 397) (n := 15)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v389 : evalPairs 388 (fullRow 389) = (181) := by
  apply row_from_table table_ok (p := 389) (n := 16)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v383 : evalPairs 382 (fullRow 383) = (-72) := by
  apply row_from_table table_ok (p := 383) (n := 16)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v379 : evalPairs 378 (fullRow 379) = (361) := by
  apply row_from_table table_ok (p := 379) (n := 17)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v373 : evalPairs 372 (fullRow 373) = (599) := by
  apply row_from_table table_ok (p := 373) (n := 17)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v367 : evalPairs 366 (fullRow 367) = (405) := by
  apply row_from_table table_ok (p := 367) (n := 17)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v359 : evalPairs 358 (fullRow 359) = (-468) := by
  apply row_from_table table_ok (p := 359) (n := 18)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v353 : evalPairs 352 (fullRow 353) = (-818) := by
  apply row_from_table table_ok (p := 353) (n := 19)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v349 : evalPairs 348 (fullRow 349) = (724) := by
  apply row_from_table table_ok (p := 349) (n := 19)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v347 : evalPairs 346 (fullRow 347) = (-815) := by
  apply row_from_table table_ok (p := 347) (n := 20)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v337 : evalPairs 336 (fullRow 337) = (843) := by
  apply row_from_table table_ok (p := 337) (n := 20)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v331 : evalPairs 330 (fullRow 331) = (440) := by
  apply row_from_table table_ok (p := 331) (n := 21)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v317 : evalPairs 316 (fullRow 317) = (-724) := by
  apply row_from_table table_ok (p := 317) (n := 23)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v313 : evalPairs 312 (fullRow 313) = (596) := by
  apply row_from_table table_ok (p := 313) (n := 24)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v311 : evalPairs 310 (fullRow 311) = (-592) := by
  apply row_from_table table_ok (p := 311) (n := 24)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v307 : evalPairs 306 (fullRow 307) = (933) := by
  apply row_from_table table_ok (p := 307) (n := 25)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v293 : evalPairs 292 (fullRow 293) = (-79) := by
  apply row_from_table table_ok (p := 293) (n := 26)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v283 : evalPairs 282 (fullRow 283) = (489) := by
  apply row_from_table table_ok (p := 283) (n := 29)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v281 : evalPairs 280 (fullRow 281) = (-168) := by
  apply row_from_table table_ok (p := 281) (n := 30)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v277 : evalPairs 276 (fullRow 277) = (-448) := by
  apply row_from_table table_ok (p := 277) (n := 30)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v271 : evalPairs 270 (fullRow 271) = (160) := by
  apply row_from_table table_ok (p := 271) (n := 31)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v269 : evalPairs 268 (fullRow 269) = (-60) := by
  apply row_from_table table_ok (p := 269) (n := 32)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v263 : evalPairs 262 (fullRow 263) = (-165) := by
  apply row_from_table table_ok (p := 263) (n := 33)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v257 : evalPairs 256 (fullRow 257) = (267) := by
  apply row_from_table table_ok (p := 257) (n := 35)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v251 : evalPairs 250 (fullRow 251) = (385) := by
  apply row_from_table table_ok (p := 251) (n := 37)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v241 : evalPairs 240 (fullRow 241) = (-516) := by
  apply row_from_table table_ok (p := 241) (n := 39)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v239 : evalPairs 238 (fullRow 239) = (494) := by
  apply row_from_table table_ok (p := 239) (n := 41)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v233 : evalPairs 232 (fullRow 233) = (499) := by
  apply row_from_table table_ok (p := 233) (n := 42)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v229 : evalPairs 228 (fullRow 229) = (-290) := by
  apply row_from_table table_ok (p := 229) (n := 44)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v227 : evalPairs 226 (fullRow 227) = (-47) := by
  apply row_from_table table_ok (p := 227) (n := 45)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v223 : evalPairs 222 (fullRow 223) = (265) := by
  apply row_from_table table_ok (p := 223) (n := 46)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v211 : evalPairs 210 (fullRow 211) = (-63) := by
  apply row_from_table table_ok (p := 211) (n := 50)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v199 : evalPairs 198 (fullRow 199) = (682) := by
  apply row_from_table table_ok (p := 199) (n := 56)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v197 : evalPairs 196 (fullRow 197) = (178) := by
  apply row_from_table table_ok (p := 197) (n := 60)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v193 : evalPairs 192 (fullRow 193) = (381) := by
  apply row_from_table table_ok (p := 193) (n := 62)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v191 : evalPairs 190 (fullRow 191) = (-148) := by
  apply row_from_table table_ok (p := 191) (n := 64)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v181 : evalPairs 180 (fullRow 181) = (-128) := by
  apply row_from_table table_ok (p := 181) (n := 68)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v179 : evalPairs 178 (fullRow 179) = (-192) := by
  apply row_from_table table_ok (p := 179) (n := 72)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v173 : evalPairs 172 (fullRow 173) = (4) := by
  apply row_from_table table_ok (p := 173) (n := 76)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v167 : evalPairs 166 (fullRow 167) = (189) := by
  apply row_from_table table_ok (p := 167) (n := 81)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v163 : evalPairs 162 (fullRow 163) = (13) := by
  apply row_from_table table_ok (p := 163) (n := 86)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v157 : evalPairs 156 (fullRow 157) = (499) := by
  apply row_from_table table_ok (p := 157) (n := 91)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v151 : evalPairs 150 (fullRow 151) = (-164) := by
  apply row_from_table table_ok (p := 151) (n := 98)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v149 : evalPairs 148 (fullRow 149) = (62) := by
  apply row_from_table table_ok (p := 149) (n := 104)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v139 : evalPairs 138 (fullRow 139) = (-116) := by
  apply row_from_table table_ok (p := 139) (n := 113)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v137 : evalPairs 136 (fullRow 137) = (564) := by
  apply row_from_table table_ok (p := 137) (n := 122)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v131 : evalPairs 130 (fullRow 131) = (200) := by
  apply row_from_table table_ok (p := 131) (n := 130)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v127 : evalPairs 126 (fullRow 127) = (-54) := by
  apply row_from_table table_ok (p := 127) (n := 140)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v113 : evalPairs 112 (fullRow 113) = (365) := by
  apply row_from_table table_ok (p := 113) (n := 162)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v109 : evalPairs 108 (fullRow 109) = (142) := by
  apply row_from_table table_ok (p := 109) (n := 189)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v107 : evalPairs 106 (fullRow 107) = (-116) := by
  apply row_from_table table_ok (p := 107) (n := 200)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v103 : evalPairs 102 (fullRow 103) = (-96) := by
  apply row_from_table table_ok (p := 103) (n := 211)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v101 : evalPairs 100 (fullRow 101) = (-478) := by
  apply row_from_table table_ok (p := 101) (n := 224)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v97 : evalPairs 96 (fullRow 97) = (-513) := by
  apply row_from_table table_ok (p := 97) (n := 238)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v89 : evalPairs 88 (fullRow 89) = (370) := by
  apply row_from_table table_ok (p := 89) (n := 270)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v83 : evalPairs 82 (fullRow 83) = (271) := by
  apply row_from_table table_ok (p := 83) (n := 272)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v79 : evalPairs 78 (fullRow 79) = (144) := by
  apply row_from_table table_ok (p := 79) (n := 270)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v73 : evalPairs 72 (fullRow 73) = (96) := by
  apply row_from_table table_ok (p := 73) (n := 251)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v71 : evalPairs 70 (fullRow 71) = (-158) := by
  apply row_from_table table_ok (p := 71) (n := 258)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v67 : evalPairs 66 (fullRow 67) = (627) := by
  apply row_from_table table_ok (p := 67) (n := 274)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v61 : evalPairs 60 (fullRow 61) = (172) := by
  apply row_from_table table_ok (p := 61) (n := 274)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v59 : evalPairs 58 (fullRow 59) = (-320) := by
  apply row_from_table table_ok (p := 59) (n := 265)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v53 : evalPairs 52 (fullRow 53) = (323) := by
  apply row_from_table table_ok (p := 53) (n := 269)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v47 : evalPairs 46 (fullRow 47) = (201) := by
  apply row_from_table table_ok (p := 47) (n := 274)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v43 : evalPairs 42 (fullRow 43) = (-51) := by
  apply row_from_table table_ok (p := 43) (n := 272)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v41 : evalPairs 40 (fullRow 41) = (-16) := by
  apply row_from_table table_ok (p := 41) (n := 269)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v37 : evalPairs 36 (fullRow 37) = (-192) := by
  apply row_from_table table_ok (p := 37) (n := 270)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v31 : evalPairs 30 (fullRow 31) = (73) := by
  apply row_from_table table_ok (p := 31) (n := 271)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v29 : evalPairs 28 (fullRow 29) = (91) := by
  apply row_from_table table_ok (p := 29) (n := 274)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v23 : evalPairs 22 (fullRow 23) = (-118) := by
  apply row_from_table table_ok (p := 23) (n := 271)
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem v19 : evalPairs 18 (fullRow 19) = (4) := by
  apply row_from_table table_ok (p := 19) (n := 273)
  all_goals decide +kernel
end SunHardCompact.Proof
end

section
namespace SunHardCompact
open SunHardRank SunPrimePermutation Finset

private def weights0 : List (ℕ × ℤ) := [(19,4),(23,(-118)),(29,91),(31,73),(37,(-192)),(41,(-16)),(43,(-51)),(47,201),(53,323),(59,(-320)),(61,172),(67,627),(71,(-158)),(73,96)]
private theorem weights0_ok : Scored weights0 := by
  apply scores_cons (p := 19) (z := 4) Proof.v19
  apply scores_cons (p := 23) (z := (-118)) Proof.v23
  apply scores_cons (p := 29) (z := 91) Proof.v29
  apply scores_cons (p := 31) (z := 73) Proof.v31
  apply scores_cons (p := 37) (z := (-192)) Proof.v37
  apply scores_cons (p := 41) (z := (-16)) Proof.v41
  apply scores_cons (p := 43) (z := (-51)) Proof.v43
  apply scores_cons (p := 47) (z := 201) Proof.v47
  apply scores_cons (p := 53) (z := 323) Proof.v53
  apply scores_cons (p := 59) (z := (-320)) Proof.v59
  apply scores_cons (p := 61) (z := 172) Proof.v61
  apply scores_cons (p := 67) (z := 627) Proof.v67
  apply scores_cons (p := 71) (z := (-158)) Proof.v71
  apply scores_cons (p := 73) (z := 96) Proof.v73
  exact scores_nil

private def weights1 : List (ℕ × ℤ) := [(79,144),(83,271),(89,370),(97,(-513)),(101,(-478)),(103,(-96)),(107,(-116)),(109,142),(113,365),(127,(-54)),(131,200),(137,564),(139,(-116)),(149,62)]
private theorem weights1_ok : Scored weights1 := by
  apply scores_cons (p := 79) (z := 144) Proof.v79
  apply scores_cons (p := 83) (z := 271) Proof.v83
  apply scores_cons (p := 89) (z := 370) Proof.v89
  apply scores_cons (p := 97) (z := (-513)) Proof.v97
  apply scores_cons (p := 101) (z := (-478)) Proof.v101
  apply scores_cons (p := 103) (z := (-96)) Proof.v103
  apply scores_cons (p := 107) (z := (-116)) Proof.v107
  apply scores_cons (p := 109) (z := 142) Proof.v109
  apply scores_cons (p := 113) (z := 365) Proof.v113
  apply scores_cons (p := 127) (z := (-54)) Proof.v127
  apply scores_cons (p := 131) (z := 200) Proof.v131
  apply scores_cons (p := 137) (z := 564) Proof.v137
  apply scores_cons (p := 139) (z := (-116)) Proof.v139
  apply scores_cons (p := 149) (z := 62) Proof.v149
  exact scores_nil

private def weights2 : List (ℕ × ℤ) := [(151,(-164)),(157,499),(163,13),(167,189),(173,4),(179,(-192)),(181,(-128)),(191,(-148)),(193,381),(197,178),(199,682),(211,(-63)),(223,265),(227,(-47))]
private theorem weights2_ok : Scored weights2 := by
  apply scores_cons (p := 151) (z := (-164)) Proof.v151
  apply scores_cons (p := 157) (z := 499) Proof.v157
  apply scores_cons (p := 163) (z := 13) Proof.v163
  apply scores_cons (p := 167) (z := 189) Proof.v167
  apply scores_cons (p := 173) (z := 4) Proof.v173
  apply scores_cons (p := 179) (z := (-192)) Proof.v179
  apply scores_cons (p := 181) (z := (-128)) Proof.v181
  apply scores_cons (p := 191) (z := (-148)) Proof.v191
  apply scores_cons (p := 193) (z := 381) Proof.v193
  apply scores_cons (p := 197) (z := 178) Proof.v197
  apply scores_cons (p := 199) (z := 682) Proof.v199
  apply scores_cons (p := 211) (z := (-63)) Proof.v211
  apply scores_cons (p := 223) (z := 265) Proof.v223
  apply scores_cons (p := 227) (z := (-47)) Proof.v227
  exact scores_nil

private def weights3 : List (ℕ × ℤ) := [(229,(-290)),(233,499),(239,494),(241,(-516)),(251,385),(257,267),(263,(-165)),(269,(-60)),(271,160),(277,(-448)),(281,(-168)),(283,489),(293,(-79)),(307,933)]
private theorem weights3_ok : Scored weights3 := by
  apply scores_cons (p := 229) (z := (-290)) Proof.v229
  apply scores_cons (p := 233) (z := 499) Proof.v233
  apply scores_cons (p := 239) (z := 494) Proof.v239
  apply scores_cons (p := 241) (z := (-516)) Proof.v241
  apply scores_cons (p := 251) (z := 385) Proof.v251
  apply scores_cons (p := 257) (z := 267) Proof.v257
  apply scores_cons (p := 263) (z := (-165)) Proof.v263
  apply scores_cons (p := 269) (z := (-60)) Proof.v269
  apply scores_cons (p := 271) (z := 160) Proof.v271
  apply scores_cons (p := 277) (z := (-448)) Proof.v277
  apply scores_cons (p := 281) (z := (-168)) Proof.v281
  apply scores_cons (p := 283) (z := 489) Proof.v283
  apply scores_cons (p := 293) (z := (-79)) Proof.v293
  apply scores_cons (p := 307) (z := 933) Proof.v307
  exact scores_nil

private def weights4 : List (ℕ × ℤ) := [(311,(-592)),(313,596),(317,(-724)),(331,440),(337,843),(347,(-815)),(349,724),(353,(-818)),(359,(-468)),(367,405),(373,599),(379,361),(383,(-72)),(389,181)]
private theorem weights4_ok : Scored weights4 := by
  apply scores_cons (p := 311) (z := (-592)) Proof.v311
  apply scores_cons (p := 313) (z := 596) Proof.v313
  apply scores_cons (p := 317) (z := (-724)) Proof.v317
  apply scores_cons (p := 331) (z := 440) Proof.v331
  apply scores_cons (p := 337) (z := 843) Proof.v337
  apply scores_cons (p := 347) (z := (-815)) Proof.v347
  apply scores_cons (p := 349) (z := 724) Proof.v349
  apply scores_cons (p := 353) (z := (-818)) Proof.v353
  apply scores_cons (p := 359) (z := (-468)) Proof.v359
  apply scores_cons (p := 367) (z := 405) Proof.v367
  apply scores_cons (p := 373) (z := 599) Proof.v373
  apply scores_cons (p := 379) (z := 361) Proof.v379
  apply scores_cons (p := 383) (z := (-72)) Proof.v383
  apply scores_cons (p := 389) (z := 181) Proof.v389
  exact scores_nil

private def weights5 : List (ℕ × ℤ) := [(397,194),(401,(-265)),(409,371),(419,(-335)),(421,285),(431,296),(433,18),(439,53),(443,20),(449,78),(457,410),(461,(-171)),(463,(-44)),(467,54)]
private theorem weights5_ok : Scored weights5 := by
  apply scores_cons (p := 397) (z := 194) Proof.v397
  apply scores_cons (p := 401) (z := (-265)) Proof.v401
  apply scores_cons (p := 409) (z := 371) Proof.v409
  apply scores_cons (p := 419) (z := (-335)) Proof.v419
  apply scores_cons (p := 421) (z := 285) Proof.v421
  apply scores_cons (p := 431) (z := 296) Proof.v431
  apply scores_cons (p := 433) (z := 18) Proof.v433
  apply scores_cons (p := 439) (z := 53) Proof.v439
  apply scores_cons (p := 443) (z := 20) Proof.v443
  apply scores_cons (p := 449) (z := 78) Proof.v449
  apply scores_cons (p := 457) (z := 410) Proof.v457
  apply scores_cons (p := 461) (z := (-171)) Proof.v461
  apply scores_cons (p := 463) (z := (-44)) Proof.v463
  apply scores_cons (p := 467) (z := 54) Proof.v467
  exact scores_nil

private def weights6 : List (ℕ × ℤ) := [(479,(-332)),(487,368),(491,(-119)),(499,190),(503,7),(509,(-200)),(521,24),(523,(-162)),(541,64),(547,177),(557,185),(563,2),(569,(-31)),(571,216)]
private theorem weights6_ok : Scored weights6 := by
  apply scores_cons (p := 479) (z := (-332)) Proof.v479
  apply scores_cons (p := 487) (z := 368) Proof.v487
  apply scores_cons (p := 491) (z := (-119)) Proof.v491
  apply scores_cons (p := 499) (z := 190) Proof.v499
  apply scores_cons (p := 503) (z := 7) Proof.v503
  apply scores_cons (p := 509) (z := (-200)) Proof.v509
  apply scores_cons (p := 521) (z := 24) Proof.v521
  apply scores_cons (p := 523) (z := (-162)) Proof.v523
  apply scores_cons (p := 541) (z := 64) Proof.v541
  apply scores_cons (p := 547) (z := 177) Proof.v547
  apply scores_cons (p := 557) (z := 185) Proof.v557
  apply scores_cons (p := 563) (z := 2) Proof.v563
  apply scores_cons (p := 569) (z := (-31)) Proof.v569
  apply scores_cons (p := 571) (z := 216) Proof.v571
  exact scores_nil

private def weights7 : List (ℕ × ℤ) := [(577,397),(587,(-362)),(593,(-95)),(599,21),(601,222),(607,(-31)),(613,395),(617,(-368)),(619,184),(631,344),(641,(-257)),(643,278),(647,(-486)),(653,(-59))]
private theorem weights7_ok : Scored weights7 := by
  apply scores_cons (p := 577) (z := 397) Proof.v577
  apply scores_cons (p := 587) (z := (-362)) Proof.v587
  apply scores_cons (p := 593) (z := (-95)) Proof.v593
  apply scores_cons (p := 599) (z := 21) Proof.v599
  apply scores_cons (p := 601) (z := 222) Proof.v601
  apply scores_cons (p := 607) (z := (-31)) Proof.v607
  apply scores_cons (p := 613) (z := 395) Proof.v613
  apply scores_cons (p := 617) (z := (-368)) Proof.v617
  apply scores_cons (p := 619) (z := 184) Proof.v619
  apply scores_cons (p := 631) (z := 344) Proof.v631
  apply scores_cons (p := 641) (z := (-257)) Proof.v641
  apply scores_cons (p := 643) (z := 278) Proof.v643
  apply scores_cons (p := 647) (z := (-486)) Proof.v647
  apply scores_cons (p := 653) (z := (-59)) Proof.v653
  exact scores_nil

private def weights8 : List (ℕ × ℤ) := [(659,(-191)),(661,252),(673,246),(677,139),(683,276),(691,(-150)),(701,38),(709,8),(719,(-83)),(727,57),(733,5),(739,(-154)),(743,105),(751,56)]
private theorem weights8_ok : Scored weights8 := by
  apply scores_cons (p := 659) (z := (-191)) Proof.v659
  apply scores_cons (p := 661) (z := 252) Proof.v661
  apply scores_cons (p := 673) (z := 246) Proof.v673
  apply scores_cons (p := 677) (z := 139) Proof.v677
  apply scores_cons (p := 683) (z := 276) Proof.v683
  apply scores_cons (p := 691) (z := (-150)) Proof.v691
  apply scores_cons (p := 701) (z := 38) Proof.v701
  apply scores_cons (p := 709) (z := 8) Proof.v709
  apply scores_cons (p := 719) (z := (-83)) Proof.v719
  apply scores_cons (p := 727) (z := 57) Proof.v727
  apply scores_cons (p := 733) (z := 5) Proof.v733
  apply scores_cons (p := 739) (z := (-154)) Proof.v739
  apply scores_cons (p := 743) (z := 105) Proof.v743
  apply scores_cons (p := 751) (z := 56) Proof.v751
  exact scores_nil

private def weights9 : List (ℕ × ℤ) := [(757,277),(761,(-219)),(769,279),(773,(-248)),(787,122),(797,(-117)),(809,(-113)),(811,207),(821,(-72)),(823,133),(827,(-21)),(829,90),(839,(-230)),(853,326)]
private theorem weights9_ok : Scored weights9 := by
  apply scores_cons (p := 757) (z := 277) Proof.v757
  apply scores_cons (p := 761) (z := (-219)) Proof.v761
  apply scores_cons (p := 769) (z := 279) Proof.v769
  apply scores_cons (p := 773) (z := (-248)) Proof.v773
  apply scores_cons (p := 787) (z := 122) Proof.v787
  apply scores_cons (p := 797) (z := (-117)) Proof.v797
  apply scores_cons (p := 809) (z := (-113)) Proof.v809
  apply scores_cons (p := 811) (z := 207) Proof.v811
  apply scores_cons (p := 821) (z := (-72)) Proof.v821
  apply scores_cons (p := 823) (z := 133) Proof.v823
  apply scores_cons (p := 827) (z := (-21)) Proof.v827
  apply scores_cons (p := 829) (z := 90) Proof.v829
  apply scores_cons (p := 839) (z := (-230)) Proof.v839
  apply scores_cons (p := 853) (z := 326) Proof.v853
  exact scores_nil

private def weights10 : List (ℕ × ℤ) := [(857,(-24)),(859,273),(863,(-70)),(877,108),(881,(-7))]
private theorem weights10_ok : Scored weights10 := by
  apply scores_cons (p := 857) (z := (-24)) Proof.v857
  apply scores_cons (p := 859) (z := 273) Proof.v859
  apply scores_cons (p := 863) (z := (-70)) Proof.v863
  apply scores_cons (p := 877) (z := 108) Proof.v877
  apply scores_cons (p := 881) (z := (-7)) Proof.v881
  exact scores_nil

private def weights : List (ℕ × ℤ) := (((weights0 ++ weights1) ++ (weights2 ++ (weights3 ++ weights4))) ++ ((weights5 ++ (weights6 ++ weights7)) ++ (weights8 ++ (weights9 ++ weights10))))
private theorem scores : Scored weights := (scores_append (scores_append (scores_append weights0_ok weights1_ok) (scores_append weights2_ok (scores_append weights3_ok weights4_ok))) (scores_append (scores_append weights5_ok (scores_append weights6_ok weights7_ok)) (scores_append weights8_ok (scores_append weights9_ok weights10_ok))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hardTotal_of_compact_rows
    (h : ∀ p ∈ Ioc 17 881, p.Prime → (originalQueries p).Perm (fullRow p)) :
    hardTotal 608981813029 8477 17 8477 = 7941 :=
  aggregate_rows (ws := weights) scores (by decide +kernel) (by decide +kernel) (by decide +kernel) h

end SunHardCompact
end

section
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a321727.main) :=
  SunPrimePermutation.disproof_of_hard_sum
    (SunHardCompact.hardTotal_of_compact_rows SunHardCompact.all_compact_permutations)
end

