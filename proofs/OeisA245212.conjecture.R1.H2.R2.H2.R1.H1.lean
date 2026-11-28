import OMAReductions.R_OeisA245212_conjecture_R1_H2_R2_H2_R1
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Multiplicity
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

open Finset
namespace D7TwoAdic

lemma val_add_of_lt {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (h : padicValNat 2 a < padicValNat 2 b) :
    padicValNat 2 (a+b) = padicValNat 2 a := by
  have hv : padicValRat 2 (a:ℚ) < padicValRat 2 (b:ℚ) := by
    simpa using (show (padicValNat 2 a : ℤ) < padicValNat 2 b by exact_mod_cast h)
  have hh := padicValRat.add_eq_of_lt (p:=2)
    (q:=(a:ℚ)) (r:=(b:ℚ)) (by positivity) (by positivity) (by positivity) hv
  simpa only [← Nat.cast_add, padicValRat.of_nat, Nat.cast_inj] using hh

lemma odd_quotient {a : ℕ} (ha : 0 < a) :
    Odd (a / 2 ^ padicValNat 2 a) := by
  have hd : 2 ^ padicValNat 2 a ∣ a :=
    (padicValNat_dvd_iff_le ha.ne').mpr le_rfl
  have hp : 0 < a / 2 ^ padicValNat 2 a :=
    Nat.div_pos (Nat.le_of_dvd ha hd) (by positivity)
  have hv : padicValNat 2 (a / 2 ^ padicValNat 2 a) = 0 := by
    rw [padicValNat.div_pow hd, Nat.sub_self]
  have hn : ¬ 2 ∣ a / 2 ^ padicValNat 2 a := by
    intro hd'
    have hh := one_le_padicValNat_of_dvd hp.ne' hd'
    omega
  exact Nat.not_even_iff_odd.mp (by simpa only [even_iff_two_dvd] using hn)

lemma val_add_of_eq {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (he : padicValNat 2 a = padicValNat 2 b) :
    padicValNat 2 a < padicValNat 2 (a+b) := by
  let e := padicValNat 2 a
  have hda : 2^e ∣ a := (padicValNat_dvd_iff_le ha.ne').mpr le_rfl
  have hdb : 2^e ∣ b := (padicValNat_dvd_iff_le hb.ne').mpr he.le
  have hao : Odd (a/2^e) := odd_quotient ha
  have hbo : Odd (b/2^e) := by simpa only [e,he] using odd_quotient hb
  have hs : 2 ∣ a/2^e + b/2^e := (hao.add_odd hbo).two_dvd
  have hd : 2^(e+1) ∣ a+b := by
    rw [pow_succ]
    have hh := Nat.mul_dvd_mul_left (2^e) hs
    simpa only [Nat.mul_add, Nat.mul_div_cancel' hda, Nat.mul_div_cancel' hdb] using hh
  have hh := (padicValNat_dvd_iff_le (show a+b≠0 by omega)).mp hd
  change e < padicValNat 2 (a+b)
  omega

def weighted (a t : ℕ) : ℕ := ∑ j ∈ range t, (j+1)*a^j
def geometric (a t : ℕ) : ℕ := ∑ j ∈ range t, a^j

lemma weighted_pos {a t : ℕ} (ht : 0 < t) : 0 < weighted a t := by
  apply sum_pos' (fun _ _ => Nat.zero_le _)
  exact ⟨0,mem_range.mpr ht,by simp⟩

lemma geometric_pos {a t : ℕ} (ht : 0 < t) : 0 < geometric a t := by
  apply sum_pos' (fun _ _ => Nat.zero_le _)
  exact ⟨0,mem_range.mpr ht,by simp⟩

lemma weighted_double (a t : ℕ) :
    weighted a (2*t) + geometric (a^2) t = 2*(a+1)*weighted (a^2) t := by
  induction t with
  | zero => simp [weighted,geometric]
  | succ t ih =>
    have hw (x n : ℕ) : weighted x (n+1) = weighted x n+(n+1)*x^n := by
      simp [weighted,sum_range_succ]
    have hg (x n : ℕ) : geometric x (n+1) = geometric x n+x^n := by
      simp [geometric,sum_range_succ]
    rw [show 2*(t+1)=2*t+1+1 by omega,hw,hw,hg,hw]
    rw [pow_add,pow_one,←pow_mul]
    nlinarith only [ih]

lemma val_odd {a : ℕ} (ha : a%2=1) : padicValNat 2 a = 0 := by
  exact padicValNat.eq_zero_of_not_dvd (by omega)

lemma val_mod_four {a : ℕ} (ha : a%4=2) : padicValNat 2 a = 1 := by
  have hp : a≠0 := by omega
  have hlow : 1 ≤ padicValNat 2 a := one_le_padicValNat_of_dvd hp (by omega)
  have hhigh : ¬ 2 ≤ padicValNat 2 a := by
    intro h
    have hh := (padicValNat_dvd_iff_le hp).mpr h
    norm_num only [pow_succ,pow_one] at hh
    omega
  omega

lemma geometric_mod_two {a : ℕ} (ha : a%2=1) (t : ℕ) :
    geometric a t % 2 = t%2 := by
  induction t with
  | zero => simp [geometric]
  | succ t ih =>
    simp only [geometric,sum_range_succ] at *
    rw [Nat.add_mod,ih,Nat.pow_mod,ha,one_pow]
    omega

lemma geometric_double (a t : ℕ) :
    geometric a (2*t) = (a^t+1)*geometric a t := by
  unfold geometric
  rw [show 2*t=t+t by omega,sum_range_add]
  simp only [pow_add]
  rw [←mul_sum]
  ring

lemma geometric_val {a : ℕ} (ha : a%4=1) {t : ℕ} (ht : 0 < t) :
    padicValNat 2 (geometric a t) = padicValNat 2 t := by
  induction t using Nat.strong_induction_on with
  | h t ih =>
    by_cases he : t%2=1
    · rw [val_odd he]
      exact val_odd (by simpa only [he] using geometric_mod_two (a:=a) (by omega) t)
    · have ht0 : t%2=0 := by omega
      let r := t/2
      have hr : 0 < r := by dsimp [r]; omega
      have heq : t=2*r := by dsimp [r]; omega
      have hrlt : r < t := by omega
      have hm : (a^r+1)%4=2 := by
        rw [Nat.add_mod,Nat.pow_mod,ha,one_pow]
        norm_num
      have hh := ih r hrlt hr
      rw [heq,geometric_double,
        padicValNat.mul (by omega : a^r+1≠0) (geometric_pos hr).ne',
        val_mod_four hm,hh,
        padicValNat.mul (by decide : 2≠0) hr.ne',padicValNat_self]

lemma square_mod_four {a : ℕ} (ha : Odd a) : a^2%4=1 := by
  have ham : a%2=1 := Nat.odd_iff.mp ha
  have h : a%4=1 ∨ a%4=3 := by omega
  rw [Nat.pow_mod]
  rcases h with h|h <;> norm_num [h]

lemma val_left_of_sum_gt {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (h : padicValNat 2 b < padicValNat 2 (a+b)) :
    padicValNat 2 a = padicValNat 2 b := by
  rcases lt_trichotomy (padicValNat 2 a) (padicValNat 2 b) with hl|he|hg
  · have hh := val_add_of_lt ha hb hl
    omega
  · exact he
  · have hh := val_add_of_lt hb ha hg
    rw [add_comm] at hh
    omega

lemma val_left_of_sum_lt {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (h : padicValNat 2 (a+b) < padicValNat 2 b) :
    padicValNat 2 a = padicValNat 2 (a+b) := by
  rcases lt_trichotomy (padicValNat 2 a) (padicValNat 2 b) with hl|he|hg
  · exact (val_add_of_lt ha hb hl).symm
  · have hh := val_add_of_eq ha hb he
    omega
  · have hh := val_add_of_lt hb ha hg
    rw [add_comm] at hh
    omega

lemma val_left_of_sum_eq {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (h : padicValNat 2 (a+b) = padicValNat 2 b) :
    padicValNat 2 b < padicValNat 2 a := by
  rcases lt_trichotomy (padicValNat 2 a) (padicValNat 2 b) with hl|he|hg
  · have hh := val_add_of_lt ha hb hl
    omega
  · have hh := val_add_of_eq ha hb he
    omega
  · exact hg

lemma weighted_double_val {a r : ℕ} (ha : Odd a) (hr : 0 < r)
    (hsmall : padicValNat 2 (weighted (a^2) r)+1 =
      padicValNat 2 r + padicValNat 2 (r+1)) :
    padicValNat 2 (weighted a (2*r)) = padicValNat 2 r := by
  have heven : 2 ∣ a+1 := ha.add_odd (by decide : Odd (1:ℕ)) |>.two_dvd
  have hlow : 1 ≤ padicValNat 2 (a+1) :=
    one_le_padicValNat_of_dvd (by omega) heven
  have hg := geometric_val (square_mod_four ha) hr
  have hright : padicValNat 2 r < padicValNat 2 (2*(a+1)*weighted (a^2) r) := by
    rw [padicValNat.mul (by positivity) (weighted_pos hr).ne',
      padicValNat.mul (by decide : 2≠0) (by omega : a+1≠0),padicValNat_self]
    omega
  have hsum : padicValNat 2 (geometric (a^2) r) <
      padicValNat 2 (weighted a (2*r)+geometric (a^2) r) := by
    rw [hg,weighted_double]
    exact hright
  exact (val_left_of_sum_gt (weighted_pos (by omega)) (geometric_pos hr) hsum).trans hg

theorem weighted_val (a t : ℕ) (ha : Odd a) (ht : 0 < t) :
    padicValNat 2 (weighted a t)+1 = padicValNat 2 t+padicValNat 2 (t+1) := by
  induction t using Nat.strong_induction_on generalizing a with
  | h t ih =>
    by_cases hone : t=1
    · subst t
      norm_num [weighted,padicValNat_self]
    rcases Nat.mod_two_eq_zero_or_one t with he|ho
    · let r := t/2
      have hr : 0 < r := by dsimp [r]; omega
      have hrlt : r < t := by dsimp [r]; omega
      have heq : t=2*r := by dsimp [r]; omega
      have hsmall := ih r hrlt (a^2) ha.pow hr
      have hw := weighted_double_val ha hr hsmall
      rw [heq,hw,padicValNat.mul (by decide : 2≠0) hr.ne',padicValNat_self,
        val_odd (a:=2*r+1) (by omega)]
      omega
    · let r := (t+1)/2
      have hr : 0 < r := by dsimp [r]; omega
      have hrlt : r < t := by dsimp [r]; omega
      have heq : t+1=2*r := by dsimp [r]; omega
      have hsmall := ih r hrlt (a^2) ha.pow hr
      have hw := weighted_double_val ha hr hsmall
      have hs : weighted a (2*r) = weighted a t+(t+1)*a^t := by
        rw [←heq]
        simp [weighted,sum_range_succ]
      have hp : 0 < a := ha.pos
      have hvpow : padicValNat 2 (a^t)=0 := by
        rw [padicValNat.pow,val_odd (Nat.odd_iff.mp ha),mul_zero]
      have hvterm : padicValNat 2 ((t+1)*a^t)=1+padicValNat 2 r := by
        rw [padicValNat.mul (by omega : t+1≠0) (pow_ne_zero _ hp.ne'),
          hvpow,add_zero,heq,padicValNat.mul (by decide : 2≠0) hr.ne',padicValNat_self]
      have hvs : padicValNat 2 (weighted a t+(t+1)*a^t)=padicValNat 2 r := by
        rw [←hs,hw]
      have hlt : padicValNat 2 (weighted a t+(t+1)*a^t) <
          padicValNat 2 ((t+1)*a^t) := by rw [hvs,hvterm]; omega
      have hwt := (val_left_of_sum_lt (weighted_pos ht) (by positivity) hlt).trans hvs
      rw [hwt,val_odd ho,heq,padicValNat.mul (by decide : 2≠0) hr.ne',padicValNat_self]
      omega

lemma geometric_alternate (a t : ℕ) :
    geometric a (2*t) = (a+1)*geometric (a^2) t := by
  induction t with
  | zero => simp [geometric]
  | succ t ih =>
    have hg (x n : ℕ) : geometric x (n+1)=geometric x n+x^n := by
      simp [geometric,sum_range_succ]
    rw [show 2*(t+1)=2*t+1+1 by omega,hg,hg,hg,ih]
    rw [pow_add,pow_one,←pow_mul]
    ring

lemma geometric_val_odd_base {a e : ℕ} (ha : Odd a) :
    padicValNat 2 (geometric a (e+1)) = padicValNat 2 (e+1) +
      if Odd e then padicValNat 2 (a+1)-1 else 0 := by
  by_cases he : Odd e
  · let r := (e+1)/2
    have hem : e%2=1 := Nat.odd_iff.mp he
    have hr : 0 < r := by dsimp [r]; omega
    have heq : e+1=2*r := by dsimp [r]; omega
    have hap : 1 ≤ padicValNat 2 (a+1) :=
      one_le_padicValNat_of_dvd (by omega)
        ((ha.add_odd (by decide : Odd (1:ℕ))).two_dvd)
    rw [if_pos he,heq,geometric_alternate,
      padicValNat.mul (by omega : a+1≠0) (geometric_pos hr).ne',
      geometric_val (square_mod_four ha) hr,
      padicValNat.mul (by decide : 2≠0) hr.ne',padicValNat_self]
    omega
  · have hem : (e+1)%2=1 := by
      have := Nat.mod_two_eq_zero_or_one e
      have hn : e%2≠1 := fun h => he (Nat.odd_iff.mpr h)
      omega
    rw [if_neg he,val_odd hem,add_zero]
    exact val_odd (by simpa only [hem] using geometric_mod_two (Nat.odd_iff.mp ha) (e+1))

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

def moment : ArithmeticFunction ℕ :=
  (ArithmeticFunction.id.pmul (σ 0))*ArithmeticFunction.zeta

lemma moment_apply (m : ℕ) : moment m = ∑ d ∈ m.divisors, d*d.divisors.card := by
  rw [moment,ArithmeticFunction.mul_zeta_apply]
  simp only [pmul_apply,id_apply,sigma_zero_apply]

lemma moment_multiplicative : moment.IsMultiplicative :=
  (isMultiplicative_id.pmul isMultiplicative_sigma).mul isMultiplicative_zeta

lemma moment_prime (p e : ℕ) (hp : p.Prime) :
    moment (p^e) = weighted p (e+1) := by
  rw [moment_apply,Nat.sum_divisors_prime_pow hp]
  simp only [Nat.divisors_prime_pow hp,card_map,card_range,weighted]
  exact sum_congr rfl (fun _ _ => by ring)

lemma sigma_prime (p e : ℕ) (hp : p.Prime) :
    σ 1 (p^e) = geometric p (e+1) := by
  rw [sigma_apply_prime_pow hp]
  simp [geometric]

lemma val_prod (s : Finset ℕ) (f : ℕ → ℕ) (hf : ∀ p∈s, 0 < f p) :
    padicValNat 2 (∏ p∈s, f p) = ∑ p∈s, padicValNat 2 (f p) := by
  simpa only [Nat.factorization_def _ Nat.prime_two] using
    (Nat.factorization_prod_apply (p:=2) (S:=s) (g:=f) (fun p hp => (hf p hp).ne'))

lemma multiplicative_product (f : ArithmeticFunction ℕ) (hf : f.IsMultiplicative)
    {m : ℕ} (hm : m≠0) :
    f m = ∏ p∈m.primeFactors, f (p^(m.factorization p)) := by
  simpa only [Nat.prod_factorization_eq_prod_primeFactors] using
    hf.multiplicative_factorization f hm

lemma odd_factor {m p : ℕ} (hm : Odd m) (hp : p∈m.primeFactors) : Odd p := by
  have hprime := Nat.prime_of_mem_primeFactors hp
  rcases hprime.eq_two_or_odd with htwo|hodd
  · subst p
    have hd := Nat.dvd_of_mem_primeFactors hp
    have ho := Nat.odd_iff.mp hm
    omega
  · exact Nat.odd_iff.mpr hodd

lemma tau_val {m : ℕ} (hm : m≠0) :
    padicValNat 2 m.divisors.card =
      ∑ p∈m.primeFactors, padicValNat 2 (m.factorization p+1) := by
  rw [Nat.card_divisors hm,val_prod _ _ (by intro p hp; omega)]

lemma moment_valuations {m : ℕ} (hm : Odd m) :
    padicValNat 2 (moment m)+m.primeFactors.card =
      padicValNat 2 m.divisors.card+
        ∑ p∈m.primeFactors, padicValNat 2 (m.factorization p+2) := by
  have hprod : moment m = ∏ p∈m.primeFactors, weighted p (m.factorization p+1) := by
    rw [multiplicative_product moment moment_multiplicative hm.pos.ne']
    exact prod_congr rfl (fun p hp => moment_prime p _ (Nat.prime_of_mem_primeFactors hp))
  rw [hprod,val_prod _ _ (by intro p hp; exact weighted_pos (by omega)),tau_val hm.pos.ne']
  have hh := sum_congr (s₁:=m.primeFactors) rfl
    (fun p hp => weighted_val p (m.factorization p+1) (odd_factor hm hp) (by omega))
  simpa [sum_add_distrib,sum_const,nsmul_eq_mul,mul_one,Nat.add_assoc] using hh

lemma sigma_valuations {m : ℕ} (hm : Odd m) :
    padicValNat 2 (σ 1 m) = padicValNat 2 m.divisors.card+
      ∑ p∈m.primeFactors,
        if Odd (m.factorization p) then padicValNat 2 (p+1)-1 else 0 := by
  have hprod : σ 1 m = ∏ p∈m.primeFactors, geometric p (m.factorization p+1) := by
    rw [multiplicative_product (σ 1) isMultiplicative_sigma hm.pos.ne']
    exact prod_congr rfl (fun p hp => sigma_prime p _ (Nat.prime_of_mem_primeFactors hp))
  rw [hprod,val_prod _ _ (by intro p hp; exact geometric_pos (by omega)),tau_val hm.pos.ne',←sum_add_distrib]
  exact sum_congr rfl (fun p hp => geometric_val_odd_base (odd_factor hm hp))

lemma tau_pos {m : ℕ} (hm : m≠0) : 0 < m.divisors.card := by
  exact card_pos.mpr ⟨1,Nat.one_mem_divisors.mpr hm⟩

lemma moment_pos {m : ℕ} (hm : m≠0) : 0 < moment m := by
  rw [moment_apply]
  exact sum_pos' (fun _ _ => Nat.zero_le _)
    ⟨1,Nat.one_mem_divisors.mpr hm,by simp⟩

lemma sigma_pos {m : ℕ} (hm : m≠0) : 0 < σ 1 m := by
  rw [sigma_one_apply]
  exact sum_pos' (fun _ _ => Nat.zero_le _)
    ⟨1,Nat.one_mem_divisors.mpr hm,by simp⟩

theorem valuation_test (k m : ℕ) (hm : Odd m)
    (h : (k*2^(k+1)+1)*moment m + (2^(k+1)-1)*σ 1 m =
      2^(k+1)*(k+1)*(m*m.divisors.card)) :
    let E := ∑ p∈m.primeFactors, padicValNat 2 (m.factorization p+2)
    let U := ∑ p∈m.primeFactors,
      if Odd (m.factorization p) then padicValNat 2 (p+1)-1 else 0
    let H := 1+k+padicValNat 2 (k+1)
    if U < H then E=m.primeFactors.card+U
    else if H < U then E=m.primeFactors.card+H else m.primeFactors.card+H < E := by
  let P := 2^(k+1)
  let F := moment m
  let S := σ 1 m
  let T := m.divisors.card
  let A := (k*P+1)*F
  let B := (P-1)*S
  let E := ∑ p∈m.primeFactors, padicValNat 2 (m.factorization p+2)
  let U := ∑ p∈m.primeFactors,
    if Odd (m.factorization p) then padicValNat 2 (p+1)-1 else 0
  let H := 1+k+padicValNat 2 (k+1)
  change if U < H then E=m.primeFactors.card+U
    else if H < U then E=m.primeFactors.card+H else m.primeFactors.card+H < E
  have hP : 1 < P := Nat.one_lt_two_pow (by omega : k+1≠0)
  have hPmod : P%2=0 := by
    dsimp [P]
    rw [Nat.pow_mod]
    simp
  have hAodd : (k*P+1)%2=1 := by
    rw [Nat.add_mod,Nat.mul_mod,hPmod]
    simp
  have hBodd : (P-1)%2=1 := by omega
  have hF : 0 < F := moment_pos hm.pos.ne'
  have hS : 0 < S := sigma_pos hm.pos.ne'
  have hT : 0 < T := tau_pos hm.pos.ne'
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 < B := Nat.mul_pos (by omega) hS
  have hfv : padicValNat 2 F + m.primeFactors.card = padicValNat 2 T+E :=
    moment_valuations hm
  have hsv : padicValNat 2 S = padicValNat 2 T+U := sigma_valuations hm
  have hAv : padicValNat 2 A = padicValNat 2 F := by
    dsimp only [A]
    rw [padicValNat.mul (by omega : k*P+1≠0) hF.ne',val_odd hAodd,zero_add]
  have hBv : padicValNat 2 B = padicValNat 2 T+U := by
    dsimp only [B]
    rw [padicValNat.mul (by omega : P-1≠0) hS.ne',val_odd hBodd,zero_add,hsv]
  have hsum : A+B=P*(k+1)*(m*T) := h
  have hvP : padicValNat 2 P=k+1 := padicValNat.prime_pow (k+1)
  have hmv : padicValNat 2 m=0 := val_odd (Nat.odd_iff.mp hm)
  have htot : padicValNat 2 (A+B)=padicValNat 2 T+H := by
    rw [hsum,padicValNat.mul
        (mul_ne_zero (by omega : P≠0) (by omega : k+1≠0))
        (mul_ne_zero hm.pos.ne' hT.ne'),
      padicValNat.mul (by omega : P≠0) (by omega : k+1≠0),
      padicValNat.mul hm.pos.ne' hT.ne',hvP,hmv]
    dsimp only [H]
    omega
  split_ifs with hUH hHU
  · have hlt : padicValNat 2 B < padicValNat 2 (A+B) := by rw [hBv,htot]; omega
    have hh := val_left_of_sum_gt hA hB hlt
    rw [hAv,hBv] at hh
    omega
  · have hlt : padicValNat 2 (A+B) < padicValNat 2 B := by rw [hBv,htot]; omega
    have hh := val_left_of_sum_lt hA hB hlt
    rw [hAv,htot] at hh
    omega
  · have heq : padicValNat 2 (A+B)=padicValNat 2 B := by rw [hBv,htot]; omega
    have hh := val_left_of_sum_eq hA hB heq
    rw [hAv,hBv] at hh
    omega

end D7TwoAdic
open scoped ArithmeticFunction.sigma

open private OMA.R_OeisA245212_conjecture_R1_H2_R2.at_power_product
  OMA.R_OeisA245212_conjecture_R1_H2_R2.geom2
  OMA.R_OeisA245212_conjecture_R1_H2_R2.weighted2
  from OMAReductions.R_OeisA245212_conjecture_R1_H2_R2

theorem OMA.solution : OMA.R_OeisA245212_conjecture_R1_H2_R2_H2_R1.H1 := by
  intro k m hm heq
  have hh := (OMA.R_OeisA245212_conjecture_R1_H2_R2.at_power_product
    2 k m Nat.prime_two hm.pos.ne' (Nat.coprime_two_left.mpr hm)).mp heq
  rw [←D7TwoAdic.moment_apply m] at hh
  have expand :
      (∑ j∈range (k+1), ((j+1)*D7TwoAdic.moment m+σ 1 m)*2^j) =
      (∑ j∈range (k+1), 2^j*(j+1))*D7TwoAdic.moment m+
        (∑ j∈range (k+1), 2^j)*σ 1 m := by
    rw [sum_mul,sum_mul,←sum_add_distrib]
    exact sum_congr rfl (fun _ _ => by ring)
  rw [expand,OMA.R_OeisA245212_conjecture_R1_H2_R2.weighted2] at hh
  have hg := OMA.R_OeisA245212_conjecture_R1_H2_R2.geom2 k
  have hgeo : (∑ j∈range (k+1), 2^j)=2^(k+1)-1 := by omega
  rw [hgeo] at hh
  have identity : (k*2^(k+1)+1)*D7TwoAdic.moment m+(2^(k+1)-1)*σ 1 m =
      2^(k+1)*(k+1)*(m*m.divisors.card) := by
    calc
      _ = (2*m*(k+1)*m.divisors.card)*2^k := hh
      _ = _ := by rw [pow_succ]; ring
  have ht := D7TwoAdic.valuation_test k m hm identity
  have hE := Finset.sum_coe_sort m.primeFactors
    (fun p : ℕ => padicValNat 2 (m.factorization p+2))
  have hU := Finset.sum_coe_sort m.primeFactors
    (fun p : ℕ => if Odd (m.factorization p) then padicValNat 2 (p+1)-1 else 0)
  dsimp only
  simpa only [Nat.factorization_def _ Nat.prime_two,hE,hU] using ht
