import OMAStatements.S_mo_94765
import Mathlib

/-!
# Decimal digit sums of multiples

If a has fewer digits than b, put q = 10^k at the leading digit of b.
Multiplying by q + 1 creates disjoint decimal blocks for a, but a carry
for b when the leading and trailing digits add to at least ten.
The multiplier q − 1 instead detects a borrow when the trailing digit of b
is at most its leading digit. This leaves two cases below.
-/

namespace OMA.R_mo_94765_R1

open OMA.S_mo_94765

/-- Inputs of the same decimal length and equal digit sum. -/
def H1 : Prop :=
  ∀ k a b : ℕ, 10^k ≤ a → a < b → b < 10^k*10 →
    a%10 ≠ 0 → b%10 ≠ 0 → digitSum a = digitSum b →
    ∃ n : ℕ, 0 < n ∧ n < b ∧ digitSum (n*a) ≠ digitSum (n*b)

/-- Inputs of unequal length whose leading and trailing digits evade both
tests. The inequalities force the leading digit of b to be at most four. -/
def H2 : Prop :=
  ∀ k a b : ℕ, a < 10^k → 10^k ≤ b → b < 10^k*10 → a < b →
    a%10 ≠ 0 → b%10 ≠ 0 → digitSum a = digitSum b →
    b/10^k < b%10 → b%10 + b/10^k < 10 →
    ∃ n : ℕ, 0 < n ∧ n < b ∧ digitSum (n*a) ≠ digitSum (n*b)

lemma ds_split (m : ℕ) : digitSum m = digitSum (m / 10) + m % 10 := by
  by_cases h : m = 0
  · simp [h, digitSum]
  · unfold digitSum
    rw [Nat.digits_eq_cons_digits_div (by decide : 1 < 10) h, List.sum_cons, add_comm]

lemma ds_block (k u r : ℕ) (hr : r < 10^k) :
    digitSum (10^k*u+r) = digitSum u + digitSum r := by
  induction k generalizing r with
  | zero =>
    have : r = 0 := by simpa using hr
    simp [this,digitSum]
  | succ k ih =>
    let p := 10^k*u
    have hd : r/10 < 10^k := by rw [pow_succ] at hr; omega
    have val : 10^(k+1)*u+r = 10*p+r := by dsimp [p]; ring
    rw [val,ds_split (10*p+r), show (10*p+r)/10 = p+r/10 by omega,
      show (10*p+r)%10 = r%10 by omega, ih (r/10) hd, ds_split r]
    omega

lemma ds_complement (k r : ℕ) (hr : r < 10^k) :
    digitSum (10^k-1-r) + digitSum r = 9*k := by
  induction k generalizing r with
  | zero =>
    have : r = 0 := by simpa using hr
    simp [this,digitSum]
  | succ k ih =>
    rw [pow_succ] at hr ⊢
    have hd : r/10 < 10^k := by omega
    have ih' := ih (r/10) hd
    have quot : (10^k * 10 - 1 - r)/10 = 10^k - 1 - r/10 := by omega
    have rem' : (10^k * 10 - 1 - r)%10 + r%10 = 9 := by omega
    rw [ds_split (10^k * 10 - 1 - r), quot, ds_split r]
    omega

lemma ds_small (d : ℕ) (hd : d < 10) : digitSum d = d := by
  by_cases h : d = 0
  · simp [h, digitSum]
  · simp [digitSum, Nat.digits_of_lt 10 d h hd]

lemma ds_succ_le (x : ℕ) : digitSum (x + 1) ≤ digitSum x + 1 := by
  induction x using Nat.strong_induction_on with
  | h x ih =>
    by_cases zero : x = 0
    · subst x
      decide
    rw [ds_split (x+1), ds_split x]
    by_cases nine : x % 10 = 9
    · have smaller : x / 10 < x := by omega
      have inc := ih (x / 10) smaller
      rw [show (x+1)/10 = x/10 + 1 by omega]
      omega
    · rw [show (x+1)/10 = x/10 by omega]
      omega

lemma ds_carry (x d : ℕ) (hd : d < 10) (hc : 10 ≤ x % 10 + d) :
    digitSum (x+d) < digitSum x + d := by
  rw [ds_split (x+d), ds_split x, show (x+d)/10 = x/10 + 1 by omega]
  have inc := ds_succ_le (x/10)
  omega

lemma ds_plus_sep (k a b d r : ℕ) (ha : a < 10^k) (hb : b = 10^k*d+r)
    (hr : r < 10^k) (hd : d < 10) (hcarry : 10 ≤ b%10+d)
    (heq : digitSum a = digitSum b) :
    digitSum ((10^k+1)*a) ≠ digitSum ((10^k+1)*b) := by
  have leftProduct : (10^k+1)*a = 10^k*a+a := by ring
  have rightProduct : (10^k+1)*b = 10^k*(b+d)+r := by
    calc
      (10^k+1)*b = 10^k*b+b := by ring
      _ = 10^k*b+(10^k*d+r) := congrArg (10^k*b+·) hb
      _ = 10^k*(b+d)+r := by ring
  have base : digitSum b = d + digitSum r := by
    rw [hb, ds_block k d r hr, ds_small d hd]
  have dec := ds_carry b d hd hcarry
  rw [leftProduct, rightProduct, ds_block k a a ha, ds_block k (b+d) r hr]
  omega

lemma ds_minus_sep (k a b d r : ℕ) (ha0 : 0 < a) (ha : a < 10^k)
    (hb : b = 10^k*d+r) (hr0 : 0 < r) (hr : r < 10^k)
    (hd : d < 10) (hlast : 0 < b % 10) (hborrow : b%10 ≤ d) :
    digitSum ((10^k-1)*a) ≠ digitSum ((10^k-1)*b) := by
  let q := 10^k
  change a < q at ha
  change r < q at hr
  change b = q*d+r at hb
  have hq : 1 ≤ q := by omega
  have eqA : (q-1)*a = q*(a-1)+(q-1-(a-1)) := by
    have h₁ : q - 1 + 1 = q := by omega
    have h₂ : a - 1 + 1 = a := by omega
    have h₃ : q-1-(a-1) + a = q := by omega
    nlinarith only [congrArg (fun m : ℕ => m*a) h₁, congrArg (fun m : ℕ => q*m) h₂, h₃]
  have hA : digitSum ((q-1)*a) = 9*k := by
    rw [eqA, ds_block k _ _ (show q-1-(a-1) < q by omega)]
    have hc := ds_complement k (a-1) (by change a-1 < q; omega)
    exact (Nat.add_comm _ _).trans hc
  let j := b-1-d
  have db : d < b := by nlinarith [Nat.mul_le_mul_right d hq]
  have hj : j+d+1=b := by dsimp [j]; omega
  have eqB : (q-1)*b = q*j+(q-1-(r-1)) := by
    have h₁ : q-1+1=q := by omega
    have h₂ : q-1-(r-1)+r=q := by omega
    nlinarith only [congrArg (fun m : ℕ => m*b) h₁, congrArg (fun m : ℕ => q*m) hj, hb, h₂]
  have hT : digitSum (b-1) = d+digitSum (r-1) := by
    have h : b-1 = q*d+(r-1) := by omega
    rw [h, ds_block k d (r-1) (show r-1<q by omega), ds_small _ hd]
  have hjc : 10 ≤ j%10+d := by omega
  have hC := ds_carry j d hd hjc
  rw [show j+d=b-1 by omega, hT] at hC
  have hc := ds_complement k (r-1) (by change r-1<q; omega)
  change digitSum ((q-1)*a) ≠ digitSum ((q-1)*b)
  rw [hA,eqB,ds_block k j _ (show q-1-(r-1)<q by omega)]
  change digitSum (q-1-(r-1)) + digitSum (r-1) = 9*k at hc
  omega

theorem main : H1 → H2 → type_of% @OMA.S_mo_94765.main := by
  intro sameLength separated a b hab ha10 hb10
  have ha0 : 0 < a := by omega
  by_cases hs : digitSum a = digitSum b
  · let k := Nat.log 10 b
    let q := 10^k
    have hq : q ≤ b := Nat.pow_log_le_self _ (by omega)
    have hbq : b < q*10 := by
      simpa only [q, k, pow_succ] using Nat.lt_pow_succ_log_self (by decide : 1 < 10) b
    by_cases haq : q ≤ a
    · exact sameLength k a b haq hab hbq ha10 hb10 hs
    · have haq' : a < q := by omega
      have hk : 0 < k := by
        by_contra! h
        have hk0 : k=0 := by omega
        have : q = 1 := by simp [q,hk0]
        omega
      have hdiv : 10 ∣ q := by
        obtain ⟨j,hj⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
        exact ⟨10^j,by simp only [q,hj,pow_succ,Nat.mul_comm]⟩
      have hq10 : q % 10 = 0 := Nat.mod_eq_zero_of_dvd hdiv
      have hq0 : 0 < q := by omega
      let d := b/q
      let r := b%q
      have hb : b = q*d+r := (Nat.div_add_mod b q).symm
      have hr : r < q := Nat.mod_lt _ hq0
      have hd : d < 10 := (Nat.div_lt_iff_lt_mul hq0).mpr (by simpa [Nat.mul_comm] using hbq)
      have hr0 : 0 < r := by
        by_contra! h
        have hz : r=0 := by omega
        have : 10 ∣ b := by rw [hb,hz,add_zero]; exact dvd_mul_of_dvd_left hdiv d
        exact hb10 (Nat.mod_eq_zero_of_dvd this)
      by_cases borrow : b%10 ≤ d
      · exact ⟨q-1,by omega,by omega,ds_minus_sep k a b d r ha0 haq' hb hr0 hr hd
          (by omega) borrow⟩
      by_cases carry : 10 ≤ b%10+d
      · have hnb : q+1 < b := by
          by_contra! h
          have he : b = q ∨ b = q+1 := by omega
          rcases he with he | he
          · exact hb10 (he ▸ hq10)
          · have hlt : b < q*2 := by omega
            have hdl : d < 2 := (Nat.div_lt_iff_lt_mul hq0).mpr (by simpa [Nat.mul_comm] using hlt)
            omega
        exact ⟨q+1,by omega,hnb,ds_plus_sep k a b d r haq' hb hr hd carry hs⟩
      · exact separated k a b haq' hq hbq hab ha10 hb10 hs
          (Nat.lt_of_not_ge borrow) (Nat.lt_of_not_ge carry)
  · exact ⟨1,by decide,by omega,by simpa only [one_mul] using hs⟩

end OMA.R_mo_94765_R1
