import OMAReductions.R_Erdos649_erdos_649_variants_tong_question_R1_H2_R1
import Mathlib.NumberTheory.Pell
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Data.Nat.Squarefree
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
import Mathlib.Data.Int.NatAbs
import Mathlib.Data.Nat.Factorization.Basic

/-!
# Primitive divisors of positive Pell powers

Credit: @steveDOTdigital, parent reduction #6917.
This is a known specialization of Carmichael's primitive-divisor theorem.
The cyclotomic size strategy is from Minoru Yabuta, "A Simple Proof of
Carmichael's Theorem on Primitive Divisors", Fibonacci Quarterly 39(5)
(2001), 439–443, DOI 10.1080/00150517.2001.12428701 (refereed).

The norm of Phi_n(u^2) has size at least 12^phi(n). If all prime divisors
of the nth y-coordinate occur earlier, exact lifting and comparison of
divisor products force that norm to divide rad(n)^2. Euler's theorem
shows rad(n)^2 < 12^phi(n) for n>2.
-/


/- Research helpers for the Pell primitive-divisor step. Not a submission. -/

namespace PellPrimitiveDivisor.Arithmetic

open Pell

lemma y_dvd_power {D : ℤ} (u : Solution₁ D) (n : ℕ) : u.y ∣ (u ^ n).y := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Solution₁.y_mul]
    exact dvd_add (dvd_mul_left _ _) (dvd_mul_of_dvd_left ih _)

lemma odd_lt_two_pow_totient (m : ℕ) (hm : Odd m) (hpos : 0 < m) :
    m < 2 ^ m.totient := by
  have hc : Nat.Coprime 2 m := Nat.coprime_two_left.mpr hm
  have hp : 1 < 2 ^ m.totient :=
    one_lt_pow₀ (by decide) (Nat.totient_pos.mpr hpos).ne'
  have hd : m ∣ 2 ^ m.totient - 1 :=
    (Nat.modEq_iff_dvd' hp.le).mp (Nat.ModEq.pow_totient hc).symm
  have := Nat.le_of_dvd (by omega : 0 < 2 ^ m.totient - 1) hd
  omega

lemma odd_divisor_growth (n m : ℕ) (hn : 2 < n) (hm : Odd m)
    (hpos : 0 < m) (hd : m ∣ n) :
    2 * m < 12 ^ (n.totient / 2) := by
  have ht : m.totient ≤ n.totient :=
    Nat.le_of_dvd (Nat.totient_pos.mpr (by omega)) (Nat.totient_dvd_of_dvd hd)
  have hbound : m < 2 ^ n.totient :=
    (odd_lt_two_pow_totient m hm hpos).trans_le
      (Nat.pow_le_pow_right (by decide) ht)
  obtain ⟨k, hk⟩ := Nat.totient_even hn
  have hkpos : 0 < k := by
    have := Nat.totient_pos.mpr (show 0 < n by omega)
    omega
  have hphi : n.totient = 2 * k := by omega
  have h3 : 2 < 3 ^ k := by
    have := Nat.pow_le_pow_right (by decide : 0 < 3) (show 1 ≤ k by omega)
    simpa using lt_of_lt_of_le (by decide : 2 < 3 ^ 1) this
  have hlarge : 2 * 2 ^ n.totient < 12 ^ (n.totient / 2) := by
    rw [hphi, show 2 * k / 2 = k by omega, pow_mul]
    norm_num
    calc
      2 * 4 ^ k < 3 ^ k * 4 ^ k := Nat.mul_lt_mul_of_pos_right h3 (by positivity)
      _ = 12 ^ k := by rw [← mul_pow]; norm_num
  exact (Nat.mul_lt_mul_of_pos_left hbound (by decide : 0 < 2)).trans hlarge

lemma rank_divides {D : ℤ} (u : Solution₁ D) {p k n : ℕ} (hp : p.Prime)
    (hk : 0 < k) (hyk : p ∣ (u ^ k).y.natAbs)
    (hfirst : ∀ j : ℕ, 0 < j → j < k → ¬ p ∣ (u ^ j).y.natAbs) :
    p ∣ (u ^ n).y.natAbs ↔ k ∣ n := by
  letI : Fact p.Prime := ⟨hp⟩
  have to_mod (j : ℕ) : p ∣ (u ^ j).y.natAbs ↔ ((u ^ j).y : ZMod p) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact Int.natCast_dvd.symm
  have hq : ((u ^ (k * (n / k))).y : ZMod p) = 0 := by
    apply (to_mod _).mp
    rw [pow_mul]
    exact hyk.trans (Int.natAbs_dvd_natAbs.mpr (y_dvd_power (u ^ k) (n / k)))
  have hx : ((u ^ (k * (n / k))).x : ZMod p) ≠ 0 := by
    have he := congrArg (fun a : ℤ => (a : ZMod p)) (u ^ (k * (n / k))).prop
    push_cast at he
    rw [hq] at he
    intro hz
    simp [hz] at he
  have hn : ((u ^ n).y : ZMod p) = 0 ↔ ((u ^ (n % k)).y : ZMod p) = 0 := by
    nth_rw 1 [← Nat.mod_add_div n k]
    rw [pow_add, Solution₁.y_mul]
    push_cast
    simp only [hq, mul_zero, zero_add, mul_eq_zero, hx, or_false]
  constructor
  · intro hy
    have hm := (to_mod _).mpr (hn.mp ((to_mod _).mp hy))
    have hzero : n % k = 0 := by
      by_contra hz
      exact hfirst _ (Nat.pos_of_ne_zero hz) (Nat.mod_lt _ hk) hm
    exact Nat.dvd_of_mod_eq_zero hzero
  · intro hd
    have hm : ((u ^ (n % k)).y : ZMod p) = 0 := by
      rw [Nat.mod_eq_zero_of_dvd hd]
      simp
    exact (to_mod _).mpr (hn.mpr hm)

lemma x_power_congr {D : ℤ} (u : Solution₁ D) (n : ℕ) :
    u.y ^ 2 ∣ (u ^ n).x - u.x ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨a, ha⟩ := y_dvd_power u n
    obtain ⟨b, hb⟩ := ih
    refine ⟨b * u.x + D * a, ?_⟩
    rw [pow_succ, Solution₁.x_mul, pow_succ]
    linear_combination u.x * hb + D * u.y * ha

lemma y_power_linear_congr {D : ℤ} (u : Solution₁ D) (n : ℕ) :
    u.y ^ 3 ∣ (u ^ (n + 1)).y - (n + 1 : ℕ) * u.x ^ n * u.y := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨a, ha⟩ := x_power_congr u (n + 1)
    obtain ⟨b, hb⟩ := ih
    refine ⟨a + b * u.x, ?_⟩
    rw [show n.succ + 1 = (n + 1) + 1 by omega, pow_succ, Solution₁.y_mul]
    push_cast at ha hb ⊢
    rw [pow_succ]
    simp only [pow_succ] at ha hb
    linear_combination u.y * ha + u.x * hb

lemma x_coprime_prime_of_y_dvd {D : ℤ} (u : Solution₁ D) {p : ℕ}
    (hp : p.Prime) (hy : (p : ℤ) ∣ u.y) : IsCoprime (p : ℤ) u.x := by
  have hpz := Nat.prime_iff_prime_int.mp hp
  apply hpz.coprime_iff_not_dvd.mpr
  intro hx
  apply hpz.not_dvd_one
  rw [← u.prop]
  exact dvd_sub (hx.pow (by decide : 2 ≠ 0))
    (dvd_mul_of_dvd_right (hy.pow (by decide : 2 ≠ 0)) D)

lemma prime_power_y_step {D : ℤ} (u : Solution₁ D) {p a : ℕ}
    (hp : p.Prime) (ha : 0 < a) (hy : (p : ℤ) ^ a ∣ u.y)
    (hy' : ¬ (p : ℤ) ^ (a + 1) ∣ u.y) :
    (p : ℤ) ^ (a + 1) ∣ (u ^ p).y ∧
      ¬ (p : ℤ) ^ (a + 2) ∣ (u ^ p).y := by
  have hpz := Nat.prime_iff_prime_int.mp hp
  have hpy : (p : ℤ) ∣ u.y := by
    have h := (pow_dvd_pow (p : ℤ) (show 1 ≤ a by omega)).trans hy
    simpa only [pow_one] using h
  have hx := x_coprime_prime_of_y_dvd u hp hpy
  have hrem := y_power_linear_congr u (p - 1)
  rw [Nat.sub_add_cancel hp.one_le] at hrem
  have hcube : (p : ℤ) ^ (a * 3) ∣ u.y ^ 3 := by
    simpa [pow_mul] using pow_dvd_pow_of_dvd hy 3
  have hd : (p : ℤ) ^ (a + 2) ∣
      (u ^ p).y - (p : ℤ) * u.x ^ (p - 1) * u.y :=
    ((pow_dvd_pow _ (by omega : a + 2 ≤ a * 3)).trans hcube).trans hrem
  have hl : (p : ℤ) ^ (a + 1) ∣ (p : ℤ) * u.x ^ (p - 1) * u.y := by
    simpa [pow_succ', mul_assoc] using
      mul_dvd_mul_left (p : ℤ) (dvd_mul_of_dvd_right hy (u.x ^ (p - 1)))
  have hnl : ¬ (p : ℤ) ^ (a + 2) ∣ (p : ℤ) * u.x ^ (p - 1) * u.y := by
    intro h
    have hh : (p : ℤ) ^ (a + 1) ∣ u.x ^ (p - 1) * u.y := by
      apply (mul_dvd_mul_iff_left hpz.ne_zero).mp
      simpa [pow_succ', mul_assoc] using h
    exact hy' (((hx.pow_right (n := p - 1)).pow_left (m := a + 1)).dvd_of_dvd_mul_left hh)
  constructor
  · have hd' := (pow_dvd_pow (p : ℤ) (show a + 1 ≤ a + 2 by omega)).trans hd
    simpa only [sub_add_cancel] using dvd_add hd' hl
  · intro h
    apply hnl
    have hh := dvd_sub h hd
    simpa only [sub_sub_cancel] using hh

lemma coprime_power_y_step {D : ℤ} (u : Solution₁ D) {p a n : ℕ}
    (hp : p.Prime) (ha : 0 < a) (hy : (p : ℤ) ^ a ∣ u.y)
    (hy' : ¬ (p : ℤ) ^ (a + 1) ∣ u.y) (hn : 0 < n) (hnp : ¬ p ∣ n) :
    (p : ℤ) ^ a ∣ (u ^ n).y ∧ ¬ (p : ℤ) ^ (a + 1) ∣ (u ^ n).y := by
  have hpz := Nat.prime_iff_prime_int.mp hp
  have hpy : (p : ℤ) ∣ u.y := by
    have h := (pow_dvd_pow (p : ℤ) (show 1 ≤ a by omega)).trans hy
    simpa only [pow_one] using h
  have hx := x_coprime_prime_of_y_dvd u hp hpy
  have hc : IsCoprime (p : ℤ) ((n : ℤ) * u.x ^ (n - 1)) :=
    (hpz.coprime_iff_not_dvd.mpr (by exact_mod_cast hnp)).mul_right hx.pow_right
  have hrem := y_power_linear_congr u (n - 1)
  rw [Nat.sub_add_cancel hn] at hrem
  have hcube : (p : ℤ) ^ (a * 3) ∣ u.y ^ 3 := by
    simpa [pow_mul] using pow_dvd_pow_of_dvd hy 3
  have hd : (p : ℤ) ^ (a + 1) ∣
      (u ^ n).y - (n : ℤ) * u.x ^ (n - 1) * u.y :=
    ((pow_dvd_pow _ (by omega : a + 1 ≤ a * 3)).trans hcube).trans hrem
  constructor
  · have hd' := (pow_dvd_pow (p : ℤ) (show a ≤ a + 1 by omega)).trans hd
    simpa only [sub_add_cancel] using
      dvd_add hd' (dvd_mul_of_dvd_right hy ((n : ℤ) * u.x ^ (n - 1)))
  · intro h
    apply hy'
    apply (hc.pow_left (m := a + 1)).dvd_of_dvd_mul_left
    have hh := dvd_sub h hd
    simpa only [sub_sub_cancel] using hh

lemma power_y_exact {D : ℤ} (u : Solution₁ D) {p a : ℕ}
    (hp : p.Prime) (ha : 0 < a) (hy : (p : ℤ) ^ a ∣ u.y)
    (hy' : ¬ (p : ℤ) ^ (a + 1) ∣ u.y) (n : ℕ) (hn : 0 < n) :
    (p : ℤ) ^ (a + padicValNat p n) ∣ (u ^ n).y ∧
      ¬ (p : ℤ) ^ (a + padicValNat p n + 1) ∣ (u ^ n).y := by
  letI : Fact p.Prime := ⟨hp⟩
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hd : p ∣ n
    · obtain ⟨m, rfl⟩ := hd
      have hm : 0 < m := by
        by_contra hz
        have hm0 : m = 0 := by omega
        simp only [hm0, mul_zero, lt_self_iff_false] at hn
      have hmn : m < p * m := by nlinarith [hp.two_le]
      have hi := ih m hmn hm
      have hs := prime_power_y_step (u ^ m) hp (by omega : 0 < a + padicValNat p m)
        hi.1 hi.2
      rw [← pow_mul, mul_comm m p] at hs
      rw [padicValNat.mul hp.ne_zero hm.ne', padicValNat_self]
      simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hs
    · rw [padicValNat.eq_zero_of_not_dvd hd, add_zero]
      exact coprime_power_y_step u hp ha hy hy' hn hd

lemma padicVal_y_power {D : ℤ} (u : Solution₁ D) {p : ℕ}
    (hp : p.Prime) (hy : (p : ℤ) ∣ u.y) (hy0 : u.y ≠ 0)
    (n : ℕ) (hn : 0 < n) :
    padicValInt p (u ^ n).y = padicValInt p u.y + padicValNat p n := by
  letI : Fact p.Prime := ⟨hp⟩
  let a := padicValInt p u.y
  have ha : 0 < a := by
    have hd : (p : ℤ) ^ 1 ∣ u.y := by simpa only [pow_one] using hy
    have hh := (padicValInt_dvd_iff 1 u.y).mp hd
    rcases hh with h | h
    · exact (hy0 h).elim
    · exact h
  have hnot : ¬ (p : ℤ) ^ (a + 1) ∣ u.y := by
    intro hd
    have hh := (padicValInt_dvd_iff (a + 1) u.y).mp hd
    rcases hh with h | h
    · exact hy0 h
    · change a + 1 ≤ a at h
      omega
  have he := power_y_exact u hp ha (padicValInt_dvd u.y) hnot n hn
  have hz : (u ^ n).y ≠ 0 := by
    intro hz
    exact he.2 (hz ▸ dvd_zero _)
  have hlo := ((padicValInt_dvd_iff _ _).mp he.1).resolve_left hz
  have hhi : ¬ a + padicValNat p n + 1 ≤ padicValInt p (u ^ n).y := by
    intro h
    exact he.2 ((padicValInt_dvd_iff _ _).mpr (Or.inr h))
  change padicValInt p (u ^ n).y = a + padicValNat p n
  omega

def primeRadical (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors, p

lemma divisor_sum_step (g : ℕ → ℕ) {m n : ℕ} (hn : n ≠ 0)
    (hd : m ∣ n) (hlt : m < n) :
    g n + (∑ d ∈ m.divisors, g d) ≤ ∑ d ∈ n.divisors, g d := by
  have hnot : n ∉ m.divisors := fun h => (Nat.divisor_le h).not_gt hlt
  have hsub : insert n m.divisors ⊆ n.divisors := by
    apply Finset.insert_subset
    · exact Nat.mem_divisors.mpr ⟨dvd_rfl, hn⟩
    · exact Nat.divisors_subset_of_dvd hn hd
  simpa only [Finset.sum_insert hnot] using
    Finset.sum_le_sum_of_subset hsub (f := g)

lemma factorization_bound_of_old {D : ℤ} (u : Solution₁ D) (hu : IsFundamental u)
    (C : ℕ → ℕ) (K : ℕ)
    (hsum : ∀ p : ℕ, p.Prime → ∀ t : ℕ, 0 < t →
      (∑ d ∈ t.divisors, (C d).factorization p) =
        K.factorization p + 2 * padicValInt p (u ^ t).y)
    (n : ℕ) (hn : 2 < n)
    (hold : ∀ p : ℕ, p.Prime → p ∣ (u ^ n).y.natAbs →
      ∃ j : ℕ, 0 < j ∧ j < n ∧ p ∣ (u ^ j).y.natAbs)
    (p : ℕ) (hp : p.Prime) :
    (C n).factorization p ≤ if p ∣ n then 2 else 0 := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  by_cases hyn : p ∣ (u ^ n).y.natAbs
  · have hex : ∃ r : ℕ, 0 < r ∧ p ∣ (u ^ r).y.natAbs := ⟨n, by omega, hyn⟩
    let r := Nat.find hex
    have hr : 0 < r := (Nat.find_spec hex).1
    have hyr : p ∣ (u ^ r).y.natAbs := (Nat.find_spec hex).2
    have hfirst : ∀ j : ℕ, 0 < j → j < r → ¬ p ∣ (u ^ j).y.natAbs := by
      intro j hj hjr hyj
      exact Nat.find_min hex hjr ⟨hj, hyj⟩
    have hrn : r ∣ n := (rank_divides u hp hr hyr hfirst).mp hyn
    obtain ⟨j, hj, hjn, hyj⟩ := hold p hp hyn
    have hrlt : r < n := (Nat.find_min' hex ⟨hj, hyj⟩).trans_lt hjn
    have hquot : n / r ≠ 1 := by
      intro h
      have he := Nat.mul_div_cancel' hrn
      rw [h, mul_one] at he
      omega
    obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd hquot
    obtain ⟨s, hs⟩ := hqd
    let m := r * s
    have hnm : n = q * m := by
      have he := Nat.mul_div_cancel' hrn
      rw [hs] at he
      dsimp [m]
      nlinarith only [he]
    have hm : 0 < m := by
      by_contra h
      have hm0 : m = 0 := by omega
      rw [hm0, mul_zero] at hnm
      omega
    have hmn : m < n := by rw [hnm]; nlinarith [hq.two_le]
    have hmd : m ∣ n := ⟨q, by rw [hnm]; ring⟩
    have hym : p ∣ (u ^ m).y.natAbs :=
      (rank_divides u hp hr hyr hfirst).mpr ⟨s, rfl⟩
    have hym0 : (u ^ m).y ≠ 0 := by
      have hypos := Solution₁.y_pow_succ_pos hu.x_pos hu.2.1 (m - 1)
      simp only [Nat.succ_eq_add_one, Nat.sub_add_cancel hm] at hypos
      exact hypos.ne'
    have he := padicVal_y_power (u ^ m) hp (Int.natCast_dvd.mpr hym) hym0 q hq.pos
    rw [← pow_mul, mul_comm m q, ← hnm] at he
    have hb := divisor_sum_step (fun t => (C t).factorization p) (by omega : n ≠ 0) hmd hmn
    rw [hsum p hp m hm, hsum p hp n (by omega)] at hb
    have hbound : (C n).factorization p ≤ 2 * padicValNat p q := by omega
    by_cases hqp : q = p
    · have hpn : p ∣ n := ⟨m, by simpa only [hqp] using hnm⟩
      rw [if_pos hpn]
      simpa only [hqp, padicValNat_self, mul_one] using hbound
    · have hnpq : ¬ p ∣ q := by
        intro hd
        rcases (Nat.dvd_prime hq).mp hd with h | h
        · exact hp.ne_one h
        · exact hqp h.symm
      rw [padicValNat.eq_zero_of_not_dvd hnpq, mul_zero] at hbound
      split_ifs <;> omega
  · have hb := divisor_sum_step (fun t => (C t).factorization p) (by omega : n ≠ 0)
      (one_dvd n) (by omega : 1 < n)
    rw [hsum p hp 1 (by decide), hsum p hp n (by omega)] at hb
    have he : padicValInt p (u ^ n).y = 0 := padicValNat.eq_zero_of_not_dvd hyn
    rw [he, mul_zero, add_zero] at hb
    split_ifs <;> omega

lemma radical_growth (n : ℕ) (hn : 2 < n) :
    (primeRadical n) ^ 2 < 12 ^ n.totient := by
  let m := ∏ p ∈ n.primeFactors.erase 2, p
  have hc : Nat.Coprime 2 m := by
    apply Nat.Coprime.prod_right
    intro p hp
    exact (Nat.coprime_primes Nat.prime_two
      (Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hp))).mpr
        (Finset.ne_of_mem_erase hp).symm
  have hm : Odd m := Nat.coprime_two_left.mp hc
  have hd : m ∣ n :=
    (Finset.prod_dvd_prod_of_subset _ _ id (Finset.erase_subset _ _)).trans
      (Nat.prod_primeFactors_dvd n)
  have hrad : primeRadical n ≤ 2 * m := by
    by_cases h2 : 2 ∈ n.primeFactors
    · have he : m * 2 = primeRadical n := Finset.prod_erase_mul _ _ h2
      omega
    · have he : m = primeRadical n := by simp only [m, Finset.erase_eq_of_notMem h2, primeRadical]
      omega
  have hb := hrad.trans_lt (odd_divisor_growth n m hn hm hm.pos hd)
  obtain ⟨k, hk⟩ := Nat.totient_even hn
  have hphi : n.totient = 2 * k := by omega
  rw [hphi, show 2 * k / 2 = k by omega] at hb
  have hh : primeRadical n ^ 2 < (12 ^ k) ^ 2 := by nlinarith
  simpa only [← pow_mul, hphi, Nat.mul_comm k 2] using hh

lemma primeRadical_nonzero (n : ℕ) : primeRadical n ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  exact (Nat.prime_of_mem_primeFactors hp).ne_zero

lemma primeRadical_factorization (n p : ℕ) :
    (primeRadical n).factorization p = if p ∈ n.primeFactors then 1 else 0 := by
  unfold primeRadical
  rw [Nat.factorization_prod_apply (fun q hq => (Nat.prime_of_mem_primeFactors hq).ne_zero)]
  calc
    (∑ q ∈ n.primeFactors, q.factorization p) =
        ∑ q ∈ n.primeFactors, if p = q then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [(Nat.prime_of_mem_primeFactors hq).factorization]
      simp only [Finsupp.single_apply, eq_comm]
    _ = _ := by simp

lemma dvd_square_radical_of_bound {A n : ℕ} (hA : A ≠ 0) (hn : n ≠ 0)
    (h : ∀ p : ℕ, p.Prime → A.factorization p ≤ if p ∣ n then 2 else 0) :
    A ∣ (primeRadical n) ^ 2 := by
  apply (Nat.factorization_le_iff_dvd hA (pow_ne_zero 2 (primeRadical_nonzero n))).mp
  intro p
  by_cases hp : p.Prime
  · rw [Nat.factorization_pow, Finsupp.nsmul_apply, smul_eq_mul,
      primeRadical_factorization]
    have hh := h p hp
    have hmem : p ∈ n.primeFactors ↔ p ∣ n :=
      ⟨Nat.dvd_of_mem_primeFactors, fun hd => Nat.mem_primeFactors.mpr ⟨hp, hd, hn⟩⟩
    simpa only [hmem, mul_ite, mul_one, mul_zero] using hh
  · rw [Nat.factorization_eq_zero_of_not_prime _ hp]
    exact Nat.zero_le _

end PellPrimitiveDivisor.Arithmetic

namespace PellPrimitiveDivisor.Cyclotomic
open Pell Polynomial

noncomputable def quadEval {D : ℤ} (r : ℝ) (hr : r * r = (D : ℝ)) :
    Zsqrtd D →+* ℝ := Zsqrtd.lift ⟨r, hr⟩

lemma norm_eval {D : ℤ} (r : ℝ) (hr : r * r = (D : ℝ)) (z : Zsqrtd D) :
    (z.norm : ℝ) = quadEval r hr z * quadEval (-r) (by nlinarith [hr]) z := by
  change ((z.re * z.re - D * z.im * z.im : ℤ) : ℝ) =
    ((z.re : ℝ) + z.im * r) * ((z.re : ℝ) + z.im * -r)
  push_cast
  linear_combination (z.im : ℝ) ^ 2 * hr

noncomputable def cycloNorm {D : ℤ} (u : Solution₁ D) (n : ℕ) : ℕ :=
  ((cyclotomic n (Zsqrtd D)).eval ((u : Zsqrtd D) ^ 2)).norm.natAbs

lemma cyclotomic_small_lower {n : ℕ} (hn : 0 < n) {q : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    (1 - q) ^ n.totient ≤ |(cyclotomic n ℝ).eval q| := by
  let ζ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / n)
  have hζ : IsPrimitiveRoot ζ n := Complex.isPrimitiveRoot_exp n hn.ne'
  have hbound (w : ℂ) (hw : w ∈ primitiveRoots n ℂ) :
      1 - q ≤ ‖(q : ℂ) - w‖ := by
    have hw' := (mem_primitiveRoots hn).mp hw
    have hb := norm_sub_norm_le w (q : ℂ)
    rw [hw'.norm'_eq_one hn.ne', Complex.norm_real, Real.norm_of_nonneg hq] at hb
    simpa only [norm_sub_rev] using hb
  have hprod := Finset.prod_le_prod
    (s := primitiveRoots n ℂ) (f := fun _ => 1 - q)
    (g := fun w => ‖(q : ℂ) - w‖)
    (fun _ _ => sub_nonneg.mpr hq1) (fun w hw => hbound w hw)
  have hmap : (cyclotomic n ℂ).eval (q : ℂ) =
      (((cyclotomic n ℝ).eval q : ℝ) : ℂ) :=
    cyclotomic.eval_apply q n Complex.ofRealHom
  have he : ‖(cyclotomic n ℂ).eval (q : ℂ)‖ = |(cyclotomic n ℝ).eval q| := by
    rw [hmap, Complex.norm_real, Real.norm_eq_abs]
  rw [← he, cyclotomic_eq_prod_X_sub_primitiveRoots hζ, eval_prod]
  simp only [eval_sub, eval_X, eval_C, norm_prod]
  simpa only [Finset.prod_const, Complex.card_primitiveRoots] using hprod

lemma cycloNorm_growth (D : ℕ) (u : Solution₁ (D : ℤ)) (hu : IsFundamental u)
    (n : ℕ) (hn : 0 < n) : 12 ^ n.totient ≤ cycloNorm u n := by
  let r : ℝ := Real.sqrt D
  have hr : r * r = ((D : ℤ) : ℝ) := by
    simpa only [r, ← pow_two, Int.cast_natCast] using Real.sq_sqrt (Nat.cast_nonneg D)
  let f := quadEval r hr
  let g := quadEval (-r) (by nlinarith [hr])
  let α := f (u : Zsqrtd (D : ℤ))
  let β := g (u : Zsqrtd (D : ℤ))
  have hx : (2 : ℝ) ≤ (u.x : ℝ) := by
    exact_mod_cast (show (2 : ℤ) ≤ u.x by have := hu.1; omega)
  have hy : (0 : ℝ) ≤ (u.y : ℝ) := by exact_mod_cast hu.2.1.le
  have hα : 1 < α := by
    change 1 < (u.x : ℝ) + (u.y : ℝ) * r
    have : 0 ≤ (u.y : ℝ) * r := mul_nonneg hy (Real.sqrt_nonneg _)
    linarith
  have hab : α * β = 1 := by
    have he := norm_eval r hr (u : Zsqrtd (D : ℤ))
    have hnorm : (u : Zsqrtd (D : ℤ)).norm = 1 :=
      Zsqrtd.norm_eq_one_iff_mem_unitary.mpr u.property
    rw [hnorm] at he
    simpa only [Int.cast_one] using he.symm
  have hβ : 0 < β := pos_of_mul_pos_left (by rw [mul_comm, hab]; norm_num) (by linarith : 0 ≤ α)
  have hβ1 : β < 1 := by
    have hh := mul_lt_mul_of_pos_right hα hβ
    nlinarith only [hh, hab]
  have hsum : 4 ≤ α + β := by
    change 4 ≤ ((u.x : ℝ) + u.y * r) + ((u.x : ℝ) + u.y * -r)
    linarith
  have hs : 16 ≤ (α + β) ^ 2 := by nlinarith
  have hab2 : α ^ 2 * β ^ 2 = 1 := by
    rw [← mul_pow, hab]
    norm_num
  have hbase : 12 ≤ (α ^ 2 - 1) * (1 - β ^ 2) := by
    nlinarith only [hs, hab, hab2]
  have hA : (α ^ 2 - 1) ^ n.totient ≤ |(cyclotomic n ℝ).eval (α ^ 2)| := by
    exact (sub_one_pow_totient_le_cyclotomic_eval (by nlinarith : 1 < α ^ 2) n).trans
      (le_abs_self _)
  have hB : (1 - β ^ 2) ^ n.totient ≤ |(cyclotomic n ℝ).eval (β ^ 2)| :=
    cyclotomic_small_lower hn (sq_nonneg _) (by nlinarith)
  have hnorm : (cycloNorm u n : ℝ) =
      |(cyclotomic n ℝ).eval (α ^ 2)| * |(cyclotomic n ℝ).eval (β ^ 2)| := by
    unfold cycloNorm
    rw [Nat.cast_natAbs, Int.cast_abs, norm_eval r hr, abs_mul]
    rw [← cyclotomic.eval_apply _ n f, ← cyclotomic.eval_apply _ n g]
    simp only [map_pow]
    rfl
  have hgrowth : (12 : ℝ) ^ n.totient ≤ (cycloNorm u n : ℝ) := by
    rw [hnorm]
    calc
      (12 : ℝ) ^ n.totient ≤ ((α ^ 2 - 1) * (1 - β ^ 2)) ^ n.totient :=
        pow_le_pow_left₀ (by norm_num) hbase _
      _ = (α ^ 2 - 1) ^ n.totient * (1 - β ^ 2) ^ n.totient := mul_pow _ _ _
      _ ≤ _ := mul_le_mul hA hB (pow_nonneg (by nlinarith) _) (abs_nonneg _)
  exact_mod_cast hgrowth

lemma norm_sq_sub_one {D : ℤ} (v : Solution₁ D) :
    (((v : Zsqrtd D) ^ 2 - 1).norm) = -4 * D * v.y ^ 2 := by
  simp only [pow_two, Zsqrtd.norm, Zsqrtd.re_sub, Zsqrtd.im_sub,
    Zsqrtd.re_mul, Zsqrtd.im_mul, Zsqrtd.re_one, Zsqrtd.im_one, sub_zero]
  change ((v.x * v.x + D * v.y * v.y - 1) *
      (v.x * v.x + D * v.y * v.y - 1) -
      D * (v.x * v.y + v.y * v.x) * (v.x * v.y + v.y * v.x)) = _
  linear_combination (v.x ^ 2 - D * v.y ^ 2 - 1) * v.prop

lemma cycloNorm_prod (D : ℕ) (u : Solution₁ (D : ℤ)) (n : ℕ) (hn : 0 < n) :
    (∏ d ∈ n.divisors, cycloNorm u d) = 4 * D * (u ^ n).y.natAbs ^ 2 := by
  have he := congrArg (Polynomial.eval ((u : Zsqrtd (D : ℤ)) ^ 2))
    (prod_cyclotomic_eq_X_pow_sub_one hn (Zsqrtd (D : ℤ)))
  simp only [eval_prod, eval_sub, eval_pow, eval_X, eval_one] at he
  let coeHom : Solution₁ (D : ℤ) →* Zsqrtd (D : ℤ) :=
    { toFun := fun v => (v : Zsqrtd (D : ℤ))
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hcoe : ((u ^ n : Solution₁ (D : ℤ)) : Zsqrtd (D : ℤ)) =
      (u : Zsqrtd (D : ℤ)) ^ n := coeHom.map_pow u n
  have hpow : ((u : Zsqrtd (D : ℤ)) ^ 2) ^ n =
      ((u ^ n : Solution₁ (D : ℤ)) : Zsqrtd (D : ℤ)) ^ 2 := by
    rw [hcoe, ← pow_mul, ← pow_mul, Nat.mul_comm 2 n]
  let normAbs : Zsqrtd (D : ℤ) →* ℕ :=
    Int.natAbsHom.toMonoidHom.comp Zsqrtd.normMonoidHom
  have hh := congrArg normAbs he
  rw [map_prod] at hh
  change (∏ d ∈ n.divisors, cycloNorm u d) =
    (((u : Zsqrtd (D : ℤ)) ^ 2) ^ n - 1).norm.natAbs at hh
  rw [hpow, norm_sq_sub_one] at hh
  simpa only [Int.natAbs_mul, Int.natAbs_neg, show Int.natAbs 4 = 4 from rfl,
    Int.natAbs_pow, Int.natAbs_natCast] using hh

lemma cycloNorm_pos (D : ℕ) (u : Solution₁ (D : ℤ)) (hu : IsFundamental u)
    (n : ℕ) (hn : 0 < n) : 0 < cycloNorm u n :=
  (pow_pos (by decide : 0 < (12 : ℕ)) _).trans_le (cycloNorm_growth D u hu n hn)

lemma cycloNorm_factorization_sum (D : ℕ) (u : Solution₁ (D : ℤ))
    (hu : IsFundamental u) (p : ℕ) (hp : p.Prime) (t : ℕ) (ht : 0 < t) :
    (∑ d ∈ t.divisors, (cycloNorm u d).factorization p) =
      (4 * D).factorization p + 2 * padicValInt p (u ^ t).y := by
  have hD : D ≠ 0 := by
    have hd := hu.d_pos
    exact_mod_cast hd.ne'
  have hyt : (u ^ t).y.natAbs ≠ 0 := by
    apply Int.natAbs_ne_zero.mpr
    have hy := Solution₁.y_pow_succ_pos hu.x_pos hu.2.1 (t - 1)
    simp only [Nat.succ_eq_add_one, Nat.sub_add_cancel ht] at hy
    exact hy.ne'
  have hC : ∀ d ∈ t.divisors, cycloNorm u d ≠ 0 :=
    fun d hd => (cycloNorm_pos D u hu d (Nat.pos_of_mem_divisors hd)).ne'
  have hh := congrArg (fun a : ℕ => a.factorization p) (cycloNorm_prod D u t ht)
  rw [Nat.factorization_prod_apply hC,
    Nat.factorization_mul (mul_ne_zero (by decide : 4 ≠ 0) hD) (pow_ne_zero 2 hyt),
    Nat.factorization_pow] at hh
  simpa only [Finsupp.add_apply, Finsupp.nsmul_apply, smul_eq_mul,
    Nat.factorization_def _ hp, padicValInt] using hh

end PellPrimitiveDivisor.Cyclotomic

namespace PellPrimitiveDivisor
open Pell PellPrimitiveDivisor.Arithmetic PellPrimitiveDivisor.Cyclotomic

theorem primitive_divisor (D : ℕ) (u : Solution₁ (D : ℤ)) (hu : IsFundamental u)
    (n : ℕ) (hn : 2 < n) :
    ∃ p : ℕ, p.Prime ∧ p ∣ (u ^ n).y.natAbs ∧
      ∀ j : ℕ, 0 < j → j < n → ¬ p ∣ (u ^ j).y.natAbs := by
  classical
  by_contra h
  have hold : ∀ p : ℕ, p.Prime → p ∣ (u ^ n).y.natAbs →
      ∃ j : ℕ, 0 < j ∧ j < n ∧ p ∣ (u ^ j).y.natAbs := by
    intro p hp hpy
    by_contra! hno
    exact h ⟨p, hp, hpy, hno⟩
  have hf := factorization_bound_of_old u hu (cycloNorm u) (4 * D)
    (cycloNorm_factorization_sum D u hu) n hn hold
  have hC := cycloNorm_pos D u hu n (by omega)
  have hd := dvd_square_radical_of_bound hC.ne' (by omega : n ≠ 0) hf
  have hle := Nat.le_of_dvd
    (pow_pos (Nat.pos_of_ne_zero (primeRadical_nonzero n)) 2) hd
  have hlow := cycloNorm_growth D u hu n (by omega)
  have hrad := radical_growth n hn
  omega

end PellPrimitiveDivisor

theorem OMA.solution : OMA.R_Erdos649_erdos_649_variants_tong_question_R1_H2_R1.H1 := by
  intro D u hu k hk
  exact PellPrimitiveDivisor.primitive_divisor D u hu k (by omega)
