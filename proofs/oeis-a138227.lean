import OMAStatements.S_oeis_a138227
import Mathlib

-- Problem: A138227 (odd n for which phi(n) does not divide the excess); the statement asks
-- that the set is infinite and that every 1093^k with k >= 2 is a member.
-- Upstream: formal-conjectures statements/oeis-a138227.lean:0 (declaration OMA.S_oeis_a138227.main)
-- Credit: @npnelson (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

-- Proof. Put p = 1093. The order of 2 mod p is 364, and p is a Wieferich prime: p^2 divides
-- 2^364 - 1 while p^3 does not. By lifting the exponent, v_p(2^(364 n) - 1) = 2 + v_p(n), so
-- for i >= 2 the order of 2 mod p^i is 364 p^(i-2). Hence phi(p^i) / ord(p^i) equals 1 for
-- i = 0, 3 for i = 1 and 3 p = 3279 for i >= 2, and for n = p^(k+2)
--   excess(n) = 364 p^k (3 + 3279 (k + 1)),   phi(n) = 1092 p^(k+1).
-- If phi(n) divided excess(n) then p would divide 364 (3 + 3279 (k + 1)), which is 1092 mod p.

namespace Wieferich138227Proof

open OMA.S_oeis_a138227

instance fact1093 : Fact (Nat.Prime 1093) := ⟨by norm_num⟩

theorem pow_eq_one_iff (N m : ℕ) : (2 : ZMod N) ^ m = 1 ↔ N ∣ 2 ^ m - 1 := by
  rw [← ZMod.natCast_eq_zero_iff]
  have h1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  rw [Nat.cast_sub h1]
  push_cast
  rw [sub_eq_zero]

theorem z1 : (2 : ZMod 1093) ^ 364 = 1 := by
  reduce_mod_char

theorem z2 : (2 : ZMod 1194649) ^ 364 = 1 := by
  reduce_mod_char

theorem z3 : (2 : ZMod 1305751357) ^ 364 ≠ 1 := by
  reduce_mod_char
  decide

theorem c1 : 1093 ^ 2 ∣ 2 ^ 364 - 1 := by
  rw [show (1093 : ℕ) ^ 2 = 1194649 by norm_num, ← pow_eq_one_iff]
  exact z2

theorem c2 : ¬ 1093 ^ 3 ∣ 2 ^ 364 - 1 := by
  rw [show (1093 : ℕ) ^ 3 = 1305751357 by norm_num, ← pow_eq_one_iff]
  exact z3

theorem ord1 : orderOf (2 : ZMod 1093) = 364 := by
  apply orderOf_eq_of_pow_and_pow_div_prime (by norm_num)
  · exact z1
  · intro q hq hdvd
    have hq' : q = 2 ∨ q = 7 ∨ q = 13 := by
      have h364 : (364 : ℕ) = 2 ^ 2 * 7 * 13 := by norm_num
      rw [h364] at hdvd
      rcases (Nat.Prime.dvd_mul hq).1 hdvd with h | h
      · rcases (Nat.Prime.dvd_mul hq).1 h with h | h
        · left
          exact (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 (hq.dvd_of_dvd_pow h)
        · right
          left
          exact (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).1 h
      · right
        right
        exact (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).1 h
    rcases hq' with rfl | rfl | rfl
    · rw [show 364 / 2 = 182 by norm_num, Ne, pow_eq_one_iff]
      norm_num
    · rw [show 364 / 7 = 52 by norm_num, Ne, pow_eq_one_iff]
      norm_num
    · rw [show 364 / 13 = 28 by norm_num, Ne, pow_eq_one_iff]
      norm_num

theorem pow_sub_ne (e : ℕ) (he : 0 < e) : 2 ^ e - 1 ≠ 0 := by
  have h : 2 ^ 1 ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
  omega

theorem val2 : padicValNat 1093 (2 ^ 364 - 1) = 2 := by
  have hne : 2 ^ 364 - 1 ≠ 0 := pow_sub_ne 364 (by norm_num)
  have h1 : 2 ≤ padicValNat 1093 (2 ^ 364 - 1) := (padicValNat_dvd_iff_le hne).1 c1
  have h2 : ¬ 3 ≤ padicValNat 1093 (2 ^ 364 - 1) := fun h =>
    c2 ((padicValNat_dvd_iff_le hne).2 h)
  omega

theorem lte (n : ℕ) (hn : n ≠ 0) :
    padicValNat 1093 (2 ^ (364 * n) - 1) = 2 + padicValNat 1093 n := by
  have hxy : 1093 ∣ 2 ^ 364 - 1 := Dvd.dvd.trans (dvd_pow_self 1093 (by norm_num)) c1
  have hx : ¬ 1093 ∣ 2 ^ 364 := by
    intro h
    have h2 : 1093 ∣ 2 := (Nat.Prime.dvd_of_dvd_pow (by norm_num) h)
    omega
  have hyx : 1 < 2 ^ 364 := Nat.one_lt_two_pow (by norm_num)
  have h := padicValNat.pow_sub_pow (p := 1093) (by decide) hyx hxy hx hn
  rw [← pow_mul, one_pow, val2] at h
  exact h

theorem dvd_iff (i m : ℕ) (hi : 2 ≤ i) :
    1093 ^ i ∣ 2 ^ m - 1 ↔ 364 * 1093 ^ (i - 2) ∣ m := by
  constructor
  · intro h
    have h1 : 1093 ∣ 2 ^ m - 1 := Dvd.dvd.trans (dvd_pow_self 1093 (by omega)) h
    have h2 : (2 : ZMod 1093) ^ m = 1 := (pow_eq_one_iff 1093 m).2 h1
    have h3 : 364 ∣ m := by
      rw [← ord1]
      exact orderOf_dvd_of_pow_eq_one h2
    obtain ⟨n, rfl⟩ := h3
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have hv := lte n hn.ne'
      have hne : 2 ^ (364 * n) - 1 ≠ 0 := pow_sub_ne _ (by positivity)
      have h4 : i ≤ padicValNat 1093 (2 ^ (364 * n) - 1) := (padicValNat_dvd_iff_le hne).1 h
      rw [hv] at h4
      have h5 : 1093 ^ (i - 2) ∣ n := (padicValNat_dvd_iff_le hn.ne').2 (by omega)
      exact Nat.mul_dvd_mul_left 364 h5
  · rintro ⟨t, rfl⟩
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · simp
    · have hn : 1093 ^ (i - 2) * t ≠ 0 := by positivity
      have hv := lte (1093 ^ (i - 2) * t) hn
      have hne : 2 ^ (364 * (1093 ^ (i - 2) * t)) - 1 ≠ 0 := pow_sub_ne _ (by positivity)
      rw [mul_assoc, padicValNat_dvd_iff_le hne, hv]
      have h6 : i - 2 ≤ padicValNat 1093 (1093 ^ (i - 2) * t) :=
        (padicValNat_dvd_iff_le hn).1 (Dvd.intro t rfl)
      omega

theorem ord_pow (i : ℕ) (hi : 2 ≤ i) :
    orderOf (2 : ZMod (1093 ^ i)) = 364 * 1093 ^ (i - 2) := by
  apply Nat.dvd_antisymm
  · apply orderOf_dvd_of_pow_eq_one
    rw [pow_eq_one_iff, dvd_iff i _ hi]
  · rw [← dvd_iff i _ hi, ← pow_eq_one_iff]
    exact pow_orderOf_eq_one _

theorem ordTwo_one : ordTwo 1 = 1 := by
  unfold ordTwo
  rw [orderOf_eq_one_iff]
  have hs : Subsingleton (ZMod 1) := inferInstanceAs (Subsingleton (Fin 1))
  exact Subsingleton.elim _ _

theorem term0 : (1093 ^ 0).totient / ordTwo (1093 ^ 0) = 1 := by
  rw [pow_zero, ordTwo_one, Nat.totient_one]

theorem term1 : (1093 ^ 1).totient / ordTwo (1093 ^ 1) = 3 := by
  rw [pow_one]
  unfold ordTwo
  rw [ord1, Nat.totient_prime (by norm_num)]

theorem term (i : ℕ) (hi : 2 ≤ i) : (1093 ^ i).totient / ordTwo (1093 ^ i) = 3279 := by
  unfold ordTwo
  rw [ord_pow i hi, Nat.totient_prime_pow (by norm_num) (by omega)]
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 2 := ⟨i - 2, by omega⟩
  rw [show j + 2 - 1 = j + 1 by omega, show j + 2 - 2 = j by omega,
    show (1093 : ℕ) - 1 = 1092 by norm_num]
  apply Nat.div_eq_of_eq_mul_right (by positivity)
  rw [pow_succ]
  ring

theorem sum3 :
    ∑ i ∈ Finset.range 3, (1093 ^ i).totient / ordTwo (1093 ^ i) = 3283 := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one, term0, term1,
    term 2 (le_refl 2)]

theorem sum_terms (k : ℕ) :
    ∑ i ∈ Finset.range (k + 3), (1093 ^ i).totient / ordTwo (1093 ^ i) = 4 + 3279 * (k + 1) := by
  induction k with
  | zero => exact sum3
  | succ k ih =>
    rw [Finset.sum_range_succ, ih, term (k + 3) (by omega)]
    ring

theorem member (k : ℕ) : IsMember (1093 ^ (k + 2)) := by
  refine ⟨Odd.pow (by decide), ?_⟩
  unfold excess
  rw [Nat.sum_divisors_prime_pow (by norm_num : Nat.Prime 1093),
    show k + 2 + 1 = k + 3 from rfl, sum_terms k]
  unfold ordTwo
  rw [ord_pow (k + 2) (by omega), Nat.totient_prime_pow (by norm_num) (by omega)]
  rw [show k + 2 - 2 = k by omega, show k + 2 - 1 = k + 1 by omega,
    show (1093 : ℕ) - 1 = 1092 by norm_num]
  intro h
  have e1 : 1093 ^ (k + 1) * 1092 = 1093 ^ k * (1093 * 1092) := by
    rw [pow_succ]
    ring
  have e2 : 364 * 1093 ^ k * (4 + 3279 * (k + 1) - 1)
      = 1093 ^ k * (364 * (4 + 3279 * (k + 1) - 1)) := by
    ring
  rw [e1, e2] at h
  have h2 := (Nat.mul_dvd_mul_iff_left (by positivity : 0 < 1093 ^ k)).1 h
  have h3 : 1093 ∣ 364 * (4 + 3279 * (k + 1) - 1) := Dvd.dvd.trans (Dvd.intro _ rfl) h2
  omega

end Wieferich138227Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a138227.main := by
  refine ⟨?_, Wieferich138227Proof.member⟩
  apply Set.infinite_of_injective_forall_mem (f := fun k : ℕ => 1093 ^ (k + 2))
  · intro a b h
    have h2 : a + 2 = b + 2 := Nat.pow_right_injective (by norm_num : 2 ≤ 1093) h
    omega
  · intro k
    exact Wieferich138227Proof.member k
