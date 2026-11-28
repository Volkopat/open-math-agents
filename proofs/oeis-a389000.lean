import OMAStatements.S_oeis_a389000
import Mathlib

/-!
# OEIS A389000: the smallest positive k whose digit sum and whose square's digit sum are both divisible by 9m+5 is 2*10^(2m+1) - 1

Credit: @Squee451. The proof was found with Claude (claude-fable-5-2) and Codex; the Lean text was
written by Codex.

Outline. (1) K is a 1 followed by h nines, s(K) = 1 + 9h = 2n; K^2 = 4*10^(2h) - 4*10^h + 1 has digits 3,
then h-1 nines, 6, h-1 zeros, 1, so s(K^2) = 9h + 1 = 2n. (2) Let 1 <= k < K. Either k < 10^h, or k
has leading digit 1 and its other h digits are not all nines; either way s(k) <= 9h = 2n - 1, so n |
s(k) and s(k) > 0 force s(k) = n. (3) k^2 < 4*10^(2h) gives s(k^2) <= 3 + 18h = 4n + 1, so n |
s(k^2) forces s(k^2) = u*n with u in {1,2,3,4}. (4) Modulo 9: u*n = s(k^2) = k^2 = s(k)^2 = n^2, and
n = 5 mod 9 gives 5u = 7, i.e. u = 5 mod 9, impossible for u <= 4. So no smaller positive k works.
-/

open OMA.S_oeis_a389000

namespace OMA.A389000Proof

lemma sum_step (k : ℕ) : digitSum k = k % 10 + digitSum (k / 10) := by
  by_cases hk : k = 0
  · simp [hk, digitSum]
  · simpa [digitSum] using congrArg List.sum
      (Nat.digits_eq_cons_digits_div (by decide : 1 < 10) hk)

lemma sum_small (k : ℕ) (hk : k < 10) : digitSum k = k := by
  rw [sum_step, Nat.mod_eq_of_lt hk, Nat.div_eq_of_lt hk]
  simp [digitSum]

lemma sum_last (a b : ℕ) (hb : b < 10) :
    digitSum (a * 10 + b) = digitSum a + b := by
  rw [sum_step]
  simp [Nat.add_mod, Nat.add_div, Nat.mod_eq_of_lt hb, Nat.div_eq_of_lt hb,
    Nat.add_comm, Nat.not_le_of_lt hb]

lemma sum_block (h a b : ℕ) (hb : b < 10 ^ h) :
    digitSum (a * 10 ^ h + b) = digitSum a + digitSum b := by
  induction h generalizing a b with
  | zero =>
      have : b = 0 := by simpa using hb
      simp [this, digitSum]
  | succ h ih =>
      have hb' : b / 10 < 10 ^ h := by
        apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 10)).2
        simpa [pow_succ] using hb
      have heq : a * 10 ^ (h + 1) + b =
          (a * 10 ^ h + b / 10) * 10 + b % 10 := by
        have := Nat.mod_add_div b 10
        rw [pow_succ]
        nlinarith
      rw [heq, sum_last _ _ (Nat.mod_lt _ (by decide)), ih _ _ hb', sum_step b]
      omega

lemma sum_nines (h : ℕ) : digitSum (10 ^ h - 1) = 9 * h := by
  induction h with
  | zero => simp [digitSum]
  | succ h ih =>
      have hp : 0 < (10 : ℕ) ^ h := by positivity
      have heq : 10 ^ (h + 1) - 1 = (10 ^ h - 1) * 10 + 9 := by
        rw [pow_succ]
        omega
      rw [heq, sum_last _ _ (by decide), ih]
      omega

lemma sum_bound (h k : ℕ) (hk : k < 10 ^ h) :
    digitSum k ≤ 9 * h ∧ (digitSum k = 9 * h → k = 10 ^ h - 1) := by
  induction h generalizing k with
  | zero =>
      have : k = 0 := by simpa using hk
      simp [this, digitSum]
  | succ h ih =>
      have hq : k / 10 < 10 ^ h := by
        apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 10)).2
        simpa [pow_succ] using hk
      obtain ⟨hbound, heq⟩ := ih _ hq
      have hr := Nat.mod_lt k (by decide : 0 < 10)
      have hdec := Nat.mod_add_div k 10
      have hp : 0 < (10 : ℕ) ^ h := by positivity
      rw [sum_step]
      constructor
      · omega
      · intro hs
        have hmax : digitSum (k / 10) = 9 * h := by omega
        have := heq hmax
        rw [pow_succ]
        omega

lemma sum_pos (k : ℕ) (hk : 0 < k) : 0 < digitSum k := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
      rw [sum_step]
      by_cases hq : k / 10 = 0
      · have := Nat.mod_add_div k 10
        omega
      · have := ih (k / 10) (Nat.div_lt_self hk (by decide)) (by omega)
        omega

lemma candidate_sum (h : ℕ) : digitSum (2 * 10 ^ h - 1) = 9 * h + 1 := by
  have hp : 0 < (10 : ℕ) ^ h := by positivity
  have heq : 2 * 10 ^ h - 1 = 1 * 10 ^ h + (10 ^ h - 1) := by omega
  rw [heq, sum_block _ _ _ (by omega), sum_nines, sum_small 1 (by decide)]
  omega

lemma candidate_square_sum (t : ℕ) :
    digitSum ((2 * 10 ^ (t + 1) - 1) ^ 2) = 9 * (t + 1) + 1 := by
  have hp : 0 < (10 : ℕ) ^ t := by positivity
  have hp' : 10 ≤ (10 : ℕ) ^ (t + 1) := by rw [pow_succ]; omega
  have hn : 10 ^ t - 1 + 1 = (10 : ℕ) ^ t := by omega
  have hk : 2 * 10 ^ (t + 1) - 1 + 1 = 2 * (10 : ℕ) ^ (t + 1) := by omega
  have htail : (10 ^ t - 1) * 10 + 6 < (10 : ℕ) ^ (t + 1) := by
    rw [pow_succ]
    omega
  have heq : (2 * 10 ^ (t + 1) - 1) ^ 2 =
      (3 * 10 ^ (t + 1) + ((10 ^ t - 1) * 10 + 6)) * 10 ^ (t + 1) + 1 := by
    simp only [show (10 : ℕ) ^ (t + 1) = 10 ^ t * 10 from pow_succ 10 t] at hk ⊢
    nlinarith
  rw [heq, sum_block _ _ _ (by omega), sum_block _ _ _ htail,
    sum_last _ _ (by decide), sum_nines, sum_small 3 (by decide),
    sum_small 1 (by decide)]
  omega

lemma below_candidate_sum (h k : ℕ) (hk : k < 2 * 10 ^ h - 1) :
    digitSum k ≤ 9 * h := by
  by_cases hsmall : k < 10 ^ h
  · exact (sum_bound h k hsmall).1
  · have hp : 0 < (10 : ℕ) ^ h := by positivity
    have hr : k - 10 ^ h < 10 ^ h := by omega
    have hr' : k - 10 ^ h ≠ 10 ^ h - 1 := by omega
    have heq : k = 1 * 10 ^ h + (k - 10 ^ h) := by omega
    obtain ⟨hb, he⟩ := sum_bound h (k - 10 ^ h) hr
    have hs : digitSum (k - 10 ^ h) < 9 * h := by
      by_contra hc
      exact hr' (he (by omega))
    rw [heq, sum_block _ _ _ hr, sum_small 1 (by decide)]
    omega

lemma below_square_sum (h k : ℕ) (hk : k < 2 * 10 ^ h - 1) :
    digitSum (k ^ 2) ≤ 3 + 18 * h := by
  have hp : 0 < (10 : ℕ) ^ h := by positivity
  have hpow : (10 : ℕ) ^ (2 * h) = (10 ^ h) ^ 2 := by
    rw [Nat.mul_comm 2 h, pow_mul]
  have hsquare : k ^ 2 < 4 * 10 ^ (2 * h) := by
    rw [hpow]
    have hlt : k < 2 * 10 ^ h := by omega
    nlinarith
  have hp' : 0 < (10 : ℕ) ^ (2 * h) := by positivity
  have hq : k ^ 2 / 10 ^ (2 * h) < 4 :=
    (Nat.div_lt_iff_lt_mul hp').2 hsquare
  have hr : k ^ 2 % 10 ^ (2 * h) < 10 ^ (2 * h) := Nat.mod_lt _ hp'
  have heq := Nat.div_add_mod (k ^ 2) (10 ^ (2 * h))
  have hsum := sum_block (2 * h) (k ^ 2 / 10 ^ (2 * h))
    (k ^ 2 % 10 ^ (2 * h)) hr
  rw [Nat.mul_comm (k ^ 2 / 10 ^ (2 * h)), heq,
    sum_small (k ^ 2 / 10 ^ (2 * h)) (by omega)] at hsum
  have hb := (sum_bound (2 * h) _ hr).1
  omega

lemma no_smaller (m k : ℕ) (hk : k < 2 * 10 ^ (2 * m + 1) - 1)
    (hg : Good (9 * m + 5) k) : False := by
  obtain ⟨hkpos, hdiv, hsqdiv⟩ := hg
  have hspos := sum_pos k hkpos
  have hsbound := below_candidate_sum (2 * m + 1) k hk
  have hs : digitSum k = 9 * m + 5 := by
    obtain ⟨u, hu⟩ := hdiv
    have hu1 : 1 ≤ u := by nlinarith
    have hu2 : u < 2 := by nlinarith
    have : u = 1 := by omega
    simpa [this] using hu
  have hsqbound := below_square_sum (2 * m + 1) k hk
  obtain ⟨u, hu⟩ := hsqdiv
  have hu4 : u ≤ 4 := by nlinarith
  have hmod : k ≡ digitSum k [MOD 9] := Nat.modEq_digits_sum 9 10 (by decide) k
  have hsqmod : k ^ 2 ≡ digitSum (k ^ 2) [MOD 9] :=
    Nat.modEq_digits_sum 9 10 (by decide) (k ^ 2)
  have hcong := (hmod.pow 2).symm.trans hsqmod
  rw [hs, hu] at hcong
  have hnmod : (9 * m + 5) % 9 = 5 := by omega
  have hres : 7 = (5 * u) % 9 := by
    change (9 * m + 5) ^ 2 % 9 = ((9 * m + 5) * u) % 9 at hcong
    rw [Nat.pow_mod, Nat.mul_mod, hnmod] at hcong
    rw [Nat.mul_mod]
    norm_num at hcong ⊢
    exact hcong
  interval_cases u <;> norm_num at hres

end OMA.A389000Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a389000.main := by
  intro m
  constructor
  · change Good (9 * m + 5) (2 * 10 ^ (2 * m + 1) - 1)
    have hp : 0 < (10 : ℕ) ^ (2 * m + 1) := by positivity
    refine ⟨by omega, ?_, ?_⟩
    · rw [OMA.A389000Proof.candidate_sum]
      exact ⟨2, by omega⟩
    · rw [OMA.A389000Proof.candidate_square_sum]
      exact ⟨2, by omega⟩
  · intro k hk
    by_contra hc
    exact OMA.A389000Proof.no_smaller m k (by omega) hk
