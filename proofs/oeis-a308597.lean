import OMAStatements.S_oeis_a308597
import Mathlib

/-!
# Disproof of the A308597 conjecture: a(1217712376) = 0

If m = T(a) + T(b) with T(x) = x(x+1)/2 and a <= b, then 4m + 1 = (a+b+1)^2 + (b-a)^2 is a
sum of two squares. For N = 1217712376 and every power 2^c * 5^d <= N (d <= 1, c <= 30),
the number 4(N - 2^c 5^d) + 1 has a prime factor q = 3 mod 4 to an odd power (listed below),
so it is not a sum of two squares (Nat.eq_sq_add_sq_iff). This is the counterexample found by
Giovanni Resta and recorded in OEIS A308597 by Zhi-Wei Sun (Jun 10 2019). The certificate is
checked by kernel evaluation (decide +kernel); the primes are proved prime by norm_num.
-/

namespace OMA.P_oeis_a308597

lemma not_sum_sq (r q k : ℕ) (hq : q.Prime) (h4 : q % 4 = 3) (hk : k % 2 = 1)
    (h1 : r % q ^ k = 0) (h2 : r % q ^ (k + 1) ≠ 0) : ¬ ∃ x y : ℕ, r = x ^ 2 + y ^ 2 := by
  intro hxy
  have hr : r ≠ 0 := by rintro rfl; simp at h2
  have hk0 : k ≠ 0 := by omega
  have hdvd : q ∣ r := (dvd_pow_self q hk0).trans (Nat.dvd_of_mod_eq_zero h1)
  have hv := Nat.eq_sq_add_sq_iff.1 hxy q (Nat.mem_primeFactors.2 ⟨hq, hdvd, hr⟩) h4
  have e1 : k ≤ padicValNat q r :=
    (padicValNat_dvd_iff_le_of_ne_one hq.ne_one hr).1 (Nat.dvd_of_mod_eq_zero h1)
  have e2 : ¬ (k + 1 ≤ padicValNat q r) := fun h =>
    h2 (Nat.mod_eq_zero_of_dvd ((padicValNat_dvd_iff_le_of_ne_one hq.ne_one hr).2 h))
  have e3 : padicValNat q r = k := by omega
  rw [e3] at hv
  obtain ⟨m, hm⟩ := hv
  omega

/-- The primes used in the certificates. -/
def plist : List ℕ := [3, 7, 11, 19, 23, 31, 43, 47, 67, 79, 107, 211, 251, 311, 419, 619, 743, 1091, 1231, 1303, 8779, 16879]

/-- Every entry of the list is prime. -/
def allPrime : List ℕ → Prop
  | [] => True
  | q :: qs => q.Prime ∧ allPrime qs

lemma allPrime_mem : ∀ (l : List ℕ), allPrime l → ∀ q ∈ l, q.Prime := by
  intro l
  induction l with
  | nil => intro _ q hq; simp at hq
  | cons p ps ih =>
    intro h q hq
    rcases List.mem_cons.1 hq with rfl | hq
    · exact h.1
    · exact ih h.2 q hq

set_option maxRecDepth 100000 in
lemma pr0 : Nat.Prime 3 := by norm_num

set_option maxRecDepth 100000 in
lemma pr1 : Nat.Prime 7 := by norm_num

set_option maxRecDepth 100000 in
lemma pr2 : Nat.Prime 11 := by norm_num

set_option maxRecDepth 100000 in
lemma pr3 : Nat.Prime 19 := by norm_num

set_option maxRecDepth 100000 in
lemma pr4 : Nat.Prime 23 := by norm_num

set_option maxRecDepth 100000 in
lemma pr5 : Nat.Prime 31 := by norm_num

set_option maxRecDepth 100000 in
lemma pr6 : Nat.Prime 43 := by norm_num

set_option maxRecDepth 100000 in
lemma pr7 : Nat.Prime 47 := by norm_num

set_option maxRecDepth 100000 in
lemma pr8 : Nat.Prime 67 := by norm_num

set_option maxRecDepth 100000 in
lemma pr9 : Nat.Prime 79 := by norm_num

set_option maxRecDepth 100000 in
lemma pr10 : Nat.Prime 107 := by norm_num

set_option maxRecDepth 100000 in
lemma pr11 : Nat.Prime 211 := by norm_num

set_option maxRecDepth 100000 in
lemma pr12 : Nat.Prime 251 := by norm_num

set_option maxRecDepth 100000 in
lemma pr13 : Nat.Prime 311 := by norm_num

set_option maxRecDepth 100000 in
lemma pr14 : Nat.Prime 419 := by norm_num

set_option maxRecDepth 100000 in
lemma pr15 : Nat.Prime 619 := by norm_num

set_option maxRecDepth 100000 in
lemma pr16 : Nat.Prime 743 := by norm_num

set_option maxRecDepth 100000 in
lemma pr17 : Nat.Prime 1091 := by norm_num

set_option maxRecDepth 100000 in
lemma pr18 : Nat.Prime 1231 := by norm_num

set_option maxRecDepth 100000 in
lemma pr19 : Nat.Prime 1303 := by norm_num

set_option maxRecDepth 100000 in
lemma pr20 : Nat.Prime 8779 := by norm_num

set_option maxRecDepth 100000 in
lemma pr21 : Nat.Prime 16879 := by norm_num

set_option maxRecDepth 10000 in
lemma plist_all : allPrime plist := ⟨pr0, pr1, pr2, pr3, pr4, pr5, pr6, pr7, pr8, pr9, pr10, pr11, pr12, pr13, pr14, pr15, pr16, pr17, pr18, pr19, pr20, pr21, trivial⟩

lemma plist_prime : ∀ q ∈ plist, q.Prime := allPrime_mem plist plist_all

lemma two_tri (x : ℕ) : 2 * OMA.S_oeis_a308597.triangular x = x * (x + 1) := by
  unfold OMA.S_oeis_a308597.triangular
  exact Nat.mul_div_cancel' (Nat.even_mul_succ_self x).two_dvd

lemma four_tri (a b : ℕ) (hab : a ≤ b) :
    4 * (OMA.S_oeis_a308597.triangular a + OMA.S_oeis_a308597.triangular b) + 1 =
      (a + b + 1) ^ 2 + (b - a) ^ 2 := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hab
  have ha := two_tri a
  have hb := two_tri (a + t)
  rw [Nat.add_sub_cancel_left]
  nlinarith [ha, hb]

/-- (c, d, q, k): q^k exactly divides 4 (N - 2^c 5^d) + 1. -/
def tab : List (ℕ × ℕ × ℕ × ℕ) := [(0, 0, 7, 1), (1, 0, 3, 1), (2, 0, 11, 1), (3, 0, 7, 1), (4, 0, 419, 1), (5, 0, 3, 1), (6, 0, 7, 1), (7, 0, 3, 1), (8, 0, 619, 1), (9, 0, 7, 1), (10, 0, 79, 1), (11, 0, 3, 1), (12, 0, 7, 1), (13, 0, 3, 1), (14, 0, 19, 1), (15, 0, 3, 3), (16, 0, 16879, 1), (17, 0, 3, 1), (18, 0, 7, 1), (19, 0, 3, 1), (20, 0, 743, 1), (21, 0, 7, 1), (22, 0, 11, 1), (23, 0, 3, 1), (24, 0, 7, 1), (25, 0, 3, 1), (26, 0, 67, 1), (27, 0, 7, 1), (28, 0, 211, 1), (29, 0, 3, 1), (30, 0, 7, 1), (0, 1, 3, 1), (1, 1, 47, 1), (2, 1, 3, 1), (3, 1, 311, 1), (4, 1, 107, 1), (5, 1, 43, 1), (6, 1, 3, 1), (7, 1, 31, 1), (8, 1, 3, 1), (9, 1, 1231, 1), (10, 1, 3, 3), (11, 1, 67, 1), (12, 1, 3, 1), (13, 1, 1303, 1), (14, 1, 3, 1), (15, 1, 8779, 1), (16, 1, 19, 1), (17, 1, 31, 1), (18, 1, 3, 1), (19, 1, 43, 1), (20, 1, 3, 1), (21, 1, 23, 1), (22, 1, 31, 1), (23, 1, 1091, 1), (24, 1, 3, 1), (25, 1, 251, 1), (26, 1, 3, 1), (27, 1, 31, 1)]

def good (e : ℕ × ℕ × ℕ × ℕ) : Bool :=
  let r := 4 * (1217712376 - 2 ^ e.1 * 5 ^ e.2.1) + 1
  decide (2 ^ e.1 * 5 ^ e.2.1 ≤ 1217712376) && plist.contains e.2.2.1 &&
    (e.2.2.1 % 4 == 3) && (e.2.2.2 % 2 == 1) && (r % e.2.2.1 ^ e.2.2.2 == 0) &&
    (r % e.2.2.1 ^ (e.2.2.2 + 1) != 0)

lemma tab_good : tab.all good = true := by decide +kernel

lemma cover : ∀ c, c < 31 → ∀ d, d < 2 → 2 ^ c * 5 ^ d ≤ 1217712376 →
    tab.any (fun e => e.1 == c && e.2.1 == d) = true := by decide +kernel

end OMA.P_oeis_a308597

open OMA.P_oeis_a308597 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a308597.main) := by
  intro h
  obtain ⟨a, b, c, d, hab, hd, hn⟩ := h 1217712376 (by norm_num)
  have h4 := four_tri a b hab
  set s := OMA.S_oeis_a308597.triangular a + OMA.S_oeis_a308597.triangular b with hs
  have ht : 2 ^ c * 5 ^ d ≤ 1217712376 := by rw [hn]; omega
  have hc : c < 31 := by
    by_contra hc
    have h1 : 2 ^ 31 ≤ 2 ^ c := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 2 ^ c ≤ 2 ^ c * 5 ^ d := Nat.le_mul_of_pos_right _ (by positivity)
    omega
  have hcov := cover c hc d (by omega) ht
  obtain ⟨e, he, hce⟩ := List.any_eq_true.1 hcov
  simp only [Bool.and_eq_true, beq_iff_eq] at hce
  obtain ⟨rfl, rfl⟩ := hce
  have hg := List.all_eq_true.1 tab_good e he
  simp only [good, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, bne_iff_ne, ne_eq,
    List.contains_iff_mem] at hg
  obtain ⟨⟨⟨⟨⟨_, hq⟩, h4'⟩, hk⟩, h1⟩, h2⟩ := hg
  have hr : 4 * (1217712376 - 2 ^ e.1 * 5 ^ e.2.1) + 1 = (a + b + 1) ^ 2 + (b - a) ^ 2 := by
    rw [← h4]; omega
  rw [hr] at h1 h2
  exact not_sum_sq _ _ _ (plist_prime _ hq) h4' hk h1 h2 ⟨a + b + 1, b - a, rfl⟩
