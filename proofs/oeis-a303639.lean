import OMAStatements.S_oeis_a303639
import Mathlib

/-!
# Disproof of the A303639 conjecture: a(800322180) = 0

N = 800322180 is not a^2 + b^2 + binomial(2c+1,c) + binomial(2d+1,d): here d <= 15 (since
binomial(33,16) > N), and for each of the 136 pairs c <= d <= 15 with
binomial(2c+1,c) + binomial(2d+1,d) <= N, the remainder has a prime factor q = 3 mod 4 to an
odd power (listed below), so it is not a sum of two squares (Nat.eq_sq_add_sq_iff).
This is the counterexample recorded in OEIS A303639 (Adamczewski). The certificate is
checked by kernel evaluation (decide +kernel); the primes are proved prime by norm_num.
-/

namespace OMA.P_oeis_a303639

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
def plist : List ℕ := [3, 7, 11, 19, 23, 31, 43, 59, 67, 127, 139, 163, 199, 223, 227, 467, 563, 643, 647, 719, 887, 991, 1999, 2819, 3331, 5843, 7591, 78607, 284003, 689891, 4326031, 7923067, 12504647, 19990307, 26905651, 27594131, 79512187, 200057419, 200080511, 399984727]

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
lemma pr7 : Nat.Prime 59 := by norm_num

set_option maxRecDepth 100000 in
lemma pr8 : Nat.Prime 67 := by norm_num

set_option maxRecDepth 100000 in
lemma pr9 : Nat.Prime 127 := by norm_num

set_option maxRecDepth 100000 in
lemma pr10 : Nat.Prime 139 := by norm_num

set_option maxRecDepth 100000 in
lemma pr11 : Nat.Prime 163 := by norm_num

set_option maxRecDepth 100000 in
lemma pr12 : Nat.Prime 199 := by norm_num

set_option maxRecDepth 100000 in
lemma pr13 : Nat.Prime 223 := by norm_num

set_option maxRecDepth 100000 in
lemma pr14 : Nat.Prime 227 := by norm_num

set_option maxRecDepth 100000 in
lemma pr15 : Nat.Prime 467 := by norm_num

set_option maxRecDepth 100000 in
lemma pr16 : Nat.Prime 563 := by norm_num

set_option maxRecDepth 100000 in
lemma pr17 : Nat.Prime 643 := by norm_num

set_option maxRecDepth 100000 in
lemma pr18 : Nat.Prime 647 := by norm_num

set_option maxRecDepth 100000 in
lemma pr19 : Nat.Prime 719 := by norm_num

set_option maxRecDepth 100000 in
lemma pr20 : Nat.Prime 887 := by norm_num

set_option maxRecDepth 100000 in
lemma pr21 : Nat.Prime 991 := by norm_num

set_option maxRecDepth 100000 in
lemma pr22 : Nat.Prime 1999 := by norm_num

set_option maxRecDepth 100000 in
lemma pr23 : Nat.Prime 2819 := by norm_num

set_option maxRecDepth 100000 in
lemma pr24 : Nat.Prime 3331 := by norm_num

set_option maxRecDepth 100000 in
lemma pr25 : Nat.Prime 5843 := by norm_num

set_option maxRecDepth 100000 in
lemma pr26 : Nat.Prime 7591 := by norm_num

set_option maxRecDepth 100000 in
lemma pr27 : Nat.Prime 78607 := by norm_num

set_option maxRecDepth 100000 in
lemma pr28 : Nat.Prime 284003 := by norm_num

set_option maxRecDepth 100000 in
lemma pr29 : Nat.Prime 689891 := by norm_num

set_option maxRecDepth 100000 in
lemma pr30 : Nat.Prime 4326031 := by norm_num

set_option maxRecDepth 100000 in
lemma pr31 : Nat.Prime 7923067 := by norm_num

set_option maxRecDepth 100000 in
lemma pr32 : Nat.Prime 12504647 := by norm_num

set_option maxRecDepth 100000 in
lemma pr33 : Nat.Prime 19990307 := by norm_num

set_option maxRecDepth 100000 in
lemma pr34 : Nat.Prime 26905651 := by norm_num

set_option maxRecDepth 100000 in
lemma pr35 : Nat.Prime 27594131 := by norm_num

set_option maxRecDepth 100000 in
lemma pr36 : Nat.Prime 79512187 := by norm_num

set_option maxRecDepth 100000 in
lemma pr37 : Nat.Prime 200057419 := by norm_num

set_option maxRecDepth 100000 in
lemma pr38 : Nat.Prime 200080511 := by norm_num

set_option maxRecDepth 100000 in
lemma pr39 : Nat.Prime 399984727 := by norm_num

set_option maxRecDepth 10000 in
lemma plist_all : allPrime plist := ⟨pr0, pr1, pr2, pr3, pr4, pr5, pr6, pr7, pr8, pr9, pr10, pr11, pr12, pr13, pr14, pr15, pr16, pr17, pr18, pr19, pr20, pr21, pr22, pr23, pr24, pr25, pr26, pr27, pr28, pr29, pr30, pr31, pr32, pr33, pr34, pr35, pr36, pr37, pr38, pr39, trivial⟩

lemma plist_prime : ∀ q ∈ plist, q.Prime := allPrime_mem plist plist_all

/-- binomial(2c+1, c) for c = 0, ..., 15. -/
def bv : List ℕ := [1, 3, 10, 35, 126, 462, 1716, 6435, 24310, 92378, 352716, 1352078, 5200300, 20058300, 77558760, 300540195]

lemma bv_eq (c : ℕ) (hc : c ≤ 15) : OMA.S_oeis_a303639.binomial c = bv.getD c 0 := by
  unfold OMA.S_oeis_a303639.binomial
  interval_cases c <;>
    norm_num [bv, Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial, Nat.factorial]

/-- (c, d, q, k): q^k exactly divides N - binomial(2c+1,c) - binomial(2d+1,d). -/
def tab : List (ℕ × ℕ × ℕ × ℕ) := [(0, 0, 647, 1), (0, 1, 163, 1), (0, 2, 67, 1), (0, 3, 3, 1), (0, 4, 23, 1), (0, 5, 467, 1), (0, 6, 223, 1), (0, 7, 991, 1), (0, 8, 7, 1), (0, 9, 3, 1), (0, 10, 23, 1), (0, 11, 3, 1), (0, 12, 887, 1), (0, 13, 26905651, 1), (0, 14, 7, 1), (0, 15, 1999, 1), (1, 1, 3, 3), (1, 2, 643, 1), (1, 3, 19, 1), (1, 4, 3, 1), (1, 5, 3, 7), (1, 6, 3, 1), (1, 7, 3, 1), (1, 8, 78607, 1), (1, 9, 27594131, 1), (1, 10, 3, 1), (1, 11, 31, 1), (1, 12, 11, 1), (1, 13, 3, 1), (1, 14, 3, 1), (1, 15, 3, 1), (2, 2, 11, 1), (2, 3, 3, 1), (2, 4, 200080511, 1), (2, 5, 23, 1), (2, 6, 284003, 1), (2, 7, 4326031, 1), (2, 8, 19, 1), (2, 9, 3, 1), (2, 10, 399984727, 1), (2, 11, 3, 1), (2, 12, 79512187, 1), (2, 13, 127, 1), (2, 14, 2819, 1), (2, 15, 7, 1), (3, 3, 7, 1), (3, 4, 7, 1), (3, 5, 7, 1), (3, 6, 43, 1), (3, 7, 5843, 1), (3, 8, 3, 1), (3, 9, 7923067, 1), (3, 10, 7, 1), (3, 11, 7, 1), (3, 12, 3, 1), (3, 13, 23, 1), (3, 14, 23, 1), (3, 15, 23, 1), (4, 4, 3, 1), (4, 5, 3, 1), (4, 6, 719, 1), (4, 7, 3, 1), (4, 8, 563, 1), (4, 9, 200057419, 1), (4, 10, 3, 3), (4, 11, 7, 1), (4, 12, 7, 1), (4, 13, 3, 1), (4, 14, 3, 1), (4, 15, 3, 1), (5, 5, 3, 3), (5, 6, 3, 1), (5, 7, 3, 1), (5, 8, 12504647, 1), (5, 9, 23, 1), (5, 10, 3, 1), (5, 11, 7, 1), (5, 12, 7, 1), (5, 13, 3, 1), (5, 14, 3, 1), (5, 15, 3, 1), (6, 6, 3, 1), (6, 7, 19, 1), (6, 8, 7, 1), (6, 9, 7, 1), (6, 10, 3, 1), (6, 11, 139, 1), (6, 12, 227, 1), (6, 13, 11, 1), (6, 14, 3, 5), (6, 15, 67, 1), (7, 7, 3, 1), (7, 8, 199, 1), (7, 9, 31, 1), (7, 10, 31, 1), (7, 11, 3331, 1), (7, 12, 139, 1), (7, 13, 3, 1), (7, 14, 3, 1), (7, 15, 3, 1), (8, 8, 689891, 1), (8, 9, 3, 1), (8, 10, 223, 1), (8, 11, 3, 1), (8, 12, 59, 1), (8, 13, 11, 1), (8, 14, 7591, 1), (8, 15, 19990307, 1), (9, 9, 19, 1), (9, 10, 887, 1), (9, 11, 19, 1), (9, 12, 3, 1), (9, 13, 11, 1), (9, 14, 19, 1), (9, 15, 19, 1), (10, 10, 3, 1), (10, 11, 19, 1), (10, 12, 7, 1), (10, 13, 19, 1), (10, 14, 3, 3), (10, 15, 19, 1), (11, 11, 7, 1), (11, 12, 3, 1), (11, 13, 19, 1), (11, 14, 19, 1), (11, 15, 19, 1), (12, 12, 7, 1), (12, 13, 19, 1), (12, 14, 19, 1), (12, 15, 19, 1), (13, 13, 3, 1), (13, 14, 3, 1), (13, 15, 3, 1), (14, 14, 3, 1), (14, 15, 3, 1), (15, 15, 3, 1)]

def good (e : ℕ × ℕ × ℕ × ℕ) : Bool :=
  let r := 800322180 - bv.getD e.1 0 - bv.getD e.2.1 0
  decide (bv.getD e.1 0 + bv.getD e.2.1 0 ≤ 800322180) && plist.contains e.2.2.1 &&
    (e.2.2.1 % 4 == 3) && (e.2.2.2 % 2 == 1) && (r % e.2.2.1 ^ e.2.2.2 == 0) &&
    (r % e.2.2.1 ^ (e.2.2.2 + 1) != 0)

lemma tab_good : tab.all good = true := by decide +kernel

lemma cover : ∀ d, d < 16 → ∀ c, c < d + 1 → bv.getD c 0 + bv.getD d 0 ≤ 800322180 →
    tab.any (fun e => e.1 == c && e.2.1 == d) = true := by decide +kernel

lemma bv_big (d : ℕ) (hd : 16 ≤ d) : 800322180 < OMA.S_oeis_a303639.binomial d := by
  unfold OMA.S_oeis_a303639.binomial
  have h1 : (33 : ℕ).choose 16 ≤ (2 * d + 1).choose 16 := Nat.choose_le_choose 16 (by omega)
  have h2 : (2 * d + 1).choose 16 ≤ (2 * d + 1).choose d := by
    have := Nat.choose_le_middle 16 (2 * d + 1)
    rwa [show (2 * d + 1) / 2 = d by omega] at this
  have h3 : (33 : ℕ).choose 16 = 1166803110 := by
    norm_num [Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial, Nat.factorial]
  omega

end OMA.P_oeis_a303639

open OMA.P_oeis_a303639 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a303639.main) := by
  intro h
  obtain ⟨a, b, c, d, _, hcd, hn⟩ := h 800322180 (by norm_num)
  set s := a ^ 2 + b ^ 2 with hs
  have hdle : OMA.S_oeis_a303639.binomial d ≤ 800322180 := by rw [hn]; omega
  have hd : d ≤ 15 := by
    by_contra hd
    have := bv_big d (by omega)
    omega
  rw [bv_eq c (by omega), bv_eq d hd] at hn
  have hcov := cover d (by omega) c (by omega) (by omega)
  obtain ⟨e, he, hce⟩ := List.any_eq_true.1 hcov
  simp only [Bool.and_eq_true, beq_iff_eq] at hce
  obtain ⟨rfl, rfl⟩ := hce
  have hg := List.all_eq_true.1 tab_good e he
  simp only [good, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, bne_iff_ne, ne_eq,
    List.contains_iff_mem] at hg
  obtain ⟨⟨⟨⟨⟨_, hq⟩, h4⟩, hk⟩, h1⟩, h2⟩ := hg
  have hr : 800322180 - bv.getD e.1 0 - bv.getD e.2.1 0 = a ^ 2 + b ^ 2 := by omega
  rw [hr] at h1 h2
  exact not_sum_sq _ _ _ (plist_prime _ hq) h4 hk h1 h2 ⟨a, b, hs⟩
