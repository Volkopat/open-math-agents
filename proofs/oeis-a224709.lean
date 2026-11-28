import OMAStatements.S_oeis_a224709
import Mathlib

-- Disproof of the A224709 conjecture at n = 13344: a(40041) = a(40040) = 33203,
-- so a(3n+9) > a(3n+8) fails. Primality below 80089 = 283^2 is decided by one gcd with 282!.

namespace A224709

open OMA.S_oeis_a224709

def F : ℕ := 1329068837384190068811150283189534157917248156984147973342429842044408817655739386347513129353362435849569694522424163497637753176795095401983716205184963777702786397656418169231229017315072038237563761242039022268879475091778340489571294395827541820719781068066789360900574790260546178182785084148575662177166918890536883308516366440681125228122921464309137998824059298263006744606693799345715148254400816380503667266738285815849549335166436915152644393492871088208158525432747246896051475099982757888000000000000000000000000000000000000000000000000000000000000000000000

theorem F_eq : Nat.factorial 282 = F := by decide +kernel

def isPr (q : ℕ) : Bool :=
  if q < 283 then (decide (2 ≤ q) && Nat.gcd q (Nat.factorial (q - 1)) == 1) else Nat.gcd q F == 1

def isC (m : ℕ) : Bool := decide (1 < m) && !isPr m

def gp (n x : ℕ) : Bool := isC x && isC (2 * n - x)

theorem prime_of_gcd (q k : ℕ) (h2 : 2 ≤ q) (hq : q < (k + 1) ^ 2)
    (hg : Nat.gcd q (Nat.factorial k) = 1) : q.Prime := by
  by_contra hp
  have hm := Nat.minFac_sq_le_self (by omega) hp
  have hmp := Nat.minFac_prime (show q ≠ 1 by omega)
  have hmk : q.minFac ≤ k := by
    by_contra h
    have h' : k + 1 ≤ q.minFac := by omega
    have := Nat.pow_le_pow_left h' 2
    linarith
  have h1 : q.minFac ∣ Nat.gcd q (Nat.factorial k) :=
    Nat.dvd_gcd (Nat.minFac_dvd q) (Nat.dvd_factorial hmp.pos hmk)
  rw [hg] at h1
  exact hmp.one_lt.ne' (Nat.dvd_one.mp h1)

theorem gcd_of_prime (q k : ℕ) (hp : q.Prime) (hk : k < q) : Nat.gcd q (Nat.factorial k) = 1 := by
  have h : ¬ q ∣ Nat.factorial k := by
    rw [hp.dvd_factorial]
    omega
  exact (Nat.Prime.coprime_iff_not_dvd hp).mpr h

theorem isPr_iff (q : ℕ) (hq : q < 80089) : isPr q = true ↔ q.Prime := by
  unfold isPr
  split_ifs with h
  · simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    constructor
    · rintro ⟨h2, hg⟩
      have e : q - 1 + 1 = q := by omega
      exact prime_of_gcd q (q - 1) h2 (by rw [e]; nlinarith) hg
    · intro hp
      exact ⟨hp.two_le, gcd_of_prime q (q - 1) hp (by have := hp.two_le; omega)⟩
  · simp only [beq_iff_eq]
    constructor
    · intro hg
      rw [← F_eq] at hg
      exact prime_of_gcd q 282 (by omega) (lt_of_lt_of_eq hq (by norm_num)) hg
    · intro hp
      rw [← F_eq]
      exact gcd_of_prime q 282 hp (by omega)

theorem isC_iff (m : ℕ) (hm : m < 80089) : isC m = true ↔ IsComposite m := by
  have h := isPr_iff m hm
  unfold isC IsComposite
  cases hb : isPr m <;> simp_all

theorem card_filter_Icc (n : ℕ) (b : ℕ → Bool) :
    ((Finset.Icc 1 n).filter (fun x => b x = true)).card = (List.range' 1 n).countP b := by
  rw [Nat.Icc_eq_range', Finset.card, Finset.filter_val, Multiset.filter_coe, Multiset.coe_card,
    List.countP_eq_length_filter]
  simp

theorem a_eq (n : ℕ) (hn : 2 * n < 80089) : a n = (List.range' 1 n).countP (gp n) := by
  unfold a
  have hc : (Finset.Icc 1 n).filter (fun x => IsComposite x ∧ IsComposite (2 * n - x)) =
      (Finset.Icc 1 n).filter (fun x => gp n x = true) := by
    apply Finset.filter_congr
    intro x hx
    rw [Finset.mem_Icc] at hx
    simp only [gp, Bool.and_eq_true]
    rw [isC_iff x (by omega), isC_iff (2 * n - x) (by omega)]
  rw [hc, card_filter_Icc]

theorem comb {g : ℕ → Bool} {s L K s' L' K' : ℕ} (h1 : (List.range' s L).countP g = K)
    (h2 : (List.range' s' L').countP g = K') (hs : s + L = s') :
    (List.range' s (L + L')).countP g = K + K' := by
  subst hs
  rw [← List.range'_append_1, List.countP_append, h1, h2]


def c40040_0 : (List.range' 1 4000).countP (gp 40040) = 3222 := by decide +kernel
def c40040_1 : (List.range' 4001 4000).countP (gp 40040) = 3289 := by decide +kernel
def c40040_2 : (List.range' 8001 4000).countP (gp 40040) = 3319 := by decide +kernel
def c40040_3 : (List.range' 12001 4000).countP (gp 40040) = 3319 := by decide +kernel
def c40040_4 : (List.range' 16001 4000).countP (gp 40040) = 3337 := by decide +kernel
def c40040_5 : (List.range' 20001 4000).countP (gp 40040) = 3317 := by decide +kernel
def c40040_6 : (List.range' 24001 4000).countP (gp 40040) = 3346 := by decide +kernel
def c40040_7 : (List.range' 28001 4000).countP (gp 40040) = 3339 := by decide +kernel
def c40040_8 : (List.range' 32001 4000).countP (gp 40040) = 3344 := by decide +kernel
def c40040_9 : (List.range' 36001 4000).countP (gp 40040) = 3337 := by decide +kernel
def c40040_10 : (List.range' 40001 40).countP (gp 40040) = 34 := by decide +kernel

theorem t40040 : (List.range' 1 40040).countP (gp 40040) = 33203 := by
  have h := (comb c40040_0 (comb c40040_1 (comb c40040_2 (comb c40040_3 (comb c40040_4 (comb c40040_5 (comb c40040_6 (comb c40040_7 (comb c40040_8 (comb c40040_9 c40040_10 (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num))
  simp only [Nat.reduceAdd] at h
  exact h

def c40041_0 : (List.range' 1 4000).countP (gp 40041) = 3219 := by decide +kernel
def c40041_1 : (List.range' 4001 4000).countP (gp 40041) = 3291 := by decide +kernel
def c40041_2 : (List.range' 8001 4000).countP (gp 40041) = 3313 := by decide +kernel
def c40041_3 : (List.range' 12001 4000).countP (gp 40041) = 3321 := by decide +kernel
def c40041_4 : (List.range' 16001 4000).countP (gp 40041) = 3342 := by decide +kernel
def c40041_5 : (List.range' 20001 4000).countP (gp 40041) = 3314 := by decide +kernel
def c40041_6 : (List.range' 24001 4000).countP (gp 40041) = 3343 := by decide +kernel
def c40041_7 : (List.range' 28001 4000).countP (gp 40041) = 3344 := by decide +kernel
def c40041_8 : (List.range' 32001 4000).countP (gp 40041) = 3333 := by decide +kernel
def c40041_9 : (List.range' 36001 4000).countP (gp 40041) = 3348 := by decide +kernel
def c40041_10 : (List.range' 40001 41).countP (gp 40041) = 35 := by decide +kernel

theorem t40041 : (List.range' 1 40041).countP (gp 40041) = 33203 := by
  have h := (comb c40041_0 (comb c40041_1 (comb c40041_2 (comb c40041_3 (comb c40041_4 (comb c40041_5 (comb c40041_6 (comb c40041_7 (comb c40041_8 (comb c40041_9 c40041_10 (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num))
  simp only [Nat.reduceAdd] at h
  exact h

end A224709

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a224709.main) := by
  intro h
  have h1 := (h 13344 (by norm_num)).1
  simp only [Nat.reduceMul, Nat.reduceAdd] at h1
  rw [A224709.a_eq 40041 (by norm_num), A224709.a_eq 40040 (by norm_num), A224709.t40041,
    A224709.t40040] at h1
  omega
