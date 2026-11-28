import OMAStatements.S_oeis_a126693
import Mathlib.Data.Nat.Nth

-- Problem: A126693: Prime numbers p such that 10000-p is also a prime
-- Credit: @Luckylamb666

open OMA.S_oeis_a126693

namespace OMA_A126693_Proof

def smallPrimes : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97]

def fastPrime (n : ℕ) : Bool :=
  2 ≤ n && smallPrimes.all (fun p => n == p || n % p != 0)

def fastIsTerm (p : ℕ) : Bool :=
  fastPrime p && fastPrime (10000 - p)

lemma smallPrimes_prime : ∀ p ∈ smallPrimes, p.Prime := by
  decide

lemma prime_le_100_mem_smallPrimes : ∀ p < 101, p.Prime → p ∈ smallPrimes := by
  decide

lemma fastPrime_iff {n : ℕ} (hn : n ≤ 10000) : fastPrime n = true ↔ n.Prime := by
  unfold fastPrime
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true,
    beq_iff_eq, bne_iff_ne, ne_eq]
  constructor
  · rintro ⟨h2, hall⟩
    by_contra hnp
    have hmf_prime : n.minFac.Prime := Nat.minFac_prime (by omega)
    have hmf_sq : n.minFac ^ 2 ≤ n := Nat.minFac_sq_le_self (by omega) hnp
    have hmf_lt : n.minFac < 101 := by nlinarith
    have hmem : n.minFac ∈ smallPrimes := prime_le_100_mem_smallPrimes n.minFac hmf_lt hmf_prime
    have hcases := hall n.minFac hmem
    have hdvd : n.minFac ∣ n := Nat.minFac_dvd n
    have hmod : n % n.minFac = 0 := Nat.mod_eq_zero_of_dvd hdvd
    rcases hcases with heq | hne
    · rw [heq] at hnp
      exact hnp hmf_prime
    · exact hne hmod
  · intro hp
    refine ⟨hp.two_le, ?_⟩
    intro q hq
    by_cases hmod : n % q = 0
    · left
      have hdvd : q ∣ n := Nat.dvd_of_mod_eq_zero hmod
      have hqp : q.Prime := smallPrimes_prime q hq
      rcases hp.eq_one_or_self_of_dvd q hdvd with h1 | hself
      · exact absurd h1 hqp.ne_one
      · exact hself.symm
    · right
      exact hmod

lemma fastIsTerm_iff (p : ℕ) : fastIsTerm p = true ↔ IsTerm p := by
  unfold fastIsTerm IsTerm
  simp only [Bool.and_eq_true]
  constructor
  · rintro ⟨h1, h2⟩
    have hge2 : 2 ≤ 10000 - p := by
      unfold fastPrime at h2
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
      exact h2.1
    have hp_le : p ≤ 10000 := by omega
    have hsub_le : 10000 - p ≤ 10000 := by omega
    exact ⟨(fastPrime_iff hp_le).mp h1, (fastPrime_iff hsub_le).mp h2⟩
  · rintro ⟨h1, h2⟩
    have hge2 : 2 ≤ 10000 - p := h2.two_le
    have hp_le : p ≤ 10000 := by omega
    have hsub_le : 10000 - p ≤ 10000 := by omega
    exact ⟨(fastPrime_iff hp_le).mpr h1, (fastPrime_iff hsub_le).mpr h2⟩

def countRange : ℕ → ℕ → ℕ → ℕ
  | _, 0, acc => acc
  | start, len + 1, acc => countRange (start + 1) len (if fastIsTerm start then acc + 1 else acc)

open scoped Classical in
lemma countRange_eq (start len acc : ℕ) :
    countRange start len acc + Nat.count IsTerm start = acc + Nat.count IsTerm (start + len) := by
  induction len generalizing start acc with
  | zero =>
    simp [countRange]
  | succ len ih =>
    unfold countRange
    have hstep : start + (len + 1) = (start + 1) + len := by omega
    rw [hstep]
    have hrec := ih (start + 1) (if fastIsTerm start then acc + 1 else acc)
    have hcnt : Nat.count IsTerm (start + 1) = Nat.count IsTerm start + if IsTerm start then 1 else 0 := by
      rw [Nat.count_succ]
    have hiff : fastIsTerm start = true ↔ IsTerm start := fastIsTerm_iff start
    by_cases h : fastIsTerm start = true
    · have ht : IsTerm start := hiff.mp h
      simp only [h, ↓reduceIte] at hrec ⊢
      simp only [ht, ↓reduceIte] at hcnt
      omega
    · have hf : ¬ IsTerm start := fun ht => h (hiff.mpr ht)
      simp only [h, Bool.false_eq_true, ↓reduceIte] at hrec ⊢
      simp only [hf, ↓reduceIte] at hcnt
      omega

def allFalseRange : ℕ → ℕ → Bool
  | 0, _ => true
  | len + 1, start => !fastIsTerm start && allFalseRange len (start + 1)

lemma allFalseRange_sound (len start : ℕ) (h : allFalseRange len start = true) :
    ∀ p, start ≤ p → p < start + len → fastIsTerm p = false := by
  induction len generalizing start with
  | zero =>
    intro p h1 h2; omega
  | succ len ih =>
    unfold allFalseRange at h
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
    intro p h1 h2
    rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
    · exact h.1
    · exact ih (start + 1) h.2 p (by omega) (by omega)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
lemma chunk0 : countRange 0 1000 0 = 33 := by decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
lemma chunk1 : countRange 1000 1000 0 = 25 := by decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
lemma chunk2 : countRange 2000 1000 0 = 26 := by decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
lemma chunk3 : countRange 3000 1000 0 = 21 := by decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
lemma chunk4 : countRange 4000 1000 0 = 22 := by decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
lemma chunk5 : countRange 5000 1000 0 = 22 := by decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
lemma chunk6 : countRange 6000 1000 0 = 21 := by decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
lemma chunk7 : countRange 7000 1000 0 = 26 := by decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
lemma chunk8 : countRange 8000 1000 0 = 25 := by decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
lemma chunk9 : countRange 9000 941 0 = 32 := by decide

lemma isTerm_9941 : fastIsTerm 9941 = true := by
  decide

lemma no_term_above_9941 : allFalseRange 60 9942 = true := by
  decide

open scoped Classical in
lemma count_eq_253 : Nat.count IsTerm 9941 = 253 := by
  have h0 := countRange_eq 0 1000 0
  have h1 := countRange_eq 1000 1000 0
  have h2 := countRange_eq 2000 1000 0
  have h3 := countRange_eq 3000 1000 0
  have h4 := countRange_eq 4000 1000 0
  have h5 := countRange_eq 5000 1000 0
  have h6 := countRange_eq 6000 1000 0
  have h7 := countRange_eq 7000 1000 0
  have h8 := countRange_eq 8000 1000 0
  have h9 := countRange_eq 9000 941 0
  have hz : Nat.count IsTerm 0 = 0 := Nat.count_zero IsTerm
  rw [chunk0, hz, show (0 + 1000 : ℕ) = 1000 from rfl] at h0
  rw [chunk1, show (1000 + 1000 : ℕ) = 2000 from rfl] at h1
  rw [chunk2, show (2000 + 1000 : ℕ) = 3000 from rfl] at h2
  rw [chunk3, show (3000 + 1000 : ℕ) = 4000 from rfl] at h3
  rw [chunk4, show (4000 + 1000 : ℕ) = 5000 from rfl] at h4
  rw [chunk5, show (5000 + 1000 : ℕ) = 6000 from rfl] at h5
  rw [chunk6, show (6000 + 1000 : ℕ) = 7000 from rfl] at h6
  rw [chunk7, show (7000 + 1000 : ℕ) = 8000 from rfl] at h7
  rw [chunk8, show (8000 + 1000 : ℕ) = 9000 from rfl] at h8
  rw [chunk9, show (9000 + 941 : ℕ) = 9941 from rfl] at h9
  omega

lemma le_9941 (p : ℕ) (hp : IsTerm p) : p ≤ 9941 := by
  have hge2 : 2 ≤ 10000 - p := hp.2.two_le
  have hp_le : p ≤ 9998 := by omega
  by_contra hgt
  have hfalse : fastIsTerm p = false :=
    allFalseRange_sound 60 9942 no_term_above_9941 p (by omega) (by omega)
  have htrue : fastIsTerm p = true := (fastIsTerm_iff p).mpr hp
  rw [hfalse] at htrue
  exact Bool.false_ne_true htrue

end OMA_A126693_Proof

open scoped Classical in
theorem OMA.solution : type_of% @OMA.S_oeis_a126693.main := by
  refine ⟨?_, OMA_A126693_Proof.le_9941⟩
  have h9941 : IsTerm 9941 := (OMA_A126693_Proof.fastIsTerm_iff 9941).mp OMA_A126693_Proof.isTerm_9941
  have hcnt : Nat.count IsTerm 9941 = 253 := OMA_A126693_Proof.count_eq_253
  rw [← hcnt]
  exact Nat.nth_count h9941
