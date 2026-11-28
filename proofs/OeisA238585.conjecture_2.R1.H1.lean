import OMAReductions.R_OeisA238585_conjecture_2_R1

/-! The first 44 primes suffice to evaluate all twelve listed indices. -/

open Finset

private def primeAt (i : ℕ) : ℕ :=
  (#[2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61,
    67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139,
    149, 151, 157, 163, 167, 173, 179, 181, 191, 193] : Array ℕ)[i]!

/-- Trial division only needs to examine possible factors through the square root. -/
private def trialPrime (n : ℕ) : Bool :=
  decide (2 ≤ n) && (List.range (n.sqrt + 1)).all (fun d => decide (d < 2 ∨ n % d ≠ 0))

private theorem trialPrime_iff (n : ℕ) : trialPrime n = true ↔ n.Prime := by
  simp only [trialPrime, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, Nat.prime_def_le_sqrt]
  constructor
  · rintro ⟨hn, h⟩
    refine ⟨hn, fun d hd hs hdvd => ?_⟩
    rcases h d (by omega) with hl | hnd
    · omega
    · exact hnd (Nat.mod_eq_zero_of_dvd hdvd)
  · rintro ⟨hn, h⟩
    refine ⟨hn, fun d hd => or_iff_not_imp_left.mpr (fun hl hmod => ?_)⟩
    exact h d (by omega) (by omega) (Nat.dvd_of_mod_eq_zero hmod)

private def computedPrimeCount (n : ℕ) : ℕ := (List.range n).countP trialPrime

private theorem computedPrimeCount_eq (n : ℕ) : computedPrimeCount n = Nat.count Nat.Prime n := by
  unfold computedPrimeCount Nat.count
  congr 1
  funext d
  exact Bool.eq_iff_iff.mpr (by simp [trialPrime_iff])

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem primeTableCertified : (List.range 44).all (fun i =>
    trialPrime (primeAt i) && decide (computedPrimeCount (primeAt i) = i)) = true := by
  decide +kernel

private theorem nth_prime_eq_primeAt {i : ℕ} (hi : i < 44) : Nat.nth Nat.Prime i = primeAt i := by
  have hc := List.all_eq_true.mp primeTableCertified i (List.mem_range.mpr hi)
  simp only [Bool.and_eq_true, trialPrime_iff, decide_eq_true_eq, computedPrimeCount_eq] at hc
  calc
    Nat.nth Nat.Prime i = Nat.nth Nat.Prime (Nat.count Nat.Prime (primeAt i)) :=
      congrArg (Nat.nth Nat.Prime) hc.2.symm
    _ = primeAt i := Nat.nth_count hc.1

private def computedCount (n : ℕ) : ℕ :=
  ∑ p ∈ Ico 1 n,
    if trialPrime p && trialPrime (primeAt (p - 1) ^ 2 + (primeAt (n - 1) - 1) ^ 2)
    then 1 else 0

private theorem count_eq_computedCount {n : ℕ} (hn : n ≤ 44) :
    OeisA238585.a n = computedCount n := by
  unfold OeisA238585.a computedCount
  apply sum_congr rfl
  intro p hp
  have hpn := (mem_Ico.mp hp).2
  rw [nth_prime_eq_primeAt (show p - 1 < 44 by omega),
    nth_prime_eq_primeAt (show n - 1 < 44 by omega)]
  simp only [Bool.and_eq_true, trialPrime_iff]

private def listed : List ℕ := [4, 5, 7, 10, 11, 12, 19, 21, 22, 31, 42, 44]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem listedCounts : listed.all (fun n => decide (computedCount n = 1)) = true := by
  decide +kernel

theorem OMA.solution : OMA.R_OeisA238585_conjecture_2_R1.H1 := by
  intro n hn
  have hlisted : n ∈ listed := by
    simpa [listed, List.mem_cons, Set.mem_insert_iff, Set.mem_singleton_iff] using hn
  have hbound : listed.all (fun n => decide (n ≤ 44)) = true := by decide
  have hle : n ≤ 44 := of_decide_eq_true (List.all_eq_true.mp hbound n hlisted)
  rw [count_eq_computedCount hle]
  exact of_decide_eq_true (List.all_eq_true.mp listedCounts n hlisted)
