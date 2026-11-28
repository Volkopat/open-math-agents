import OMAReductions.R_GoldbachConjecture_goldbach_R2

-- Step GoldbachConjecture.goldbach.R2.H1
-- Credit: @caa1982

private def smallPrimes : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73,
   79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163,
   167, 173, 179, 181, 191, 193, 197, 199, 211, 223]

private def checkDivs (n : ℕ) : List ℕ → Bool
  | [] => true
  | p :: ps =>
    if p * p > n then true
    else if n % p == 0 then false
    else checkDivs n ps

private def isPrimeFast (n : ℕ) : Bool :=
  if n < 2 then false else checkDivs n smallPrimes

private lemma smallPrimes_spec :
    smallPrimes.Pairwise (· ≤ ·) ∧
    (∀ p ∈ smallPrimes, p.Prime) ∧
    (∀ p : ℕ, p < 227 → p.Prime → p ∈ smallPrimes) := by
  decide +kernel

private lemma checkDivs_sound (n : ℕ) (ps : List ℕ) (hsort : ps.Pairwise (· ≤ ·))
    (h : checkDivs n ps = true) : ∀ p ∈ ps, p * p ≤ n → ¬ p ∣ n := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    have ⟨hp_le, hps_sort⟩ := List.pairwise_cons.mp hsort
    unfold checkDivs at h
    split_ifs at h with h1 h2
    · intro q hq hqle
      rcases List.mem_cons.mp hq with rfl | hq'
      · omega
      · have hpq : p ≤ q := hp_le q hq'
        have : p * p ≤ q * q := Nat.mul_le_mul hpq hpq
        omega
    · simp only [beq_iff_eq] at h2
      have hndvd : ¬ p ∣ n := fun hd => h2 (Nat.mod_eq_zero_of_dvd hd)
      intro q hq hqle
      rcases List.mem_cons.mp hq with rfl | hq'
      · exact hndvd
      · exact ih hps_sort h q hq' hqle

private lemma prime_of_isPrimeFast {n : ℕ} (hn : n < 51529) (h : isPrimeFast n = true) :
    n.Prime := by
  unfold isPrimeFast at h
  split_ifs at h with hlt
  have hall := checkDivs_sound n smallPrimes smallPrimes_spec.1 h
  by_contra hnp
  set p := n.minFac
  have hp : p.Prime := Nat.minFac_prime (by omega)
  have hpdvd : p ∣ n := Nat.minFac_dvd n
  have hpsq : p ^ 2 ≤ n := Nat.minFac_sq_le_self (by omega) hnp
  have hp_lt : p < 227 := by nlinarith
  have hpmem : p ∈ smallPrimes := smallPrimes_spec.2.2 p hp_lt hp
  exact hall p hpmem (by nlinarith) hpdvd

private def hasGoldbach (n : ℕ) : Bool :=
  smallPrimes.any fun p => decide (p < n) && isPrimeFast (n - p)

private def checkChunk (lo len : ℕ) : Bool :=
  match len with
  | 0 => true
  | r + 1 => hasGoldbach (2 * lo) && checkChunk (lo + 1) r

private lemma checkChunk_sound (lo len : ℕ) (h : checkChunk lo len = true) :
    ∀ m : ℕ, lo ≤ m → m < lo + len → hasGoldbach (2 * m) = true := by
  induction len generalizing lo with
  | zero => intro m h1 h2; omega
  | succ r ih =>
    unfold checkChunk at h
    simp only [Bool.and_eq_true] at h
    intro m hm1 hm2
    rcases eq_or_lt_of_le hm1 with rfl | hlt
    · exact h.1
    · exact ih (lo + 1) h.2 m (by omega) (by omega)

set_option maxHeartbeats 800000 in
private lemma chk0 : checkChunk 2 2499 = true := by decide +kernel
set_option maxHeartbeats 800000 in
private lemma chk1 : checkChunk 2501 2500 = true := by decide +kernel
set_option maxHeartbeats 800000 in
private lemma chk2 : checkChunk 5001 2500 = true := by decide +kernel
set_option maxHeartbeats 800000 in
private lemma chk3 : checkChunk 7501 2500 = true := by decide +kernel
set_option maxHeartbeats 800000 in
private lemma chk4 : checkChunk 10001 2500 = true := by decide +kernel
set_option maxHeartbeats 800000 in
private lemma chk5 : checkChunk 12501 2500 = true := by decide +kernel
set_option maxHeartbeats 800000 in
private lemma chk6 : checkChunk 15001 2500 = true := by decide +kernel
set_option maxHeartbeats 800000 in
private lemma chk7 : checkChunk 17501 2500 = true := by decide +kernel
set_option maxHeartbeats 800000 in
private lemma chk8 : checkChunk 20001 2500 = true := by decide +kernel
set_option maxHeartbeats 800000 in
private lemma chk9 : checkChunk 22501 2500 = true := by decide +kernel

theorem OMA.solution : OMA.R_GoldbachConjecture_goldbach_R2.H1 := by
  intro n hn2 heven hn50k
  obtain ⟨m, rfl⟩ := heven
  have hm_eq : m + m = 2 * m := by ring
  rw [hm_eq] at hn2 hn50k ⊢
  have hgb : hasGoldbach (2 * m) = true := by
    by_cases h0 : m < 2501
    · exact checkChunk_sound 2 2499 chk0 m (by omega) (by omega)
    by_cases h1 : m < 5001
    · exact checkChunk_sound 2501 2500 chk1 m (by omega) (by omega)
    by_cases h2 : m < 7501
    · exact checkChunk_sound 5001 2500 chk2 m (by omega) (by omega)
    by_cases h3 : m < 10001
    · exact checkChunk_sound 7501 2500 chk3 m (by omega) (by omega)
    by_cases h4 : m < 12501
    · exact checkChunk_sound 10001 2500 chk4 m (by omega) (by omega)
    by_cases h5 : m < 15001
    · exact checkChunk_sound 12501 2500 chk5 m (by omega) (by omega)
    by_cases h6 : m < 17501
    · exact checkChunk_sound 15001 2500 chk6 m (by omega) (by omega)
    by_cases h7 : m < 20001
    · exact checkChunk_sound 17501 2500 chk7 m (by omega) (by omega)
    by_cases h8 : m < 22501
    · exact checkChunk_sound 20001 2500 chk8 m (by omega) (by omega)
    exact checkChunk_sound 22501 2500 chk9 m (by omega) (by omega)
  simp only [hasGoldbach, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hgb
  obtain ⟨p, hp_mem, hp_lt, hq_fast⟩ := hgb
  have hp : p.Prime := smallPrimes_spec.2.1 p hp_mem
  have hq : (2 * m - p).Prime := prime_of_isPrimeFast (by omega) hq_fast
  exact ⟨p, 2 * m - p, Nat.prime_iff.mp hp, Nat.prime_iff.mp hq, by omega⟩
