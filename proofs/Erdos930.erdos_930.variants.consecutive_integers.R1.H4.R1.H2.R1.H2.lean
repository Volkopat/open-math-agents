import OMAReductions.R_Erdos930_erdos_930_variants_consecutive_integers_R1_H4_R1_H2_R1

/-! A kernel-checked certificate for the range from 30000 to 60183. Primes are counted in
blocks with a gcd test against the product of the primes below 246, which every prime from
246 on passes. On a geometric grid of ratio 1.004 starting at 30000 the logarithm is at most
10.32 + 0.004 j at the j-th grid point, and on each grid interval the count at its right end
times this bound is at most its left end. -/

namespace OMA930b

/-- The primes below 246. -/
def SP : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241]

/-- The product of the primes below 246. -/
def Q : ℕ := 256041159035492609053110100510385311995538591998443060216114576417920917800321526504084465112487730

def isP (n : ℕ) : Bool := if n < 246 then SP.contains n else Nat.beq (Nat.gcd n Q) 1

def blkCount : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k + 1, n => (isP n).toNat + blkCount k (n + 1)

lemma SP_static : SP.all (fun a => decide (0 < a) && decide (a < 246)) = true := by
  decide +kernel

lemma Q_eq : Q = SP.prod := by decide +kernel

lemma small_static : (List.range 246).all (fun n => SP.contains n || decide (n < 2) ||
    (List.range n).any (fun d => decide (2 ≤ d) && decide (n % d = 0))) = true := by
  decide +kernel

lemma prime_isP {n : ℕ} (hp : n.Prime) : isP n = true := by
  unfold isP
  by_cases h : n < 246
  · rw [if_pos h]
    have hs := small_static
    rw [List.all_eq_true] at hs
    have h1 := hs n (List.mem_range.2 h)
    simp only [Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true, List.mem_range,
      Bool.and_eq_true] at h1
    rcases h1 with (h1 | h1) | ⟨d, hd, hd2, hd3⟩
    · exact h1
    · exact absurd hp.two_le (not_le.2 h1)
    · have hdvd : d ∣ n := Nat.dvd_of_mod_eq_zero hd3
      rcases (Nat.dvd_prime hp).1 hdvd with h2 | h2
      · omega
      · omega
  · rw [if_neg h]
    have hnd : ¬ n ∣ Q := by
      rw [Q_eq, (Nat.Prime.prime hp).dvd_prod_iff]
      rintro ⟨a, ha, hna⟩
      have hs := SP_static
      rw [List.all_eq_true] at hs
      have h1 := hs a ha
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
      have h2 := Nat.le_of_dvd h1.1 hna
      omega
    have hcop : Nat.gcd n Q = 1 := (Nat.Prime.coprime_iff_not_dvd hp).2 hnd
    rw [hcop]
    rfl

lemma count_add_le : ∀ len b,
    Nat.count Nat.Prime (b + len) ≤ Nat.count Nat.Prime b + blkCount len b := by
  intro len
  induction len with
  | zero =>
    intro b
    simp [blkCount]
  | succ len ih =>
    intro b
    have h1 := ih (b + 1)
    have h2 : b + (len + 1) = b + 1 + len := by omega
    rw [h2, blkCount]
    have h3 : Nat.count Nat.Prime (b + 1) ≤ Nat.count Nat.Prime b + (isP b).toNat := by
      rw [Nat.count_succ]
      by_cases hp : Nat.Prime b
      · rw [if_pos hp, prime_isP hp]
        exact le_of_eq rfl
      · rw [if_neg hp]
        omega
    omega

def Cnt (b c : ℕ) : Prop := Nat.count Nat.Prime b ≤ c

lemma cstep (b len c d : ℕ) (h : Cnt b c) (hd : blkCount len b = d) :
    Cnt (b + len) (c + d) := by
  have h1 := count_add_le len b
  unfold Cnt at *
  omega

lemma log_30000 : Real.log 30000 ≤ 10.32 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have h1 : Real.exp 10.32 = Real.exp 1 ^ 10 * Real.exp 0.32 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    norm_num
  rw [h1]
  have h2 : (2.7182818283:ℝ) ^ 10 ≤ Real.exp 1 ^ 10 :=
    pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 10
  have h3 : (1.3712:ℝ) ≤ Real.exp 0.32 := by
    have h := Real.quadratic_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 0.32)
    exact le_trans (by norm_num) h
  have h4 : (22026:ℝ) ≤ (2.7182818283:ℝ) ^ 10 := by norm_num
  calc (30000:ℝ) ≤ 22026 * 1.3712 := by norm_num
    _ ≤ Real.exp 1 ^ 10 * Real.exp 0.32 :=
        mul_le_mul (h4.trans h2) h3 (by norm_num) (by positivity)

lemma log_grid (a' j : ℕ) (hpos : 0 < a') (hgrid : a' * 1000 ^ j ≤ 30000 * 1004 ^ j) :
    Real.log a' ≤ 10.32 + 0.004 * j := by
  have hR : (a':ℝ) * 1000 ^ j ≤ 30000 * 1004 ^ j := by exact_mod_cast hgrid
  have ha : (0:ℝ) < a' := by exact_mod_cast hpos
  have h := Real.log_le_log (by positivity) hR
  rw [Real.log_mul ha.ne' (by positivity), Real.log_mul (by norm_num) (by positivity),
    Real.log_pow, Real.log_pow] at h
  have h1 : Real.log 1004 - Real.log 1000 ≤ 0.004 := by
    rw [← Real.log_div (by norm_num) (by norm_num)]
    exact (Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 1004 / 1000)).trans (by norm_num)
  have h2 := log_30000
  have hj : (0:ℝ) ≤ j := Nat.cast_nonneg j
  have h3 := mul_le_mul_of_nonneg_left h1 hj
  linarith

lemma interval (a a' P j : ℕ) (ha : 30000 ≤ a) (hc : Cnt a' P)
    (hgrid : a' * 1000 ^ j ≤ 30000 * 1004 ^ j) (hnum : P * (9120 + 4 * j) ≤ 1000 * a)
    (k : ℕ) (hak : a ≤ k) (hka : k < a') :
    (k.primesBelow.card : ℝ) * (Real.log k - 6/5) ≤ k := by
  have hk3 : (30000:ℝ) ≤ k := by exact_mod_cast (by omega : 30000 ≤ k)
  have hkpos : (0:ℝ) < k := by linarith
  have hcard : (k.primesBelow.card : ℝ) ≤ P := by
    have h1 : k.primesBelow.card ≤ P := by
      rw [Nat.primesBelow_card_eq_primeCounting']
      show Nat.count Nat.Prime k ≤ P
      exact le_trans (Nat.count_monotone _ hka.le) hc
    exact_mod_cast h1
  have hlogk : Real.log k ≤ 10.32 + 0.004 * j :=
    (Real.log_le_log hkpos (by exact_mod_cast hka.le)).trans (log_grid a' j (by omega) hgrid)
  have hlog0 : (6/5 : ℝ) ≤ Real.log k := by
    rw [Real.le_log_iff_exp_le hkpos]
    have h2 : Real.exp (6/5) ≤ Real.exp (1 + 1) := Real.exp_le_exp.2 (by norm_num)
    rw [Real.exp_add] at h2
    have h3 := Real.exp_one_lt_d9
    have h4 := Real.exp_pos 1
    have h5 := mul_lt_mul'' h3 h3 h4.le h4.le
    linarith
  have hnumR : (P:ℝ) * (9120 + 4 * j) ≤ 1000 * a := by exact_mod_cast hnum
  have hakR : (a:ℝ) ≤ k := by exact_mod_cast hak
  have hP0 : (0:ℝ) ≤ P := Nat.cast_nonneg P
  calc (k.primesBelow.card : ℝ) * (Real.log k - 6/5)
      ≤ P * (Real.log k - 6/5) := mul_le_mul_of_nonneg_right hcard (by linarith)
    _ ≤ P * (10.32 + 0.004 * j - 6/5) := mul_le_mul_of_nonneg_left (by linarith) hP0
    _ = (P * (9120 + 4 * j)) / 1000 := by ring
    _ ≤ (1000 * a) / 1000 := div_le_div_of_nonneg_right hnumR (by norm_num)
    _ = a := by ring
    _ ≤ k := hakR

def Good (b : ℕ) : Prop :=
  ∀ k : ℕ, 30000 ≤ k → k < b → (k.primesBelow.card : ℝ) * (Real.log k - 6/5) ≤ k

lemma extend (a a' P j : ℕ) (hg : Good a) (ha : 30000 ≤ a) (hc : Cnt a' P)
    (hgrid : a' * 1000 ^ j ≤ 30000 * 1004 ^ j) (hnum : P * (9120 + 4 * j) ≤ 1000 * a) :
    Good a' := by
  intro k hk hlt
  by_cases h : k < a
  · exact hg k hk h
  · exact interval a a' P j ha hc hgrid hnum k (not_lt.1 h) hlt

/-- Count primes in blocks of 1000 up to 30000, then walk the geometric grid, checking each step. -/
def W : ℕ → ℕ → ℕ → ℕ → Bool
  | 0, _, a, _ => a == 60184
  | n + 1, j, a, c =>
    if a + 1000 ≤ 30000 then W n j (a + 1000) (c + blkCount 1000 a)
    else
      let b := min 60184 (30000 * 1004 ^ j / 1000 ^ j)
      let d := c + blkCount (b - a) a
      decide (30000 ≤ a ∧ a ≤ b ∧ b * 1000 ^ j ≤ 30000 * 1004 ^ j ∧ d * (9120 + 4 * j) ≤ 1000 * a) &&
        W n (j + 1) b d

set_option maxRecDepth 100000 in
lemma S : ∀ n j a c, W n j a c = true → Cnt a c → Good a → Good 60184
  | 0, j, a, c, h, _, g => by
    simp only [W, beq_iff_eq] at h
    subst h
    exact g
  | n + 1, j, a, c, h, hc, g => by
    unfold W at h
    split_ifs at h with h0
    · exact S n j _ _ h (cstep a 1000 c (blkCount 1000 a) hc rfl) (fun k h1 h2 => by omega)
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨h1, h2, h3, h4⟩, h5⟩ := h
      have := cstep a (min 60184 (30000 * 1004 ^ j / 1000 ^ j) - a) c _ hc rfl
      rw [Nat.add_sub_cancel' h2] at this
      exact S n (j + 1) _ _ h5 this (extend a _ _ j g h1 this h3 h4)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma W_ok : W 205 1 0 0 = true := by decide +kernel

end OMA930b

theorem OMA.solution :
    OMA.R_Erdos930_erdos_930_variants_consecutive_integers_R1_H4_R1_H2_R1.H2 :=
  OMA930b.S 205 1 0 0 OMA930b.W_ok (by simp [OMA930b.Cnt]) (fun k h1 h2 => by omega)
