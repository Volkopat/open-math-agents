import OMAStatements.S_oeis_a022894

-- Problem: A022894: Number of solutions to c(1)*prime(1) +...+ c(2n+1)*prime(2n+1) = 0, where c(i) = +-1 for i > 1, c(1) = 1.
-- Credit: @sobrien032

/-!
Clark Kimberling contributed OEIS sequence A022894. Václav Kotěšovec
conjectured in 2019 that the nth root of its terms tends to four.
The board statement was formalized by David Ganz. Lean proof by Codex.

The first prime has positive sign, and all the remaining primes are odd.
After reserving a short initial segment of the odd primes, vary the signs of
the tail freely. Flipping a prefix of the tail reduces the imbalance to at
most twice its largest prime. Recording the length of that prefix recovers
the original assignment from the modified one.

The first six odd primes realize all even sums from −36 through 36.
Bertrand's postulate extends this correction interval as more primes are
added. Chebyshev's lower bound for the prime-counting function shows that
a sublinear number of reserved primes suffices. The resulting lower and
upper bounds have the same nth-root limit.
-/

namespace SignedPrimes

noncomputable def oddP (j : ℕ) : ℤ := OMA.S_oeis_a022894.prime (j+2)

noncomputable def tot (m : ℕ) : ℤ := ∑ i : Fin m, oddP i

def signed (b : Bool) (x : ℤ) : ℤ := (if b then 1 else -1) * x

noncomputable def wt {m : ℕ} (c : Fin m → Bool) : ℤ := ∑ i, signed (c i) (oddP i)

theorem oddP_eq (i : ℕ) : oddP i = (Nat.nth Nat.Prime (i+1) : ℤ) := rfl

theorem oddP_nonneg (i : ℕ) : 0 ≤ oddP i := by rw [oddP_eq]; positivity

theorem oddP_mono : Monotone oddP := by
  intro i j hij
  simp only [oddP_eq, Nat.cast_le]
  exact (Nat.nth_strictMono Nat.infinite_setOfPred_prime).monotone (by omega)

theorem oddP_odd (i : ℕ) : Odd (oddP i) := by
  rw [oddP_eq]
  have h := Nat.add_two_le_nth_prime (i+1)
  have hodd := (Nat.prime_nth_prime (i+1)).odd_of_ne_two (by omega)
  exact_mod_cast hodd

end SignedPrimes

namespace SignedPrimes

private def initial : Fin 6 → ℤ := ![3,5,7,11,13,17]

private theorem firstPrimes (i : Fin 6) : oddP i = initial i := by
  have h13 : Nat.nth Nat.Prime 5 = 13 := Nat.nth_count (by decide : Nat.Prime 13)
  have h17 : Nat.nth Nat.Prime 6 = 17 := Nat.nth_count (by decide : Nat.Prime 17)
  fin_cases i <;> norm_num [oddP, OMA.S_oeis_a022894.prime, initial, h13, h17]

private theorem initialTotal : tot 6 = 56 := by
  unfold tot
  simp_rw [firstPrimes]
  decide

private def mask : Fin 37 → ℕ :=
  ![5,8,6,16,9,7,17,32,18,11,33,19,34,21,36,35,15,37,40,38,48,41,39,49,29,50,43,52,51,31,53,56,54,47,57,55,58]

private theorem initialCheck : ∀ k : Fin 37,
    (∑ i : Fin 6, signed ((mask k).testBit i.val) (initial i)) = 2*(k:ℤ)-36 := by
  decide

private theorem initialCorrection (t : ℤ) (ht : |t| ≤ tot 6 - 20)
    (hpar : t ≡ tot 6 [ZMOD 2]) : ∃ c : Fin 6 → Bool, wt c = t := by
  rw [initialTotal] at ht hpar
  rw [abs_le] at ht
  change t % 2 = 56 % 2 at hpar
  let k : Fin 37 := ⟨((t+36)/2).toNat, by omega⟩
  refine ⟨fun i => (mask k).testBit i.val, ?_⟩
  unfold wt
  simp_rw [firstPrimes]
  rw [initialCheck]
  dsimp [k]
  omega

private theorem next_double (j : ℕ) : oddP (j+1) ≤ 2*oddP j := by
  let p := Nat.nth Nat.Prime (j+1)
  have hp : p.Prime := Nat.prime_nth_prime _
  obtain ⟨q,hq,hpq,hq2⟩ := Nat.exists_prime_lt_and_le_two_mul p hp.ne_zero
  have hmono := Nat.nth_strictMono Nat.infinite_setOfPred_prime
  have hi : j+1 < Nat.count Nat.Prime q := hmono.lt_iff_lt.mp ((Nat.nth_count hq).symm ▸ hpq)
  have hle : Nat.nth Nat.Prime (j+1+1) ≤ q := (hmono.monotone hi).trans_eq (Nat.nth_count hq)
  have h := hle.trans hq2
  simp only [oddP_eq]
  exact_mod_cast h

private theorem total_add (m : ℕ) : tot (m+1) = tot m + oddP m := by
  simp [tot, Fin.sum_univ_castSucc]

private theorem wt_append {m : ℕ} (c : Fin m → Bool) (b : Bool) :
    wt (Fin.snoc c b) = wt c + signed b (oddP m) := by
  simp [wt, Fin.sum_univ_castSucc]

private theorem correctionAux (m : ℕ) (hm : 6 ≤ m) :
    oddP m ≤ tot m - 20 ∧
    ∀ t : ℤ, |t| ≤ tot m - 20 → t ≡ tot m [ZMOD 2] → ∃ c : Fin m → Bool, wt c = t := by
  induction m, hm using Nat.le_induction with
  | base =>
    refine ⟨?_,initialCorrection⟩
    have h19 : Nat.nth Nat.Prime 7 = 19 := Nat.nth_count (by decide : Nat.Prime 19)
    norm_num [oddP, OMA.S_oeis_a022894.prime, initialTotal, h19]
  | succ m hm ih =>
    obtain ⟨hwidth,ih⟩ := ih
    refine ⟨?_,?_⟩
    · rw [total_add]
      linarith [next_double m]
    · intro t ht hpar
      rw [total_add] at ht hpar
      rw [abs_le] at ht
      change t % 2 = (tot m + oddP m) % 2 at hpar
      by_cases ht0 : 0 ≤ t
      · obtain ⟨c,hc⟩ := ih (t - oddP m) (abs_le.mpr (by omega)) (by
          change (t - oddP m) % 2 = (tot m) % 2
          omega)
        exact ⟨Fin.snoc c true, by rw [wt_append,hc]; simp [signed]⟩
      · obtain ⟨c,hc⟩ := ih (t + oddP m) (abs_le.mpr (by omega)) (by
          change (t + oddP m) % 2 = (tot m) % 2
          omega)
        exact ⟨Fin.snoc c false, by rw [wt_append,hc]; simp [signed]⟩

theorem correct (m : ℕ) (hm : 6 ≤ m) (t : ℤ) (ht : |t| ≤ tot m - 20)
    (hpar : t ≡ tot m [ZMOD 2]) : ∃ c : Fin m → Bool, wt c = t :=
  (correctionAux m hm).2 t ht hpar

end SignedPrimes

namespace SignedPrimes

private def flipPrefix {k : ℕ} (t : ℕ) (c : Fin k → Bool) (i : Fin k) : Bool :=
  if i.val < t then !(c i) else c i

private theorem flipPrefix_twice {k : ℕ} (t : ℕ) (c : Fin k → Bool) :
    flipPrefix t (flipPrefix t c) = c := by
  funext i
  by_cases h : i.val < t <;> simp [flipPrefix, h]

private theorem signed_not_eq (b : Bool) (x : ℤ) : signed (!b) x = -signed b x := by
  cases b <;> simp [signed]

private theorem flip_step {k : ℕ} (c : Fin k → Bool) (w : Fin k → ℤ)
    (j : ℕ) (hj : j < k) :
    (∑ i, signed (flipPrefix (j+1) c i) (w i)) -
      (∑ i, signed (flipPrefix j c i) (w i)) =
      -2 * signed (c ⟨j,hj⟩) (w ⟨j,hj⟩) := by
  rw [← Finset.sum_sub_distrib, Finset.sum_eq_single (⟨j,hj⟩ : Fin k)]
  · simp [flipPrefix, signed_not_eq]
    ring
  · intro i _ hne
    have hv : i.val ≠ j := fun h ↦ hne (Fin.ext h)
    by_cases h : i.val < j
    · simp [flipPrefix, h, show i.val < j+1 by omega]
    · simp [flipPrefix, h, show ¬ i.val < j+1 by omega]
  · simp

private theorem flip_exists {k : ℕ} (c : Fin k → Bool) (w : Fin k → ℤ)
    (M : ℤ) (hM : 0 ≤ M) (hw : ∀ i, |w i| ≤ M) :
    ∃ t : Fin (k+1), |∑ i, signed (flipPrefix t.val c i) (w i)| ≤ 2*M := by
  let S (j : ℕ) : ℤ := ∑ i, signed (flipPrefix j c i) (w i)
  have hend : S k = -S 0 := by
    simp [S, flipPrefix, signed_not_eq, Finset.sum_neg_distrib]
  have hstep (j : ℕ) (hj : j < k) : |S (j+1) - S j| ≤ 2*M := by
    change |(∑ i, signed (flipPrefix (j+1) c i) (w i)) - _| ≤ _
    rw [flip_step c w j hj, abs_mul]
    have hsign (b : Bool) (x : ℤ) : |signed b x| = |x| := by
      cases b <;> simp [signed]
    rw [hsign]
    norm_num
    linarith [hw ⟨j,hj⟩]
  by_contra h
  push Not at h
  have hfar (j : ℕ) (hj : j ≤ k) : 2*M < |S j| := h ⟨j,by omega⟩
  have hside (j : ℕ) (hj : j ≤ k) : 0 < S j ↔ 0 < S 0 := by
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [← ih (by omega)]
      have hjump := abs_le.mp (hstep j (by omega))
      have ha := hfar j (by omega)
      have hb := hfar (j+1) hj
      rw [lt_abs] at ha hb
      change 0 < S (j+1) ↔ 0 < S j
      omega
  have he := hside k le_rfl
  rw [hend] at he
  have hzero := hfar 0 (Nat.zero_le _)
  rw [lt_abs] at hzero
  omega

theorem balanced_count (k : ℕ) (w : Fin k → ℤ) (M : ℤ) (hM : 0 ≤ M)
    (hw : ∀ i, |w i| ≤ M) :
    2^k ≤ (k+1) * (Finset.univ.filter
      (fun c : Fin k → Bool ↦ |∑ i, signed (c i) (w i)| ≤ 2*M)).card := by
  classical
  let G := Finset.univ.filter (fun c : Fin k → Bool ↦ |∑ i, signed (c i) (w i)| ≤ 2*M)
  choose t ht using fun c : Fin k → Bool ↦ flip_exists c w M hM hw
  let f (c : Fin k → Bool) : Fin (k+1) × ↥G :=
    (t c, ⟨flipPrefix (t c).val c, Finset.mem_filter.mpr ⟨Finset.mem_univ _,ht c⟩⟩)
  have hf : Function.Injective f := by
    intro c d e
    have he : t c = t d := congrArg Prod.fst e
    have hp : flipPrefix (t c).val c = flipPrefix (t d).val d :=
      congrArg (fun y : Fin (k+1) × ↥G ↦ y.2.val) e
    rw [he] at hp
    simpa only [flipPrefix_twice] using congrArg (flipPrefix (t d).val) hp
  change 2^k ≤ (k+1) * G.card
  simpa only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Fintype.card_prod,
    Fintype.card_coe] using Fintype.card_le_of_injective f hf

end SignedPrimes

namespace SignedPrimes

open Filter

private def quarter (n : ℕ) : ℕ := n.sqrt.sqrt

private theorem quarter_bounds (n : ℕ) :
    quarter n ^ 4 ≤ n ∧ n < (quarter n + 1)^4 := by
  constructor
  · calc
      quarter n ^ 4 = (quarter n ^ 2)^2 := by ring
      _ ≤ n.sqrt^2 := Nat.pow_le_pow_left (Nat.sqrt_le' n.sqrt) _
      _ ≤ n := Nat.sqrt_le' n
  · calc
      n < (n.sqrt+1)^2 := Nat.lt_succ_sqrt' n
      _ ≤ ((quarter n+1)^2)^2 := Nat.pow_le_pow_left (Nat.lt_succ_sqrt' n.sqrt) _
      _ = (quarter n+1)^4 := by ring

private theorem quarter_tendsto : Tendsto quarter atTop atTop := by
  apply tendsto_atTop.mpr
  intro k
  filter_upwards [eventually_ge_atTop (k^4)] with n hn
  apply Nat.le_sqrt'.mpr
  apply Nat.le_sqrt'.mpr
  simpa only [← pow_mul] using hn

private theorem many_primes (t : ℕ) (ht : 1024 ≤ t) :
    48*t^4 ≤ Nat.primeCounting (t^6) := by
  let x : ℝ := t
  have h : 1024 ≤ x := by dsimp [x]; exact_mod_cast ht
  have hx : 0 < x := by linarith
  have h1 : 1 ≤ x^4 := one_le_pow₀ (by linarith)
  have h5 : x ≤ x^5 := by nlinarith [mul_le_mul_of_nonneg_right h1 hx.le]
  have h6 : 1024*x^5 ≤ x^6 := by nlinarith [mul_le_mul_of_nonneg_right h (pow_nonneg hx.le 5)]
  have hpos : 0 < Real.log (x^6) := Real.log_pos (one_lt_pow₀ (by linarith) (by decide))
  have hlog : Real.log (x^6) ≤ 6*x := by
    rw [Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    nlinarith [Real.log_le_sub_one_of_pos hx]
  have hx6 : 1 ≤ x^6 := one_le_pow₀ (by linarith)
  have hlog1 : Real.log (x^6+1) ≤ 1+6*x := by
    calc
      Real.log (x^6+1) ≤ Real.log (2*x^6) := Real.log_le_log (by positivity) (by linarith)
      _ = Real.log 2 + Real.log (x^6) := Real.log_mul (by norm_num) (by positivity)
      _ ≤ 1+6*x := by linarith [Real.log_le_sub_one_of_pos (by norm_num : 0 < (2:ℝ))]
  have hhalf : 1/2 ≤ Real.log 2 := by
    have ha := Real.one_sub_inv_le_log_of_pos (by norm_num : 0 < (2:ℝ))
    norm_num at ha ⊢
    linarith
  have hcompare : 48*x^4*Real.log (x^6) ≤ x^6 * Real.log 2 - Real.log (x^6+1) := by
    nlinarith [mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ 48*x^4),
      mul_le_mul_of_nonneg_left hhalf (pow_nonneg hx.le 6)]
  have hc := Chebyshev.pi_ge (t^6)
  push_cast at hc
  have hreal : 48*x^4 ≤ (Nat.primeCounting (t^6) : ℝ) :=
    ((le_div_iff₀ hpos).mpr hcompare).trans hc
  dsimp [x] at hreal
  exact_mod_cast hreal

private theorem tot_sq (m : ℕ) : (m : ℤ)^2 ≤ 2*tot m := by
  induction m with
  | zero => simp [tot]
  | succ m ih =>
    have hs : tot (m+1) = tot m + oddP m := by
      exact Fin.sum_univ_castSucc _
    have hd : (m:ℤ)+1+2 ≤ oddP m := by
      rw [oddP_eq]
      exact_mod_cast Nat.add_two_le_nth_prime (m+1)
    rw [hs]
    push_cast
    nlinarith

theorem reserve_exists : ∃ r : ℕ → ℕ,
    Tendsto (fun n : ℕ ↦ (r n : ℝ) / n) atTop (nhds 0) ∧
      ∀ᶠ n : ℕ in atTop, 6 ≤ r n ∧ r n ≤ 2*n ∧ 2*oddP (2*n) + 22 ≤ tot (r n) := by
  let r (n : ℕ) := 4*(quarter n)^3
  refine ⟨r, ?_, ?_⟩
  · apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      ((tendsto_const_div_atTop_nhds_zero_nat (4:ℝ)).comp quarter_tendsto)
    · exact Eventually.of_forall (fun n => by positivity)
    · filter_upwards [quarter_tendsto.eventually_ge_atTop 1] with n ht
      have hq : (quarter n : ℝ)^4 ≤ n := by exact_mod_cast (quarter_bounds n).1
      have hpos : 0 < (quarter n : ℝ) := by exact_mod_cast ht
      have hn : 0 < (n:ℝ) := lt_of_lt_of_le (pow_pos hpos _) hq
      change (r n : ℝ) / n ≤ 4 / (quarter n : ℝ)
      rw [div_le_div_iff₀ hn hpos]
      dsimp [r]
      push_cast
      nlinarith
  · filter_upwards [quarter_tendsto.eventually_ge_atTop 1024] with n ht
    let t := quarter n
    have htN : 1024 ≤ t := ht
    obtain ⟨hlo,hu⟩ := quarter_bounds n
    change t^4 ≤ n at hlo
    change n < (t+1)^4 at hu
    have hdouble : t+1 ≤ 2*t := by omega
    have hu' : n < 16*t^4 := by
      have h' := Nat.pow_le_pow_left hdouble 4
      nlinarith
    have hidx : 2*n+1 < Nat.primeCounting (t^6) := by
      have hh := many_primes t htN
      omega
    have hprime : Nat.nth Nat.Prime (2*n+1) ≤ t^6 :=
      Nat.le_of_lt_succ (Nat.nth_lt_of_lt_count hidx)
    have hn : 6 ≤ 4*t^3 := by
      have := Nat.pow_le_pow_left htN 3
      omega
    have hr : 4*t^3 ≤ 2*n := by
      nlinarith [Nat.mul_le_mul_right (t^3) (show 2 ≤ t by omega)]
    refine ⟨hn,hr,?_⟩
    change 2*oddP (2*n)+22 ≤ tot (4*t^3)
    rw [oddP_eq]
    have hp : ((Nat.nth Nat.Prime (2*n+1)):ℤ) ≤ (t:ℤ)^6 := by exact_mod_cast hprime
    have H := tot_sq (4*t^3)
    push_cast at H
    have hs : (1024:ℤ) ≤ t := by exact_mod_cast ht
    have h6 : (1024:ℤ)^6 ≤ (t:ℤ)^6 := pow_le_pow_left₀ (by norm_num) hs _
    nlinarith

end SignedPrimes

namespace SignedPrimes

open OMA.S_oeis_a022894

private noncomputable def good (L : ℕ) : Finset (Fin L → Bool) :=
  Finset.univ.filter fun c ↦ (2 : ℤ) + wt c = 0

private theorem a_eq (n : ℕ) : a n = (good (2*n)).card := by
  apply congrArg Finset.card
  ext c
  simp [good, wt, signed, oddP, prime, Nat.nth_prime_zero_eq_two]

theorem a_upper (n : ℕ) : a n ≤ 2^(2*n) := by
  rw [a_eq]
  exact (Finset.card_le_univ _).trans (by simp)

private theorem sum_parity {ι : Type} (s : Finset ι) (f : ι → ℤ)
    (h : ∀ i, f i % 2 = 1) : (∑ i ∈ s, f i) % 2 = (s.card : ℤ) % 2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.card_insert_of_notMem hi, Nat.cast_add, Nat.cast_one]
    have := h i
    omega

private theorem odd_mod (j : ℕ) : oddP j % 2 = 1 := by
  obtain ⟨k,hk⟩ := oddP_odd j
  omega

private theorem signed_mod (b : Bool) (j : ℕ) : signed b (oddP j) % 2 = 1 := by
  have := odd_mod j
  cases b <;> simp [signed] <;> omega

private theorem append_wt {m k : ℕ} (p : Fin m → Bool) (c : Fin k → Bool) :
    wt (Fin.append p c) = wt p + ∑ i, signed (c i) (oddP (m+i.val)) := by
  unfold wt
  rw [Fin.sum_univ_add]
  simp

theorem count_corrected (n m k : ℕ) (hlen : m+k = 2*n) (hm : 6 ≤ m)
    (hroom : 2*oddP (2*n)+22 ≤ tot m) :
    (Finset.univ.filter (fun c : Fin k → Bool ↦
      |∑ i, signed (c i) (oddP (m+i.val))| ≤ 2*oddP (2*n))).card ≤ a n := by
  classical
  let T (c : Fin k → Bool) : ℤ := ∑ i, signed (c i) (oddP (m+i.val))
  let F := Finset.univ.filter (fun c : Fin k → Bool ↦ |T c| ≤ 2*oddP (2*n))
  have choosePrefix (c : F) : ∃ p : Fin m → Bool, wt p = -2 - T c.val := by
    have hb := (Finset.mem_filter.mp c.property).2
    change |T c.val| ≤ 2*oddP (2*n) at hb
    obtain ⟨hlo,hhi⟩ := abs_le.mp hb
    apply correct m hm
    · apply abs_le.mpr
      omega
    · have h₁ := sum_parity (Finset.univ : Finset (Fin k))
          (fun i ↦ signed (c.val i) (oddP (m+i.val))) (fun i ↦ signed_mod _ _)
      have h₂ := sum_parity (Finset.univ : Finset (Fin m))
          (fun i ↦ oddP i.val) (fun i ↦ odd_mod _)
      simp only [Finset.card_univ, Fintype.card_fin] at h₁ h₂
      change (T c.val) % 2 = _ at h₁
      change (tot m) % 2 = _ at h₂
      change (-2 - T c.val) % 2 = (tot m) % 2
      omega
  let ext (c : F) := Fin.append (choosePrefix c).choose c.val
  have he (c : F) : ext c ∈ good (m+k) := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    change 2 + wt (Fin.append _ c.val) = 0
    rw [append_wt, (choosePrefix c).choose_spec]
    change 2 + (-2 - T c.val + T c.val) = 0
    ring
  let lift (c : F) : good (m+k) := ⟨ext c, he c⟩
  have hinj : Function.Injective lift := by
    intro x y heq
    apply Subtype.ext
    funext i
    have hh := congrArg (fun z : good (m+k) ↦ z.val (Fin.natAdd m i)) heq
    simpa [lift, ext] using hh
  change F.card ≤ a n
  calc
    F.card ≤ (good (m+k)).card := Finset.card_le_card_of_injective (f := lift) hinj
    _ = a n := by rw [hlen, a_eq]

theorem a_lower (n m : ℕ) (hm : 6 ≤ m) (hle : m ≤ 2*n)
    (hroom : 2*oddP (2*n)+22 ≤ tot m) :
    2^(2*n-m) ≤ (2*n+1)*a n := by
  let k := 2*n-m
  have he : m+k = 2*n := by dsimp [k]; omega
  have hw (i : Fin k) : |oddP (m+i.val)| ≤ oddP (2*n) := by
    rw [abs_of_nonneg (oddP_nonneg _)]
    exact oddP_mono (by have := i.isLt; omega)
  have hb := balanced_count k (fun i ↦ oddP (m+i.val)) (oddP (2*n)) (oddP_nonneg _) hw
  exact hb.trans (Nat.mul_le_mul (by omega) (count_corrected n m k he hm hroom))

end SignedPrimes

namespace SignedPrimes

open Real Filter
open scoped Topology

theorem root_limit (a r : ℕ → ℕ)
    (hr : Tendsto (fun n : ℕ ↦ (r n : ℝ) / n) atTop (𝓝 0))
    (hu : ∀ n, a n ≤ 2^(2*n))
    (hl : ∀ᶠ n : ℕ in atTop, r n ≤ 2*n ∧ 2^(2*n-r n) ≤ (2*n+1)*a n) :
    Tendsto (fun n : ℕ ↦ (a n : ℝ) ^ ((1:ℝ)/n)) atTop (𝓝 4) := by
  have hpos : ∀ᶠ n in atTop, 0 < (a n : ℝ) := by
    filter_upwards [hl] with n hn
    have hpow : 0 < (2:ℕ)^(2*n-r n) := by positivity
    have hh := hpow.trans_le hn.2
    exact_mod_cast Nat.pos_of_ne_zero (fun h => by simp [h] at hh)
  have hlog : Tendsto (fun n : ℕ ↦ log (n:ℝ) / n) atTop (𝓝 0) := by
    have h : Tendsto (fun x : ℝ => log x / x) atTop (𝓝 0) := by
      simpa using tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    exact h.comp tendsto_natCast_atTop_atTop
  let L := 2*log 2
  have hlo : Tendsto (fun n : ℕ => L - ((r n : ℝ)/n*log 2 + log 3/n + log n/n))
      atTop (𝓝 L) := by
    simpa only [zero_mul, zero_add, sub_zero] using
      (tendsto_const_nhds (x := L)).sub
        (((hr.mul_const (log 2)).add (tendsto_const_div_atTop_nhds_zero_nat (log 3))).add hlog)
  have hs : Tendsto (fun n : ℕ => log (a n)/n) atTop (𝓝 L) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo (tendsto_const_nhds (x := L))
    · filter_upwards [hl, hpos, eventually_gt_atTop 0] with n hn ha hn0
      have hnR : 0 < (n:ℝ) := by exact_mod_cast hn0
      have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn0
      have he : (2:ℝ)^(2*n-r n) ≤ (2*(n:ℝ)+1)*(a n:ℝ) := by exact_mod_cast hn.2
      have h := log_le_log (by positivity) he
      rw [log_pow, log_mul (by positivity) ha.ne', Nat.cast_sub hn.1, Nat.cast_mul,
        Nat.cast_ofNat] at h
      have hs := log_le_log (by positivity : 0 < 2*(n:ℝ)+1) (by linarith : 2*(n:ℝ)+1 ≤ 3*n)
      rw [log_mul (by norm_num) hnR.ne'] at hs
      calc
        _ = ((2*(n:ℝ)-r n)*log 2 - log 3 - log n)/n := by
          dsimp [L]
          field_simp
          ring
        _ ≤ _ := div_le_div_of_nonneg_right (by linarith) hnR.le
    · filter_upwards [hpos, eventually_gt_atTop 0] with n ha hn
      have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
      have h := log_le_log ha (show (a n : ℝ) ≤ (2:ℝ)^(2*n) by exact_mod_cast hu n)
      rw [log_pow, Nat.cast_mul, Nat.cast_ofNat] at h
      apply (div_le_iff₀ hnR).mpr
      dsimp [L]
      linarith
  have hL : exp L = 4 := by
    dsimp [L]
    rw [two_mul,exp_add,exp_log (by norm_num : (0:ℝ)<2)]
    norm_num
  rw [← hL]
  apply (continuous_exp.continuousAt.tendsto.comp hs).congr'
  filter_upwards [hpos] with n hn
  rw [rpow_def_of_pos hn]
  simp [div_eq_mul_inv]

end SignedPrimes

open SignedPrimes Filter in
theorem OMA.solution : type_of% @OMA.S_oeis_a022894.main := by
  obtain ⟨r, hr, hg⟩ := reserve_exists
  apply root_limit OMA.S_oeis_a022894.a r hr a_upper
  filter_upwards [hg] with n hn
  exact ⟨hn.2.1, a_lower n (r n) hn.1 hn.2.1 hn.2.2⟩
