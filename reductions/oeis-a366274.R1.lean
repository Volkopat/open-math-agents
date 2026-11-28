import OMAStatements.S_oeis_a366274

/-! # Reduction of OEIS A366274 to Dusart and Rosser-Schoenfeld prime-counting bounds

For `n ≥ 3`, setting `k = n - 1` reduces the conjecture to `prime n + prime (n + 1) ≤ prime (2 * n)`.
For `n ≥ 5`, letting `x = (prime n + prime (n + 1)) / 2 - 1` gives `prime n ≤ x < prime (n + 1)`, so
`Nat.primeCounting x = n` and `2 * x + 1 = prime n + prime (n + 1) - 1`. The inequality is then
equivalent to `Nat.primeCounting (2 * x + 1) < 2 * Nat.primeCounting x`.

For `x ≥ 599`, this follows from two standard explicit prime-counting bounds:
* `H1`: Dusart's lower bound `x / log x * (1 + 1 / log x) ≤ π(x)` for `x ≥ 599`
  (arXiv:1002.0442, Theorem 6.9).
* `H2`: Rosser and Schoenfeld's upper bound `π(x) ≤ x / log x * (1 + 3 / (2 * log x))`
  for `x ≥ 599` (Illinois J. Math. 6, 1962, Corollary 1).

All small cases `n = 3, 4` and `11 ≤ x ≤ 598` are proved directly inside this file via
Meissel-Lehmer sieving on 25 monotone covering intervals. -/

namespace OMA.R_oeis_a366274_R1

open Real Finset

/-- Dusart's explicit lower bound on the prime-counting function (arXiv:1002.0442, Theorem 6.9). -/
def H1 : Prop := ∀ x : ℕ, 599 ≤ x →
    (x : ℝ) / Real.log x * (1 + 1 / Real.log x) ≤ (Nat.primeCounting x : ℝ)

/-- Rosser-Schoenfeld explicit upper bound on the prime-counting function
(Illinois J. Math. 6, 1962, Corollary 1), restricted to `x ≥ 599`. -/
def H2 : Prop := ∀ x : ℕ, 599 ≤ x →
    (Nat.primeCounting x : ℝ) ≤ (x : ℝ) / Real.log x * (1 + 3 / (2 * Real.log x))

/-- Analytic comparison showing that `H1` and `H2` imply `π(2x + 1) < 2 π(x)` for `x ≥ 599`. -/
lemma analytic_ineq {x : ℝ} (hx : 599 ≤ x) :
    (2 * x + 1) / log (2 * x + 1) * (1 + 3 / (2 * log (2 * x + 1))) <
      2 * (x / log x * (1 + 1 / log x)) := by
  have hxpos : 0 < x := by linarith
  have hx1 : 1 < x := by linarith
  have htpos : 0 < log x := log_pos hx1
  set t : ℝ := log x
  set s : ℝ := log (2 * x + 1)
  have hd : (69 / 100 : ℝ) < log 2 :=
    (by norm_num : (69 / 100 : ℝ) < 0.6931471803).trans log_two_gt_d9
  have hs_gt : t + 69 / 100 < s := by
    have h1 : log (2 * x) < log (2 * x + 1) := log_lt_log (by linarith) (by linarith)
    rw [log_mul (by norm_num) hxpos.ne'] at h1
    dsimp [s, t]
    linarith
  have hdpos : 0 < t + 69 / 100 := by linarith
  have hspos : 0 < s := by linarith
  -- Monotonicity in the denominator: replace `s` by `t + 69/100`.
  have hstep1 :
      (2 * x + 1) / s * (1 + 3 / (2 * s)) <
        (2 * x + 1) / (t + 69 / 100) * (1 + 3 / (2 * (t + 69 / 100))) := by
    have hdiv1 : (2 * x + 1) / s < (2 * x + 1) / (t + 69 / 100) :=
      div_lt_div_of_pos_left (by linarith) hdpos hs_gt
    have hdiv2 : 3 / (2 * s) < 3 / (2 * (t + 69 / 100)) :=
      div_lt_div_of_pos_left (by norm_num) (by linarith) (by linarith)
    have hpos1 : 0 < (2 * x + 1) / s := div_pos (by linarith) hspos
    have hpos2 : 0 < 1 + 3 / (2 * (t + 69 / 100)) := by positivity
    nlinarith
  -- Upper bound `t = log x ≤ x / 10 + 2` from `log (x / 10) ≤ x / 10 - 1` and `10 < exp 3`.
  have ht_upper : t ≤ x / 10 + 2 := by
    have h10 : log 10 < 3 := by
      rw [log_lt_iff_lt_exp (by norm_num)]
      have he : (5 / 2 : ℝ) < exp 1 :=
        (by norm_num : (5 / 2 : ℝ) < 2.7182818283).trans exp_one_gt_d9
      have he3 : (5 / 2 : ℝ) ^ 3 < exp 3 := by
        rw [show exp 3 = (exp 1) ^ 3 by simp [← exp_nat_mul]]
        exact pow_lt_pow_left₀ he (by norm_num) (by norm_num)
      norm_num at he3
      linarith
    have hsub : log (x / 10) ≤ x / 10 - 1 := log_le_sub_one_of_pos (by linarith)
    rw [log_div hxpos.ne' (by norm_num)] at hsub
    dsimp [t]
    linarith
  -- Clear denominators and close by polynomial algebra.
  have hstep2 :
      (2 * x + 1) / (t + 69 / 100) * (1 + 3 / (2 * (t + 69 / 100))) <
        2 * (x / t * (1 + 1 / t)) := by
    rw [show (2 * x + 1) / (t + 69 / 100) * (1 + 3 / (2 * (t + 69 / 100))) =
        (2 * x + 1) * (2 * (t + 69 / 100) + 3) / (2 * (t + 69 / 100) ^ 2) by field_simp]
    rw [show 2 * (x / t * (1 + 1 / t)) = 2 * x * (t + 1) / t ^ 2 by field_simp]
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    -- Goal: (2*x + 1)*(2*(t + 69/100) + 3)*t^2 < 2*x*(t + 1)*(2*(t + 69/100)^2)
    have hdiff :
        2 * x * (t + 1) * (2 * (t + 69 / 100) ^ 2) -
          (2 * x + 1) * (2 * (t + 69 / 100) + 3) * t ^ 2 =
        t ^ 2 * ((19 / 25) * x - (2 * t + 219 / 50)) +
          x * ((18561 / 2500) * t + 4761 / 2500) := by
      ring
    have h1 : 0 < (19 / 25 : ℝ) * x - (2 * t + 219 / 50) := by linarith
    have h2 : 0 < t ^ 2 * ((19 / 25 : ℝ) * x - (2 * t + 219 / 50)) :=
      mul_pos (sq_pos_of_pos htpos) h1
    have h3 : 0 < x * ((18561 / 2500 : ℝ) * t + 4761 / 2500) := by positivity
    linarith
  exact hstep1.trans hstep2

/-- Large-`x` prime-counting inequality from `H1` and `H2`. -/
lemma pi_double_add_one_lt_large (h1 : H1) (h2 : H2) {x : ℕ} (hx : 599 ≤ x) :
    Nat.primeCounting (2 * x + 1) < 2 * Nat.primeCounting x := by
  have hlo : (x : ℝ) / log x * (1 + 1 / log x) ≤ (Nat.primeCounting x : ℝ) := h1 x hx
  have hhi :
      (Nat.primeCounting (2 * x + 1) : ℝ) ≤
        ((2 * x + 1 : ℕ) : ℝ) / log ((2 * x + 1 : ℕ) : ℝ) *
          (1 + 3 / (2 * log ((2 * x + 1 : ℕ) : ℝ))) :=
    h2 (2 * x + 1) (by omega)
  have hcast : ((2 * x + 1 : ℕ) : ℝ) = 2 * (x : ℝ) + 1 := by push_cast; ring
  rw [hcast] at hhi
  have hstrict := analytic_ineq (x := (x : ℝ)) (by exact_mod_cast hx)
  have hreal : (Nat.primeCounting (2 * x + 1) : ℝ) < 2 * (Nat.primeCounting x : ℝ) := by
    linarith
  exact_mod_cast hreal

/-- Finite verification of `π(2x + 1) < 2 π(x)` for all `11 ≤ x ≤ 598`, using Meissel-Lehmer
sieving on 25 monotone covering intervals. -/
lemma pi_double_add_one_lt_small {x : ℕ} (hlo : 11 ≤ x) (hhi : x ≤ 598) :
    Nat.primeCounting (2 * x + 1) < 2 * Nat.primeCounting x := by
  let phi : List ℕ → ℕ → ℕ :=
    List.rec (fun n => n) (fun p _ ih n => if n = 0 then 0 else ih n - ih (n / p))
  have card_sieve : ∀ (ps : List ℕ), (∀ p ∈ ps, 0 < p) → ps.Pairwise Nat.Coprime →
      ∀ n : ℕ, ((Icc 1 n).filter (fun m => ∀ q ∈ ps, ¬ q ∣ m)).card = phi ps n := by
    intro ps
    induction ps with
    | nil =>
      intro _ _ n
      simp [phi]
    | cons p ps ih =>
      intro hpos hpw n
      obtain ⟨hcop_p, hpw_ps⟩ := List.pairwise_cons.mp hpw
      have hp : 0 < p := hpos p (List.mem_cons_self ..)
      have hpos_ps : ∀ q ∈ ps, 0 < q := fun q hq => hpos q (List.mem_cons_of_mem p hq)
      by_cases hn : n = 0
      · subst hn
        simp [phi]
      · have hphi_eq : phi (p :: ps) n = phi ps n - phi ps (n / p) := if_neg hn
        rw [hphi_eq]
        set S := (Icc 1 n).filter (fun m => ∀ q ∈ ps, ¬ q ∣ m)
        have hS : S.card = phi ps n := ih hpos_ps hpw_ps n
        have hA_eq :
            (Icc 1 n).filter (fun m => ∀ q ∈ p :: ps, ¬ q ∣ m) =
              S.filter (fun m => ¬ p ∣ m) := by
          ext m
          simp only [S, mem_filter, List.mem_cons, forall_eq_or_imp]
          tauto
        have hsplit : (S.filter (fun m => ¬ p ∣ m)).card + (S.filter (fun m => p ∣ m)).card = S.card := by
          simpa [add_comm] using Finset.card_filter_add_card_filter_not (s := S) (p := fun m => p ∣ m)
        have hB :
            (S.filter (fun m => p ∣ m)).card =
              ((Icc 1 (n / p)).filter (fun k => ∀ q ∈ ps, ¬ q ∣ k)).card := by
          symm
          refine Finset.card_bij (fun k _ => p * k) ?_ ?_ ?_
          · intro k hk
            simp only [mem_filter, mem_Icc, S] at hk ⊢
            obtain ⟨⟨hk1, hkle⟩, hnd⟩ := hk
            refine ⟨⟨⟨by nlinarith,
              (Nat.mul_comm p k).trans_le ((Nat.le_div_iff_mul_le hp).mp hkle)⟩,
              fun q hq hdiv => ?_⟩, dvd_mul_right p k⟩
            have hcop : q.Coprime p := (hcop_p q hq).symm
            exact hnd q hq (hcop.dvd_of_dvd_mul_left hdiv)
          · intro k₁ _ k₂ _ heq
            exact Nat.eq_of_mul_eq_mul_left hp heq
          · intro m hm
            simp only [mem_filter, mem_Icc, S] at hm
            obtain ⟨⟨⟨hm1, hmn⟩, hnd⟩, ⟨k, rfl⟩⟩ := hm
            refine ⟨k, ?_, rfl⟩
            simp only [mem_filter, mem_Icc]
            refine ⟨⟨?_, (Nat.le_div_iff_mul_le hp).mpr (by rw [Nat.mul_comm]; exact hmn)⟩,
              fun q hq hdiv => hnd q hq (dvd_mul_of_dvd_right hdiv p)⟩
            by_contra hk0
            have : k = 0 := by omega
            subst this
            omega
        have hB_phi : (S.filter (fun m => p ∣ m)).card = phi ps (n / p) := by
          rw [hB]
          exact ih hpos_ps hpw_ps (n / p)
        rw [hA_eq]
        omega
  have primeCounting_eq_phi :
      ∀ (ps : List ℕ) (n : ℕ),
        (∀ p ∈ ps, p.Prime) → ps.Nodup → (∀ p ∈ ps, p ≤ n) →
        (∀ q : ℕ, q.Prime → q * q ≤ n → q ∈ ps) → 1 ≤ n →
        Nat.primeCounting n + 1 = ps.length + phi ps n := by
    intro ps n hprime hnodup hle hsq hn1
    have hpos : ∀ p ∈ ps, 0 < p := fun p hp => (hprime p hp).pos
    have hpw : ps.Pairwise Nat.Coprime := by
      refine hnodup.imp_of_mem ?_
      intro a b ha hb hne
      exact (Nat.coprime_primes (hprime a ha) (hprime b hb)).mpr hne
    have hcard := card_sieve ps hpos hpw n
    set S := (Icc 1 n).filter (fun m => ∀ q ∈ ps, ¬ q ∣ m)
    have hSeq : S = insert 1 (Nat.primesLE n \ ps.toFinset) := by
      ext m
      simp only [S, mem_filter, mem_Icc, mem_insert, mem_sdiff, Nat.mem_primesLE, List.mem_toFinset]
      constructor
      · rintro ⟨⟨hm1, hmn⟩, hnd⟩
        by_cases h1 : m = 1
        · exact Or.inl h1
        · right
          have hmpr : m.Prime := by
            by_contra hnot
            have hqpr : m.minFac.Prime := Nat.minFac_prime h1
            have hqsq : m.minFac * m.minFac ≤ m := by
              simpa [sq] using Nat.minFac_sq_le_self (by omega) hnot
            have hqmem : m.minFac ∈ ps := hsq m.minFac hqpr (hqsq.trans hmn)
            exact hnd m.minFac hqmem (Nat.minFac_dvd m)
          refine ⟨⟨hmn, hmpr⟩, fun hmem => hnd m hmem dvd_rfl⟩
      · rintro (rfl | ⟨⟨hmn, hmpr⟩, hnotmem⟩)
        · exact ⟨⟨le_rfl, hn1⟩, fun q hq => (hprime q hq).not_dvd_one⟩
        · refine ⟨⟨hmpr.one_le, hmn⟩, fun q hq hdvd => ?_⟩
          have heq : q = m := (Nat.prime_dvd_prime_iff_eq (hprime q hq) hmpr).mp hdvd
          exact hnotmem (heq ▸ hq)
    have hsub : ps.toFinset ⊆ Nat.primesLE n := by
      intro p hp
      rw [List.mem_toFinset] at hp
      exact Nat.mem_primesLE.mpr ⟨hle p hp, hprime p hp⟩
    have h1not : (1 : ℕ) ∉ Nat.primesLE n \ ps.toFinset := by
      intro h1
      exact Nat.not_prime_one (Nat.mem_primesLE.mp (mem_sdiff.mp h1).1).2
    have hScard : S.card = 1 + ((Nat.primesLE n).card - ps.toFinset.card) := by
      rw [hSeq, card_insert_of_notMem h1not, card_sdiff_of_subset hsub]
      omega
    have hlen : ps.toFinset.card = ps.length := List.toFinset_card_of_nodup hnodup
    have hpi : (Nat.primesLE n).card = Nat.primeCounting n := Nat.primesLE_card_eq_primeCounting n
    have hle_card : ps.toFinset.card ≤ (Nat.primesLE n).card := card_le_card hsub
    rw [hlen, hpi] at hScard hle_card
    omega
  let ps4 : List ℕ := [7, 5, 3, 2]
  let ps11 : List ℕ := [31, 29, 23, 19, 17, 13, 11, 7, 5, 3, 2]
  have hpi4 : ∀ n : ℕ, 7 ≤ n → n ≤ 120 → Nat.primeCounting n + 1 = 4 + phi ps4 n := by
    intro n hnlo hnhi
    have hsq0 : ∀ q ≤ 10, q.Prime → q ∈ ps4 := by decide
    have hsq : ∀ q : ℕ, q.Prime → q * q ≤ n → q ∈ ps4 :=
      fun q hq hqq => hsq0 q (by nlinarith) hq
    exact primeCounting_eq_phi ps4 n (by decide) (by decide)
      (fun p hp => by
        have : p ≤ 7 := by revert p hp; decide
        omega)
      hsq (by omega)
  have hpi11 : ∀ n : ℕ, 31 ≤ n → n ≤ 1368 → Nat.primeCounting n + 1 = 11 + phi ps11 n := by
    intro n hnlo hnhi
    have hsq0 : ∀ q ≤ 36, q.Prime → q ∈ ps11 := by decide
    have hsq : ∀ q : ℕ, q.Prime → q * q ≤ n → q ∈ ps11 :=
      fun q hq hqq => hsq0 q (by nlinarith) hq
    exact primeCounting_eq_phi ps11 n (by decide) (by decide)
      (fun p hp => by
        have : p ≤ 31 := by revert p hp; decide
        omega)
      hsq (by omega)
  let ivs4 : List (ℕ × ℕ) :=
    [(11, 13), (14, 17), (18, 20), (21, 25), (26, 29), (30, 34)]
  let ivs11 : List (ℕ × ℕ) :=
    [(35, 38), (39, 43), (44, 52), (53, 64), (65, 74), (75, 89), (90, 110),
     (111, 134), (135, 154), (155, 178), (179, 209), (210, 238), (239, 283),
     (284, 335), (336, 377), (378, 427), (428, 484), (485, 547), (548, 598)]
  have hok4 : ∀ iv ∈ ivs4, 7 ≤ iv.1 ∧ 2 * iv.2 + 1 ≤ 120 ∧
      phi ps4 (2 * iv.2 + 1) < 3 + 2 * phi ps4 iv.1 := by decide
  have hok11 : ∀ iv ∈ ivs11, 31 ≤ iv.1 ∧ 2 * iv.2 + 1 ≤ 1368 ∧
      phi ps11 (2 * iv.2 + 1) < 10 + 2 * phi ps11 iv.1 := by decide
  have hcov : (∃ iv ∈ ivs4, iv.1 ≤ x ∧ x ≤ iv.2) ∨ (∃ iv ∈ ivs11, iv.1 ≤ x ∧ x ≤ iv.2) := by
    by_cases h1 : x ≤ 13; · exact Or.inl ⟨(11, 13), by decide, by omega, by omega⟩
    by_cases h2 : x ≤ 17; · exact Or.inl ⟨(14, 17), by decide, by omega, by omega⟩
    by_cases h3 : x ≤ 20; · exact Or.inl ⟨(18, 20), by decide, by omega, by omega⟩
    by_cases h4 : x ≤ 25; · exact Or.inl ⟨(21, 25), by decide, by omega, by omega⟩
    by_cases h5 : x ≤ 29; · exact Or.inl ⟨(26, 29), by decide, by omega, by omega⟩
    by_cases h6 : x ≤ 34; · exact Or.inl ⟨(30, 34), by decide, by omega, by omega⟩
    by_cases h7 : x ≤ 38; · exact Or.inr ⟨(35, 38), by decide, by omega, by omega⟩
    by_cases h8 : x ≤ 43; · exact Or.inr ⟨(39, 43), by decide, by omega, by omega⟩
    by_cases h9 : x ≤ 52; · exact Or.inr ⟨(44, 52), by decide, by omega, by omega⟩
    by_cases h10 : x ≤ 64; · exact Or.inr ⟨(53, 64), by decide, by omega, by omega⟩
    by_cases h11 : x ≤ 74; · exact Or.inr ⟨(65, 74), by decide, by omega, by omega⟩
    by_cases h12 : x ≤ 89; · exact Or.inr ⟨(75, 89), by decide, by omega, by omega⟩
    by_cases h13 : x ≤ 110; · exact Or.inr ⟨(90, 110), by decide, by omega, by omega⟩
    by_cases h14 : x ≤ 134; · exact Or.inr ⟨(111, 134), by decide, by omega, by omega⟩
    by_cases h15 : x ≤ 154; · exact Or.inr ⟨(135, 154), by decide, by omega, by omega⟩
    by_cases h16 : x ≤ 178; · exact Or.inr ⟨(155, 178), by decide, by omega, by omega⟩
    by_cases h17 : x ≤ 209; · exact Or.inr ⟨(179, 209), by decide, by omega, by omega⟩
    by_cases h18 : x ≤ 238; · exact Or.inr ⟨(210, 238), by decide, by omega, by omega⟩
    by_cases h19 : x ≤ 283; · exact Or.inr ⟨(239, 283), by decide, by omega, by omega⟩
    by_cases h20 : x ≤ 335; · exact Or.inr ⟨(284, 335), by decide, by omega, by omega⟩
    by_cases h21 : x ≤ 377; · exact Or.inr ⟨(336, 377), by decide, by omega, by omega⟩
    by_cases h22 : x ≤ 427; · exact Or.inr ⟨(378, 427), by decide, by omega, by omega⟩
    by_cases h23 : x ≤ 484; · exact Or.inr ⟨(428, 484), by decide, by omega, by omega⟩
    by_cases h24 : x ≤ 547; · exact Or.inr ⟨(485, 547), by decide, by omega, by omega⟩
    exact Or.inr ⟨(548, 598), by decide, by omega, by omega⟩
  rcases hcov with ⟨⟨a, b⟩, hmem, hax, hxb⟩ | ⟨⟨a, b⟩, hmem, hax, hxb⟩
  · obtain ⟨ha7, hb120, hcmp⟩ := hok4 (a, b) hmem
    dsimp only at ha7 hb120 hcmp hax hxb
    have hpa := hpi4 a ha7 (by omega)
    have hpb := hpi4 (2 * b + 1) (by omega) hb120
    have hm1 := Nat.monotone_primeCounting hax
    have hm2 := Nat.monotone_primeCounting (show 2 * x + 1 ≤ 2 * b + 1 by omega)
    omega
  · obtain ⟨ha31, hb1368, hcmp⟩ := hok11 (a, b) hmem
    dsimp only at ha31 hb1368 hcmp hax hxb
    have hpa := hpi11 a ha31 (by omega)
    have hpb := hpi11 (2 * b + 1) (by omega) hb1368
    have hm1 := Nat.monotone_primeCounting hax
    have hm2 := Nat.monotone_primeCounting (show 2 * x + 1 ≤ 2 * b + 1 by omega)
    omega

/-- Small helper: `Nat.nth Nat.Prime 5 = 13` and `Nat.nth Nat.Prime 7 = 19`. -/
lemma nth_prime_eq_of_count {k p : ℕ} (hp : p.Prime) (hc : Nat.primeCounting' p = k) :
    Nat.nth Nat.Prime k = p := by
  rw [← hc]
  exact Nat.nth_count hp

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a366274.main := by
  intro h1 h2 n hn
  refine ⟨n - 1, by omega, ?_⟩
  have hidx : n + 1 + (n - 1) = 2 * n := by omega
  rw [hidx]
  unfold OMA.S_oeis_a366274.prime
  rw [show n + 1 - 1 = n by omega]
  by_cases hn3 : n = 3
  · subst hn3
    have h5 : Nat.nth Nat.Prime 5 = 13 := nth_prime_eq_of_count (by decide) (by decide)
    rw [show 3 - 1 = 2 by rfl, show 2 * 3 - 1 = 5 by rfl,
      Nat.nth_prime_two_eq_five, Nat.nth_prime_three_eq_seven, h5]
    omega
  by_cases hn4 : n = 4
  · subst hn4
    have h7 : Nat.nth Nat.Prime 7 = 19 := nth_prime_eq_of_count (by decide) (by decide)
    rw [show 4 - 1 = 3 by rfl, show 2 * 4 - 1 = 7 by rfl,
      Nat.nth_prime_three_eq_seven, Nat.nth_prime_four_eq_eleven, h7]
    omega
  have hn5 : 5 ≤ n := by omega
  set p := Nat.nth Nat.Prime (n - 1)
  set q := Nat.nth Nat.Prime n
  have hmono : StrictMono (Nat.nth Nat.Prime) := Nat.nth_strictMono Nat.infinite_setOfPred_prime
  have hp_pr : p.Prime := Nat.prime_nth_prime (n - 1)
  have hq_pr : q.Prime := Nat.prime_nth_prime n
  have hp11 : 11 ≤ p := Nat.nth_prime_four_eq_eleven ▸ hmono.monotone (show 4 ≤ n - 1 by omega)
  have hpq : p < q := hmono (by omega)
  have hp_odd : p % 2 = 1 := by
    rcases hp_pr.eq_two_or_odd with h | h <;> omega
  have hq_odd : q % 2 = 1 := by
    rcases hq_pr.eq_two_or_odd with h | h <;> omega
  set x := (p + q) / 2 - 1
  have hx_lo : p ≤ x := by omega
  have hx_lt : x < q := by omega
  have hx_two : 2 * x + 1 = p + q - 1 := by omega
  have hpi_x : Nat.primeCounting x = n := by
    have hlo_c : n ≤ Nat.primeCounting x := by
      have h1' : Nat.primeCounting' (p + 1) ≤ Nat.primeCounting' (x + 1) :=
        Nat.monotone_primeCounting' (by omega)
      have h2' : Nat.primeCounting' (p + 1) = n := by
        rw [Nat.primeCounting', Nat.count_succ, if_pos hp_pr]
        have := Nat.primeCounting'_nth_eq (n - 1)
        simp only [Nat.primeCounting', p] at this ⊢
        omega
      simpa [Nat.primeCounting] using h2'.symm.trans_le h1'
    have hhi_c : Nat.primeCounting x ≤ n := by
      have h1' : Nat.primeCounting' (x + 1) ≤ Nat.primeCounting' q :=
        Nat.monotone_primeCounting' (by omega)
      have h2' : Nat.primeCounting' q = n := Nat.primeCounting'_nth_eq n
      simpa [Nat.primeCounting] using h1'.trans_eq h2'
    omega
  have hpi_lt : Nat.primeCounting (2 * x + 1) < 2 * Nat.primeCounting x := by
    by_cases hsmall : x ≤ 598
    · exact pi_double_add_one_lt_small (by omega) hsmall
    · exact pi_double_add_one_lt_large h1 h2 (by omega)
  rw [hx_two, hpi_x] at hpi_lt
  by_contra hlt
  push Not at hlt
  have hcnt : 2 * n ≤ Nat.primeCounting' (p + q) := by
    have hle1 : Nat.primeCounting' (Nat.nth Nat.Prime (2 * n - 1) + 1) ≤
        Nat.primeCounting' (p + q) := Nat.monotone_primeCounting' (by omega)
    have hpr : (Nat.nth Nat.Prime (2 * n - 1)).Prime := Nat.prime_nth_prime (2 * n - 1)
    have heq1 : Nat.primeCounting' (Nat.nth Nat.Prime (2 * n - 1) + 1) = 2 * n := by
      rw [Nat.primeCounting', Nat.count_succ, if_pos hpr]
      have := Nat.primeCounting'_nth_eq (2 * n - 1)
      simp only [Nat.primeCounting'] at this ⊢
      omega
    omega
  rw [← Nat.primeCounting_sub_one] at hcnt
  omega

end OMA.R_oeis_a366274_R1
