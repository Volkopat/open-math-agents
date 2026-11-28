import OMAReductions.R_RiemannHypothesis_lagarias_criterion_R1_H2_R1_H1_R1_H1_R1_H2_R1
import Mathlib

/-!
# Mertens' Third Theorem for the Truncated Prime-Power Harmonic Sum

We prove `OMA.R_RiemannHypothesis_lagarias_criterion_R1_H2_R1_H1_R1_H1_R1_H2_R1.H1`:
letting `F(x) = ∑_{p ≤ x} ∑_{k=1}^{⌊log_p x⌋} p^{-k} / k`, we have
`F(y) - log (log y) → γ` as `y → ∞`, where `γ = Real.eulerMascheroniConstant`.

## Proof outline
1. Rewrite `F(x)` as `∑_{n=0}^{⌊x⌋} c(n)` where `c(n) = Λ(n) / (n * log n)`.
2. Prove Mertens' first theorem `|M(N) - log N| ≤ log 4 + 4` for `M(N) = ∑_{n=1}^N Λ(n) / n`,
   using `∑_{d ∣ k} Λ(d) = log k` and Chebyshev's upper bound `ψ(N) ≤ (log 4 + 4) * N`.
3. Deduce by finite summation by parts and comparison with two absolutely summable series that
   there exists a real limit `L` with `F(y) - log (log y) → L` as `y → ∞`.
4. Identify `L = γ` by evaluating `G(δ) + log δ` as `δ → 0⁺`, where
   `G(δ) = ∑'_{n} c(n) * n^{-δ}`:
   - By the Euler product for `riemannZeta` and `log_riemannZeta_add_log_sub_isLittleO_ofReal`,
     `G(δ) + log δ → 0`.
   - By Abel summation and the substitution `u = δ * log t`,
     `G(δ) + log δ → L + ∫_{0}^{∞} log u * exp (-u) du = L - γ`,
     where the Gamma-derivative integral is evaluated via `Real.hasDerivAt_Gamma_one`.
-/

namespace OMA.MertensThirdProof

open Filter Finset Real Set MeasureTheory Topology ArithmeticFunction

private noncomputable def F (x : ℝ) : ℝ :=
  ∑ p ∈ Nat.primesLE ⌊x⌋₊, ∑ k ∈ Finset.range (Nat.log p ⌊x⌋₊),
    ((1 : ℝ) / p) ^ (k + 1) / ((k : ℝ) + 1)

private noncomputable def c (n : ℕ) : ℝ :=
  Λ n / ((n : ℝ) * Real.log n)

private noncomputable def M (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, Λ n / (n : ℝ)

/- ### Step 1: Rewriting `F` via `vonMangoldt` -/

private lemma c_zero : c 0 = 0 := by
  simp [c]

private lemma c_one : c 1 = 0 := by
  simp [c]

private lemma c_nonneg (n : ℕ) : 0 ≤ c n := by
  unfold c
  by_cases hn : n = 0
  · subst hn; simp
  · have h1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    exact div_nonneg vonMangoldt_nonneg (mul_nonneg (Nat.cast_nonneg n) (Real.log_nonneg h1))

private lemma c_eq_zero_of_not_isPrimePow {n : ℕ} (hn : ¬ IsPrimePow n) : c n = 0 := by
  simp [c, vonMangoldt_eq_zero_iff.mpr hn]

private lemma c_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    c (p ^ (k + 1)) = ((1 : ℝ) / p) ^ (k + 1) / ((k : ℝ) + 1) := by
  unfold c
  have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp_gt1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hlogp : Real.log (p : ℝ) ≠ 0 := (Real.log_pos hp_gt1).ne'
  have hL : Λ (p ^ (k + 1)) = Real.log p := by
    rw [vonMangoldt_apply_pow (Nat.succ_ne_zero k), vonMangoldt_apply_prime hp]
  rw [hL, Nat.cast_pow, Real.log_pow, one_div, inv_pow]
  push_cast
  field_simp [hlogp, hp_pos.ne']

private lemma prime_pow_inj {p₁ p₂ k₁ k₂ : ℕ} (hp₁ : p₁.Prime) (hp₂ : p₂.Prime)
    (h : p₁ ^ (k₁ + 1) = p₂ ^ (k₂ + 1)) : p₁ = p₂ ∧ k₁ = k₂ := by
  have hdvd : p₁ ∣ p₂ ^ (k₂ + 1) := h ▸ dvd_pow_self p₁ (Nat.succ_ne_zero k₁)
  have hdvd' : p₁ ∣ p₂ := hp₁.dvd_of_dvd_pow hdvd
  have hp_eq : p₁ = p₂ := (Nat.prime_dvd_prime_iff_eq hp₁ hp₂).mp hdvd'
  subst hp_eq
  have hk : k₁ + 1 = k₂ + 1 := Nat.pow_right_injective hp₁.two_le h
  exact ⟨rfl, by omega⟩

private lemma F_eq_sum_c (x : ℝ) : F x = ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, c n := by
  classical
  unfold F
  set N := ⌊x⌋₊
  have hsig :
      ∑ p ∈ Nat.primesLE N, ∑ k ∈ Finset.range (Nat.log p N),
        ((1 : ℝ) / p) ^ (k + 1) / ((k : ℝ) + 1) =
      ∑ a ∈ (Nat.primesLE N).sigma (fun p => Finset.range (Nat.log p N)),
        ((1 : ℝ) / a.1) ^ (a.2 + 1) / ((a.2 : ℝ) + 1) :=
    (Finset.sum_sigma _ _ (fun a : (_ : ℕ) × ℕ => ((1 : ℝ) / a.1) ^ (a.2 + 1) / ((a.2 : ℝ) + 1))).symm
  have hfilt : ∑ n ∈ Finset.Icc 0 N, c n = ∑ n ∈ (Finset.Icc 0 N).filter IsPrimePow, c n :=
    (Finset.sum_filter_of_ne fun n _ hn => by
      by_contra hnot; exact hn (c_eq_zero_of_not_isPrimePow hnot)).symm
  rw [hsig, hfilt]
  refine Finset.sum_bij (fun a _ => a.1 ^ (a.2 + 1)) ?_ ?_ ?_ ?_
  · rintro ⟨p, k⟩ ha
    simp only [Finset.mem_sigma, Finset.mem_range] at ha
    have hp : p.Prime := Nat.prime_of_mem_primesLE ha.1
    have hpN : p ≤ N := Nat.le_of_mem_primesLE ha.1
    have hN0 : N ≠ 0 := by have := hp.pos; omega
    have hpow : p ^ (k + 1) ≤ N :=
      (Nat.le_log_iff_pow_le hp.one_lt hN0).mp (Nat.succ_le_of_lt ha.2)
    simp only [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨Nat.zero_le _, hpow⟩, hp.isPrimePow.pow (Nat.succ_ne_zero k)⟩
  · rintro ⟨p₁, k₁⟩ ha₁ ⟨p₂, k₂⟩ ha₂ h
    simp only [Finset.mem_sigma] at ha₁ ha₂
    have ⟨hp, hk⟩ := prime_pow_inj (Nat.prime_of_mem_primesLE ha₁.1)
      (Nat.prime_of_mem_primesLE ha₂.1) h
    subst hp; subst hk; rfl
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨p, m, hp_nat, hm_pos, rfl⟩ := (isPrimePow_nat_iff n).mp hn.2
    obtain ⟨k, hk_eq⟩ := Nat.exists_eq_succ_of_ne_zero hm_pos.ne'
    have hpow_le : p ^ (k + 1) ≤ N := by simpa [hk_eq] using hn.1.2
    have hN0 : N ≠ 0 := by
      have : 0 < p ^ (k + 1) := pow_pos hp_nat.pos _
      omega
    have hp_le : p ≤ N := (Nat.le_self_pow (Nat.succ_ne_zero k) p).trans hpow_le
    have hk_lt : k < Nat.log p N :=
      Nat.lt_of_succ_le ((Nat.le_log_iff_pow_le hp_nat.one_lt hN0).mpr hpow_le)
    refine ⟨⟨p, k⟩, ?_, by simp [hk_eq]⟩
    simp only [Finset.mem_sigma, Finset.mem_range]
    exact ⟨Nat.mem_primesLE.mpr ⟨hp_le, hp_nat⟩, hk_lt⟩
  · rintro ⟨p, k⟩ ha
    simp only [Finset.mem_sigma] at ha
    exact (c_prime_pow (Nat.prime_of_mem_primesLE ha.1) k).symm

private lemma F_eq_zero_of_lt_two {x : ℝ} (hx : x < 2) : F x = 0 := by
  rw [F_eq_sum_c]
  apply Finset.sum_eq_zero
  intro n hn
  simp only [Finset.mem_Icc] at hn
  have hfl : ⌊x⌋₊ < 2 := (Nat.floor_lt' (by norm_num)).mpr hx
  have hn1 : n = 0 ∨ n = 1 := by omega
  rcases hn1 with rfl | rfl
  · exact c_zero
  · exact c_one

private lemma F_mono : Monotone F := by
  intro x y hxy
  rw [F_eq_sum_c, F_eq_sum_c]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.Icc_subset_Icc_right (Nat.floor_le_floor hxy))
    (fun n _ _ => c_nonneg n)

private lemma F_nonneg (x : ℝ) : 0 ≤ F x := by
  rw [F_eq_sum_c]
  exact Finset.sum_nonneg (fun n _ => c_nonneg n)

/- ### Step 2: Mertens' first theorem `|M(N) - log N| ≤ log 4 + 4` -/

private lemma sum_log_eq_sum_vonMangoldt_mul_div (N : ℕ) :
    ∑ k ∈ Finset.Icc 1 N, Real.log k = ∑ d ∈ Finset.Icc 1 N, Λ d * ((N / d : ℕ) : ℝ) := by
  have h1 : ∀ k ∈ Finset.Icc 1 N, Real.log k = ∑ d ∈ k.divisors, Λ d := fun k _ =>
    (vonMangoldt_sum (n := k)).symm
  rw [Finset.sum_congr rfl h1]
  have h2 : ∑ k ∈ Finset.Icc 1 N, ∑ d ∈ k.divisors, Λ d =
      ∑ k ∈ Finset.Icc 1 N, ∑ d ∈ Finset.Icc 1 N, if d ∣ k then Λ d else 0 := by
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext d
    simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have hkN : k ≤ N := (Finset.mem_Icc.mp hk).2
    have hk0 : k ≠ 0 := by omega
    constructor
    · rintro ⟨hd, _⟩
      have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd (by omega)
      have hdle : d ≤ k := Nat.le_of_dvd (by omega) hd
      exact ⟨⟨hdpos, hdle.trans hkN⟩, hd⟩
    · rintro ⟨_, hd⟩
      exact ⟨hd, hk0⟩
  rw [h2, Finset.sum_comm]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  congr 1
  have hdpos : 0 < d := (Finset.mem_Icc.mp hd).1
  have hcard : ((Finset.Icc 1 N).filter (fun k => d ∣ k)).card = N / d := by
    have heq : (Finset.Icc 1 N).filter (fun k => d ∣ k) =
        (Finset.Icc 1 (N / d)).image (fun m => d * m) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
      constructor
      · rintro ⟨⟨hk1, hkN⟩, ⟨m, rfl⟩⟩
        refine ⟨m, ⟨?_, ?_⟩, rfl⟩
        · by_contra hm
          have : m = 0 := by omega
          subst this; simp at hk1
        · exact (Nat.le_div_iff_mul_le hdpos).mpr (by linarith)
      · rintro ⟨m, ⟨hm1, hmN⟩, rfl⟩
        refine ⟨⟨?_, ?_⟩, ⟨m, rfl⟩⟩
        · exact Nat.mul_pos hdpos hm1
        · have := (Nat.le_div_iff_mul_le hdpos).mp hmN
          linarith
    rw [heq, Finset.card_image_of_injective _ (mul_right_injective₀ hdpos.ne'), Nat.card_Icc]
    exact Nat.add_sub_cancel (N / d) 1
  exact_mod_cast hcard

private lemma sum_log_ge_mul_log_sub (N : ℕ) (hN : 1 ≤ N) :
    (N : ℝ) * Real.log N - N ≤ ∑ k ∈ Finset.Icc 1 N, Real.log k := by
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    have hIcc : Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
      ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [hIcc, Finset.sum_insert (by simp)]
    have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
    have hlog_step : (n : ℝ) * (Real.log (n + 1 : ℝ) - Real.log n) ≤ 1 := by
      have hdiv : Real.log ((n + 1 : ℝ) / n) ≤ (n + 1 : ℝ) / n - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      rw [Real.log_div (by positivity) hn_pos.ne'] at hdiv
      have hmul := mul_le_mul_of_nonneg_left hdiv hn_pos.le
      have hsimp : (n : ℝ) * ((n + 1 : ℝ) / n - 1) = 1 := by field_simp [hn_pos.ne']; ring
      linarith
    push_cast
    linarith

private lemma sum_log_le_mul_log (N : ℕ) :
    ∑ k ∈ Finset.Icc 1 N, Real.log k ≤ (N : ℝ) * Real.log N := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  · calc ∑ k ∈ Finset.Icc 1 N, Real.log k
        ≤ ∑ _k ∈ Finset.Icc 1 N, Real.log N := by
          refine Finset.sum_le_sum fun k hk => ?_
          have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
          have hkN : k ≤ N := (Finset.mem_Icc.mp hk).2
          exact Real.log_le_log (by exact_mod_cast hk1) (by exact_mod_cast hkN)
      _ = (N : ℝ) * Real.log N := by
          rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
          simp

private lemma mertens_first_bound (N : ℕ) (hN : 1 ≤ N) :
    |M N - Real.log N| ≤ Real.log 4 + 4 := by
  have hN_pos : (0 : ℝ) < N := by exact_mod_cast hN
  have hNM : (N : ℝ) * M N = ∑ d ∈ Finset.Icc 1 N, Λ d * ((N : ℝ) / d) := by
    unfold M
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => by ring
  have hlow : ∑ k ∈ Finset.Icc 1 N, Real.log k ≤ (N : ℝ) * M N := by
    rw [sum_log_eq_sum_vonMangoldt_mul_div, hNM]
    refine Finset.sum_le_sum fun d hd => ?_
    have hd_pos : (0 : ℝ) < d := by exact_mod_cast (Finset.mem_Icc.mp hd).1
    refine mul_le_mul_of_nonneg_left ?_ vonMangoldt_nonneg
    exact Nat.cast_div_le
  have hup : (N : ℝ) * M N - ∑ k ∈ Finset.Icc 1 N, Real.log k ≤ Chebyshev.psi N := by
    rw [sum_log_eq_sum_vonMangoldt_mul_div, hNM, ← Finset.sum_sub_distrib]
    have hpsi : Chebyshev.psi N = ∑ d ∈ Finset.Icc 1 N, Λ d := by
      unfold Chebyshev.psi
      rw [Nat.floor_natCast]
      refine Finset.sum_congr ?_ (fun _ _ => rfl)
      ext d; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega
    rw [hpsi]
    refine Finset.sum_le_sum fun d hd => ?_
    have hd_pos : (0 : ℝ) < d := by exact_mod_cast (Finset.mem_Icc.mp hd).1
    rw [← mul_sub]
    have hdiff : (N : ℝ) / d - ((N / d : ℕ) : ℝ) ≤ 1 := by
      have hlt : (N : ℝ) / d < ((N / d : ℕ) : ℝ) + 1 := by
        rw [← Nat.floor_div_eq_div (K := ℝ)]
        exact Nat.lt_floor_add_one _
      linarith
    calc Λ d * ((N : ℝ) / d - ((N / d : ℕ) : ℝ))
        ≤ Λ d * 1 := mul_le_mul_of_nonneg_left hdiff vonMangoldt_nonneg
      _ = Λ d := mul_one _
  have hpsi_le : Chebyshev.psi N ≤ (Real.log 4 + 4) * N :=
    Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg N)
  have hlog_ge := sum_log_ge_mul_log_sub N hN
  have hlog_le := sum_log_le_mul_log N
  have hlog4_pos : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  rw [abs_le]
  constructor
  · have h1 : (N : ℝ) * (Real.log N - 1) ≤ (N : ℝ) * M N := by linarith
    have h2 : Real.log N - 1 ≤ M N := le_of_mul_le_mul_left h1 hN_pos
    linarith
  · have h1 : (N : ℝ) * M N ≤ (N : ℝ) * (Real.log N + (Real.log 4 + 4)) := by linarith
    have h2 : M N ≤ Real.log N + (Real.log 4 + 4) := le_of_mul_le_mul_left h1 hN_pos
    linarith

/- ### Step 3: Existence of the limit `L` for `F(y) - log (log y)` -/

private lemma M_sub_prev {n : ℕ} (hn : 2 ≤ n) : M n - M (n - 1) = Λ n / (n : ℝ) := by
  unfold M
  have hIcc : Finset.Icc 1 n = insert n (Finset.Icc 1 (n - 1)) := by
    ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  rw [hIcc, Finset.sum_insert (by simp; omega)]
  ring

private lemma summable_loglog_err :
    Summable (fun n : ℕ =>
      if 3 ≤ n then
        (Real.log (Real.log n) - Real.log (Real.log (n - 1 : ℕ))) -
          (Real.log n - Real.log (n - 1 : ℕ)) / Real.log n
      else 0) := by
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine Summable.of_nonneg_of_le (f := fun n : ℕ => (1 / (Real.log 2) ^ 2) * (1 / ((n - 1 : ℕ) : ℝ) ^ 2))
    ?_ ?_ ?_
  · intro n
    split_ifs with hn
    · have ha : 0 < Real.log ((n - 1 : ℕ) : ℝ) :=
        Real.log_pos (by exact_mod_cast (by omega : 1 < n - 1))
      have hb : 0 < Real.log (n : ℝ) :=
        Real.log_pos (by exact_mod_cast (by omega : 1 < n))
      have h1 : 1 - Real.log ((n - 1 : ℕ) : ℝ) / Real.log n ≤
          Real.log (Real.log n / Real.log ((n - 1 : ℕ) : ℝ)) := by
        have := Real.one_sub_inv_le_log_of_pos (div_pos hb ha)
        rwa [inv_div] at this
      rw [Real.log_div hb.ne' ha.ne'] at h1
      have h2 : 1 - Real.log ((n - 1 : ℕ) : ℝ) / Real.log n =
          (Real.log n - Real.log ((n - 1 : ℕ) : ℝ)) / Real.log n := by
        field_simp [hb.ne']
      linarith
    · exact le_rfl
  · intro n
    split_ifs with hn
    · have hn1_ge2 : (2 : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 ≤ n - 1)
      have hn1_pos : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := by linarith
      have ha : Real.log 2 ≤ Real.log ((n - 1 : ℕ) : ℝ) := Real.log_le_log (by norm_num) hn1_ge2
      have ha_pos : 0 < Real.log ((n - 1 : ℕ) : ℝ) := hlog2_pos.trans_le ha
      have hb_ge : Real.log ((n - 1 : ℕ) : ℝ) ≤ Real.log (n : ℝ) :=
        Real.log_le_log hn1_pos (by exact_mod_cast (by omega : n - 1 ≤ n))
      have hb_pos : 0 < Real.log (n : ℝ) := ha_pos.trans_le hb_ge
      have hupper : Real.log (Real.log n) - Real.log (Real.log ((n - 1 : ℕ) : ℝ)) ≤
          (Real.log n - Real.log ((n - 1 : ℕ) : ℝ)) / Real.log ((n - 1 : ℕ) : ℝ) := by
        have := Real.log_le_sub_one_of_pos (div_pos hb_pos ha_pos)
        rw [Real.log_div hb_pos.ne' ha_pos.ne'] at this
        have hrew : Real.log n / Real.log ((n - 1 : ℕ) : ℝ) - 1 =
            (Real.log n - Real.log ((n - 1 : ℕ) : ℝ)) / Real.log ((n - 1 : ℕ) : ℝ) := by
          field_simp [ha_pos.ne']
        linarith
      have hdiff_nonneg : 0 ≤ Real.log n - Real.log ((n - 1 : ℕ) : ℝ) := by linarith
      have hdiff_le : Real.log n - Real.log ((n - 1 : ℕ) : ℝ) ≤ 1 / ((n - 1 : ℕ) : ℝ) := by
        have hcast : (n : ℝ) = ((n - 1 : ℕ) : ℝ) + 1 := by
          have : n = (n - 1) + 1 := by omega
          exact_mod_cast this
        have hdiv := Real.log_le_sub_one_of_pos (div_pos (by linarith : (0 : ℝ) < n) hn1_pos)
        rw [Real.log_div (by linarith) hn1_pos.ne'] at hdiv
        have hrew : (n : ℝ) / ((n - 1 : ℕ) : ℝ) - 1 = 1 / ((n - 1 : ℕ) : ℝ) := by
          rw [hcast]; field_simp [hn1_pos.ne']; ring
        linarith
      have hcomb : (Real.log n - Real.log ((n - 1 : ℕ) : ℝ)) / Real.log ((n - 1 : ℕ) : ℝ) -
          (Real.log n - Real.log ((n - 1 : ℕ) : ℝ)) / Real.log n =
          (Real.log n - Real.log ((n - 1 : ℕ) : ℝ)) ^ 2 /
            (Real.log ((n - 1 : ℕ) : ℝ) * Real.log n) := by
        field_simp [ha_pos.ne', hb_pos.ne']
      have hden : (Real.log 2) ^ 2 ≤ Real.log ((n - 1 : ℕ) : ℝ) * Real.log n := by
        rw [sq]
        exact mul_le_mul ha (ha.trans hb_ge) hlog2_pos.le ha_pos.le
      calc (Real.log (Real.log n) - Real.log (Real.log ((n - 1 : ℕ) : ℝ))) -
              (Real.log n - Real.log ((n - 1 : ℕ) : ℝ)) / Real.log n
          ≤ (Real.log n - Real.log ((n - 1 : ℕ) : ℝ)) ^ 2 /
              (Real.log ((n - 1 : ℕ) : ℝ) * Real.log n) := by linarith
        _ ≤ (1 / ((n - 1 : ℕ) : ℝ)) ^ 2 / (Real.log 2) ^ 2 := by
            exact div_le_div₀ (by positivity)
              (pow_le_pow_left₀ hdiff_nonneg hdiff_le 2) (by positivity) hden
        _ = (1 / (Real.log 2) ^ 2) * (1 / ((n - 1 : ℕ) : ℝ) ^ 2) := by ring
    · positivity
  · have hshift : Summable (fun n : ℕ => (1 : ℝ) / ((n - 1 : ℕ) : ℝ) ^ 2) := by
      rw [← summable_nat_add_iff 1]
      simp
    exact hshift.mul_left _

private lemma sum_by_parts_R (R : ℕ → ℝ) (N : ℕ) (hN : 2 ≤ N) :
    ∑ n ∈ Finset.Icc 3 N, (R n - R (n - 1)) / Real.log n =
      R N / Real.log N - R 2 / Real.log 2 +
        ∑ n ∈ Finset.Icc 2 (N - 1), R n * (1 / Real.log n - 1 / Real.log (n + 1 : ℕ)) := by
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ k hk ih =>
    have hIcc1 : Finset.Icc 3 (k + 1) = insert (k + 1) (Finset.Icc 3 k) := by
      ext m; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hIcc2 : Finset.Icc 2 k = insert k (Finset.Icc 2 (k - 1)) := by
      ext m; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [hIcc1, Finset.sum_insert (by simp), ih]
    simp only [Nat.add_sub_cancel]
    rw [hIcc2, Finset.sum_insert (by simp; omega)]
    ring

private lemma summable_R_log_diff :
    Summable (fun n : ℕ =>
      if 2 ≤ n then (M n - Real.log n) * (1 / Real.log n - 1 / Real.log (n + 1 : ℕ)) else 0) := by
  set C₁ := Real.log 4 + 4
  have hC₁ : 0 ≤ C₁ := by have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4); linarith
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have htele : Summable (fun n : ℕ =>
      if 2 ≤ n then 1 / Real.log n - 1 / Real.log (n + 1 : ℕ) else 0) := by
    refine summable_of_sum_range_le (c := 1 / Real.log 2) ?_ ?_
    · intro n
      split_ifs with hn
      · have h1 : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
        have h2 : Real.log (n : ℝ) ≤ Real.log ((n + 1 : ℕ) : ℝ) :=
          Real.log_le_log (by exact_mod_cast (by omega : 0 < n)) (by exact_mod_cast (by omega : n ≤ n + 1))
        exact sub_nonneg.mpr (one_div_le_one_div_of_le h1 h2)
      · exact le_rfl
    · intro N
      have hsum_eq : ∀ m : ℕ, 2 ≤ m →
          ∑ n ∈ Finset.range m, (if 2 ≤ n then 1 / Real.log n - 1 / Real.log (n + 1 : ℕ) else 0) =
            1 / Real.log 2 - 1 / Real.log m := by
        intro m hm
        induction m, hm using Nat.le_induction with
        | base => simp [Finset.sum_range_succ]
        | succ j hj ihj =>
          rw [Finset.sum_range_succ, ihj, if_pos hj]
          ring
      by_cases hN : 2 ≤ N
      · rw [hsum_eq N hN]
        have hpos : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
        linarith [one_div_pos.mpr hpos]
      · have hzero : ∑ n ∈ Finset.range N,
            (if 2 ≤ n then 1 / Real.log n - 1 / Real.log (n + 1 : ℕ) else 0) = 0 :=
          Finset.sum_eq_zero fun n hn => by
            rw [if_neg (by simp only [Finset.mem_range] at hn; omega)]
        rw [hzero]
        exact one_div_nonneg.mpr hlog2_pos.le
  refine Summable.of_norm_bounded (htele.mul_left C₁) fun n => ?_
  split_ifs with hn
  · rw [Real.norm_eq_abs, abs_mul]
    have h1 : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
    have h2 : Real.log (n : ℝ) ≤ Real.log ((n + 1 : ℕ) : ℝ) :=
      Real.log_le_log (by exact_mod_cast (by omega : 0 < n)) (by exact_mod_cast (by omega : n ≤ n + 1))
    have hdiff : 0 ≤ 1 / Real.log n - 1 / Real.log (n + 1 : ℕ) :=
      sub_nonneg.mpr (one_div_le_one_div_of_le h1 h2)
    rw [abs_of_nonneg hdiff]
    exact mul_le_mul_of_nonneg_right (mertens_first_bound n (by omega)) hdiff
  · simp

private lemma exists_limit_F_sub_log_log :
    ∃ L : ℝ, Tendsto (fun y : ℝ => F y - Real.log (Real.log y)) atTop (𝓝 L) := by
  let d : ℕ → ℝ := fun n =>
    if 3 ≤ n then
      (Real.log (Real.log n) - Real.log (Real.log (n - 1 : ℕ))) -
        (Real.log n - Real.log (n - 1 : ℕ)) / Real.log n
    else 0
  let R : ℕ → ℝ := fun n => M n - Real.log n
  let s : ℕ → ℝ := fun n =>
    if 2 ≤ n then R n * (1 / Real.log n - 1 / Real.log (n + 1 : ℕ)) else 0
  have hd_sum : Summable d := summable_loglog_err
  have hs_sum : Summable s := summable_R_log_diff
  let L : ℝ := F 2 - Real.log (Real.log 2) - (∑' n, d n) - R 2 / Real.log 2 + (∑' n, s n)
  refine ⟨L, ?_⟩
  have hnat : Tendsto (fun N : ℕ => F N - Real.log (Real.log N)) atTop (𝓝 L) := by
    have h_eq : ∀ N : ℕ, 2 ≤ N →
        F N - Real.log (Real.log N) =
          F 2 - Real.log (Real.log 2) - (∑ n ∈ Finset.range (N + 1), d n) +
            R N / Real.log N - R 2 / Real.log 2 + (∑ n ∈ Finset.range N, s n) := by
      intro N hN
      have htele_ll : ∑ n ∈ Finset.Icc 3 N,
          (Real.log (Real.log n) - Real.log (Real.log (n - 1 : ℕ))) =
          Real.log (Real.log N) - Real.log (Real.log 2) := by
        induction N, hN using Nat.le_induction with
        | base => simp
        | succ k hk ih =>
          have hIcc : Finset.Icc 3 (k + 1) = insert (k + 1) (Finset.Icc 3 k) := by
            ext m; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
          rw [hIcc, Finset.sum_insert (by simp), ih]
          simp only [Nat.add_sub_cancel]
          ring
      have hFN : F N - F 2 = ∑ n ∈ Finset.Icc 3 N, c n := by
        rw [F_eq_sum_c, F_eq_sum_c, Nat.floor_natCast, Nat.floor_ofNat]
        have hsplit : Finset.Icc 0 N = Finset.Icc 0 2 ∪ Finset.Icc 3 N := by
          ext k; simp only [Finset.mem_Icc, Finset.mem_union]; omega
        rw [hsplit, Finset.sum_union (Finset.disjoint_left.mpr fun k hk1 hk2 => by
          simp only [Finset.mem_Icc] at hk1 hk2; omega)]
        ring
      have hc_decomp : ∑ n ∈ Finset.Icc 3 N, c n =
          (∑ n ∈ Finset.Icc 3 N, (Real.log n - Real.log (n - 1 : ℕ)) / Real.log n) +
            (∑ n ∈ Finset.Icc 3 N, (R n - R (n - 1)) / Real.log n) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun n hn => ?_
        have hn3 : 3 ≤ n := (Finset.mem_Icc.mp hn).1
        have hM := M_sub_prev (by omega : 2 ≤ n)
        unfold c
        dsimp only [R]
        rw [← div_div, ← hM]
        ring
      have hd_eq : ∑ n ∈ Finset.range (N + 1), d n =
          (Real.log (Real.log N) - Real.log (Real.log 2)) -
            ∑ n ∈ Finset.Icc 3 N, (Real.log n - Real.log (n - 1 : ℕ)) / Real.log n := by
        rw [← htele_ll, ← Finset.sum_sub_distrib]
        have hsub : Finset.range (N + 1) = Finset.range 3 ∪ Finset.Icc 3 N := by
          ext m; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Icc]; omega
        rw [hsub, Finset.sum_union (Finset.disjoint_left.mpr fun m hm1 hm2 => by
          simp only [Finset.mem_range, Finset.mem_Icc] at hm1 hm2; omega)]
        have hzero : ∑ n ∈ Finset.range 3, d n = 0 :=
          Finset.sum_eq_zero fun n hn => by
            dsimp only [d]; rw [if_neg (by simp only [Finset.mem_range] at hn; omega)]
        rw [hzero, zero_add]
        refine Finset.sum_congr rfl fun n hn => by
          dsimp only [d]; rw [if_pos (Finset.mem_Icc.mp hn).1]
      have hs_eq : ∑ n ∈ Finset.range N, s n =
          ∑ n ∈ Finset.Icc 2 (N - 1), R n * (1 / Real.log n - 1 / Real.log (n + 1 : ℕ)) := by
        have hsub : Finset.range N = Finset.range 2 ∪ Finset.Icc 2 (N - 1) := by
          ext m; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Icc]; omega
        rw [hsub, Finset.sum_union (Finset.disjoint_left.mpr fun m hm1 hm2 => by
          simp only [Finset.mem_range, Finset.mem_Icc] at hm1 hm2; omega)]
        have hzero : ∑ n ∈ Finset.range 2, s n = 0 :=
          Finset.sum_eq_zero fun n hn => by
            dsimp only [s]; rw [if_neg (by simp only [Finset.mem_range] at hn; omega)]
        rw [hzero, zero_add]
        refine Finset.sum_congr rfl fun n hn => by
          dsimp only [s]; rw [if_pos (Finset.mem_Icc.mp hn).1]
      have hparts := sum_by_parts_R R N hN
      linarith
    have hR_zero : Tendsto (fun N : ℕ => R N / Real.log N) atTop (𝓝 0) := by
      refine squeeze_zero_norm' (a := fun N : ℕ => (Real.log 4 + 4) / Real.log N) ?_ ?_
      · filter_upwards [eventually_ge_atTop 2] with N hN
        rw [Real.norm_eq_abs, abs_div, abs_of_pos (Real.log_pos (by exact_mod_cast (by omega : 1 < N)))]
        exact div_le_div_of_nonneg_right (mertens_first_bound N (by omega))
          (Real.log_pos (by exact_mod_cast (by omega : 1 < N))).le
      · simpa using (tendsto_const_nhds (x := Real.log 4 + 4)).div_atTop
          (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
    have h1 : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range (N + 1), d n) atTop (𝓝 (∑' n, d n)) :=
      hd_sum.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
    have h2 : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, s n) atTop (𝓝 (∑' n, s n)) :=
      hs_sum.hasSum.tendsto_sum_nat
    have hcomb : Tendsto (fun N : ℕ =>
        F 2 - Real.log (Real.log 2) - (∑ n ∈ Finset.range (N + 1), d n) +
          R N / Real.log N - R 2 / Real.log 2 + (∑ n ∈ Finset.range N, s n)) atTop (𝓝 L) := by
      have := (((tendsto_const_nhds (x := F 2 - Real.log (Real.log 2))).sub h1).add hR_zero).sub
        (tendsto_const_nhds (x := R 2 / Real.log 2)) |>.add h2
      simpa [L] using this
    refine hcomb.congr' ?_
    filter_upwards [eventually_ge_atTop 2] with N hN using (h_eq N hN).symm
  -- Extend from `ℕ` to `ℝ` via `⌊y⌋₊`
  have hfl : Tendsto (fun y : ℝ => F ⌊y⌋₊ - Real.log (Real.log ⌊y⌋₊)) atTop (𝓝 L) :=
    hnat.comp tendsto_nat_floor_atTop
  have herr : Tendsto (fun y : ℝ => Real.log (Real.log y) - Real.log (Real.log ⌊y⌋₊)) atTop (𝓝 0) := by
    refine squeeze_zero' ?_ ?_
      ((tendsto_const_nhds (x := (1 : ℝ))).div_atTop
        ((tendsto_natCast_atTop_atTop.comp tendsto_nat_floor_atTop).atTop_mul_atTop₀
          (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp tendsto_nat_floor_atTop))))
    · filter_upwards [eventually_ge_atTop (3 : ℝ)] with y hy
      have hfl2 : (2 : ℝ) ≤ ⌊y⌋₊ := by
        have : 2 ≤ ⌊y⌋₊ := Nat.le_floor (by norm_num; linarith)
        exact_mod_cast this
      have hle : (⌊y⌋₊ : ℝ) ≤ y := Nat.floor_le (by linarith)
      have hl1 : 0 < Real.log (⌊y⌋₊ : ℝ) := Real.log_pos (by linarith)
      have hl2 : Real.log (⌊y⌋₊ : ℝ) ≤ Real.log y := Real.log_le_log (by linarith) hle
      exact sub_nonneg.mpr (Real.log_le_log hl1 hl2)
    · filter_upwards [eventually_ge_atTop (3 : ℝ)] with y hy
      have hfl2 : (2 : ℝ) ≤ ⌊y⌋₊ := by
        have : 2 ≤ ⌊y⌋₊ := Nat.le_floor (by norm_num; linarith)
        exact_mod_cast this
      have hfl_pos : (0 : ℝ) < ⌊y⌋₊ := by linarith
      have hy_lt : y < (⌊y⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one y
      have hle : (⌊y⌋₊ : ℝ) ≤ y := Nat.floor_le (by linarith)
      have hl1 : 0 < Real.log (⌊y⌋₊ : ℝ) := Real.log_pos (by linarith)
      have hl2 : 0 < Real.log y := Real.log_pos (by linarith)
      have hstep1 : Real.log (Real.log y) - Real.log (Real.log (⌊y⌋₊ : ℝ)) ≤
          (Real.log y - Real.log (⌊y⌋₊ : ℝ)) / Real.log (⌊y⌋₊ : ℝ) := by
        have := Real.log_le_sub_one_of_pos (div_pos hl2 hl1)
        rw [Real.log_div hl2.ne' hl1.ne'] at this
        have hrew : Real.log y / Real.log (⌊y⌋₊ : ℝ) - 1 =
            (Real.log y - Real.log (⌊y⌋₊ : ℝ)) / Real.log (⌊y⌋₊ : ℝ) := by
          field_simp [hl1.ne']
        linarith
      have hstep2 : Real.log y - Real.log (⌊y⌋₊ : ℝ) ≤ 1 / (⌊y⌋₊ : ℝ) := by
        have := Real.log_le_sub_one_of_pos (div_pos (by linarith : 0 < y) hfl_pos)
        rw [Real.log_div (by linarith) hfl_pos.ne'] at this
        have hrew : y / (⌊y⌋₊ : ℝ) - 1 ≤ 1 / (⌊y⌋₊ : ℝ) := by
          rw [div_sub_one hfl_pos.ne']
          exact div_le_div_of_nonneg_right (by linarith) hfl_pos.le
        linarith
      calc Real.log (Real.log y) - Real.log (Real.log (⌊y⌋₊ : ℝ))
          ≤ (Real.log y - Real.log (⌊y⌋₊ : ℝ)) / Real.log (⌊y⌋₊ : ℝ) := hstep1
        _ ≤ (1 / (⌊y⌋₊ : ℝ)) / Real.log (⌊y⌋₊ : ℝ) :=
            div_le_div_of_nonneg_right hstep2 hl1.le
        _ = 1 / ((⌊y⌋₊ : ℝ) * Real.log (⌊y⌋₊ : ℝ)) := by ring
  have hsub := hfl.sub herr
  rw [sub_zero] at hsub
  refine hsub.congr' ?_
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with y hy
  have hFy : F (⌊y⌋₊ : ℝ) = F y := by
    simp only [F, Nat.floor_natCast]
  rw [hFy]
  ring

/- ### Step 4A: Gamma derivative integral `∫_{0}^{∞} log u * exp (-u) du = -γ` -/

private lemma integrableOn_log_mul_exp_neg :
    IntegrableOn (fun u : ℝ => Real.exp (-u) * Real.log u) (Ioi 0) := by
  have hbound : IntegrableOn (fun u : ℝ =>
      4 * (Real.exp (-u) * u ^ ((1 / 4 : ℝ) - 1)) +
        Real.exp (-u) * u ^ ((5 / 2 : ℝ) - 1)) (Ioi 0) :=
    ((Real.GammaIntegral_convergent (by norm_num : (0 : ℝ) < 1 / 4)).const_mul 4).add
      (Real.GammaIntegral_convergent (by norm_num : (0 : ℝ) < 5 / 2))
  refine hbound.mono' ?_ ?_
  · exact ((Real.continuous_exp.comp continuous_neg).measurable.mul
      Real.measurable_log).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu_pos : 0 < u := hu
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos (-u))]
    by_cases h1 : u ≤ 1
    · have hlog_neg : Real.log u ≤ 0 := Real.log_nonpos hu_pos.le h1
      have habs : |Real.log u| = Real.log (u⁻¹) := by
        rw [abs_of_nonpos hlog_neg, Real.log_inv]
      have hle : Real.log (u⁻¹) ≤ 4 * u ^ (-(1 / 4 : ℝ)) := by
        have h := Real.log_le_rpow_div (ε := (1 / 4 : ℝ)) (inv_nonneg.mpr hu_pos.le) (by norm_num)
        rw [Real.inv_rpow hu_pos.le, ← Real.rpow_neg hu_pos.le] at h
        linarith
      have hrpow_le : u ^ (-(1 / 4 : ℝ)) ≤ u ^ ((1 / 4 : ℝ) - 1) :=
        Real.rpow_le_rpow_of_exponent_ge hu_pos h1 (by norm_num)
      have hterm2 : 0 ≤ Real.exp (-u) * u ^ ((5 / 2 : ℝ) - 1) := by positivity
      calc Real.exp (-u) * |Real.log u|
          ≤ Real.exp (-u) * (4 * u ^ ((1 / 4 : ℝ) - 1)) := by
            rw [habs]
            exact mul_le_mul_of_nonneg_left (hle.trans (by linarith)) (Real.exp_pos _).le
        _ ≤ 4 * (Real.exp (-u) * u ^ ((1 / 4 : ℝ) - 1)) +
              Real.exp (-u) * u ^ ((5 / 2 : ℝ) - 1) := by linarith
    · push Not at h1
      have habs : |Real.log u| = Real.log u := abs_of_pos (Real.log_pos h1)
      have hle : Real.log u ≤ u := (Real.log_le_sub_one_of_pos hu_pos).trans (by linarith)
      have hpow : u ≤ u ^ ((5 / 2 : ℝ) - 1) := by
        calc u = u ^ (1 : ℝ) := (Real.rpow_one u).symm
          _ ≤ u ^ ((5 / 2 : ℝ) - 1) := Real.rpow_le_rpow_of_exponent_le h1.le (by norm_num)
      have hterm1 : 0 ≤ 4 * (Real.exp (-u) * u ^ ((1 / 4 : ℝ) - 1)) := by positivity
      calc Real.exp (-u) * |Real.log u|
          ≤ Real.exp (-u) * u ^ ((5 / 2 : ℝ) - 1) := by
            rw [habs]
            exact mul_le_mul_of_nonneg_left (hle.trans hpow) (Real.exp_pos _).le
        _ ≤ 4 * (Real.exp (-u) * u ^ ((1 / 4 : ℝ) - 1)) +
              Real.exp (-u) * u ^ ((5 / 2 : ℝ) - 1) := by linarith

private lemma integral_exp_neg_mul_log_eq_neg_gamma :
    ∫ u in Ioi (0 : ℝ), Real.exp (-u) * Real.log u = -Real.eulerMascheroniConstant := by
  let μ := volume.restrict (Ioi (0 : ℝ))
  let Fg : ℝ → ℝ → ℝ := fun s u => Real.exp (-u) * u ^ (s - 1)
  let Fg' : ℝ → ℝ → ℝ := fun s u => Real.exp (-u) * (u ^ (s - 1) * Real.log u)
  let bound : ℝ → ℝ := fun u =>
    4 * (Real.exp (-u) * u ^ ((1 / 4 : ℝ) - 1)) + Real.exp (-u) * u ^ ((5 / 2 : ℝ) - 1)
  have hbound_int : Integrable bound μ :=
    ((Real.GammaIntegral_convergent (by norm_num : (0 : ℝ) < 1 / 4)).const_mul 4).add
      (Real.GammaIntegral_convergent (by norm_num : (0 : ℝ) < 5 / 2))
  have hball : Metric.ball (1 : ℝ) (1 / 2) ∈ 𝓝 (1 : ℝ) := Metric.ball_mem_nhds 1 (by norm_num)
  have hF_meas : ∀ᶠ s in 𝓝 (1 : ℝ), AEStronglyMeasurable (Fg s) μ := by
    refine Eventually.of_forall fun s => ?_
    have hcont : ContinuousOn (Fg s) (Ioi 0) := by
      refine (Real.continuous_exp.comp continuous_neg).continuousOn.mul ?_
      intro u hu
      exact (continuousAt_id.rpow_const (Or.inl (ne_of_gt hu))).continuousWithinAt
    exact hcont.aestronglyMeasurable measurableSet_Ioi
  have hF_int : Integrable (Fg 1) μ := Real.GammaIntegral_convergent zero_lt_one
  have hF'_meas : AEStronglyMeasurable (Fg' 1) μ := by
    have hcont : ContinuousOn (Fg' 1) (Ioi 0) := by
      refine (Real.continuous_exp.comp continuous_neg).continuousOn.mul ?_
      refine ContinuousOn.mul ?_ ?_
      · intro u hu; exact (continuousAt_id.rpow_const (Or.inl (ne_of_gt hu))).continuousWithinAt
      · exact Real.continuousOn_log.mono (fun u hu => ne_of_gt hu)
    exact hcont.aestronglyMeasurable measurableSet_Ioi
  have h_bound : ∀ᵐ u ∂μ, ∀ s ∈ Metric.ball (1 : ℝ) (1 / 2), ‖Fg' s u‖ ≤ bound u := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu s hs
    have hu_pos : 0 < u := hu
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hs
    have hs_lo : -(1 / 2 : ℝ) < s - 1 := by linarith
    have hs_hi : s - 1 < 1 / 2 := by linarith
    dsimp only [Fg', bound]
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos (-u)),
      abs_of_pos (Real.rpow_pos_of_pos hu_pos _)]
    by_cases h1 : u ≤ 1
    · have hu_rpow : u ^ (s - 1) ≤ u ^ (-(1 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_ge hu_pos h1 hs_lo.le
      have habs : |Real.log u| = Real.log (u⁻¹) := by
        rw [abs_of_nonpos (Real.log_nonpos hu_pos.le h1), Real.log_inv]
      have hlog_le : |Real.log u| ≤ 4 * u ^ (-(1 / 4 : ℝ)) := by
        rw [habs]
        have h := Real.log_le_rpow_div (ε := (1 / 4 : ℝ)) (inv_nonneg.mpr hu_pos.le) (by norm_num)
        rw [Real.inv_rpow hu_pos.le, ← Real.rpow_neg hu_pos.le] at h
        linarith
      have hprod : u ^ (s - 1) * |Real.log u| ≤ 4 * u ^ ((1 / 4 : ℝ) - 1) := by
        calc u ^ (s - 1) * |Real.log u|
            ≤ u ^ (-(1 / 2 : ℝ)) * (4 * u ^ (-(1 / 4 : ℝ))) :=
              mul_le_mul hu_rpow hlog_le (abs_nonneg _) (Real.rpow_nonneg hu_pos.le _)
          _ = 4 * (u ^ (-(1 / 2 : ℝ)) * u ^ (-(1 / 4 : ℝ))) := by ring
          _ = 4 * u ^ (-(1 / 2 : ℝ) + -(1 / 4 : ℝ)) := by rw [← Real.rpow_add hu_pos]
          _ = 4 * u ^ ((1 / 4 : ℝ) - 1) := by norm_num
      have hterm2 : 0 ≤ Real.exp (-u) * u ^ ((5 / 2 : ℝ) - 1) := by positivity
      calc Real.exp (-u) * (u ^ (s - 1) * |Real.log u|)
          ≤ Real.exp (-u) * (4 * u ^ ((1 / 4 : ℝ) - 1)) :=
            mul_le_mul_of_nonneg_left hprod (Real.exp_pos _).le
        _ ≤ 4 * (Real.exp (-u) * u ^ ((1 / 4 : ℝ) - 1)) +
              Real.exp (-u) * u ^ ((5 / 2 : ℝ) - 1) := by linarith
    · push Not at h1
      have hu_rpow : u ^ (s - 1) ≤ u ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le h1.le hs_hi.le
      have hlog_le : |Real.log u| ≤ u := by
        rw [abs_of_pos (Real.log_pos h1)]
        exact (Real.log_le_sub_one_of_pos hu_pos).trans (by linarith)
      have hprod : u ^ (s - 1) * |Real.log u| ≤ u ^ ((5 / 2 : ℝ) - 1) := by
        calc u ^ (s - 1) * |Real.log u|
            ≤ u ^ (1 / 2 : ℝ) * u :=
              mul_le_mul hu_rpow hlog_le (abs_nonneg _) (Real.rpow_nonneg hu_pos.le _)
          _ = u ^ (1 / 2 : ℝ) * u ^ (1 : ℝ) := by rw [Real.rpow_one]
          _ = u ^ ((1 / 2 : ℝ) + 1) := by rw [← Real.rpow_add hu_pos]
          _ = u ^ ((5 / 2 : ℝ) - 1) := by norm_num
      have hterm1 : 0 ≤ 4 * (Real.exp (-u) * u ^ ((1 / 4 : ℝ) - 1)) := by positivity
      calc Real.exp (-u) * (u ^ (s - 1) * |Real.log u|)
          ≤ Real.exp (-u) * u ^ ((5 / 2 : ℝ) - 1) :=
            mul_le_mul_of_nonneg_left hprod (Real.exp_pos _).le
        _ ≤ 4 * (Real.exp (-u) * u ^ ((1 / 4 : ℝ) - 1)) +
              Real.exp (-u) * u ^ ((5 / 2 : ℝ) - 1) := by linarith
  have h_diff : ∀ᵐ u ∂μ, ∀ s ∈ Metric.ball (1 : ℝ) (1 / 2),
      HasDerivAt (Fg · u) (Fg' s u) s := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu s _
    have h1 : HasDerivAt (fun s : ℝ => s - 1) 1 s := (hasDerivAt_id s).sub_const 1
    have h2 := (Real.hasStrictDerivAt_const_rpow hu (s - 1)).hasDerivAt.comp s h1
    rw [mul_one] at h2
    exact h2.const_mul (Real.exp (-u))
  have hderiv := (hasDerivAt_integral_of_dominated_loc_of_deriv_le hball hF_meas hF_int hF'_meas
    h_bound hbound_int h_diff).2
  have heq_nhds : (fun s : ℝ => ∫ u, Fg s u ∂μ) =ᶠ[𝓝 (1 : ℝ)] Real.Gamma := by
    filter_upwards [Ioi_mem_nhds zero_lt_one] with s hs
    exact (Real.Gamma_eq_integral hs).symm
  have hderiv_Gamma : HasDerivAt Real.Gamma (∫ u, Fg' 1 u ∂μ) 1 :=
    hderiv.congr_of_eventuallyEq heq_nhds.symm
  have hval := hderiv_Gamma.unique Real.hasDerivAt_Gamma_one
  have hsimp : ∫ u, Fg' 1 u ∂μ = ∫ u in Ioi (0 : ℝ), Real.exp (-u) * Real.log u := by
    simp [Fg', μ]
  linarith

/- ### Step 4B: Dirichlet series `G(δ)` via Euler product and zeta asymptotics -/

private noncomputable def G (δ : ℝ) : ℝ :=
  ∑' n : ℕ, c n * (n : ℝ) ^ (-δ)

private lemma summable_neg_log_one_sub_prime {δ : ℝ} (hδ : 0 < δ) :
    Summable (fun p : Nat.Primes => -Real.log (1 - (p : ℝ) ^ (-(1 + δ)))) := by
  have hnat : Summable (fun n : ℕ => 2 * (1 / (n : ℝ) ^ (1 + δ))) :=
    ((Real.summable_one_div_nat_rpow (p := 1 + δ)).mpr (by linarith)).mul_left 2
  have hpr : Summable (fun p : Nat.Primes => 2 * (1 / ((p : ℕ) : ℝ) ^ (1 + δ))) :=
    hnat.subtype _
  refine Summable.of_nonneg_of_le (fun p => ?_) (fun p => ?_) hpr
  · have hp1 : (1 : ℝ) < (p : ℕ) := by exact_mod_cast p.prop.one_lt
    have hr_pos : 0 < ((p : ℕ) : ℝ) ^ (-(1 + δ)) := Real.rpow_pos_of_pos (by linarith) _
    have hr_lt : ((p : ℕ) : ℝ) ^ (-(1 + δ)) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
    exact neg_nonneg.mpr (Real.log_nonpos (by linarith) (by linarith))
  · have hp2 : (2 : ℝ) ≤ (p : ℕ) := by exact_mod_cast p.prop.two_le
    have hr_pos : 0 < ((p : ℕ) : ℝ) ^ (-(1 + δ)) := Real.rpow_pos_of_pos (by linarith) _
    have hr_le : ((p : ℕ) : ℝ) ^ (-(1 + δ)) ≤ 1 / 2 := by
      calc ((p : ℕ) : ℝ) ^ (-(1 + δ))
          ≤ (2 : ℝ) ^ (-(1 + δ)) :=
            Real.rpow_le_rpow_of_nonpos (by norm_num) hp2 (by linarith)
        _ ≤ (2 : ℝ) ^ (-1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = 1 / 2 := by norm_num
    have hlog : -Real.log (1 - ((p : ℕ) : ℝ) ^ (-(1 + δ))) ≤
        2 * ((p : ℕ) : ℝ) ^ (-(1 + δ)) := by
      rw [← Real.log_inv]
      have h := Real.log_le_sub_one_of_pos (inv_pos.mpr (by linarith : 0 < 1 - ((p : ℕ) : ℝ) ^ (-(1 + δ))))
      have hinv : (1 - ((p : ℕ) : ℝ) ^ (-(1 + δ)))⁻¹ - 1 ≤ 2 * ((p : ℕ) : ℝ) ^ (-(1 + δ)) := by
        rw [inv_eq_one_div, div_sub_one (by linarith : 1 - ((p : ℕ) : ℝ) ^ (-(1 + δ)) ≠ 0)]
        have hnum : 1 - (1 - ((p : ℕ) : ℝ) ^ (-(1 + δ))) = ((p : ℕ) : ℝ) ^ (-(1 + δ)) := by ring
        rw [hnum, div_le_iff₀ (by linarith : 0 < 1 - ((p : ℕ) : ℝ) ^ (-(1 + δ)))]
        nlinarith
      linarith
    refine hlog.trans_eq ?_
    rw [Real.rpow_neg (by linarith), ← one_div]

private lemma summable_c_mul_rpow {δ : ℝ} (hδ : 0 < δ) :
    Summable (fun n : ℕ => c n * (n : ℝ) ^ (-δ)) ∧
      G δ = ∑' p : Nat.Primes, -Real.log (1 - (p : ℝ) ^ (-(1 + δ))) := by
  let g : Nat.Primes × ℕ → ℝ := fun pk =>
    (((pk.1 : ℕ) : ℝ) ^ (-(1 + δ))) ^ (pk.2 + 1) / ((pk.2 : ℝ) + 1)
  have hg_nonneg : 0 ≤ g := fun pk => by
    dsimp only [g]
    have hp_pos : (0 : ℝ) < (pk.1 : ℕ) := by exact_mod_cast pk.1.prop.pos
    positivity
  have hg_inner : ∀ p : Nat.Primes,
      HasSum (fun k : ℕ => g (p, k)) (-Real.log (1 - ((p : ℕ) : ℝ) ^ (-(1 + δ)))) := by
    intro p
    have hp1 : (1 : ℝ) < (p : ℕ) := by exact_mod_cast p.prop.one_lt
    have hr_pos : 0 < ((p : ℕ) : ℝ) ^ (-(1 + δ)) := Real.rpow_pos_of_pos (by linarith) _
    have hr_lt : ((p : ℕ) : ℝ) ^ (-(1 + δ)) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
    have hhs := Real.hasSum_pow_div_log_of_abs_lt_one (x := ((p : ℕ) : ℝ) ^ (-(1 + δ)))
      (by rw [abs_of_pos hr_pos]; exact hr_lt)
    exact hhs.congr_fun fun k => by simp [g]
  have hg_summable : Summable g := by
    rw [summable_prod_of_nonneg hg_nonneg]
    refine ⟨fun p => (hg_inner p).summable, ?_⟩
    have hts : (fun p : Nat.Primes => ∑' k : ℕ, g (p, k)) =
        fun p : Nat.Primes => -Real.log (1 - ((p : ℕ) : ℝ) ^ (-(1 + δ))) :=
      funext fun p => (hg_inner p).tsum_eq
    rw [hts]
    exact summable_neg_log_one_sub_prime hδ
  have htsum_g : ∑' pk : Nat.Primes × ℕ, g pk =
      ∑' p : Nat.Primes, -Real.log (1 - ((p : ℕ) : ℝ) ^ (-(1 + δ))) := by
    rw [hg_summable.tsum_prod]
    exact tsum_congr fun p => (hg_inner p).tsum_eq
  let emb : Nat.Primes × ℕ → ℕ := fun pk => (pk.1 : ℕ) ^ (pk.2 + 1)
  have hemb_inj : Function.Injective emb := by
    rintro ⟨p₁, k₁⟩ ⟨p₂, k₂⟩ h
    have ⟨hp, hk⟩ := prime_pow_inj p₁.prop p₂.prop h
    exact Prod.ext (Subtype.ext hp) hk
  have hval : ∀ pk : Nat.Primes × ℕ, c (emb pk) * ((emb pk : ℕ) : ℝ) ^ (-δ) = g pk := by
    rintro ⟨p, k⟩
    dsimp only [emb, g]
    rw [c_prime_pow p.prop k]
    have hp_pos : (0 : ℝ) < (p : ℕ) := by exact_mod_cast p.prop.pos
    rw [Nat.cast_pow, ← Real.rpow_natCast ((p : ℕ) : ℝ), ← Real.rpow_mul hp_pos.le,
      ← Real.rpow_natCast (((p : ℕ) : ℝ) ^ (-(1 + δ))), ← Real.rpow_mul hp_pos.le,
      one_div, inv_pow, ← Real.rpow_natCast ((p : ℕ) : ℝ), ← Real.rpow_neg hp_pos.le,
      div_mul_eq_mul_div, ← Real.rpow_add hp_pos]
    congr 2
    push_cast
    ring
  have hsupp : ∀ n : ℕ, n ∉ Set.range emb → c n * (n : ℝ) ^ (-δ) = 0 := by
    intro n hn
    have hnot : ¬ IsPrimePow n := by
      intro hpp
      obtain ⟨p, m, hp, hm, rfl⟩ := (isPrimePow_nat_iff n).mp hpp
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
      exact hn ⟨⟨⟨p, hp⟩, k⟩, rfl⟩
    rw [c_eq_zero_of_not_isPrimePow hnot, zero_mul]
  have hsum_nat : Summable (fun n : ℕ => c n * (n : ℝ) ^ (-δ)) := by
    have hcomp : Summable ((fun n : ℕ => c n * (n : ℝ) ^ (-δ)) ∘ emb) := by
      simpa only [Function.comp_def, hval] using hg_summable
    exact (hemb_inj.summable_iff hsupp).mp hcomp
  refine ⟨hsum_nat, ?_⟩
  unfold G
  rw [← htsum_g, ← hemb_inj.tsum_eq (Function.support_subset_iff'.mpr hsupp)]
  exact tsum_congr hval

private lemma G_eq_log_riemannZeta_re {δ : ℝ} (hδ : 0 < δ) :
    G δ = Real.log (riemannZeta ((1 + δ : ℝ) : ℂ)).re := by
  rw [(summable_c_mul_rpow hδ).2]
  have hs : 1 < (((1 + δ : ℝ) : ℂ)).re := by simp [hδ]
  have heuler := riemannZeta_eulerProduct_exp_log hs
  have hterm : ∀ p : Nat.Primes,
      -Complex.log (1 - (p : ℂ) ^ (-((1 + δ : ℝ) : ℂ))) =
        ((-Real.log (1 - ((p : ℕ) : ℝ) ^ (-(1 + δ))) : ℝ) : ℂ) := by
    intro p
    have hp1 : (1 : ℝ) < (p : ℕ) := by exact_mod_cast p.prop.one_lt
    have hp_pos : (0 : ℝ) < (p : ℕ) := by linarith
    have hr_lt : ((p : ℕ) : ℝ) ^ (-(1 + δ)) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
    have h1sub : 0 < 1 - ((p : ℕ) : ℝ) ^ (-(1 + δ)) := by linarith
    have hcpow : (p : ℂ) ^ (-((1 + δ : ℝ) : ℂ)) = ((((p : ℕ) : ℝ) ^ (-(1 + δ)) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_neg, Complex.ofReal_cpow hp_pos.le]
      simp
    rw [hcpow, ← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_log h1sub.le,
      Complex.ofReal_neg]
  simp_rw [hterm] at heuler
  rw [← Complex.ofReal_tsum, ← Complex.ofReal_exp] at heuler
  have hre : Real.exp (∑' p : Nat.Primes, -Real.log (1 - ((p : ℕ) : ℝ) ^ (-(1 + δ)))) =
      (riemannZeta ((1 + δ : ℝ) : ℂ)).re := by
    rw [← heuler, Complex.ofReal_re]
  rw [← hre, Real.log_exp]

private lemma tendsto_G_add_log_zero :
    Tendsto (fun δ : ℝ => G δ + Real.log δ) (𝓝[>] 0) (𝓝 0) := by
  have hzeta :=
    Asymptotics.IsLittleO.tendsto_div_nhds_zero log_riemannZeta_add_log_sub_isLittleO_ofReal
  simp only [div_one] at hzeta
  have hmap : Tendsto (fun δ : ℝ => 1 + δ) (𝓝[>] (0 : ℝ)) (𝓝[>] (1 : ℝ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · simpa using (tendsto_const_nhds (x := (1 : ℝ))).add
        (continuousWithinAt_id (s := Ioi (0 : ℝ)) (x := 0)).tendsto
    · filter_upwards [self_mem_nhdsWithin] with δ hδ
      simp only [Set.mem_Ioi] at hδ ⊢; linarith
  have hcomp := hzeta.comp hmap
  refine hcomp.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  have hδ_pos : 0 < δ := hδ
  simp only [Function.comp_apply, add_sub_cancel_left]
  rw [G_eq_log_riemannZeta_re hδ_pos]

/- ### Step 4C: Abel summation and change of variables for `G(δ)` -/

private lemma G_eq_mul_integral_F {δ : ℝ} (hδ : 0 < δ) {L : ℝ}
    (hL : Tendsto (fun y : ℝ => F y - Real.log (Real.log y)) atTop (𝓝 L)) :
    G δ = δ * ∫ t in Ioi (2 : ℝ), F t * t ^ (-δ - 1) := by
  have hF_bigO : F =O[atTop] Real.log := by
    have hF_ev : ∀ᶠ t : ℝ in atTop, |F t| ≤ |L| + 1 + Real.log t := by
      have hclose := hL.eventually (Metric.ball_mem_nhds L zero_lt_one)
      filter_upwards [hclose, eventually_ge_atTop (3 : ℝ)] with t ht ht3
      rw [Real.dist_eq] at ht
      have hF_nonneg := F_nonneg t
      rw [abs_of_nonneg hF_nonneg]
      have hlt : Real.log t > 1 := by
        have := Real.exp_one_lt_d9
        exact (Real.lt_log_iff_exp_lt (by linarith)).mpr (by linarith)
      have hll : Real.log (Real.log t) ≤ Real.log t :=
        (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
      have habsL : L ≤ |L| := le_abs_self L
      linarith [abs_lt.mp ht]
    rw [Asymptotics.isBigO_iff]
    refine ⟨|L| + 2, ?_⟩
    filter_upwards [hF_ev, eventually_ge_atTop (3 : ℝ)] with t ht ht3
    have hlt : 1 ≤ Real.log t := by
      have := Real.exp_one_lt_d9
      exact ((Real.lt_log_iff_exp_lt (by linarith)).mpr (by linarith)).le
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (by linarith : 0 < Real.log t)]
    nlinarith [abs_nonneg L]
  let f : ℝ → ℝ := fun t => t ^ (-δ)
  have hf_deriv : ∀ t : ℝ, 0 < t → HasDerivAt f (-δ * t ^ (-δ - 1)) t := fun t ht =>
    Real.hasDerivAt_rpow_const (Or.inl ht.ne')
  have hf_diff : ∀ t ∈ Ici (1 : ℝ), DifferentiableAt ℝ f t := fun t ht =>
    (hf_deriv t (lt_of_lt_of_le zero_lt_one ht)).differentiableAt
  have hf_deriv_eq : ∀ t ∈ Ici (1 : ℝ), deriv f t = -δ * t ^ (-δ - 1) := fun t ht =>
    (hf_deriv t (lt_of_lt_of_le zero_lt_one ht)).deriv
  have hf_int : LocallyIntegrableOn (deriv f) (Ici 1) := by
    have hcont : ContinuousOn (fun t : ℝ => -δ * t ^ (-δ - 1)) (Ici 1) := by
      refine continuousOn_const.mul ?_
      intro t ht
      exact (continuousAt_id.rpow_const (Or.inl (lt_of_lt_of_le zero_lt_one ht).ne')).continuousWithinAt
    exact (hcont.congr hf_deriv_eq).locallyIntegrableOn measurableSet_Ici
  have hF_eq_sum : ∀ t : ℝ, ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k = F t := fun t => (F_eq_sum_c t).symm
  have h_lim : Tendsto (fun n : ℕ => f n * ∑ k ∈ Finset.Icc 0 n, c k) atTop (𝓝 0) := by
    have h1 : (fun t : ℝ => f t * F t) =o[atTop] (fun _ : ℝ => (1 : ℝ)) := by
      have hlog_o : Real.log =o[atTop] (fun t : ℝ => t ^ δ) := isLittleO_log_rpow_atTop hδ
      have hprod : (fun t : ℝ => f t * F t) =o[atTop] (fun t : ℝ => f t * t ^ δ) :=
        (Asymptotics.isBigO_refl f atTop).mul_isLittleO (hF_bigO.trans_isLittleO hlog_o)
      refine hprod.congr' EventuallyEq.rfl ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      dsimp only [f]
      rw [← Real.rpow_add ht, neg_add_cancel, Real.rpow_zero]
    have h2 : Tendsto (fun t : ℝ => f t * F t) atTop (𝓝 0) := by
      simpa using h1.tendsto_div_nhds_zero
    have h3 := h2.comp tendsto_natCast_atTop_atTop
    refine h3.congr fun n => ?_
    simp only [Function.comp_apply, F_eq_sum_c, Nat.floor_natCast]
  have hg_dom : (fun t : ℝ => deriv f t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k) =O[atTop]
      (fun t : ℝ => t ^ (-1 - δ / 2)) := by
    have hlog_o : Real.log =o[atTop] (fun t : ℝ => t ^ (δ / 2)) :=
      isLittleO_log_rpow_atTop (half_pos hδ)
    have hF_o : F =O[atTop] (fun t : ℝ => t ^ (δ / 2)) :=
      (hF_bigO.trans_isLittleO hlog_o).isBigO
    have hmul : (fun t : ℝ => (-δ * t ^ (-δ - 1)) * F t) =O[atTop]
        (fun t : ℝ => (-δ * t ^ (-δ - 1)) * t ^ (δ / 2)) :=
      (Asymptotics.isBigO_refl _ atTop).mul hF_o
    have hmul' : (fun t : ℝ => (-δ * t ^ (-δ - 1)) * t ^ (δ / 2)) =O[atTop]
        (fun t : ℝ => t ^ (-1 - δ / 2)) := by
      refine (Asymptotics.isBigO_const_mul_self (-δ) _ atTop).congr' ?_ EventuallyEq.rfl
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      rw [mul_assoc, ← Real.rpow_add ht]
      congr 2; ring
    refine (hmul.trans hmul').congr' ?_ EventuallyEq.rfl
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    rw [hf_deriv_eq t ht, hF_eq_sum t]
  have hg_int : IntegrableAtFilter (fun t : ℝ => t ^ (-1 - δ / 2)) atTop :=
    ⟨Ioi 1, Ioi_mem_atTop 1, integrableOn_Ioi_rpow_of_lt (by linarith : -1 - δ / 2 < -1) zero_lt_one⟩
  have habel := tendsto_sum_mul_atTop_nhds_one_sub_integral₀ c c_zero hf_diff hf_int
    h_lim hg_dom hg_int
  have hsum_tendsto : Tendsto (fun n : ℕ => ∑ k ∈ Finset.Icc 0 n, f k * c k) atTop (𝓝 (G δ)) := by
    have hsum := (summable_c_mul_rpow hδ).1.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
    refine hsum.congr fun n => ?_
    simp only [Function.comp_apply, Nat.range_eq_Icc_zero_sub_one _ (Nat.succ_ne_zero n)]
    refine Finset.sum_congr rfl fun k _ => mul_comm _ _
  have heq := tendsto_nhds_unique hsum_tendsto habel
  rw [zero_sub] at heq
  have hint_eq : -(∫ t in Ioi (1 : ℝ), deriv f t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k) =
      δ * ∫ t in Ioi (2 : ℝ), F t * t ^ (-δ - 1) := by
    have hcongr : ∫ t in Ioi (1 : ℝ), deriv f t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k =
        ∫ t in Ioi (1 : ℝ), (-δ) * (F t * t ^ (-δ - 1)) := by
      refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
      rw [hf_deriv_eq t (Ioi_subset_Ici_self ht), hF_eq_sum t]
      ring
    rw [hcongr, integral_const_mul, neg_mul, neg_neg]
    congr 1
    have hsplit : Ioi (1 : ℝ) = Ioc (1 : ℝ) 2 ∪ Ioi (2 : ℝ) := (Ioc_union_Ioi_eq_Ioi (by norm_num)).symm
    have hint1 : IntegrableOn (fun t : ℝ => F t * t ^ (-δ - 1)) (Ioi 1) := by
      have hloc := (locallyIntegrableOn_mul_sum_Icc c zero_le_one hf_int).integrableOn_of_isBigO_atTop
        hg_dom hg_int
      rw [integrableOn_Ici_iff_integrableOn_Ioi] at hloc
      have hloc' : IntegrableOn (fun t : ℝ => (-δ) * (F t * t ^ (-δ - 1))) (Ioi 1) :=
        hloc.congr_fun (fun t ht => by
          dsimp only
          rw [hf_deriv_eq t (Ioi_subset_Ici_self ht), hF_eq_sum t]
          ring) measurableSet_Ioi
      have hinv : IntegrableOn (fun t : ℝ => (-δ)⁻¹ * ((-δ) * (F t * t ^ (-δ - 1)))) (Ioi 1) :=
        hloc'.const_mul (-δ)⁻¹
      refine hinv.congr_fun (fun t _ => ?_) measurableSet_Ioi
      dsimp only
      field_simp [hδ.ne']
    rw [hsplit, setIntegral_union (Ioc_disjoint_Ioi_same) measurableSet_Ioi
      (hint1.mono_set (Ioc_subset_Ioi_self)) (hint1.mono_set (Ioi_subset_Ioi (by norm_num)))]
    have hzero : ∫ t in Ioc (1 : ℝ) 2, F t * t ^ (-δ - 1) = 0 := by
      rw [setIntegral_congr_set Ioo_ae_eq_Ioc.symm]
      refine setIntegral_eq_zero_of_forall_eq_zero fun t ht => ?_
      rw [F_eq_zero_of_lt_two ht.2, zero_mul]
    rw [hzero, zero_add]
  exact heq.trans hint_eq

private lemma integral_Ioi_rpow_neg_sub_one {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ) :
    δ * ∫ t in Ioi a, t ^ (-δ - 1) = a ^ (-δ) := by
  have hint := integral_Ioi_rpow_of_lt (a := -δ - 1) (c := a) (by linarith) ha
  rw [hint]
  have h1 : -δ - 1 + 1 = -δ := by ring
  rw [h1]
  field_simp [hδ.ne']

private lemma tendsto_log_log_piece :
    Tendsto (fun δ : ℝ =>
      δ * (∫ t in Ioi (2 : ℝ), Real.log (Real.log t) * t ^ (-δ - 1)) + Real.log δ)
      (𝓝[>] 0) (𝓝 (-Real.eulerMascheroniConstant)) := by
  have hrew : ∀ δ : ℝ, 0 < δ →
      δ * (∫ t in Ioi (2 : ℝ), Real.log (Real.log t) * t ^ (-δ - 1)) + Real.log δ =
        (∫ u in Ioi (δ * Real.log 2), Real.exp (-u) * Real.log u) +
          Real.log δ * (1 - (2 : ℝ) ^ (-δ)) := by
    intro δ hδ
    have hstep1 : ∫ t in Ioi (2 : ℝ), Real.log (Real.log t) * t ^ (-δ - 1) =
        ∫ y in Ioi (Real.log 2), Real.log y * Real.exp (-δ * y) := by
      have hcongr : ∫ t in Ioi (2 : ℝ), Real.log (Real.log t) * t ^ (-δ - 1) =
          ∫ t in Ioi (2 : ℝ), t⁻¹ • (Real.log (Real.log t) * Real.exp (-δ * Real.log t)) := by
        refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
        have ht_pos : 0 < t := lt_trans (by norm_num) ht
        rw [smul_eq_mul, Real.rpow_def_of_pos ht_pos]
        have hexp : Real.exp (Real.log t * (-δ - 1)) = t⁻¹ * Real.exp (-δ * Real.log t) := by
          rw [show Real.log t * (-δ - 1) = -Real.log t + (-δ * Real.log t) by ring,
            Real.exp_add, Real.exp_neg, Real.exp_log ht_pos]
        rw [hexp]; ring
      rw [hcongr]
      exact integral_comp_log_Ioi (fun y => Real.log y * Real.exp (-δ * y)) (by norm_num)
    rw [hstep1]
    have hstep2 : δ * ∫ y in Ioi (Real.log 2), Real.log y * Real.exp (-δ * y) =
        ∫ u in Ioi (δ * Real.log 2), (Real.log u - Real.log δ) * Real.exp (-u) := by
      have hcongr : ∫ y in Ioi (Real.log 2), Real.log y * Real.exp (-δ * y) =
          ∫ y in Ioi (Real.log 2), (Real.log (δ * y) - Real.log δ) * Real.exp (-(δ * y)) := by
        refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
        have hy_pos : 0 < y := lt_trans (Real.log_pos (by norm_num)) hy
        rw [Real.log_mul hδ.ne' hy_pos.ne']
        ring_nf
      rw [hcongr]
      simpa [smul_eq_mul] using
        integral_comp_mul_left_Ioi' (fun u => (Real.log u - Real.log δ) * Real.exp (-u))
          (Real.log 2) hδ
    rw [hstep2]
    have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hint_a : IntegrableOn (fun u : ℝ => Real.exp (-u) * Real.log u) (Ioi (δ * Real.log 2)) :=
      integrableOn_log_mul_exp_neg.mono_set (Ioi_subset_Ioi (mul_pos hδ hlog2_pos).le)
    have hint_b : IntegrableOn (fun u : ℝ => Real.log δ * Real.exp (-u)) (Ioi (δ * Real.log 2)) :=
      ((integrableOn_exp_neg_Ioi (δ * Real.log 2)).const_mul (Real.log δ))
    have hsplit : ∫ u in Ioi (δ * Real.log 2), (Real.log u - Real.log δ) * Real.exp (-u) =
        (∫ u in Ioi (δ * Real.log 2), Real.exp (-u) * Real.log u) -
          Real.log δ * (∫ u in Ioi (δ * Real.log 2), Real.exp (-u)) := by
      have hcongr : ∀ u : ℝ, (Real.log u - Real.log δ) * Real.exp (-u) =
          Real.exp (-u) * Real.log u - Real.log δ * Real.exp (-u) := fun u => by ring
      simp_rw [hcongr]
      rw [integral_sub hint_a hint_b, integral_const_mul]
    rw [hsplit]
    have hexp_int : ∫ u in Ioi (δ * Real.log 2), Real.exp (-u) = (2 : ℝ) ^ (-δ) := by
      rw [integral_exp_neg_Ioi (δ * Real.log 2), Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
      congr 1; ring
    rw [hexp_int]
    ring
  -- Part 1: `∫_{δ log 2}^∞ exp (-u) log u → ∫_0^∞ exp (-u) log u = -γ`
  have hpart1 : Tendsto (fun δ : ℝ => ∫ u in Ioi (δ * Real.log 2), Real.exp (-u) * Real.log u)
      (𝓝[>] 0) (𝓝 (-Real.eulerMascheroniConstant)) := by
    rw [← integral_exp_neg_mul_log_eq_neg_gamma]
    let μ := volume.restrict (Ioi (0 : ℝ))
    have heq_ind : ∀ δ : ℝ, 0 < δ →
        ∫ u in Ioi (δ * Real.log 2), Real.exp (-u) * Real.log u =
          ∫ u, (Ioi (δ * Real.log 2)).indicator (fun u => Real.exp (-u) * Real.log u) u ∂μ := by
      intro δ hδ
      rw [integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
        inter_eq_self_of_subset_left (Ioi_subset_Ioi (mul_pos hδ (Real.log_pos (by norm_num))).le)]
    have hdom : Tendsto (fun δ : ℝ =>
        ∫ u, (Ioi (δ * Real.log 2)).indicator (fun u => Real.exp (-u) * Real.log u) u ∂μ)
        (𝓝[>] 0) (𝓝 (∫ u, Real.exp (-u) * Real.log u ∂μ)) := by
      refine tendsto_integral_filter_of_dominated_convergence
        (bound := fun u => ‖Real.exp (-u) * Real.log u‖) ?_ ?_ ?_ ?_
      · refine Eventually.of_forall fun δ => ?_
        exact integrableOn_log_mul_exp_neg.aestronglyMeasurable.indicator measurableSet_Ioi
      · refine Eventually.of_forall fun δ => Eventually.of_forall fun u => ?_
        by_cases hu : u ∈ Ioi (δ * Real.log 2)
        · simp [hu]
        · simp only [Set.indicator_of_notMem hu, norm_zero, norm_nonneg]
      · exact integrableOn_log_mul_exp_neg.norm
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
        have hu_pos : 0 < u := hu
        have hlt : Tendsto (fun δ : ℝ => δ * Real.log 2) (𝓝[>] 0) (𝓝 0) := by
          have h := ((continuousWithinAt_id (s := Ioi (0 : ℝ)) (x := 0)).mul_const (Real.log 2)).tendsto
          simpa using h
        have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ * Real.log 2 < u := hlt.eventually (gt_mem_nhds hu_pos)
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [hev] with δ hδu
        exact (Set.indicator_of_mem hδu (fun u => Real.exp (-u) * Real.log u)).symm
    refine hdom.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with δ hδ using (heq_ind δ hδ).symm
  -- Part 2: `log δ * (1 - 2 ^ (-δ)) → 0` as `δ → 0⁺`
  have hpart2 : Tendsto (fun δ : ℝ => Real.log δ * (1 - (2 : ℝ) ^ (-δ))) (𝓝[>] 0) (𝓝 0) := by
    have hmul_log : Tendsto (fun δ : ℝ => δ * Real.log δ) (𝓝[>] 0) (𝓝 0) := by
      have h := tendsto_log_mul_rpow_nhdsGT_zero zero_lt_one
      refine h.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with δ _
      rw [Real.rpow_one, mul_comm]
    have hbound : ∀ᶠ δ in 𝓝[>] (0 : ℝ),
        ‖Real.log δ * (1 - (2 : ℝ) ^ (-δ))‖ ≤ Real.log 2 * |δ * Real.log δ| := by
      filter_upwards [self_mem_nhdsWithin] with δ hδ
      have hδ_pos : 0 < δ := hδ
      have h1 : 0 ≤ 1 - (2 : ℝ) ^ (-δ) := by
        have : (2 : ℝ) ^ (-δ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
        linarith
      have h2 : 1 - (2 : ℝ) ^ (-δ) ≤ δ * Real.log 2 := by
        rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
        have := Real.add_one_le_exp (-(Real.log 2 * δ))
        have hrew : Real.log 2 * -δ = -(Real.log 2 * δ) := by ring
        rw [hrew]; linarith
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h1, abs_mul, abs_of_pos hδ_pos]
      calc |Real.log δ| * (1 - (2 : ℝ) ^ (-δ))
          ≤ |Real.log δ| * (δ * Real.log 2) := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
        _ = Real.log 2 * (δ * |Real.log δ|) := by ring
    refine squeeze_zero_norm' hbound ?_
    simpa using (hmul_log.abs).const_mul (Real.log 2)
  have hsum := hpart1.add hpart2
  rw [add_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with δ hδ using (hrew δ hδ).symm

private lemma measurable_F : Measurable F := by
  have hF : F = (fun N : ℕ => ∑ n ∈ Finset.Icc 0 N, c n) ∘ (fun x : ℝ => ⌊x⌋₊) := by
    funext x
    exact F_eq_sum_c x
  rw [hF]
  exact (measurable_of_countable _).comp Nat.measurable_floor

private lemma tendsto_error_piece {L : ℝ}
    (hL : Tendsto (fun y : ℝ => F y - Real.log (Real.log y)) atTop (𝓝 L)) :
    Tendsto (fun δ : ℝ =>
      δ * ∫ t in Ioi (2 : ℝ), (F t - Real.log (Real.log t) - L) * t ^ (-δ - 1))
      (𝓝[>] 0) (𝓝 0) := by
  let E : ℝ → ℝ := fun t => F t - Real.log (Real.log t) - L
  have hE_zero : Tendsto E atTop (𝓝 0) := by
    simpa [E] using hL.sub_const L
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := (Metric.tendsto_atTop.mp hE_zero) (ε / 2) (half_pos hε)
  set T : ℝ := max 2 T₀
  have hT2 : 2 ≤ T := le_max_left 2 T₀
  have hT_pos : 0 < T := by linarith
  have hE_tail : ∀ t : ℝ, T ≤ t → |E t| ≤ ε / 2 := fun t ht => by
    have := hT₀ t ((le_max_right 2 T₀).trans ht)
    rw [Real.dist_eq, sub_zero] at this
    exact this.le
  set B : ℝ := F T + |Real.log (Real.log 2)| + |Real.log (Real.log T)| + |L|
  have hB_nonneg : 0 ≤ B := by
    have := F_nonneg T
    positivity
  have hE_bdd : ∀ t ∈ Ioc (2 : ℝ) T, |E t| ≤ B := by
    intro t ht
    have hFt_nonneg : 0 ≤ F t := F_nonneg t
    have hFt_le : F t ≤ F T := F_mono ht.2
    have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hll_lo : Real.log (Real.log 2) ≤ Real.log (Real.log t) :=
      Real.log_le_log hlog2_pos (Real.log_le_log (by norm_num) ht.1.le)
    have hll_hi : Real.log (Real.log t) ≤ Real.log (Real.log T) :=
      Real.log_le_log (Real.log_pos (by linarith [ht.1])) (Real.log_le_log (by linarith [ht.1]) ht.2)
    have habs_ll : |Real.log (Real.log t)| ≤ |Real.log (Real.log 2)| + |Real.log (Real.log T)| := by
      rw [abs_le]
      constructor
      · linarith [neg_abs_le (Real.log (Real.log 2)), abs_nonneg (Real.log (Real.log T))]
      · linarith [le_abs_self (Real.log (Real.log T)), abs_nonneg (Real.log (Real.log 2))]
    dsimp only [E, B]
    calc |F t - Real.log (Real.log t) - L|
        ≤ |F t| + |Real.log (Real.log t)| + |L| := by
          linarith [abs_sub (F t - Real.log (Real.log t)) L, abs_sub (F t) (Real.log (Real.log t))]
      _ ≤ F T + (|Real.log (Real.log 2)| + |Real.log (Real.log T)|) + |L| := by
          rw [abs_of_nonneg hFt_nonneg]; linarith
      _ = F T + |Real.log (Real.log 2)| + |Real.log (Real.log T)| + |L| := by ring
  set δ₀ : ℝ := ε / (2 * (B * (T - 2) + 1))
  have hδ₀_pos : 0 < δ₀ := by
    have : 0 ≤ B * (T - 2) := mul_nonneg hB_nonneg (by linarith)
    positivity
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hδ₀_pos)] with δ hδ hδ_lt
  have hδ_pos : 0 < δ := hδ
  rw [Real.dist_eq, sub_zero]
  have hE_meas : AEStronglyMeasurable (fun t : ℝ => E t * t ^ (-δ - 1)) (volume.restrict (Ioi 2)) := by
    have hll_meas : Measurable (fun t : ℝ => Real.log (Real.log t)) :=
      Real.measurable_log.comp Real.measurable_log
    have hpow_meas : Measurable (fun t : ℝ => t ^ (-δ - 1)) :=
      measurable_id.pow_const _
    exact (((measurable_F.sub hll_meas).sub measurable_const).mul hpow_meas).aestronglyMeasurable
  have hint_tail : IntegrableOn (fun t : ℝ => E t * t ^ (-δ - 1)) (Ioi T) := by
    have hdom : IntegrableOn (fun t : ℝ => (ε / 2) * t ^ (-δ - 1)) (Ioi T) :=
      (integrableOn_Ioi_rpow_of_lt (by linarith : -δ - 1 < -1) hT_pos).const_mul (ε / 2)
    refine hdom.mono' (hE_meas.mono_set (Ioi_subset_Ioi hT2)) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos (lt_trans hT_pos ht) _)]
    exact mul_le_mul_of_nonneg_right (hE_tail t (le_of_lt ht))
      (Real.rpow_pos_of_pos (lt_trans hT_pos ht) _).le
  have hint_const_head : IntegrableOn (fun _ : ℝ => B) (Ioc 2 T) :=
    integrableOn_const (hs := measure_Ioc_lt_top.ne)
  have hint_head : IntegrableOn (fun t : ℝ => E t * t ^ (-δ - 1)) (Ioc 2 T) := by
    refine hint_const_head.mono' (hE_meas.mono_set Ioc_subset_Ioi_self) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have ht_ge1 : 1 ≤ t := by linarith [ht.1]
    have hpow_le : t ^ (-δ - 1) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos ht_ge1 (by linarith)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos (by linarith) _)]
    calc |E t| * t ^ (-δ - 1)
        ≤ B * 1 := mul_le_mul (hE_bdd t ht) hpow_le (Real.rpow_nonneg (by linarith) _) hB_nonneg
      _ = B := mul_one B
  have hsplit : Ioi (2 : ℝ) = Ioc (2 : ℝ) T ∪ Ioi T := (Ioc_union_Ioi_eq_Ioi hT2).symm
  rw [hsplit, setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hint_head hint_tail,
    mul_add]
  have h1 : |δ * ∫ t in Ioc (2 : ℝ) T, E t * t ^ (-δ - 1)| < ε / 2 := by
    rw [abs_mul, abs_of_pos hδ_pos]
    have hnorm : |∫ t in Ioc (2 : ℝ) T, E t * t ^ (-δ - 1)| ≤ B * (T - 2) := by
      calc |∫ t in Ioc (2 : ℝ) T, E t * t ^ (-δ - 1)|
          = ‖∫ t in Ioc (2 : ℝ) T, E t * t ^ (-δ - 1)‖ := (Real.norm_eq_abs _).symm
        _ ≤ ∫ t in Ioc (2 : ℝ) T, ‖E t * t ^ (-δ - 1)‖ := norm_integral_le_integral_norm _
        _ ≤ ∫ _t in Ioc (2 : ℝ) T, B := by
            refine setIntegral_mono_on hint_head.norm hint_const_head measurableSet_Ioc fun t ht => ?_
            have ht_ge1 : 1 ≤ t := by linarith [ht.1]
            rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos (by linarith) _)]
            calc |E t| * t ^ (-δ - 1)
                ≤ B * 1 := mul_le_mul (hE_bdd t ht)
                  (Real.rpow_le_one_of_one_le_of_nonpos ht_ge1 (by linarith))
                  (Real.rpow_nonneg (by linarith) _) hB_nonneg
              _ = B := mul_one B
        _ = B * (T - 2) := by
            rw [setIntegral_const, Measure.real_def, Real.volume_Ioc,
              ENNReal.toReal_ofReal (by linarith), smul_eq_mul, mul_comm]
    have hmul_lt : δ * (B * (T - 2)) < ε / 2 := by
      have hden_pos : 0 < B * (T - 2) + 1 := by
        have := mul_nonneg hB_nonneg (by linarith : 0 ≤ T - 2); linarith
      calc δ * (B * (T - 2))
          < δ * (B * (T - 2) + 1) := mul_lt_mul_of_pos_left (by linarith) hδ_pos
        _ < δ₀ * (B * (T - 2) + 1) := mul_lt_mul_of_pos_right hδ_lt hden_pos
        _ = ε / 2 := by dsimp only [δ₀]; field_simp [hden_pos.ne']
    exact (mul_le_mul_of_nonneg_left hnorm hδ_pos.le).trans_lt hmul_lt
  have h2 : |δ * ∫ t in Ioi T, E t * t ^ (-δ - 1)| ≤ ε / 2 := by
    rw [abs_mul, abs_of_pos hδ_pos]
    have hnorm : |∫ t in Ioi T, E t * t ^ (-δ - 1)| ≤ ∫ t in Ioi T, (ε / 2) * t ^ (-δ - 1) := by
      calc |∫ t in Ioi T, E t * t ^ (-δ - 1)|
          = ‖∫ t in Ioi T, E t * t ^ (-δ - 1)‖ := (Real.norm_eq_abs _).symm
        _ ≤ ∫ t in Ioi T, ‖E t * t ^ (-δ - 1)‖ := norm_integral_le_integral_norm _
        _ ≤ ∫ t in Ioi T, (ε / 2) * t ^ (-δ - 1) := by
            refine setIntegral_mono_on hint_tail.norm
              ((integrableOn_Ioi_rpow_of_lt (by linarith : -δ - 1 < -1) hT_pos).const_mul (ε / 2))
              measurableSet_Ioi fun t ht => ?_
            rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos (lt_trans hT_pos ht) _)]
            exact mul_le_mul_of_nonneg_right (hE_tail t (le_of_lt ht))
              (Real.rpow_pos_of_pos (lt_trans hT_pos ht) _).le
    calc δ * |∫ t in Ioi T, E t * t ^ (-δ - 1)|
        ≤ δ * ∫ t in Ioi T, (ε / 2) * t ^ (-δ - 1) := mul_le_mul_of_nonneg_left hnorm hδ_pos.le
      _ = (ε / 2) * (δ * ∫ t in Ioi T, t ^ (-δ - 1)) := by rw [integral_const_mul]; ring
      _ = (ε / 2) * T ^ (-δ) := by rw [integral_Ioi_rpow_neg_sub_one hT_pos hδ_pos]
      _ ≤ (ε / 2) * 1 := mul_le_mul_of_nonneg_left
          (Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)) (half_pos hε).le
      _ = ε / 2 := mul_one _
  linarith [abs_add_le (δ * ∫ t in Ioc (2 : ℝ) T, E t * t ^ (-δ - 1))
    (δ * ∫ t in Ioi T, E t * t ^ (-δ - 1))]

private lemma tendsto_G_add_log_L_sub_gamma {L : ℝ}
    (hL : Tendsto (fun y : ℝ => F y - Real.log (Real.log y)) atTop (𝓝 L)) :
    Tendsto (fun δ : ℝ => G δ + Real.log δ) (𝓝[>] 0) (𝓝 (L - Real.eulerMascheroniConstant)) := by
  have h1 : Tendsto (fun δ : ℝ => L * (2 : ℝ) ^ (-δ)) (𝓝[>] 0) (𝓝 L) := by
    have hpow : Tendsto (fun δ : ℝ => (2 : ℝ) ^ (-δ)) (𝓝[>] 0) (𝓝 1) := by
      have hcont : ContinuousAt (fun δ : ℝ => (2 : ℝ) ^ (-δ)) 0 :=
        continuousAt_const.rpow continuousAt_id.neg (Or.inl (by norm_num))
      simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
    simpa using hpow.const_mul L
  have h2 := tendsto_log_log_piece
  have h3 := tendsto_error_piece hL
  have hcomb : Tendsto (fun δ : ℝ =>
      L * (2 : ℝ) ^ (-δ) +
        (δ * (∫ t in Ioi (2 : ℝ), Real.log (Real.log t) * t ^ (-δ - 1)) + Real.log δ) +
        δ * ∫ t in Ioi (2 : ℝ), (F t - Real.log (Real.log t) - L) * t ^ (-δ - 1))
      (𝓝[>] 0) (𝓝 (L - Real.eulerMascheroniConstant)) := by
    simpa [sub_eq_add_neg] using (h1.add h2).add h3
  -- Global uniform bound on `|F t - log (log t) - L|` for `t > 2`
  have hE_global : ∃ M₀ : ℝ, 0 ≤ M₀ ∧ ∀ t ∈ Ioi (2 : ℝ), |F t - Real.log (Real.log t) - L| ≤ M₀ := by
    obtain ⟨T₀, hT₀⟩ := (Metric.tendsto_atTop.mp (hL.sub_const L)) 1 zero_lt_one
    set T := max 2 T₀
    set B := F T + |Real.log (Real.log 2)| + |Real.log (Real.log T)| + |L|
    refine ⟨max B 1, le_trans zero_le_one (le_max_right _ _), fun t ht => ?_⟩
    by_cases hle : t ≤ T
    · have ht2 : 2 < t := ht
      have hFt_nonneg : 0 ≤ F t := F_nonneg t
      have hFt_le : F t ≤ F T := F_mono hle
      have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have hll_lo : Real.log (Real.log 2) ≤ Real.log (Real.log t) :=
        Real.log_le_log hlog2_pos (Real.log_le_log (by norm_num) ht2.le)
      have hll_hi : Real.log (Real.log t) ≤ Real.log (Real.log T) :=
        Real.log_le_log (Real.log_pos (by linarith)) (Real.log_le_log (by linarith) hle)
      have habs_ll : |Real.log (Real.log t)| ≤ |Real.log (Real.log 2)| + |Real.log (Real.log T)| := by
        rw [abs_le]
        constructor
        · linarith [neg_abs_le (Real.log (Real.log 2)), abs_nonneg (Real.log (Real.log T))]
        · linarith [le_abs_self (Real.log (Real.log T)), abs_nonneg (Real.log (Real.log 2))]
      have hB : |F t - Real.log (Real.log t) - L| ≤ B := by
        calc |F t - Real.log (Real.log t) - L|
            ≤ |F t| + |Real.log (Real.log t)| + |L| := by
              linarith [abs_sub (F t - Real.log (Real.log t)) L, abs_sub (F t) (Real.log (Real.log t))]
          _ ≤ F T + (|Real.log (Real.log 2)| + |Real.log (Real.log T)|) + |L| := by
              rw [abs_of_nonneg hFt_nonneg]; linarith
          _ = B := by dsimp only [B]; ring
      exact hB.trans (le_max_left _ _)
    · push Not at hle
      have hdist := hT₀ t ((le_max_right 2 T₀).trans hle.le)
      simp only [sub_self, Real.dist_eq, sub_zero] at hdist
      exact hdist.le.trans (le_max_right _ _)
  obtain ⟨M₀, hM₀_nonneg, hM₀⟩ := hE_global
  refine hcomb.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  have hδ_pos : 0 < δ := hδ
  rw [G_eq_mul_integral_F hδ_pos hL]
  have hint_const : IntegrableOn (fun t : ℝ => L * t ^ (-δ - 1)) (Ioi 2) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith : -δ - 1 < -1) (by norm_num)).const_mul L
  have hint_ll : IntegrableOn (fun t : ℝ => Real.log (Real.log t) * t ^ (-δ - 1)) (Ioi 2) := by
    have hdom : IntegrableOn (fun t : ℝ =>
        |Real.log (Real.log 2)| * t ^ (-δ - 1) + (2 / δ) * t ^ (-δ / 2 - 1)) (Ioi 2) :=
      ((integrableOn_Ioi_rpow_of_lt (by linarith : -δ - 1 < -1) (by norm_num)).const_mul _).add
        ((integrableOn_Ioi_rpow_of_lt (by linarith : -δ / 2 - 1 < -1) (by norm_num)).const_mul _)
    refine hdom.mono' ?_ ?_
    · exact ((Real.measurable_log.comp Real.measurable_log).mul
        (measurable_id.pow_const _)).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht_pos : 0 < t := lt_trans (by norm_num) ht
      have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have hlogt_ge : Real.log 2 ≤ Real.log t := Real.log_le_log (by norm_num) ht.le
      have hlogt_pos : 0 < Real.log t := hlog2_pos.trans_le hlogt_ge
      have habs_ll : |Real.log (Real.log t)| ≤ |Real.log (Real.log 2)| + Real.log t := by
        by_cases h1 : Real.log t ≤ 1
        · rw [abs_of_nonpos (Real.log_nonpos hlogt_pos.le h1)]
          have hll_ge : Real.log (Real.log 2) ≤ Real.log (Real.log t) :=
            Real.log_le_log hlog2_pos hlogt_ge
          linarith [neg_abs_le (Real.log (Real.log 2))]
        · push Not at h1
          rw [abs_of_pos (Real.log_pos h1)]
          linarith [Real.log_le_sub_one_of_pos hlogt_pos, abs_nonneg (Real.log (Real.log 2))]
      have hlog_rpow : Real.log t ≤ (2 / δ) * t ^ (δ / 2) := by
        have h := Real.log_le_rpow_div (ε := δ / 2) ht_pos.le (half_pos hδ_pos)
        have hrew : t ^ (δ / 2) / (δ / 2) = (2 / δ) * t ^ (δ / 2) := by
          field_simp [hδ_pos.ne']
        linarith
      have hrpow_mul : t ^ (δ / 2) * t ^ (-δ - 1) = t ^ (-δ / 2 - 1) := by
        rw [← Real.rpow_add ht_pos]
        congr 1; ring
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos ht_pos _)]
      calc |Real.log (Real.log t)| * t ^ (-δ - 1)
          ≤ (|Real.log (Real.log 2)| + (2 / δ) * t ^ (δ / 2)) * t ^ (-δ - 1) :=
            mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg ht_pos.le _)
        _ = |Real.log (Real.log 2)| * t ^ (-δ - 1) + (2 / δ) * (t ^ (δ / 2) * t ^ (-δ - 1)) := by
            ring
        _ = |Real.log (Real.log 2)| * t ^ (-δ - 1) + (2 / δ) * t ^ (-δ / 2 - 1) := by
            rw [hrpow_mul]
  have hint_E : IntegrableOn (fun t : ℝ => (F t - Real.log (Real.log t) - L) * t ^ (-δ - 1)) (Ioi 2) := by
    have hdom : IntegrableOn (fun t : ℝ => M₀ * t ^ (-δ - 1)) (Ioi 2) :=
      (integrableOn_Ioi_rpow_of_lt (by linarith : -δ - 1 < -1) (by norm_num)).const_mul M₀
    refine hdom.mono' ?_ ?_
    · exact (((measurable_F.sub (Real.measurable_log.comp Real.measurable_log)).sub measurable_const).mul
        (measurable_id.pow_const _)).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht_pos : 0 < t := lt_trans (by norm_num) ht
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos ht_pos _)]
      exact mul_le_mul_of_nonneg_right (hM₀ t ht) (Real.rpow_nonneg ht_pos.le _)
  have hint_const_ll :
      IntegrableOn (fun t : ℝ => L * t ^ (-δ - 1) + Real.log (Real.log t) * t ^ (-δ - 1)) (Ioi 2) :=
    hint_const.add hint_ll
  have hsum_int : ∫ t in Ioi (2 : ℝ), F t * t ^ (-δ - 1) =
      (∫ t in Ioi (2 : ℝ), L * t ^ (-δ - 1)) +
        (∫ t in Ioi (2 : ℝ), Real.log (Real.log t) * t ^ (-δ - 1)) +
        (∫ t in Ioi (2 : ℝ), (F t - Real.log (Real.log t) - L) * t ^ (-δ - 1)) := by
    rw [← integral_add hint_const hint_ll, ← integral_add hint_const_ll hint_E]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => by ring
  rw [hsum_int, mul_add, mul_add, integral_const_mul, ← mul_assoc, mul_comm δ L, mul_assoc,
    integral_Ioi_rpow_neg_sub_one (by norm_num) hδ_pos]
  ring

end OMA.MertensThirdProof

theorem OMA.solution : OMA.R_RiemannHypothesis_lagarias_criterion_R1_H2_R1_H1_R1_H1_R1_H2_R1.H1 := by
  obtain ⟨L, hL⟩ := OMA.MertensThirdProof.exists_limit_F_sub_log_log
  have h1 := OMA.MertensThirdProof.tendsto_G_add_log_zero
  have h2 := OMA.MertensThirdProof.tendsto_G_add_log_L_sub_gamma hL
  have hL_eq : L = Real.eulerMascheroniConstant := by
    have := tendsto_nhds_unique h1 h2
    linarith
  simpa [OMA.R_RiemannHypothesis_lagarias_criterion_R1_H2_R1_H1_R1_H1_R1_H2_R1.H1,
    OMA.MertensThirdProof.F, hL_eq] using hL
