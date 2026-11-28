import FormalConjectures.ErdosProblems.«5»
import Mathlib

/-! Reduction of the Hildebrand-Maier variant of Erdos Problem 5 to three steps, following the Lean
development OAI.NumberTheory.PrimeGaps (github.com/openai/math, Apache License 2.0, copyright OpenAI):
H1 is the Bombieri-Vinogradov estimate (proved there from Siegel-Walfisz), H2 is the existence of an
admissible family with small marked ratio, H3 is positive lower density of large prime gaps (1-based
indexing) from H1 and H2. The final glue to the limit-point statement is proved here.
Glue credit: lemma code reused from merged OMA reductions and step proofs by @minimumnz (R1),
Marcus Buffett / ivillar (R1.H1.R1, R1.H1.R1.H2), @loremcdmx (R1.H2), and @mucoucah. -/

open scoped ContDiff

namespace OMA.R_Erdos5_erdos_5_variants_hildebrand_maier_R2

def H1 : Prop :=
  ∀ A : ℝ, 0 < A → ∃ b : ℝ, 0 < b ∧ ∃ M : ℝ, 0 < M ∧ ∃ x₀ : ℝ, 1 < x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
      (∑ q ∈ Finset.Icc 1 ⌊x ^ (1 / 2 : ℝ) * Real.log x ^ (-b)⌋₊,
        (((Finset.range q).sup fun c => if Nat.Coprime c q then
          NNReal.mk |(∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (fun n => n % q = c),
            ArithmeticFunction.vonMangoldt n) - x / q.totient| (abs_nonneg _) else 0 : NNReal) : ℝ))
        ≤ M * x * Real.log x ^ (-A)

def H2 : Prop :=
  ∀ l τ e : ℝ, 0 < l → 0 < τ → 0 < e → ∃ k : ℕ, ∃ f : (j : ℕ) → (Fin j → ℝ) → ℝ,
      (0 < k ∧ (∀ j, j ≤ k → ContDiff ℝ ∞ (f j) ∧ HasCompactSupport (f j) ∧
        tsupport (f j) ⊆ {t | (∀ i, 0 < t i) ∧ ∑ i, t i < τ} ∧
        ∀ (σ : Equiv.Perm (Fin j)) (t : Fin j → ℝ), f j (t ∘ σ) = f j t) ∧ (∀ j, k < j → f j = 0)) ∧
      f 0 = 0 ∧ 0 < ∑ j ∈ Finset.range (k + 1), l ^ j / j.factorial * ∫ t, f j t ^ 2 ∧
      (l * ∑ j ∈ Finset.range (k + 1), l ^ j / j.factorial *
          ∫ t, (f j t + ∫ u : ℝ, f (j + 1) (Fin.snoc t u)) ^ 2) /
        (∑ j ∈ Finset.range (k + 1), l ^ j / j.factorial * ∫ t, f j t ^ 2) ≤ e

def H3 : Prop :=
  (∀ A : ℝ, 0 < A → ∃ b : ℝ, 0 < b ∧ ∃ M : ℝ, 0 < M ∧ ∃ x₀ : ℝ, 1 < x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
      (∑ q ∈ Finset.Icc 1 ⌊x ^ (1 / 2 : ℝ) * Real.log x ^ (-b)⌋₊,
        (((Finset.range q).sup fun c => if Nat.Coprime c q then
          NNReal.mk |(∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (fun n => n % q = c),
            ArithmeticFunction.vonMangoldt n) - x / q.totient| (abs_nonneg _) else 0 : NNReal) : ℝ))
        ≤ M * x * Real.log x ^ (-A)) →
    (∀ l τ e : ℝ, 0 < l → 0 < τ → 0 < e → ∃ k : ℕ, ∃ f : (j : ℕ) → (Fin j → ℝ) → ℝ,
      (0 < k ∧ (∀ j, j ≤ k → ContDiff ℝ ∞ (f j) ∧ HasCompactSupport (f j) ∧
        tsupport (f j) ⊆ {t | (∀ i, 0 < t i) ∧ ∑ i, t i < τ} ∧
        ∀ (σ : Equiv.Perm (Fin j)) (t : Fin j → ℝ), f j (t ∘ σ) = f j t) ∧ (∀ j, k < j → f j = 0)) ∧
      f 0 = 0 ∧ 0 < ∑ j ∈ Finset.range (k + 1), l ^ j / j.factorial * ∫ t, f j t ^ 2 ∧
      (l * ∑ j ∈ Finset.range (k + 1), l ^ j / j.factorial *
          ∫ t, (f j t + ∫ u : ℝ, f (j + 1) (Fin.snoc t u)) ^ 2) /
        (∑ j ∈ Finset.range (k + 1), l ^ j / j.factorial * ∫ t, f j t ^ 2) ≤ e) →
    ∀ C : ℝ, 0 < C → ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      c * (N : ℝ) ≤ (((Finset.Icc 1 N).filter fun n => C * Real.log (Nat.nth Nat.Prime (n - 1) : ℝ) < (Nat.nth Nat.Prime (n + 1 - 1) : ℝ) - (Nat.nth Nat.Prime (n - 1) : ℝ)).card : ℝ)

namespace OMAE5Glue

open Finset Filter Real
open scoped Topology
open scoped Classical

lemma gap_cast (m : ℕ) :
    ((primeGap m : ℕ) : ℝ) = (Nat.nth Nat.Prime (m + 1) : ℝ) - Nat.nth Nat.Prime m := by
  rw [primeGap, Nat.cast_sub
    ((Nat.nth_strictMono Nat.infinite_setOfPred_prime) (Nat.lt_succ_self m)).le]

lemma density
    (hmain : ∀ C : ℝ, 0 < C → ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      c * (N : ℝ) ≤ (((Finset.Icc 1 N).filter fun n => C * Real.log (Nat.nth Nat.Prime (n - 1) : ℝ) < (Nat.nth Nat.Prime (n + 1 - 1) : ℝ) - (Nat.nth Nat.Prime (n - 1) : ℝ)).card : ℝ))
    (A : ℝ) (hA : 0 < A) : ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop,
      c * N ≤ (((range N).filter fun n =>
        A * log (Nat.nth Nat.Prime n) < (primeGap n : ℝ)).card : ℝ) := by
  obtain ⟨c, hc, N₀, h⟩ := hmain A hA
  refine ⟨c, hc, eventually_atTop.2 ⟨N₀, fun N hN => (h N hN).trans ?_⟩⟩
  have hle : ((Finset.Icc 1 N).filter fun n => A * Real.log (Nat.nth Nat.Prime (n - 1) : ℝ) < (Nat.nth Nat.Prime (n + 1 - 1) : ℝ) - (Nat.nth Nat.Prime (n - 1) : ℝ)).card ≤ ((range N).filter fun n =>
      A * log (Nat.nth Nat.Prime n) < (primeGap n : ℝ)).card := by
    apply Finset.card_le_card_of_injOn (fun n => n - 1)
    · intro n hn
      simp only [Finset.mem_coe,
        Finset.mem_filter, Finset.mem_Icc, Nat.add_sub_cancel] at hn
      obtain ⟨⟨h1, h2⟩, hc⟩ := hn
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
      refine ⟨by omega, ?_⟩
      rw [gap_cast, Nat.sub_add_cancel h1]
      exact hc
    · intro a ha b hb hab
      simp only [Finset.mem_coe,
        Finset.mem_filter, Finset.mem_Icc] at ha hb
      simp only at hab
      omega
  exact_mod_cast hle

lemma sum_gaps (N : ℕ) : ∑ n ∈ range N, (primeGap n : ℝ) ≤ Nat.nth Nat.Prime N := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, gap_cast]
    linarith

lemma eventually_theta_ge_half : ∀ᶠ x : ℝ in atTop, x / 2 ≤ Chebyshev.theta x := by
  have hsqrt : Real.sqrt =o[atTop] (id : ℝ → ℝ) := by
    refine Asymptotics.isLittleO_iff.mpr fun ε hε => ?_
    filter_upwards [eventually_ge_atTop ((1 / ε) ^ 2)] with x hx
    have hx0 : 0 ≤ x := (sq_nonneg _).trans hx
    have hh : 1 / ε ≤ Real.sqrt x := Real.le_sqrt_of_sq_le hx
    have he : 1 ≤ ε * Real.sqrt x := by
      rw [div_le_iff₀ hε] at hh
      simpa [mul_comm] using hh
    simp only [id_eq, Real.norm_eq_abs, abs_of_nonneg hx0,
      abs_of_nonneg (Real.sqrt_nonneg x)]
    calc
      Real.sqrt x = 1 * Real.sqrt x := (one_mul _).symm
      _ ≤ (ε * Real.sqrt x) * Real.sqrt x :=
        mul_le_mul_of_nonneg_right he (Real.sqrt_nonneg x)
      _ = ε * x := by rw [mul_assoc, Real.mul_self_sqrt hx0]
  have herr := (Chebyshev.isBigO_psi_sub_theta_sqrt.trans_isLittleO hsqrt).bound
    (show (0 : ℝ) < 1 / 16 by norm_num)
  have hlog := Real.isLittleO_log_id_atTop.bound (show (0 : ℝ) < 1 / 32 by norm_num)
  filter_upwards [herr, hlog, eventually_ge_atTop (32 : ℝ)] with x he hl hx
  have hx0 : 0 ≤ x := by linarith
  simp only [id_eq, Real.norm_eq_abs, abs_of_nonneg hx0] at he hl
  have hl' := (le_abs_self (Real.log x)).trans hl
  have hlogadd : Real.log (x + 2) ≤ Real.log 2 + Real.log x := by
    rw [← Real.log_mul (by norm_num) (by positivity)]
    exact Real.log_le_log (by positivity) (by linarith)
  have hpsi := Chebyshev.psi_ge' hx0
  have hdiff := (le_abs_self (Chebyshev.psi x - Chebyshev.theta x)).trans he
  have hprod := mul_le_mul_of_nonneg_left
    (show (2 / 3 : ℝ) ≤ Real.log 2 by linarith [Real.log_two_gt_d9]) (show 0 ≤ x - 1 by linarith)
  linarith [Real.log_two_lt_d9]

lemma pi_lower : ∀ᶠ x : ℝ in atTop, x / (2 * Real.log x) ≤ (Nat.primeCounting ⌊x⌋₊ : ℝ) := by
  filter_upwards [eventually_theta_ge_half, eventually_ge_atTop (3 : ℝ)] with x hx hx3
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have h1 := Chebyshev.theta_le_psi x
  have h2 := Chebyshev.psi_le_primeCounting_mul_log' x
  rw [div_le_iff₀ (by positivity)]
  nlinarith

lemma tendsto_x : Tendsto (fun n : ℕ => 5 * (n : ℝ) * Real.log n) atTop atTop := by
  have h1 : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have h2 : Tendsto (fun n : ℕ => Real.log n) atTop atTop := Real.tendsto_log_atTop.comp h1
  have h3 := h1.atTop_mul_atTop₀ h2
  have h4 := h3.const_mul_atTop (show (0:ℝ) < 5 by norm_num)
  refine h4.congr fun n => ?_
  ring

lemma nth_le : ∀ᶠ n : ℕ in atTop, (Nat.nth Nat.Prime n : ℝ) ≤ 5 * n * Real.log n := by
  have hA := tendsto_x.eventually pi_lower
  have hB : ∀ᶠ n : ℕ in atTop, Real.log n ≤ 1 / 5 * n := by
    have := Real.isLittleO_log_id_atTop.bound (show (0 : ℝ) < 1 / 5 by norm_num)
    filter_upwards [tendsto_natCast_atTop_atTop.eventually this] with n hn
    simp only [id_eq, Real.norm_eq_abs] at hn
    have h0 : (0:ℝ) ≤ n := Nat.cast_nonneg n
    rw [abs_of_nonneg h0] at hn
    exact (le_abs_self _).trans hn
  filter_upwards [hA, hB, eventually_ge_atTop 4] with n hA hB hn4
  have hn : (4 : ℝ) ≤ n := by exact_mod_cast hn4
  have hlogn : 1 < Real.log n := by
    rw [Real.lt_log_iff_exp_lt (by linarith)]
    linarith [Real.exp_one_lt_d9]
  set x := 5 * (n : ℝ) * Real.log n with hxdef
  have hxpos : 0 < x := by positivity
  have hx2 : x ≤ (n : ℝ) ^ 2 := by
    rw [hxdef, sq]; nlinarith
  have hlogx : Real.log x ≤ 2 * Real.log n := by
    have := Real.log_le_log hxpos hx2
    rwa [Real.log_pow, Nat.cast_ofNat] at this
  have hlogxpos : 0 < Real.log x := Real.log_pos (by nlinarith)
  have hcount : (n : ℝ) + 1 ≤ (Nat.primeCounting ⌊x⌋₊ : ℝ) := by
    refine le_trans ?_ hA
    rw [le_div_iff₀ (by positivity)]
    have : 2 * Real.log x ≤ 4 * Real.log n := by linarith
    calc ((n:ℝ) + 1) * (2 * Real.log x) ≤ ((n:ℝ) + 1) * (4 * Real.log n) := by
          apply mul_le_mul_of_nonneg_left this; positivity
      _ ≤ x := by rw [hxdef]; nlinarith
  have hlt : n < Nat.count Nat.Prime (⌊x⌋₊ + 1) := by
    have : n + 1 ≤ Nat.primeCounting ⌊x⌋₊ := by exact_mod_cast hcount
    unfold Nat.primeCounting Nat.primeCounting' at this
    omega
  have := Nat.nth_lt_of_lt_count hlt
  have h3 : Nat.nth Nat.Prime n ≤ ⌊x⌋₊ := by omega
  calc (Nat.nth Nat.Prime n : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast h3
    _ ≤ x := Nat.floor_le hxpos.le

theorem windows
    (density : ∀ A : ℝ, 0 < A → ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop,
      c * N ≤ (((range N).filter fun n =>
        A * log (Nat.nth Nat.Prime n) < (primeGap n : ℝ)).card : ℝ))
    (cheb : ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop, (Nat.nth Nat.Prime N : ℝ) ≤ C * N * log N) :
    ∀ A : ℝ, 0 < A → ∃ B : ℝ, 0 ≤ B ∧
      ∃ᶠ n : ℕ in atTop,
        A * log (Nat.nth Nat.Prime n) ≤ (primeGap n : ℝ) ∧
        (primeGap n : ℝ) ≤ B * log (Nat.nth Nat.Prime n) := by
  intro A hA
  obtain ⟨c,hc,freq⟩ := density A hA
  obtain ⟨C,hC,hu⟩ := cheb
  let B := 8*C/c
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨B,hB.le,frequently_atTop.mpr ?_⟩
  intro M
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp (freq.and hu)
  obtain ⟨T,hT⟩ := exists_nat_ge (2/c)
  let t := max M (max T (max N₀ 2))
  have htM : M ≤ t := le_max_left ..
  have htT : T ≤ t := (le_max_left ..).trans (le_max_right ..)
  have htN : N₀ ≤ t := (le_max_left ..).trans ((le_max_right ..).trans (le_max_right ..))
  have ht2 : 2 ≤ t := (le_max_right ..).trans ((le_max_right ..).trans (le_max_right ..))
  have tpos : (0:ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have tc : 2 ≤ c * t := by
    have hh := (div_le_iff₀ hc).mp (hT.trans (Nat.cast_le.mpr htT))
    linarith
  have ltlog : 0 < log t := log_pos (by exact_mod_cast (show 1 < t by omega))
  obtain ⟨hn,hn'⟩ := hN₀ (t^2) (htN.trans (by nlinarith))
  let P := (range (t^2)).filter fun n => A * log (Nat.nth Nat.Prime n) < (primeGap n:ℝ)
  let S := P \ range t
  have hcard : c*(t:ℝ)^2/2 ≤ S.card := by
    change c*(t^2:ℕ) ≤ (P.card:ℝ) at hn
    push_cast at hn
    have hh := le_card_sdiff (range t) P
    rw [card_range] at hh
    have hh' : P.card ≤ S.card+t := by dsimp [S]; omega
    have r : (P.card:ℝ) ≤ S.card + (t:ℝ) := by exact_mod_cast hh'
    nlinarith [mul_le_mul_of_nonneg_right tc tpos.le]
  by_contra! bad
  have large (n : ℕ) (hn : n ∈ S) : B * log t ≤ (primeGap n : ℝ) := by
    obtain ⟨hp,ht⟩ := mem_sdiff.mp hn
    have hit := (mem_filter.mp hp).2
    have htn : t ≤ n := by simpa using ht
    have hbig := bad n (htM.trans htn) hit.le
    apply le_trans _ hbig.le
    apply mul_le_mul_of_nonneg_left _ hB.le
    exact Real.log_le_log tpos
      (by exact_mod_cast htn.trans (by have := Nat.add_two_le_nth_prime n; omega))
  have total : (S.card:ℝ) * (B * log t) ≤ (Nat.nth Nat.Prime (t^2):ℝ) := calc
    _ = ∑ _n ∈ S, B * log t := by simp
    _ ≤ ∑ n ∈ S, (primeGap n:ℝ) := sum_le_sum large
    _ ≤ ∑ n ∈ range (t^2), (primeGap n:ℝ) := by
      apply sum_le_sum_of_subset_of_nonneg (sdiff_subset.trans (filter_subset _ _))
      exact fun n _ _ => Nat.cast_nonneg _
    _ ≤ _ := sum_gaps _
  have high : c*(t:ℝ)^2/2*(B*log t) ≤ C*(t:ℝ)^2*(2*log t) := by
    apply (mul_le_mul_of_nonneg_right hcard (mul_nonneg hB.le ltlog.le)).trans
    exact total.trans (by simpa only [Nat.cast_pow,Real.log_pow,Nat.cast_ofNat] using hn')
  have eq : c*(t:ℝ)^2/2*(B*log t) = 4 * (C*(t:ℝ)^2*log t) := by dsimp [B]; field_simp; ring
  rw [eq] at high
  nlinarith only [high,mul_pos (mul_pos hC (sq_pos_of_pos tpos)) ltlog]

lemma nth_sq (m : ℕ) (hm : 16 ≤ m) : Nat.nth Nat.Prime m ≤ m ^ 2 := by
  have hm' : (16:ℝ) ≤ m := by exact_mod_cast hm
  have hpi := Chebyshev.pi_ge (m ^ 2)
  have hlogm : 0 < Real.log m := Real.log_pos (by linarith)
  have hl2 : Real.log (((m ^ 2 : ℕ) : ℝ)) = 2 * Real.log m := by
    push_cast; rw [Real.log_pow]; norm_num
  have h2 := Real.log_two_gt_d9
  have hA : Real.log (m : ℝ) ≤ m / 8 + 3 := by
    have h8 : Real.log ((m:ℝ) / 8) ≤ m / 8 - 1 := Real.log_le_sub_one_of_pos (by linarith)
    rw [Real.log_div (by linarith) (by norm_num)] at h8
    have : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8:ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
    have h2' := Real.log_two_lt_d9
    linarith
  have h2' := Real.log_two_lt_d9
  have hB : Real.log (((m ^ 2 : ℕ) : ℝ) + 1) ≤ Real.log 2 + 2 * Real.log m := by
    have e : Real.log (2 * (m:ℝ) ^ 2) = Real.log 2 + 2 * Real.log m := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]; norm_num
    rw [← e]
    apply Real.log_le_log (by positivity)
    push_cast; nlinarith
  have hm0 : (0:ℝ) ≤ m := by linarith
  have h3 : (m:ℝ) * Real.log m ≤ (m:ℝ) * (m / 8 + 3) := mul_le_mul_of_nonneg_left hA hm0
  have h4 : (m:ℝ)^2 * 0.69 ≤ (m:ℝ)^2 * Real.log 2 :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hlt : (m : ℝ) < (((m ^ 2 : ℕ) : ℝ) * Real.log 2 - Real.log (((m ^ 2 : ℕ) : ℝ) + 1)) /
      Real.log (((m ^ 2 : ℕ) : ℝ)) := by
    rw [hl2, lt_div_iff₀ (by linarith)]
    push_cast at hB ⊢
    nlinarith
  have hcnt : (m : ℝ) < (Nat.primeCounting (m ^ 2) : ℝ) := lt_of_lt_of_le hlt hpi
  have hcnt' : m < Nat.primeCounting (m ^ 2) := by exact_mod_cast hcnt
  have := Nat.nth_lt_of_lt_count (p := Nat.Prime) (n := m ^ 2 + 1) (k := m) hcnt'
  omega

lemma scale : ∀ᶠ n : ℕ in atTop, 0 < log n ∧
    log n ≤ log (Nat.nth Nat.Prime n) ∧ log (Nat.nth Nat.Prime n) ≤ 2 * log n := by
  filter_upwards [eventually_ge_atTop 16] with n hn
  have hn' : (16:ℝ) ≤ n := by exact_mod_cast hn
  have hpos : 0 < Real.log n := Real.log_pos (by linarith)
  have hle : n ≤ Nat.nth Nat.Prime n := by
    have := Nat.add_two_le_nth_prime n; omega
  have hk := nth_sq n hn
  refine ⟨hpos, ?_, ?_⟩
  · exact Real.log_le_log (by linarith) (by exact_mod_cast hle)
  · have hp : (0:ℝ) < Nat.nth Nat.Prime n := by
      have : (0:ℕ) < Nat.nth Nat.Prime n := by omega
      exact_mod_cast this
    calc Real.log (Nat.nth Nat.Prime n) ≤ Real.log ((n:ℝ) ^ 2) :=
          Real.log_le_log hp (by exact_mod_cast hk)
      _ = 2 * Real.log n := by rw [Real.log_pow]; norm_num

end OMAE5Glue

open Filter Real Set in
theorem OMAE5.glue
    (hmain : ∀ C : ℝ, 0 < C → ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      c * (N : ℝ) ≤ (((Finset.Icc 1 N).filter fun n => C * Real.log (Nat.nth Nat.Prime (n - 1) : ℝ) < (Nat.nth Nat.Prime (n + 1 - 1) : ℝ) - (Nat.nth Nat.Prime (n - 1) : ℝ)).card : ℝ)) :
    ∀ C : ℝ, ∃ x ∈ Erdos5.limitPointSet, C < x := by
  intro C
  let A := max C 0 + 1
  have hA : 0 < A := by dsimp [A]; linarith [le_max_right C 0]
  obtain ⟨B, hB, hits⟩ := OMAE5Glue.windows (OMAE5Glue.density hmain)
    ⟨5, by norm_num, OMAE5Glue.nth_le⟩ A hA
  have visits : ∃ᶠ n : ℕ in atTop, Erdos5.normalizedGap n ∈ Icc A (B * 2) := by
    apply (hits.and_eventually OMAE5Glue.scale).mono
    rintro n ⟨⟨lo, hi⟩, pos, lower, upper⟩
    constructor
    · exact (le_div_iff₀ pos).2 ((mul_le_mul_of_nonneg_left lower hA.le).trans lo)
    · apply (div_le_iff₀ pos).2
      simpa only [mul_assoc] using hi.trans (mul_le_mul_of_nonneg_left upper hB)
  obtain ⟨x, hx, cluster⟩ := isCompact_Icc.exists_mapClusterPt_of_frequently visits
  refine ⟨x, cluster, lt_of_lt_of_le ?_ hx.1⟩
  dsimp [A]
  linarith [le_max_left C 0]

theorem main : H1 → H2 → H3 → type_of% @Erdos5.erdos_5.variants.hildebrand_maier :=
  fun h1 h2 h3 => OMAE5.glue (h3 h1 h2)

end OMA.R_Erdos5_erdos_5_variants_hildebrand_maier_R2
