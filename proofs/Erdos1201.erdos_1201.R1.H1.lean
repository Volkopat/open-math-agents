import OMAReductions.R_Erdos1201_erdos_1201_R1
import Mathlib

-- Step H1 of the Erdős 1201 reduction: Erdős's case ε = 1 / 2 plus monotonicity in ε.
-- The ε = 1 / 2 theorem (namespace HalfPrime and OMA.half) is adapted from the merged proof of
-- Erdos1201.erdos_1201.variants.epsilon_half in open-math-agents (PR 2325, by @Genbox).
-- The monotonicity argument (namespace OMA1201) is new.
/-!
Large prime factors in blocks of consecutive integers.

Consider the sum of log p over prime divisors p up to the square root of the
counting cutoff. Subtract its expected value and sum the result over the block.
The Chinese remainder theorem bounds the off-diagonal terms in the resulting
second moment. A square-divisor estimate lets us neglect repeated factors.
Outside these two exceptional sets, a block with no large prime factor would
have an excessively large centered sum.
-/

open Finset Filter

namespace HalfPrime

private theorem quotient_card {N m : ℕ} (A : Finset ℕ) (hA : A ⊆ range N)
    (hr : ∀ a ∈ A, ∀ b ∈ A, a ≡ b [MOD m]) : A.card ≤ N / m + 1 := by
  have hi : (A : Set ℕ).InjOn (fun a => a/m) := by
    intro a ha b hb hab
    change a/m = b/m at hab
    have hr' : a%m = b%m := hr a ha b hb
    have h₁ := Nat.div_add_mod a m
    have h₂ := Nat.div_add_mod b m
    rw [hab, hr'] at h₁
    omega
  have hsub : A.image (fun a => a/m) ⊆ range (N/m+1) := by
    intro q hq
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hq
    exact mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right (mem_range.mp (hA ha)).le))
  rw [← card_range (N/m+1), ← card_image_of_injOn hi]
  exact card_le_card hsub

private theorem shifted_modEq {p n m i : ℕ} (hn : p ∣ n+i) (hm : p ∣ m+i) :
    n ≡ m [MOD p] :=
  Nat.ModEq.add_right_cancel' i
    ((Nat.modEq_zero_iff_dvd.mpr hn).trans (Nat.modEq_zero_iff_dvd.mpr hm).symm)

private def hits (N p i : ℕ) : Finset ℕ := (range N).filter (fun n => p ∣ n+i)

private theorem cast_div_le (N p : ℕ) (hp : 0 < p) :
    ((N/p : ℕ) : ℝ) ≤ (N : ℝ)/p := by
  rw [le_div_iff₀ (by exact_mod_cast hp : 0 < (p : ℝ))]
  exact_mod_cast Nat.div_mul_le_self N p

private theorem le_cast_div_succ (N p : ℕ) (hp : 0 < p) :
    (N : ℝ)/p ≤ ((N/p : ℕ) : ℝ) + 1 := by
  apply (div_le_iff₀ (by exact_mod_cast hp : 0 < (p : ℝ))).mpr
  rw [mul_comm]
  exact_mod_cast (Nat.lt_mul_div_succ N hp).le

private theorem hits_lower (N p i : ℕ) (hp : 0 < p) :
    (N : ℝ)/p - 1 ≤ ((hits N p i).card : ℝ) := by
  let : NeZero p := ⟨hp.ne'⟩
  let r := (-(i : ZMod p)).val
  have hr : r < p := ZMod.val_lt _
  let f (u : ℕ) := p*u+r
  have hsub : (range (N/p)).image f ⊆ hits N p i := by
    intro n hn
    obtain ⟨u, hu, rfl⟩ := mem_image.mp hn
    have hu' := mem_range.mp hu
    refine mem_filter.mpr ⟨mem_range.mpr ?_, ?_⟩
    · dsimp [f]
      calc
        p*u+r < p*u+p := Nat.add_lt_add_left hr _
        _ = (u+1)*p := by ring
        _ ≤ (N/p)*p := Nat.mul_le_mul_right p (by omega)
        _ ≤ N := Nat.div_mul_le_self _ _
    · apply (ZMod.natCast_eq_zero_iff _ _).mp
      push_cast [f]
      rw [ZMod.natCast_self, zero_mul, zero_add, ZMod.natCast_zmod_val, neg_add_cancel]
  have hi : Function.Injective f := by
    intro a b h
    apply Nat.eq_of_mul_eq_mul_left hp
    exact Nat.add_right_cancel h
  have hc := card_le_card hsub
  rw [card_image_of_injective _ hi, card_range] at hc
  have hc' : ((N/p : ℕ) : ℝ) ≤ ((hits N p i).card : ℝ) := by exact_mod_cast hc
  linarith [le_cast_div_succ N p hp]

private theorem hits_upper (N p i : ℕ) (hp : 0 < p) :
    ((hits N p i).card : ℝ) ≤ (N : ℝ)/p + 1 := by
  have h := quotient_card (hits N p i) (filter_subset _ _)
    (fun a ha b hb => shifted_modEq (mem_filter.mp ha).2 (mem_filter.mp hb).2)
  have h' : ((hits N p i).card : ℝ) ≤ ((N/p : ℕ) : ℝ) + 1 := by exact_mod_cast h
  linarith [cast_div_le N p hp]

private theorem count_both (N K p q i j : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hKp : K ≤ p) (hi : i < K) (hj : j < K) :
    (((hits N p i ∩ hits N q j).card : ℝ)) ≤
      (N : ℝ)/p/q + 1 + (if p=q ∧ i=j then (N : ℝ)/p else 0) := by
  by_cases he : p=q
  · subst q
    by_cases hij : i=j
    · subst j
      simp only [inter_self, and_self, if_true]
      linarith [hits_upper N p i hp.pos, show 0 ≤ (N : ℝ)/p/p by positivity]
    · have hEmpty : Disjoint (hits N p i) (hits N p j) := by
        refine disjoint_left.mpr (fun n hn hm => ?_)
        have hni := (mem_filter.mp hn).2
        have hnj := (mem_filter.mp hm).2
        have hmod : i ≡ j [MOD p] := Nat.ModEq.add_left_cancel' n
          ((Nat.modEq_zero_iff_dvd.mpr hni).trans (Nat.modEq_zero_iff_dvd.mpr hnj).symm)
        have := hmod.eq_of_lt_of_lt (hi.trans_le hKp) (hj.trans_le hKp)
        exact hij this
      rw [disjoint_iff_inter_eq_empty.mp hEmpty, card_empty, Nat.cast_zero]
      split <;> positivity
  · have hco := (Nat.coprime_primes hp hq).mpr he
    have hc := quotient_card (m := p*q) (hits N p i ∩ hits N q j)
      ((inter_subset_left).trans (filter_subset _ _)) (fun a ha b hb => by
        obtain ⟨ha₁, ha₂⟩ := mem_inter.mp ha
        obtain ⟨hb₁, hb₂⟩ := mem_inter.mp hb
        exact (Nat.modEq_and_modEq_iff_modEq_mul hco).mp
          ⟨shifted_modEq (mem_filter.mp ha₁).2 (mem_filter.mp hb₁).2,
          shifted_modEq (mem_filter.mp ha₂).2 (mem_filter.mp hb₂).2⟩)
    have hc' : (((hits N p i ∩ hits N q j).card : ℝ)) ≤ ((N/(p*q) : ℕ) : ℝ) + 1 := by
      exact_mod_cast hc
    simp only [he, false_and, if_false, add_zero]
    have hd := cast_div_le N (p*q) (mul_pos hp.pos hq.pos)
    push_cast at hd
    rw [← div_div] at hd
    linarith

private theorem count_positive_shift (N p i : ℕ) :
    ((range N).filter (fun n => n ≠ 0 ∧ p ∣ n+i)).card ≤ (N+i)/p := by
  let S := (range N).filter (fun n => n ≠ 0 ∧ p ∣ n+i)
  have hi : Function.Injective (fun n : ℕ => n+i) := fun _ _ => Nat.add_right_cancel
  have hsub : S.image (fun n => n+i) ⊆ ((range (N+i+1)).filter (fun n => n ≠ 0 ∧ p ∣ n)) := by
    intro m hm
    obtain ⟨n, hn, rfl⟩ := mem_image.mp hm
    obtain ⟨hnN, hn0, hnD⟩ := mem_filter.mp hn
    exact mem_filter.mpr ⟨mem_range.mpr (by have := mem_range.mp hnN; omega), by omega, hnD⟩
  have hc := card_le_card hsub
  rw [card_image_of_injective _ hi, Nat.card_multiples'] at hc
  exact hc

private theorem log_factors {n : ℕ} (hn : 0 < n) :
    Real.log n = ∑ p ∈ n.primeFactors, (n.factorization p : ℝ)*Real.log p := by
  have hprod : (∏ p ∈ n.primeFactors, p^(n.factorization p)) = n :=
    Nat.prod_factorization_pow_eq_self hn.ne'
  calc
    Real.log n = Real.log ((∏ p ∈ n.primeFactors, p^(n.factorization p) : ℕ) : ℝ) := by rw [hprod]
    _ = _ := by
      push_cast
      rw [Real.log_prod]
      · simp only [Real.log_pow]
      · intro p hp
        exact pow_ne_zero _ (by exact_mod_cast (Nat.mem_primeFactors.mp hp).1.ne_zero)

private theorem prime_log_sum (Y : ℕ) :
    (∑ p ∈ Nat.primesLE Y, Real.log p) ≤ Real.log 4 * Y := by
  rw [← Chebyshev.theta_eq_sum_primesLE_log]
  exact Chebyshev.theta_le_log4_mul_x (by positivity)

private theorem prime_log_harmonic {Y : ℕ} (hY : 0 < Y) :
    (∑ p ∈ Nat.primesLE Y, Real.log p / (p : ℝ)) ≤ Real.log Y + Real.log 4 := by
  let P := Nat.primesLE Y
  have hY' : 0 < (Y : ℝ) := by exact_mod_cast hY
  have hp (p : ℕ) (hp : p ∈ P) : p.Prime ∧ p ≤ Y := ⟨(Nat.mem_primesLE.mp hp).2, (Nat.mem_primesLE.mp hp).1⟩
  have hfac (p : ℕ) (hp : p.Prime) : Y/p ≤ Y.factorial.factorization p := by
    rw [Nat.factorization_factorial hp (show Nat.log p Y < Nat.log p Y + 2 by omega)]
    simpa only [pow_one] using
      (single_le_sum (f := fun i : ℕ => Y/p^i) (fun _ _ => Nat.zero_le _)
        (mem_Ico.mpr (show 1 ≤ (1 : ℕ) ∧ 1 < Nat.log p Y + 2 by omega)))
  have hmul : (Y : ℝ) * (∑ p ∈ P, Real.log p / (p : ℝ)) ≤
      Real.log Y.factorial + ∑ p ∈ P, Real.log p := by
    rw [mul_sum, log_factors (Nat.factorial_pos Y)]
    calc
      _ ≤ ∑ p ∈ P, ((Y.factorial.factorization p : ℝ)+1) * Real.log p := by
        apply sum_le_sum
        intro p hP
        have hq := (hp p hP).1
        have hbound := (le_cast_div_succ Y p hq.pos).trans
          (add_le_add_left (show ((Y/p : ℕ) : ℝ) ≤ (Y.factorial.factorization p : ℝ) by
            exact_mod_cast hfac p hq) 1)
        rw [show (Y : ℝ) * (Real.log p / (p : ℝ)) = ((Y : ℝ)/p)*Real.log p by ring]
        apply mul_le_mul_of_nonneg_right hbound
        exact Real.log_natCast_nonneg p
      _ = (∑ p ∈ P, (Y.factorial.factorization p : ℝ)*Real.log p) + ∑ p ∈ P, Real.log p := by
        simp only [add_mul, one_mul, sum_add_distrib]
      _ ≤ _ := by
        apply add_le_add_left
        refine sum_le_sum_of_subset_of_nonneg ?_ (fun p _ _ =>
          mul_nonneg (by positivity) (Real.log_natCast_nonneg p))
        intro p hP
        obtain ⟨hp, hpY⟩ := hp p hP
        exact Nat.mem_primeFactors.mpr
          ⟨hp, hp.dvd_factorial.mpr hpY, Nat.factorial_ne_zero _⟩
  have hlog : Real.log Y.factorial ≤ (Y : ℝ)*Real.log Y := by
    rw [← Real.log_pow]
    apply Real.log_le_log (by exact_mod_cast Nat.factorial_pos Y)
    exact_mod_cast Nat.factorial_le_pow Y
  have hθ := prime_log_sum Y
  apply (mul_le_mul_iff_of_pos_left hY').mp
  linarith

private theorem sqrt_nat_cast (N : ℕ) : (N.sqrt : ℝ) ≤ Real.sqrt N := by
  apply (Real.le_sqrt (by positivity) (by positivity)).mpr
  exact_mod_cast Nat.sqrt_le' N

private theorem sqrt_log (N : ℕ) (hN : 1 ≤ N) :
    Real.log N.sqrt ≤ Real.log N / 2 := by
  have hN' : (0 : ℝ) < (N.sqrt : ℝ) := by
    exact_mod_cast (Nat.le_sqrt'.mpr (show 1^2 ≤ N by simpa using hN))
  rw [← Real.log_sqrt (by positivity : 0 ≤ (N : ℝ))]
  exact Real.log_le_log hN' (sqrt_nat_cast N)

private def indicator (p i n : ℕ) : ℝ := if p ∣ n+i then 1 else 0

private noncomputable def centered (p i n : ℕ) : ℝ := indicator p i n - (p : ℝ)⁻¹

private theorem sum_indicator (N p i : ℕ) :
    (∑ n ∈ range N, indicator p i n) = ((hits N p i).card : ℝ) := by
  calc
    _ = ∑ _n ∈ hits N p i, (1 : ℝ) := by rw [hits, sum_filter]; rfl
    _ = _ := by simp

private theorem sum_joint (N p q i j : ℕ) :
    (∑ n ∈ range N, indicator p i n * indicator q j n) =
        ((hits N p i ∩ hits N q j).card : ℝ) := by
  have hfilter : hits N p i ∩ hits N q j =
      (range N).filter (fun n => p ∣ n+i ∧ q ∣ n+j) := by
    ext n
    simp only [hits, mem_filter, mem_inter]
    tauto
  calc
    _ = ∑ _n ∈ (range N).filter (fun n => p ∣ n+i ∧ q ∣ n+j), (1 : ℝ) := by
      rw [sum_filter]
      apply sum_congr rfl
      intro n _
      by_cases hp : p ∣ n+i <;> by_cases hq : q ∣ n+j <;> simp [indicator, hp, hq]
    _ = _ := by rw [← hfilter]; simp

private theorem covariance_upper (N K p q i j : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hKp : K ≤ p) (hi : i < K) (hj : j < K) :
    (∑ n ∈ range N, centered p i n * centered q j n) ≤
      3 + (if p=q ∧ i=j then (N : ℝ)/p else 0) := by
  have hp₀ : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hq₀ : 0 < (q : ℝ) := by exact_mod_cast hq.pos
  have hp₁ : (p : ℝ)⁻¹ ≤ 1 := (inv_le_one₀ hp₀).mpr (by exact_mod_cast hp.one_lt.le)
  have hq₁ : (q : ℝ)⁻¹ ≤ 1 := (inv_le_one₀ hq₀).mpr (by exact_mod_cast hq.one_lt.le)
  have h₁ := mul_le_mul_of_nonneg_right (hits_lower N p i hp.pos) (inv_nonneg.mpr hq₀.le)
  have h₂ := mul_le_mul_of_nonneg_left (hits_lower N q j hq.pos) (inv_nonneg.mpr hp₀.le)
  have h₃ := count_both N K p q i j hp hq hKp hi hj
  have he : (∑ n ∈ range N, centered p i n * centered q j n) =
      ((hits N p i ∩ hits N q j).card : ℝ) -
        ((hits N p i).card : ℝ)*(q : ℝ)⁻¹ -
        ((p : ℝ)⁻¹*((hits N q j).card : ℝ) - (N : ℝ)*((p : ℝ)⁻¹*(q : ℝ)⁻¹)) := by
    simp only [centered, sub_mul, mul_sub, sum_sub_distrib, ← sum_mul, ← mul_sum,
      sum_indicator, sum_joint, sum_const, card_range, nsmul_eq_mul]
    ring
  rw [he]
  simp only [div_eq_mul_inv] at h₁ h₂ h₃
  ring_nf at h₁ h₂ h₃ ⊢
  linarith

private noncomputable def signal (K : ℕ) (P : Finset ℕ) (n : ℕ) : ℝ :=
  ∑ x ∈ (range K ×ˢ P), Real.log x.2 * centered x.2 x.1 n

private theorem moment_bound (N K : ℕ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ K ≤ p) :
    (∑ n ∈ range N, signal K P n ^ 2) ≤
      3 * ((K : ℝ) * ∑ p ∈ P, Real.log p)^2 +
      (N : ℝ)*K*(∑ p ∈ P, (Real.log p)^2 / (p : ℝ)) := by
  let S := range K ×ˢ P
  let w (x : ℕ × ℕ) := Real.log x.2
  let z (x : ℕ × ℕ) (n : ℕ) := centered x.2 x.1 n
  have hw (x : ℕ × ℕ) : 0 ≤ w x := Real.log_natCast_nonneg _
  have hwSum : (∑ x ∈ S, w x) = (K : ℝ) * ∑ p ∈ P, Real.log p := by
    rw [sum_product]
    simp [w]
  have hdiagSum : (∑ x ∈ S, w x^2 / (x.2 : ℝ)) =
      (K : ℝ) * ∑ p ∈ P, (Real.log p)^2 / (p : ℝ) := by
    rw [sum_product]
    simp [w]
  have huv (x : ℕ × ℕ) (hx : x ∈ S) (y : ℕ × ℕ) (hy : y ∈ S) :
      (∑ n ∈ range N, z x n * z y n) ≤ 3 + (if x=y then (N : ℝ)/(x.2 : ℝ) else 0) := by
    obtain ⟨hx₁, hx₂⟩ := mem_product.mp hx
    obtain ⟨hy₁, hy₂⟩ := mem_product.mp hy
    have h := covariance_upper N K x.2 y.2 x.1 y.1 (hP _ hx₂).1 (hP _ hy₂).1
      (hP _ hx₂).2 (mem_range.mp hx₁) (mem_range.mp hy₁)
    simpa only [z, Prod.ext_iff, and_comm] using h
  have he (x : ℕ × ℕ) (hx : x ∈ S) :
      (∑ y ∈ S, w x*w y * (if x=y then (N : ℝ)/(x.2 : ℝ) else 0)) =
      (N : ℝ) * (w x^2 / (x.2 : ℝ)) := by
    rw [sum_eq_single_of_mem x hx]
    · simp; ring
    · intro y hy hne
      simp [hne.symm]
  calc
    _ = ∑ n ∈ range N, ∑ x ∈ S, ∑ y ∈ S, w x*w y*(z x n*z y n) := by
      apply sum_congr rfl
      intro n hn
      change (∑ x ∈ S, w x*z x n)^2 = _
      rw [sq, sum_mul]
      simp_rw [mul_sum]
      apply sum_congr rfl
      intro x hx
      apply sum_congr rfl
      intro y hy
      ring
    _ = ∑ x ∈ S, ∑ y ∈ S, w x*w y*(∑ n ∈ range N, z x n*z y n) := by
      rw [sum_comm]
      apply sum_congr rfl
      intro x hx
      rw [sum_comm]
      simp_rw [mul_sum]
    _ ≤ ∑ x ∈ S, ∑ y ∈ S, w x*w y*(3 + (if x=y then (N : ℝ)/(x.2 : ℝ) else 0)) :=
      sum_le_sum fun x hx => sum_le_sum fun y hy =>
        mul_le_mul_of_nonneg_left (huv x hx y hy) (mul_nonneg (hw x) (hw y))
    _ = 3 * (∑ x ∈ S, w x)^2 + (N : ℝ) * (∑ x ∈ S, w x^2 / (x.2 : ℝ)) := by
      simp_rw [mul_add, sum_add_distrib]
      rw [sum_congr rfl he, ← mul_sum]
      congr 1
      rw [sq, sum_mul]
      simp_rw [mul_sum]
      apply sum_congr rfl
      intro x hx
      apply sum_congr rfl
      intro y hy
      ring
    _ = _ := by rw [hwSum, hdiagSum]; ring

private def squareHits (N K T : ℕ) : Finset ℕ :=
  (range K).biUnion (fun i => (Icc T (N+K)).biUnion (fun a =>
    (range N).filter (fun n => n ≠ 0 ∧ a^2 ∣ n+i)))

private theorem square_hits_bound {K : ℕ} (hK : 0 < K) {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 1 ≤ T ∧ ∀ N ≥ K, ((squareHits N K T).card : ℝ) ≤ ε * N := by
  let w (a : ℕ) : ℝ := ((a : ℝ)^2)⁻¹
  have hs : Summable w := by
    convert (Real.summable_nat_rpow.mpr (show (-2 : ℝ) < -1 by norm_num)) using 1
    funext a
    rw [Real.rpow_neg (Nat.cast_nonneg a)]
    norm_num [w, Real.rpow_natCast]
  obtain ⟨S, hS⟩ := hs.vanishing (Iio_mem_nhds (show 0 < ε/(2*(K : ℝ)) by positivity))
  obtain ⟨T₀, hT₀⟩ := exists_nat_subset_range S
  let T := max T₀ 1
  have hT : 1 ≤ T := le_max_right _ _
  refine ⟨T, hT, fun N hN => ?_⟩
  have hd : Disjoint (Icc T (N+K)) S := by
    refine disjoint_left.mpr fun a ha hb => ?_
    have h₁ := (mem_Icc.mp ha).1
    have h₂ := mem_range.mp (hT₀ hb)
    dsimp [T] at h₁
    omega
  have hsmall := Set.mem_Iio.mp (hS (Icc T (N+K)) hd)
  have hcnt (i : ℕ) (hi : i ∈ range K) :
      (((Icc T (N+K)).biUnion (fun a =>
        (range N).filter (fun n => n ≠ 0 ∧ a^2 ∣ n+i))).card : ℝ) ≤ ε / K * N := by
    have hi' : (i : ℝ) ≤ (N : ℝ) := by exact_mod_cast (mem_range.mp hi).le.trans hN
    calc
      _ ≤ ∑ a ∈ Icc T (N+K), (((range N).filter (fun n => n ≠ 0 ∧ a^2 ∣ n+i)).card : ℝ) := by
        exact_mod_cast card_biUnion_le
      _ ≤ ∑ a ∈ Icc T (N+K), (2*(N : ℝ))*w a := by
        apply sum_le_sum
        intro a ha
        have ha₀ : 0 < a := hT.trans (mem_Icc.mp ha).1
        have hdvd : (((range N).filter (fun n => n ≠ 0 ∧ a^2 ∣ n+i)).card : ℝ) ≤
            (((N+i)/(a^2) : ℕ) : ℝ) := by exact_mod_cast count_positive_shift N (a^2) i
        apply hdvd.trans ((cast_div_le _ _ (pow_pos ha₀ _)).trans ?_)
        push_cast
        rw [div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = (2*(N : ℝ))*∑ a ∈ Icc T (N+K), w a := (mul_sum ..).symm
      _ ≤ (2*(N : ℝ))*(ε/(2*(K : ℝ))) := mul_le_mul_of_nonneg_left hsmall.le (by positivity)
      _ = _ := by ring
  calc
    ((squareHits N K T).card : ℝ) ≤
        ∑ i ∈ range K, (((Icc T (N+K)).biUnion (fun a =>
          (range N).filter (fun n => n ≠ 0 ∧ a^2 ∣ n+i))).card : ℝ) := by
      exact_mod_cast card_biUnion_le
    _ ≤ ∑ _i ∈ range K, ε / K * N := sum_le_sum hcnt
    _ = _ := by
      simp only [sum_const, card_range, nsmul_eq_mul]
      have hK' : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
      field_simp

private def mediumPrimes (N K : ℕ) : Finset ℕ :=
  (Nat.primesLE N.sqrt).filter (fun p => K ≤ p)

private theorem shift_log_bound {N K T n i : ℕ}
    (hn : n < N) (hn₀ : n ≠ 0) (hi : i < K) (hSq : n ∉ squareHits N K T)
    (hp : ∀ p ∈ (n+i).primeFactors, p ≤ N.sqrt) :
    Real.log (n+i : ℕ) ≤ 2 * Real.log T + Real.log 4 * K +
      ∑ p ∈ mediumPrimes N K, Real.log p * indicator p i n := by
  have hni : 0 < n+i := by omega
  obtain ⟨b, a, hb, ha, hab, hbSq⟩ := Nat.sq_mul_squarefree_of_pos hni
  have haN : a ≤ N+K := by
    have haD : a ∣ n+i := by rw [← hab]; exact dvd_mul_of_dvd_left (dvd_pow_self _ (by decide : 2 ≠ 0)) _
    exact (Nat.le_of_dvd hni haD).trans (by omega)
  have haT : a < T := by
    by_contra! hTa
    apply hSq
    refine mem_biUnion.mpr ⟨i, mem_range.mpr hi, mem_biUnion.mpr ⟨a, mem_Icc.mpr ⟨hTa, haN⟩, ?_⟩⟩
    exact mem_filter.mpr ⟨mem_range.mpr hn, hn₀, ⟨b, hab.symm⟩⟩
  have hbD : b ∣ n+i := ⟨a^2, by rw [← hab, mul_comm]⟩
  have hbp (p : ℕ) (hp' : p ∈ b.primeFactors) :
      p.Prime ∧ p ∣ n+i ∧ p ≤ N.sqrt := by
    obtain ⟨hprime, hdiv, _⟩ := Nat.mem_primeFactors.mp hp'
    have hdvd := hdiv.trans hbD
    exact ⟨hprime, hdvd, hp p (Nat.mem_primeFactors.mpr ⟨hprime, hdvd, hni.ne'⟩)⟩
  have hlb : Real.log b = ∑ p ∈ b.primeFactors, Real.log p := by
    rw [log_factors hb]
    apply sum_congr rfl
    intro p hp
    obtain ⟨hp₁, hp₂, _⟩ := Nat.mem_primeFactors.mp hp
    rw [Nat.factorization_eq_one_of_squarefree hbSq hp₁ hp₂, Nat.cast_one, one_mul]
  have hlarge : (b.primeFactors.filter (fun p => K ≤ p)) ⊆
      (mediumPrimes N K).filter (fun p => p ∣ n+i) := by
    intro p hp
    obtain ⟨hpb, hpK⟩ := mem_filter.mp hp
    obtain ⟨hp₁, hp₂, hp₃⟩ := hbp p hpb
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨hp₃, hp₁⟩, hpK⟩, hp₂⟩
  have hsmall : (b.primeFactors.filter (fun p => ¬ K ≤ p)) ⊆ Nat.primesLE K := by
    intro p hp
    obtain ⟨hpb, hpK⟩ := mem_filter.mp hp
    exact Nat.mem_primesLE.mpr ⟨Nat.le_of_lt (Nat.lt_of_not_ge hpK), (hbp p hpb).1⟩
  have hsmall' := (sum_le_sum_of_subset_of_nonneg hsmall
    (f := fun p : ℕ => Real.log p) (fun p _ _ => Real.log_natCast_nonneg p)).trans (prime_log_sum K)
  have hlarge' := sum_le_sum_of_subset_of_nonneg hlarge
    (f := fun p : ℕ => Real.log p) (fun p _ _ => Real.log_natCast_nonneg p)
  have hfilter : (∑ p ∈ (mediumPrimes N K).filter (fun p => p ∣ n+i), Real.log p) =
      ∑ p ∈ mediumPrimes N K, (if p ∣ n+i then Real.log p else 0) := by rw [sum_filter]
  have hs : (∑ p ∈ mediumPrimes N K, (if p ∣ n+i then Real.log p else 0)) =
      ∑ p ∈ mediumPrimes N K, Real.log p * indicator p i n := by
    apply sum_congr rfl
    intro p _
    by_cases hp₁ : p ∣ n+i <;> simp [indicator, hp₁]
  rw [hfilter, hs] at hlarge'
  rw [← sum_filter_add_sum_filter_not b.primeFactors (fun p => K ≤ p)] at hlb
  have hla : Real.log a ≤ Real.log T :=
    Real.log_le_log (by exact_mod_cast ha) (by exact_mod_cast haT.le)
  have hlog : Real.log (n+i : ℕ) = 2*Real.log a + Real.log b := by
    rw [← hab]
    push_cast
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
    norm_num
  linarith

private theorem medium_harmonic (N K : ℕ) (hN : 1 ≤ N) :
    (∑ p ∈ mediumPrimes N K, Real.log p / (p : ℝ)) ≤ Real.log N/2 + Real.log 4 := by
  have hY : 0 < N.sqrt := Nat.le_sqrt'.mpr (by simpa using hN)
  refine (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun p _ _ =>
    div_nonneg (Real.log_natCast_nonneg p) (by positivity))).trans ?_
  exact (prime_log_harmonic hY).trans (add_le_add_left (sqrt_log N hN) _)

private theorem medium_moment (N K : ℕ) (hN : 1 ≤ N)
    (hlog : 2 * Real.log 4 ≤ Real.log N) :
    (∑ n ∈ range N, signal K (mediumPrimes N K) n ^ 2) ≤
      3 * ((K : ℝ) * Real.log 4)^2 * N + (N : ℝ) * K * Real.log N^2 := by
  have hθ : (∑ p ∈ mediumPrimes N K, Real.log p) ≤ Real.log 4 * Real.sqrt N :=
    ((sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun p _ _ =>
      Real.log_natCast_nonneg p)).trans (prime_log_sum N.sqrt)).trans
        (mul_le_mul_of_nonneg_left (sqrt_nat_cast N) (Real.log_natCast_nonneg 4))
  have hℓ (p : ℕ) (hp : p ∈ mediumPrimes N K) : Real.log p ≤ Real.log N/2 :=
    (Real.log_le_log (by exact_mod_cast (Nat.mem_primesLE.mp (mem_filter.mp hp).1).2.pos)
      (by exact_mod_cast (Nat.mem_primesLE.mp (mem_filter.mp hp).1).1)).trans (sqrt_log N hN)
  have hL : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have h₂ : (∑ p ∈ mediumPrimes N K, (Real.log p)^2 / (p : ℝ)) ≤ Real.log N^2 := by
    calc
      _ ≤ (Real.log N/2) * (∑ p ∈ mediumPrimes N K, Real.log p/(p : ℝ)) := by
        rw [mul_sum]
        apply sum_le_sum
        intro p hp
        rw [show (Real.log p)^2 / (p : ℝ) = Real.log p * (Real.log p / (p : ℝ)) by ring]
        exact mul_le_mul_of_nonneg_right (hℓ p hp)
          (div_nonneg (Real.log_natCast_nonneg p) (by positivity))
      _ ≤ (Real.log N/2) * (Real.log N/2 + Real.log 4) :=
        mul_le_mul_of_nonneg_left (medium_harmonic N K hN) (by positivity)
      _ ≤ Real.log N^2 := by
        have hx := mul_le_mul_of_nonneg_left hlog hL
        nlinarith
  have hP (p : ℕ) (hp : p ∈ mediumPrimes N K) : p.Prime ∧ K ≤ p :=
    ⟨(Nat.mem_primesLE.mp (mem_filter.mp hp).1).2, (mem_filter.mp hp).2⟩
  have hb := moment_bound N K _ hP
  have hθ₁ : 0 ≤ (K : ℝ) * (∑ p ∈ mediumPrimes N K, Real.log p) :=
    mul_nonneg (by positivity) (sum_nonneg fun p _ => Real.log_natCast_nonneg p)
  have hθ₂ : ((K : ℝ) * ∑ p ∈ mediumPrimes N K, Real.log p)^2 ≤
      ((K : ℝ) * Real.log 4)^2 * N := by
    calc
      _ ≤ ((K : ℝ) * (Real.log 4 * Real.sqrt N))^2 :=
        pow_le_pow_left₀ hθ₁ (mul_le_mul_of_nonneg_left hθ (by positivity)) _
      _ = _ := by
        rw [show ((K : ℝ) * (Real.log 4 * Real.sqrt N))^2 =
          ((K : ℝ) * Real.log 4)^2 * (Real.sqrt N)^2 by ring]
        rw [Real.sq_sqrt (by positivity : 0 ≤ (N : ℝ))]
  have hfirst : 3*((K : ℝ)*∑ p ∈ mediumPrimes N K, Real.log p)^2 ≤
      3*((K : ℝ)*Real.log 4)^2*N := by
    simpa only [mul_assoc] using
      (mul_le_mul_of_nonneg_left hθ₂ (show (0 : ℝ) ≤ 3 by norm_num))
  exact hb.trans (add_le_add hfirst
    (mul_le_mul_of_nonneg_left h₂ (show 0 ≤ (N : ℝ)*K by positivity)))

private noncomputable def highSignal (N K : ℕ) : Finset ℕ :=
  (range N).filter (fun n => (K : ℝ) * Real.log N / 4 ≤ signal K (mediumPrimes N K) n)

private theorem high_signal_bound {N K : ℕ} {ε : ℝ} (hN : 1 ≤ N) (hK : 0 < K)
    (hL : 0 < Real.log N) (hlog : 2 * Real.log 4 ≤ Real.log N)
    (hε₁ : 3 * Real.log 4^2 ≤ ε/32 * Real.log N^2) (hε₂ : 1 ≤ ε/32 * K) :
    ((highSignal N K).card : ℝ) ≤ ε * N := by
  let t := (K : ℝ) * Real.log N / 4
  have ht : 0 < t := by dsimp [t]; positivity
  have hlo : ((highSignal N K).card : ℝ)*t^2 ≤
      ∑ n ∈ range N, signal K (mediumPrimes N K) n^2 := by
    calc
      _ = ∑ _n ∈ highSignal N K, t^2 := by simp
      _ ≤ ∑ n ∈ highSignal N K, signal K (mediumPrimes N K) n^2 :=
        sum_le_sum fun n hn => pow_le_pow_left₀ ht.le (mem_filter.mp hn).2 _
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => sq_nonneg _)
  have hhi : (∑ n ∈ range N, signal K (mediumPrimes N K) n^2) ≤ (ε*N)*t^2 := by
    have h₁ := mul_le_mul_of_nonneg_left hε₁ (show 0 ≤ (K : ℝ)^2 * N by positivity)
    have h₂ := mul_le_mul_of_nonneg_left hε₂ (show 0 ≤ (N : ℝ)*K*Real.log N^2 by positivity)
    refine (medium_moment N K hN hlog).trans ?_
    dsimp [t]
    ring_nf at h₁ h₂ ⊢
    linarith
  exact (mul_le_mul_iff_of_pos_right (pow_pos ht _)).mp (hlo.trans hhi)

private theorem prime_at_most_sqrt {n N K i : ℕ} (hn : n < N) (hn₀ : 0 < n)
    (hi : i < K+1) (hbad : n ∉ Erdos1201.Erdos1201Set (1/2 : ℝ) K) :
    ∀ p ∈ (n+i).primeFactors, p ≤ N.sqrt := by
  intro p hp
  let m := ∏ j ∈ range (K+1), (n+j)
  have hm : 0 < m := prod_pos (fun e _ => by omega)
  have hp' := Nat.mem_primeFactors.mp hp
  have hd : p ∣ m := hp'.2.1.trans (dvd_prod_of_mem (fun j => n+j) (mem_range.mpr hi))
  have hbounded : BddAbove {q : ℕ | q.Prime ∧ q ∣ m} :=
    ⟨m, fun q hq => Nat.le_of_dvd hm hq.2⟩
  have hsup : p ≤ sSup {q : ℕ | q.Prime ∧ q ∣ m} := le_csSup hbounded ⟨hp'.1, hd⟩
  have hle : ((sSup {q : ℕ | q.Prime ∧ q ∣ m} : ℕ) : ℝ) ≤ (n : ℝ)^(1-(1/2 : ℝ)) :=
    le_of_not_gt hbad
  have hps : (p : ℝ) ≤ Real.sqrt n := by
    rw [show (1 : ℝ)-1/2 = 1/2 by norm_num, ← Real.sqrt_eq_rpow] at hle
    exact (by exact_mod_cast hsup : (p : ℝ) ≤ _).trans hle
  apply Nat.le_sqrt'.mpr
  have hpow : (p : ℝ)^2 ≤ (n : ℝ) := (Real.le_sqrt (by positivity) (by positivity)).mp hps
  exact (by exact_mod_cast hpow : p^2 ≤ n).trans hn.le

private theorem signal_of_bad {N k n T M : ℕ} (hM : 0 < M)
    (hn : n < N) (hcut : N ≤ M*n) (hSq : n ∉ squareHits N (k+1) T)
    (hbad : n ∉ Erdos1201.Erdos1201Set (1/2 : ℝ) k)
    (hbig : 4 * (2 * Real.log T + Real.log 4 * ((k+1 : ℕ) : ℝ) + Real.log M + Real.log 4) ≤
      Real.log N) :
    n ∈ highSignal N (k+1) := by
  have hN : 1 ≤ N := by omega
  have hn₀ : 0 < n := by
    by_contra! h
    have hnz : n = 0 := by omega
    simp [hnz] at hcut
    omega
  have hlogn : Real.log N ≤ Real.log M + Real.log n := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    apply Real.log_le_log (by exact_mod_cast hN)
    exact_mod_cast hcut
  let K := k+1
  let P := mediumPrimes N K
  let μ := ∑ p ∈ P, Real.log p / (p : ℝ)
  have hμ : μ ≤ Real.log N/2 + Real.log 4 := medium_harmonic N K hN
  have hsignal : signal K P n = ∑ i ∈ range K,
      ((∑ p ∈ P, Real.log p * indicator p i n) - μ) := by
    rw [signal, sum_product]
    apply sum_congr rfl
    intro i hi
    simp [centered, mul_sub, sum_sub_distrib, μ, div_eq_mul_inv]
  refine mem_filter.mpr ⟨mem_range.mpr hn, ?_⟩
  change (K : ℝ) * Real.log N/4 ≤ signal K P n
  rw [hsignal, show (K : ℝ)*Real.log N/4 = ∑ _i ∈ range K, Real.log N/4 by simp; ring]
  apply sum_le_sum
  intro i hi
  have hi' : i < k+1 := mem_range.mp hi
  have hshift := shift_log_bound hn hn₀.ne' hi' hSq (prime_at_most_sqrt hn hn₀ hi' hbad)
  have hmono : Real.log n ≤ Real.log (n+i : ℕ) :=
    Real.log_le_log (by exact_mod_cast hn₀) (by exact_mod_cast (Nat.le_add_right n i))
  dsimp [P, K]
  linarith

open scoped Classical in
private theorem interval_count {η : ℝ} (hη : 0 < η) :
    ∃ k : ℕ, ∀ᶠ N : ℕ in atTop,
      1-η ≤ (Nat.count (· ∈ Erdos1201.Erdos1201Set (1/2 : ℝ) k) N : ℝ) / N := by
  classical
  let ε := η/4
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨k, hk⟩ := exists_nat_gt (32/ε)
  let K := k+1
  have hK : 0 < K := by dsimp [K]; omega
  have hK' : 1 ≤ ε/32*(K : ℝ) := by
    have hk' := (div_lt_iff₀ hε).mp hk
    have hcast : (k : ℝ) ≤ (K : ℝ) := by exact_mod_cast (Nat.le_succ k)
    have hmul := mul_le_mul_of_nonneg_left hcast hε.le
    linarith
  obtain ⟨m, hm⟩ := exists_nat_gt (2/ε)
  let M := m+1
  have hM : 0 < M := by dsimp [M]; omega
  have hM' : 2 ≤ ε * (M : ℝ) := by
    have hm' := (div_lt_iff₀ hε).mp hm
    have hcast : (m : ℝ) ≤ (M : ℝ) := by exact_mod_cast (Nat.le_succ m)
    have hmul := mul_le_mul_of_nonneg_left hcast hε.le
    linarith
  obtain ⟨T, _, hSq⟩ := square_hits_bound hK hε
  let C := 2*Real.log T + Real.log 4 * (K : ℝ) + Real.log M + Real.log 4
  let L := max 1 (max (2*Real.log 4) (max (4*C) (96*(Real.log 4)^2/ε)))
  have hL : ∀ᶠ N : ℕ in atTop, L ≤ Real.log N :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop L
  have hNε : ∀ᶠ N : ℕ in atTop, (2 : ℝ)/ε ≤ (N : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop _
  refine ⟨k, ?_⟩
  filter_upwards [eventually_ge_atTop K, hL, hNε] with N hN hlog hnε
  have hN₁ : 1 ≤ N := hK.trans_le hN
  have hN' : 0 < (N : ℝ) := by exact_mod_cast hN₁
  have hlog₁ : 1 ≤ Real.log N := (le_max_left _ _).trans hlog
  have hlog₂ : 2 * Real.log 4 ≤ Real.log N :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hlog)
  have hlog₃ : 4*C ≤ Real.log N :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hlog))
  have hlog₄ : 96*(Real.log 4)^2/ε ≤ Real.log N :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hlog))
  have hE : 3 * Real.log 4^2 ≤ ε/32 * Real.log N^2 := by
    have h₁ := (div_le_iff₀ hε).mp hlog₄
    have h₂ : Real.log N ≤ Real.log N^2 := by nlinarith
    have h₃ := mul_le_mul_of_nonneg_left h₂ hε.le
    linarith
  let bad := (range N).filter (fun n => n ∉ Erdos1201.Erdos1201Set (1/2 : ℝ) k)
  let small := (range N).filter (fun n => ¬N ≤ M*n)
  have hsmall : (small.card : ℝ) ≤ ε*N := by
    have hsub : small ⊆ range (N/M+1) := by
      intro n hn
      have hh := (mem_filter.mp hn).2
      apply mem_range.mpr
      apply Nat.lt_succ_of_le
      exact (Nat.le_div_iff_mul_le hM).mpr (by rw [mul_comm]; omega)
    have hn₁ := (div_le_iff₀ hε).mp hnε
    have hdiv : (N : ℝ)/M ≤ (ε/2)*N := by
      apply (div_le_iff₀ (by exact_mod_cast hM : 0 < (M : ℝ))).mpr
      have hh := mul_le_mul_of_nonneg_right hM' (show 0 ≤ (N : ℝ)/2 by positivity)
      linarith
    have hcard : (small.card : ℝ) ≤ ((N/M : ℕ) : ℝ) + 1 := by
      exact_mod_cast (card_le_card hsub).trans_eq (card_range _)
    linarith [cast_div_le N M hM]
  have hcover : bad ⊆ small ∪ (squareHits N K T ∪ highSignal N K) := by
    intro n hn
    obtain ⟨hnN, hbad⟩ := mem_filter.mp hn
    by_cases hcut : N ≤ M*n
    · by_cases hhit : n ∈ squareHits N K T
      · exact mem_union_right _ (mem_union_left _ hhit)
      · exact mem_union_right _ (mem_union_right _ (signal_of_bad hM (mem_range.mp hnN)
          hcut hhit hbad hlog₃))
    · exact mem_union_left _ (mem_filter.mpr ⟨hnN, hcut⟩)
  have hbad : (bad.card : ℝ) ≤ η*N := by
    have hb : (bad.card : ℝ) ≤ (small.card : ℝ) + (squareHits N K T).card + (highSignal N K).card := by
      exact_mod_cast (show bad.card ≤ small.card + (squareHits N K T).card + (highSignal N K).card from by
        have h₁ := (card_le_card hcover).trans (card_union_le _ _)
        have h₂ := card_union_le (squareHits N K T) (highSignal N K)
        omega)
    have hh := high_signal_bound hN₁ hK (by linarith) hlog₂ hE hK'
    have hηN := mul_nonneg hη.le hN'.le
    dsimp [ε] at hsmall hh
    have hs := hSq N hN
    dsimp [ε] at hs
    linarith
  rw [Nat.count_eq_card_filter_range, le_div_iff₀ hN']
  have hcard : (((range N).filter (· ∈ Erdos1201.Erdos1201Set (1/2 : ℝ) k)).card : ℝ) +
      bad.card = (N : ℝ) := by
    exact_mod_cast (card_filter_add_card_filter_not (s := range N)
      (· ∈ Erdos1201.Erdos1201Set (1/2 : ℝ) k)).trans (card_range _)
  nlinarith

end HalfPrime

theorem OMA.half : type_of% @Erdos1201.erdos_1201.variants.epsilon_half := by
  classical
  intro η hη
  by_cases ht : η = ⊤
  · subst η
    exact ⟨0, by simp [EReal.sub_top]⟩
  have hb : η ≠ ⊥ := ne_bot_of_gt hη
  lift η to ℝ using ⟨ht, hb⟩
  have hη' : 0 < η := by exact_mod_cast hη
  obtain ⟨k, hk⟩ := HalfPrime.interval_count hη'
  refine ⟨k, le_liminf_of_le (h := ?_)⟩
  filter_upwards [hk] with N hN
  exact EReal.coe_le_coe hN
namespace OMA1201
open Filter Erdos1201 Nat

theorem set_mono {ε : ℝ} (hε : 1 / 2 ≤ ε) (k : ℕ) :
    Erdos1201Set (1 / 2 : ℝ) k ⊆ Erdos1201Set ε k := by
  intro n hn
  simp only [Erdos1201Set, Set.mem_ofPred_eq, gt_iff_lt] at hn ⊢
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · exfalso
    have : ((0 : ℕ) : ℝ) ^ (1 - (1 / 2 : ℝ)) = 0 := by
      rw [Nat.cast_zero]; exact Real.zero_rpow (by norm_num)
    rw [this] at hn
    have hS : sSup {p : ℕ | p.Prime ∧ p ∣ ∏ i ∈ Finset.range (k + 1), (0 + i)} = 0 := by
      have hz : ∏ i ∈ Finset.range (k + 1), (0 + i) = 0 :=
        Finset.prod_eq_zero (Finset.mem_range.2 (Nat.succ_pos k)) (by simp)
      rw [hz]
      apply Nat.sSup_of_not_bddAbove
      rintro ⟨b, hb⟩
      obtain ⟨p, hp1, hp2⟩ := Nat.exists_infinite_primes (b + 1)
      have := hb ⟨hp2, dvd_zero p⟩
      omega
    rw [hS] at hn
    simp at hn
  · have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hpos
    exact lt_of_le_of_lt (Real.rpow_le_rpow_of_exponent_le h1 (by linarith)) hn

open scoped Classical in
theorem from_half (half : type_of% @Erdos1201.erdos_1201.variants.epsilon_half) :
    ∀ ε : ℝ, 1 / 2 ≤ ε → ∀ η > 0, ∃ k : ℕ,
      atTop.liminf (fun x : ℕ ↦
        (((count (· ∈ Erdos1201Set ε k) x : ℝ) / (x : ℝ)) : EReal)) ≥ (1 - η : EReal) := by
  intro ε hε η hη
  obtain ⟨k, hk⟩ := half η hη
  refine ⟨k, le_trans hk (Filter.liminf_le_liminf (Filter.Eventually.of_forall fun x => ?_))⟩
  apply EReal.coe_le_coe_iff.2
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg x)
  rw [Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range]
  exact_mod_cast Finset.card_le_card (Finset.monotone_filter_right _ fun n _ hn => set_mono hε k hn)

end OMA1201

theorem OMA.solution : OMA.R_Erdos1201_erdos_1201_R1.H1 := OMA1201.from_half OMA.half
