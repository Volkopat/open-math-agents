import OMAStatements.S_oeis_a382124
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Tactic

namespace OMA.P_oeis_a382124

open OMA.S_oeis_a382124

/-- Cauchy convolution of two sequences over `ℚ`. -/
private def convQ (f g : ℕ → ℚ) (n : ℕ) : ℚ :=
  ∑ i ∈ Finset.range (n + 1), f i * g (n - i)

/-- Cauchy convolution of two sequences over `ℕ`. -/
private def convN (f g : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (n + 1), f i * g (n - i)

private lemma convQ_cast (f g : ℕ → ℕ) (n : ℕ) :
    convQ (fun k => (f k : ℚ)) (fun k => (g k : ℚ)) n = (convN f g n : ℚ) := by
  unfold convQ convN
  push_cast
  rfl

private lemma expLogSeq_succ_Icc (u : ℕ → ℚ) (n : ℕ) :
    expLogSeq u (n + 1) =
      (∑ k ∈ Finset.Icc 1 (n + 1), u k * expLogSeq u (n + 1 - k)) / ((n + 1 : ℕ) : ℚ) := by
  rw [expLogSeq]
  congr 1
  apply Finset.sum_bij (fun k _ => k + 1)
  · intro k hk; rw [Finset.mem_range] at hk; rw [Finset.mem_Icc]; omega
  · intro k1 _ k2 _ heq; omega
  · intro j hj; rw [Finset.mem_Icc] at hj
    exact ⟨j - 1, Finset.mem_range.mpr (by omega), by omega⟩
  · intro k _
    rw [show n + 1 - (k + 1) = n - k by omega]

/-- `expLogSeq u n` only depends on `u k` for `1 ≤ k ≤ n`. -/
private lemma expLogSeq_congr {u v : ℕ → ℚ} (n : ℕ)
    (h : ∀ k, 1 ≤ k → k ≤ n → u k = v k) :
    expLogSeq u n = expLogSeq v n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [expLogSeq]
    | succ m =>
      rw [expLogSeq_succ_Icc, expLogSeq_succ_Icc]
      congr 1
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mem_Icc] at hk
      rw [h k hk.1 hk.2, ih (m + 1 - k) (by omega) (fun j hj1 hj2 => h j hj1 (by omega))]

/-- Helper for `expLogSeq_conv`: shifting the `k`-weighted sum. -/
private lemma sum_weighted_conv (u : ℕ → ℚ) (g : ℕ → ℚ) (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), ((i : ℚ) * expLogSeq u i) * g (n - i) =
      ∑ k ∈ Finset.Icc 1 n, u k * convQ (expLogSeq u) g (n - k) := by
  have h1 : ∑ i ∈ Finset.range (n + 1), ((i : ℚ) * expLogSeq u i) * g (n - i) =
      ∑ i ∈ Finset.Icc 1 n,
        (∑ k ∈ Finset.Icc 1 i, u k * expLogSeq u (i - k)) * g (n - i) := by
    rw [Finset.sum_range_succ']
    simp only [Nat.cast_zero, zero_mul, add_zero]
    symm
    apply Finset.sum_bij (fun i _ => i - 1)
    · intro i hi; rw [Finset.mem_Icc] at hi; rw [Finset.mem_range]; omega
    · intro i1 h1 i2 h2 heq; rw [Finset.mem_Icc] at h1 h2; omega
    · intro j hj; rw [Finset.mem_range] at hj
      exact ⟨j + 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
    · intro i hi
      rw [Finset.mem_Icc] at hi
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
      simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel]
      have hmul : ((m + 1 : ℕ) : ℚ) * expLogSeq u (m + 1) =
          ∑ k ∈ Finset.Icc 1 (m + 1), u k * expLogSeq u (m + 1 - k) := by
        rw [expLogSeq_succ_Icc]
        have hnz : ((m + 1 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        field_simp
      rw [hmul]
  rw [h1]
  have h2 : ∑ i ∈ Finset.Icc 1 n,
        (∑ k ∈ Finset.Icc 1 i, u k * expLogSeq u (i - k)) * g (n - i) =
      ∑ i ∈ Finset.Icc 1 n, ∑ k ∈ Finset.Icc 1 n,
        if k ≤ i then u k * expLogSeq u (i - k) * g (n - i) else 0 := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_Icc] at hi
    rw [Finset.sum_mul, ← Finset.sum_filter]
    congr 1; ext k; simp only [Finset.mem_Icc, Finset.mem_filter]; omega
  rw [h2, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_Icc] at hk
  rw [← Finset.sum_filter]
  have hfilt : (Finset.Icc 1 n).filter (fun i => k ≤ i) = Finset.Icc k n := by
    ext i; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
  rw [hfilt]
  unfold convQ
  rw [Finset.mul_sum]
  symm
  apply Finset.sum_bij (fun r _ => k + r)
  · intro r hr; rw [Finset.mem_range] at hr; rw [Finset.mem_Icc]; omega
  · intro r1 _ r2 _ heq; omega
  · intro i hi; rw [Finset.mem_Icc] at hi
    exact ⟨i - k, Finset.mem_range.mpr (by omega), by omega⟩
  · intro r hr
    rw [Finset.mem_range] at hr
    rw [show k + r - k = r by omega, show n - (k + r) = n - k - r by omega]
    ring

private lemma convQ_comm (f g : ℕ → ℚ) (n : ℕ) : convQ f g n = convQ g f n := by
  unfold convQ
  apply Finset.sum_bij (fun i _ => n - i)
  · intro i hi; rw [Finset.mem_range] at hi ⊢; omega
  · intro i1 h1 i2 h2 heq; rw [Finset.mem_range] at h1 h2; omega
  · intro j hj; rw [Finset.mem_range] at hj
    exact ⟨n - j, Finset.mem_range.mpr (by omega), by omega⟩
  · intro i hi; rw [Finset.mem_range] at hi
    rw [show n - (n - i) = i by omega, mul_comm]

/-- Key multiplication identity for `expLogSeq`:
`convQ (expLogSeq u) (expLogSeq v) = expLogSeq (u + v)`. -/
private lemma expLogSeq_conv (u v : ℕ → ℚ) :
    ∀ n : ℕ, convQ (expLogSeq u) (expLogSeq v) n = expLogSeq (fun k => u k + v k) n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [convQ, expLogSeq]
    | succ m =>
      have hnz : ((m + 1 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      suffices hmul : ((m + 1 : ℕ) : ℚ) * convQ (expLogSeq u) (expLogSeq v) (m + 1) =
          ∑ k ∈ Finset.Icc 1 (m + 1), (u k + v k) * expLogSeq (fun j => u j + v j) (m + 1 - k) by
        rw [expLogSeq_succ_Icc]
        rw [eq_div_iff hnz, mul_comm]
        exact hmul
      have hsplit : ((m + 1 : ℕ) : ℚ) * convQ (expLogSeq u) (expLogSeq v) (m + 1) =
          (∑ i ∈ Finset.range (m + 2), ((i : ℚ) * expLogSeq u i) * expLogSeq v (m + 1 - i)) +
          (∑ i ∈ Finset.range (m + 2), ((i : ℚ) * expLogSeq v i) * expLogSeq u (m + 1 - i)) := by
        have hrev : ∑ i ∈ Finset.range (m + 2), ((i : ℚ) * expLogSeq v i) * expLogSeq u (m + 1 - i) =
            ∑ i ∈ Finset.range (m + 2), expLogSeq u i * (((m + 1 - i : ℕ) : ℚ) * expLogSeq v (m + 1 - i)) := by
          apply Finset.sum_bij (fun i _ => m + 1 - i)
          · intro i hi; rw [Finset.mem_range] at hi ⊢; omega
          · intro i1 h1 i2 h2 heq; rw [Finset.mem_range] at h1 h2; omega
          · intro j hj; rw [Finset.mem_range] at hj
            exact ⟨m + 1 - j, Finset.mem_range.mpr (by omega), by omega⟩
          · intro i hi; rw [Finset.mem_range] at hi
            rw [show m + 1 - (m + 1 - i) = i by omega]; ring
        rw [hrev, ← Finset.sum_add_distrib]
        unfold convQ
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mem_range] at hi
        have hadd : ((i : ℕ) : ℚ) + ((m + 1 - i : ℕ) : ℚ) = ((m + 1 : ℕ) : ℚ) := by
          exact_mod_cast (show i + (m + 1 - i) = m + 1 by omega)
        calc ((m + 1 : ℕ) : ℚ) * (expLogSeq u i * expLogSeq v (m + 1 - i))
            = (((i : ℕ) : ℚ) + ((m + 1 - i : ℕ) : ℚ)) * (expLogSeq u i * expLogSeq v (m + 1 - i)) := by
                rw [hadd]
          _ = ((i : ℚ) * expLogSeq u i) * expLogSeq v (m + 1 - i) +
                expLogSeq u i * (((m + 1 - i : ℕ) : ℚ) * expLogSeq v (m + 1 - i)) := by ring
      rw [hsplit, sum_weighted_conv u (expLogSeq v) (m + 1), sum_weighted_conv v (expLogSeq u) (m + 1)]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mem_Icc] at hk
      rw [convQ_comm (expLogSeq v) (expLogSeq u) (m + 1 - k)]
      rw [ih (m + 1 - k) (by omega)]
      ring

/-- Indicator sequence `1_{d ∣ n}` is `expLogSeq` of `k ↦ if d ∣ k then d else 0`. -/
private lemma expLogSeq_dvd_ind (d : ℕ) (hd : 1 ≤ d) :
    ∀ n : ℕ, expLogSeq (fun k => if d ∣ k then (d : ℚ) else 0) n = if d ∣ n then 1 else 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [expLogSeq]
    | succ m =>
      rw [expLogSeq_succ_Icc]
      have hnz : ((m + 1 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      rw [div_eq_iff hnz]
      have hsub : ∑ k ∈ Finset.Icc 1 (m + 1),
            (if d ∣ k then (d : ℚ) else 0) * expLogSeq (fun j => if d ∣ j then (d : ℚ) else 0) (m + 1 - k) =
          ∑ k ∈ Finset.Icc 1 (m + 1),
            (if d ∣ k then (d : ℚ) else 0) * (if d ∣ (m + 1 - k) then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [Finset.mem_Icc] at hk
        rw [ih (m + 1 - k) (by omega)]
      rw [hsub]
      by_cases hdiv : d ∣ m + 1
      · rw [if_pos hdiv, one_mul]
        rcases hdiv with ⟨q, hq⟩
        have hsum : ∑ k ∈ Finset.Icc 1 (m + 1),
              (if d ∣ k then (d : ℚ) else 0) * (if d ∣ (m + 1 - k) then 1 else 0) =
            ∑ j ∈ Finset.Icc 1 q, (d : ℚ) := by
          have hite : ∀ k : ℕ,
              (if d ∣ k then (d : ℚ) else 0) * (if d ∣ (m + 1 - k) then 1 else 0) =
                if d ∣ k then ((d : ℚ) * if d ∣ (m + 1 - k) then 1 else 0) else 0 := by
            intro k; by_cases hdk : d ∣ k <;> simp [hdk]
          rw [Finset.sum_congr rfl (fun k _ => hite k), ← Finset.sum_filter (p := fun k => d ∣ k)]
          have hfilt_eq : ∑ k ∈ (Finset.Icc 1 (m + 1)).filter (fun k => d ∣ k),
                ((d : ℚ) * if d ∣ (m + 1 - k) then 1 else 0) =
              ∑ k ∈ (Finset.Icc 1 (m + 1)).filter (fun k => d ∣ k), (d : ℚ) := by
            apply Finset.sum_congr rfl
            intro k hk
            rw [Finset.mem_filter, Finset.mem_Icc] at hk
            have hdsub : d ∣ m + 1 - k := Nat.dvd_sub (⟨q, hq⟩) hk.2
            simp [hdsub]
          rw [hfilt_eq]
          symm
          apply Finset.sum_bij (fun j _ => d * j)
          · intro j hj; rw [Finset.mem_Icc] at hj
            rw [Finset.mem_filter, Finset.mem_Icc]
            exact ⟨⟨by nlinarith, by nlinarith⟩, dvd_mul_right d j⟩
          · intro j1 _ j2 _ heq; exact Nat.eq_of_mul_eq_mul_left (by omega) heq
          · intro k hk; rw [Finset.mem_filter, Finset.mem_Icc] at hk
            rcases hk.2 with ⟨j, rfl⟩
            exact ⟨j, Finset.mem_Icc.mpr ⟨by nlinarith, by nlinarith⟩, rfl⟩
          · intro _ _; rfl
        rw [hsum, Finset.sum_const, Nat.card_Icc, show q + 1 - 1 = q by omega, nsmul_eq_mul]
        exact_mod_cast (show (q * d : ℕ) = m + 1 by nlinarith)
      · rw [if_neg hdiv, zero_mul]
        apply Finset.sum_eq_zero
        intro k hk
        rw [Finset.mem_Icc] at hk
        by_cases hdk : d ∣ k
        · have hnd : ¬ d ∣ m + 1 - k := fun hsub_dvd => by
            have hadd := Nat.dvd_add hdk hsub_dvd
            rw [show k + (m + 1 - k) = m + 1 by omega] at hadd
            exact hdiv hadd
          simp [hdk, hnd]
        · simp [hdk]

/-- Iterated integer-valued `expLogSeq` for `c * d * 1_{d ∣ k}`. -/
private lemma expLogSeq_nat_single (d c : ℕ) (hd : 1 ≤ d) :
    ∃ f : ℕ → ℕ, ∀ n, expLogSeq (fun k => if d ∣ k then ((d * c : ℕ) : ℚ) else 0) n = (f n : ℚ) := by
  induction c with
  | zero =>
    refine ⟨fun n => if n = 0 then 1 else 0, ?_⟩
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      cases n with
      | zero => simp [expLogSeq]
      | succ m =>
        simp [expLogSeq]
  | succ c ih =>
    rcases ih with ⟨f, hf⟩
    refine ⟨convN f (fun n => if d ∣ n then 1 else 0), ?_⟩
    intro n
    rw [← convQ_cast]
    have h1 : convQ (fun k => (f k : ℚ)) (fun k => ((if d ∣ k then 1 else 0 : ℕ) : ℚ)) n =
        convQ (expLogSeq (fun k => if d ∣ k then ((d * c : ℕ) : ℚ) else 0))
              (expLogSeq (fun k => if d ∣ k then (d : ℚ) else 0)) n := by
      unfold convQ
      apply Finset.sum_congr rfl
      intro i _
      rw [hf i, expLogSeq_dvd_ind d hd (n - i)]
      by_cases hdiv : d ∣ n - i <;> simp [hdiv]
    rw [h1, expLogSeq_conv]
    apply expLogSeq_congr n
    intro k _ _
    by_cases hdk : d ∣ k
    · simp only [if_pos hdk]; push_cast; ring
    · simp [hdk]

/-- Any finite Euler product with `ℕ` exponents has `ℕ` coefficients. -/
private lemma expLogSeq_euler_nat (c : ℕ → ℕ) (N : ℕ) :
    ∃ f : ℕ → ℕ, ∀ n,
      expLogSeq (fun k => ∑ d ∈ Finset.Icc 1 N, if d ∣ k then ((d * c d : ℕ) : ℚ) else 0) n = (f n : ℚ) := by
  induction N with
  | zero =>
    refine ⟨fun n => if n = 0 then 1 else 0, ?_⟩
    intro n
    cases n with
    | zero => simp [expLogSeq]
    | succ m => simp [expLogSeq]
  | succ N ih =>
    rcases ih with ⟨f, hf⟩
    rcases expLogSeq_nat_single (N + 1) (c (N + 1)) (by omega) with ⟨g, hg⟩
    refine ⟨convN f g, ?_⟩
    intro n
    rw [← convQ_cast]
    have h1 : convQ (fun k => (f k : ℚ)) (fun k => (g k : ℚ)) n =
        convQ (expLogSeq (fun k => ∑ d ∈ Finset.Icc 1 N, if d ∣ k then ((d * c d : ℕ) : ℚ) else 0))
              (expLogSeq (fun k => if N + 1 ∣ k then (((N + 1) * c (N + 1) : ℕ) : ℚ) else 0)) n := by
      unfold convQ
      apply Finset.sum_congr rfl
      intro i _
      rw [hf i, hg (n - i)]
    rw [h1, expLogSeq_conv]
    apply expLogSeq_congr n
    intro k _ _
    have hIcc : Finset.Icc 1 (N + 1) = insert (N + 1) (Finset.Icc 1 N) := by
      ext d; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hnot : N + 1 ∉ Finset.Icc 1 N := by simp
    rw [hIcc, Finset.sum_insert hnot, add_comm]

/-- Prime-power Euler exponent `c_{p^k}` for `A382124`. -/
private def cPP (p k : ℕ) : ℕ :=
  if k = 0 then 1
  else if p = 2 then 2 ^ (k + 1) - 1
  else (∑ i ∈ Finset.range (k + 1), p ^ i) + (∑ i ∈ Finset.range k, p ^ i)

/-- Explicit multiplicative Euler exponent `c(n)` for `A382124`. -/
private def cSeq (n : ℕ) : ℕ :=
  if n = 0 then 0 else ∏ p ∈ n.primeFactors, cPP p (n.factorization p)

private lemma sigma_eq_arith (n : ℕ) : sigma n = ArithmeticFunction.sigma 1 n := by
  unfold sigma; simp [ArithmeticFunction.sigma_apply]

private lemma sigma_prime_pow (p k : ℕ) (hp : p.Prime) :
    sigma (p ^ k) = ∑ i ∈ Finset.range (k + 1), p ^ i := by
  rw [sigma_eq_arith]
  simpa using ArithmeticFunction.sigma_apply_prime_pow (k := 1) hp (i := k)

private lemma sigma_two_pow (k : ℕ) : sigma (2 ^ k) = 2 ^ (k + 1) - 1 := by
  rw [sigma_prime_pow 2 k Nat.prime_two]
  have h : (∑ i ∈ Finset.range (k + 1), 2 ^ i) + 1 = 2 ^ (k + 1) := by
    induction k with
    | zero => simp
    | succ k ih => rw [Finset.sum_range_succ]; omega
  omega

private lemma cSeq_one : cSeq 1 = 1 := by simp [cSeq]

private lemma cSeq_prime_pow (p k : ℕ) (hp : p.Prime) :
    cSeq (p ^ k) = cPP p k := by
  cases k with
  | zero => simp [cSeq, cPP]
  | succ k' =>
    unfold cSeq
    have hnz : p ^ (k' + 1) ≠ 0 := pow_ne_zero _ hp.ne_zero
    rw [if_neg hnz, Nat.primeFactors_pow p (by omega), hp.primeFactors, Finset.prod_singleton,
        hp.factorization_pow, Finsupp.single_eq_same]

private lemma cSeq_mul_coprime {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hcop : Nat.Coprime a b) :
    cSeq (a * b) = cSeq a * cSeq b := by
  unfold cSeq
  rw [if_neg (mul_ne_zero ha hb), if_neg ha, if_neg hb]
  rw [Nat.primeFactors_mul ha hb, Finset.prod_union hcop.disjoint_primeFactors]
  congr 1
  · apply Finset.prod_congr rfl
    intro p hp
    have hnp : p ∉ b.primeFactors := Finset.disjoint_left.mp hcop.disjoint_primeFactors hp
    have hfb : b.factorization p = 0 := by
      by_contra hne
      exact hnp (by simpa [Nat.support_factorization] using Finsupp.mem_support_iff.mpr hne)
    rw [Nat.factorization_mul ha hb, Finsupp.coe_add, Pi.add_apply, hfb, add_zero]
  · apply Finset.prod_congr rfl
    intro p hp
    have hnp : p ∉ a.primeFactors := Finset.disjoint_right.mp hcop.disjoint_primeFactors hp
    have hfa : a.factorization p = 0 := by
      by_contra hne
      exact hnp (by simpa [Nat.support_factorization] using Finsupp.mem_support_iff.mpr hne)
    rw [Nat.factorization_mul ha hb, Finsupp.coe_add, Pi.add_apply, hfa, zero_add]

private lemma sum_div_two_pow (k : ℕ) :
    3 * (∑ d ∈ (2 ^ k).divisors, d * cSeq d) = sigma (2 ^ k) * sigma (2 * 2 ^ k) := by
  rw [Nat.divisors_prime_pow Nat.prime_two, Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk]
  have h1 : ∀ m : ℕ, ∑ j ∈ Finset.range (m + 1), 2 ^ j * cSeq (2 ^ j) =
      ∑ j ∈ Finset.range (m + 1), 2 ^ j * cPP 2 j := fun m =>
    Finset.sum_congr rfl (fun j _ => by rw [cSeq_prime_pow 2 j Nat.prime_two])
  rw [h1 k, show 2 * 2 ^ k = 2 ^ (k + 1) by ring, sigma_two_pow k, sigma_two_pow (k + 1)]
  clear h1
  induction k with
  | zero => simp [cPP]
  | succ k ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    have hcpp : cPP 2 (k + 1) = 2 ^ (k + 2) - 1 := by simp [cPP]
    rw [hcpp]
    have hge1 : 1 ≤ 2 ^ (k + 1) := Nat.one_le_pow _ _ (by decide)
    have hge2 : 1 ≤ 2 ^ (k + 2) := Nat.one_le_pow _ _ (by decide)
    have hge3 : 1 ≤ 2 ^ (k + 3) := Nat.one_le_pow _ _ (by decide)
    zify [hge1, hge2, hge3]
    ring

private lemma sum_div_odd_prime_pow (p k : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    3 * (∑ d ∈ (p ^ k).divisors, d * cSeq d) = sigma (p ^ k) * sigma (2 * p ^ k) := by
  have hcop2 : Nat.Coprime 2 (p ^ k) :=
    (Nat.prime_two.coprime_iff_not_dvd.mpr (fun hd => hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp hd).symm)).pow_right k
  have hsig2 : sigma (2 * p ^ k) = 3 * sigma (p ^ k) := by
    rw [sigma_eq_arith, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop2,
        ← sigma_eq_arith, ← sigma_eq_arith]
    have hs2 : sigma 2 = 3 := by decide
    rw [hs2]
  rw [hsig2]
  suffices hsq : ∑ d ∈ (p ^ k).divisors, d * cSeq d = sigma (p ^ k) ^ 2 by
    rw [hsq]; ring
  rw [Nat.divisors_prime_pow hp, Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk]
  have h1 : ∑ j ∈ Finset.range (k + 1), p ^ j * cSeq (p ^ j) =
      ∑ j ∈ Finset.range (k + 1), p ^ j * cPP p j :=
    Finset.sum_congr rfl (fun j _ => by rw [cSeq_prime_pow p j hp])
  rw [h1]
  clear hcop2 hsig2 h1
  induction k with
  | zero =>
    rw [sigma_prime_pow p 0 hp]
    simp [cPP]
  | succ k ih =>
    rw [Finset.sum_range_succ, ih, sigma_prime_pow p (k + 1) hp, sigma_prime_pow p k hp]
    have hcpp : cPP p (k + 1) =
        (∑ i ∈ Finset.range (k + 2), p ^ i) + (∑ i ∈ Finset.range (k + 1), p ^ i) := by
      simp [cPP, hp2]
    rw [hcpp, Finset.sum_range_succ (fun i => p ^ i) (k + 1)]
    ring

/-- Core identity: `3 * ∑_{d ∣ n} d * cSeq d = σ(n) * σ(2n)` for every `n ≥ 1`. -/
private lemma three_mul_sum_div_cSeq :
    ∀ n : ℕ, 1 ≤ n → 3 * (∑ d ∈ n.divisors, d * cSeq d) = sigma n * sigma (2 * n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    by_cases hn1 : n = 1
    · subst hn1
      have h1 : sigma 1 = 1 := by decide
      have h2 : sigma 2 = 3 := by decide
      simp [cSeq_one, h1, h2]
    · set p := n.minFac
      have hp : p.Prime := Nat.minFac_prime hn1
      set k := n.factorization p
      have hk_pos : 1 ≤ k := Nat.pos_of_ne_zero (by
        intro h0
        have hdvd : p ∣ n := Nat.minFac_dvd n
        have := (hp.dvd_iff_one_le_factorization (by omega)).mp hdvd
        omega)
      set m := n / p ^ k
      have hpk_dvd : p ^ k ∣ n := Nat.ordProj_dvd n p
      have hnm : p ^ k * m = n := Nat.mul_div_cancel' hpk_dvd
      have hm_pos : 1 ≤ m := by
        rcases Nat.eq_zero_or_pos m with hm0 | hpos
        · rw [hm0, mul_zero] at hnm; omega
        · exact hpos
      have hcop : Nat.Coprime (p ^ k) m := by
        have hnot : ¬ p ∣ m := by
          intro hpm
          have hdvd1 : p ^ (k + 1) ∣ n := by
            rcases hpm with ⟨r, hr⟩
            exact ⟨r, by rw [← hnm, hr]; ring⟩
          have hle := (hp.pow_dvd_iff_le_factorization (by omega)).mp hdvd1
          omega
        exact (hp.coprime_iff_not_dvd.mpr hnot).pow_left k
      by_cases hm1 : m = 1
      · have hnpk : n = p ^ k := by rw [← hnm, hm1, mul_one]
        rw [hnpk]
        by_cases hp2 : p = 2
        · rw [hp2]; exact sum_div_two_pow k
        · exact sum_div_odd_prime_pow p k hp hp2
      · have hpk_gt1 : 1 < p ^ k := one_lt_pow₀ hp.one_lt (by omega)
        have hm2 : 2 ≤ m := by omega
        have hpk_lt : p ^ k < n := by nlinarith
        have hm_lt : m < n := by nlinarith
        have h1 := ih (p ^ k) hpk_lt (by omega)
        have h2 := ih m hm_lt hm_pos
        -- Multiplicativity of sum_{d|n} d * cSeq d
        have hsum_mul : ∑ d ∈ n.divisors, d * cSeq d =
            (∑ d ∈ (p ^ k).divisors, d * cSeq d) * (∑ d ∈ m.divisors, d * cSeq d) := by
          have hdiv_eq : (p ^ k * m).divisors =
              ((p ^ k).divisors ×ˢ m.divisors).image (fun x => x.1 * x.2) := by
            ext d
            simp only [Nat.mem_divisors, Finset.mem_image, Finset.mem_product, Prod.exists]
            constructor
            · rintro ⟨hd, hnz⟩
              refine ⟨Nat.gcd d (p ^ k), Nat.gcd d m,
                ⟨⟨Nat.gcd_dvd_right d (p ^ k), by positivity⟩,
                 ⟨Nat.gcd_dvd_right d m, by omega⟩⟩, ?_⟩
              have hmul_gcd : Nat.gcd d (p ^ k) * Nat.gcd d m = Nat.gcd d (p ^ k * m) :=
                (hcop.gcd_mul d).symm
              rw [hmul_gcd, Nat.gcd_eq_left hd]
            · rintro ⟨a, b, ⟨⟨ha, _⟩, ⟨hb, _⟩⟩, rfl⟩
              exact ⟨mul_dvd_mul ha hb, mul_ne_zero (by positivity) (by omega)⟩
          rw [← hnm, hdiv_eq, Finset.sum_mul_sum, Finset.sum_image]
          · rw [Finset.sum_product]
            apply Finset.sum_congr rfl
            intro a ha
            apply Finset.sum_congr rfl
            intro b hb
            have ha0 : a ≠ 0 := (Nat.pos_of_mem_divisors ha).ne'
            have hb0 : b ≠ 0 := (Nat.pos_of_mem_divisors hb).ne'
            have hcop_ab : Nat.Coprime a b :=
              hcop.coprime_dvd_left (Nat.dvd_of_mem_divisors ha) |>.coprime_dvd_right (Nat.dvd_of_mem_divisors hb)
            rw [cSeq_mul_coprime ha0 hb0 hcop_ab]; ring
          · intro x hx y hy hxy
            dsimp only at hxy
            simp only [Finset.mem_coe, Finset.mem_product] at hx hy
            have hx1 := Nat.dvd_of_mem_divisors hx.1
            have hx2 := Nat.dvd_of_mem_divisors hx.2
            have hy1 := Nat.dvd_of_mem_divisors hy.1
            have hy2 := Nat.dvd_of_mem_divisors hy.2
            have hcop_xy1 : Nat.Coprime x.1 y.2 := hcop.coprime_dvd_left hx1 |>.coprime_dvd_right hy2
            have hcop_yx1 : Nat.Coprime y.1 x.2 := hcop.coprime_dvd_left hy1 |>.coprime_dvd_right hx2
            have h1dvd : x.1 ∣ y.1 := hcop_xy1.dvd_of_dvd_mul_right ⟨x.2, hxy.symm⟩
            have h2dvd : y.1 ∣ x.1 := hcop_yx1.dvd_of_dvd_mul_right ⟨y.2, hxy⟩
            have heq1 : x.1 = y.1 := Nat.dvd_antisymm h1dvd h2dvd
            have hx1pos : 0 < x.1 := Nat.pos_of_mem_divisors hx.1
            have heq2 : x.2 = y.2 := Nat.eq_of_mul_eq_mul_left hx1pos (by change x.1 * x.2 = y.1 * y.2 at hxy; rw [← heq1] at hxy; exact hxy)
            exact Prod.ext heq1 heq2
        -- Multiplicativity of sigma(n) * sigma(2n) / 3: either p = 2 or m is odd or p^k is odd
        have hsig_n : sigma n = sigma (p ^ k) * sigma m := by
          rw [← hnm, sigma_eq_arith, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop,
              ← sigma_eq_arith, ← sigma_eq_arith]
        by_cases hp2 : p = 2
        · -- Then m is odd, so gcd(2, m) = 1 and gcd(2 * p^k, m) = 1
          have hcop2m : Nat.Coprime 2 m := by
            have hcop' : Nat.Coprime (2 ^ k) m := by rwa [hp2] at hcop
            exact hcop'.coprime_dvd_left (dvd_pow_self 2 (by omega))
          have hcop_2pkm : Nat.Coprime (2 * p ^ k) m := hcop2m.mul_left hcop
          have hsig_2n : sigma (2 * n) = sigma (2 * p ^ k) * sigma m := by
            rw [← hnm, show 2 * (p ^ k * m) = (2 * p ^ k) * m by ring, sigma_eq_arith,
                ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop_2pkm,
                ← sigma_eq_arith, ← sigma_eq_arith]
          have hsig_2m : sigma (2 * m) = 3 * sigma m := by
            rw [sigma_eq_arith, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop2m,
                ← sigma_eq_arith, ← sigma_eq_arith, (by decide : sigma 2 = 3)]
          rw [hsum_mul, hsig_n, hsig_2n]
          rw [hsig_2m] at h2
          have h2' : ∑ d ∈ m.divisors, d * cSeq d = sigma m * sigma m := by linarith
          calc 3 * ((∑ d ∈ (p ^ k).divisors, d * cSeq d) * (∑ d ∈ m.divisors, d * cSeq d))
              = (3 * ∑ d ∈ (p ^ k).divisors, d * cSeq d) * (∑ d ∈ m.divisors, d * cSeq d) := by ring
            _ = (sigma (p ^ k) * sigma (2 * p ^ k)) * (sigma m * sigma m) := by rw [h1, h2']
            _ = (sigma (p ^ k) * sigma m) * (sigma (2 * p ^ k) * sigma m) := by ring
        · -- Then p is odd, so gcd(2, p^k) = 1 and gcd(p^k, 2 * m) = 1
          have hcop2pk : Nat.Coprime 2 (p ^ k) :=
            (Nat.prime_two.coprime_iff_not_dvd.mpr (fun hd => hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp hd).symm)).pow_right k
          have hcop_pk2m : Nat.Coprime (p ^ k) (2 * m) := hcop2pk.symm.mul_right hcop
          have hsig_2n : sigma (2 * n) = sigma (p ^ k) * sigma (2 * m) := by
            rw [← hnm, show 2 * (p ^ k * m) = p ^ k * (2 * m) by ring, sigma_eq_arith,
                ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop_pk2m,
                ← sigma_eq_arith, ← sigma_eq_arith]
          have hsig_2pk : sigma (2 * p ^ k) = 3 * sigma (p ^ k) := by
            rw [sigma_eq_arith, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop2pk,
                ← sigma_eq_arith, ← sigma_eq_arith, (by decide : sigma 2 = 3)]
          rw [hsum_mul, hsig_n, hsig_2n]
          rw [hsig_2pk] at h1
          have h1' : ∑ d ∈ (p ^ k).divisors, d * cSeq d = sigma (p ^ k) * sigma (p ^ k) := by linarith
          calc 3 * ((∑ d ∈ (p ^ k).divisors, d * cSeq d) * (∑ d ∈ m.divisors, d * cSeq d))
              = (∑ d ∈ (p ^ k).divisors, d * cSeq d) * (3 * ∑ d ∈ m.divisors, d * cSeq d) := by ring
            _ = (sigma (p ^ k) * sigma (p ^ k)) * (sigma m * sigma (2 * m)) := by rw [h1', h2]
            _ = (sigma (p ^ k) * sigma m) * (sigma (p ^ k) * sigma (2 * m)) := by ring

/-- Every term `a382124 n` is a natural number. -/
private lemma a382124_is_nat (n : ℕ) : ∃ m : ℕ, a382124 n = (m : ℚ) := by
  rcases expLogSeq_euler_nat cSeq n with ⟨f, hf⟩
  refine ⟨f n, ?_⟩
  rw [← hf n]
  unfold a382124
  apply expLogSeq_congr n
  intro k hk1 hkn
  have hsum_eq : (∑ d ∈ Finset.Icc 1 n, if d ∣ k then ((d * cSeq d : ℕ) : ℚ) else 0) =
      ((∑ d ∈ k.divisors, d * cSeq d : ℕ) : ℚ) := by
    rw [← Finset.sum_filter]
    have hfilt : (Finset.Icc 1 n).filter (fun d => d ∣ k) = k.divisors := by
      ext d
      simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
      constructor
      · rintro ⟨⟨_, _⟩, hdk⟩; exact ⟨hdk, by omega⟩
      · rintro ⟨hdk, hk0⟩
        have hd1 : 1 ≤ d := Nat.pos_of_dvd_of_pos hdk (by omega)
        have hdle : d ≤ k := Nat.le_of_dvd (by omega) hdk
        exact ⟨⟨hd1, by omega⟩, hdk⟩
    rw [hfilt]
    push_cast
    rfl
  rw [hsum_eq]
  have h3 := three_mul_sum_div_cSeq k hk1
  have h3q : (3 : ℚ) * ((∑ d ∈ k.divisors, d * cSeq d : ℕ) : ℚ) =
      ((sigma k * sigma (2 * k) : ℕ) : ℚ) := by exact_mod_cast h3
  linarith

/-- `a382125` is the triple Cauchy convolution of `a382124`. -/
private lemma a382125_eq_cube (n : ℕ) :
    a382125 n = convQ (convQ a382124 a382124) a382124 n := by
  set u : ℕ → ℚ := fun k => ((sigma k * sigma (2 * k) : ℕ) : ℚ) / 3
  have ha : a382124 = expLogSeq u := rfl
  have hinner : convQ (expLogSeq u) (expLogSeq u) = expLogSeq (fun k => u k + u k) :=
    funext (expLogSeq_conv u u)
  rw [ha, hinner, expLogSeq_conv]
  unfold a382125
  apply expLogSeq_congr n
  intro k _ _
  simp only [u]
  ring

/-- Polynomial Frobenius mod 3 gives the triple convolution congruences! -/
private lemma triple_convN_zmod3 (z : ℕ → ℕ) (n : ℕ) :
    ((convN (convN z z) z (3 * n) : ℕ) : ZMod 3) = (z n : ZMod 3) ∧
    ((convN (convN z z) z (3 * n + 1) : ℕ) : ZMod 3) = 0 ∧
    ((convN (convN z z) z (3 * n + 2) : ℕ) : ZMod 3) = 0 := by
  set N : ℕ := 3 * n + 2
  set P : Polynomial (ZMod 3) :=
    ∑ m ∈ Finset.range (N + 1), Polynomial.C (z m : ZMod 3) * Polynomial.X ^ m
  have hPcoeff : ∀ k ≤ N, P.coeff k = (z k : ZMod 3) := by
    intro k hk
    simp only [P, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    rw [Finset.sum_eq_single k]
    · simp
    · intro m _ hne; simp [hne.symm]
    · intro hnot; exact absurd (Finset.mem_range.mpr (by omega)) hnot
  have hP2coeff : ∀ k ≤ N, (P * P).coeff k = ((convN z z k : ℕ) : ZMod 3) := by
    intro k hk
    rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => P.coeff i * P.coeff j)]
    unfold convN
    push_cast
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    rw [hPcoeff i (by omega), hPcoeff (k - i) (by omega)]
  have hP3coeff : ∀ k ≤ N, (P ^ 3).coeff k = ((convN (convN z z) z k : ℕ) : ZMod 3) := by
    intro k hk
    rw [show P ^ 3 = (P * P) * P by ring, Polynomial.coeff_mul,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => (P * P).coeff i * P.coeff j)]
    have hR : ((convN (convN z z) z k : ℕ) : ZMod 3) =
        ∑ i ∈ Finset.range (k + 1), ((convN z z i : ℕ) : ZMod 3) * (z (k - i) : ZMod 3) := by
      simp only [convN, Nat.cast_sum, Nat.cast_mul]
    rw [hR]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    rw [hP2coeff i (by omega), hPcoeff (k - i) (by omega)]
  have hFrob : P ^ 3 = ∑ m ∈ Finset.range (N + 1),
      Polynomial.C (z m : ZMod 3) * Polynomial.X ^ (3 * m) := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hsum : (∑ m ∈ Finset.range (N + 1), Polynomial.C (z m : ZMod 3) * Polynomial.X ^ m) ^ 3 =
        ∑ m ∈ Finset.range (N + 1), (Polynomial.C (z m : ZMod 3) * Polynomial.X ^ m) ^ 3 :=
      map_sum (frobenius (Polynomial (ZMod 3)) 3) _ _
    rw [show P ^ 3 = _ from hsum]
    apply Finset.sum_congr rfl
    intro m _
    rw [mul_pow, ← map_pow, ← pow_mul, mul_comm m 3]
    have hz3 : (z m : ZMod 3) ^ 3 = (z m : ZMod 3) := ZMod.pow_card (z m : ZMod 3)
    rw [hz3]
  have hFcoeff : ∀ k, (P ^ 3).coeff k = if 3 ∣ k ∧ k / 3 ≤ N then (z (k / 3) : ZMod 3) else 0 := by
    intro k
    rw [hFrob]
    simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    by_cases hcond : 3 ∣ k ∧ k / 3 ≤ N
    · rw [if_pos hcond, Finset.sum_eq_single (k / 3)]
      · have heq : 3 * (k / 3) = k := Nat.mul_div_cancel' hcond.1
        simp [heq]
      · intro m _ hne
        have hne3 : k ≠ 3 * m := fun h => hne (by omega)
        simp [hne3]
      · intro hnot; exact absurd (Finset.mem_range.mpr (by omega)) hnot
    · rw [if_neg hcond]
      apply Finset.sum_eq_zero
      intro m hm
      rw [Finset.mem_range] at hm
      have hne3 : k ≠ 3 * m := fun h => hcond ⟨⟨m, h⟩, by omega⟩
      simp [hne3]
  refine ⟨?_, ?_, ?_⟩
  · rw [← hP3coeff (3 * n) (by omega), hFcoeff (3 * n)]
    have hc : 3 ∣ 3 * n ∧ 3 * n / 3 ≤ N := ⟨dvd_mul_right 3 n, by omega⟩
    rw [if_pos hc, Nat.mul_div_cancel_left n (by decide)]
  · rw [← hP3coeff (3 * n + 1) (by omega), hFcoeff (3 * n + 1)]
    have hc : ¬(3 ∣ 3 * n + 1 ∧ (3 * n + 1) / 3 ≤ N) := fun h => by omega
    rw [if_neg hc]
  · rw [← hP3coeff (3 * n + 2) (by omega), hFcoeff (3 * n + 2)]
    have hc : ¬(3 ∣ 3 * n + 2 ∧ (3 * n + 2) / 3 ≤ N) := fun h => by omega
    rw [if_neg hc]

private lemma nat_cast_rat_num_den (m : ℕ) :
    ((m : ℚ)).den = 1 ∧ ((m : ℚ)).num = (m : ℤ) := by
  have hd : ((m : ℚ)).den = 1 := by simp
  have hn : (((m : ℚ)).num : ℚ) = (m : ℚ) := Rat.coe_int_num_of_den_eq_one hd
  exact ⟨hd, by exact_mod_cast hn⟩

private lemma prove_main :
    ∀ n : ℕ,
      (a382124 n).den = 1 ∧ (a382125 (3 * n)).den = 1 ∧
      (a382124 n).num % 3 = (a382125 (3 * n)).num % 3 := by
  choose z hz using a382124_is_nat
  intro n
  have ha : a382124 n = (z n : ℚ) := hz n
  have hb : a382125 (3 * n) = ((convN (convN z z) z (3 * n) : ℕ) : ℚ) := by
    rw [a382125_eq_cube (3 * n)]
    have hfun : a382124 = fun k => (z k : ℚ) := funext hz
    rw [hfun]
    have h1 : convQ (fun k => (z k : ℚ)) (fun k => (z k : ℚ)) = fun k => (convN z z k : ℚ) :=
      funext (convQ_cast z z)
    rw [h1, convQ_cast]
  rw [ha, hb, (nat_cast_rat_num_den _).1, (nat_cast_rat_num_den _).1,
      (nat_cast_rat_num_den _).2, (nat_cast_rat_num_den _).2]
  refine ⟨rfl, rfl, ?_⟩
  have hzmod := (triple_convN_zmod3 z n).1
  have hmod : (convN (convN z z) z (3 * n)) % 3 = z n % 3 := by
    have h1 := congrArg ZMod.val hzmod
    simpa [ZMod.val_natCast] using h1
  exact_mod_cast hmod.symm

end OMA.P_oeis_a382124

theorem OMA.solution : type_of% @OMA.S_oeis_a382124.main :=
  OMA.P_oeis_a382124.prove_main
