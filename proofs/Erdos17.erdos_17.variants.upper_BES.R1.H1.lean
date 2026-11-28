import OMAReductions.R_Erdos17_erdos_17_variants_upper_BES_R1
import Mathlib

/-!
# Upper bound for cluster primes

We prove that the number of cluster primes up to `x` is at most
`x * exp (-c * (log (log x))^2)` for every `c ∈ (0, 1/8)`, establishing
`OMA.R_Erdos17_erdos_17_variants_upper_BES_R1.H1`.

The proof combines:
1. Elementary Mertens first and second theorems via Legendre's factorial
   formula, Chebyshev's upper bound on `θ(x)`, and discrete Abel summation.
2. A Bonferroni inclusion-exclusion upper sieve on primes in `(z, y]` for
   prime `k`-tuples with shifts in `[0, z]`.
3. A multiscale additive lower bound on the local prime count `[p - w, p]`
   below any cluster prime `p`, yielding exponential bounds `d_j ≤ exp (3 j)`
   on the `j`-th smallest prime gap below `p`.
-/

namespace Erdos17Elsholtz

open Filter Finset Nat Real

/- Section 1: Elementary Inequalities and Mertens Theorems -/

private lemma pow_div_factorial_le_exp {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    x ^ n / (n.factorial : ℝ) ≤ Real.exp x := by
  have h1 : x ^ n / (n.factorial : ℝ) ≤
      ∑ i ∈ Finset.range (n + 1), x ^ i / (i.factorial : ℝ) :=
    Finset.single_le_sum (fun i _ => div_nonneg (pow_nonneg hx i) (Nat.cast_nonneg _))
      (Finset.mem_range.mpr (Nat.lt_succ_self n))
  exact h1.trans (Real.sum_le_exp_of_nonneg hx (n + 1))

private lemma log_factorial_ge {n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ) * Real.log n - n ≤ Real.log (n.factorial : ℝ) := by
  have hn_pos : (0 : ℝ) < n := by positivity
  have hfac_pos : (0 : ℝ) < n.factorial := by positivity
  have hbound : (n : ℝ) ^ n / (n.factorial : ℝ) ≤ Real.exp n :=
    pow_div_factorial_le_exp hn_pos.le n
  have h1 : (n : ℝ) ^ n ≤ Real.exp n * (n.factorial : ℝ) := (div_le_iff₀ hfac_pos).mp hbound
  have hlog : Real.log ((n : ℝ) ^ n) ≤ Real.log (Real.exp n * (n.factorial : ℝ)) :=
    Real.log_le_log (pow_pos hn_pos n) h1
  rw [Real.log_pow, Real.log_mul (Real.exp_pos _).ne' hfac_pos.ne', Real.log_exp] at hlog
  linarith

private lemma log_factorial_le (n : ℕ) :
    Real.log (n.factorial : ℝ) ≤ (n : ℝ) * Real.log n := by
  have hfac_le : n.factorial ≤ n ^ n := Nat.factorial_le_pow n
  have hfac_pos : (0 : ℝ) < n.factorial := by positivity
  have hlog : Real.log (n.factorial : ℝ) ≤ Real.log ((n : ℝ) ^ n) := by
    apply Real.log_le_log hfac_pos
    exact_mod_cast hfac_le
  rwa [Real.log_pow] at hlog

private lemma log_factorial_eq_sum_primesLE (n : ℕ) :
    Real.log (n.factorial : ℝ) =
      ∑ p ∈ Nat.primesLE n, (n.factorial.factorization p : ℝ) * Real.log p := by
  have hne : n.factorial ≠ 0 := Nat.factorial_ne_zero n
  have hprod : n.factorial = ∏ p ∈ n.factorial.primeFactors, p ^ (n.factorial.factorization p) :=
    (Nat.prod_factorization_pow_eq_self hne).symm
  have hsub : n.factorial.primeFactors ⊆ Nat.primesLE n := by
    intro p hp
    rw [Nat.mem_primeFactors] at hp
    rw [Nat.mem_primesLE]
    exact ⟨hp.1.dvd_factorial.mp hp.2.1, hp.1⟩
  have hprod2 : n.factorial = ∏ p ∈ Nat.primesLE n, p ^ (n.factorial.factorization p) := by
    conv_lhs => rw [hprod]
    apply Finset.prod_subset hsub
    intro p _ hp
    have hzero : n.factorial.factorization p = 0 :=
      Finsupp.notMem_support_iff.mp (by simpa [Nat.support_factorization] using hp)
    rw [hzero, pow_zero]
  have hcast : (n.factorial : ℝ) =
      ∏ p ∈ Nat.primesLE n, ((p : ℝ) ^ (n.factorial.factorization p)) := by
    conv_lhs => rw [hprod2]
    push_cast
    rfl
  rw [hcast, Real.log_prod]
  · refine Finset.sum_congr rfl fun p _ => ?_
    rw [Real.log_pow]
  · intro p hp
    have hp_prime : p.Prime := (Nat.mem_primesLE.mp hp).2
    exact pow_ne_zero _ (Nat.cast_ne_zero.mpr hp_prime.ne_zero)

private lemma log_le_two_sqrt {x : ℝ} (hx : 0 < x) : Real.log x ≤ 2 * Real.sqrt x := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have h1 : Real.log (Real.sqrt x) ≤ Real.sqrt x - 1 := Real.log_le_sub_one_of_pos hs
  have h2 : Real.log x = 2 * Real.log (Real.sqrt x) := by
    rw [Real.log_sqrt hx.le]
    ring
  linarith

private lemma sum_log_div_p_mul_pred_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
      ∑ p ∈ Nat.primesLE n, Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) ≤ C := by
  have hsum : Summable (fun m : ℕ => (4 : ℝ) * (1 / (m : ℝ) ^ ((3 : ℝ) / 2))) := by
    have h := Real.summable_one_div_nat_rpow.mpr (show (1 : ℝ) < (3 : ℝ) / 2 by norm_num)
    exact h.mul_left 4
  refine ⟨∑' m : ℕ, (4 : ℝ) * (1 / (m : ℝ) ^ ((3 : ℝ) / 2)),
    tsum_nonneg fun m => by positivity, fun n => ?_⟩
  have hle : ∑ p ∈ Nat.primesLE n, Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) ≤
      ∑ p ∈ Nat.primesLE n, (4 : ℝ) * (1 / (p : ℝ) ^ ((3 : ℝ) / 2)) := by
    apply Finset.sum_le_sum
    intro p hp
    have hp2 : 2 ≤ p := (Nat.mem_primesLE.mp hp).2.two_le
    have hp_pos : (0 : ℝ) < p := by positivity
    have hp2r : (2 : ℝ) ≤ p := by exact_mod_cast hp2
    have hpred : (p : ℝ) / 2 ≤ (p : ℝ) - 1 := by linarith
    have hlog : Real.log p ≤ 2 * Real.sqrt p := log_le_two_sqrt hp_pos
    have hrpow : (p : ℝ) ^ ((3 : ℝ) / 2) = (p : ℝ) * Real.sqrt p := by
      rw [Real.sqrt_eq_rpow]
      conv_lhs => rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add hp_pos,
        Real.rpow_one]
    have hden_pos : (0 : ℝ) < (p : ℝ) * ((p : ℝ) - 1) := by nlinarith
    have hden2_pos : (0 : ℝ) < (p : ℝ) * ((p : ℝ) / 2) := by positivity
    calc Real.log p / ((p : ℝ) * ((p : ℝ) - 1))
        ≤ (2 * Real.sqrt p) / ((p : ℝ) * ((p : ℝ) / 2)) := by
          gcongr
      _ = 4 / ((p : ℝ) * Real.sqrt p) := by
          have hsq : Real.sqrt p * Real.sqrt p = p := Real.mul_self_sqrt hp_pos.le
          have hs_ne : Real.sqrt p ≠ 0 := (Real.sqrt_pos.mpr hp_pos).ne'
          field_simp
          nlinarith [hsq]
      _ = 4 * (1 / (p : ℝ) ^ ((3 : ℝ) / 2)) := by rw [hrpow]; ring
  exact hle.trans (hsum.sum_le_tsum (Nat.primesLE n) (fun m _ => by positivity))

private lemma mertens_first :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 1 ≤ n →
      |∑ p ∈ Nat.primesLE n, Real.log p / (p : ℝ) - Real.log n| ≤ C := by
  obtain ⟨C2, hC2_nonneg, hC2⟩ := sum_log_div_p_mul_pred_le
  refine ⟨max (1 + C2) (Real.log 4), le_trans (by positivity) (le_max_left _ _), fun n hn => ?_⟩
  have hn_pos : (0 : ℝ) < n := by positivity
  rw [abs_le]
  constructor
  · have h1 : (n : ℝ) * Real.log n - n ≤ Real.log (n.factorial : ℝ) := log_factorial_ge hn
    rw [log_factorial_eq_sum_primesLE] at h1
    have h2 : ∑ p ∈ Nat.primesLE n, (n.factorial.factorization p : ℝ) * Real.log p ≤
        (n : ℝ) * (∑ p ∈ Nat.primesLE n, Real.log p / (p : ℝ)) +
        (n : ℝ) * (∑ p ∈ Nat.primesLE n, Real.log p / ((p : ℝ) * ((p : ℝ) - 1))) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro p hp
      have hp_prime : p.Prime := (Nat.mem_primesLE.mp hp).2
      have hp_ge2 : (2 : ℝ) ≤ p := by exact_mod_cast hp_prime.two_le
      have hp_pos : (0 : ℝ) < p := by linarith
      have hp1_pos : (0 : ℝ) < (p : ℝ) - 1 := by linarith
      have hlog_nonneg : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
      have hvp_nat : (p - 1) * n.factorial.factorization p ≤ n := by
        rw [Nat.sub_one_mul_factorization_factorial hp_prime]
        exact Nat.sub_le n _
      have hvp : (n.factorial.factorization p : ℝ) ≤ (n : ℝ) / ((p : ℝ) - 1) := by
        rw [le_div_iff₀ hp1_pos]
        have hcast : ((p - 1 : ℕ) : ℝ) * (n.factorial.factorization p : ℝ) ≤ (n : ℝ) := by
          exact_mod_cast hvp_nat
        rw [Nat.cast_sub hp_prime.one_le, Nat.cast_one] at hcast
        linarith
      have hfrac : (n : ℝ) / ((p : ℝ) - 1) * Real.log p =
          (n : ℝ) * (Real.log p / (p : ℝ)) +
          (n : ℝ) * (Real.log p / ((p : ℝ) * ((p : ℝ) - 1))) := by
        field_simp
        ring
      calc (n.factorial.factorization p : ℝ) * Real.log p
          ≤ (n : ℝ) / ((p : ℝ) - 1) * Real.log p := by gcongr
        _ = (n : ℝ) * (Real.log p / (p : ℝ)) +
            (n : ℝ) * (Real.log p / ((p : ℝ) * ((p : ℝ) - 1))) := hfrac
    have h3 : (n : ℝ) * Real.log n - n ≤
        (n : ℝ) * (∑ p ∈ Nat.primesLE n, Real.log p / (p : ℝ)) + (n : ℝ) * C2 := by
      have h4 := hC2 n
      nlinarith
    have h5 : Real.log n - (1 + C2) ≤ ∑ p ∈ Nat.primesLE n, Real.log p / (p : ℝ) := by
      nlinarith
    have hmax : (1 + C2) ≤ max (1 + C2) (Real.log 4) := le_max_left _ _
    linarith
  · have h1 : Real.log (n.factorial : ℝ) ≤ (n : ℝ) * Real.log n := log_factorial_le n
    rw [log_factorial_eq_sum_primesLE] at h1
    have htheta : ∑ p ∈ Nat.primesLE n, Real.log p ≤ Real.log 4 * n := by
      rw [← Chebyshev.theta_eq_sum_primesLE_log]
      exact Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg n)
    have h2 : (n : ℝ) * (∑ p ∈ Nat.primesLE n, Real.log p / (p : ℝ)) ≤
        (∑ p ∈ Nat.primesLE n, (n.factorial.factorization p : ℝ) * Real.log p) +
        (∑ p ∈ Nat.primesLE n, Real.log p) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro p hp
      have hp_le : p ≤ n := (Nat.mem_primesLE.mp hp).1
      have hp_prime : p.Prime := (Nat.mem_primesLE.mp hp).2
      have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp_prime.pos
      have hlog_nonneg : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp_prime.one_le)
      have hdiv_le : n / p ≤ n.factorial.factorization p := by
        rw [Nat.factorization_factorial hp_prime (Nat.lt_succ_self (Nat.log p n))]
        have h1log : 1 ≤ Nat.log p n := Nat.le_log_of_pow_le hp_prime.one_lt (by simpa using hp_le)
        have hmem : 1 ∈ Finset.Ico 1 (Nat.log p n + 1) :=
          Finset.mem_Ico.mpr ⟨le_rfl, Nat.lt_succ_of_le h1log⟩
        have hs := Finset.single_le_sum (f := fun i => n / p ^ i) (fun _ _ => Nat.zero_le _) hmem
        simpa using hs
      have hfloor : (n : ℝ) / (p : ℝ) ≤ (n / p : ℕ) + 1 := by
        rw [div_le_iff₀ hp_pos]
        have hmod : n < (n / p + 1) * p := by
          have h1 := Nat.div_add_mod n p
          have h2 := Nat.mod_lt n hp_prime.pos
          nlinarith
        have hcast : (n : ℝ) < ((n / p + 1 : ℕ) : ℝ) * (p : ℝ) := by exact_mod_cast hmod
        push_cast at hcast
        linarith
      have hbound : (n : ℝ) / (p : ℝ) ≤ (n.factorial.factorization p : ℝ) + 1 :=
        hfloor.trans (by gcongr)
      calc (n : ℝ) * (Real.log p / (p : ℝ))
          = ((n : ℝ) / (p : ℝ)) * Real.log p := by ring
        _ ≤ ((n.factorial.factorization p : ℝ) + 1) * Real.log p := by gcongr
        _ = (n.factorial.factorization p : ℝ) * Real.log p + Real.log p := by ring
    have h3 : (n : ℝ) * (∑ p ∈ Nat.primesLE n, Real.log p / (p : ℝ)) ≤
        (n : ℝ) * Real.log n + Real.log 4 * (n : ℝ) := by linarith
    have h4 : ∑ p ∈ Nat.primesLE n, Real.log p / (p : ℝ) ≤ Real.log n + Real.log 4 := by
      nlinarith
    have hmax : Real.log 4 ≤ max (1 + C2) (Real.log 4) := le_max_right _ _
    linarith

private lemma sum_Ico_sub_succ (f : ℕ → ℝ) (a b : ℕ) (hab : a ≤ b) :
    ∑ n ∈ Finset.Ico a b, (f n - f (n + 1)) = f a - f b := by
  induction b with
  | zero =>
    have ha0 : a = 0 := Nat.eq_zero_of_le_zero hab
    subst ha0
    simp
  | succ b ih =>
    rcases eq_or_lt_of_le hab with rfl | hlt
    · simp
    · have hle : a ≤ b := Nat.lt_succ_iff.mp hlt
      have hIco : Finset.Ico a (b + 1) = insert b (Finset.Ico a b) := by
        ext x; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
      rw [hIco, Finset.sum_insert (by simp), ih hle]
      ring

private lemma abel_summation_Ioc (f g : ℕ → ℝ) (a b : ℕ) (hab : a < b) :
    ∑ n ∈ Finset.Ioc a b, (f n - f (n - 1)) * g n =
      f b * g b - f a * g (a + 1) +
      ∑ n ∈ Finset.Ico (a + 1) b, f n * (g n - g (n + 1)) := by
  induction b with
  | zero => omega
  | succ b ih =>
    rcases eq_or_lt_of_le (Nat.lt_succ_iff.mp hab) with rfl | hlt
    · have hIoc : Finset.Ioc a (a + 1) = {a + 1} := by
        ext x; simp only [Finset.mem_Ioc, Finset.mem_singleton]; omega
      rw [hIoc, Finset.sum_singleton, add_tsub_cancel_right, Finset.Ico_self, Finset.sum_empty,
        add_zero]
      ring
    · rw [Finset.sum_Ioc_succ_top hlt.le, ih hlt]
      have hIco : Finset.Ico (a + 1) (b + 1) = insert b (Finset.Ico (a + 1) b) := by
        ext x
        simp only [Finset.mem_Ico, Finset.mem_insert]
        omega
      rw [hIco, Finset.sum_insert (by simp)]
      simp only [add_tsub_cancel_right]
      ring

private lemma log_diff_bounds {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    (v - u) / v ≤ Real.log v - Real.log u ∧ Real.log v - Real.log u ≤ (v - u) / u := by
  have hv : 0 < v := lt_of_lt_of_le hu huv
  constructor
  · have h1 : Real.log (u / v) ≤ u / v - 1 := Real.log_le_sub_one_of_pos (div_pos hu hv)
    rw [Real.log_div hu.ne' hv.ne'] at h1
    have h2 : (v - u) / v = 1 - u / v := by field_simp
    linarith
  · have h1 : Real.log (v / u) ≤ v / u - 1 := Real.log_le_sub_one_of_pos (div_pos hv hu)
    rw [Real.log_div hv.ne' hu.ne'] at h1
    have h2 : (v - u) / u = v / u - 1 := by field_simp
    linarith

private lemma sum_inv_mul_pred_le (a b : ℕ) (ha : 2 ≤ a) :
    ∑ n ∈ Finset.Ico a b, (1 : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)) ≤ 1 := by
  let h : ℕ → ℝ := fun n => 1 / ((n : ℝ) - 1)
  have hle : ∀ n ∈ Finset.Ico a b,
      (1 : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)) = h n - h (n + 1) := by
    intro n hn
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast le_trans ha (Finset.mem_Ico.mp hn).1
    have hn0 : (n : ℝ) ≠ 0 := by linarith
    have hn1 : (n : ℝ) - 1 ≠ 0 := by linarith
    dsimp only [h]
    push_cast
    have hsub : (n : ℝ) + 1 - 1 = (n : ℝ) := by ring
    rw [hsub]
    field_simp
    ring
  rw [Finset.sum_congr rfl hle]
  rcases le_or_gt b a with hba | hab
  · rw [Finset.Ico_eq_empty_of_le hba, Finset.sum_empty]
    norm_num
  · rw [sum_Ico_sub_succ h a b hab.le]
    dsimp only [h]
    have ha2 : (2 : ℝ) ≤ a := by exact_mod_cast ha
    have hb2 : (2 : ℝ) ≤ b := by exact_mod_cast (le_trans ha hab.le)
    have h1 : (1 : ℝ) / ((a : ℝ) - 1) ≤ 1 := by
      rw [div_le_one (by linarith)]
      linarith
    have h2 : (0 : ℝ) ≤ 1 / ((b : ℝ) - 1) := by
      apply div_nonneg (by norm_num) (by linarith)
    linarith

private lemma mertens_second :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a b : ℕ, 2 ≤ a → a < b →
      |∑ p ∈ Nat.primesLE b \ Nat.primesLE a, (1 : ℝ) / p -
        (Real.log (Real.log b) - Real.log (Real.log (a + 1)))| ≤ C := by
  obtain ⟨C1, hC1_nonneg, hC1⟩ := mertens_first
  refine ⟨2 * C1 / Real.log 2 + 1 + 6, by positivity, fun a b ha hab => ?_⟩
  let M : ℕ → ℝ := fun n => ∑ p ∈ Nat.primesLE n, Real.log p / (p : ℝ)
  let g : ℕ → ℝ := fun n => 1 / Real.log n
  have hsum_eq : ∑ p ∈ Nat.primesLE b \ Nat.primesLE a, (1 : ℝ) / p =
      ∑ n ∈ Finset.Ioc a b, (M n - M (n - 1)) * g n := by
    have hterm : ∀ n ∈ Finset.Ioc a b,
        (M n - M (n - 1)) * g n = if n.Prime then (1 : ℝ) / n else 0 := by
      intro n hn
      have hn_gt : a < n := (Finset.mem_Ioc.mp hn).1
      have hlog_pos : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
      have hMdiff : M n - M (n - 1) = if n.Prime then Real.log n / (n : ℝ) else 0 := by
        dsimp only [M]
        have hsucc : Nat.primesLE n =
            if n.Prime then insert n (Nat.primesLE (n - 1)) else Nat.primesLE (n - 1) := by
          ext p
          split_ifs with hp
          · simp only [Nat.mem_primesLE, Finset.mem_insert]
            constructor
            · rintro ⟨hle, hpp⟩
              rcases eq_or_lt_of_le hle with rfl | hlt
              · exact Or.inl rfl
              · exact Or.inr ⟨by omega, hpp⟩
            · rintro (rfl | ⟨hle, hpp⟩)
              · exact ⟨le_rfl, hp⟩
              · exact ⟨by omega, hpp⟩
          · simp only [Nat.mem_primesLE]
            constructor
            · rintro ⟨hle, hpp⟩
              have hne : p ≠ n := fun h => hp (h ▸ hpp)
              exact ⟨by omega, hpp⟩
            · rintro ⟨hle, hpp⟩
              exact ⟨by omega, hpp⟩
        rw [hsucc]
        split_ifs with hp
        · have hnot : n ∉ Nat.primesLE (n - 1) := by
            simp only [Nat.mem_primesLE, not_and]
            intro h; omega
          rw [Finset.sum_insert hnot, add_sub_cancel_right]
        · rw [sub_self]
      rw [hMdiff]
      dsimp only [g]
      split_ifs
      · field_simp [hlog_pos.ne']
      · simp
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter]
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext p
    simp only [Finset.mem_sdiff, Nat.mem_primesLE, Finset.mem_filter, Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨hpb, hpp⟩, hna⟩
      exact ⟨⟨by by_contra hle; exact hna ⟨by omega, hpp⟩, hpb⟩, hpp⟩
    · rintro ⟨⟨hpa, hpb⟩, hpp⟩
      exact ⟨⟨hpb, hpp⟩, fun h => by omega⟩
  rw [hsum_eq, abel_summation_Ioc M g a b hab]
  let E : ℕ → ℝ := fun n => M n - Real.log n
  have hE : ∀ n : ℕ, 1 ≤ n → |E n| ≤ C1 := fun n hn => hC1 n hn
  have hsplit : M b * g b - M a * g (a + 1) +
      ∑ n ∈ Finset.Ico (a + 1) b, M n * (g n - g (n + 1)) =
      (Real.log b * g b - Real.log a * g (a + 1) +
        ∑ n ∈ Finset.Ico (a + 1) b, Real.log n * (g n - g (n + 1))) +
      (E b * g b - E a * g (a + 1) +
        ∑ n ∈ Finset.Ico (a + 1) b, E n * (g n - g (n + 1))) := by
    have hsum_split :
        ∑ n ∈ Finset.Ico (a + 1) b, M n * (g n - g (n + 1)) =
        ∑ n ∈ Finset.Ico (a + 1) b, Real.log n * (g n - g (n + 1)) +
        ∑ n ∈ Finset.Ico (a + 1) b, E n * (g n - g (n + 1)) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun n _ => ?_
      dsimp only [E]; ring
    rw [hsum_split]; dsimp only [E]; ring
  rw [hsplit]
  have hg_mono : ∀ n : ℕ, 2 ≤ n → 0 ≤ g n - g (n + 1) := by
    intro n hn
    dsimp only [g]
    have h1 : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
    have h2 : Real.log n ≤ Real.log ((n + 1 : ℕ) : ℝ) :=
      Real.log_le_log (by positivity) (by exact_mod_cast Nat.le_succ n)
    have h3 : 1 / Real.log ((n + 1 : ℕ) : ℝ) ≤ 1 / Real.log n := one_div_le_one_div_of_le h1 h2
    linarith
  have htel_g : ∑ n ∈ Finset.Ico (a + 1) b, (g n - g (n + 1)) = g (a + 1) - g b :=
    sum_Ico_sub_succ g (a + 1) b hab
  have hlog_b_pos : 0 < Real.log b := Real.log_pos (by exact_mod_cast (show 1 < b by omega))
  have hlog_a1_pos : 0 < Real.log ((a + 1 : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < a + 1 by omega))
  have herr_bound : |E b * g b - E a * g (a + 1) +
      ∑ n ∈ Finset.Ico (a + 1) b, E n * (g n - g (n + 1))| ≤ 2 * C1 / Real.log 2 := by
    have hgb_nonneg : 0 ≤ g b := by dsimp [g]; positivity
    have hga1_nonneg : 0 ≤ g (a + 1) := by dsimp [g]; positivity
    have hsum_abs : |∑ n ∈ Finset.Ico (a + 1) b, E n * (g n - g (n + 1))| ≤
        C1 * (g (a + 1) - g b) := by
      calc |∑ n ∈ Finset.Ico (a + 1) b, E n * (g n - g (n + 1))|
          ≤ ∑ n ∈ Finset.Ico (a + 1) b, |E n * (g n - g (n + 1))| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ n ∈ Finset.Ico (a + 1) b, C1 * (g n - g (n + 1)) := by
            apply Finset.sum_le_sum
            intro n hn
            have hn2 : 2 ≤ n := by have := (Finset.mem_Ico.mp hn).1; omega
            rw [abs_mul, abs_of_nonneg (hg_mono n hn2)]
            exact mul_le_mul_of_nonneg_right (hE n (by omega)) (hg_mono n hn2)
        _ = C1 * ∑ n ∈ Finset.Ico (a + 1) b, (g n - g (n + 1)) := by rw [← Finset.mul_sum]
        _ = C1 * (g (a + 1) - g b) := by rw [htel_g]
    have h1 : |E b * g b - E a * g (a + 1)| ≤ C1 * g b + C1 * g (a + 1) := by
      calc |E b * g b - E a * g (a + 1)|
          ≤ |E b * g b| + |E a * g (a + 1)| := abs_sub _ _
        _ = |E b| * g b + |E a| * g (a + 1) := by
            rw [abs_mul, abs_mul, abs_of_nonneg hgb_nonneg, abs_of_nonneg hga1_nonneg]
        _ ≤ C1 * g b + C1 * g (a + 1) := by
            gcongr
            · exact hE b (by omega)
            · exact hE a (by omega)
    have hga1_le : g (a + 1) ≤ 1 / Real.log 2 := by
      dsimp only [g]
      apply one_div_le_one_div_of_le (Real.log_pos (by norm_num))
      exact Real.log_le_log (by norm_num) (by exact_mod_cast (show 2 ≤ a + 1 by omega))
    calc |E b * g b - E a * g (a + 1) +
            ∑ n ∈ Finset.Ico (a + 1) b, E n * (g n - g (n + 1))|
        ≤ |E b * g b - E a * g (a + 1)| +
            |∑ n ∈ Finset.Ico (a + 1) b, E n * (g n - g (n + 1))| := abs_add_le _ _
      _ ≤ (C1 * g b + C1 * g (a + 1)) + C1 * (g (a + 1) - g b) := add_le_add h1 hsum_abs
      _ = 2 * C1 * g (a + 1) := by ring
      _ ≤ 2 * C1 * (1 / Real.log 2) := by gcongr
      _ = 2 * C1 / Real.log 2 := by ring
  have htel_ll : ∑ n ∈ Finset.Ico (a + 1) b,
      (Real.log (Real.log ((n + 1 : ℕ) : ℝ)) - Real.log (Real.log (n : ℝ))) =
      Real.log (Real.log b) - Real.log (Real.log ((a + 1 : ℕ) : ℝ)) := by
    let F : ℕ → ℝ := fun n => -Real.log (Real.log (n : ℝ))
    have h := sum_Ico_sub_succ F (a + 1) b hab
    have hlhs : ∑ n ∈ Finset.Ico (a + 1) b, (F n - F (n + 1)) =
        ∑ n ∈ Finset.Ico (a + 1) b,
          (Real.log (Real.log ((n + 1 : ℕ) : ℝ)) - Real.log (Real.log (n : ℝ))) := by
      refine Finset.sum_congr rfl fun n _ => by dsimp only [F]; ring
    rw [← hlhs, h]
    dsimp only [F]
    ring
  have hmain_bound : |(Real.log b * g b - Real.log a * g (a + 1) +
      ∑ n ∈ Finset.Ico (a + 1) b, Real.log n * (g n - g (n + 1))) -
      (Real.log (Real.log b) - Real.log (Real.log (a + 1)))| ≤ 1 + 6 := by
    have hbdry : 0 ≤ Real.log b * g b - Real.log a * g (a + 1) ∧
        Real.log b * g b - Real.log a * g (a + 1) ≤ 1 := by
      dsimp only [g]
      have hbb : Real.log b * (1 / Real.log b) = 1 := by field_simp [hlog_b_pos.ne']
      rw [hbb]
      have hlog_a_nonneg : 0 ≤ Real.log a :=
        Real.log_nonneg (by exact_mod_cast (show 1 ≤ a by omega))
      have hlog_a_le : Real.log a ≤ Real.log ((a + 1 : ℕ) : ℝ) :=
        Real.log_le_log (by positivity) (by exact_mod_cast Nat.le_succ a)
      have hfrac_le : Real.log a * (1 / Real.log ((a + 1 : ℕ) : ℝ)) ≤ 1 := by
        rw [mul_one_div, div_le_one hlog_a1_pos]
        exact hlog_a_le
      have hfrac_nonneg : 0 ≤ Real.log a * (1 / Real.log ((a + 1 : ℕ) : ℝ)) := by positivity
      constructor <;> linarith
    have hsum_upper : ∑ n ∈ Finset.Ico (a + 1) b, Real.log n * (g n - g (n + 1)) ≤
        Real.log (Real.log b) - Real.log (Real.log ((a + 1 : ℕ) : ℝ)) := by
      rw [← htel_ll]
      apply Finset.sum_le_sum
      intro n hn
      have hn3 : 3 ≤ n := by have := (Finset.mem_Ico.mp hn).1; omega
      have hln_pos : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
      have hln1_pos : 0 < Real.log ((n + 1 : ℕ) : ℝ) :=
        Real.log_pos (by exact_mod_cast (show 1 < n + 1 by omega))
      have hln_le : Real.log n ≤ Real.log ((n + 1 : ℕ) : ℝ) :=
        Real.log_le_log (by positivity) (by exact_mod_cast Nat.le_succ n)
      have hsimp : Real.log n * (g n - g (n + 1)) =
          (Real.log ((n + 1 : ℕ) : ℝ) - Real.log n) / Real.log ((n + 1 : ℕ) : ℝ) := by
        dsimp only [g]
        field_simp [hln_pos.ne', hln1_pos.ne']
      rw [hsimp]
      exact (log_diff_bounds hln_pos hln_le).1
    have hsum_lower : Real.log (Real.log b) - Real.log (Real.log ((a + 1 : ℕ) : ℝ)) - 6 ≤
        ∑ n ∈ Finset.Ico (a + 1) b, Real.log n * (g n - g (n + 1)) := by
      have hdiff_le : (Real.log (Real.log b) - Real.log (Real.log ((a + 1 : ℕ) : ℝ))) -
          ∑ n ∈ Finset.Ico (a + 1) b, Real.log n * (g n - g (n + 1)) ≤ 6 := by
        rw [← htel_ll, ← Finset.sum_sub_distrib]
        calc ∑ n ∈ Finset.Ico (a + 1) b,
              ((Real.log (Real.log ((n + 1 : ℕ) : ℝ)) - Real.log (Real.log (n : ℝ))) -
                Real.log n * (g n - g (n + 1)))
            ≤ ∑ n ∈ Finset.Ico (a + 1) b,
                (6 : ℝ) * (1 / ((n : ℝ) * ((n : ℝ) - 1))) := by
              apply Finset.sum_le_sum
              intro n hn
              have hn3 : 3 ≤ n := by have := (Finset.mem_Ico.mp hn).1; omega
              have hnr : (3 : ℝ) ≤ n := by exact_mod_cast hn3
              have hn_pos : (0 : ℝ) < n := by linarith
              have hln_pos : 0 < Real.log n :=
                Real.log_pos (by exact_mod_cast (show 1 < n by omega))
              have hln1_pos : 0 < Real.log ((n + 1 : ℕ) : ℝ) :=
                Real.log_pos (by exact_mod_cast (show 1 < n + 1 by omega))
              have hln_le : Real.log n ≤ Real.log ((n + 1 : ℕ) : ℝ) :=
                Real.log_le_log hn_pos (by exact_mod_cast Nat.le_succ n)
              have hll_le : Real.log (Real.log ((n + 1 : ℕ) : ℝ)) - Real.log (Real.log n) ≤
                  (Real.log ((n + 1 : ℕ) : ℝ) - Real.log n) / Real.log n :=
                (log_diff_bounds hln_pos hln_le).2
              have hsimp : Real.log n * (g n - g (n + 1)) =
                  (Real.log ((n + 1 : ℕ) : ℝ) - Real.log n) / Real.log ((n + 1 : ℕ) : ℝ) := by
                dsimp only [g]
                field_simp [hln_pos.ne', hln1_pos.ne']
              have hdiff_log : Real.log ((n + 1 : ℕ) : ℝ) - Real.log n ≤ 1 / (n : ℝ) := by
                have h := (log_diff_bounds hn_pos (show (n : ℝ) ≤ (n : ℝ) + 1 by linarith)).2
                push_cast
                simpa using h
              have hdiff_nonneg : 0 ≤ Real.log ((n + 1 : ℕ) : ℝ) - Real.log n :=
                sub_nonneg.mpr hln_le
              have hlog2_ge : (1 : ℝ) / 2 ≤ Real.log 2 := by
                linarith [Real.log_two_gt_d9]
              have hln_ge : (1 : ℝ) / 2 ≤ Real.log n :=
                hlog2_ge.trans (Real.log_le_log (by norm_num) (by linarith))
              have hln1_ge : (1 : ℝ) / 2 ≤ Real.log ((n + 1 : ℕ) : ℝ) := hln_ge.trans hln_le
              have hident : (Real.log ((n + 1 : ℕ) : ℝ) - Real.log n) / Real.log n -
                  (Real.log ((n + 1 : ℕ) : ℝ) - Real.log n) / Real.log ((n + 1 : ℕ) : ℝ) =
                  (Real.log ((n + 1 : ℕ) : ℝ) - Real.log n) ^ 2 /
                    (Real.log n * Real.log ((n + 1 : ℕ) : ℝ)) := by
                field_simp [hln_pos.ne', hln1_pos.ne']
              calc (Real.log (Real.log ((n + 1 : ℕ) : ℝ)) - Real.log (Real.log n)) -
                    Real.log n * (g n - g (n + 1))
                  ≤ (Real.log ((n + 1 : ℕ) : ℝ) - Real.log n) / Real.log n -
                    (Real.log ((n + 1 : ℕ) : ℝ) - Real.log n) / Real.log ((n + 1 : ℕ) : ℝ) := by
                      rw [hsimp]; linarith
                _ = (Real.log ((n + 1 : ℕ) : ℝ) - Real.log n) ^ 2 /
                    (Real.log n * Real.log ((n + 1 : ℕ) : ℝ)) := hident
                _ ≤ (1 / (n : ℝ)) ^ 2 / ((1 / 2) * (1 / 2)) := by
                      gcongr
                _ = 4 / ((n : ℝ) * (n : ℝ)) := by field_simp; norm_num
                _ ≤ 6 * (1 / ((n : ℝ) * ((n : ℝ) - 1))) := by
                      have hpos : 0 < (n : ℝ) * ((n : ℝ) - 1) := by nlinarith
                      rw [mul_one_div, div_le_div_iff₀ (by positivity) hpos]
                      nlinarith
          _ = 6 * ∑ n ∈ Finset.Ico (a + 1) b, (1 : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)) := by
              rw [← Finset.mul_sum]
          _ ≤ 6 * 1 := by
              gcongr
              exact sum_inv_mul_pred_le (a + 1) b (by omega)
          _ = 6 := mul_one 6
      linarith
    push_cast at hsum_upper hsum_lower
    rw [abs_le]
    constructor <;> linarith
  have htri : |((Real.log b * g b - Real.log a * g (a + 1) +
        ∑ n ∈ Finset.Ico (a + 1) b, Real.log n * (g n - g (n + 1))) +
        (E b * g b - E a * g (a + 1) +
        ∑ n ∈ Finset.Ico (a + 1) b, E n * (g n - g (n + 1)))) -
        (Real.log (Real.log b) - Real.log (Real.log (a + 1)))| ≤
      |(Real.log b * g b - Real.log a * g (a + 1) +
        ∑ n ∈ Finset.Ico (a + 1) b, Real.log n * (g n - g (n + 1))) -
        (Real.log (Real.log b) - Real.log (Real.log (a + 1)))| +
      |E b * g b - E a * g (a + 1) +
        ∑ n ∈ Finset.Ico (a + 1) b, E n * (g n - g (n + 1))| := by
    have : ∀ u v w : ℝ, |u + v - w| ≤ |u - w| + |v| := fun u v w => by
      simpa [sub_add_eq_add_sub] using abs_add_le (u - w) v
    exact this _ _ _
  linarith

/- Section 2: Bonferroni Inclusion-Exclusion Upper Sieve -/

private lemma alternating_choose_sum (m t : ℕ) (hm : 1 ≤ m) :
    ∑ j ∈ Finset.range (t + 1), (-1 : ℝ) ^ j * (m.choose j : ℝ) =
      (-1 : ℝ) ^ t * ((m - 1).choose t : ℝ) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Finset.sum_range_succ, ih]
    have hpas : m.choose (t + 1) = (m - 1).choose t + (m - 1).choose (t + 1) := by
      cases m with
      | zero => omega
      | succ m' =>
        simp only [add_tsub_cancel_right]
        exact Nat.choose_succ_succ m' t
    rw [hpas]
    push_cast
    ring

private lemma bonferroni_upper_bound (m r : ℕ) :
    (if m = 0 then (1 : ℝ) else 0) ≤
      ∑ j ∈ Finset.range (2 * r + 1), (-1 : ℝ) ^ j * (m.choose j : ℝ) := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp only [↓reduceIte]
    rw [Finset.sum_eq_single 0]
    · simp
    · intro j _ hj
      cases j with
      | zero => exact absurd rfl hj
      | succ j' => simp
    · intro h; exact absurd (Finset.mem_range.mpr (Nat.succ_pos _)) h
  · simp only [hm, ↓reduceIte]
    rw [alternating_choose_sum m (2 * r) (Nat.pos_of_ne_zero hm)]
    have h1 : (-1 : ℝ) ^ (2 * r) = 1 := by
      rw [pow_mul]
      norm_num
    rw [h1, one_mul]
    exact Nat.cast_nonneg _

private lemma bonferroni_finset {α : Type*} [DecidableEq α] (E : Finset α) (r : ℕ) :
    (if E = ∅ then (1 : ℝ) else 0) ≤
      ∑ S ∈ E.powerset.filter (fun S => S.card ≤ 2 * r), (-1 : ℝ) ^ S.card := by
  have h1 : (if E = ∅ then (1 : ℝ) else 0) = if E.card = 0 then 1 else 0 := by
    simp [Finset.card_eq_zero]
  rw [h1]
  have h2 : ∑ S ∈ E.powerset.filter (fun S => S.card ≤ 2 * r), (-1 : ℝ) ^ S.card =
      ∑ j ∈ Finset.range (2 * r + 1), (-1 : ℝ) ^ j * (E.card.choose j : ℝ) := by
    rw [← Finset.sum_fiberwise_of_maps_to
      (g := Finset.card) (t := Finset.range (2 * r + 1))
      (fun S hS => Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_filter.mp hS).2))]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hfilt : (E.powerset.filter (fun S => S.card ≤ 2 * r)).filter (fun S => S.card = j) =
        E.powersetCard j := by
      ext S
      simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_powersetCard]
      constructor
      · rintro ⟨⟨hsub, _⟩, hcard⟩; exact ⟨hsub, hcard⟩
      · rintro ⟨hsub, hcard⟩
        exact ⟨⟨hsub, hcard ▸ Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)⟩, hcard⟩
    rw [hfilt]
    calc ∑ S ∈ E.powersetCard j, (-1 : ℝ) ^ S.card
        = ∑ _S ∈ E.powersetCard j, (-1 : ℝ) ^ j :=
          Finset.sum_congr rfl fun S hS => by rw [(Finset.mem_powersetCard.mp hS).2]
      _ = ((E.powersetCard j).card : ℝ) * (-1 : ℝ) ^ j := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = (-1 : ℝ) ^ j * (E.card.choose j : ℝ) := by
          rw [Finset.card_powersetCard]; ring
  rw [h2]
  exact bonferroni_upper_bound E.card r

private lemma card_residue_classes_crt
    (D : Finset ℕ) (z : ℕ) (hD : ∀ d ∈ D, d ≤ z)
    (S : Finset ℕ) (hS : ∀ q ∈ S, q.Prime ∧ z < q) :
    ((Finset.range (∏ q ∈ S, q)).filter
      (fun a => ∀ q ∈ S, ∃ d ∈ D, a % q = d)).card = D.card ^ S.card := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp
  | insert q S hqS ih =>
    have hq_prime : q.Prime := (hS q (Finset.mem_insert_self q S)).1
    have hq_gt : z < q := (hS q (Finset.mem_insert_self q S)).2
    have hS' : ∀ p ∈ S, p.Prime ∧ z < p := fun p hp => hS p (Finset.mem_insert_of_mem hp)
    have hcop : q.Coprime (∏ p ∈ S, p) := by
      refine Nat.Coprime.prod_right fun p hp => ?_
      have hp_prime : p.Prime := (hS' p hp).1
      exact (Nat.coprime_primes hq_prime hp_prime).mpr (fun h => hqS (h ▸ hp))
    have hM_pos : 0 < ∏ p ∈ S, p :=
      Finset.prod_pos fun p hp => (hS' p hp).1.pos
    rw [Finset.prod_insert hqS, Finset.card_insert_of_notMem hqS, pow_succ', ← ih hS']
    let A := (Finset.range (∏ p ∈ S, p)).filter (fun a => ∀ p ∈ S, ∃ d ∈ D, a % p = d)
    let B := (Finset.range (q * ∏ p ∈ S, p)).filter
      (fun a => ∀ p ∈ insert q S, ∃ d ∈ D, a % p = d)
    suffices hcard : B.card = (D ×ˢ A).card by
      rw [hcard, Finset.card_product]
    apply Finset.card_bij (fun a _ => (a % q, a % ∏ p ∈ S, p))
    · intro a ha
      rw [Finset.mem_filter] at ha
      rw [Finset.mem_product]
      refine ⟨?_, ?_⟩
      · obtain ⟨d, hd, hmod⟩ := ha.2 q (Finset.mem_insert_self q S)
        rwa [hmod]
      · rw [Finset.mem_filter, Finset.mem_range]
        refine ⟨Nat.mod_lt a hM_pos, fun p hp => ?_⟩
        obtain ⟨d, hd, hmod⟩ := ha.2 p (Finset.mem_insert_of_mem hp)
        refine ⟨d, hd, ?_⟩
        dsimp only
        have hdvd : p ∣ ∏ x ∈ S, x := Finset.dvd_prod_of_mem (fun x => x) hp
        rw [Nat.mod_mod_of_dvd a hdvd]
        exact hmod
    · intro a₁ ha₁ a₂ ha₂ heq
      rw [Prod.mk.injEq] at heq
      have h1 : a₁ < q * ∏ p ∈ S, p := Finset.mem_range.mp (Finset.mem_filter.mp ha₁).1
      have h2 : a₂ < q * ∏ p ∈ S, p := Finset.mem_range.mp (Finset.mem_filter.mp ha₂).1
      have hmodeq : a₁ ≡ a₂ [MOD q * ∏ p ∈ S, p] :=
        (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨heq.1, heq.2⟩
      rw [Nat.ModEq, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at hmodeq
      exact hmodeq
    · rintro ⟨d, r⟩ hdr
      rw [Finset.mem_product] at hdr
      obtain ⟨hdD, hrA⟩ := hdr
      dsimp only at hdD hrA
      rw [Finset.mem_filter, Finset.mem_range] at hrA
      let c := Nat.chineseRemainder hcop d r
      have hc_lt : c.val < q * ∏ p ∈ S, p :=
        Nat.chineseRemainder_lt_mul hcop d r hq_prime.ne_zero hM_pos.ne'
      have hd_lt : d < q := lt_of_le_of_lt (hD d hdD) hq_gt
      have hcq : c.val % q = d := Eq.trans c.property.1 (Nat.mod_eq_of_lt hd_lt)
      have hcm : c.val % ∏ p ∈ S, p = r := Eq.trans c.property.2 (Nat.mod_eq_of_lt hrA.1)
      refine ⟨c.val, ?_, ?_⟩
      · rw [Finset.mem_filter, Finset.mem_range]
        refine ⟨hc_lt, fun p hp => ?_⟩
        rcases Finset.mem_insert.mp hp with hpeq | hpS
        · rw [hpeq]
          exact ⟨d, hdD, hcq⟩
        · obtain ⟨d', hd'D, hmod'⟩ := hrA.2 p hpS
          refine ⟨d', hd'D, ?_⟩
          have hdvd : p ∣ ∏ x ∈ S, x := Finset.dvd_prod_of_mem (fun x => x) hpS
          rw [← Nat.mod_mod_of_dvd c.val hdvd, hcm]
          exact hmod'
      · ext
        · exact hcq
        · exact hcm

private lemma card_Icc_mod_eq_approx (x M a : ℕ) (hM : 0 < M) (ha : a < M) :
    |(((Finset.Icc 1 x).filter (fun n => n % M = a)).card : ℝ) - (x : ℝ) / (M : ℝ)| ≤ 1 := by
  have hM_pos : (0 : ℝ) < M := by positivity
  have hlower : x / M ≤ ((Finset.Icc 1 x).filter (fun n => n % M = a)).card := by
    rcases eq_or_ne a 0 with rfl | ha0
    · have hcard : (Finset.Icc 1 (x / M)).card ≤
          ((Finset.Icc 1 x).filter (fun n => n % M = 0)).card := by
        refine Finset.card_le_card_of_injOn (fun k => k * M) ?_ ?_
        · intro k hk
          rw [Finset.mem_coe, Finset.mem_Icc] at hk
          rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc]
          refine ⟨⟨?_, ?_⟩, Nat.mul_mod_left k M⟩
          · exact Nat.mul_pos hk.1 hM
          · exact (Nat.mul_le_mul_right M hk.2).trans (Nat.div_mul_le_self x M)
        · intro k₁ _ k₂ _ heq
          exact Nat.eq_of_mul_eq_mul_right hM heq
      simpa using hcard
    · have hcard : (Finset.range (x / M)).card ≤
          ((Finset.Icc 1 x).filter (fun n => n % M = a)).card := by
        refine Finset.card_le_card_of_injOn (fun k => k * M + a) ?_ ?_
        · intro k hk
          rw [Finset.mem_coe, Finset.mem_range] at hk
          rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc]
          dsimp only
          refine ⟨⟨by omega, ?_⟩, ?_⟩
          · have h1 : (k + 1) * M ≤ (x / M) * M := Nat.mul_le_mul_right M hk
            have h2 : (x / M) * M ≤ x := Nat.div_mul_le_self x M
            nlinarith
          · rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt ha]
        · intro k₁ _ k₂ _ heq
          dsimp only at heq
          have : k₁ * M = k₂ * M := by omega
          exact Nat.eq_of_mul_eq_mul_right hM this
      simpa using hcard
  have hupper : ((Finset.Icc 1 x).filter (fun n => n % M = a)).card ≤ x / M + 1 := by
    have hcard : ((Finset.Icc 1 x).filter (fun n => n % M = a)).card ≤
        (Finset.range (x / M + 1)).card := by
      refine Finset.card_le_card_of_injOn (fun n => n / M) ?_ ?_
      · intro n hn
        rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hn
        rw [Finset.mem_coe, Finset.mem_range]
        exact Nat.lt_succ_of_le (Nat.div_le_div_right hn.1.2)
      · intro n₁ hn₁ n₂ hn₂ heq
        dsimp only at heq
        rw [Finset.mem_coe, Finset.mem_filter] at hn₁ hn₂
        have h1 := Nat.div_add_mod n₁ M
        have h2 := Nat.div_add_mod n₂ M
        rw [heq, hn₁.2] at h1
        rw [hn₂.2] at h2
        omega
    simpa using hcard
  have hdiv_le : ((x / M : ℕ) : ℝ) ≤ (x : ℝ) / (M : ℝ) := by
    rw [le_div_iff₀ hM_pos]
    exact_mod_cast Nat.div_mul_le_self x M
  have hdiv_gt : (x : ℝ) / (M : ℝ) ≤ ((x / M : ℕ) : ℝ) + 1 := by
    rw [div_le_iff₀ hM_pos]
    have hlt : x < (x / M + 1) * M := by
      have h1 := Nat.div_add_mod x M
      have h2 := Nat.mod_lt x hM
      nlinarith
    have hcast : (x : ℝ) < ((x / M + 1 : ℕ) : ℝ) * (M : ℝ) := by exact_mod_cast hlt
    push_cast at hcast
    linarith
  have hlo : ((x / M : ℕ) : ℝ) ≤ (((Finset.Icc 1 x).filter (fun n => n % M = a)).card : ℝ) := by
    exact_mod_cast hlower
  have hhi : (((Finset.Icc 1 x).filter (fun n => n % M = a)).card : ℝ) ≤ ((x / M : ℕ) : ℝ) + 1 := by
    exact_mod_cast hupper
  rw [abs_le]
  constructor <;> linarith

private lemma sum_powersetCard_prod_le {α : Type*} [DecidableEq α]
    (Q : Finset α) (f : α → ℝ) (hf : ∀ q ∈ Q, 0 ≤ f q) (j : ℕ) :
    ∑ S ∈ Q.powersetCard j, ∏ q ∈ S, f q ≤ (∑ q ∈ Q, f q) ^ j / (j.factorial : ℝ) := by
  induction j with
  | zero =>
    simp
  | succ j ih =>
    have hdouble : ((j + 1 : ℕ) : ℝ) * ∑ S ∈ Q.powersetCard (j + 1), ∏ q ∈ S, f q ≤
        (∑ q ∈ Q, f q) * ∑ T ∈ Q.powersetCard j, ∏ p ∈ T, f p := by
      have hlhs : ((j + 1 : ℕ) : ℝ) * ∑ S ∈ Q.powersetCard (j + 1), ∏ q ∈ S, f q =
          ∑ S ∈ Q.powersetCard (j + 1), ∑ q ∈ S, f q * ∏ p ∈ S.erase q, f p := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun S hS => ?_
        have hcard : S.card = j + 1 := (Finset.mem_powersetCard.mp hS).2
        have hterm : ∀ q ∈ S, f q * ∏ p ∈ S.erase q, f p = ∏ p ∈ S, f p :=
          fun q hq => Finset.mul_prod_erase S f hq
        rw [Finset.sum_congr rfl hterm, Finset.sum_const, hcard, nsmul_eq_mul]
      rw [hlhs]
      have hreidx : ∑ S ∈ Q.powersetCard (j + 1), ∑ q ∈ S, f q * ∏ p ∈ S.erase q, f p =
          ∑ T ∈ Q.powersetCard j, ∑ q ∈ Q \ T, f q * ∏ p ∈ T, f p := by
        rw [Finset.sum_sigma', Finset.sum_sigma']
        refine Finset.sum_bij (fun x _ => ⟨x.1.erase x.2, x.2⟩) ?_ ?_ ?_ ?_
        · rintro ⟨S, q⟩ hx
          rw [Finset.mem_sigma] at hx ⊢
          obtain ⟨hS, hqS⟩ := hx
          obtain ⟨hSQ, hcard⟩ := Finset.mem_powersetCard.mp hS
          refine ⟨Finset.mem_powersetCard.mpr ⟨(Finset.erase_subset q S).trans hSQ, ?_⟩,
            Finset.mem_sdiff.mpr ⟨hSQ hqS, Finset.notMem_erase q S⟩⟩
          rw [Finset.card_erase_of_mem hqS, hcard]
          omega
        · rintro ⟨S₁, q₁⟩ hx₁ ⟨S₂, q₂⟩ hx₂ heq
          rw [Sigma.mk.inj_iff] at heq
          obtain ⟨h1, h2⟩ := heq
          have hq : q₁ = q₂ := eq_of_heq h2
          subst hq
          have hqS₁ : q₁ ∈ S₁ := (Finset.mem_sigma.mp hx₁).2
          have hqS₂ : q₁ ∈ S₂ := (Finset.mem_sigma.mp hx₂).2
          have hS : S₁ = S₂ := by
            rw [← Finset.insert_erase hqS₁, ← Finset.insert_erase hqS₂, h1]
          subst hS
          rfl
        · rintro ⟨T, q⟩ hy
          rw [Finset.mem_sigma] at hy
          obtain ⟨hT, hq⟩ := hy
          obtain ⟨hTQ, hTcard⟩ := Finset.mem_powersetCard.mp hT
          obtain ⟨hqQ, hqT⟩ := Finset.mem_sdiff.mp hq
          refine ⟨⟨insert q T, q⟩, ?_, ?_⟩
          · rw [Finset.mem_sigma]
            refine ⟨Finset.mem_powersetCard.mpr ⟨Finset.insert_subset hqQ hTQ, ?_⟩,
              Finset.mem_insert_self q T⟩
            rw [Finset.card_insert_of_notMem hqT, hTcard]
          · simp [Finset.erase_insert hqT]
        · rintro ⟨S, q⟩ _
          rfl
      rw [hreidx]
      have hsub_le : ∑ T ∈ Q.powersetCard j, ∑ q ∈ Q \ T, f q * ∏ p ∈ T, f p ≤
          ∑ T ∈ Q.powersetCard j, ∑ q ∈ Q, f q * ∏ p ∈ T, f p := by
        apply Finset.sum_le_sum
        intro T hT
        have hprod_nonneg : 0 ≤ ∏ p ∈ T, f p :=
          Finset.prod_nonneg fun p hp => hf p ((Finset.mem_powersetCard.mp hT).1 hp)
        exact Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
          fun q hq _ => mul_nonneg (hf q hq) hprod_nonneg
      calc ∑ T ∈ Q.powersetCard j, ∑ q ∈ Q \ T, f q * ∏ p ∈ T, f p
          ≤ ∑ T ∈ Q.powersetCard j, ∑ q ∈ Q, f q * ∏ p ∈ T, f p := hsub_le
        _ = (∑ q ∈ Q, f q) * ∑ T ∈ Q.powersetCard j, ∏ p ∈ T, f p := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun T _ => by rw [← Finset.sum_mul]
    have hsum_nonneg : 0 ≤ ∑ q ∈ Q, f q := Finset.sum_nonneg hf
    have hfac_pos : (0 : ℝ) < (j + 1 : ℕ) := by positivity
    rw [Nat.factorial_succ, Nat.cast_mul, pow_succ]
    calc ∑ S ∈ Q.powersetCard (j + 1), ∏ q ∈ S, f q
        ≤ (∑ q ∈ Q, f q) * (∑ T ∈ Q.powersetCard j, ∏ p ∈ T, f p) / ((j + 1 : ℕ) : ℝ) := by
          rwa [le_div_iff₀ hfac_pos, mul_comm]
      _ ≤ (∑ q ∈ Q, f q) * ((∑ q ∈ Q, f q) ^ j / (j.factorial : ℝ)) / ((j + 1 : ℕ) : ℝ) := by
          gcongr
      _ = (∑ q ∈ Q, f q) ^ j * (∑ q ∈ Q, f q) / (((j + 1 : ℕ) : ℝ) * (j.factorial : ℝ)) := by
          ring

private lemma bonferroni_main_term_le
    (Q : Finset ℕ) (k r : ℕ) (hk : 1 ≤ k) (hQ : ∀ q ∈ Q, k ≤ q)
    (hr : 12 * ((k : ℝ) * ∑ q ∈ Q, (1 : ℝ) / q) ≤ 2 * (r : ℝ)) :
    ∑ S ∈ Q.powerset.filter (fun S => S.card ≤ 2 * r), ∏ q ∈ S, (-(k : ℝ) / q) ≤
      2 * Real.exp (-((k : ℝ) * ∑ q ∈ Q, (1 : ℝ) / q)) := by
  let f : ℕ → ℝ := fun q => (k : ℝ) / q
  let U : ℝ := (k : ℝ) * ∑ q ∈ Q, (1 : ℝ) / q
  have hU_eq : ∑ q ∈ Q, f q = U := by
    dsimp only [f, U]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => by ring
  have hf_nonneg : ∀ q ∈ Q, 0 ≤ f q := fun q _ => by dsimp only [f]; positivity
  have hU_nonneg : 0 ≤ U := by rw [← hU_eq]; exact Finset.sum_nonneg hf_nonneg
  have hfull : ∏ q ∈ Q, (1 - f q) = ∑ S ∈ Q.powerset, ∏ q ∈ S, (-f q) := by
    have h := Finset.prod_one_add (s := Q) (f := fun q => -f q)
    simpa [sub_eq_add_neg] using h
  have hsplit : ∑ S ∈ Q.powerset.filter (fun S => S.card ≤ 2 * r), ∏ q ∈ S, (-f q) =
      ∏ q ∈ Q, (1 - f q) -
      ∑ S ∈ Q.powerset.filter (fun S => 2 * r < S.card), ∏ q ∈ S, (-f q) := by
    rw [hfull]
    have hadd := Finset.sum_filter_add_sum_filter_not Q.powerset
      (fun S => S.card ≤ 2 * r) (fun S => ∏ q ∈ S, (-f q))
    simp only [not_le] at hadd
    linarith
  have hneg_eq : ∀ S : Finset ℕ, ∏ q ∈ S, (-(k : ℝ) / q) = ∏ q ∈ S, (-f q) := by
    intro S
    refine Finset.prod_congr rfl fun q _ => by dsimp only [f]; ring
  rw [Finset.sum_congr rfl (fun S _ => hneg_eq S), hsplit]
  have hprod_le : ∏ q ∈ Q, (1 - f q) ≤ Real.exp (-U) := by
    rw [← hU_eq, ← Finset.sum_neg_distrib, Real.exp_sum]
    apply Finset.prod_le_prod
    · intro q hq
      have hqk : k ≤ q := hQ q hq
      have hq_nat : 0 < q := by omega
      have hq_pos : (0 : ℝ) < q := by exact_mod_cast hq_nat
      dsimp only [f]
      rw [sub_nonneg, div_le_one hq_pos]
      exact_mod_cast hqk
    · intro q _
      linarith [Real.add_one_le_exp (-f q)]
  have htail_le : |∑ S ∈ Q.powerset.filter (fun S => 2 * r < S.card), ∏ q ∈ S, (-f q)| ≤
      Real.exp (-U) := by
    calc |∑ S ∈ Q.powerset.filter (fun S => 2 * r < S.card), ∏ q ∈ S, (-f q)|
        ≤ ∑ S ∈ Q.powerset.filter (fun S => 2 * r < S.card), |∏ q ∈ S, (-f q)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ S ∈ Q.powerset.filter (fun S => 2 * r < S.card), ∏ q ∈ S, f q := by
          refine Finset.sum_congr rfl fun S hS => ?_
          rw [Finset.abs_prod]
          refine Finset.prod_congr rfl fun q hq => ?_
          rw [abs_neg, abs_of_nonneg (hf_nonneg q ((Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1) hq))]
      _ ≤ ∑ j ∈ Finset.Icc (2 * r + 1) Q.card, ∑ S ∈ Q.powersetCard j, ∏ q ∈ S, f q := by
          rw [← Finset.sum_fiberwise_of_maps_to
            (g := Finset.card) (t := Finset.Icc (2 * r + 1) Q.card)]
          · apply Finset.sum_le_sum
            intro j hj
            have hfilt : (Q.powerset.filter (fun S => 2 * r < S.card)).filter
                (fun S => S.card = j) = Q.powersetCard j := by
              ext S
              simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_powersetCard]
              constructor
              · rintro ⟨⟨hsub, _⟩, hc⟩; exact ⟨hsub, hc⟩
              · rintro ⟨hsub, hc⟩
                exact ⟨⟨hsub, hc ▸ Nat.lt_of_succ_le (Finset.mem_Icc.mp hj).1⟩, hc⟩
            rw [hfilt]
          · intro S hS
            rw [Finset.mem_filter, Finset.mem_powerset] at hS
            rw [Finset.mem_Icc]
            exact ⟨hS.2, Finset.card_le_card hS.1⟩
      _ ≤ ∑ j ∈ Finset.Icc (2 * r + 1) Q.card, U ^ j / (j.factorial : ℝ) := by
          apply Finset.sum_le_sum
          intro j _
          rw [← hU_eq]
          exact sum_powersetCard_prod_le Q f hf_nonneg j
      _ ≤ ∑ j ∈ Finset.Icc (2 * r + 1) Q.card, ((1 : ℝ) / 4) ^ j := by
          apply Finset.sum_le_sum
          intro j hj
          have hj_gt : 2 * r < j := Nat.lt_of_succ_le (Finset.mem_Icc.mp hj).1
          have hj_nat : 0 < j := by omega
          have hj_pos : (0 : ℝ) < j := by exact_mod_cast hj_nat
          have hexp_j : (j : ℝ) ^ j / (j.factorial : ℝ) ≤ Real.exp j :=
            pow_div_factorial_le_exp hj_pos.le j
          have hfac_ge : (j : ℝ) ^ j / Real.exp j ≤ (j.factorial : ℝ) := by
            rw [div_le_iff₀ (Real.exp_pos _)]
            have hfac_pos : (0 : ℝ) < j.factorial := by positivity
            have hmul := (div_le_iff₀ hfac_pos).mp hexp_j
            linarith
          have he3 : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
          have hrat : U * Real.exp 1 / (j : ℝ) ≤ 1 / 4 := by
            rw [div_le_iff₀ hj_pos]
            have hjr : (2 : ℝ) * r ≤ j := by exact_mod_cast hj_gt.le
            nlinarith
          have hrew : U ^ j / ((j : ℝ) ^ j / Real.exp j) = (U * Real.exp 1 / (j : ℝ)) ^ j := by
            have hexp_pow : Real.exp (j : ℝ) = (Real.exp 1) ^ j := by
              rw [← Real.exp_nat_mul, mul_one]
            rw [div_div_eq_mul_div, hexp_pow, ← mul_pow, ← div_pow]
          calc U ^ j / (j.factorial : ℝ)
              ≤ U ^ j / ((j : ℝ) ^ j / Real.exp j) := by gcongr
            _ = (U * Real.exp 1 / (j : ℝ)) ^ j := hrew
            _ ≤ ((1 : ℝ) / 4) ^ j := by gcongr
      _ ≤ ((1 : ℝ) / 4) ^ (2 * r) := by
          have hgeom : ∀ m N : ℕ, ∑ j ∈ Finset.Icc (m + 1) N, ((1 : ℝ) / 4) ^ j ≤
              ((1 : ℝ) / 4) ^ m := by
            intro m N
            rcases le_or_gt N m with hNm | hNm
            · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
              positivity
            · have hmul : (3 / 4 : ℝ) * ∑ j ∈ Finset.Icc (m + 1) N, ((1 : ℝ) / 4) ^ j =
                  ((1 : ℝ) / 4) ^ (m + 1) - ((1 : ℝ) / 4) ^ (N + 1) := by
                have h1 : ∀ j, (3 / 4 : ℝ) * ((1 : ℝ) / 4) ^ j =
                    ((1 : ℝ) / 4) ^ j - ((1 : ℝ) / 4) ^ (j + 1) := fun j => by ring
                rw [Finset.mul_sum, Finset.sum_congr rfl (fun j _ => h1 j)]
                have hIcc : Finset.Icc (m + 1) N = Finset.Ico (m + 1) (N + 1) := by
                  ext j; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
                rw [hIcc]
                exact sum_Ico_sub_succ (fun j => ((1 : ℝ) / 4) ^ j) (m + 1) (N + 1) (by omega)
              have hpos : (0 : ℝ) ≤ ((1 : ℝ) / 4) ^ (N + 1) := by positivity
              have ha_nonneg : (0 : ℝ) ≤ ((1 : ℝ) / 4) ^ m := by positivity
              have hstep : ((1 : ℝ) / 4) ^ (m + 1) = (1 / 4 : ℝ) * ((1 : ℝ) / 4) ^ m := by ring
              linarith
          exact hgeom (2 * r) Q.card
      _ ≤ Real.exp (-U) := by
          have h14 : (1 : ℝ) / 4 ≤ Real.exp (-1) := by
            rw [Real.exp_neg, le_inv_comm₀ (by norm_num) (Real.exp_pos 1)]
            linarith [Real.exp_one_lt_d9]
          calc ((1 : ℝ) / 4) ^ (2 * r)
              ≤ (Real.exp (-1)) ^ (2 * r) := by gcongr
            _ = Real.exp (-((2 * r : ℕ) : ℝ)) := by
                rw [← Real.exp_nat_mul]; congr 1; ring
            _ ≤ Real.exp (-U) := by
                apply Real.exp_le_exp.mpr
                push_cast
                linarith
  have hneg_le : -∑ S ∈ Q.powerset.filter (fun S => 2 * r < S.card), ∏ q ∈ S, (-f q) ≤
      Real.exp (-U) := (neg_le_abs _).trans htail_le
  linarith

private lemma nat_choose_le_pow (n j : ℕ) : n.choose j ≤ n ^ j := by
  rw [Nat.choose_eq_descFactorial_div_factorial]
  exact (Nat.div_le_self _ _).trans (Nat.descFactorial_le_pow n j)

private lemma prime_ktuple_sieve_bound
    (x z y k r : ℕ) (hk : 1 ≤ k) (hzy : z < y)
    (D : Finset ℕ) (hD_card : D.card = k) (hD_le : ∀ d ∈ D, d ≤ z)
    (hr : 12 * ((k : ℝ) * ∑ q ∈ Nat.primesLE y \ Nat.primesLE z, (1 : ℝ) / q) ≤ 2 * (r : ℝ)) :
    (((Finset.Icc 1 x).filter (fun p => ∀ d ∈ D, d < p ∧ (p - d).Prime)).card : ℝ) ≤
      (y + z : ℝ) +
      2 * (x : ℝ) * Real.exp (-((k : ℝ) * ∑ q ∈ Nat.primesLE y \ Nat.primesLE z, (1 : ℝ) / q)) +
      ((2 * r + 1 : ℕ) : ℝ) * ((k : ℝ) * (y : ℝ)) ^ (2 * r) := by
  classical
  let Q := Nat.primesLE y \ Nat.primesLE z
  have hQ_props : ∀ q ∈ Q, q.Prime ∧ z < q ∧ q ≤ y := by
    intro q hq
    rw [Finset.mem_sdiff, Nat.mem_primesLE, Nat.mem_primesLE] at hq
    refine ⟨hq.1.2, ?_, hq.1.1⟩
    by_contra hle
    exact hq.2 ⟨by omega, hq.1.2⟩
  have hQ_ge_k : ∀ q ∈ Q, k ≤ q := by
    intro q hq
    have hD_sub : D ⊆ Finset.Icc 0 z := fun d hd => Finset.mem_Icc.mpr ⟨Nat.zero_le d, hD_le d hd⟩
    have hk_le : k ≤ z + 1 := by
      rw [← hD_card]
      exact (Finset.card_le_card hD_sub).trans (by simp)
    have hzq : z < q := (hQ_props q hq).2.1
    omega
  let Good := (Finset.Icc 1 x).filter (fun p => ∀ d ∈ D, d < p ∧ (p - d).Prime)
  let GoodSmall := Good.filter (fun p => p ≤ y + z)
  let GoodLarge := Good.filter (fun p => y + z < p)
  have hGood_split : Good.card = GoodSmall.card + GoodLarge.card := by
    simpa [GoodSmall, GoodLarge, not_le] using (Finset.card_filter_add_card_filter_not
      (s := Good) (p := fun p => p ≤ y + z)).symm
  have hSmall_le : GoodSmall.card ≤ y + z := by
    have hsub : GoodSmall ⊆ Finset.Icc 1 (y + z) := by
      intro p hp
      rw [Finset.mem_filter] at hp
      rw [Finset.mem_Icc]
      exact ⟨(Finset.mem_Icc.mp (Finset.mem_filter.mp hp.1).1).1, hp.2⟩
    exact (Finset.card_le_card hsub).trans (by simp)
  let E : ℕ → Finset ℕ := fun n => Q.filter (fun q => ∃ d ∈ D, n % q = d)
  have hLarge_E : ∀ p ∈ GoodLarge, E p = ∅ := by
    intro p hp
    rw [Finset.mem_filter] at hp
    obtain ⟨hpG, hpBig⟩ := hp
    have hp_all := (Finset.mem_filter.mp hpG).2
    rw [Finset.eq_empty_iff_forall_notMem]
    intro q hq
    rw [Finset.mem_filter] at hq
    obtain ⟨hqQ, d, hdD, hmod⟩ := hq
    obtain ⟨hq_prime, hzq, hqy⟩ := hQ_props q hqQ
    obtain ⟨hdp, hpd_prime⟩ := hp_all d hdD
    have hdz : d ≤ z := hD_le d hdD
    have hq_dvd : q ∣ p - d := by
      have h1 : p % q = d % q := by rw [hmod, Nat.mod_eq_of_lt (lt_of_le_of_lt hdz hzq)]
      exact (Nat.modEq_iff_dvd' hdp.le).mp h1.symm
    have hpd_gt : q < p - d := by omega
    rcases (Nat.dvd_prime hpd_prime).mp hq_dvd with hq1 | hqeq
    · exact hq_prime.ne_one hq1
    · omega
  let Qsmall := Q.powerset.filter (fun S => S.card ≤ 2 * r)
  have hLarge_le : (GoodLarge.card : ℝ) ≤
      ∑ n ∈ Finset.Icc 1 x, ∑ S ∈ Qsmall, if S ⊆ E n then (-1 : ℝ) ^ S.card else 0 := by
    calc (GoodLarge.card : ℝ)
        = ∑ n ∈ Finset.Icc 1 x, if n ∈ GoodLarge then (1 : ℝ) else 0 := by
          rw [← Finset.sum_filter]
          have hfilt : (Finset.Icc 1 x).filter (fun n => n ∈ GoodLarge) = GoodLarge := by
            ext n; simp only [Finset.mem_filter]
            exact ⟨fun h => h.2, fun h => ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp h).1).1, h⟩⟩
          rw [hfilt, Finset.sum_const, nsmul_eq_mul, mul_one]
      _ ≤ ∑ n ∈ Finset.Icc 1 x, if E n = ∅ then (1 : ℝ) else 0 := by
          apply Finset.sum_le_sum
          intro n _
          split_ifs with h1 h2
          · exact le_rfl
          · exact absurd (hLarge_E n h1) h2
          · norm_num
          · exact le_rfl
      _ ≤ ∑ n ∈ Finset.Icc 1 x,
            ∑ S ∈ (E n).powerset.filter (fun S => S.card ≤ 2 * r), (-1 : ℝ) ^ S.card := by
          exact Finset.sum_le_sum fun n _ => bonferroni_finset (E n) r
      _ = ∑ n ∈ Finset.Icc 1 x,
            ∑ S ∈ Qsmall, if S ⊆ E n then (-1 : ℝ) ^ S.card else 0 := by
          refine Finset.sum_congr rfl fun n _ => ?_
          rw [← Finset.sum_filter]
          refine Finset.sum_congr ?_ (fun _ _ => rfl)
          ext S
          simp only [Qsmall, Finset.mem_filter, Finset.mem_powerset]
          exact ⟨fun ⟨h1, h2⟩ => ⟨⟨h1.trans (Finset.filter_subset _ Q), h2⟩, h1⟩,
            fun ⟨⟨_, h2⟩, h1⟩ => ⟨h1, h2⟩⟩
  rw [Finset.sum_comm] at hLarge_le
  have hswap : ∑ S ∈ Qsmall, ∑ n ∈ Finset.Icc 1 x, (if S ⊆ E n then (-1 : ℝ) ^ S.card else 0) =
      ∑ S ∈ Qsmall, (-1 : ℝ) ^ S.card *
        (((Finset.Icc 1 x).filter (fun n => ∀ q ∈ S, ∃ d ∈ D, n % q = d)).card : ℝ) := by
    refine Finset.sum_congr rfl fun S hS => ?_
    have hSQ : S ⊆ Q := Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
    have hfilt_eq : (Finset.Icc 1 x).filter (fun n => S ⊆ E n) =
        (Finset.Icc 1 x).filter (fun n => ∀ q ∈ S, ∃ d ∈ D, n % q = d) := by
      ext n
      simp only [Finset.mem_filter, E]
      constructor
      · rintro ⟨hn, hsub⟩
        exact ⟨hn, fun q hq => (Finset.mem_filter.mp (hsub hq)).2⟩
      · rintro ⟨hn, hall⟩
        exact ⟨hn, fun q hq => Finset.mem_filter.mpr ⟨hSQ hq, hall q hq⟩⟩
    rw [hfilt_eq]
  rw [hswap] at hLarge_le
  have happrox : ∀ S ∈ Qsmall,
      |(((Finset.Icc 1 x).filter (fun n => ∀ q ∈ S, ∃ d ∈ D, n % q = d)).card : ℝ) -
        (x : ℝ) * ((k : ℝ) ^ S.card / ((∏ q ∈ S, q : ℕ) : ℝ))| ≤ (k : ℝ) ^ S.card := by
    intro S hS
    have hSQ : S ⊆ Q := Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1
    have hS_props : ∀ q ∈ S, q.Prime ∧ z < q :=
      fun q hq => ⟨(hQ_props q (hSQ hq)).1, (hQ_props q (hSQ hq)).2.1⟩
    let M := ∏ q ∈ S, q
    have hM_pos : 0 < M := Finset.prod_pos fun q hq => (hS_props q hq).1.pos
    let A := (Finset.range M).filter (fun a => ∀ q ∈ S, ∃ d ∈ D, a % q = d)
    have hA_card : A.card = k ^ S.card := by
      rw [← hD_card]
      exact card_residue_classes_crt D z hD_le S hS_props
    have hfib : ((Finset.Icc 1 x).filter (fun n => ∀ q ∈ S, ∃ d ∈ D, n % q = d)).card =
        ∑ a ∈ A, ((Finset.Icc 1 x).filter (fun n => n % M = a)).card := by
      have h1 := Finset.card_eq_sum_card_fiberwise (f := fun n => n % M)
        (s := (Finset.Icc 1 x).filter (fun n => ∀ q ∈ S, ∃ d ∈ D, n % q = d))
        (t := A)
        (fun n hn => by
          rw [Finset.mem_coe, Finset.mem_filter] at hn
          rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
          refine ⟨Nat.mod_lt n hM_pos, fun q hq => ?_⟩
          have hdvd : q ∣ M := Finset.dvd_prod_of_mem (fun x => x) hq
          rw [Nat.mod_mod_of_dvd n hdvd]
          exact hn.2 q hq)
      rw [h1]
      refine Finset.sum_congr rfl fun a ha => ?_
      congr 1
      ext n
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨⟨hn, _⟩, hmod⟩; exact ⟨hn, hmod⟩
      · rintro ⟨hn, hmod⟩
        refine ⟨⟨hn, fun q hq => ?_⟩, hmod⟩
        have hdvd : q ∣ M := Finset.dvd_prod_of_mem (fun x => x) hq
        rw [← Nat.mod_mod_of_dvd n hdvd, hmod]
        exact (Finset.mem_filter.mp ha).2 q hq
    rw [hfib, Nat.cast_sum]
    have hmain_eq : (x : ℝ) * ((k : ℝ) ^ S.card / (M : ℝ)) =
        ∑ _a ∈ A, (x : ℝ) / (M : ℝ) := by
      rw [Finset.sum_const, nsmul_eq_mul, hA_card]
      push_cast
      ring
    rw [hmain_eq, ← Finset.sum_sub_distrib]
    calc |∑ a ∈ A, ((((Finset.Icc 1 x).filter (fun n => n % M = a)).card : ℝ) - (x : ℝ) / (M : ℝ))|
        ≤ ∑ a ∈ A, |(((Finset.Icc 1 x).filter (fun n => n % M = a)).card : ℝ) - (x : ℝ) / (M : ℝ)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _a ∈ A, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro a ha
          exact card_Icc_mod_eq_approx x M a hM_pos (Finset.mem_range.mp (Finset.mem_filter.mp ha).1)
      _ = (k : ℝ) ^ S.card := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_one, hA_card]
          push_cast
          rfl
  have hsum_bound : ∑ S ∈ Qsmall, (-1 : ℝ) ^ S.card *
      (((Finset.Icc 1 x).filter (fun n => ∀ q ∈ S, ∃ d ∈ D, n % q = d)).card : ℝ) ≤
      (x : ℝ) * (∑ S ∈ Qsmall, ∏ q ∈ S, (-(k : ℝ) / q)) +
      ∑ S ∈ Qsmall, (k : ℝ) ^ S.card := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro S hS
    have hprod_eq : (x : ℝ) * ∏ q ∈ S, (-(k : ℝ) / q) =
        (-1 : ℝ) ^ S.card * ((x : ℝ) * ((k : ℝ) ^ S.card / ((∏ q ∈ S, q : ℕ) : ℝ))) := by
      have h1 : ∏ q ∈ S, (-(k : ℝ) / q) =
          ∏ q ∈ S, ((-1 : ℝ) * (k : ℝ) / (q : ℝ)) :=
        Finset.prod_congr rfl fun q _ => by ring
      rw [h1, Finset.prod_div_distrib, Finset.prod_mul_distrib, Finset.prod_const,
        Finset.prod_const, Nat.cast_prod]
      ring
    rw [hprod_eq]
    have hdiff := happrox S hS
    have habs_sign : |(-1 : ℝ) ^ S.card *
        ((((Finset.Icc 1 x).filter (fun n => ∀ q ∈ S, ∃ d ∈ D, n % q = d)).card : ℝ) -
          (x : ℝ) * ((k : ℝ) ^ S.card / ((∏ q ∈ S, q : ℕ) : ℝ)))| ≤ (k : ℝ) ^ S.card := by
      rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
      exact hdiff
    linarith [(le_abs_self _).trans habs_sign]
  have hmain_le : ∑ S ∈ Qsmall, ∏ q ∈ S, (-(k : ℝ) / q) ≤
      2 * Real.exp (-((k : ℝ) * ∑ q ∈ Q, (1 : ℝ) / q)) :=
    bonferroni_main_term_le Q k r hk hQ_ge_k hr
  have herr_le : ∑ S ∈ Qsmall, (k : ℝ) ^ S.card ≤
      ((2 * r + 1 : ℕ) : ℝ) * ((k : ℝ) * (y : ℝ)) ^ (2 * r) := by
    have hQ_card : Q.card ≤ y := by
      have hsub : Q ⊆ Finset.Icc 1 y := by
        intro q hq
        obtain ⟨hq_prime, _, hqy⟩ := hQ_props q hq
        exact Finset.mem_Icc.mpr ⟨hq_prime.one_le, hqy⟩
      exact (Finset.card_le_card hsub).trans (by simp)
    have hky_ge1 : (1 : ℝ) ≤ (k : ℝ) * (y : ℝ) := by
      have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
      have hy1 : (1 : ℝ) ≤ y := by exact_mod_cast (show 1 ≤ y by omega)
      nlinarith
    calc ∑ S ∈ Qsmall, (k : ℝ) ^ S.card
        = ∑ j ∈ Finset.range (2 * r + 1),
            ∑ S ∈ Qsmall.filter (fun S => S.card = j), (k : ℝ) ^ S.card := by
          rw [Finset.sum_fiberwise_of_maps_to
            (fun S hS => Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_filter.mp hS).2))]
      _ = ∑ j ∈ Finset.range (2 * r + 1), (Q.card.choose j : ℝ) * (k : ℝ) ^ j := by
          refine Finset.sum_congr rfl fun j hj => ?_
          have hfilt : Qsmall.filter (fun S => S.card = j) = Q.powersetCard j := by
            ext S
            simp only [Qsmall, Finset.mem_filter, Finset.mem_powerset, Finset.mem_powersetCard]
            exact ⟨fun ⟨⟨h1, _⟩, h2⟩ => ⟨h1, h2⟩,
              fun ⟨h1, h2⟩ => ⟨⟨h1, h2 ▸ Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)⟩, h2⟩⟩
          rw [hfilt]
          calc ∑ S ∈ Q.powersetCard j, (k : ℝ) ^ S.card
              = ∑ _S ∈ Q.powersetCard j, (k : ℝ) ^ j :=
                Finset.sum_congr rfl fun S hS => by rw [(Finset.mem_powersetCard.mp hS).2]
            _ = (Q.card.choose j : ℝ) * (k : ℝ) ^ j := by
                rw [Finset.sum_const, nsmul_eq_mul, Finset.card_powersetCard]
      _ ≤ ∑ _j ∈ Finset.range (2 * r + 1), ((k : ℝ) * (y : ℝ)) ^ (2 * r) := by
          apply Finset.sum_le_sum
          intro j hj
          have hj_le : j ≤ 2 * r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
          have hch : (Q.card.choose j : ℝ) ≤ (y : ℝ) ^ j := by
            have h1 : Q.card.choose j ≤ Q.card ^ j := nat_choose_le_pow Q.card j
            have h2 : Q.card ^ j ≤ y ^ j := Nat.pow_le_pow_left hQ_card j
            exact_mod_cast h1.trans h2
          calc (Q.card.choose j : ℝ) * (k : ℝ) ^ j
              ≤ (y : ℝ) ^ j * (k : ℝ) ^ j := by gcongr
            _ = ((k : ℝ) * (y : ℝ)) ^ j := by rw [mul_pow, mul_comm]
            _ ≤ ((k : ℝ) * (y : ℝ)) ^ (2 * r) := pow_le_pow_right₀ hky_ge1 hj_le
      _ = ((2 * r + 1 : ℕ) : ℝ) * ((k : ℝ) * (y : ℝ)) ^ (2 * r) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hGood_cast : (Good.card : ℝ) = (GoodSmall.card : ℝ) + (GoodLarge.card : ℝ) := by
    exact_mod_cast hGood_split
  have hSmall_cast : (GoodSmall.card : ℝ) ≤ (y + z : ℝ) := by exact_mod_cast hSmall_le
  have hx_nonneg : (0 : ℝ) ≤ x := Nat.cast_nonneg x
  calc (Good.card : ℝ)
      = (GoodSmall.card : ℝ) + (GoodLarge.card : ℝ) := hGood_cast
    _ ≤ (y + z : ℝ) + ((x : ℝ) * (∑ S ∈ Qsmall, ∏ q ∈ S, (-(k : ℝ) / q)) +
          ∑ S ∈ Qsmall, (k : ℝ) ^ S.card) := by linarith [hSmall_cast, hLarge_le, hsum_bound]
    _ ≤ (y + z : ℝ) + ((x : ℝ) * (2 * Real.exp (-((k : ℝ) * ∑ q ∈ Q, (1 : ℝ) / q))) +
          ((2 * r + 1 : ℕ) : ℝ) * ((k : ℝ) * (y : ℝ)) ^ (2 * r)) := by
        gcongr
    _ = (y + z : ℝ) +
        2 * (x : ℝ) * Real.exp (-((k : ℝ) * ∑ q ∈ Q, (1 : ℝ) / q)) +
        ((2 * r + 1 : ℕ) : ℝ) * ((k : ℝ) * (y : ℝ)) ^ (2 * r) := by ring

/- Section 3: Multiscale Lower Bound on Primes Below a Cluster Prime -/

private def localGaps (p w : ℕ) : Finset ℕ :=
  (Finset.Icc 0 w).filter (fun d => (p - d).Prime)

private lemma clusterPrime_odd_coverage {p w : ℕ}
    (hp : Erdos17.IsClusterPrime p) (hw3 : 3 ≤ w) (hwp : w < p) :
    ((Finset.Icc 3 w).filter Odd).card ≤
      Nat.primeCounting w * (localGaps p w).card := by
  classical
  have hp_prime : p.Prime := hp.1
  have hp_odd : Odd p := hp_prime.odd_of_ne_two (by omega)
  let A := Nat.primesLE w
  let B := localGaps p w
  have hsub : (Finset.Icc 3 w).filter Odd ⊆ (A ×ˢ B).image (fun x => x.1 + x.2) := by
    intro m hm
    rw [Finset.mem_filter, Finset.mem_Icc] at hm
    obtain ⟨⟨hm3, hmw⟩, hm_odd⟩ := hm
    have hpm_even : Even (p - m) := by
      obtain ⟨a, ha⟩ := hp_odd
      obtain ⟨b, hb⟩ := hm_odd
      exact ⟨a - b, by omega⟩
    have hpm_le : ((p - m : ℕ) : ℤ) ≤ (p - 3 : ℤ) := by omega
    obtain ⟨q₁, q₂, hq1p, hq2p, hq1le, hq2le, heq⟩ := hp.2 hpm_even hpm_le
    have hq2_ne2 : q₂ ≠ 2 := by
      intro h2
      subst h2
      have hq1_eq : q₁ = (p - m) + 2 := by omega
      have hq1_even : Even q₁ := by
        rw [hq1_eq]
        exact hpm_even.add ⟨1, rfl⟩
      have hq1_eq2 : q₁ = 2 := (Nat.Prime.even_iff hq1p).mp hq1_even
      omega
    have hq2_ge3 : 3 ≤ q₂ := by
      have := hq2p.two_le
      omega
    have hsum : q₂ + (p - q₁) = m := by omega
    rw [Finset.mem_image]
    refine ⟨(q₂, p - q₁), Finset.mem_product.mpr ⟨?_, ?_⟩, hsum⟩
    · rw [Nat.mem_primesLE]
      exact ⟨by omega, hq2p⟩
    · dsimp only [B, localGaps]
      rw [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨Nat.zero_le _, by omega⟩, ?_⟩
      have hsub_eq : p - (p - q₁) = q₁ := by omega
      rwa [hsub_eq]
  calc ((Finset.Icc 3 w).filter Odd).card
      ≤ ((A ×ˢ B).image (fun x => x.1 + x.2)).card := Finset.card_le_card hsub
    _ ≤ (A ×ˢ B).card := Finset.card_image_le
    _ = A.card * B.card := Finset.card_product A B
    _ = Nat.primeCounting w * (localGaps p w).card := by
        rw [Nat.primesLE_card_eq_primeCounting]

private lemma card_odd_Icc_ge (w : ℕ) (hw : 3 ≤ w) :
    (w - 2) / 2 ≤ ((Finset.Icc 3 w).filter Odd).card := by
  have hcard : (Finset.range ((w - 2) / 2)).card ≤ ((Finset.Icc 3 w).filter Odd).card := by
    refine Finset.card_le_card_of_injOn (fun j => 2 * j + 3) ?_ ?_
    · intro j hj
      rw [Finset.mem_coe, Finset.mem_range] at hj
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc]
      dsimp only
      exact ⟨⟨by omega, by omega⟩, ⟨j + 1, by omega⟩⟩
    · intro j₁ _ j₂ _ heq
      dsimp only at heq
      omega
  simpa using hcard

private lemma exists_w0_localGaps_lower :
    ∃ w₀ : ℕ, 100 ≤ w₀ ∧ ∀ p w : ℕ,
      Erdos17.IsClusterPrime p → w₀ ≤ w → w < p →
        Real.log w / 3 ≤ ((localGaps p w).card : ℝ) := by
  have hcheb := Chebyshev.eventually_primeCounting_le (ε := (1 : ℝ) / 20) (by norm_num)
  rw [Filter.eventually_atTop] at hcheb
  obtain ⟨X₀, hX₀⟩ := hcheb
  let w₀ := max 200 (Nat.ceil X₀)
  refine ⟨w₀, by omega, fun p w hp hw hwp => ?_⟩
  have hw200 : 200 ≤ w := le_trans (le_max_left _ _) hw
  have hwX : X₀ ≤ (w : ℝ) :=
    (Nat.le_ceil X₀).trans (by exact_mod_cast le_trans (le_max_right _ _) hw)
  have hpi_le : (Nat.primeCounting w : ℝ) ≤ (Real.log 4 + 1 / 20) * (w : ℝ) / Real.log w := by
    have h := hX₀ (w : ℝ) hwX
    simpa [Nat.floor_natCast] using h
  have hlog4 : Real.log 4 < 1.39 := by
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    linarith [Real.log_two_lt_d9]
  have hpi_le2 : (Nat.primeCounting w : ℝ) ≤ 1.44 * (w : ℝ) / Real.log w := by
    have hlog_pos : 0 < Real.log w := Real.log_pos (by exact_mod_cast (show 1 < w by omega))
    have hw_pos : (0 : ℝ) < w := by positivity
    have hmul : (Real.log 4 + 1 / 20) * (w : ℝ) ≤ 1.44 * (w : ℝ) := by nlinarith
    exact hpi_le.trans (div_le_div_of_nonneg_right hmul hlog_pos.le)
  have hodd_nat : (w - 2) / 2 ≤ ((Finset.Icc 3 w).filter Odd).card := card_odd_Icc_ge w (by omega)
  have hodd_real : 0.48 * (w : ℝ) ≤ (((Finset.Icc 3 w).filter Odd).card : ℝ) := by
    have h1 : (w : ℝ) - 4 ≤ 2 * (((w - 2) / 2 : ℕ) : ℝ) := by
      have : w - 4 ≤ 2 * ((w - 2) / 2) := by omega
      have hcast : ((w - 4 : ℕ) : ℝ) ≤ (2 * ((w - 2) / 2) : ℕ) := by exact_mod_cast this
      rw [Nat.cast_sub (by omega), Nat.cast_mul] at hcast
      push_cast at hcast
      linarith
    have h2 : (((w - 2) / 2 : ℕ) : ℝ) ≤ (((Finset.Icc 3 w).filter Odd).card : ℝ) := by
      exact_mod_cast hodd_nat
    have hw_r : (200 : ℝ) ≤ w := by exact_mod_cast hw200
    linarith
  have hcov : (((Finset.Icc 3 w).filter Odd).card : ℝ) ≤
      (Nat.primeCounting w : ℝ) * ((localGaps p w).card : ℝ) := by
    exact_mod_cast clusterPrime_odd_coverage hp (by omega) hwp
  have hlog_pos : 0 < Real.log w := Real.log_pos (by exact_mod_cast (show 1 < w by omega))
  have hw_pos : (0 : ℝ) < w := by positivity
  have hcard_nonneg : (0 : ℝ) ≤ (localGaps p w).card := Nat.cast_nonneg _
  have hchain : 0.48 * (w : ℝ) ≤ 1.44 * (w : ℝ) / Real.log w * ((localGaps p w).card : ℝ) :=
    hodd_real.trans (hcov.trans (mul_le_mul_of_nonneg_right hpi_le2 hcard_nonneg))
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 3)]
  have h := (mul_le_mul_iff_left₀ hlog_pos).mpr hchain
  field_simp [hlog_pos.ne', hw_pos.ne'] at h
  linarith

private noncomputable def gapBound (w₀ j : ℕ) : ℕ :=
  max w₀ (Nat.floor (Real.exp (3 * (j : ℝ))) + 1)

private lemma gapBound_mono (w₀ : ℕ) : Monotone (gapBound w₀) := by
  intro i j hij
  dsimp only [gapBound]
  apply max_le_max_left
  apply Nat.add_le_add_right
  apply Nat.floor_mono
  apply Real.exp_le_exp.mpr
  have : (i : ℝ) ≤ j := by exact_mod_cast hij
  linarith

private lemma clusterPrime_has_bounded_ktuple
    (w₀ : ℕ) (hw₀_pos : 1 ≤ w₀)
    (hw₀ : ∀ p w : ℕ, Erdos17.IsClusterPrime p → w₀ ≤ w → w < p →
      Real.log w / 3 ≤ ((localGaps p w).card : ℝ))
    (k : ℕ) (p : ℕ) (hp : Erdos17.IsClusterPrime p)
    (hp_big : Nat.ceil (Real.exp (3 * (k : ℝ))) + w₀ + 2 < p) :
    ∃ f : Fin k → ℕ,
      StrictMono f ∧
      (∀ j : Fin k, f j ≤ gapBound w₀ j.1) ∧
      (∀ j : Fin k, f j < p ∧ (p - f j).Prime) := by
  let W := Nat.ceil (Real.exp (3 * (k : ℝ))) + w₀ + 1
  have hW_ge : w₀ ≤ W := by omega
  have hW_lt : W < p := by omega
  have hcard_ge : k ≤ (localGaps p W).card := by
    have h1 := hw₀ p W hp hW_ge hW_lt
    have hW_exp : Real.exp (3 * (k : ℝ)) ≤ (W : ℝ) := by
      have hceil : Real.exp (3 * (k : ℝ)) ≤ (Nat.ceil (Real.exp (3 * (k : ℝ))) : ℝ) :=
        Nat.le_ceil _
      have hle : (Nat.ceil (Real.exp (3 * (k : ℝ))) : ℝ) ≤ (W : ℝ) := by
        exact_mod_cast (show Nat.ceil (Real.exp (3 * (k : ℝ))) ≤ W by omega)
      exact hceil.trans hle
    have hlog : 3 * (k : ℝ) ≤ Real.log W := by
      rw [← Real.log_exp (3 * (k : ℝ))]
      exact Real.log_le_log (Real.exp_pos _) hW_exp
    have hk_le_r : (k : ℝ) ≤ ((localGaps p W).card : ℝ) := by linarith
    exact_mod_cast hk_le_r
  let e : Fin (localGaps p W).card ↪o ℕ := (localGaps p W).orderEmbOfFin rfl
  let f : Fin k → ℕ := fun j => e ⟨j.1, lt_of_lt_of_le j.2 hcard_ge⟩
  have hf_strict : StrictMono f := fun i j hij => e.strictMono (by exact hij)
  have hf_mem : ∀ j : Fin k, f j ∈ localGaps p W := fun j => Finset.orderEmbOfFin_mem _ rfl _
  refine ⟨f, hf_strict, ?_, ?_⟩
  · intro j
    by_cases hfj : f j ≤ w₀
    · exact hfj.trans (le_max_left _ _)
    · push Not at hfj
      let w := f j - 1
      have hw_ge : w₀ ≤ w := by omega
      have hfj_le_W : f j ≤ W := (Finset.mem_Icc.mp (Finset.mem_filter.mp (hf_mem j)).1).2
      have hw_lt : w < p := by omega
      have hsub_card : (localGaps p w).card ≤ j.1 := by
        have hsub : localGaps p w ⊆
            Finset.image (fun i : Fin j.1 => e ⟨i.1, lt_trans i.2 (lt_of_lt_of_le j.2 hcard_ge)⟩)
              Finset.univ := by
          intro d hd
          have hdW : d ∈ localGaps p W := by
            rw [localGaps, Finset.mem_filter, Finset.mem_Icc] at hd ⊢
            exact ⟨⟨hd.1.1, by omega⟩, hd.2⟩
          obtain ⟨idx, hidx⟩ : ∃ idx : Fin (localGaps p W).card, e idx = d := by
            have hmem : d ∈ Set.range e := by
              rw [Finset.range_orderEmbOfFin]
              exact hdW
            exact hmem
          have hd_lt : d < f j := by
            have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).2
            omega
          have hidx_lt : idx.1 < j.1 := by
            have : idx < ⟨j.1, lt_of_lt_of_le j.2 hcard_ge⟩ :=
              e.strictMono.lt_iff_lt.mp (by simpa [f, hidx] using hd_lt)
            exact this
          rw [Finset.mem_image]
          exact ⟨⟨idx.1, hidx_lt⟩, Finset.mem_univ _, hidx⟩
        calc (localGaps p w).card
            ≤ (Finset.image _ Finset.univ).card := Finset.card_le_card hsub
          _ ≤ (Finset.univ : Finset (Fin j.1)).card := Finset.card_image_le
          _ = j.1 := by simp
      have hlog_le : Real.log w / 3 ≤ (j.1 : ℝ) :=
        (hw₀ p w hp hw_ge hw_lt).trans (by exact_mod_cast hsub_card)
      have hw_le_exp : (w : ℝ) ≤ Real.exp (3 * (j.1 : ℝ)) := by
        have hw_pos : (0 : ℝ) < w := by
          have : 1 ≤ w := by omega
          positivity
        rw [← Real.exp_log hw_pos]
        exact Real.exp_le_exp.mpr (by linarith)
      have hw_le_floor : w ≤ Nat.floor (Real.exp (3 * (j.1 : ℝ))) :=
        Nat.le_floor hw_le_exp
      have hfj_le : f j ≤ Nat.floor (Real.exp (3 * (j.1 : ℝ))) + 1 := by omega
      exact hfj_le.trans (le_max_right _ _)
  · intro j
    have hmem := hf_mem j
    rw [localGaps, Finset.mem_filter, Finset.mem_Icc] at hmem
    exact ⟨by omega, hmem.2⟩

/- Section 4: Asymptotic Parameter Optimization -/

private lemma clusterPrimeCount_eq_card_Icc (x : ℕ) [DecidablePred Erdos17.IsClusterPrime] :
    Erdos17.clusterPrimeCount x =
      ((Finset.Icc 1 x).filter Erdos17.IsClusterPrime).card := by
  rw [Erdos17.clusterPrimeCount]
  have hset : {p : ℕ | p ≤ x ∧ Erdos17.IsClusterPrime p} =
      ((Finset.Icc 1 x).filter Erdos17.IsClusterPrime : Set ℕ) := by
    ext p
    simp only [Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨hle, hcp⟩
      exact ⟨⟨hcp.1.one_le, hle⟩, hcp⟩
    · rintro ⟨⟨_, hle⟩, hcp⟩
      exact ⟨hle, hcp⟩
  rw [hset, Nat.card_coe_set_eq, Set.ncard_coe_finset]

private lemma prod_gapBound_le (w₀ k : ℕ) (hw₀ : 1 ≤ w₀) :
    (∏ j : Fin k, ((gapBound w₀ j.1 + 1 : ℕ) : ℝ)) ≤
      ((w₀ + 3 : ℕ) : ℝ) ^ k * Real.exp (3 / 2 * (k : ℝ) ^ 2) := by
  have hterm : ∀ j : Fin k, ((gapBound w₀ j.1 + 1 : ℕ) : ℝ) ≤
      ((w₀ + 3 : ℕ) : ℝ) * Real.exp (3 * (j.1 : ℝ)) := by
    intro j
    have hexp_ge1 : (1 : ℝ) ≤ Real.exp (3 * (j.1 : ℝ)) := Real.one_le_exp (by positivity)
    have hfl : (Nat.floor (Real.exp (3 * (j.1 : ℝ))) : ℝ) ≤ Real.exp (3 * (j.1 : ℝ)) :=
      Nat.floor_le (Real.exp_pos _).le
    have h1 : (gapBound w₀ j.1 : ℝ) ≤ (w₀ : ℝ) + Real.exp (3 * (j.1 : ℝ)) + 1 := by
      dsimp only [gapBound]
      rcases le_total w₀ (Nat.floor (Real.exp (3 * (j.1 : ℝ))) + 1) with h | h
      · rw [max_eq_right h]; push_cast; linarith
      · rw [max_eq_left h]; linarith
    have hw₀r : (1 : ℝ) ≤ w₀ := by exact_mod_cast hw₀
    push_cast
    nlinarith
  calc ∏ j : Fin k, ((gapBound w₀ j.1 + 1 : ℕ) : ℝ)
      ≤ ∏ j : Fin k, (((w₀ + 3 : ℕ) : ℝ) * Real.exp (3 * (j.1 : ℝ))) :=
        Finset.prod_le_prod (fun _ _ => by positivity) (fun j _ => hterm j)
    _ = ((w₀ + 3 : ℕ) : ℝ) ^ k * Real.exp (∑ j : Fin k, 3 * (j.1 : ℝ)) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
          Real.exp_sum]
    _ ≤ ((w₀ + 3 : ℕ) : ℝ) ^ k * Real.exp (3 / 2 * (k : ℝ) ^ 2) := by
        gcongr
        have hsum_nat : 2 * ∑ j ∈ Finset.range k, j ≤ k * k := by
          have h1 := Finset.sum_range_id_mul_two k
          have h2 : k * (k - 1) ≤ k * k := Nat.mul_le_mul_left k (Nat.sub_le k 1)
          linarith only [h1, h2]
        have hsum_fin : ∑ j : Fin k, (j.1 : ℝ) = ∑ j ∈ Finset.range k, (j : ℝ) := by
          rw [Fin.sum_univ_eq_sum_range]
        rw [← Finset.mul_sum, hsum_fin]
        have hcast : 2 * ∑ j ∈ Finset.range k, (j : ℝ) ≤ (k : ℝ) ^ 2 := by
          have h' : ((2 * ∑ j ∈ Finset.range k, j : ℕ) : ℝ) ≤ ((k * k : ℕ) : ℝ) := by
            exact_mod_cast hsum_nat
          push_cast at h'
          linarith only [h']
        linarith only [hcast]

private lemma eventually_clusterPrimeCount_le_exp_neg_one_seventh :
    ∀ᶠ x : ℕ in atTop,
      (Erdos17.clusterPrimeCount x : ℝ) ≤
        (x : ℝ) * Real.exp (-(1 : ℝ) / 7 * (Real.log (Real.log x)) ^ 2) := by
  classical
  obtain ⟨w₀, hw₀_ge, hw₀⟩ := exists_w0_localGaps_lower
  obtain ⟨C_M, hCM_nonneg, hCM⟩ := mertens_second
  have hL_top : Tendsto (fun x : ℕ => Real.log x) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hL2_top : Tendsto (fun x : ℕ => Real.log (Real.log x)) atTop atTop :=
    Real.tendsto_log_atTop.comp hL_top
  have hL3_top : Tendsto (fun x : ℕ => Real.log (Real.log (Real.log x))) atTop atTop :=
    Real.tendsto_log_atTop.comp hL2_top
  have hL2_sq_o_L : ∀ᶠ x : ℕ in atTop,
      (Real.log (Real.log x)) ^ 3 ≤ Real.log x / 10000 := by
    have h := (isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 / 3 by norm_num)).bound
      (show (0 : ℝ) < (1 / 10000 : ℝ) ^ ((1 : ℝ) / 3) by positivity)
    filter_upwards [hL_top.eventually h, hL_top.eventually (eventually_gt_atTop (10 : ℝ))] with x hx hL10
    have hL_pos : 0 < Real.log x := by linarith only [hL10]
    have hL2_pos : 0 < Real.log (Real.log x) := Real.log_pos (by linarith only [hL10])
    rw [Real.norm_of_nonneg hL2_pos.le, Real.norm_of_nonneg (Real.rpow_nonneg hL_pos.le _)] at hx
    have hcube : (Real.log (Real.log x)) ^ 3 ≤
        (((1 / 10000 : ℝ) ^ ((1 : ℝ) / 3)) * (Real.log x) ^ ((1 : ℝ) / 3)) ^ 3 :=
      pow_le_pow_left₀ hL2_pos.le hx 3
    have hrhs : (((1 / 10000 : ℝ) ^ ((1 : ℝ) / 3)) * (Real.log x) ^ ((1 : ℝ) / 3)) ^ 3 =
        Real.log x / 10000 := by
      rw [mul_pow, ← Real.rpow_natCast, ← Real.rpow_natCast,
        ← Real.rpow_mul (by norm_num), ← Real.rpow_mul hL_pos.le]
      norm_num
      ring
    linarith only [hcube, hrhs]
  have hL2_logL2_o_L2sq : ∀ᶠ x : ℕ in atTop,
      (100 + C_M + Real.log (w₀ + 3 : ℕ)) * Real.log (Real.log x) *
        Real.log (Real.log (Real.log x)) ≤
      (1 / 100 : ℝ) * (Real.log (Real.log x)) ^ 2 := by
    let K : ℝ := 100 + C_M + Real.log (w₀ + 3 : ℕ)
    have hK_pos : 0 < K := by
      have hlw : (0 : ℝ) ≤ Real.log (w₀ + 3 : ℕ) :=
        Real.log_nonneg (by exact_mod_cast (show 1 ≤ w₀ + 3 by omega))
      dsimp only [K]; linarith only [hCM_nonneg, hlw]
    have h := (isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 by norm_num)).bound
      (show (0 : ℝ) < (1 / 100 : ℝ) / K by positivity)
    filter_upwards [hL2_top.eventually h,
      hL2_top.eventually (eventually_gt_atTop (10 : ℝ))] with x hx hL2
    have hL2_pos : 0 < Real.log (Real.log x) := by linarith only [hL2]
    have hL3_pos : 0 < Real.log (Real.log (Real.log x)) := Real.log_pos (by linarith only [hL2])
    rw [Real.rpow_one, Real.norm_of_nonneg hL3_pos.le, Real.norm_of_nonneg hL2_pos.le] at hx
    have h1 : K * Real.log (Real.log (Real.log x)) ≤ (1 / 100 : ℝ) * Real.log (Real.log x) := by
      have hmul := mul_le_mul_of_nonneg_left hx hK_pos.le
      have hsimp : K * ((1 / 100 : ℝ) / K * Real.log (Real.log x)) =
          (1 / 100 : ℝ) * Real.log (Real.log x) := by field_simp [hK_pos.ne']
      linarith only [hmul, hsimp]
    nlinarith only [h1, hL2_pos]
  have hL2_large : ∀ᶠ x : ℕ in atTop,
      max (1000 : ℝ) (10 * C_M + 10 * (w₀ : ℝ) + 100) ≤ Real.log (Real.log x) :=
    hL2_top.eventually (eventually_ge_atTop _)
  have hL3_large : ∀ᶠ x : ℕ in atTop, (4 : ℝ) ≤ Real.log (Real.log (Real.log x)) :=
    hL3_top.eventually (eventually_ge_atTop 4)
  filter_upwards [hL2_sq_o_L, hL2_logL2_o_L2sq, hL2_large, hL3_large] with
    x hL2_cube hL2_dom hL2_big hL3_big
  let L : ℝ := Real.log x
  let L₂ : ℝ := Real.log L
  let L₃ : ℝ := Real.log L₂
  have hL2_1000 : (1000 : ℝ) ≤ L₂ := le_trans (le_max_left _ _) hL2_big
  have hL2_CM : 10 * C_M + 10 * (w₀ : ℝ) + 100 ≤ L₂ := le_trans (le_max_right _ _) hL2_big
  have hL_ge : (1000 : ℝ) ≤ L := by
    have h1 : (1000 : ℝ) ^ 3 ≤ L₂ ^ 3 := by gcongr
    have h2 : (1000 : ℝ) ^ 3 ≤ L / 10000 := h1.trans hL2_cube
    linarith only [h2]
  have hL_pos : 0 < L := by linarith only [hL_ge]
  have hx_pos : (0 : ℝ) < x := by
    by_contra h
    push Not at h
    have hx0 : x = 0 := by exact_mod_cast le_antisymm h (Nat.cast_nonneg x)
    simp only [L, hx0, Nat.cast_zero, Real.log_zero] at hL_pos
    linarith only [hL_pos]
  have hx_exp : (x : ℝ) = Real.exp L := (Real.exp_log hx_pos).symm
  let k : ℕ := Nat.floor (L₂ / 3)
  let r : ℕ := Nat.ceil (24 * (k : ℝ) * L₂)
  let y : ℕ := Nat.floor (Real.exp (L / (6 * (r : ℝ))))
  let z : ℕ := gapBound w₀ (k - 1)
  let W : ℕ := Nat.ceil (Real.exp (3 * (k : ℝ))) + w₀ + 2
  have hk_bounds : L₂ / 3 - 1 ≤ (k : ℝ) ∧ (k : ℝ) ≤ L₂ / 3 :=
    ⟨by linarith only [Nat.lt_floor_add_one (L₂ / 3)], Nat.floor_le (by linarith only [hL2_1000])⟩
  have hk_ge1 : 1 ≤ k := by
    have : (1 : ℝ) ≤ (k : ℝ) := by linarith only [hk_bounds.1, hL2_1000]
    exact_mod_cast this
  have hr_bounds : 24 * (k : ℝ) * L₂ ≤ (r : ℝ) ∧ (r : ℝ) ≤ 24 * (k : ℝ) * L₂ + 1 :=
    ⟨Nat.le_ceil _, (Nat.ceil_lt_add_one (by positivity)).le⟩
  have hr_le : (r : ℝ) ≤ 9 * L₂ ^ 2 := by nlinarith only [hr_bounds.2, hk_bounds.2, hL2_1000]
  have hr_ge : (100 : ℝ) ≤ r := by nlinarith only [hr_bounds.1, hk_bounds.1, hL2_1000]
  have hr_pos : (0 : ℝ) < r := by linarith only [hr_ge]
  have hexp3k_le : Real.exp (3 * (k : ℝ)) ≤ L := by
    calc Real.exp (3 * (k : ℝ))
        ≤ Real.exp L₂ := Real.exp_le_exp.mpr (by linarith only [hk_bounds.2])
      _ = L := Real.exp_log hL_pos
  have hz_le : (z : ℝ) ≤ 2 * L := by
    dsimp only [z, gapBound]
    have hfl : (Nat.floor (Real.exp (3 * ((k - 1 : ℕ) : ℝ))) : ℝ) ≤ L := by
      calc (Nat.floor (Real.exp (3 * ((k - 1 : ℕ) : ℝ))) : ℝ)
          ≤ Real.exp (3 * ((k - 1 : ℕ) : ℝ)) := Nat.floor_le (Real.exp_pos _).le
        _ ≤ Real.exp (3 * (k : ℝ)) := by
            apply Real.exp_le_exp.mpr
            have : ((k - 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast Nat.sub_le k 1
            linarith only [this]
        _ ≤ L := hexp3k_le
    have hw₀_le_L : (w₀ : ℝ) ≤ L := by
      have hL2L : L₂ ≤ L := by linarith only [Real.log_le_sub_one_of_pos hL_pos]
      linarith only [hL2_CM, hCM_nonneg, hL2L]
    rcases le_total w₀ (Nat.floor (Real.exp (3 * ((k - 1 : ℕ) : ℝ))) + 1) with h | h
    · rw [max_eq_right h]; push_cast; linarith only [hfl, hL_ge]
    · rw [max_eq_left h]; linarith only [hw₀_le_L, hL_ge]
  have hz_ge2 : 2 ≤ z := le_trans (by omega) (le_max_left w₀ _)
  have hW_le : (W : ℝ) ≤ 2 * L := by
    have hceil : (Nat.ceil (Real.exp (3 * (k : ℝ))) : ℝ) ≤ L + 1 :=
      (Nat.ceil_lt_add_one (Real.exp_pos _).le).le.trans (by linarith only [hexp3k_le])
    have hw₀_le_L2 : (w₀ : ℝ) ≤ L₂ := by linarith only [hL2_CM, hCM_nonneg]
    have hL2_le_L : L₂ ≤ L / 4 := by
      have hL2_sq : L₂ ≤ L₂ ^ 2 := by nlinarith only [hL2_1000]
      have hL2_le_cube : L₂ ≤ L₂ ^ 3 := by nlinarith only [hL2_sq, hL2_1000]
      have hL2_cube' : L₂ ^ 3 ≤ L / 10000 := hL2_cube
      linarith only [hL2_le_cube, hL2_cube', hL_pos]
    have hW_cast : (W : ℝ) = (Nat.ceil (Real.exp (3 * (k : ℝ))) : ℝ) + (w₀ : ℝ) + 2 := by
      dsimp only [W]; push_cast; ring
    linarith only [hceil, hw₀_le_L2, hL2_le_L, hW_cast, hL_ge]
  have hL_div_6r_ge : 100 * L₂ ≤ L / (6 * (r : ℝ)) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [hL2_cube, hr_le, hL2_1000]
  have hy_ge : Real.exp (L / (6 * (r : ℝ))) / 2 ≤ (y : ℝ) := by
    have hexp_ge2 : (2 : ℝ) ≤ Real.exp (L / (6 * (r : ℝ))) := by
      have h1 : (2 : ℝ) ≤ L / (6 * (r : ℝ)) := by linarith only [hL_div_6r_ge, hL2_1000]
      linarith only [Real.add_one_le_exp (L / (6 * (r : ℝ))), h1]
    have hfl := Nat.lt_floor_add_one (Real.exp (L / (6 * (r : ℝ))))
    linarith only [hexp_ge2, hfl]
  have hy_le_exp : (y : ℝ) ≤ Real.exp (L / (6 * (r : ℝ))) :=
    Nat.floor_le (Real.exp_pos _).le
  have hy_gt_z : z < y := by
    have h1 : (2 * L : ℝ) < Real.exp (L / (6 * (r : ℝ))) / 2 := by
      have hlog4 : Real.log 4 < 2 := by
        have h4 : Real.log 4 = 2 * Real.log 2 := by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
          norm_num
        linarith only [h4, Real.log_two_lt_d9]
      have h2 : L₂ + Real.log 4 < L / (6 * (r : ℝ)) := by
        linarith only [hlog4, hL_div_6r_ge, hL2_1000]
      have h3 : Real.exp (L₂ + Real.log 4) < Real.exp (L / (6 * (r : ℝ))) :=
        Real.exp_lt_exp.mpr h2
      rw [Real.exp_add, Real.exp_log hL_pos, Real.exp_log (by norm_num : (0 : ℝ) < 4)] at h3
      linarith only [h3]
    have hcast : (z : ℝ) < (y : ℝ) := lt_of_le_of_lt hz_le (lt_of_lt_of_le h1 hy_ge)
    exact_mod_cast hcast
  have hy_pos : (0 : ℝ) < y := by
    have : 0 < y := by omega
    exact_mod_cast this
  have hy_le_x : (y : ℝ) ≤ (x : ℝ) := by
    rw [hx_exp]
    apply hy_le_exp.trans (Real.exp_le_exp.mpr _)
    have h6r : (1 : ℝ) ≤ 6 * (r : ℝ) := by linarith only [hr_ge]
    exact div_le_self hL_pos.le h6r
  let Q := Nat.primesLE y \ Nat.primesLE z
  let S_inv : ℝ := ∑ q ∈ Q, (1 : ℝ) / q
  have hMert := hCM z y hz_ge2 hy_gt_z
  have hlog_y_ge : L / (12 * (r : ℝ)) ≤ Real.log y := by
    have hexp_pos : 0 < Real.exp (L / (6 * (r : ℝ))) / 2 := by positivity
    have hlog := Real.log_le_log hexp_pos hy_ge
    rw [Real.log_div (Real.exp_pos _).ne' (by norm_num), Real.log_exp] at hlog
    have hlog2 : Real.log 2 < 1 := by linarith only [Real.log_two_lt_d9]
    have hhalf : L / (12 * (r : ℝ)) + 1 ≤ L / (6 * (r : ℝ)) := by
      have h1 : L / (6 * (r : ℝ)) - L / (12 * (r : ℝ)) = L / (12 * (r : ℝ)) := by ring
      have h2 : 1 ≤ L / (12 * (r : ℝ)) := by
        rw [le_div_iff₀ (by positivity)]
        nlinarith only [hL2_cube, hr_le, hL2_1000]
      linarith only [h1, h2]
    linarith only [hlog, hlog2, hhalf]
  have hlog_y_le : Real.log y ≤ L := Real.log_le_log hy_pos hy_le_x
  have hlog_z1_le : Real.log ((z + 1 : ℕ) : ℝ) ≤ 2 * L₂ := by
    have hz1 : ((z + 1 : ℕ) : ℝ) ≤ L ^ 2 := by
      push_cast
      nlinarith only [hz_le, hL_ge]
    calc Real.log ((z + 1 : ℕ) : ℝ) ≤ Real.log (L ^ 2) := Real.log_le_log (by positivity) hz1
      _ = 2 * L₂ := by rw [Real.log_pow]; norm_num; rfl
  have hlog_z1_ge : (1 : ℝ) ≤ Real.log ((z + 1 : ℕ) : ℝ) := by
    have hz1 : Real.exp 1 ≤ ((z + 1 : ℕ) : ℝ) := by
      have h3 : (3 : ℝ) ≤ (z + 1 : ℕ) := by exact_mod_cast (show 3 ≤ z + 1 by omega)
      linarith only [h3, Real.exp_one_lt_d9]
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hz1
  have hS_upper : S_inv ≤ 2 * L₂ := by
    have h1 := (abs_le.mp hMert).2
    have hll_y : Real.log (Real.log y) ≤ L₂ := by
      have hly_pos : 0 < Real.log y := lt_of_lt_of_le (by positivity) hlog_y_ge
      exact Real.log_le_log hly_pos hlog_y_le
    have hll_z : 0 ≤ Real.log (Real.log ((z + 1 : ℕ) : ℝ)) := Real.log_nonneg hlog_z1_ge
    push_cast at h1 hll_z
    linarith only [h1, hll_y, hll_z, hL2_CM, hCM_nonneg]
  have hr_cond : 12 * ((k : ℝ) * S_inv) ≤ 2 * (r : ℝ) := by
    have hk_nonneg : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    nlinarith only [hr_bounds.1, hS_upper, hk_nonneg]
  have hS_lower : L₂ - 4 * L₃ - C_M - 10 ≤ S_inv := by
    have h1 := (abs_le.mp hMert).1
    have hll_y : L₂ - Real.log (12 * (r : ℝ)) ≤ Real.log (Real.log y) := by
      have hpos : 0 < L / (12 * (r : ℝ)) := by positivity
      have h := Real.log_le_log hpos hlog_y_ge
      rw [Real.log_div hL_pos.ne' (by positivity)] at h
      exact h
    have hlog12r : Real.log (12 * (r : ℝ)) ≤ 2 * L₃ + 5 := by
      have h12r : 12 * (r : ℝ) ≤ 108 * L₂ ^ 2 := by nlinarith only [hr_le]
      have hlog108 : Real.log 108 ≤ 5 := by
        have h108 : (108 : ℝ) ≤ (Real.exp 1) ^ 5 := by
          have he : (2.71 : ℝ) ≤ Real.exp 1 := by linarith only [Real.exp_one_gt_d9]
          calc (108 : ℝ) ≤ (2.71 : ℝ) ^ 5 := by norm_num
            _ ≤ (Real.exp 1) ^ 5 := by gcongr
        rw [← Real.exp_nat_mul, mul_one] at h108
        have h := Real.log_le_log (by norm_num : (0 : ℝ) < 108) h108
        rwa [Real.log_exp] at h
      calc Real.log (12 * (r : ℝ))
          ≤ Real.log (108 * L₂ ^ 2) := Real.log_le_log (by positivity) h12r
        _ = Real.log 108 + 2 * L₃ := by
            rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
            norm_num
            rfl
        _ ≤ 2 * L₃ + 5 := by linarith only [hlog108]
    have hll_z : Real.log (Real.log ((z + 1 : ℕ) : ℝ)) ≤ L₃ + 1 := by
      have hz1_pos : 0 < Real.log ((z + 1 : ℕ) : ℝ) := by linarith only [hlog_z1_ge]
      calc Real.log (Real.log ((z + 1 : ℕ) : ℝ))
          ≤ Real.log (2 * L₂) := Real.log_le_log hz1_pos hlog_z1_le
        _ = Real.log 2 + L₃ := Real.log_mul (by norm_num) (by linarith only [hL2_1000])
        _ ≤ L₃ + 1 := by linarith only [Real.log_two_lt_d9]
    push_cast at h1 hll_z
    change -C_M ≤ S_inv - (Real.log (Real.log (y : ℝ)) - Real.log (Real.log ((z : ℝ) + 1))) at h1
    linarith only [h1, hll_y, hlog12r, hll_z, hL3_big]
  let Tuples : Finset (Fin k → ℕ) :=
    (Fintype.piFinset (fun j : Fin k => Finset.Icc 0 (gapBound w₀ j.1))).filter StrictMono
  have hcover : (Finset.Icc 1 x).filter Erdos17.IsClusterPrime ⊆
      Finset.Icc 1 W ∪
        Tuples.biUnion (fun f =>
          (Finset.Icc 1 x).filter (fun p =>
            ∀ d ∈ Finset.univ.image f, d < p ∧ (p - d).Prime)) := by
    intro p hp
    rw [Finset.mem_filter, Finset.mem_Icc] at hp
    obtain ⟨⟨hp1, hpx⟩, hcp⟩ := hp
    rw [Finset.mem_union]
    by_cases hpW : p ≤ W
    · exact Or.inl (Finset.mem_Icc.mpr ⟨hp1, hpW⟩)
    · right
      push Not at hpW
      obtain ⟨f, hf_strict, hf_le, hf_prime⟩ :=
        clusterPrime_has_bounded_ktuple w₀ (by omega) hw₀ k p hcp hpW
      rw [Finset.mem_biUnion]
      refine ⟨f, ?_, ?_⟩
      · rw [Finset.mem_filter, Fintype.mem_piFinset]
        exact ⟨fun j => Finset.mem_Icc.mpr ⟨Nat.zero_le _, hf_le j⟩, hf_strict⟩
      · rw [Finset.mem_filter, Finset.mem_Icc]
        refine ⟨⟨hp1, hpx⟩, fun d hd => ?_⟩
        obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hd
        exact hf_prime j
  have hcount_le : (Erdos17.clusterPrimeCount x : ℝ) ≤
      (W : ℝ) + (Tuples.card : ℝ) *
        ((y + z : ℝ) + 2 * (x : ℝ) * Real.exp (-((k : ℝ) * S_inv)) +
          ((2 * r + 1 : ℕ) : ℝ) * ((k : ℝ) * (y : ℝ)) ^ (2 * r)) := by
    rw [clusterPrimeCount_eq_card_Icc]
    have h1 : ((Finset.Icc 1 x).filter Erdos17.IsClusterPrime).card ≤
        (Finset.Icc 1 W).card +
          ∑ f ∈ Tuples, ((Finset.Icc 1 x).filter (fun p =>
            ∀ d ∈ Finset.univ.image f, d < p ∧ (p - d).Prime)).card :=
      (Finset.card_le_card hcover).trans (Finset.card_union_le _ _ |>.trans
        (Nat.add_le_add_left Finset.card_biUnion_le _))
    have h1r : (((Finset.Icc 1 x).filter Erdos17.IsClusterPrime).card : ℝ) ≤
        (W : ℝ) + ∑ f ∈ Tuples, (((Finset.Icc 1 x).filter (fun p =>
          ∀ d ∈ Finset.univ.image f, d < p ∧ (p - d).Prime)).card : ℝ) := by
      have hcardW : (Finset.Icc 1 W).card = W := by simp
      rw [hcardW] at h1
      exact_mod_cast h1
    refine h1r.trans ?_
    gcongr
    have hper : ∀ f ∈ Tuples,
        (((Finset.Icc 1 x).filter (fun p =>
          ∀ d ∈ Finset.univ.image f, d < p ∧ (p - d).Prime)).card : ℝ) ≤
        (y + z : ℝ) + 2 * (x : ℝ) * Real.exp (-((k : ℝ) * S_inv)) +
          ((2 * r + 1 : ℕ) : ℝ) * ((k : ℝ) * (y : ℝ)) ^ (2 * r) := by
      intro f hf
      rw [Finset.mem_filter, Fintype.mem_piFinset] at hf
      obtain ⟨hf_mem, hf_strict⟩ := hf
      have hD_card : (Finset.univ.image f).card = k := by
        rw [Finset.card_image_of_injective _ hf_strict.injective, Finset.card_univ, Fintype.card_fin]
      have hD_le : ∀ d ∈ Finset.univ.image f, d ≤ z := by
        intro d hd
        obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hd
        have hj_le : f j ≤ gapBound w₀ j.1 := (Finset.mem_Icc.mp (hf_mem j)).2
        exact hj_le.trans (gapBound_mono w₀ (Nat.le_sub_one_of_lt j.2))
      exact prime_ktuple_sieve_bound x z y k r hk_ge1 hy_gt_z
        (Finset.univ.image f) hD_card hD_le hr_cond
    calc ∑ f ∈ Tuples, (((Finset.Icc 1 x).filter (fun p =>
            ∀ d ∈ Finset.univ.image f, d < p ∧ (p - d).Prime)).card : ℝ)
        ≤ ∑ _f ∈ Tuples, ((y + z : ℝ) + 2 * (x : ℝ) * Real.exp (-((k : ℝ) * S_inv)) +
            ((2 * r + 1 : ℕ) : ℝ) * ((k : ℝ) * (y : ℝ)) ^ (2 * r)) :=
          Finset.sum_le_sum hper
      _ = (Tuples.card : ℝ) *
            ((y + z : ℝ) + 2 * (x : ℝ) * Real.exp (-((k : ℝ) * S_inv)) +
              ((2 * r + 1 : ℕ) : ℝ) * ((k : ℝ) * (y : ℝ)) ^ (2 * r)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hTuples_card : (Tuples.card : ℝ) ≤
      Real.exp (3 / 2 * (k : ℝ) ^ 2 + (k : ℝ) * Real.log (w₀ + 3 : ℕ)) := by
    have h1 : Tuples.card ≤ ∏ j : Fin k, (gapBound w₀ j.1 + 1) := by
      calc Tuples.card
          ≤ (Fintype.piFinset (fun j : Fin k => Finset.Icc 0 (gapBound w₀ j.1))).card :=
            Finset.card_filter_le _ _
        _ = ∏ j : Fin k, (Finset.Icc 0 (gapBound w₀ j.1)).card := Fintype.card_piFinset _
        _ = ∏ j : Fin k, (gapBound w₀ j.1 + 1) := by
            refine Finset.prod_congr rfl fun j _ => by simp
    have h1r : (Tuples.card : ℝ) ≤ ∏ j : Fin k, ((gapBound w₀ j.1 + 1 : ℕ) : ℝ) := by
      exact_mod_cast h1
    calc (Tuples.card : ℝ)
        ≤ ((w₀ + 3 : ℕ) : ℝ) ^ k * Real.exp (3 / 2 * (k : ℝ) ^ 2) :=
          h1r.trans (prod_gapBound_le w₀ k (by omega))
      _ = Real.exp ((k : ℝ) * Real.log (w₀ + 3 : ℕ)) * Real.exp (3 / 2 * (k : ℝ) ^ 2) := by
          congr 1
          rw [Real.exp_nat_mul, Real.exp_log (by positivity)]
      _ = Real.exp (3 / 2 * (k : ℝ) ^ 2 + (k : ℝ) * Real.log (w₀ + 3 : ℕ)) := by
          rw [← Real.exp_add]; congr 1; ring
  have hMain_piece : (Tuples.card : ℝ) * (2 * (x : ℝ) * Real.exp (-((k : ℝ) * S_inv))) ≤
      (1 / 3 : ℝ) * (x : ℝ) * Real.exp (-(1 : ℝ) / 7 * L₂ ^ 2) := by
    have hexp_comb : (Tuples.card : ℝ) * Real.exp (-((k : ℝ) * S_inv)) ≤
        Real.exp (3 / 2 * (k : ℝ) ^ 2 + (k : ℝ) * Real.log (w₀ + 3 : ℕ) - (k : ℝ) * S_inv) := by
      calc (Tuples.card : ℝ) * Real.exp (-((k : ℝ) * S_inv))
          ≤ Real.exp (3 / 2 * (k : ℝ) ^ 2 + (k : ℝ) * Real.log (w₀ + 3 : ℕ)) *
              Real.exp (-((k : ℝ) * S_inv)) := by gcongr
        _ = Real.exp (3 / 2 * (k : ℝ) ^ 2 + (k : ℝ) * Real.log (w₀ + 3 : ℕ) - (k : ℝ) * S_inv) := by
            rw [← Real.exp_add, sub_eq_add_neg]
    have hexp_le : 3 / 2 * (k : ℝ) ^ 2 + (k : ℝ) * Real.log (w₀ + 3 : ℕ) - (k : ℝ) * S_inv ≤
        -(1 : ℝ) / 7 * L₂ ^ 2 - 2 := by
      have hkS : (k : ℝ) * (L₂ - 4 * L₃ - C_M - 10) ≤ (k : ℝ) * S_inv :=
        mul_le_mul_of_nonneg_left hS_lower (Nat.cast_nonneg k)
      have hquad : 3 / 2 * (k : ℝ) ^ 2 - (k : ℝ) * L₂ ≤ -(1 : ℝ) / 6 * L₂ ^ 2 + L₂ := by
        nlinarith only [hk_bounds.1, hk_bounds.2, hL2_1000]
      have hlog_w_nonneg : (0 : ℝ) ≤ Real.log (w₀ + 3 : ℕ) :=
        Real.log_nonneg (by exact_mod_cast (show 1 ≤ w₀ + 3 by omega))
      have hlin : (k : ℝ) * (4 * L₃ + C_M + 10 + Real.log (w₀ + 3 : ℕ)) + L₂ + 2 ≤
          (1 / 100 : ℝ) * L₂ ^ 2 := by
        have hk_nonneg : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        have hstep1 : (k : ℝ) * (4 * L₃ + C_M + 10 + Real.log (w₀ + 3 : ℕ)) ≤
            L₂ * (4 * L₃ + C_M + 10 + Real.log (w₀ + 3 : ℕ)) := by
          have hpos : 0 ≤ 4 * L₃ + C_M + 10 + Real.log (w₀ + 3 : ℕ) := by
            linarith only [hL3_big, hCM_nonneg, hlog_w_nonneg]
          nlinarith only [hk_bounds.2, hL2_1000, hpos]
        have hstep2 : 4 * L₃ + C_M + 10 + Real.log (w₀ + 3 : ℕ) + 2 ≤
            (100 + C_M + Real.log (w₀ + 3 : ℕ)) * L₃ := by
          nlinarith only [hL3_big, hCM_nonneg, hlog_w_nonneg]
        have h1 : (k : ℝ) * (4 * L₃ + C_M + 10 + Real.log (w₀ + 3 : ℕ)) + L₂ + 2 ≤
            (100 + C_M + Real.log (w₀ + 3 : ℕ)) * L₂ * L₃ := by
          nlinarith only [hstep1, hstep2, hL2_1000]
        exact h1.trans hL2_dom
      have hgap : (1 / 100 : ℝ) * L₂ ^ 2 ≤ (1 / 6 - 1 / 7 : ℝ) * L₂ ^ 2 := by
        nlinarith only [hL2_1000]
      linarith only [hkS, hquad, hlin, hgap]
    have h6_le : (6 : ℝ) ≤ Real.exp 2 := by
      have he : (2.7 : ℝ) ≤ Real.exp 1 := by linarith only [Real.exp_one_gt_d9]
      calc (6 : ℝ) ≤ (2.7 : ℝ) ^ 2 := by norm_num
        _ ≤ (Real.exp 1) ^ 2 := by gcongr
        _ = Real.exp 2 := by rw [← Real.exp_nat_mul]; norm_num
    have hstep : 2 * Real.exp (-(1 : ℝ) / 7 * L₂ ^ 2 - 2) ≤
        (1 / 3 : ℝ) * Real.exp (-(1 : ℝ) / 7 * L₂ ^ 2) := by
      rw [Real.exp_sub]
      have hexp2_pos : 0 < Real.exp 2 := Real.exp_pos 2
      have hexp_pos : 0 < Real.exp (-(1 : ℝ) / 7 * L₂ ^ 2) := Real.exp_pos _
      rw [mul_div_assoc', div_le_iff₀ hexp2_pos]
      nlinarith only [h6_le, hexp_pos]
    calc (Tuples.card : ℝ) * (2 * (x : ℝ) * Real.exp (-((k : ℝ) * S_inv)))
        = (x : ℝ) * (2 * ((Tuples.card : ℝ) * Real.exp (-((k : ℝ) * S_inv)))) := by ring
      _ ≤ (x : ℝ) * (2 * Real.exp (3 / 2 * (k : ℝ) ^ 2 + (k : ℝ) * Real.log (w₀ + 3 : ℕ) -
            (k : ℝ) * S_inv)) := by gcongr
      _ ≤ (x : ℝ) * (2 * Real.exp (-(1 : ℝ) / 7 * L₂ ^ 2 - 2)) := by gcongr
      _ ≤ (x : ℝ) * ((1 / 3 : ℝ) * Real.exp (-(1 : ℝ) / 7 * L₂ ^ 2)) := by gcongr
      _ = (1 / 3 : ℝ) * (x : ℝ) * Real.exp (-(1 : ℝ) / 7 * L₂ ^ 2) := by ring
  have hErr_piece : (Tuples.card : ℝ) *
      ((y + z : ℝ) + ((2 * r + 1 : ℕ) : ℝ) * ((k : ℝ) * (y : ℝ)) ^ (2 * r)) ≤
      (1 / 3 : ℝ) * (x : ℝ) * Real.exp (-(1 : ℝ) / 7 * L₂ ^ 2) := by
    have hky_ge1 : (1 : ℝ) ≤ (k : ℝ) * (y : ℝ) := by
      have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk_ge1
      have hy1 : (1 : ℝ) ≤ y := by exact_mod_cast (show 1 ≤ y by omega)
      nlinarith only [hk1, hy1]
    have hyz_le : (y + z : ℝ) ≤ ((2 * r + 1 : ℕ) : ℝ) * ((k : ℝ) * (y : ℝ)) ^ (2 * r) := by
      have hyz : (y + z : ℝ) ≤ 2 * (y : ℝ) := by
        have hzy_r : (z : ℝ) ≤ y := by exact_mod_cast hy_gt_z.le
        linarith only [hzy_r]
      have h2r1 : (2 : ℝ) ≤ ((2 * r + 1 : ℕ) : ℝ) := by push_cast; linarith only [hr_ge]
      have hky_pow : (y : ℝ) ≤ ((k : ℝ) * (y : ℝ)) ^ (2 * r) := by
        have h1 : (y : ℝ) ≤ (k : ℝ) * (y : ℝ) := by
          have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk_ge1
          nlinarith only [hk1, hy_pos]
        have h2 : ((k : ℝ) * (y : ℝ)) ^ 1 ≤ ((k : ℝ) * (y : ℝ)) ^ (2 * r) :=
          pow_le_pow_right₀ hky_ge1 (by
            have : 1 ≤ r := by exact_mod_cast (show (1 : ℝ) ≤ r by linarith only [hr_ge])
            omega)
        rw [pow_one] at h2
        exact h1.trans h2
      nlinarith only [hyz, h2r1, hky_pow, hy_pos]
    have hTuples_exp : (Tuples.card : ℝ) ≤ Real.exp (L / 6) := by
      refine hTuples_card.trans (Real.exp_le_exp.mpr ?_)
      have hlog_w_le : Real.log (w₀ + 3 : ℕ) ≤ L₂ := by
        have h1 : ((w₀ + 3 : ℕ) : ℝ) ≤ L₂ := by push_cast; linarith only [hL2_CM, hCM_nonneg]
        exact (Real.log_le_sub_one_of_pos (by positivity)).trans (by linarith only [h1])
      have hk_nonneg : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      have hL2_sq : L₂ ^ 2 ≤ L₂ ^ 3 := by nlinarith only [hL2_1000]
      nlinarith only [hk_bounds.2, hk_nonneg, hlog_w_le, hL2_sq, hL2_cube, hL2_1000]
    have h2r1_exp : (2 * ((2 * r + 1 : ℕ) : ℝ)) ≤ Real.exp (L / 6) := by
      have h1 : 2 * ((2 * r + 1 : ℕ) : ℝ) ≤ L / 6 := by
        push_cast; nlinarith only [hr_le, hL2_cube, hL2_1000]
      linarith only [Real.add_one_le_exp (L / 6), h1]
    have hk_pow_exp : ((k : ℝ) ^ (2 * r)) ≤ Real.exp (L / 6) := by
      have hk_pos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
      have hk_eq : (k : ℝ) ^ (2 * r) = Real.exp (((2 * r : ℕ) : ℝ) * Real.log k) := by
        rw [Real.exp_nat_mul, Real.exp_log hk_pos]
      rw [hk_eq]
      apply Real.exp_le_exp.mpr
      have hlogk : Real.log k ≤ L₂ := by
        calc Real.log k ≤ (k : ℝ) := (Real.log_le_sub_one_of_pos hk_pos).trans (by linarith only)
          _ ≤ L₂ := by linarith only [hk_bounds.2, hL2_1000]
      push_cast
      nlinarith only [hr_le, hr_pos, hlogk, hL2_cube, hL2_1000]
    have hy_pow_exp : ((y : ℝ) ^ (2 * r)) ≤ Real.exp (L / 3) := by
      calc (y : ℝ) ^ (2 * r)
          ≤ (Real.exp (L / (6 * (r : ℝ)))) ^ (2 * r) := by gcongr
        _ = Real.exp (((2 * r : ℕ) : ℝ) * (L / (6 * (r : ℝ)))) := by rw [← Real.exp_nat_mul]
        _ = Real.exp (L / 3) := by
            congr 1; push_cast; field_simp [hr_pos.ne']; ring
    have hprod_exp : (Tuples.card : ℝ) *
        (2 * ((2 * r + 1 : ℕ) : ℝ) * ((k : ℝ) * (y : ℝ)) ^ (2 * r)) ≤
        Real.exp (5 * L / 6) := by
      calc (Tuples.card : ℝ) * (2 * ((2 * r + 1 : ℕ) : ℝ) * ((k : ℝ) * (y : ℝ)) ^ (2 * r))
          = (Tuples.card : ℝ) * (2 * ((2 * r + 1 : ℕ) : ℝ)) *
              ((k : ℝ) ^ (2 * r)) * ((y : ℝ) ^ (2 * r)) := by rw [mul_pow]; ring
        _ ≤ Real.exp (L / 6) * Real.exp (L / 6) * Real.exp (L / 6) * Real.exp (L / 3) := by
            gcongr
        _ = Real.exp (5 * L / 6) := by
            rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
    have hexp_tail : Real.exp (5 * L / 6) ≤
        (1 / 3 : ℝ) * (x : ℝ) * Real.exp (-(1 : ℝ) / 7 * L₂ ^ 2) := by
      rw [hx_exp]
      have h3_le : (3 : ℝ) ≤ Real.exp 2 := by
        have he : (2.7 : ℝ) ≤ Real.exp 1 := by linarith only [Real.exp_one_gt_d9]
        calc (3 : ℝ) ≤ (2.7 : ℝ) ^ 2 := by norm_num
          _ ≤ (Real.exp 1) ^ 2 := by gcongr
          _ = Real.exp 2 := by rw [← Real.exp_nat_mul]; norm_num
      have hgap : 5 * L / 6 + 2 ≤ L - 1 / 7 * L₂ ^ 2 := by nlinarith only [hL2_cube, hL2_1000]
      have h1 : Real.exp (5 * L / 6) * Real.exp 2 ≤
          Real.exp L * Real.exp (-(1 : ℝ) / 7 * L₂ ^ 2) := by
        rw [← Real.exp_add, ← Real.exp_add]
        apply Real.exp_le_exp.mpr
        linarith only [hgap]
      nlinarith only [h3_le, h1, Real.exp_pos (5 * L / 6)]
    calc (Tuples.card : ℝ) *
          ((y + z : ℝ) + ((2 * r + 1 : ℕ) : ℝ) * ((k : ℝ) * (y : ℝ)) ^ (2 * r))
        ≤ (Tuples.card : ℝ) *
            (2 * ((2 * r + 1 : ℕ) : ℝ) * ((k : ℝ) * (y : ℝ)) ^ (2 * r)) :=
          mul_le_mul_of_nonneg_left (by linarith only [hyz_le]) (Nat.cast_nonneg _)
      _ ≤ Real.exp (5 * L / 6) := hprod_exp
      _ ≤ (1 / 3 : ℝ) * (x : ℝ) * Real.exp (-(1 : ℝ) / 7 * L₂ ^ 2) := hexp_tail
  have hW_piece : (W : ℝ) ≤ (1 / 3 : ℝ) * (x : ℝ) * Real.exp (-(1 : ℝ) / 7 * L₂ ^ 2) := by
    rw [hx_exp]
    have h6L : 6 * L ≤ Real.exp (L / 2) := by
      have h2 : (L / 2) ^ 2 / 2 ≤ Real.exp (L / 2) := by
        have h := pow_div_factorial_le_exp (show (0 : ℝ) ≤ L / 2 by linarith only [hL_pos]) 2
        have hfac2 : ((Nat.factorial 2 : ℕ) : ℝ) = 2 := by norm_num [Nat.factorial]
        rwa [hfac2] at h
      nlinarith only [h2, hL_ge]
    have hgap : L / 2 ≤ L - 1 / 7 * L₂ ^ 2 := by nlinarith only [hL2_cube, hL2_1000]
    have h3 : 3 * (W : ℝ) ≤ Real.exp (L - 1 / 7 * L₂ ^ 2) := by
      calc 3 * (W : ℝ) ≤ 6 * L := by linarith only [hW_le]
        _ ≤ Real.exp (L / 2) := h6L
        _ ≤ Real.exp (L - 1 / 7 * L₂ ^ 2) := Real.exp_le_exp.mpr hgap
    have h5 : Real.exp (L - 1 / 7 * L₂ ^ 2) =
        Real.exp L * Real.exp (-(1 : ℝ) / 7 * L₂ ^ 2) := by
      rw [sub_eq_add_neg, Real.exp_add]; congr 2; ring
    linarith only [h3, h5]
  calc (Erdos17.clusterPrimeCount x : ℝ)
      ≤ (W : ℝ) + (Tuples.card : ℝ) *
          ((y + z : ℝ) + 2 * (x : ℝ) * Real.exp (-((k : ℝ) * S_inv)) +
            ((2 * r + 1 : ℕ) : ℝ) * ((k : ℝ) * (y : ℝ)) ^ (2 * r)) := hcount_le
    _ = (W : ℝ) +
        (Tuples.card : ℝ) * (2 * (x : ℝ) * Real.exp (-((k : ℝ) * S_inv))) +
        (Tuples.card : ℝ) * ((y + z : ℝ) +
          ((2 * r + 1 : ℕ) : ℝ) * ((k : ℝ) * (y : ℝ)) ^ (2 * r)) := by ring
    _ ≤ (1 / 3 : ℝ) * (x : ℝ) * Real.exp (-(1 : ℝ) / 7 * L₂ ^ 2) +
        (1 / 3 : ℝ) * (x : ℝ) * Real.exp (-(1 : ℝ) / 7 * L₂ ^ 2) +
        (1 / 3 : ℝ) * (x : ℝ) * Real.exp (-(1 : ℝ) / 7 * L₂ ^ 2) := by
        linarith only [hW_piece, hMain_piece, hErr_piece]
    _ = (x : ℝ) * Real.exp (-(1 : ℝ) / 7 * (Real.log (Real.log x)) ^ 2) := by ring

end Erdos17Elsholtz

/- Section 5: Main Theorem -/

theorem OMA.solution : OMA.R_Erdos17_erdos_17_variants_upper_BES_R1.H1 := by
  refine ⟨1, one_pos, fun c hc => ?_⟩
  rw [Asymptotics.isBigOWith_iff]
  filter_upwards [Erdos17Elsholtz.eventually_clusterPrimeCount_le_exp_neg_one_seventh] with x hx
  rw [one_mul, Real.norm_of_nonneg (Nat.cast_nonneg _),
    Real.norm_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le)]
  refine hx.trans ?_
  gcongr
  have hc_lt : c < 1 / 8 := hc.2
  have hsq : 0 ≤ (Real.log (Real.log x)) ^ 2 := sq_nonneg _
  nlinarith only [hc_lt, hsq]
