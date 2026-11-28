import FormalConjectures.ErdosProblems.«726»
import Mathlib

/-! For an odd prime, a change of the upper-half indicator from n to n+1
requires a divisor of n+1 or 2n+1. This gives uniform control of the
oscillation between consecutive checkpoints, (k+1)^2 integers apart in
the dyadic block [2^k,2^(k+1)). The two remaining estimates concern only
primes above (k+3)^4 at the checkpoints. -/

private lemma e726_change_step {p n : ℕ} (hp : Odd p)
    (h : ¬ ((p < 2 * (n % p)) ↔ (p < 2 * ((n + 1) % p)))) :
    p ∣ n + 1 ∨ p ∣ 2*n + 1 := by
  obtain ⟨k, hk⟩ := hp
  have hr := Nat.mod_lt n (show 0 < p by omega)
  have hd := Nat.mod_add_div n p
  by_cases hw : n % p + 1 = p
  · left
    refine ⟨n / p + 1, ?_⟩
    rw [Nat.mul_add, Nat.mul_one]
    omega
  · have hs : n % p + 1 < p := by omega
    have hm : (n+1) % p = n % p + 1 := by
      rw [← Nat.mod_add_mod n p 1, Nat.mod_eq_of_lt hs]
    rw [hm] at h
    have hc : 2*(n%p) + 1 = p := by omega
    right
    refine ⟨2*(n/p) + 1, ?_⟩
    rw [Nat.mul_add, Nat.mul_one, ← Nat.mul_assoc, Nat.mul_comm p 2, Nat.mul_assoc]
    omega

private lemma e726_cutoff_change_step {p n : ℕ} (hp : Odd p)
    (h : ¬ ((p ≤ n ∧ p < 2*(n%p)) ↔ (p ≤ n+1 ∧ p < 2*((n+1)%p)))) :
    p ∣ n+1 ∨ p ∣ 2*n+1 := by
  by_cases hn : p ≤ n
  · have hs : p ≤ n+1 := by omega
    simp only [hn, hs, true_and] at h
    exact e726_change_step hp h
  · by_cases hs : p = n+1
    · exact Or.inl (hs ▸ dvd_refl _)
    · have hnp : ¬ p ≤ n+1 := by omega
      simp [hn, hnp] at h

private lemma e726_product_of_step {p n h : ℕ} (P : ℕ → Prop)
    (step : ∀ t, ¬ (P t ↔ P (t+1)) → p ∣ t+1 ∨ p ∣ 2*t+1)
    (hdiff : ¬ (P n ↔ P (n+h))) :
    p ∣ ∏ j ∈ Finset.range h, (n+j+1)*(2*(n+j)+1) := by
  induction h with
  | zero => simp at hdiff
  | succ t ih =>
    rw [Finset.prod_range_succ]
    by_cases H : P n ↔ P (n+t)
    · have last : ¬ (P (n+t) ↔ P (n+t+1)) := fun hl => hdiff (H.trans hl)
      rcases step (n+t) last with hl | hr
      · exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_left hl _) _
      · exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right hr _) _
    · exact dvd_mul_of_dvd_left (ih H) _

private lemma e726_change_product {p n h : ℕ} (hp : Odd p)
    (hdiff : ¬ ((p < 2*(n%p)) ↔ (p < 2*((n+h)%p)))) :
    p ∣ ∏ j ∈ Finset.range h, (n+j+1)*(2*(n+j)+1) :=
  e726_product_of_step (fun t => p < 2*(t%p)) (fun _ => e726_change_step hp) hdiff

private lemma e726_cutoff_change_product {p n h : ℕ} (hp : Odd p)
    (hdiff : ¬ ((p ≤ n ∧ p < 2*(n%p)) ↔ (p ≤ n+h ∧ p < 2*((n+h)%p)))) :
    p ∣ ∏ j ∈ Finset.range h, (n+j+1)*(2*(n+j)+1) :=
  e726_product_of_step (fun t => p ≤ t ∧ p < 2*(t%p))
    (fun _ => e726_cutoff_change_step hp) hdiff

private lemma e726_oscillation (n h B : ℕ) :
    let S := fun t : ℕ =>
      ∑ p ∈ (Finset.range (t+1)).filter
        (fun p : ℕ => p.Prime ∧ (p:ℝ)/2 < ((t%p:ℕ):ℝ)), (1:ℝ)/p
    let H := ∑ p ∈ (Finset.range (B+1)).filter Nat.Prime, (1:ℝ)/p
    let M := ∏ j ∈ Finset.range h, (n+j+1)*(2*(n+j)+1)
    |S (n+h)-S n| ≤ H + ∑ p ∈ M.primeFactors.filter (B < ·), (1:ℝ)/p := by
  classical
  let T (t : ℕ) := (Finset.range (t+1)).filter
    (fun p : ℕ => p.Prime ∧ (p:ℝ)/2 < ((t%p:ℕ):ℝ))
  let M := ∏ j ∈ Finset.range h, (n+j+1)*(2*(n+j)+1)
  let U := (Finset.range (B+1)).filter Nat.Prime
  let V := M.primeFactors.filter (B < ·)
  let mass (A : Finset ℕ) := ∑ p ∈ A, (1:ℝ)/p
  change |mass (T (n+h)) - mass (T n)| ≤ mass U + mass V
  have mem (p t : ℕ) : p ∈ T t ↔ p.Prime ∧ p ≤ t ∧ p < 2*(t%p) := by
    have hh : (p:ℝ)/2 < ((t%p:ℕ):ℝ) ↔ p < 2*(t%p) := by
      rw [div_lt_iff₀ (by norm_num : 0 < (2:ℝ)), mul_comm]
      exact_mod_cast Iff.rfl
    simp only [T, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff, hh]
    tauto
  have hM : 0 < M := Finset.prod_pos fun j _ => Nat.mul_pos (by omega) (by omega)
  have change_mem (p : ℕ) (hd : ¬ ((p ∈ T n) ↔ (p ∈ T (n+h)))) : p ∈ U ∪ V := by
    simp only [mem] at hd
    by_cases hp : p.Prime
    · simp only [hp, true_and] at hd
      by_cases hB : p ≤ B
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr (by omega), hp⟩)
      · rcases hp.eq_two_or_odd' with rfl | ho
        · omega
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr
            ⟨Nat.mem_primeFactors.mpr ⟨hp,e726_cutoff_change_product ho hd,hM.ne'⟩, by omega⟩)
    · simp [hp] at hd
  have union_bound (A C : Finset ℕ) : mass (A ∪ C) ≤ mass A + mass C := by
    have he := Finset.sum_union_inter (s₁ := A) (s₂ := C) (f := fun p : ℕ => (1:ℝ)/p)
    have hn : 0 ≤ mass (A ∩ C) := Finset.sum_nonneg (by intros; positivity)
    change mass (A ∪ C) + mass (A ∩ C) = mass A + mass C at he
    linarith
  have bound (A C : Finset ℕ) (hd : ∀ p ∈ A, p ∉ C → p ∈ U ∪ V) :
      mass A ≤ mass C + (mass U + mass V) := by
    have hs : A ⊆ C ∪ (U ∪ V) := by
      intro p hp
      by_cases hpc : p ∈ C
      · exact Finset.mem_union_left _ hpc
      · exact Finset.mem_union_right _ (hd p hp hpc)
    calc
      mass A ≤ mass (C ∪ (U ∪ V)) := Finset.sum_le_sum_of_subset_of_nonneg hs
        (by intros; positivity)
      _ ≤ mass C + mass (U ∪ V) := union_bound _ _
      _ ≤ mass C + (mass U + mass V) := add_le_add_right (union_bound U V) _
  have h₁ := bound (T n) (T (n+h)) (fun p hp hpn => change_mem p (fun he => hpn (he.mp hp)))
  have h₂ := bound (T (n+h)) (T n) (fun p hp hpn => change_mem p (fun he => hpn (he.mpr hp)))
  exact abs_le.mpr ⟨by linarith, by linarith⟩

private lemma e726_card_primeFactors {M D : ℕ} (hM : 0 < M) (hD : M ≤ 2 ^ D) :
    M.primeFactors.card ≤ D := by
  have hprod : ∏ _p ∈ M.primeFactors, (2 : ℕ) ≤ ∏ p ∈ M.primeFactors, p :=
    Finset.prod_le_prod' fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le
  have hpow : 2 ^ M.primeFactors.card ≤ 2 ^ D := by
    simpa using hprod.trans ((Nat.le_of_dvd hM M.prod_primeFactors_dvd).trans hD)
  exact (pow_le_pow_iff_right₀ (by decide : 1 < (2 : ℕ))).mp hpow

private lemma e726_large_prime_mass {M D B : ℕ} (hM : 0 < M) (hD : M ≤ 2 ^ D)
    (hB : 0 < B) :
    ∑ p ∈ M.primeFactors.filter (B < ·), (1 : ℝ) / p ≤ (D : ℝ) / B := by
  let S := M.primeFactors.filter (B < ·)
  have hcard : S.card ≤ D :=
    (Finset.card_filter_le _ _).trans (e726_card_primeFactors hM hD)
  calc
    _ ≤ ∑ _p ∈ S, (1 : ℝ) / B := by
      apply Finset.sum_le_sum
      intro p hp
      exact one_div_le_one_div_of_le (by exact_mod_cast hB)
        (by exact_mod_cast (Finset.mem_filter.mp hp).2.le)
    _ = (S.card : ℝ) / B := by simp [div_eq_mul_inv]
    _ ≤ _ := div_le_div_of_nonneg_right (by exact_mod_cast hcard) (by positivity)

private lemma e726_product_le (n h : ℕ) :
    (∏ j ∈ Finset.range h, (n+j+1)*(2*(n+j)+1)) ≤
      2 ^ (2 * h * ((n+h+1).log2 + 2)) := by
  let L := (n+h+1).log2
  have hlt : n+h+1 < 2 ^ (L+1) :=
    (Nat.log2_lt (show n+h+1 ≠ 0 by omega)).mp (Nat.lt_succ_self _)
  have hdouble : 2 ^ (L+2) = 2 ^ (L+1) * 2 := pow_succ ..
  calc
    _ ≤ ∏ _j ∈ Finset.range h, 2^(L+2) * 2^(L+2) := by
      apply Finset.prod_le_prod'
      intro j hj
      have hj' := Finset.mem_range.mp hj
      rw [hdouble]
      exact Nat.mul_le_mul (by omega) (by omega)
    _ = 2 ^ (2 * h * ((n+h+1).log2 + 2)) := by
      rw [Finset.prod_const, Finset.card_range, ← pow_add, ← pow_mul]
      congr 1
      dsimp [L]
      ring

/-- Each member of the k-th dyadic interval is within (k+1)^2 of a grid point. -/
private lemma e726_dyadic_grid {n k : ℕ} (lo : 2^k ≤ n) (hi : n < 2^(k+1)) :
    ∃ j h : ℕ, let x := 2^k + j*(k+1)^2
      n=x+h ∧ x < 2^(k+1) ∧ h < (k+1)^2 := by
  let step := (k+1)^2
  have step_pos : 0 < step := by dsimp [step]; positivity
  let j := (n-2^k)/step
  let h := (n-2^k)%step
  let x := 2^k+j*step
  have partition : n=x+h := by
    have e := Nat.mod_add_div (n-2^k) step
    dsimp [x,j,h]
    rw [Nat.mul_comm step] at e
    omega
  have hsmall : h<step := Nat.mod_lt _ step_pos
  exact ⟨j,h,partition,by change x < _; omega,hsmall⟩

/-
The upper bounds for the first two Mertens theorems below are from the
Left to Solve contribution by @chris01-dev, PR #4205, commit 62ab1ad16.
Source: https://github.com/lefttosolve2/open-math-agents/pull/4205
They use Chebyshev's bound for θ and discrete partial summation.
-/
namespace E726MertensUpper

open Finset

-- Mertens, first theorem (upper bound): the sum of log p / p over primes up to n.
lemma sum_log_div_le (n : ℕ) (hn : 1 ≤ n) :
    ∑ p ∈ Nat.primesLE n, Real.log p / p ≤ Real.log n + Real.log 4 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmem : ∀ p ∈ Nat.primesLE n, p.Prime ∧ p ≤ n := by
    intro p hp
    simp only [Nat.primesLE, Nat.primesBelow, mem_filter, mem_range] at hp
    exact ⟨hp.2, by omega⟩
  have ha : ∑ k ∈ Ioc 0 n, Real.log k ≤ n * Real.log n := by
    calc ∑ k ∈ Ioc 0 n, Real.log k ≤ ∑ _k ∈ Ioc 0 n, Real.log n := by
          apply Finset.sum_le_sum
          intro k hk
          have hk0 : 0 < k := (mem_Ioc.1 hk).1
          have hkn : k ≤ n := (mem_Ioc.1 hk).2
          exact Real.log_le_log (by exact_mod_cast hk0) (by exact_mod_cast hkn)
      _ = n * Real.log n := by simp
  have hb : ∀ k ∈ Ioc 0 n,
      ∑ p ∈ Nat.primesLE n, (if p ∣ k then Real.log p else 0) ≤ Real.log k := by
    intro k hk
    have hk0 : 0 < k := (mem_Ioc.1 hk).1
    have hkn : k ≤ n := (mem_Ioc.1 hk).2
    rw [← Finset.sum_filter]
    have hfe : (Nat.primesLE n).filter (fun p => p ∣ k) = k.primeFactors := by
      ext p
      simp only [Nat.primesLE, Nat.primesBelow, mem_filter, mem_range, Nat.mem_primeFactors]
      constructor
      · rintro ⟨⟨_, hp⟩, hd⟩
        exact ⟨hp, hd, hk0.ne'⟩
      · rintro ⟨hp, hd, _⟩
        have := Nat.le_of_dvd hk0 hd
        exact ⟨⟨by omega, hp⟩, hd⟩
    rw [hfe]
    have hd := Nat.le_of_dvd hk0 (Nat.prod_primeFactors_dvd k)
    have hpos : (0 : ℝ) < ∏ p ∈ k.primeFactors, (p : ℝ) :=
      Finset.prod_pos (fun p hp => by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos)
    calc ∑ p ∈ k.primeFactors, Real.log p = Real.log (∏ p ∈ k.primeFactors, (p : ℝ)) := by
          rw [Real.log_prod]
          intro p hp
          exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
      _ ≤ Real.log k := by
          apply Real.log_le_log hpos
          have hcast : ((∏ p ∈ k.primeFactors, p : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast hd
          push_cast at hcast
          exact hcast
  have hc : ∑ k ∈ Ioc 0 n, ∑ p ∈ Nat.primesLE n, (if p ∣ k then Real.log p else 0) =
      ∑ p ∈ Nat.primesLE n, Real.log p * ((n / p : ℕ) : ℝ) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [← Finset.sum_filter, Finset.sum_const, Nat.Ioc_filter_dvd_card_eq_div, nsmul_eq_mul,
      mul_comm]
  have hd : ∀ p ∈ Nat.primesLE n,
      Real.log p * ((n : ℝ) / p - 1) ≤ Real.log p * ((n / p : ℕ) : ℝ) := by
    intro p hp
    have hpp : p.Prime := (hmem p hp).1
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
    apply mul_le_mul_of_nonneg_left _ (Real.log_nonneg (by exact_mod_cast hpp.one_lt.le))
    have h1 : (n : ℝ) = (p : ℝ) * ((n / p : ℕ) : ℝ) + ((n % p : ℕ) : ℝ) := by
      exact_mod_cast (Nat.div_add_mod n p).symm
    have h2 : ((n % p : ℕ) : ℝ) < p := by exact_mod_cast Nat.mod_lt n hpp.pos
    have h3 : (n : ℝ) / p < ((n / p : ℕ) : ℝ) + 1 := by
      rw [div_lt_iff₀ hp0]
      nlinarith
    linarith
  have hθ : ∑ p ∈ Nat.primesLE n, Real.log p ≤ Real.log 4 * n := by
    rw [← Chebyshev.theta_eq_sum_primesLE_log]
    exact Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg n)
  have hmain : (n : ℝ) * ∑ p ∈ Nat.primesLE n, Real.log p / p - ∑ p ∈ Nat.primesLE n, Real.log p
      ≤ n * Real.log n := by
    calc (n : ℝ) * ∑ p ∈ Nat.primesLE n, Real.log p / p - ∑ p ∈ Nat.primesLE n, Real.log p
        = ∑ p ∈ Nat.primesLE n, Real.log p * ((n : ℝ) / p - 1) := by
          rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl (fun p _ => ?_)
          ring
      _ ≤ ∑ p ∈ Nat.primesLE n, Real.log p * ((n / p : ℕ) : ℝ) := Finset.sum_le_sum hd
      _ = ∑ k ∈ Ioc 0 n, ∑ p ∈ Nat.primesLE n, (if p ∣ k then Real.log p else 0) := hc.symm
      _ ≤ ∑ k ∈ Ioc 0 n, Real.log k := Finset.sum_le_sum hb
      _ ≤ n * Real.log n := ha
  have hfin : (n : ℝ) * ∑ p ∈ Nat.primesLE n, Real.log p / p ≤
      n * (Real.log n + Real.log 4) := by
    rw [mul_add]
    linarith
  exact le_of_mul_le_mul_left hfin hnR

-- Sums over primes up to N as sums over a range, convenient for induction.
lemma primesLE_sum (N : ℕ) (f : ℕ → ℝ) :
    ∑ p ∈ Nat.primesLE N, f p = ∑ p ∈ range (N + 1), (if p.Prime then f p else 0) := by
  rw [Nat.primesLE, Nat.primesBelow, Finset.sum_filter]

-- Mertens, second theorem (upper bound), by discrete partial summation.
lemma sum_inv_primes_le (N : ℕ) (hN : 2 ≤ N) :
    ∑ p ∈ Nat.primesLE N, (1 : ℝ) / p ≤
      Real.log (Real.log N) + (3 - Real.log (Real.log 2)) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have key : ∀ M : ℕ, 2 ≤ M →
      ∑ p ∈ Nat.primesLE M, (1 : ℝ) / p - (∑ p ∈ Nat.primesLE M, Real.log p / p) / Real.log M ≤
        Real.log (Real.log M) - Real.log (Real.log 2) +
          Real.log 4 * (1 / Real.log 2 - 1 / Real.log M) := by
    intro M hM
    induction M, hM using Nat.le_induction with
    | base =>
      have h2 : Nat.primesLE 2 = {2} := by decide
      rw [h2]
      simp only [Finset.sum_singleton, Nat.cast_ofNat]
      have : Real.log 2 / 2 / Real.log 2 = 1 / 2 := by field_simp
      rw [this]
      norm_num
    | succ M hM ih =>
      have hMR : (2 : ℝ) ≤ M := by exact_mod_cast hM
      have hL : 0 < Real.log M := Real.log_pos (by linarith)
      have hL1 : 0 < Real.log ((M + 1 : ℕ) : ℝ) := Real.log_pos (by push_cast; linarith)
      have hLL : Real.log M ≤ Real.log ((M + 1 : ℕ) : ℝ) :=
        Real.log_le_log (by linarith) (by push_cast; linarith)
      have hA := sum_log_div_le M (by omega)
      have hS1 : ∑ p ∈ Nat.primesLE (M + 1), (1 : ℝ) / p =
          ∑ p ∈ Nat.primesLE M, (1 : ℝ) / p +
            (if (M + 1).Prime then (1 : ℝ) / ((M + 1 : ℕ) : ℝ) else 0) := by
        rw [primesLE_sum, primesLE_sum, Finset.sum_range_succ]
      have hA1 : ∑ p ∈ Nat.primesLE (M + 1), Real.log p / p =
          ∑ p ∈ Nat.primesLE M, Real.log p / p +
            (if (M + 1).Prime then Real.log ((M + 1 : ℕ) : ℝ) / ((M + 1 : ℕ) : ℝ) else 0) := by
        rw [primesLE_sum, primesLE_sum, Finset.sum_range_succ]
      have hcancel : (if (M + 1).Prime then (1 : ℝ) / ((M + 1 : ℕ) : ℝ) else 0) -
          (if (M + 1).Prime then Real.log ((M + 1 : ℕ) : ℝ) / ((M + 1 : ℕ) : ℝ) else 0) /
            Real.log ((M + 1 : ℕ) : ℝ) = 0 := by
        split_ifs
        · field_simp
          ring
        · simp
      have hstep : (∑ p ∈ Nat.primesLE M, Real.log p / p) *
          (1 / Real.log M - 1 / Real.log ((M + 1 : ℕ) : ℝ)) ≤
          (Real.log (Real.log ((M + 1 : ℕ) : ℝ)) - Real.log (Real.log M)) +
            Real.log 4 * (1 / Real.log M - 1 / Real.log ((M + 1 : ℕ) : ℝ)) := by
        have hd0 : 0 ≤ 1 / Real.log M - 1 / Real.log ((M + 1 : ℕ) : ℝ) := by
          rw [sub_nonneg]
          exact one_div_le_one_div_of_le hL hLL
        have h1 : (∑ p ∈ Nat.primesLE M, Real.log p / p) *
            (1 / Real.log M - 1 / Real.log ((M + 1 : ℕ) : ℝ)) ≤
            (Real.log M + Real.log 4) * (1 / Real.log M - 1 / Real.log ((M + 1 : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_right hA hd0
        have h2 : Real.log M * (1 / Real.log M - 1 / Real.log ((M + 1 : ℕ) : ℝ)) ≤
            Real.log (Real.log ((M + 1 : ℕ) : ℝ)) - Real.log (Real.log M) := by
          have hx : 0 < Real.log ((M + 1 : ℕ) : ℝ) / Real.log M := div_pos hL1 hL
          have h3 := Real.one_sub_inv_le_log_of_pos hx
          rw [Real.log_div hL1.ne' hL.ne'] at h3
          have e : Real.log M * (1 / Real.log M - 1 / Real.log ((M + 1 : ℕ) : ℝ)) =
              1 - (Real.log ((M + 1 : ℕ) : ℝ) / Real.log M)⁻¹ := by
            field_simp
          rw [e]
          exact h3
        nlinarith
      rw [hS1, hA1]
      have e : ∑ p ∈ Nat.primesLE M, (1 : ℝ) / p +
            (if (M + 1).Prime then (1 : ℝ) / ((M + 1 : ℕ) : ℝ) else 0) -
          (∑ p ∈ Nat.primesLE M, Real.log p / p +
            (if (M + 1).Prime then Real.log ((M + 1 : ℕ) : ℝ) / ((M + 1 : ℕ) : ℝ) else 0)) /
            Real.log ((M + 1 : ℕ) : ℝ) =
          (∑ p ∈ Nat.primesLE M, (1 : ℝ) / p -
            (∑ p ∈ Nat.primesLE M, Real.log p / p) / Real.log M) +
          (∑ p ∈ Nat.primesLE M, Real.log p / p) *
            (1 / Real.log M - 1 / Real.log ((M + 1 : ℕ) : ℝ)) +
          ((if (M + 1).Prime then (1 : ℝ) / ((M + 1 : ℕ) : ℝ) else 0) -
          (if (M + 1).Prime then Real.log ((M + 1 : ℕ) : ℝ) / ((M + 1 : ℕ) : ℝ) else 0) /
            Real.log ((M + 1 : ℕ) : ℝ)) := by
        ring
      rw [e, hcancel]
      linarith
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hL : 0 < Real.log N := Real.log_pos (by linarith)
  have hA := sum_log_div_le N (by omega)
  have hk := key N hN
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have h5 : (∑ p ∈ Nat.primesLE N, Real.log p / p) / Real.log N ≤ 1 + Real.log 4 / Real.log N := by
    rw [div_le_iff₀ hL]
    have : (1 + Real.log 4 / Real.log N) * Real.log N = Real.log N + Real.log 4 := by
      field_simp
    rw [this]
    exact hA
  have h6 : Real.log 4 * (1 / Real.log 2 - 1 / Real.log N) = 2 - Real.log 4 / Real.log N := by
    rw [h4]
    field_simp
  linarith

lemma range_bound (N : ℕ) (hN : 2 ≤ N) :
    ∑ p ∈ (Finset.range (N+1)).filter Nat.Prime, (1 : ℝ) / p ≤
      Real.log (Real.log N) + (3 - Real.log (Real.log 2)) :=
  sum_inv_primes_le N hN

end E726MertensUpper

open Filter Asymptotics Finset

private lemma e726_log_cutoff_bound :
    (fun k : ℕ => Real.log (((k+3)^4 : ℕ) : ℝ)) =O[atTop]
      fun k : ℕ => Real.log (k : ℝ) := by
  refine isBigO_iff.mpr ⟨8, ?_⟩
  filter_upwards [eventually_ge_atTop 3] with k hk
  have hx : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hle : (k : ℝ)+3 ≤ (k:ℝ)^2 := by nlinarith
  have hlog := Real.log_le_log (show 0 < (k:ℝ)+3 by positivity) hle
  rw [Real.log_pow] at hlog
  have hlx : 0 ≤ Real.log ((k:ℝ)+3) := Real.log_nonneg (by linarith)
  push_cast
  rw [Real.log_pow, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg (by linarith))]
  norm_num at *
  linarith

private lemma e726_small_mass {C : ℝ}
    (upper : ∀ N : ℕ, 2 ≤ N → ∑ p ∈ (range (N+1)).filter Nat.Prime, (1:ℝ)/p ≤
        Real.log (Real.log (N:ℝ)) + C) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop,
      (∑ p ∈ (range ((k+3)^4+1)).filter Nat.Prime, (1:ℝ)/p) + 1 ≤
        ε * Real.log (k:ℝ) := by
  have ht : Tendsto (fun k : ℕ => (k+3)^4) atTop atTop :=
    (tendsto_add_atTop_nat 3).atTop_pow (by decide)
  have hl := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp ht)
  have hsmall : (fun k : ℕ => Real.log (Real.log (((k+3)^4 : ℕ) : ℝ))) =o[atTop]
      fun k : ℕ => Real.log (k:ℝ) :=
    (Real.isLittleO_log_id_atTop.comp_tendsto hl).trans_isBigO e726_log_cutoff_bound
  have hconst : (fun _ : ℕ => C+1) =o[atTop] fun k : ℕ => Real.log (k:ℝ) :=
    Real.isLittleO_const_log_atTop.comp_tendsto tendsto_natCast_atTop_atTop
  filter_upwards [(hsmall.add hconst).bound hε, eventually_ge_atTop 2,
    ht.eventually_ge_atTop 2] with k hk hk₂ hN
  change ‖Real.log (Real.log (((k+3)^4 : ℕ) : ℝ)) + (C+1)‖ ≤ ε * ‖Real.log (k:ℝ)‖ at hk
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (Real.log_nonneg (by exact_mod_cast (show 1 ≤ k by omega)))] at hk
  have h := (le_abs_self _).trans hk
  linarith [upper ((k+3)^4) hN]

/-- The reciprocal-prime sum changes by o(log k) uniformly over intervals of length
at most (k+1)^2 below 2^(k+1). -/
theorem Erdos726Checkpoint.short_interval_stability :
    let S := fun t : ℕ =>
      ∑ p ∈ (Finset.range (t+1)).filter (fun p : ℕ =>
        p.Prime ∧ (p:ℝ)/2 < ((t%p:ℕ):ℝ)), (1:ℝ)/p
    ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ k : ℕ, K ≤ k → ∀ n h : ℕ,
      n+h < 2^(k+1) → h ≤ (k+1)^2 → |S (n+h) - S n| ≤ ε * Real.log (k:ℝ) := by
  intro S ε hε
  obtain ⟨K,hK⟩ := Filter.eventually_atTop.1 (e726_small_mass E726MertensUpper.range_bound ε hε)
  refine ⟨K, ?_⟩
  intro k hk n h hhi hh
  let B := (k+3)^4
  let M := ∏ i ∈ Finset.range h, (n+i+1)*(2*(n+i)+1)
  let D := 2*h*((n+h+1).log2+2)
  have lk : (n+h+1).log2 ≤ k+1 := by
    apply Nat.le_of_lt_succ
    apply (Nat.log2_lt (Nat.succ_ne_zero (n+h))).2
    rw [pow_succ _ (k+1)]
    omega
  have hD : D ≤ B := by
    calc
      D ≤ 2*(k+1)^2*(k+3) := Nat.mul_le_mul (Nat.mul_le_mul_left 2 hh) (by omega)
      _ ≤ B := by dsimp [B]; ring_nf; omega
  have mpos : 0 < M := Finset.prod_pos fun i _ => by positivity
  have bpos : 0 < B := by dsimp [B]; positivity
  have large := e726_large_prime_mass mpos (e726_product_le n h) bpos
  have ratio : (D:ℝ)/B ≤ 1 := by
    apply (div_le_one (by exact_mod_cast bpos : 0 < (B:ℝ))).mpr
    exact_mod_cast hD
  exact (e726_oscillation n h B).trans
    ((add_le_add_right (large.trans ratio) _).trans (hK k hk))

open Finset

private lemma e726_bands (x B T : ℕ) :
    let S : ℝ := ∑ p ∈ (range (x+1)).filter
      (fun p : ℕ => p.Prime ∧ (p:ℝ)/2 < ((x%p : ℕ):ℝ)), (1:ℝ)/p
    let small : ℝ := ∑ p ∈ (range (x+1)).filter
      (fun p : ℕ => p.Prime ∧ (p:ℝ)/2 < ((x%p : ℕ):ℝ) ∧ p≤B), (1:ℝ)/p
    let middle : ℝ := ∑ p ∈ (range (x+1)).filter
      (fun p : ℕ => p.Prime ∧ (p:ℝ)/2 < ((x%p : ℕ):ℝ) ∧ B<p ∧ p≤T), (1:ℝ)/p
    let high : ℝ := ∑ p ∈ (range (x+1)).filter
      (fun p : ℕ => p.Prime ∧ (p:ℝ)/2 < ((x%p : ℕ):ℝ) ∧ B<p ∧ T<p), (1:ℝ)/p
    let H : ℝ := ∑ p ∈ (range (B+1)).filter Nat.Prime, (1:ℝ)/p
    S = small + middle + high ∧ |S - middle - high| ≤ H := by
  intro S small middle high H
  have hsplit : S = small + middle + high := by
    dsimp only [S,small,middle,high]
    simp only [sum_filter, ← sum_add_distrib]
    apply sum_congr rfl
    intro p _
    by_cases hp : p.Prime <;> by_cases hres : (p:ℝ)/2 < ((x%p : ℕ):ℝ) <;>
      by_cases hB : p≤B <;> by_cases hT : p≤T <;> simp [hp,hres, ← not_le, hB,hT]
  refine ⟨hsplit, ?_⟩
  rw [show S - middle - high = small by linarith]
  dsimp only [small,H]
  rw [abs_of_nonneg (sum_nonneg fun p _ => by positivity)]
  apply sum_le_sum_of_subset_of_nonneg
  · intro p hp
    rcases mem_filter.mp hp with ⟨_, hprim, _, hB⟩
    exact mem_filter.mpr ⟨mem_range.mpr (by omega),hprim⟩
  · intro p _ _
    positivity

open Filter Asymptotics

private lemma e726_dyadic_log_gap {n k : ℕ} (hk : 1 ≤ k)
    (hlo : 2^k ≤ n) (hhi : n < 2^(k+1)) :
    |Real.log (k:ℝ) / 2 - Real.log (Real.log (n:ℝ)) / 2| ≤ 1 := by
  have hk' : 1 ≤ (k:ℝ) := by exact_mod_cast hk
  have hk₀ : 0 < (k:ℝ) := by linarith
  have hnr : (2:ℝ)^k ≤ n := by exact_mod_cast hlo
  have hnr' : (n:ℝ) ≤ (2:ℝ)^(k+1) := by exact_mod_cast hhi.le
  have ha := Real.log_le_log (by positivity : 0 < (2:ℝ)^k) hnr
  have hb := Real.log_le_log (lt_of_lt_of_le (by positivity) hnr) hnr'
  rw [Real.log_pow] at ha hb
  push_cast at hb
  have l₂ : (1:ℝ)/2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have u₂ : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  have ha' : (k:ℝ)/2 ≤ Real.log n := by nlinarith [mul_le_mul_of_nonneg_left l₂ hk₀.le]
  have hb' : Real.log n ≤ (k:ℝ)*2 := by nlinarith [mul_le_mul_of_nonneg_left u₂ (by linarith : 0 ≤ (k:ℝ)+1)]
  have hl := Real.log_le_log (by positivity : 0 < (k:ℝ)/2) ha'
  have hu := Real.log_le_log (lt_of_lt_of_le (by positivity) ha') hb'
  rw [Real.log_div hk₀.ne' (by norm_num)] at hl
  rw [Real.log_mul hk₀.ne' (by norm_num)] at hu
  exact abs_le.mpr ⟨by linarith, by linarith⟩

private lemma e726_dyadic_asymptotic (f : ℕ → ℝ)
    (hf : ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ k : ℕ, K ≤ k → ∀ n : ℕ,
      2^k ≤ n → n < 2^(k+1) → |f n - Real.log (k:ℝ)/2| ≤ ε*Real.log (k:ℝ)) :
    f ~[atTop] (fun n : ℕ => Real.log (Real.log (n:ℝ))/2) := by
  let g (n : ℕ) := Real.log (n.log2:ℝ)/2
  have hg : f ~[atTop] g := by
    apply isLittleO_iff.mpr
    intro ε he
    obtain ⟨K,hK⟩ := hf (ε/2) (by linarith)
    filter_upwards [eventually_ge_atTop (2^(max K 1) : ℕ)] with n hn
    have hpos : n ≠ 0 := ne_of_gt (lt_of_lt_of_le (by positivity) hn)
    have hlog := (Nat.le_log2 hpos).2 hn
    have hkn : 1 ≤ (n.log2:ℝ) := by exact_mod_cast (show 1 ≤ n.log2 by omega)
    have he' := hK n.log2 (by omega) n (Nat.log2_self_le hpos) Nat.lt_log2_self
    change |f n - Real.log (n.log2:ℝ)/2| ≤ ε*|Real.log (n.log2:ℝ)/2|
    rw [abs_of_nonneg (show 0 ≤ Real.log (n.log2:ℝ)/2 by linarith [Real.log_nonneg hkn])]
    linarith
  apply hg.trans
  apply isLittleO_iff.mpr
  intro ε he
  have ht : Tendsto (fun n : ℕ => Real.log (Real.log (n:ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [eventually_ge_atTop (2:ℕ), ht.eventually_ge_atTop (2/ε)] with n hn hε
  have hn₀ : n ≠ 0 := by omega
  have hk : 1 ≤ n.log2 := (Nat.le_log2 hn₀).2 (by simpa using hn)
  have hgap := e726_dyadic_log_gap hk (Nat.log2_self_le hn₀) Nat.lt_log2_self
  change 2/ε ≤ Real.log (Real.log (n:ℝ)) at hε
  have hmul := (div_le_iff₀ he).mp hε
  have hnonneg : 0 ≤ Real.log (Real.log (n:ℝ)) := (by positivity : 0 ≤ 2/ε).trans hε
  change |Real.log (n.log2:ℝ)/2 - Real.log (Real.log (n:ℝ))/2| ≤ ε*|Real.log (Real.log (n:ℝ))/2|
  rw [abs_of_nonneg (show 0 ≤ Real.log (Real.log (n:ℝ))/2 by linarith)]
  linarith

namespace OMA.R_Erdos726_erdos_726_R1

/-- Uniform middle-prime estimate at the checkpoints. -/
def H1 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ k : ℕ, K ≤ k → ∀ j : ℕ,
    let x := 2^k + j*(k+1)^2
    let B := (k+3)^4
    let T := 2^(k.sqrt.sqrt^3)
    x < 2^(k+1) →
      |(∑ p ∈ (Finset.range (x+1)).filter (fun p : ℕ => p.Prime ∧
        (p:ℝ)/2 < ((x%p:ℕ):ℝ) ∧ B<p ∧ p≤T), (1:ℝ)/p) -
          (3:ℝ)/8*Real.log (k:ℝ)| ≤ ε*Real.log (k:ℝ)

/-- Uniform large-prime estimate at the same checkpoints. -/
def H2 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ k : ℕ, K ≤ k → ∀ j : ℕ,
    let x := 2^k + j*(k+1)^2
    let B := (k+3)^4
    let T := 2^(k.sqrt.sqrt^3)
    x < 2^(k+1) →
      |(∑ p ∈ (Finset.range (x+1)).filter (fun p : ℕ => p.Prime ∧
        (p:ℝ)/2 < ((x%p:ℕ):ℝ) ∧ B<p ∧ T<p), (1:ℝ)/p) -
          (1:ℝ)/8*Real.log (k:ℝ)| ≤ ε*Real.log (k:ℝ)

theorem main : H1 → H2 → type_of% @Erdos726.erdos_726 := by
  intro middle high
  apply e726_dyadic_asymptotic
  intro ε hε
  have hδ : 0 < ε/4 := by positivity
  obtain ⟨K₁,hm⟩ := middle (ε/4) hδ
  obtain ⟨K₂,hl⟩ := high (ε/4) hδ
  obtain ⟨K₀,hb⟩ := Filter.eventually_atTop.mp (e726_small_mass E726MertensUpper.range_bound (ε/4) hδ)
  obtain ⟨K₃,ho⟩ := Erdos726Checkpoint.short_interval_stability (ε/4) hδ
  refine ⟨max (max K₀ K₃) (max K₁ K₂),?_⟩
  intro k hk n hn hn'
  obtain ⟨j,h,nh,hx,hh⟩ := e726_dyadic_grid hn hn'
  let x := 2^k+j*(k+1)^2
  let B := (k+3)^4
  let T := 2^(k.sqrt.sqrt^3)
  change n = x+h at nh
  have osc := ho k (by omega) x h (by rwa [← nh]) hh.le
  rw [← nh] at osc
  have mid := hm k (by omega) j hx
  have top := hl k (by omega) j hx
  have band := (e726_bands x B T).2
  have small := hb k (by omega)
  dsimp only at mid top osc band small ⊢
  dsimp only [x,B,T] at band
  dsimp only [x] at osc
  obtain ⟨o₁,o₂⟩ := abs_le.mp osc
  obtain ⟨b₁,b₂⟩ := abs_le.mp band
  obtain ⟨m₁,m₂⟩ := abs_le.mp mid
  obtain ⟨t₁,t₂⟩ := abs_le.mp top
  apply abs_le.mpr
  constructor <;> linarith only [o₁,o₂,b₁,b₂,m₁,m₂,t₁,t₂,small]

end OMA.R_Erdos726_erdos_726_R1
