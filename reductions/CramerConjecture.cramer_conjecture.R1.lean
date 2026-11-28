import FormalConjectures.Wikipedia.CramerConjecture
import Mathlib

-- Reduction CramerConjecture.cramer_conjecture.R1 of Cramér's Conjecture
-- Credit: @hadijannat
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Reduction of Cramér's Conjecture via triangular-weight Chebyshev localization

The second difference of the integrated Chebyshev sum `F(n) = ∑ k < n, Λ(k) * (n - k)` localizes
the von Mangoldt mass to a short interval `[x, x + 2h)` of length `2h` at scale
`h = ⌈C * (log x)^2⌉₊`. Removing higher prime powers yields a prime in `(p_n, p_n + 2h]`
and hence `p_{n+1} - p_n = O((log p_n)^2)`. The finite tent estimate is adapted from
`CramerConjecture.cramer_conjecture.variants.baker_harman_pintz.R1` and `@senamakel`'s
conditional-RH proof in this repository.

* `H1` (open core): analytic short-interval lower bound on `F(x + 2h) - 2F(x + h) + F(x)`
  at scale `h = ⌈C * (log x)^2⌉₊` for some `C, c > 0`.
* `H2` (known step): higher prime-power sum in `[x, x + 2h)` is `o((log x)^2)` for every `C > 0`.
-/

namespace OMA.R_CramerConjecture_cramer_conjecture_R1

open Filter Real Asymptotics ArithmeticFunction Finset
open scoped Topology

/-- Analytic short-interval input, with triangular weights at Cramér scale. -/
def H1 : Prop :=
  let F (n : ℕ) := ∑ k ∈ range n, (Λ k : ℝ) * ((n : ℝ) - k)
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ᶠ x : ℕ in atTop,
    let h := ⌈C * (Real.log (x : ℝ)) ^ 2⌉₊
    c * (h : ℝ) ^ 2 ≤ F (x + 2 * h) - 2 * F (x + h) + F x

/-- Negligibility of higher prime powers on the `C * (log x)^2` gap scale. -/
def H2 : Prop :=
  ∀ C : ℝ, 0 < C →
    (fun x : ℕ =>
      ∑ d ∈ (Ico x (x + 2 * ⌈C * (Real.log (x : ℝ)) ^ 2⌉₊)).filter (fun d => ¬ d.Prime),
        (Λ d : ℝ))
      =o[atTop] fun x : ℕ => (Real.log (x : ℝ)) ^ 2

lemma truncate_sum {n N : ℕ} (hn : n ≤ N) :
    (fun m : ℕ => ∑ k ∈ range m, (Λ k : ℝ) * ((m : ℝ) - k)) n =
      ∑ k ∈ range N, (Λ k : ℝ) * max ((n : ℝ) - k) 0 := by
  rw [← sum_subset (range_subset_range.mpr hn)]
  · refine sum_congr rfl fun k hk => ?_
    have : (k : ℝ) < n := by exact_mod_cast mem_range.mp hk
    rw [max_eq_left (by linarith)]
  · intro k _ hk
    have : (n : ℝ) ≤ k := by exact_mod_cast not_lt.mp (by simpa using hk)
    rw [max_eq_right (by linarith), mul_zero]

lemma tent_bound (a h : ℕ) :
    (fun m : ℕ => ∑ k ∈ range m, (Λ k : ℝ) * ((m : ℝ) - k)) (a + 2 * h) -
        2 * (fun m : ℕ => ∑ k ∈ range m, (Λ k : ℝ) * ((m : ℝ) - k)) (a + h) +
        (fun m : ℕ => ∑ k ∈ range m, (Λ k : ℝ) * ((m : ℝ) - k)) a
      ≤ h * ∑ k ∈ Ico a (a + 2 * h), (Λ k : ℝ) := by
  set b := a + 2 * h
  rw [truncate_sum (N := b) le_rfl, truncate_sum (N := b) (by omega),
    truncate_sum (n := a) (N := b) (by omega), mul_sum, ← sum_sub_distrib,
    ← sum_add_distrib]
  rw [← sum_range_add_sum_Ico _ (show a ≤ b by omega)]
  have h0 : ∑ k ∈ range a, ((Λ k : ℝ) * max ((b : ℝ) - k) 0 - 2 * ((Λ k : ℝ) *
      max (((a + h : ℕ) : ℝ) - k) 0) + (Λ k : ℝ) * max ((a : ℝ) - k) 0) = 0 := by
    refine sum_eq_zero fun k hk => ?_
    have hk' : (k : ℝ) < a := by exact_mod_cast mem_range.mp hk
    have hb : (b : ℝ) = a + 2 * h := by simp [b]
    push_cast
    have hh : (0 : ℝ) ≤ h := h.cast_nonneg
    rw [max_eq_left (by rw [hb]; linarith), max_eq_left (by linarith),
      max_eq_left (by linarith), hb]
    ring
  rw [h0, zero_add, Finset.mul_sum]
  refine sum_le_sum fun k hk => ?_
  obtain ⟨hk1, hk2⟩ := mem_Ico.mp hk
  have hΛ : (0 : ℝ) ≤ Λ k := vonMangoldt_nonneg
  have hak : (a : ℝ) ≤ k := by exact_mod_cast hk1
  have hkb : (k : ℝ) < a + 2 * h := by exact_mod_cast hk2
  have hb : (b : ℝ) = a + 2 * h := by simp [b]
  rw [max_eq_right (show (a : ℝ) - k ≤ 0 by linarith), hb]
  push_cast
  have key : max ((a : ℝ) + 2 * h - k) 0 - 2 * max ((a : ℝ) + h - k) 0 ≤ h := by
    rcases le_total ((a : ℝ) + h) k with h1 | h1
    · rw [max_eq_right (show (a : ℝ) + h - k ≤ 0 by linarith),
        max_eq_left (show (0 : ℝ) ≤ a + 2 * h - k by linarith)]; linarith
    · rw [max_eq_left (show (0 : ℝ) ≤ a + h - k by linarith),
        max_eq_left (show (0 : ℝ) ≤ a + 2 * h - k by linarith)]; linarith
  nlinarith

theorem main : H1 → H2 → type_of% @CramerConjecture.cramer_conjecture := by
  rintro ⟨C, c, hC, hc, hcF⟩ hpowers
  let h (x : ℕ) := ⌈C * (Real.log (x : ℝ)) ^ 2⌉₊
  have interval : ∀ᶠ x : ℕ in atTop, ∃ p ∈ Ico x (x + 2 * h x), Nat.Prime p := by
    filter_upwards [hcF, (hpowers C hC).bound (show 0 < c * C / 2 by positivity),
      eventually_ge_atTop (2 : ℕ)] with x hx hpow hx2
    have hlog_pos : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < x by omega))
    have hlog_sq : 0 < (Real.log (x : ℝ)) ^ 2 := sq_pos_of_pos hlog_pos
    have hh : C * (Real.log (x : ℝ)) ^ 2 ≤ (h x : ℝ) := Nat.le_ceil _
    have hp : (0 : ℝ) < h x := by positivity
    have ht := tent_bound x (h x)
    have hbig : c * (h x : ℝ) ^ 2 ≤ (h x : ℝ) * ∑ k ∈ Ico x (x + 2 * h x), (Λ k : ℝ) :=
      hx.trans ht
    by_contra! absent
    have eqn : (Ico x (x + 2 * h x)).filter (fun k => ¬ k.Prime) = Ico x (x + 2 * h x) :=
      filter_eq_self.mpr absent
    change ‖∑ k ∈ (Ico x (x + 2 * h x)).filter (fun k => ¬ k.Prime), (Λ k : ℝ)‖ ≤
      (c * C / 2) * ‖(Real.log (x : ℝ)) ^ 2‖ at hpow
    rw [eqn, Real.norm_of_nonneg (sum_nonneg fun _ _ => vonMangoldt_nonneg),
      Real.norm_of_nonneg hlog_sq.le] at hpow
    have hb : c * (h x : ℝ) ≤ ∑ k ∈ Ico x (x + 2 * h x), (Λ k : ℝ) := by
      apply le_of_mul_le_mul_left _ hp
      nlinarith only [hbig]
    have hcC : c * C * (Real.log (x : ℝ)) ^ 2 ≤ c * (h x : ℝ) := by nlinarith
    nlinarith [mul_pos (mul_pos hc hC) hlog_sq]
  let p := Nat.nth Nat.Prime
  have mono : StrictMono p := Nat.nth_strictMono Nat.infinite_setOfPred_prime
  have ind : Tendsto (fun n => p n + 1) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_succ (p n)) mono.tendsto_atTop
  refine isBigO_iff.mpr ⟨3 + 8 * C, ?_⟩
  filter_upwards [ind.eventually interval, eventually_ge_atTop (1 : ℕ)] with n hn hn1
  obtain ⟨q, hq, hqp⟩ := hn
  have bounds := mem_Ico.mp hq
  have hnq : p (n + 1) ≤ q := by
    by_contra! hlt
    have : q ≤ p n := Nat.le_nth_of_lt_nth_succ hlt hqp
    omega
  have hp3 : 3 ≤ p n := by
    simpa only [p, Nat.nth_prime_one_eq_three] using mono.monotone hn1
  have hlog_gt1 : 1 < Real.log (p n : ℝ) :=
    (Real.lt_log_iff_exp_lt (by exact_mod_cast (show 0 < p n by omega))).mpr
      (by linarith [Real.exp_one_lt_d9, show (3 : ℝ) ≤ p n by exact_mod_cast hp3])
  have hlog_sq1 : 1 ≤ (Real.log (p n : ℝ)) ^ 2 := by nlinarith
  have hsq : ((p n + 1 : ℕ) : ℝ) ≤ (p n : ℝ) ^ 2 := by
    push_cast
    nlinarith [show (3 : ℝ) ≤ p n by exact_mod_cast hp3]
  have hlog_succ : Real.log ((p n + 1 : ℕ) : ℝ) ≤ 2 * Real.log (p n : ℝ) := by
    have h1 := Real.log_le_log (by positivity) hsq
    rwa [Real.log_pow, Nat.cast_ofNat] at h1
  have hlog_succ_nonneg : 0 ≤ Real.log ((p n + 1 : ℕ) : ℝ) :=
    Real.log_nonneg (by push_cast; linarith [show (3 : ℝ) ≤ p n by exact_mod_cast hp3])
  have hlog_succ_sq :
      (Real.log ((p n + 1 : ℕ) : ℝ)) ^ 2 ≤ 4 * (Real.log (p n : ℝ)) ^ 2 := by
    nlinarith
  have ch : (h (p n + 1) : ℝ) < C * (Real.log ((p n + 1 : ℕ) : ℝ)) ^ 2 + 1 := by
    simpa only [h] using Nat.ceil_lt_add_one (by positivity : 0 ≤ C * (Real.log ((p n + 1 : ℕ) : ℝ)) ^ 2)
  have gp : primeGap n ≤ 2 * h (p n + 1) := by
    change p (n + 1) - p n ≤ 2 * h (p n + 1)
    omega
  have gr : (primeGap n : ℝ) ≤ 2 * (h (p n + 1) : ℝ) := by exact_mod_cast gp
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (sq_nonneg _)]
  nlinarith

end OMA.R_CramerConjecture_cramer_conjecture_R1
