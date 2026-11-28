import FormalConjectures.ErdosProblems.«270»
import Mathlib

-- Reduction Erdos270.erdos_270.variants.monotone.R1 of Erdős Problem 270 — monotone
-- Credit: @rickmanelius
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Erdős 270 for nondecreasing `f`: the Liouville case

The target says that for every nondecreasing `f` with `f(n) → ∞` the sum
`∑_{m ≥ 1} 1 / ((m + 1) ⋯ (m + f(m)))` is irrational (`Erdos270.series f`).

Proved below, with no hypothesis, `irrational_of_jumps`: the sum is irrational as soon as
`f(N + 1) > (N + f(N))^2 + 2` for infinitely many `N`. Write `G = N + f(N)`. Since `m + f(m)` is
nondecreasing, every denominator `(m + 1) ⋯ (m + f(m))` with `m ≤ N` divides `G!`
(`prod_dvd_factorial`), so `G!` times the partial sum through `m = N` is an integer. The tail
starts at `m = N + 1`; each of its terms is at most `(m + 1)^(-f(N + 1))` (`pow_le_prod`), so the
tail is positive and at most `2 (N + 2)^(2 - f(N + 1))`, using `∑ 1/(m + 1)^2 = π^2/6 < 2`. If
the sum were `a / D`, then `D G!` times the tail would be an integer strictly between `0` and
`1`, because `2 D G! < 2^(G^2 + 1)` (`key_nat`). This is the classical argument for the
irrationality of `e`, made to work by the large gaps.

What is left are the nondecreasing `f → ∞` with `f(n + 1) ≤ (n + f(n))^2 + 2` for all large `n`.
They are split by growth; both hypotheses are special cases of the target.

* `H1`: `f(n) ≤ n` for all large `n`. This contains `f(n) = n`, settled by Crmarić and Kovač,
  and every slower `f`, such as `f(n) = ⌊log n⌋`.
* `H2`: `f(n) > n` for infinitely many `n`, with no jump above `(n + f(n))^2 + 2` for large `n`.
-/

namespace OMA.R_Erdos270_erdos_270_variants_monotone_R1

open Erdos270 Filter Finset

/-- The slowly growing case: if `f` is nondecreasing, `f → ∞` and `f(n) ≤ n` for all large `n`,
the sum is irrational. -/
def H1 : Prop :=
  ∀ f : ℕ → ℕ, Monotone f → Tendsto f atTop atTop → (∀ᶠ n in atTop, f n ≤ n) →
    Irrational (Erdos270.series f)

/-- The fast case without large jumps: if `f` is nondecreasing, `f → ∞`, `f(n) > n` for
infinitely many `n` and `f(n + 1) ≤ (n + f(n))^2 + 2` for all large `n`, the sum is irrational. -/
def H2 : Prop :=
  ∀ f : ℕ → ℕ, Monotone f → Tendsto f atTop atTop → (∃ᶠ n in atTop, n < f n) →
    (∀ᶠ n in atTop, f (n + 1) ≤ (n + f n) ^ 2 + 2) → Irrational (Erdos270.series f)

lemma prod_Icc_one (b : ℕ) : ∏ i ∈ Finset.Icc 1 b, i = b.factorial := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [Finset.prod_Icc_succ_top (by omega), ih, Nat.factorial_succ]
    ring

/-- A denominator divides `G!` once its top factor is at most `G`. -/
lemma prod_dvd_factorial (n k G : ℕ) (h : n + 1 + k ≤ G) :
    (∏ i ∈ Finset.Icc (n + 2) (n + 1 + k), i) ∣ G.factorial := by
  have h1 : (∏ i ∈ Finset.Icc (n + 2) (n + 1 + k), i) ∣ ∏ i ∈ Finset.Icc 1 (n + 1 + k), i :=
    Finset.prod_dvd_prod_of_subset _ _ _ (by
      intro i hi
      simp only [Finset.mem_Icc] at hi ⊢
      omega)
  rw [prod_Icc_one] at h1
  exact h1.trans (Nat.factorial_dvd_factorial h)

/-- A denominator with `k` factors, all at least `n + 2`, is at least `(n + 2)^k`. -/
lemma pow_le_prod (n k : ℕ) : (n + 2) ^ k ≤ ∏ i ∈ Finset.Icc (n + 2) (n + 1 + k), i := by
  have hcard : (Finset.Icc (n + 2) (n + 1 + k)).card = k := by
    rw [Nat.card_Icc]
    omega
  calc (n + 2) ^ k = ∏ _i ∈ Finset.Icc (n + 2) (n + 1 + k), (n + 2) := by
        rw [Finset.prod_const, hcard]
    _ ≤ _ := Finset.prod_le_prod' (fun i hi => by
        simp only [Finset.mem_Icc] at hi
        omega)

/-- The arithmetic heart: `2 D G! < 2^(G^2 + 1)` when `1 ≤ G` and `D ≤ G`. -/
lemma key_nat {D G : ℕ} (hG : 1 ≤ G) (hD : D ≤ G) : 2 * D * G.factorial < 2 ^ (G ^ 2 + 1) := by
  have h1 : G ≤ 2 ^ (G - 1) := by
    have := Nat.lt_two_pow_self (n := G - 1)
    omega
  have h2 : G.factorial ≤ G ^ G := Nat.factorial_le_pow G
  have h3 : D * G ^ G ≤ G ^ (G + 1) := by
    rw [pow_succ]
    nlinarith [Nat.zero_le (G ^ G)]
  have h4 : G ^ (G + 1) ≤ (2 ^ (G - 1)) ^ (G + 1) := Nat.pow_le_pow_left h1 _
  have h5 : (2 ^ (G - 1)) ^ (G + 1) = 2 ^ ((G - 1) * (G + 1)) := by rw [← pow_mul]
  have h6 : (G - 1) * (G + 1) < G ^ 2 := by
    obtain ⟨g, rfl⟩ : ∃ g, G = g + 1 := ⟨G - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    nlinarith
  have h7 : 2 ^ ((G - 1) * (G + 1)) < 2 ^ (G ^ 2) := Nat.pow_lt_pow_right (by norm_num) h6
  have h8 : D * G.factorial ≤ D * G ^ G := Nat.mul_le_mul_left _ h2
  calc 2 * D * G.factorial = 2 * (D * G.factorial) := by ring
    _ < 2 * 2 ^ (G ^ 2) := by omega
    _ = 2 ^ (G ^ 2 + 1) := by ring

/-- The series `∑ 1/(n + 1)^2` converges to `π^2/6`. -/
lemma hasSum_inv_sq : HasSum (fun n : ℕ => (((n : ℝ) + 1) ^ 2)⁻¹) (Real.pi ^ 2 / 6) := by
  have h := (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, inv_zero, sub_zero, Nat.cast_add,
    Nat.cast_one, one_div] at h
  exact h

/-- Liouville-type irrationality: infinitely many jumps `f(N + 1) > (N + f(N))^2 + 2` make the
sum irrational. -/
lemma irrational_of_jumps (f : ℕ → ℕ) (hmono : Monotone f) (htend : Tendsto f atTop atTop)
    (hjump : ∃ᶠ N in atTop, (N + f N) ^ 2 + 2 < f (N + 1)) : Irrational (series f) := by
  set t : ℕ → ℝ := fun n => (∏ i ∈ Finset.Icc (n + 2) (n + 1 + f (n + 1)), (i : ℝ))⁻¹
    with ht
  have hseries : series f = ∑' n, t n := rfl
  have tcast : ∀ n, t n = (((∏ i ∈ Finset.Icc (n + 2) (n + 1 + f (n + 1)), i : ℕ) : ℝ))⁻¹ := by
    intro n
    simp only [ht]
    push_cast
    rfl
  have hPpos : ∀ n, 0 < ∏ i ∈ Finset.Icc (n + 2) (n + 1 + f (n + 1)), i := fun n =>
    Finset.prod_pos (fun i hi => by simp only [Finset.mem_Icc] at hi; omega)
  have tpos : ∀ n, 0 < t n := by
    intro n
    rw [tcast]
    exact inv_pos.2 (by exact_mod_cast hPpos n)
  have tle : ∀ n, t n ≤ (((n : ℝ) + 2) ^ f (n + 1))⁻¹ := by
    intro n
    rw [tcast]
    apply inv_anti₀ (by positivity)
    have := pow_le_prod n (f (n + 1))
    exact_mod_cast this
  have hsq := hasSum_inv_sq
  -- summability
  have hsum : Summable t := by
    obtain ⟨K, hK⟩ := (htend.eventually_ge_atTop 2).exists_forall_of_atTop
    rw [← summable_nat_add_iff K]
    refine Summable.of_nonneg_of_le (fun n => (tpos _).le) (fun n => ?_) hsq.summable
    refine (tle (n + K)).trans ?_
    apply inv_anti₀ (by positivity)
    have h2 : 2 ≤ f (n + K + 1) := hK _ (by omega)
    have hb : (1 : ℝ) ≤ ((n + K : ℕ) : ℝ) + 2 := by
      have : (0 : ℝ) ≤ ((n + K : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith
    calc ((n : ℝ) + 1) ^ 2 ≤ (((n + K : ℕ) : ℝ) + 2) ^ 2 := by
          apply pow_le_pow_left₀ (by positivity)
          push_cast
          have : (0 : ℝ) ≤ K := Nat.cast_nonneg _
          linarith
      _ ≤ (((n + K : ℕ) : ℝ) + 2) ^ f (n + K + 1) := pow_le_pow_right₀ hb h2
  -- suppose the sum is rational
  rintro ⟨r, hr⟩
  have hDpos : 0 < r.den := r.den_pos
  obtain ⟨N, hjN, hfN⟩ := (hjump.and_eventually (htend.eventually_ge_atTop (r.den + 4))).exists
  set G := N + f N with hG
  set F := f (N + 1) with hF
  have hsplit := hsum.sum_add_tsum_nat_add N
  set R := ∑' i, t (i + N) with hR
  -- the partial sum times `G!` is an integer
  obtain ⟨m, hm⟩ : ∃ m : ℕ, (G.factorial : ℝ) * ∑ i ∈ Finset.range N, t i = m := by
    refine ⟨∑ i ∈ Finset.range N,
      G.factorial / (∏ j ∈ Finset.Icc (i + 2) (i + 1 + f (i + 1)), j), ?_⟩
    rw [Finset.mul_sum, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    have hfi : f (i + 1) ≤ f N := hmono (by omega)
    have hdvd := prod_dvd_factorial i (f (i + 1)) G (by omega)
    rw [tcast, Nat.cast_div hdvd (by exact_mod_cast (hPpos i).ne')]
    rw [div_eq_mul_inv]
  -- the tail is positive
  have hRpos : 0 < R :=
    ((summable_nat_add_iff N).mpr hsum).tsum_pos (fun i => (tpos _).le) 0 (tpos _)
  -- the tail is small
  have hF2 : G ^ 2 + 3 ≤ F := by omega
  have hRle : R ≤ ((((N : ℝ) + 2) ^ (F - 2))⁻¹) * 2 := by
    have hb : ∀ i : ℕ, t (i + N) ≤ (((N : ℝ) + 2) ^ (F - 2))⁻¹ * (((i : ℝ) + 1) ^ 2)⁻¹ := by
      intro i
      refine (tle (i + N)).trans ?_
      rw [← mul_inv]
      apply inv_anti₀ (by positivity)
      have hfF : F ≤ f (i + N + 1) := hmono (by omega)
      have hb1 : (1 : ℝ) ≤ ((i + N : ℕ) : ℝ) + 2 := by
        have : (0 : ℝ) ≤ ((i + N : ℕ) : ℝ) := Nat.cast_nonneg _
        linarith
      calc ((N : ℝ) + 2) ^ (F - 2) * ((i : ℝ) + 1) ^ 2
          ≤ (((i + N : ℕ) : ℝ) + 2) ^ (F - 2) * (((i + N : ℕ) : ℝ) + 2) ^ 2 := by
            apply mul_le_mul _ _ (by positivity) (by positivity)
            · apply pow_le_pow_left₀ (by positivity)
              push_cast
              have : (0 : ℝ) ≤ i := Nat.cast_nonneg _
              linarith
            · apply pow_le_pow_left₀ (by positivity)
              push_cast
              have : (0 : ℝ) ≤ N := Nat.cast_nonneg _
              linarith
        _ = (((i + N : ℕ) : ℝ) + 2) ^ F := by
            rw [← pow_add]
            congr 1
            omega
        _ ≤ (((i + N : ℕ) : ℝ) + 2) ^ f (i + N + 1) := pow_le_pow_right₀ hb1 hfF
    calc R ≤ ∑' i : ℕ, (((N : ℝ) + 2) ^ (F - 2))⁻¹ * (((i : ℝ) + 1) ^ 2)⁻¹ :=
          Summable.tsum_le_tsum hb ((summable_nat_add_iff N).mpr hsum) (hsq.summable.mul_left _)
      _ = (((N : ℝ) + 2) ^ (F - 2))⁻¹ * ∑' i : ℕ, (((i : ℝ) + 1) ^ 2)⁻¹ := tsum_mul_left
      _ ≤ (((N : ℝ) + 2) ^ (F - 2))⁻¹ * 2 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [hsq.tsum_eq]
          have hpi := Real.pi_lt_d2
          have hpi0 := Real.pi_pos
          nlinarith
  -- the integer `den * G! * R` lies strictly between `0` and `1`
  have hkey : 2 * r.den * G.factorial < 2 ^ (F - 2) := by
    have h1 := key_nat (D := r.den) (G := G) (by omega) (by omega)
    have h2 : 2 ^ (G ^ 2 + 1) ≤ 2 ^ (F - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hkey' : (2 : ℝ) * r.den * G.factorial < ((N : ℝ) + 2) ^ (F - 2) := by
    have h1 : ((2 * r.den * G.factorial : ℕ) : ℝ) < ((2 ^ (F - 2) : ℕ) : ℝ) := by
      exact_mod_cast hkey
    have h2 : (2 : ℝ) ^ (F - 2) ≤ ((N : ℝ) + 2) ^ (F - 2) := by
      apply pow_le_pow_left₀ (by norm_num)
      have : (0 : ℝ) ≤ N := Nat.cast_nonneg _
      linarith
    push_cast at h1
    linarith
  have hrr : (r : ℝ) = r.num / r.den := Rat.cast_def r
  have hDR : (0 : ℝ) < r.den := by exact_mod_cast hDpos
  set z : ℤ := G.factorial * r.num - r.den * m with hz
  have hX : (z : ℝ) = (r.den : ℝ) * G.factorial * R := by
    have hRe : R = (r : ℝ) - ∑ i ∈ Finset.range N, t i := by
      rw [hr, hseries, ← hsplit]
      ring
    rw [hz, hRe]
    push_cast
    rw [mul_sub, hrr]
    field_simp
    linear_combination (r.den : ℝ) * hm
  have hz0 : (0 : ℝ) < z := by
    rw [hX]
    positivity
  have hz1 : (z : ℝ) < 1 := by
    rw [hX]
    have hpowpos : (0 : ℝ) < ((N : ℝ) + 2) ^ (F - 2) := by positivity
    calc (r.den : ℝ) * G.factorial * R ≤ (r.den : ℝ) * G.factorial *
          ((((N : ℝ) + 2) ^ (F - 2))⁻¹ * 2) := by
          apply mul_le_mul_of_nonneg_left hRle (by positivity)
      _ = (2 * r.den * G.factorial) / ((N : ℝ) + 2) ^ (F - 2) := by
          field_simp
      _ < 1 := by
          rw [div_lt_one hpowpos]
          exact hkey'
  have h0 : 0 < z := by exact_mod_cast hz0
  have h1 : z < 1 := by exact_mod_cast hz1
  omega

theorem main : H1 → H2 → type_of% @Erdos270.erdos_270.variants.monotone := by
  intro h1 h2 f hmono htend
  by_cases hj : ∃ᶠ N in atTop, (N + f N) ^ 2 + 2 < f (N + 1)
  · exact irrational_of_jumps f hmono htend hj
  · rw [Filter.not_frequently] at hj
    have hj' : ∀ᶠ N in atTop, f (N + 1) ≤ (N + f N) ^ 2 + 2 := hj.mono fun N h => not_lt.1 h
    by_cases hlin : ∀ᶠ n in atTop, f n ≤ n
    · exact h1 f hmono htend hlin
    · rw [Filter.not_eventually] at hlin
      exact h2 f hmono htend (hlin.mono fun n h => not_le.1 h) hj'

end OMA.R_Erdos270_erdos_270_variants_monotone_R1
