import OMAStatements.S_erdos_1054

/-!
# Disproof of `OMA.S_erdos_1054.main`

We disprove the first conjunct of `OMA.S_erdos_1054.main`:
it is false that for every `ε > 0`, the set `{n ∈ [1, N] : f(n) ≤ ε n}` has asymptotic density `1`.

## Proof outline
1. **Elementary harmonic & telescoping bounds** (`sum_inv_sq_le_two`, `double_sum_max_lcm_le`,
   `harmonic_lower_bound`, `harmonic_upper_bound`, `cauchy_schwarz_finset`).
2. **Tao's divisor-prefix second-moment bound (`tao_upper_bound`)**:
   For any `δ > 0` and `N ≥ 1`, the number of representable integers `n ∈ [N/20, N]` with
   `f(n) ≤ δ n` is at most `6400 δ³ N`.
3. **Representability of `p + 2^(r+1) - 1` (`representable_prime_add_pow_two`)**:
   Whenever `p` is prime and `2^r < p`, the `r + 2` smallest divisors of `2^r * p` are
   `1, 2, …, 2^r, p`, summing to `p + (2^(r+1) - 1)`.
4. **Chebyshev & weak Mertens bounds**:
   Using Mathlib's `primorial_le_four_pow` and `Nat.four_pow_lt_mul_centralBinom`, we establish
   `pi_upper`, `pi_lower`, `primes_in_band`, `sum_log_div_prime_le`, and `sum_inv_prime_le`.
5. **Selberg's upper-bound sieve (`selberg_shifted_primes`)**:
   Self-contained proof that for all even `h > 0` and large `x`,
   `#{p ≤ x : p and p + h prime} ≤ 200 * (x / (log x)^2) * (h / φ(h))^2`.
6. **Romanoff's theorem (`romanoff_lower_density`)**:
   Using `ord2(d) = orderOf (2 : ZMod d)` and dyadic grouping of odd squarefree `d`, we prove
   `∑_{m=1}^K ((2^m - 1) / φ(2^m - 1))^2 ≤ C_R * K`, and by Cauchy–Schwarz conclude that a
   positive fraction `c₀ N` of integers `n ∈ [N/20, N]` are representable.
7. **Contradiction (`prove_disproof`)**:
   Choosing `δ = min (1 / 2) (c₀ / 12800)` yields at least `(c₀ / 2) N` integers in `[1, N]`
   with `f(n) > δ n` for all large `N`, so the density cannot tend to `1`.
-/

namespace OMA.P_erdos_1054

open Filter Finset BigOperators OMA.S_erdos_1054
open scoped Topology Classical

/-! ### Section 1: Elementary Inequalities & Telescoping Sums -/

private lemma sum_inv_sq_le_two_sub (M : ℕ) (hM : 1 ≤ M) :
    ∑ k ∈ Finset.Icc 1 M, (1 : ℝ) / (k : ℝ) ^ 2 ≤ 2 - 1 / (M : ℝ) := by
  induction M, hM using Nat.le_induction with
  | base =>
    simp; norm_num
  | succ m hm ih =>
    have hIcc : Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hnot : m + 1 ∉ Finset.Icc 1 m := by simp
    rw [hIcc, Finset.sum_insert hnot]
    have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (by omega)
    have hm1_pos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
    have hstep : (1 : ℝ) / ((m + 1 : ℕ) : ℝ) ^ 2 ≤ 1 / (m : ℝ) - 1 / ((m + 1 : ℕ) : ℝ) := by
      rw [div_sub_div _ _ hm_pos.ne' hm1_pos.ne']
      rw [div_le_div_iff₀ (sq_pos_of_pos hm1_pos) (mul_pos hm_pos hm1_pos)]
      push_cast
      nlinarith
    linarith

private lemma sum_inv_sq_le_two (M : ℕ) :
    ∑ k ∈ Finset.Icc 1 M, (1 : ℝ) / (k : ℝ) ^ 2 ≤ 2 := by
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · simp
  · have h := sum_inv_sq_le_two_sub M hM
    have hpos : (0 : ℝ) ≤ 1 / (M : ℝ) := by positivity
    linarith

private lemma sum_inv_sq_from_le (u M : ℕ) (hu : 1 ≤ u) :
    ∑ v ∈ Finset.Icc u M, (1 : ℝ) / (v : ℝ) ^ 2 ≤ 2 / (u : ℝ) := by
  by_cases hle : u ≤ M
  · have hsub : ∀ n, u ≤ n →
        ∑ v ∈ Finset.Icc u n, (1 : ℝ) / (v : ℝ) ^ 2 ≤ 2 / (u : ℝ) - 1 / (n : ℝ) := by
      intro n hn
      induction n, hn using Nat.le_induction with
      | base =>
        simp only [Finset.Icc_self, Finset.sum_singleton]
        have hu1 : (1 : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu
        have hu_pos : (0 : ℝ) < (u : ℝ) := by linarith
        rw [show 2 / (u : ℝ) - 1 / (u : ℝ) = 1 / (u : ℝ) by ring]
        exact div_le_div_of_nonneg_left zero_le_one hu_pos (by nlinarith)
      | succ m hm ih =>
        have hIcc : Finset.Icc u (m + 1) = insert (m + 1) (Finset.Icc u m) := by
          ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
        have hnot : m + 1 ∉ Finset.Icc u m := by simp
        rw [hIcc, Finset.sum_insert hnot]
        have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (by omega)
        have hm1_pos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
        have hstep : (1 : ℝ) / ((m + 1 : ℕ) : ℝ) ^ 2 ≤ 1 / (m : ℝ) - 1 / ((m + 1 : ℕ) : ℝ) := by
          rw [div_sub_div _ _ hm_pos.ne' hm1_pos.ne']
          rw [div_le_div_iff₀ (sq_pos_of_pos hm1_pos) (mul_pos hm_pos hm1_pos)]
          push_cast; nlinarith
        linarith
    have h := hsub M hle
    have hpos : (0 : ℝ) ≤ 1 / (M : ℝ) := by positivity
    linarith
  · have hempty : Finset.Icc u M = ∅ := Finset.Icc_eq_empty hle
    rw [hempty, Finset.sum_empty]
    positivity

private lemma double_sum_max_lcm_le (M : ℕ) :
    ∑ a ∈ Finset.Icc 1 M, ∑ b ∈ Finset.Icc 1 M,
      (1 : ℝ) / ((max a b : ℕ) * (Nat.lcm a b : ℝ)) ≤ 16 := by
  have hsym : ∑ a ∈ Finset.Icc 1 M, ∑ b ∈ Finset.Icc 1 M,
      (1 : ℝ) / ((max a b : ℕ) * (Nat.lcm a b : ℝ)) ≤
      2 * ∑ a ∈ Finset.Icc 1 M, ∑ b ∈ Finset.Icc a M,
        (1 : ℝ) / ((b : ℝ) * (Nat.lcm a b : ℝ)) := by
    have h1 : ∑ a ∈ Finset.Icc 1 M, ∑ b ∈ Finset.Icc 1 M,
        (1 : ℝ) / ((max a b : ℕ) * (Nat.lcm a b : ℝ)) ≤
        ∑ a ∈ Finset.Icc 1 M, ∑ b ∈ Finset.Icc 1 M,
          ((if a ≤ b then (1 : ℝ) / ((b : ℝ) * (Nat.lcm a b : ℝ)) else 0) +
           (if b ≤ a then (1 : ℝ) / ((a : ℝ) * (Nat.lcm a b : ℝ)) else 0)) := by
      apply Finset.sum_le_sum; intro a _
      apply Finset.sum_le_sum; intro b _
      rcases le_total a b with hab | hba
      · rw [max_eq_right hab, if_pos hab]
        have hnn : (0 : ℝ) ≤ if b ≤ a then 1 / ((a : ℝ) * (Nat.lcm a b : ℝ)) else 0 := by
          split_ifs <;> positivity
        linarith
      · rw [max_eq_left hba, if_pos hba]
        have hnn : (0 : ℝ) ≤ if a ≤ b then 1 / ((b : ℝ) * (Nat.lcm a b : ℝ)) else 0 := by
          split_ifs <;> positivity
        linarith
    calc ∑ a ∈ Finset.Icc 1 M, ∑ b ∈ Finset.Icc 1 M,
          (1 : ℝ) / ((max a b : ℕ) * (Nat.lcm a b : ℝ))
      _ ≤ ∑ a ∈ Finset.Icc 1 M, ∑ b ∈ Finset.Icc 1 M,
            ((if a ≤ b then (1 : ℝ) / ((b : ℝ) * (Nat.lcm a b : ℝ)) else 0) +
             (if b ≤ a then (1 : ℝ) / ((a : ℝ) * (Nat.lcm a b : ℝ)) else 0)) := h1
      _ = (∑ a ∈ Finset.Icc 1 M, ∑ b ∈ Finset.Icc 1 M,
            if a ≤ b then (1 : ℝ) / ((b : ℝ) * (Nat.lcm a b : ℝ)) else 0) +
          (∑ a ∈ Finset.Icc 1 M, ∑ b ∈ Finset.Icc 1 M,
            if b ≤ a then (1 : ℝ) / ((a : ℝ) * (Nat.lcm a b : ℝ)) else 0) := by
          simp_rw [Finset.sum_add_distrib]
      _ = 2 * ∑ a ∈ Finset.Icc 1 M, ∑ b ∈ Finset.Icc a M,
            (1 : ℝ) / ((b : ℝ) * (Nat.lcm a b : ℝ)) := by
          have hA : ∑ a ∈ Finset.Icc 1 M, ∑ b ∈ Finset.Icc 1 M,
              (if a ≤ b then (1 : ℝ) / ((b : ℝ) * (Nat.lcm a b : ℝ)) else 0) =
              ∑ a ∈ Finset.Icc 1 M, ∑ b ∈ Finset.Icc a M,
                (1 : ℝ) / ((b : ℝ) * (Nat.lcm a b : ℝ)) := by
            apply Finset.sum_congr rfl; intro a ha
            rw [Finset.mem_Icc] at ha
            rw [← Finset.sum_filter]
            congr 1; ext b; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
          have hB : ∑ a ∈ Finset.Icc 1 M, ∑ b ∈ Finset.Icc 1 M,
              (if b ≤ a then (1 : ℝ) / ((a : ℝ) * (Nat.lcm a b : ℝ)) else 0) =
              ∑ b ∈ Finset.Icc 1 M, ∑ a ∈ Finset.Icc b M,
                (1 : ℝ) / ((a : ℝ) * (Nat.lcm b a : ℝ)) := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl; intro b hb
            rw [Finset.mem_Icc] at hb
            rw [← Finset.sum_filter]
            apply Finset.sum_congr
            · ext a; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
            · intro a _; rw [Nat.lcm_comm]
          rw [hA, hB]; ring
  let S := (Finset.Icc 1 M ×ˢ Finset.Icc 1 M).filter (fun p => p.1 ≤ p.2)
  let T := ((Finset.Icc 1 M ×ˢ Finset.Icc 1 M) ×ˢ Finset.Icc 1 M).filter
      (fun q => q.1.2 ≤ q.2)
  have hS_eq : ∑ a ∈ Finset.Icc 1 M, ∑ b ∈ Finset.Icc a M,
      (1 : ℝ) / ((b : ℝ) * (Nat.lcm a b : ℝ)) =
      ∑ p ∈ S, (1 : ℝ) / ((p.2 : ℝ) * (Nat.lcm p.1 p.2 : ℝ)) := by
    rw [Finset.sum_filter, Finset.sum_product]
    apply Finset.sum_congr rfl; intro a ha
    rw [Finset.mem_Icc] at ha
    rw [← Finset.sum_filter]
    congr 1; ext b; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
  let φ : ℕ × ℕ → (ℕ × ℕ) × ℕ := fun p =>
    ((Nat.gcd p.1 p.2, p.1 / Nat.gcd p.1 p.2), p.2 / Nat.gcd p.1 p.2)
  have hφ_mem : ∀ p ∈ S, φ p ∈ T := by
    intro p hp
    simp only [S, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp
    rcases hp with ⟨⟨⟨ha1, haM⟩, ⟨hb1, hbM⟩⟩, hab⟩
    have hg_pos : 0 < Nat.gcd p.1 p.2 := Nat.gcd_pos_of_pos_left p.2 (by omega)
    have hg_le : Nat.gcd p.1 p.2 ≤ M := le_trans (Nat.gcd_le_left p.2 (by omega)) haM
    have hu1 : 1 ≤ p.1 / Nat.gcd p.1 p.2 := Nat.div_pos (Nat.gcd_le_left p.2 (by omega)) hg_pos
    have huM : p.1 / Nat.gcd p.1 p.2 ≤ M := le_trans (Nat.div_le_self _ _) haM
    have hv1 : 1 ≤ p.2 / Nat.gcd p.1 p.2 := Nat.div_pos (Nat.gcd_le_right p.1 (by omega)) hg_pos
    have hvM : p.2 / Nat.gcd p.1 p.2 ≤ M := le_trans (Nat.div_le_self _ _) hbM
    have huv : p.1 / Nat.gcd p.1 p.2 ≤ p.2 / Nat.gcd p.1 p.2 := Nat.div_le_div_right hab
    simp only [T, φ, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
    exact ⟨⟨⟨⟨by omega, hg_le⟩, ⟨hu1, huM⟩⟩, ⟨hv1, hvM⟩⟩, huv⟩
  have hφ_inj : ∀ p1 ∈ S, ∀ p2 ∈ S, φ p1 = φ p2 → p1 = p2 := by
    intro p1 _ p2 _ heq
    simp only [φ, Prod.mk.injEq] at heq
    rcases heq with ⟨⟨hg, hu⟩, hv⟩
    have h1a : p1.1 = Nat.gcd p1.1 p1.2 * (p1.1 / Nat.gcd p1.1 p1.2) :=
      (Nat.mul_div_cancel' (Nat.gcd_dvd_left p1.1 p1.2)).symm
    have h2a : p2.1 = Nat.gcd p2.1 p2.2 * (p2.1 / Nat.gcd p2.1 p2.2) :=
      (Nat.mul_div_cancel' (Nat.gcd_dvd_left p2.1 p2.2)).symm
    have h1b : p1.2 = Nat.gcd p1.1 p1.2 * (p1.2 / Nat.gcd p1.1 p1.2) :=
      (Nat.mul_div_cancel' (Nat.gcd_dvd_right p1.1 p1.2)).symm
    have h2b : p2.2 = Nat.gcd p2.1 p2.2 * (p2.2 / Nat.gcd p2.1 p2.2) :=
      (Nat.mul_div_cancel' (Nat.gcd_dvd_right p2.1 p2.2)).symm
    ext
    · rw [h1a, h2a, hu, hg]
    · rw [h1b, h2b, hv, hg]
  have hφ_val : ∀ p ∈ S,
      (1 : ℝ) / ((p.2 : ℝ) * (Nat.lcm p.1 p.2 : ℝ)) =
      (1 : ℝ) / (((φ p).1.1 : ℝ) ^ 2 * ((φ p).1.2 : ℝ) * ((φ p).2 : ℝ) ^ 2) := by
    intro p hp
    simp only [S, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp
    set g := Nat.gcd p.1 p.2
    set u := p.1 / g
    set v := p.2 / g
    have hg_pos : 0 < g := Nat.gcd_pos_of_pos_left p.2 (by omega)
    have ha : p.1 = g * u := (Nat.mul_div_cancel' (Nat.gcd_dvd_left p.1 p.2)).symm
    have hb : p.2 = g * v := (Nat.mul_div_cancel' (Nat.gcd_dvd_right p.1 p.2)).symm
    have hlcm : Nat.lcm p.1 p.2 = g * u * v := by
      have hmul := Nat.gcd_mul_lcm p.1 p.2
      have h1 : g * Nat.lcm p.1 p.2 = g * (g * u * v) := by
        calc g * Nat.lcm p.1 p.2 = p.1 * p.2 := hmul
          _ = (g * u) * (g * v) := by rw [← ha, ← hb]
          _ = g * (g * u * v) := by ring
      exact Nat.eq_of_mul_eq_mul_left hg_pos h1
    change (1 : ℝ) / ((p.2 : ℝ) * (Nat.lcm p.1 p.2 : ℝ)) =
      (1 : ℝ) / ((g : ℝ) ^ 2 * (u : ℝ) * (v : ℝ) ^ 2)
    rw [hlcm, hb]; push_cast; ring
  have hT_le : ∑ p ∈ S, (1 : ℝ) / ((p.2 : ℝ) * (Nat.lcm p.1 p.2 : ℝ)) ≤
      ∑ q ∈ T, (1 : ℝ) / ((q.1.1 : ℝ) ^ 2 * (q.1.2 : ℝ) * (q.2 : ℝ) ^ 2) := by
    let F : (ℕ × ℕ) × ℕ → ℝ := fun q => (1 : ℝ) / ((q.1.1 : ℝ) ^ 2 * (q.1.2 : ℝ) * (q.2 : ℝ) ^ 2)
    calc ∑ p ∈ S, (1 : ℝ) / ((p.2 : ℝ) * (Nat.lcm p.1 p.2 : ℝ))
      _ = ∑ p ∈ S, F (φ p) := Finset.sum_congr rfl hφ_val
      _ = ∑ q ∈ S.image φ, F q := (Finset.sum_image (f := F) hφ_inj).symm
      _ ≤ ∑ q ∈ T, F q := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro q hq
            rcases Finset.mem_image.mp hq with ⟨p, hp, rfl⟩
            exact hφ_mem p hp
          · intro q _ _; dsimp only [F]; positivity
  have hT_bound : ∑ q ∈ T, (1 : ℝ) / ((q.1.1 : ℝ) ^ 2 * (q.1.2 : ℝ) * (q.2 : ℝ) ^ 2) ≤ 8 := by
    have hT_eq : ∑ q ∈ T, (1 : ℝ) / ((q.1.1 : ℝ) ^ 2 * (q.1.2 : ℝ) * (q.2 : ℝ) ^ 2) =
        (∑ g ∈ Finset.Icc 1 M, (1 : ℝ) / (g : ℝ) ^ 2) *
        (∑ u ∈ Finset.Icc 1 M, (1 : ℝ) / (u : ℝ) *
          ∑ v ∈ Finset.Icc u M, (1 : ℝ) / (v : ℝ) ^ 2) := by
      simp only [T, Finset.sum_filter, Finset.sum_product]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl; intro g _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro u hu
      rw [Finset.mem_Icc] at hu
      rw [← Finset.sum_filter]
      have hfilt : (Finset.Icc 1 M).filter (fun v => u ≤ v) = Finset.Icc u M := by
        ext v; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
      rw [hfilt, Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro v _; ring
    rw [hT_eq]
    have hg2 : ∑ g ∈ Finset.Icc 1 M, (1 : ℝ) / (g : ℝ) ^ 2 ≤ 2 := sum_inv_sq_le_two M
    have huv4 : ∑ u ∈ Finset.Icc 1 M, (1 : ℝ) / (u : ℝ) *
        ∑ v ∈ Finset.Icc u M, (1 : ℝ) / (v : ℝ) ^ 2 ≤ 4 := by
      calc ∑ u ∈ Finset.Icc 1 M, (1 : ℝ) / (u : ℝ) *
            ∑ v ∈ Finset.Icc u M, (1 : ℝ) / (v : ℝ) ^ 2
        _ ≤ ∑ u ∈ Finset.Icc 1 M, (1 : ℝ) / (u : ℝ) * (2 / (u : ℝ)) := by
            apply Finset.sum_le_sum; intro u hu
            rw [Finset.mem_Icc] at hu
            exact mul_le_mul_of_nonneg_left (sum_inv_sq_from_le u M hu.1) (by positivity)
        _ = 2 * ∑ u ∈ Finset.Icc 1 M, (1 : ℝ) / (u : ℝ) ^ 2 := by
            rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro u _; ring
        _ ≤ 2 * 2 := by linarith [sum_inv_sq_le_two M]
        _ = 4 := by norm_num
    have hnn1 : 0 ≤ ∑ g ∈ Finset.Icc 1 M, (1 : ℝ) / (g : ℝ) ^ 2 :=
      Finset.sum_nonneg (fun _ _ => by positivity)
    have hnn2 : 0 ≤ ∑ u ∈ Finset.Icc 1 M, (1 : ℝ) / (u : ℝ) *
        ∑ v ∈ Finset.Icc u M, (1 : ℝ) / (v : ℝ) ^ 2 :=
      Finset.sum_nonneg (fun _ _ => mul_nonneg (by positivity)
        (Finset.sum_nonneg (fun _ _ => by positivity)))
    nlinarith
  linarith [hsym, hS_eq, hT_le, hT_bound]

private lemma harmonic_lower_bound (Y : ℕ) (hY : 1 ≤ Y) :
    Real.log (Y : ℝ) ≤ ∑ k ∈ Finset.Icc 1 Y, (1 : ℝ) / (k : ℝ) := by
  have hstrong : Real.log ((Y + 1 : ℕ) : ℝ) ≤ ∑ k ∈ Finset.Icc 1 Y, (1 : ℝ) / (k : ℝ) := by
    induction Y, hY using Nat.le_induction with
    | base =>
      simp only [Finset.Icc_self, Finset.sum_singleton, Nat.cast_one, div_one]
      have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (2 : ℝ) by norm_num)
      norm_num at h ⊢; linarith
    | succ m hm ih =>
      have hIcc : Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      have hnot : m + 1 ∉ Finset.Icc 1 m := by simp
      rw [hIcc, Finset.sum_insert hnot]
      have hm1 : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
      have hm2 : (0 : ℝ) < ((m + 2 : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
      have hstep : Real.log ((m + 2 : ℕ) : ℝ) - Real.log ((m + 1 : ℕ) : ℝ) ≤
          1 / ((m + 1 : ℕ) : ℝ) := by
        rw [← Real.log_div hm2.ne' hm1.ne']
        have h := Real.log_le_sub_one_of_pos (div_pos hm2 hm1)
        have heq : ((m + 2 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ) - 1 = 1 / ((m + 1 : ℕ) : ℝ) := by
          field_simp; push_cast; ring
        linarith
      linarith
  have hle : Real.log (Y : ℝ) ≤ Real.log ((Y + 1 : ℕ) : ℝ) := by
    apply Real.log_le_log (Nat.cast_pos.mpr (by omega))
    exact_mod_cast Nat.le_succ Y
  linarith

private lemma harmonic_upper_bound (z : ℕ) (hz : 1 ≤ z) :
    ∑ k ∈ Finset.Icc 1 z, (1 : ℝ) / (k : ℝ) ≤ Real.log (z : ℝ) + 1 := by
  induction z, hz using Nat.le_induction with
  | base =>
    simp
  | succ m hm ih =>
    have hIcc : Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hnot : m + 1 ∉ Finset.Icc 1 m := by simp
    rw [hIcc, Finset.sum_insert hnot]
    have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (by omega)
    have hm1_pos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
    have hstep : 1 / ((m + 1 : ℕ) : ℝ) ≤ Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ) := by
      have h := Real.log_le_sub_one_of_pos (div_pos hm_pos hm1_pos)
      rw [Real.log_div hm_pos.ne' hm1_pos.ne'] at h
      have heq : (m : ℝ) / ((m + 1 : ℕ) : ℝ) - 1 = -(1 / ((m + 1 : ℕ) : ℝ)) := by
        field_simp; push_cast; ring
      linarith
    linarith

private lemma cauchy_schwarz_finset {α : Type*} (s : Finset α) (g : α → ℝ) :
    (∑ x ∈ s, g x) ^ 2 ≤ (s.card : ℝ) * ∑ x ∈ s, (g x) ^ 2 := by
  have h0 : (0 : ℝ) ≤ ∑ x ∈ s, ∑ y ∈ s, (g x - g y) ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hexp : ∑ x ∈ s, ∑ y ∈ s, (g x - g y) ^ 2 =
      2 * (s.card : ℝ) * ∑ x ∈ s, (g x) ^ 2 - 2 * (∑ x ∈ s, g x) ^ 2 := by
    have h1 : ∀ x, ∑ y ∈ s, (g x - g y) ^ 2 =
        (s.card : ℝ) * (g x) ^ 2 - 2 * g x * (∑ y ∈ s, g y) + ∑ y ∈ s, (g y) ^ 2 := by
      intro x
      calc ∑ y ∈ s, (g x - g y) ^ 2
        _ = ∑ y ∈ s, ((g x) ^ 2 - 2 * g x * g y + (g y) ^ 2) := by
            apply Finset.sum_congr rfl; intro y _; ring
        _ = (∑ _y ∈ s, (g x) ^ 2) - (∑ y ∈ s, 2 * g x * g y) + ∑ y ∈ s, (g y) ^ 2 := by
            rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
        _ = (s.card : ℝ) * (g x) ^ 2 - 2 * g x * (∑ y ∈ s, g y) + ∑ y ∈ s, (g y) ^ 2 := by
            rw [Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
    simp_rw [h1]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        Finset.sum_const, nsmul_eq_mul]
    have h2 : ∑ x ∈ s, 2 * g x * ∑ y ∈ s, g y = 2 * (∑ x ∈ s, g x) ^ 2 := by
      rw [← Finset.sum_mul, ← Finset.mul_sum]; ring
    rw [h2]; ring
  linarith

private lemma card_multiples_Icc_le (M L : ℕ) (hL : 1 ≤ L) :
    (((Finset.Icc 1 M).filter (fun m => L ∣ m)).card : ℝ) ≤ (M : ℝ) / (L : ℝ) := by
  have hle : ((Finset.Icc 1 M).filter (fun m => L ∣ m)).card ≤ M / L := by
    have hinj : Set.InjOn (fun m => m / L)
        (((Finset.Icc 1 M).filter (fun m => L ∣ m) : Finset ℕ) : Set ℕ) := by
      intro a ha b hb hab
      dsimp only at hab
      simp only [Finset.mem_coe, Finset.mem_filter] at ha hb
      calc a = L * (a / L) := (Nat.mul_div_cancel' ha.2).symm
        _ = L * (b / L) := by rw [hab]
        _ = b := Nat.mul_div_cancel' hb.2
    have hsub : ((Finset.Icc 1 M).filter (fun m => L ∣ m)).image (fun m => m / L) ⊆
        Finset.Icc 1 (M / L) := by
      intro k hk
      rcases Finset.mem_image.mp hk with ⟨m, hm, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_Icc] at hm
      rw [Finset.mem_Icc]
      exact ⟨Nat.div_pos (Nat.le_of_dvd (by omega) hm.2) (by omega), Nat.div_le_div_right hm.1.2⟩
    calc ((Finset.Icc 1 M).filter (fun m => L ∣ m)).card
      _ = (((Finset.Icc 1 M).filter (fun m => L ∣ m)).image (fun m => m / L)).card :=
          (Finset.card_image_of_injOn hinj).symm
      _ ≤ (Finset.Icc 1 (M / L)).card := Finset.card_le_card hsub
      _ = M / L := by simp
  have hcast : (((Finset.Icc 1 M).filter (fun m => L ∣ m)).card : ℝ) ≤ ((M / L : ℕ) : ℝ) := by
    exact_mod_cast hle
  have hdiv : ((M / L : ℕ) : ℝ) ≤ (M : ℝ) / (L : ℝ) := by
    rw [le_div_iff₀ (Nat.cast_pos.mpr (by omega))]
    exact_mod_cast Nat.div_mul_le_self M L
  linarith

private lemma eq_prod_primeFactors_pow {n : ℕ} (hn : n ≠ 0) :
    n = ∏ p ∈ n.primeFactors, p ^ (n.factorization p) := by
  have h := Nat.prod_factorization_pow_eq_self hn
  conv_lhs => rw [← h]
  change ∏ p ∈ n.factorization.support, p ^ (n.factorization p) = _
  rw [Nat.support_factorization]

private lemma rad_dvd_self {n : ℕ} (hn : n ≠ 0) :
    (∏ p ∈ n.primeFactors, p) ∣ n := by
  conv_rhs => rw [eq_prod_primeFactors_pow hn]
  apply Finset.prod_dvd_prod_of_dvd
  intro q hq
  have h1 : 1 ≤ n.factorization q :=
    Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp (Nat.support_factorization n ▸ hq))
  exact dvd_pow_self q (by omega)

private lemma rad_squarefree (n : ℕ) : Squarefree (∏ p ∈ n.primeFactors, p) := by
  rw [Nat.squarefree_iff_prime_squarefree]
  intro p hp hpp
  rcases (hp.prime.dvd_finsetProd_iff _).mp (dvd_trans (dvd_mul_left p p) hpp) with ⟨q, hq, hpq⟩
  have hpeq : p = q := (Nat.prime_dvd_prime_iff_eq hp (Nat.prime_of_mem_primeFactors hq)).mp hpq
  subst hpeq
  have hsplit : (∏ x ∈ n.primeFactors, x) = p * ∏ x ∈ n.primeFactors.erase p, x :=
    (Finset.mul_prod_erase n.primeFactors id hq).symm
  rw [hsplit] at hpp
  have hprest : p ∣ ∏ x ∈ n.primeFactors.erase p, x := (Nat.mul_dvd_mul_iff_left hp.pos).mp hpp
  rcases (hp.prime.dvd_finsetProd_iff _).mp hprest with ⟨q2, hq2, hpq2⟩
  have := (Nat.prime_dvd_prime_iff_eq hp
    (Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hq2))).mp hpq2
  exact (Finset.mem_erase.mp hq2).1 this.symm

private lemma rad_primeFactors_eq (n : ℕ) :
    (∏ q ∈ n.primeFactors, q).primeFactors = n.primeFactors := by
  ext p
  have hne : (∏ q ∈ n.primeFactors, q) ≠ 0 :=
    (Finset.prod_pos fun q hq => (Nat.prime_of_mem_primeFactors hq).pos).ne'
  rw [Nat.mem_primeFactors]
  constructor
  · rintro ⟨hp, hdvd, _⟩
    rcases (hp.prime.dvd_finsetProd_iff _).mp hdvd with ⟨q, hq, hpq⟩
    exact ((Nat.prime_dvd_prime_iff_eq hp (Nat.prime_of_mem_primeFactors hq)).mp hpq) ▸ hq
  · intro hp
    exact ⟨Nat.prime_of_mem_primeFactors hp, Finset.dvd_prod_of_mem _ hp, hne⟩

private lemma rad_divisors_eq {n : ℕ} (hn : n ≠ 0) :
    (∏ q ∈ n.primeFactors, q).divisors = n.divisors.filter Squarefree := by
  ext d
  have hne : (∏ q ∈ n.primeFactors, q) ≠ 0 :=
    (Finset.prod_pos fun q hq => (Nat.prime_of_mem_primeFactors hq).pos).ne'
  simp only [Nat.mem_divisors, Finset.mem_filter, hn, hne, ne_eq, not_false_eq_true, and_true]
  constructor
  · intro hd
    exact ⟨dvd_trans hd (rad_dvd_self hn), (rad_squarefree n).squarefree_of_dvd hd⟩
  · rintro ⟨hdn, hdsq⟩
    rw [← Nat.prod_primeFactors_of_squarefree hdsq]
    apply Finset.prod_dvd_prod_of_subset
    intro p hp
    exact Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hp,
      dvd_trans (Nat.dvd_of_mem_primeFactors hp) hdn, hn⟩

/-! ### Section 2: Tao's Upper Bound on Representable `n ∈ [N/20, N]` with `f(n) ≤ δ n` -/

/-- `n` has at least one `m` such that `n` is the sum of the `k` smallest divisors of `m`. -/
def Representable (n : ℕ) : Prop :=
  ∃ m : ℕ, IsSumOfSmallestDivisors n m

private lemma pairwise_lt_of_sort (s : Finset ℕ) : (s.sort (· ≤ ·)).Pairwise (· < ·) := by
  have hle := Finset.pairwise_sort s (· ≤ ·)
  have hnd := Finset.sort_nodup s (· ≤ ·)
  exact (List.pairwise_iff_getElem.mpr fun i j hi hj hij => by
    have h1 := List.pairwise_iff_getElem.mp hle i j hi hj hij
    have h2 := List.pairwise_iff_getElem.mp hnd i j hi hj hij
    omega)

private lemma exists_divisor_cutoff {n m : ℕ} (hn : 1 ≤ n) (hrep : IsSumOfSmallestDivisors n m) :
    1 ≤ m ∧ ∃ c ∈ m.divisors,
      (n : ℝ) = (m : ℝ) * ∑ a ∈ m.divisors.filter (fun a => c ≤ a), (1 : ℝ) / (a : ℝ) := by
  rcases hrep with ⟨k, hk, hsum⟩
  have hm0 : m ≠ 0 := by
    intro h0; subst h0
    simp only [Nat.divisors_zero, Finset.sort_empty, List.take_nil, List.sum_nil] at hsum
    omega
  refine ⟨Nat.pos_of_ne_zero hm0, ?_⟩
  set L := m.divisors.sort (· ≤ ·)
  have hL_lt : L.Pairwise (· < ·) := pairwise_lt_of_sort m.divisors
  have hL_mem : ∀ x, x ∈ L ↔ x ∈ m.divisors := fun x => Finset.mem_sort (· ≤ ·)
  have h1_mem : 1 ∈ L := (hL_mem 1).mpr (Nat.one_mem_divisors.mpr hm0)
  have hL_pos : 0 < L.length := List.length_pos_of_mem h1_mem
  set k' := min k L.length
  have hk'_pos : 1 ≤ k' := le_min hk hL_pos
  have hk'_le : k' ≤ L.length := min_le_right k L.length
  have htake_eq : L.take k = L.take k' := by
    by_cases hkl : k ≤ L.length
    · simp [k', min_eq_left hkl]
    · simp only [k', min_eq_right (le_of_not_ge hkl)]
      rw [List.take_of_length_le (le_of_not_ge hkl), List.take_length]
  rw [htake_eq] at hsum
  set d0 := L[k' - 1]'(by omega)
  have hd0_mem : d0 ∈ m.divisors := (hL_mem d0).mp (List.getElem_mem _)
  have htake_nd : (L.take k').Nodup := (Finset.sort_nodup m.divisors (· ≤ ·)).take
  have htoFinset : (L.take k').toFinset = m.divisors.filter (fun d => d ≤ d0) := by
    ext x
    rw [List.mem_toFinset, Finset.mem_filter]
    constructor
    · intro hx
      have hxL : x ∈ L := List.mem_of_mem_take hx
      refine ⟨(hL_mem x).mp hxL, ?_⟩
      rw [List.mem_iff_getElem] at hx
      rcases hx with ⟨i, hi, rfl⟩
      rw [List.length_take, min_eq_left hk'_le] at hi
      rw [List.getElem_take]
      by_cases hieq : i = k' - 1
      · subst hieq; exact le_rfl
      · exact le_of_lt (List.pairwise_iff_getElem.mp hL_lt i (k' - 1) (by omega) (by omega) (by omega))
    · rintro ⟨hxd, hxle⟩
      have hxL : x ∈ L := (hL_mem x).mpr hxd
      rw [List.mem_iff_getElem] at hxL
      rcases hxL with ⟨i, hi, rfl⟩
      have hik : i < k' := by
        by_contra hge
        have hlt := List.pairwise_iff_getElem.mp hL_lt (k' - 1) i (by omega) hi (by omega)
        change d0 < L[i] at hlt
        omega
      rw [List.mem_iff_getElem]
      exact ⟨i, by rw [List.length_take, min_eq_left hk'_le]; exact hik, by rw [List.getElem_take]⟩
  have hn_sum : n = ∑ d ∈ m.divisors.filter (fun d => d ≤ d0), d := by
    rw [hsum, ← htoFinset, List.sum_toFinset _ htake_nd]; simp only [List.map_id']
  set c := m / d0
  have hd0_dvd : d0 ∣ m := Nat.dvd_of_mem_divisors hd0_mem
  have hd0_pos : 0 < d0 := Nat.pos_of_mem_divisors hd0_mem
  have hc_mul : c * d0 = m := Nat.div_mul_cancel hd0_dvd
  have hc_mem : c ∈ m.divisors := Nat.mem_divisors.mpr ⟨⟨d0, hc_mul.symm⟩, hm0⟩
  refine ⟨c, hc_mem, ?_⟩
  have hcast : (n : ℝ) = ∑ d ∈ m.divisors.filter (fun d => d ≤ d0), (d : ℝ) := by
    rw [hn_sum]; push_cast; rfl
  rw [hcast, Finset.mul_sum]
  apply Finset.sum_bij (fun d _ => m / d)
  · intro d hd
    simp only [Finset.mem_filter] at hd ⊢
    have hdm := Nat.dvd_of_mem_divisors hd.1
    have hd_pos := Nat.pos_of_mem_divisors hd.1
    refine ⟨Nat.mem_divisors.mpr ⟨⟨d, (Nat.div_mul_cancel hdm).symm⟩, hm0⟩, ?_⟩
    have hmul : d * (m / d) = c * d0 := by rw [Nat.mul_div_cancel' hdm, hc_mul]
    nlinarith [hd.2, hd_pos]
  · intro d1 hd1 d2 hd2 heq
    simp only [Finset.mem_filter] at hd1 hd2
    have h1 := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd1.1)
    have h2 := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd2.1)
    have hq_pos : 0 < m / d1 :=
      Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) (Nat.dvd_of_mem_divisors hd1.1))
        (Nat.pos_of_mem_divisors hd1.1)
    have hmul : d1 * (m / d1) = d2 * (m / d1) := by rw [h1, heq, h2]
    exact Nat.eq_of_mul_eq_mul_right hq_pos hmul
  · intro a ha
    simp only [Finset.mem_filter] at ha
    have ham := Nat.dvd_of_mem_divisors ha.1
    have ha_pos := Nat.pos_of_mem_divisors ha.1
    refine ⟨m / a, ?_, ?_⟩
    · simp only [Finset.mem_filter]
      refine ⟨Nat.mem_divisors.mpr ⟨⟨a, (Nat.div_mul_cancel ham).symm⟩, hm0⟩, ?_⟩
      have hmul : (m / a) * a = d0 * c := by rw [Nat.div_mul_cancel ham, mul_comm, hc_mul]
      have hc_pos : 0 < c := Nat.pos_of_mem_divisors hc_mem
      nlinarith [ha.2]
    · have h1 : a * (m / a) = m := Nat.mul_div_cancel' ham
      have hpos : 0 < m / a :=
        Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) ham) ha_pos
      exact Nat.div_eq_of_eq_mul_left hpos h1.symm
  · intro d hd
    simp only [Finset.mem_filter] at hd
    have hdm := Nat.dvd_of_mem_divisors hd.1
    have hd_pos := Nat.pos_of_mem_divisors hd.1
    have hq_pos : (0 : ℝ) < ((m / d : ℕ) : ℝ) := by
      exact_mod_cast Nat.div_pos
        (Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) hdm) hd_pos
    have hmul : (d : ℝ) * ((m / d : ℕ) : ℝ) = (m : ℝ) := by
      exact_mod_cast Nat.mul_div_cancel' hdm
    rw [mul_one_div, eq_div_iff hq_pos.ne']
    exact hmul

private lemma tao_upper_bound (N : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    (((Finset.Icc 1 N).filter (fun n => N ≤ 20 * n ∧ Representable n ∧ (f n : ℝ) ≤ δ * n)).card : ℝ)
      ≤ 6400 * δ ^ 3 * (N : ℝ) := by
  set T := (Finset.Icc 1 N).filter (fun n => N ≤ 20 * n ∧ Representable n ∧ (f n : ℝ) ≤ δ * n)
  set M := Nat.floor (δ * (N : ℝ))
  let Sval : ℕ → ℕ → ℝ := fun m c =>
    ∑ a ∈ m.divisors.filter (fun a => c ≤ a), (1 : ℝ) / (a : ℝ)
  have hmem_wit : ∀ n ∈ T, 1 ≤ f n ∧ f n ≤ M ∧ ∃ c ∈ (f n).divisors,
      (n : ℝ) = (f n : ℝ) * Sval (f n) c := by
    intro n hn
    simp only [T, Finset.mem_filter, Finset.mem_Icc] at hn
    rcases hn with ⟨⟨hn1, hnN⟩, _, hrep, hfn⟩
    have hf_mem : IsSumOfSmallestDivisors n (f n) := Nat.sInf_mem hrep
    rcases exists_divisor_cutoff hn1 hf_mem with ⟨hf1, c, hc, heq⟩
    have hfM : f n ≤ M := by
      apply Nat.le_floor
      have hnle : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hnN
      nlinarith
    exact ⟨hf1, hfM, c, hc, heq⟩
  choose cWit hcWit_spec using fun n (hn : n ∈ T) => (hmem_wit n hn).2.2
  let ψ : ℕ → ℕ × ℕ := fun n => if h : n ∈ T then (f n, cWit n h) else (0, 0)
  let Pairs := (Finset.Icc 1 M ×ˢ Finset.Icc 1 M).filter (fun p => p.2 ∈ p.1.divisors)
  have hψ_mem : ∀ n ∈ T, ψ n ∈ Pairs := by
    intro n hn
    simp only [ψ, dif_pos hn, Pairs, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
    have h1 := (hmem_wit n hn).1
    have h2 := (hmem_wit n hn).2.1
    have hc := (hcWit_spec n hn).1
    have hc1 : 1 ≤ cWit n hn := Nat.pos_of_mem_divisors hc
    have hcM : cWit n hn ≤ M :=
      le_trans (Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_divisors hc)) h2
    exact ⟨⟨⟨h1, h2⟩, ⟨hc1, hcM⟩⟩, hc⟩
  have hψ_inj : ∀ n1 ∈ T, ∀ n2 ∈ T, ψ n1 = ψ n2 → n1 = n2 := by
    intro n1 hn1 n2 hn2 heq
    simp only [ψ, dif_pos hn1, dif_pos hn2, Prod.mk.injEq] at heq
    have e1 := (hcWit_spec n1 hn1).2
    have e2 := (hcWit_spec n2 hn2).2
    have hreal : (n1 : ℝ) = (n2 : ℝ) := by rw [e1, e2, heq.1, heq.2]
    exact_mod_cast hreal
  have h1_le : ∀ n ∈ T, (1 : ℝ) ≤ 400 * δ ^ 2 * (Sval (ψ n).1 (ψ n).2) ^ 2 := by
    intro n hn
    have hn' := hn
    simp only [T, Finset.mem_filter, Finset.mem_Icc] at hn'
    simp only [ψ, dif_pos hn]
    have heq := (hcWit_spec n hn).2
    have hN20 : (N : ℝ) ≤ 20 * (n : ℝ) := by exact_mod_cast hn'.2.1
    have hfn_le : (f n : ℝ) ≤ δ * (N : ℝ) := by
      have : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hn'.1.2
      nlinarith [hn'.2.2.2]
    have hN_pos : (0 : ℝ) < (N : ℝ) := by
      have : 1 ≤ N := le_trans hn'.1.1 hn'.1.2
      exact Nat.cast_pos.mpr (by omega)
    have hS_nn : 0 ≤ Sval (f n) (cWit n hn) :=
      Finset.sum_nonneg (fun _ _ => by positivity)
    have hkey : (N : ℝ) ≤ 20 * δ * (N : ℝ) * Sval (f n) (cWit n hn) := by
      have hmul : (f n : ℝ) * Sval (f n) (cWit n hn) ≤ δ * (N : ℝ) * Sval (f n) (cWit n hn) :=
        mul_le_mul_of_nonneg_right hfn_le hS_nn
      linarith
    have h1_le_lin : (1 : ℝ) ≤ 20 * δ * Sval (f n) (cWit n hn) := by
      nlinarith
    nlinarith
  have hcard_le : (T.card : ℝ) ≤ 400 * δ ^ 2 * ∑ p ∈ Pairs, (Sval p.1 p.2) ^ 2 := by
    let Fp : ℕ × ℕ → ℝ := fun p => (Sval p.1 p.2) ^ 2
    calc (T.card : ℝ) = ∑ _n ∈ T, (1 : ℝ) := by simp
      _ ≤ ∑ n ∈ T, 400 * δ ^ 2 * Fp (ψ n) := Finset.sum_le_sum h1_le
      _ = 400 * δ ^ 2 * ∑ n ∈ T, Fp (ψ n) := by rw [← Finset.mul_sum]
      _ = 400 * δ ^ 2 * ∑ p ∈ T.image ψ, Fp p := by rw [Finset.sum_image (f := Fp) hψ_inj]
      _ ≤ 400 * δ ^ 2 * ∑ p ∈ Pairs, Fp p := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro p hp
            rcases Finset.mem_image.mp hp with ⟨n, hn, rfl⟩
            exact hψ_mem n hn
          · intro _ _ _; dsimp only [Fp]; positivity
  have hPairs_eq : ∑ p ∈ Pairs, (Sval p.1 p.2) ^ 2 =
      ∑ m ∈ Finset.Icc 1 M, ∑ c ∈ m.divisors, (Sval m c) ^ 2 := by
    simp only [Pairs, Finset.sum_filter, Finset.sum_product]
    apply Finset.sum_congr rfl; intro m hm
    rw [Finset.mem_Icc] at hm
    rw [← Finset.sum_filter]
    congr 1; ext c
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · exact fun h => h.2
    · intro hc
      refine ⟨⟨Nat.pos_of_mem_divisors hc, ?_⟩, hc⟩
      exact le_trans (Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_divisors hc)) hm.2
  have hsum_le : ∑ m ∈ Finset.Icc 1 M, ∑ c ∈ m.divisors, (Sval m c) ^ 2 ≤ 16 * (M : ℝ) := by
    have hinner : ∀ m ∈ Finset.Icc 1 M,
        ∑ c ∈ m.divisors, (Sval m c) ^ 2 ≤
        ∑ a ∈ m.divisors, ∑ b ∈ m.divisors, (1 : ℝ) / (max a b : ℕ) := by
      intro m _
      calc ∑ c ∈ m.divisors, (Sval m c) ^ 2
        _ = ∑ c ∈ m.divisors, ∑ a ∈ m.divisors, ∑ b ∈ m.divisors,
              (if c ≤ a ∧ c ≤ b then (1 : ℝ) / ((a : ℝ) * (b : ℝ)) else 0) := by
            apply Finset.sum_congr rfl; intro c _
            simp only [Sval, sq, Finset.sum_filter]
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl; intro a _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl; intro b _
            by_cases ha : c ≤ a <;> by_cases hb : c ≤ b <;> simp [ha, hb]; ring
        _ = ∑ a ∈ m.divisors, ∑ b ∈ m.divisors, ∑ c ∈ m.divisors,
              (if c ≤ a ∧ c ≤ b then (1 : ℝ) / ((a : ℝ) * (b : ℝ)) else 0) := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl; intro a _
            rw [Finset.sum_comm]
        _ ≤ ∑ a ∈ m.divisors, ∑ b ∈ m.divisors, (1 : ℝ) / (max a b : ℕ) := by
            apply Finset.sum_le_sum; intro a ha
            apply Finset.sum_le_sum; intro b hb
            rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
            have hcnt : (m.divisors.filter (fun c => c ≤ a ∧ c ≤ b)).card ≤ min a b := by
              have hsub : m.divisors.filter (fun c => c ≤ a ∧ c ≤ b) ⊆ Finset.Icc 1 (min a b) := by
                intro c hc
                simp only [Finset.mem_filter, Finset.mem_Icc] at hc ⊢
                exact ⟨Nat.pos_of_mem_divisors hc.1, le_min hc.2.1 hc.2.2⟩
              exact le_trans (Finset.card_le_card hsub) (by simp)
            have hcnt' : ((m.divisors.filter (fun c => c ≤ a ∧ c ≤ b)).card : ℝ) ≤
                ((min a b : ℕ) : ℝ) := by exact_mod_cast hcnt
            have ha_pos : (0 : ℝ) < (a : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_mem_divisors ha)
            have hb_pos : (0 : ℝ) < (b : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_mem_divisors hb)
            have hmin_max : ((min a b : ℕ) : ℝ) * ((max a b : ℕ) : ℝ) = (a : ℝ) * (b : ℝ) := by
              rcases le_total a b with hab | hba
              · rw [min_eq_left hab, max_eq_right hab]
              · rw [min_eq_right hba, max_eq_left hba, mul_comm]
            have hmax_pos : (0 : ℝ) < ((max a b : ℕ) : ℝ) := by
              rcases le_total a b with hab | hba
              · rw [max_eq_right hab]; exact hb_pos
              · rw [max_eq_left hba]; exact ha_pos
            have heq : ((min a b : ℕ) : ℝ) * ((1 : ℝ) / ((a : ℝ) * (b : ℝ))) =
                (1 : ℝ) / ((max a b : ℕ) : ℝ) := by
              rw [mul_one_div, div_eq_div_iff (mul_pos ha_pos hb_pos).ne' hmax_pos.ne']
              linarith [hmin_max]
            calc ((m.divisors.filter (fun c => c ≤ a ∧ c ≤ b)).card : ℝ) *
                  ((1 : ℝ) / ((a : ℝ) * (b : ℝ)))
              _ ≤ ((min a b : ℕ) : ℝ) * ((1 : ℝ) / ((a : ℝ) * (b : ℝ))) :=
                  mul_le_mul_of_nonneg_right hcnt' (by positivity)
              _ = (1 : ℝ) / ((max a b : ℕ) : ℝ) := heq
    calc ∑ m ∈ Finset.Icc 1 M, ∑ c ∈ m.divisors, (Sval m c) ^ 2
      _ ≤ ∑ m ∈ Finset.Icc 1 M, ∑ a ∈ m.divisors, ∑ b ∈ m.divisors,
            (1 : ℝ) / ((max a b : ℕ) : ℝ) := Finset.sum_le_sum hinner
      _ = ∑ m ∈ Finset.Icc 1 M, ∑ a ∈ Finset.Icc 1 M, ∑ b ∈ Finset.Icc 1 M,
            (if Nat.lcm a b ∣ m then (1 : ℝ) / ((max a b : ℕ) : ℝ) else 0) := by
          apply Finset.sum_congr rfl; intro m hm
          rw [Finset.mem_Icc] at hm
          have hm0 : m ≠ 0 := by omega
          have hsub : m.divisors ⊆ Finset.Icc 1 M := fun d hd =>
            Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd,
              le_trans (Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_divisors hd)) hm.2⟩
          have hiff : ∀ a b, (Nat.lcm a b ∣ m) ↔ (a ∈ m.divisors ∧ b ∈ m.divisors) := by
            intro a b
            simp only [Nat.lcm_dvd_iff, Nat.mem_divisors, hm0, ne_eq, not_false_eq_true, and_true]
          calc ∑ a ∈ m.divisors, ∑ b ∈ m.divisors, (1 : ℝ) / ((max a b : ℕ) : ℝ)
            _ = ∑ a ∈ Finset.Icc 1 M, if a ∈ m.divisors then
                  (∑ b ∈ Finset.Icc 1 M, if b ∈ m.divisors then (1 : ℝ) / ((max a b : ℕ) : ℝ) else 0)
                else 0 := by
                rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hsub]
                apply Finset.sum_congr rfl; intro a _
                rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hsub]
            _ = ∑ a ∈ Finset.Icc 1 M, ∑ b ∈ Finset.Icc 1 M,
                  (if Nat.lcm a b ∣ m then (1 : ℝ) / ((max a b : ℕ) : ℝ) else 0) := by
                apply Finset.sum_congr rfl; intro a _
                by_cases ham : a ∈ m.divisors
                · rw [if_pos ham]
                  apply Finset.sum_congr rfl; intro b _
                  simp only [hiff a b, ham, true_and]
                · rw [if_neg ham, Finset.sum_eq_zero]
                  intro b _
                  simp only [hiff a b, ham, false_and, ↓reduceIte]
      _ = ∑ a ∈ Finset.Icc 1 M, ∑ b ∈ Finset.Icc 1 M,
            (((Finset.Icc 1 M).filter (fun m => Nat.lcm a b ∣ m)).card : ℝ) *
              ((1 : ℝ) / ((max a b : ℕ) : ℝ)) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro a _
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro b _
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ a ∈ Finset.Icc 1 M, ∑ b ∈ Finset.Icc 1 M,
            ((M : ℝ) / (Nat.lcm a b : ℝ)) * ((1 : ℝ) / ((max a b : ℕ) : ℝ)) := by
          apply Finset.sum_le_sum; intro a ha
          apply Finset.sum_le_sum; intro b hb
          rw [Finset.mem_Icc] at ha hb
          have hlcm_pos : 1 ≤ Nat.lcm a b :=
            Nat.pos_of_ne_zero (Nat.lcm_ne_zero (by omega) (by omega))
          exact mul_le_mul_of_nonneg_right (card_multiples_Icc_le M (Nat.lcm a b) hlcm_pos)
            (by positivity)
      _ = (M : ℝ) * ∑ a ∈ Finset.Icc 1 M, ∑ b ∈ Finset.Icc 1 M,
            (1 : ℝ) / ((max a b : ℕ) * (Nat.lcm a b : ℝ)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro a _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro b _; ring
      _ ≤ (M : ℝ) * 16 := mul_le_mul_of_nonneg_left (double_sum_max_lcm_le M) (Nat.cast_nonneg _)
      _ = 16 * (M : ℝ) := by ring
  have hM_le : (M : ℝ) ≤ δ * (N : ℝ) := Nat.floor_le (by positivity)
  calc (T.card : ℝ) ≤ 400 * δ ^ 2 * ∑ p ∈ Pairs, (Sval p.1 p.2) ^ 2 := hcard_le
    _ = 400 * δ ^ 2 * ∑ m ∈ Finset.Icc 1 M, ∑ c ∈ m.divisors, (Sval m c) ^ 2 := by rw [hPairs_eq]
    _ ≤ 400 * δ ^ 2 * (16 * (M : ℝ)) := mul_le_mul_of_nonneg_left hsum_le (by positivity)
    _ ≤ 400 * δ ^ 2 * (16 * (δ * (N : ℝ))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hM_le (by norm_num)) (by positivity)
    _ = 6400 * δ ^ 3 * (N : ℝ) := by ring

/-! ### Section 3: Representability of `p + 2^(r+1) - 1` -/

private lemma list_eq_of_pairwise_lt_iff {L1 L2 : List ℕ}
    (h1 : L1.Pairwise (· < ·)) (h2 : L2.Pairwise (· < ·))
    (hmem : ∀ x, x ∈ L1 ↔ x ∈ L2) : L1 = L2 := by
  induction L1 generalizing L2 with
  | nil =>
    cases L2 with
    | nil => rfl
    | cons b t =>
      exfalso
      have : b ∈ ([] : List ℕ) := (hmem b).mpr (by simp)
      simp at this
  | cons a s ih =>
    cases L2 with
    | nil =>
      exfalso
      have : a ∈ ([] : List ℕ) := (hmem a).mp (by simp)
      simp at this
    | cons b t =>
      rw [List.pairwise_cons] at h1 h2
      have hab : a = b := by
        have ha : a ∈ b :: t := (hmem a).mp (by simp)
        have hb : b ∈ a :: s := (hmem b).mpr (by simp)
        rcases List.mem_cons.mp ha with rfl | hat
        · rfl
        · rcases List.mem_cons.mp hb with rfl | hbs
          · rfl
          · have hlt1 : b < a := h2.1 a hat
            have hlt2 : a < b := h1.1 b hbs
            omega
      subst hab
      congr 1
      apply ih h1.2 h2.2
      intro x
      have hx := hmem x
      simp only [List.mem_cons] at hx
      constructor
      · intro hxs
        have hne : x ≠ a := ne_of_gt (h1.1 x hxs)
        exact (hx.mp (Or.inr hxs)).resolve_left hne
      · intro hxt
        have hne : x ≠ a := ne_of_gt (h2.1 x hxt)
        exact (hx.mpr (Or.inr hxt)).resolve_left hne

private lemma representable_prime_add_pow_two (r p : ℕ) (hp : p.Prime) (hgt : 2 ^ r < p) :
    Representable (p + (2 ^ (r + 1) - 1)) := by
  refine ⟨2 ^ r * p, r + 2, by omega, ?_⟩
  set L1 : List ℕ := (List.range (r + 1)).map (fun j => 2 ^ j)
  set L2 : List ℕ := (List.range (r + 1)).map (fun j => 2 ^ j * p)
  set L : List ℕ := L1 ++ L2
  have hL1_lt : L1.Pairwise (· < ·) := by
    rw [List.pairwise_map]
    exact List.pairwise_lt_range.imp (fun {a b} hab => Nat.pow_lt_pow_right (by norm_num) hab)
  have hL2_lt : L2.Pairwise (· < ·) := by
    rw [List.pairwise_map]
    exact List.pairwise_lt_range.imp (fun {a b} hab =>
      Nat.mul_lt_mul_of_pos_right (Nat.pow_lt_pow_right (by norm_num) hab) hp.pos)
  have hL_lt : L.Pairwise (· < ·) := by
    rw [List.pairwise_append]
    refine ⟨hL1_lt, hL2_lt, ?_⟩
    intro x hx y hy
    rcases List.mem_map.mp hx with ⟨i, hi, rfl⟩
    rcases List.mem_map.mp hy with ⟨j, hj, rfl⟩
    rw [List.mem_range] at hi hj
    have h1 : 2 ^ i ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : p ≤ 2 ^ j * p := Nat.le_mul_of_pos_left p (Nat.two_pow_pos j)
    omega
  have hcop : (2 ^ r).Coprime p := by
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · simp
    · apply Nat.Coprime.pow_left
      have hp2 : p ≠ 2 := by
        have : 2 ≤ 2 ^ r := le_trans (by norm_num : 2 ≤ 2 ^ 1) (Nat.pow_le_pow_right (by norm_num) hr)
        omega
      exact ((Nat.Prime.coprime_iff_not_dvd hp).mpr
        (fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h))).symm
  have hL_mem : ∀ d, d ∈ L ↔ d ∈ (2 ^ r * p).divisors := by
    intro d
    rw [Nat.divisors_mul, Finset.mem_mul]
    simp only [L, L1, L2, List.mem_append, List.mem_map, List.mem_range]
    constructor
    · rintro (⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩)
      · exact ⟨2 ^ j, Nat.mem_divisors.mpr ⟨Nat.pow_dvd_pow 2 (by omega), (Nat.two_pow_pos r).ne'⟩,
          1, Nat.one_mem_divisors.mpr hp.ne_zero, by ring⟩
      · exact ⟨2 ^ j, Nat.mem_divisors.mpr ⟨Nat.pow_dvd_pow 2 (by omega), (Nat.two_pow_pos r).ne'⟩,
          p, Nat.mem_divisors.mpr ⟨dvd_rfl, hp.ne_zero⟩, rfl⟩
    · rintro ⟨a, ha, b, hb, rfl⟩
      rw [Nat.mem_divisors] at ha hb
      rw [Nat.dvd_prime_pow Nat.prime_two] at ha
      rcases ha.1 with ⟨j, hj, rfl⟩
      rw [Nat.dvd_prime hp] at hb
      rcases hb.1 with rfl | rfl
      · left; exact ⟨j, by omega, by ring⟩
      · right; exact ⟨j, by omega, rfl⟩
  have hsort : (2 ^ r * p).divisors.sort (· ≤ ·) = L := by
    apply list_eq_of_pairwise_lt_iff (pairwise_lt_of_sort _) hL_lt
    intro x; rw [Finset.mem_sort, hL_mem]
  rw [hsort]
  have hL1_len : L1.length = r + 1 := by simp [L1]
  have hL2_cons : L2 = p :: (List.range r).map (fun j => 2 ^ (j + 1) * p) := by
    simp only [L2, List.range_succ_eq_map, List.map_cons, List.map_map, Function.comp_def]
    simp
  have htake : L.take (r + 2) = L1 ++ [p] := by
    rw [show L = L1 ++ L2 from rfl, List.take_append, hL1_len]
    rw [show r + 2 - (r + 1) = 1 by omega, List.take_of_length_le (by omega : L1.length ≤ r + 2)]
    rw [hL2_cons]; simp
  rw [htake, List.sum_append, List.sum_singleton]
  have hsum_pow : L1.sum = 2 ^ (r + 1) - 1 := by
    clear hL1_lt hL2_lt hL_lt hcop hL_mem hsort hL1_len hL2_cons htake hgt hp
    induction r with
    | zero => simp [L1]
    | succ k ih =>
      simp only [L1, List.range_succ, List.map_append, List.map_singleton, List.sum_append,
        List.sum_singleton] at ih ⊢
      have hpos : 1 ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
      rw [ih]
      have : 2 ^ (k + 2) = 2 ^ (k + 1) + 2 ^ (k + 1) := by ring
      omega
  rw [hsum_pow]; omega

/-! ### Section 4: Chebyshev & Weak Mertens Bounds -/

private def primesUpTo (n : ℕ) : Finset ℕ := (Finset.range (n + 1)).filter Nat.Prime

private lemma theta_le (n : ℕ) :
    ∑ p ∈ primesUpTo n, Real.log (p : ℝ) ≤ (n : ℝ) * Real.log 4 := by
  have hprim : primorial n = ∏ p ∈ primesUpTo n, p := rfl
  have hle : (∏ p ∈ primesUpTo n, p : ℕ) ≤ 4 ^ n := hprim ▸ primorial_le_four_pow n
  have hprod_pos : (0 : ℝ) < (∏ p ∈ primesUpTo n, (p : ℝ)) :=
    Finset.prod_pos fun p hp => Nat.cast_pos.mpr (Finset.mem_filter.mp hp).2.pos
  have hle_real : (∏ p ∈ primesUpTo n, (p : ℝ)) ≤ (4 : ℝ) ^ n := by
    rw [← Nat.cast_prod]; exact_mod_cast hle
  calc ∑ p ∈ primesUpTo n, Real.log (p : ℝ)
    _ = Real.log (∏ p ∈ primesUpTo n, (p : ℝ)) := by
        rw [Real.log_prod (fun p hp => (Nat.cast_pos.mpr (Finset.mem_filter.mp hp).2.pos).ne')]
    _ ≤ Real.log ((4 : ℝ) ^ n) := Real.log_le_log hprod_pos hle_real
    _ = (n : ℝ) * Real.log 4 := by rw [Real.log_pow]

private lemma log_four_bounds : 1.386 < Real.log 4 ∧ Real.log 4 < 1.387 := by
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]; norm_num
  rw [h4]
  constructor <;> linarith [Real.log_two_gt_d9, Real.log_two_lt_d9]

private lemma log_le_four_fourth_root (n : ℕ) (hn : 1 ≤ n) :
    Real.log (n : ℝ) ≤ 4 * ((Nat.sqrt (Nat.sqrt n) + 1 : ℕ) : ℝ) := by
  set s := Nat.sqrt (Nat.sqrt n)
  have h1 : n < (Nat.sqrt n + 1) ^ 2 := by
    have := Nat.lt_succ_sqrt n; nlinarith
  have h2 : Nat.sqrt n < (s + 1) ^ 2 := by
    have := Nat.lt_succ_sqrt (Nat.sqrt n); nlinarith
  have h3 : n < (s + 1) ^ 4 := by
    have : Nat.sqrt n + 1 ≤ (s + 1) ^ 2 := h2
    calc n < (Nat.sqrt n + 1) ^ 2 := h1
      _ ≤ ((s + 1) ^ 2) ^ 2 := Nat.pow_le_pow_left this 2
      _ = (s + 1) ^ 4 := by ring
  have h3R : (n : ℝ) < ((s + 1 : ℕ) : ℝ) ^ 4 := by exact_mod_cast h3
  have hs_pos : (0 : ℝ) < ((s + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (Nat.succ_pos s)
  calc Real.log (n : ℝ) ≤ Real.log (((s + 1 : ℕ) : ℝ) ^ 4) :=
        Real.log_le_log (Nat.cast_pos.mpr hn) h3R.le
    _ = 4 * Real.log ((s + 1 : ℕ) : ℝ) := by rw [Real.log_pow]; norm_num
    _ ≤ 4 * (((s + 1 : ℕ) : ℝ) - 1) :=
        mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hs_pos) (by norm_num)
    _ ≤ 4 * ((s + 1 : ℕ) : ℝ) := by linarith

private lemma pi_upper (n : ℕ) (hn : 2 ^ 20 ≤ n) :
    ((primesUpTo n).card : ℝ) ≤ 3 * (n : ℝ) / Real.log (n : ℝ) := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hlog_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  set r := Nat.sqrt n
  have hsplit : (primesUpTo n).card =
      ((primesUpTo n).filter (fun p => p ≤ r)).card +
      ((primesUpTo n).filter (fun p => ¬ (p ≤ r))).card := by
    rw [Finset.card_filter_add_card_filter_not]
  have hlow : (((primesUpTo n).filter (fun p => p ≤ r)).card : ℝ) ≤ (r : ℝ) := by
    have hsub : (primesUpTo n).filter (fun p => p ≤ r) ⊆ Finset.Icc 1 r := by
      intro p hp
      simp only [primesUpTo, Finset.mem_filter, Finset.mem_Icc] at hp ⊢
      exact ⟨hp.1.2.pos, hp.2⟩
    exact_mod_cast le_trans (Finset.card_le_card hsub) (by simp)
  have hhigh : (((primesUpTo n).filter (fun p => ¬ (p ≤ r))).card : ℝ) * (Real.log (n : ℝ) / 2) ≤
      (n : ℝ) * Real.log 4 := by
    calc (((primesUpTo n).filter (fun p => ¬ (p ≤ r))).card : ℝ) * (Real.log (n : ℝ) / 2)
      _ = ∑ _p ∈ (primesUpTo n).filter (fun p => ¬ (p ≤ r)), (Real.log (n : ℝ) / 2) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ p ∈ (primesUpTo n).filter (fun p => ¬ (p ≤ r)), Real.log (p : ℝ) := by
          apply Finset.sum_le_sum; intro p hp
          simp only [Finset.mem_filter] at hp
          have hrp : r + 1 ≤ p := by omega
          have hn_lt_p2 : n < p ^ 2 := by
            have := Nat.lt_succ_sqrt n
            calc n < (r + 1) * (r + 1) := this
              _ ≤ p * p := Nat.mul_le_mul hrp hrp
              _ = p ^ 2 := (sq p).symm
          have hlog2 : Real.log (n : ℝ) ≤ 2 * Real.log (p : ℝ) := by
            calc Real.log (n : ℝ) ≤ Real.log ((p : ℝ) ^ 2) :=
                  Real.log_le_log hn_pos (by exact_mod_cast hn_lt_p2.le)
              _ = 2 * Real.log (p : ℝ) := by rw [Real.log_pow]; norm_num
          linarith
      _ ≤ ∑ p ∈ primesUpTo n, Real.log (p : ℝ) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          intro p hp _
          exact Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt.le)
      _ ≤ (n : ℝ) * Real.log 4 := theta_le n
  have hhigh' : (((primesUpTo n).filter (fun p => ¬ (p ≤ r))).card : ℝ) ≤
      2 * Real.log 4 * (n : ℝ) / Real.log (n : ℝ) := by
    rw [le_div_iff₀ hlog_pos]; linarith
  have hr_log : (r : ℝ) * Real.log (n : ℝ) ≤ 0.2 * (n : ℝ) := by
    set s := Nat.sqrt r
    have hs_ge : 32 ≤ s := by
      have hr_ge : 1024 ≤ r := by rw [Nat.le_sqrt]; omega
      rw [Nat.le_sqrt]; omega
    have hs2_le_r : s ^ 2 ≤ r := by have := Nat.sqrt_le r; nlinarith
    have hr2_le_n : r ^ 2 ≤ n := by have := Nat.sqrt_le n; nlinarith
    have hlog_bd : Real.log (n : ℝ) ≤ 4 * ((s + 1 : ℕ) : ℝ) := log_le_four_fourth_root n (by omega)
    have hr_s : (r : ℝ) * (4 * ((s + 1 : ℕ) : ℝ)) ≤ 0.2 * (n : ℝ) := by
      have hnat : 20 * (r * (s + 1)) ≤ n := by
        have h1 : 20 * (s + 1) ≤ r := by
          have : 20 * (s + 1) ≤ s ^ 2 := by nlinarith
          exact le_trans this hs2_le_r
        calc 20 * (r * (s + 1)) = r * (20 * (s + 1)) := by ring
          _ ≤ r * r := Nat.mul_le_mul_left r h1
          _ = r ^ 2 := (sq r).symm
          _ ≤ n := hr2_le_n
      have hreal : (20 : ℝ) * ((r : ℝ) * ((s + 1 : ℕ) : ℝ)) ≤ (n : ℝ) := by exact_mod_cast hnat
      linarith
    have h1 := mul_le_mul_of_nonneg_left hlog_bd (Nat.cast_nonneg r)
    linarith
  have hr_le : (r : ℝ) ≤ 0.2 * (n : ℝ) / Real.log (n : ℝ) := by
    rw [le_div_iff₀ hlog_pos]; exact hr_log
  have hcast : ((primesUpTo n).card : ℝ) =
      (((primesUpTo n).filter (fun p => p ≤ r)).card : ℝ) +
      (((primesUpTo n).filter (fun p => ¬ (p ≤ r))).card : ℝ) := by
    exact_mod_cast hsplit
  have hcoeff : 0.2 + 2 * Real.log 4 ≤ 3 := by linarith [log_four_bounds.2]
  calc ((primesUpTo n).card : ℝ)
    _ ≤ (r : ℝ) + 2 * Real.log 4 * (n : ℝ) / Real.log (n : ℝ) := by linarith
    _ ≤ 0.2 * (n : ℝ) / Real.log (n : ℝ) + 2 * Real.log 4 * (n : ℝ) / Real.log (n : ℝ) := by linarith
    _ = (0.2 + 2 * Real.log 4) * (n : ℝ) / Real.log (n : ℝ) := by ring
    _ ≤ 3 * (n : ℝ) / Real.log (n : ℝ) := by
        apply div_le_div_of_nonneg_right _ hlog_pos.le
        exact mul_le_mul_of_nonneg_right hcoeff hn_pos.le

private lemma pi_lower (n : ℕ) (hn : 2 ^ 20 ≤ n) :
    0.6 * (n : ℝ) / Real.log (n : ℝ) ≤ ((primesUpTo n).card : ℝ) := by
  set m := n / 2
  have hm4 : 4 ≤ m := by omega
  have h2m_le : 2 * m ≤ n := by omega
  have hcb_pos : 0 < m.centralBinom := Nat.centralBinom_pos m
  have h4m : 4 ^ m < m * m.centralBinom := Nat.four_pow_lt_mul_centralBinom m hm4
  have hcb_le : m.centralBinom ≤ n ^ (primesUpTo n).card := by
    have hsub : m.centralBinom.primeFactors ⊆ primesUpTo n := by
      intro p hp
      rw [Nat.mem_primeFactors] at hp
      simp only [primesUpTo, Finset.mem_filter, Finset.mem_range]
      refine ⟨?_, hp.1⟩
      have hdvd_fac : p ∣ (2 * m).factorial := by
        have hch := Nat.choose_mul_factorial_mul_factorial (show m ≤ 2 * m by omega)
        have hcb_dvd : m.centralBinom ∣ (2 * m).factorial := ⟨m.factorial * (2 * m - m).factorial, by
          unfold Nat.centralBinom; linarith⟩
        exact dvd_trans hp.2.1 hcb_dvd
      have hple : p ≤ 2 * m := (hp.1.dvd_factorial).mp hdvd_fac
      omega
    calc m.centralBinom
      _ = ∏ p ∈ m.centralBinom.primeFactors, p ^ (m.centralBinom.factorization p) :=
          eq_prod_primeFactors_pow hcb_pos.ne'
      _ ≤ ∏ _p ∈ m.centralBinom.primeFactors, n := by
          apply Finset.prod_le_prod'
          intro p _
          unfold Nat.centralBinom
          exact le_trans (Nat.pow_factorization_choose_le (by omega)) h2m_le
      _ = n ^ m.centralBinom.primeFactors.card := by rw [Finset.prod_const]
      _ ≤ n ^ (primesUpTo n).card := Nat.pow_le_pow_right (by omega) (Finset.card_le_card hsub)
  have hkey_nat : 4 ^ m ≤ m * n ^ (primesUpTo n).card :=
    le_trans h4m.le (Nat.mul_le_mul_left m hcb_le)
  have hkey_real : (4 : ℝ) ^ m ≤ (m : ℝ) * (n : ℝ) ^ (primesUpTo n).card := by
    exact_mod_cast hkey_nat
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (by omega)
  have hlog_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hlog_ineq : (m : ℝ) * Real.log 4 ≤ Real.log (m : ℝ) + ((primesUpTo n).card : ℝ) * Real.log (n : ℝ) := by
    have h := Real.log_le_log (by positivity : (0 : ℝ) < (4 : ℝ) ^ m) hkey_real
    rw [Real.log_pow, Real.log_mul hm_pos.ne' (pow_pos hn_pos _).ne', Real.log_pow] at h
    exact h
  have hlog_m : Real.log (m : ℝ) ≤ 0.01 * (n : ℝ) := by
    have h1 := log_le_four_fourth_root m (by omega)
    set s := Nat.sqrt (Nat.sqrt m)
    have hs4 : s ^ 4 ≤ m := by
      have ha : s ^ 2 ≤ Nat.sqrt m := by have := Nat.sqrt_le (Nat.sqrt m); nlinarith
      have hb : (Nat.sqrt m) ^ 2 ≤ m := by have := Nat.sqrt_le m; nlinarith
      calc s ^ 4 = (s ^ 2) ^ 2 := by ring
        _ ≤ (Nat.sqrt m) ^ 2 := Nat.pow_le_pow_left ha 2
        _ ≤ m := hb
    have hs_ge : 20 ≤ s := by
      have : 400 ≤ Nat.sqrt m := by rw [Nat.le_sqrt]; omega
      rw [Nat.le_sqrt]; omega
    have hnat : 400 * (s + 1) ≤ n := by
      have hsq : 400 ≤ s ^ 2 := by nlinarith
      have hmul1 : s + 1 ≤ s ^ 2 := by nlinarith
      have : 400 * (s + 1) ≤ s ^ 4 := by
        calc 400 * (s + 1) ≤ s ^ 2 * s ^ 2 := Nat.mul_le_mul hsq hmul1
          _ = s ^ 4 := by ring
      omega
    have hreal : (400 : ℝ) * ((s + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnat
    linarith
  have hm_ge : 0.49 * (n : ℝ) ≤ (m : ℝ) := by
    have : 49 * n ≤ 100 * m := by omega
    have hreal : (49 : ℝ) * (n : ℝ) ≤ 100 * (m : ℝ) := by exact_mod_cast this
    linarith
  rw [div_le_iff₀ hlog_pos]
  nlinarith [log_four_bounds.1]

private lemma primes_in_band (N : ℕ) (hN : 2 ^ 30 ≤ N) :
    0.05 * (N : ℝ) / Real.log (N : ℝ) ≤
      (((Finset.Ioc (N / 20) (N / 2)).filter Nat.Prime).card : ℝ) := by
  have hlogN_pos : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hlogN_ge : 20 ≤ Real.log (N : ℝ) := by
    have h2 : (2 : ℝ) ^ (30 : ℕ) ≤ (N : ℝ) := by exact_mod_cast hN
    have h := Real.log_le_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ (30 : ℕ)) h2
    rw [Real.log_pow] at h; norm_num at h
    linarith [Real.log_two_gt_d9]
  have hsub : primesUpTo (N / 20) ⊆ primesUpTo (N / 2) := by
    intro p hp
    simp only [primesUpTo, Finset.mem_filter, Finset.mem_range] at hp ⊢
    exact ⟨by omega, hp.2⟩
  have hsdiff : (Finset.Ioc (N / 20) (N / 2)).filter Nat.Prime =
      primesUpTo (N / 2) \ primesUpTo (N / 20) := by
    ext p
    simp only [primesUpTo, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_sdiff, Finset.mem_range]
    constructor
    · rintro ⟨⟨h1, h2⟩, hp⟩; exact ⟨⟨by omega, hp⟩, fun h => by omega⟩
    · rintro ⟨⟨h2, hp⟩, hnot⟩
      refine ⟨⟨?_, by omega⟩, hp⟩
      by_contra hle; exact hnot ⟨by omega, hp⟩
  have hcard : (((Finset.Ioc (N / 20) (N / 2)).filter Nat.Prime).card : ℝ) =
      ((primesUpTo (N / 2)).card : ℝ) - ((primesUpTo (N / 20)).card : ℝ) := by
    rw [hsdiff, Finset.card_sdiff_of_subset hsub, Nat.cast_sub (Finset.card_le_card hsub)]
  rw [hcard]
  have hlow := pi_lower (N / 2) (by omega)
  have hupp := pi_upper (N / 20) (by omega)
  have hlog_half_le : Real.log ((N / 2 : ℕ) : ℝ) ≤ Real.log (N : ℝ) :=
    Real.log_le_log (Nat.cast_pos.mpr (by omega)) (by exact_mod_cast Nat.div_le_self N 2)
  have hlog_half_pos : 0 < Real.log ((N / 2 : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < N / 2))
  have hN2_ge : 0.49 * (N : ℝ) ≤ ((N / 2 : ℕ) : ℝ) := by
    have : 49 * N ≤ 100 * (N / 2) := by omega
    have hreal : (49 : ℝ) * (N : ℝ) ≤ 100 * ((N / 2 : ℕ) : ℝ) := by exact_mod_cast this
    linarith
  have hlow' : 0.29 * (N : ℝ) / Real.log (N : ℝ) ≤ ((primesUpTo (N / 2)).card : ℝ) := by
    have h1 : 0.29 * (N : ℝ) / Real.log (N : ℝ) ≤ 0.6 * ((N / 2 : ℕ) : ℝ) / Real.log ((N / 2 : ℕ) : ℝ) := by
      calc 0.29 * (N : ℝ) / Real.log (N : ℝ)
        _ ≤ 0.6 * ((N / 2 : ℕ) : ℝ) / Real.log (N : ℝ) := by
            apply div_le_div_of_nonneg_right _ hlogN_pos.le; linarith
        _ ≤ 0.6 * ((N / 2 : ℕ) : ℝ) / Real.log ((N / 2 : ℕ) : ℝ) :=
            div_le_div_of_nonneg_left (by positivity) hlog_half_pos hlog_half_le
    linarith
  have hlog20_ge : 0.8 * Real.log (N : ℝ) ≤ Real.log ((N / 20 : ℕ) : ℝ) := by
    have h21 : (N : ℝ) ≤ 21 * ((N / 20 : ℕ) : ℝ) := by
      have : N ≤ 21 * (N / 20) := by omega
      exact_mod_cast this
    have hlog21 : Real.log 21 ≤ 3.5 := by
      have h1 : Real.log (21 : ℝ) ≤ Real.log ((2 : ℝ) ^ (5 : ℕ)) :=
        Real.log_le_log (by norm_num) (by norm_num)
      rw [Real.log_pow] at h1; norm_num at h1
      linarith [Real.log_two_lt_d9]
    have h := Real.log_le_log (Nat.cast_pos.mpr (by omega)) h21
    rw [Real.log_mul (by norm_num) (Nat.cast_pos.mpr (by omega)).ne'] at h
    linarith
  have hN20_le : ((N / 20 : ℕ) : ℝ) ≤ (N : ℝ) / 20 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 20)]
    exact_mod_cast Nat.div_mul_le_self N 20
  have hupp' : ((primesUpTo (N / 20)).card : ℝ) ≤ 0.2 * (N : ℝ) / Real.log (N : ℝ) := by
    have h1 : 3 * ((N / 20 : ℕ) : ℝ) / Real.log ((N / 20 : ℕ) : ℝ) ≤ 0.2 * (N : ℝ) / Real.log (N : ℝ) := by
      calc 3 * ((N / 20 : ℕ) : ℝ) / Real.log ((N / 20 : ℕ) : ℝ)
        _ ≤ 3 * ((N : ℝ) / 20) / Real.log ((N / 20 : ℕ) : ℝ) :=
            div_le_div_of_nonneg_right (by linarith) (by linarith)
        _ ≤ 3 * ((N : ℝ) / 20) / (0.8 * Real.log (N : ℝ)) :=
            div_le_div_of_nonneg_left (by positivity) (by linarith) hlog20_ge
        _ = (3 / 16) * (N : ℝ) / Real.log (N : ℝ) := by ring
        _ ≤ 0.2 * (N : ℝ) / Real.log (N : ℝ) := by
            apply div_le_div_of_nonneg_right _ hlogN_pos.le
            have : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
            linarith
    linarith
  have hdiff : (0.29 - 0.2) * (N : ℝ) / Real.log (N : ℝ) =
      0.29 * (N : ℝ) / Real.log (N : ℝ) - 0.2 * (N : ℝ) / Real.log (N : ℝ) := by ring
  have hfinal : 0.05 * (N : ℝ) / Real.log (N : ℝ) ≤ (0.29 - 0.2) * (N : ℝ) / Real.log (N : ℝ) := by
    apply div_le_div_of_nonneg_right _ hlogN_pos.le
    have : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    linarith
  linarith

private lemma factorial_le_pow (t : ℕ) : t.factorial ≤ t ^ t := by
  induction t with
  | zero => simp
  | succ k ih =>
    rw [Nat.factorial_succ, pow_succ']
    calc (k + 1) * k.factorial ≤ (k + 1) * k ^ k := Nat.mul_le_mul_left _ ih
      _ ≤ (k + 1) * (k + 1) ^ k := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.le_succ k) k)

private lemma sum_log_div_prime_le (t : ℕ) (ht : 1 ≤ t) :
    ∑ p ∈ primesUpTo t, Real.log (p : ℝ) / (p : ℝ) ≤ Real.log (t : ℝ) + Real.log 4 := by
  have ht_pos : (0 : ℝ) < (t : ℝ) := Nat.cast_pos.mpr (by omega)
  have hfac_pos : 0 < t.factorial := Nat.factorial_pos t
  have hprod_le : ∏ p ∈ primesUpTo t, p ^ (t / p) ≤ t ^ t := by
    have hsub : primesUpTo t ⊆ t.factorial.primeFactors := by
      intro p hp
      simp only [primesUpTo, Finset.mem_filter, Finset.mem_range] at hp
      exact Nat.mem_primeFactors.mpr ⟨hp.2, hp.2.dvd_factorial.mpr (by omega), hfac_pos.ne'⟩
    have hle_exp : ∀ p ∈ primesUpTo t, t / p ≤ t.factorial.factorization p := by
      intro p hp
      simp only [primesUpTo, Finset.mem_filter, Finset.mem_range] at hp
      have : Fact p.Prime := ⟨hp.2⟩
      rw [Nat.factorization_def _ hp.2]
      have hpad := padicValNat_factorial (p := p) (n := t) (b := Nat.log p t + 1) (Nat.lt_succ_self _)
      rw [hpad]
      have h1_mem : 1 ∈ Finset.Ico 1 (Nat.log p t + 1) := by
        rw [Finset.mem_Ico]
        exact ⟨le_rfl, Nat.succ_le_succ (Nat.log_pos hp.2.one_lt (by omega))⟩
      calc t / p = t / p ^ 1 := by simp
        _ ≤ ∑ i ∈ Finset.Ico 1 (Nat.log p t + 1), t / p ^ i :=
            Finset.single_le_sum (f := fun i => t / p ^ i) (fun _ _ => Nat.zero_le _) h1_mem
    calc ∏ p ∈ primesUpTo t, p ^ (t / p)
      _ ≤ ∏ p ∈ primesUpTo t, p ^ (t.factorial.factorization p) :=
          Finset.prod_le_prod' fun p hp => Nat.pow_le_pow_right (Finset.mem_filter.mp hp).2.pos (hle_exp p hp)
      _ ≤ ∏ p ∈ t.factorial.primeFactors, p ^ (t.factorial.factorization p) := by
          apply Finset.prod_le_prod_of_subset_of_one_le' hsub
          intro p hp _
          exact Nat.one_le_pow _ _ (Nat.prime_of_mem_primeFactors hp).pos
      _ = t.factorial := (eq_prod_primeFactors_pow hfac_pos.ne').symm
      _ ≤ t ^ t := factorial_le_pow t
  have hprod_real : (∏ p ∈ primesUpTo t, (p : ℝ) ^ (t / p)) ≤ (t : ℝ) ^ t := by
    simp_rw [← Nat.cast_pow]; rw [← Nat.cast_prod]; exact_mod_cast hprod_le
  have hlog_sum : ∑ p ∈ primesUpTo t, ((t / p : ℕ) : ℝ) * Real.log (p : ℝ) ≤ (t : ℝ) * Real.log (t : ℝ) := by
    have h := Real.log_le_log
      (Finset.prod_pos fun p hp => pow_pos (Nat.cast_pos.mpr (Finset.mem_filter.mp hp).2.pos) _)
      hprod_real
    rw [Real.log_prod (fun p hp => (pow_pos (Nat.cast_pos.mpr (Finset.mem_filter.mp hp).2.pos) _).ne'),
        Real.log_pow] at h
    simpa only [Real.log_pow] using h
  have hfloor : ∑ p ∈ primesUpTo t, ((t : ℝ) / (p : ℝ) - 1) * Real.log (p : ℝ) ≤
      ∑ p ∈ primesUpTo t, ((t / p : ℕ) : ℝ) * Real.log (p : ℝ) := by
    apply Finset.sum_le_sum; intro p hp
    have hp_prime := (Finset.mem_filter.mp hp).2
    have hlog_nn : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hp_prime.one_lt.le)
    apply mul_le_mul_of_nonneg_right _ hlog_nn
    have hp_pos : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hp_prime.pos
    have hmod : t < (t / p + 1) * p := by
      have := Nat.div_add_mod t p
      have := Nat.mod_lt t hp_prime.pos
      nlinarith
    have hmodR : (t : ℝ) < (((t / p : ℕ) : ℝ) + 1) * (p : ℝ) := by exact_mod_cast hmod
    rw [sub_le_iff_le_add, div_le_iff₀ hp_pos]
    linarith
  have hrearr : ∑ p ∈ primesUpTo t, ((t : ℝ) / (p : ℝ) - 1) * Real.log (p : ℝ) =
      (t : ℝ) * (∑ p ∈ primesUpTo t, Real.log (p : ℝ) / (p : ℝ)) -
      ∑ p ∈ primesUpTo t, Real.log (p : ℝ) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro p _; ring
  have hth := theta_le t
  have hmul : (t : ℝ) * (∑ p ∈ primesUpTo t, Real.log (p : ℝ) / (p : ℝ)) ≤
      (t : ℝ) * (Real.log (t : ℝ) + Real.log 4) := by linarith
  exact le_of_mul_le_mul_left hmul ht_pos

private lemma sum_inv_prime_le :
    ∃ C0 : ℝ, 0 < C0 ∧ ∀ Y : ℕ, 1 ≤ Y →
      ∑ p ∈ primesUpTo Y, (1 : ℝ) / (p : ℝ) ≤ C0 + Real.log (Y : ℝ) / 24 := by
  let L : ℕ := 2 ^ 36
  refine ⟨(L : ℝ) + Real.log 4 / 24, by positivity, fun Y hY => ?_⟩
  have hsplit : ∑ p ∈ primesUpTo Y, (1 : ℝ) / (p : ℝ) =
      (∑ p ∈ (primesUpTo Y).filter (fun p => p ≤ L), (1 : ℝ) / (p : ℝ)) +
      (∑ p ∈ (primesUpTo Y).filter (fun p => ¬ (p ≤ L)), (1 : ℝ) / (p : ℝ)) := by
    rw [Finset.sum_filter_add_sum_filter_not]
  rw [hsplit]
  have hsmall : ∑ p ∈ (primesUpTo Y).filter (fun p => p ≤ L), (1 : ℝ) / (p : ℝ) ≤ (L : ℝ) := by
    calc ∑ p ∈ (primesUpTo Y).filter (fun p => p ≤ L), (1 : ℝ) / (p : ℝ)
      _ ≤ ∑ _p ∈ (primesUpTo Y).filter (fun p => p ≤ L), (1 : ℝ) := by
          apply Finset.sum_le_sum; intro p hp
          have hp1 : (1 : ℝ) ≤ (p : ℝ) := by
            exact_mod_cast (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.pos
          exact div_le_one_of_le₀ hp1 (by linarith)
      _ = (((primesUpTo Y).filter (fun p => p ≤ L)).card : ℝ) := by simp
      _ ≤ (L : ℝ) := by
          have hsub : (primesUpTo Y).filter (fun p => p ≤ L) ⊆ Finset.Icc 1 L := by
            intro p hp
            simp only [primesUpTo, Finset.mem_filter, Finset.mem_Icc] at hp ⊢
            exact ⟨hp.1.2.pos, hp.2⟩
          exact_mod_cast le_trans (Finset.card_le_card hsub) (by simp)
  have hbig : ∑ p ∈ (primesUpTo Y).filter (fun p => ¬ (p ≤ L)), (1 : ℝ) / (p : ℝ) ≤
      (Real.log (Y : ℝ) + Real.log 4) / 24 := by
    calc ∑ p ∈ (primesUpTo Y).filter (fun p => ¬ (p ≤ L)), (1 : ℝ) / (p : ℝ)
      _ ≤ ∑ p ∈ (primesUpTo Y).filter (fun p => ¬ (p ≤ L)),
            (Real.log (p : ℝ) / (p : ℝ)) / 24 := by
          apply Finset.sum_le_sum; intro p hp
          simp only [Finset.mem_filter] at hp
          have hp_pos : (0 : ℝ) < (p : ℝ) :=
            Nat.cast_pos.mpr (Finset.mem_filter.mp hp.1).2.pos
          have hlogp : 24 ≤ Real.log (p : ℝ) := by
            have h2 : (2 : ℝ) ^ (36 : ℕ) ≤ (p : ℝ) := by
              exact_mod_cast (le_of_not_ge hp.2 : L ≤ p)
            have h := Real.log_le_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ (36 : ℕ)) h2
            rw [Real.log_pow] at h; norm_num at h
            linarith [Real.log_two_gt_d9]
          rw [div_div, div_le_div_iff₀ hp_pos (by positivity)]
          nlinarith
      _ ≤ ∑ p ∈ primesUpTo Y, (Real.log (p : ℝ) / (p : ℝ)) / 24 := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          intro p hp _
          have h1 : 0 ≤ Real.log (p : ℝ) :=
            Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt.le)
          positivity
      _ = (∑ p ∈ primesUpTo Y, Real.log (p : ℝ) / (p : ℝ)) / 24 := by rw [← Finset.sum_div]
      _ ≤ (Real.log (Y : ℝ) + Real.log 4) / 24 :=
          div_le_div_of_nonneg_right (sum_log_div_prime_le Y hY) (by norm_num)
  linarith

/-! ### Section 5: Multiplicative Helpers & Selberg's Upper-Bound Sieve -/

private lemma primeFactors_lcm_eq {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    (Nat.lcm a b).primeFactors = a.primeFactors ∪ b.primeFactors := by
  ext p
  simp only [Finset.mem_union, Nat.mem_primeFactors, Nat.lcm_ne_zero ha hb, ha, hb,
    ne_eq, not_false_eq_true, and_true]
  constructor
  · rintro ⟨hp, hdvd⟩
    have hmul : p ∣ a * b := by
      rw [← Nat.gcd_mul_lcm a b]; exact dvd_mul_of_dvd_right hdvd _
    rcases hp.dvd_mul.mp hmul with h | h
    · exact Or.inl ⟨hp, h⟩
    · exact Or.inr ⟨hp, h⟩
  · rintro (⟨hp, h⟩ | ⟨hp, h⟩)
    · exact ⟨hp, dvd_trans h (Nat.dvd_lcm_left a b)⟩
    · exact ⟨hp, dvd_trans h (Nat.dvd_lcm_right a b)⟩

private lemma squarefree_lcm {a b : ℕ} (ha : Squarefree a) (hb : Squarefree b) :
    Squarefree (Nat.lcm a b) := by
  rw [Nat.squarefree_iff_prime_squarefree]
  intro p hp hpp
  have ha0 : a ≠ 0 := ha.ne_zero
  have hb0 : b ≠ 0 := hb.ne_zero
  have hlcm_ne : Nat.lcm a b ≠ 0 := Nat.lcm_ne_zero ha0 hb0
  have hfac : 2 ≤ (Nat.lcm a b).factorization p := by
    have := (Nat.factorization_le_iff_dvd (pow_ne_zero 2 hp.ne_zero) hlcm_ne).mpr (by simpa [sq] using hpp)
    simpa [hp.factorization_pow] using this p
  have hfac_lcm : (Nat.lcm a b).factorization p = max (a.factorization p) (b.factorization p) := by
    have h1 := Nat.factorization_lcm ha0 hb0
    exact congrFun (congrArg DFunLike.coe h1) p
  rw [hfac_lcm] at hfac
  rcases le_max_iff.mp hfac with ha2 | hb2
  · have : p * p ∣ a := by
      rw [← sq, ← Nat.factorization_le_iff_dvd (pow_ne_zero 2 hp.ne_zero) ha0]
      intro q
      by_cases hqp : q = p
      · subst hqp; simpa [hp.factorization_pow] using ha2
      · simp [hp.factorization_pow, hqp]
    exact hp.not_isUnit (ha p this)
  · have : p * p ∣ b := by
      rw [← sq, ← Nat.factorization_le_iff_dvd (pow_ne_zero 2 hp.ne_zero) hb0]
      intro q
      by_cases hqp : q = p
      · subst hqp; simpa [hp.factorization_pow] using hb2
      · simp [hp.factorization_pow, hqp]
    exact hp.not_isUnit (hb p this)

private lemma sum_divisors_of_prime_prod (S : Finset ℕ) (hS : ∀ q ∈ S, q.Prime)
    (F : ℕ → ℝ) (hF1 : F 1 = 1)
    (hFmul : ∀ a b, a ≠ 0 → b ≠ 0 → a.Coprime b → F (a * b) = F a * F b) :
    ∑ k ∈ (∏ q ∈ S, q).divisors, F k = ∏ q ∈ S, (1 + F q) := by
  induction S using Finset.induction_on with
  | empty => simp [hF1]
  | insert p s hps ih =>
    have hp : p.Prime := hS p (Finset.mem_insert_self p s)
    have hs : ∀ q ∈ s, q.Prime := fun q hq => hS q (Finset.mem_insert_of_mem hq)
    set m := ∏ q ∈ s, q
    have hcop : p.Coprime m := by
      refine (hp.coprime_iff_not_dvd).mpr fun hdvd => ?_
      rcases (hp.prime.dvd_finsetProd_iff _).mp hdvd with ⟨q, hqs, hpq⟩
      exact hps ((Nat.prime_dvd_prime_iff_eq hp (hs q hqs)).mp hpq ▸ hqs)
    have hdiv_eq : (p * m).divisors = m.divisors ∪ m.divisors.image (fun k => p * k) := by
      ext d
      rw [Nat.divisors_mul, Finset.mem_mul, Finset.mem_union, Finset.mem_image]
      constructor
      · rintro ⟨a, ha, b, hb, rfl⟩
        rw [Nat.mem_divisors] at ha
        rcases (Nat.dvd_prime hp).mp ha.1 with rfl | rfl
        · left; simpa using hb
        · right; exact ⟨b, hb, rfl⟩
      · rintro (hd | ⟨k, hk, rfl⟩)
        · exact ⟨1, Nat.one_mem_divisors.mpr hp.ne_zero, d, hd, one_mul d⟩
        · exact ⟨p, Nat.mem_divisors.mpr ⟨dvd_rfl, hp.ne_zero⟩, k, hk, rfl⟩
    have hdisj : Disjoint m.divisors (m.divisors.image (fun k => p * k)) := by
      rw [Finset.disjoint_left]
      intro d hdm hdim
      rcases Finset.mem_image.mp hdim with ⟨k, _, rfl⟩
      have hpm : p ∣ m := dvd_trans (dvd_mul_right p k) (Nat.dvd_of_mem_divisors hdm)
      exact hp.not_dvd_one (hcop.dvd_of_dvd_mul_left (by simpa using hpm))
    rw [Finset.prod_insert hps, Finset.prod_insert hps, hdiv_eq, Finset.sum_union hdisj]
    have himg : ∑ k ∈ m.divisors.image (fun k => p * k), F k = F p * ∑ k ∈ m.divisors, F k := by
      rw [Finset.sum_image (fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hp.pos h)]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro k hk
      have hk0 : k ≠ 0 := (Nat.pos_of_mem_divisors hk).ne'
      have hcopk : p.Coprime k := hcop.coprime_dvd_right (Nat.dvd_of_mem_divisors hk)
      exact hFmul p k hp.ne_zero hk0 hcopk
    rw [himg, ih hs]; ring

private lemma sum_divisors_of_squarefree {d : ℕ} (hd : Squarefree d)
    (F : ℕ → ℝ) (hF1 : F 1 = 1)
    (hFmul : ∀ a b, a ≠ 0 → b ≠ 0 → a.Coprime b → F (a * b) = F a * F b) :
    ∑ k ∈ d.divisors, F k = ∏ q ∈ d.primeFactors, (1 + F q) := by
  have hprod := Nat.prod_primeFactors_of_squarefree hd
  conv_lhs => rw [← hprod]
  exact sum_divisors_of_prime_prod d.primeFactors
    (fun q hq => Nat.prime_of_mem_primeFactors hq) F hF1 hFmul

private def muSq (d : ℕ) : ℝ := (-1 : ℝ) ^ d.primeFactors.card

private lemma muSq_one : muSq 1 = 1 := by simp [muSq]

private lemma muSq_sq (d : ℕ) : (muSq d) ^ 2 = 1 := by
  unfold muSq
  rw [← pow_mul, mul_comm _ 2, pow_mul]
  norm_num

private lemma muSq_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hcop : a.Coprime b) :
    muSq (a * b) = muSq a * muSq b := by
  simp only [muSq, Nat.primeFactors_mul ha hb]
  have hdisj : Disjoint a.primeFactors b.primeFactors := by
    rw [Finset.disjoint_left]
    intro p hpa hpb
    have hp := Nat.prime_of_mem_primeFactors hpa
    exact hp.not_dvd_one (hcop.gcd_eq_one ▸ Nat.dvd_gcd (Nat.dvd_of_mem_primeFactors hpa) (Nat.dvd_of_mem_primeFactors hpb))
  rw [Finset.card_union_of_disjoint hdisj, pow_add]

private lemma sum_divisors_muSq {m : ℕ} (hm : Squarefree m) :
    ∑ k ∈ m.divisors, muSq k = if m = 1 then 1 else 0 := by
  rw [sum_divisors_of_squarefree hm muSq muSq_one (fun _ _ ha hb hc => muSq_mul ha hb hc)]
  by_cases hm1 : m = 1
  · subst hm1; simp
  · rw [if_neg hm1]
    have hne : m.primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr (by
      have := hm.ne_zero; omega)
    rcases hne with ⟨q, hq⟩
    apply Finset.prod_eq_zero hq
    have hqp := Nat.prime_of_mem_primeFactors hq
    simp [muSq, hqp.primeFactors]

private lemma div_totient_eq_prod {n : ℕ} (hn : n ≠ 0) :
    (n : ℝ) / (n.totient : ℝ) = ∏ q ∈ n.primeFactors, (q : ℝ) / ((q : ℝ) - 1) := by
  have h1 : (n : ℝ) = ∏ q ∈ n.primeFactors, (q : ℝ) ^ (n.factorization q) := by
    simp_rw [← Nat.cast_pow]; rw [← Nat.cast_prod]; exact_mod_cast eq_prod_primeFactors_pow hn
  have h2 : (n.totient : ℝ) =
      ∏ q ∈ n.primeFactors, ((q : ℝ) ^ (n.factorization q - 1) * ((q : ℝ) - 1)) := by
    have hnat : n.totient = ∏ q ∈ n.primeFactors, (q ^ (n.factorization q - 1) * (q - 1)) := by
      rw [Nat.totient_eq_prod_factorization hn]
      change ∏ q ∈ n.factorization.support, q ^ (n.factorization q - 1) * (q - 1) = _
      rw [Nat.support_factorization]
    rw [hnat, Nat.cast_prod]
    apply Finset.prod_congr rfl; intro q hq
    have hq1 : 1 ≤ q := (Nat.prime_of_mem_primeFactors hq).pos
    push_cast [Nat.cast_sub hq1]; rfl
  rw [h1, h2, ← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl; intro q hq
  have hqp := Nat.prime_of_mem_primeFactors hq
  have hk : 1 ≤ n.factorization q :=
    Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp (Nat.support_factorization n ▸ hq))
  have hq_pos : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr hqp.pos
  have hpow : (q : ℝ) ^ (n.factorization q) = (q : ℝ) ^ (n.factorization q - 1) * (q : ℝ) := by
    rw [← pow_succ, Nat.sub_add_cancel hk]
  rw [hpow, mul_div_mul_left _ _ (pow_pos hq_pos _).ne']

/-! #### Selberg sieve definitions and lemmas for a fixed even shift `h` -/

private def rho (h d : ℕ) : ℕ :=
  ∏ q ∈ d.primeFactors, if q ∣ h then 1 else 2

private noncomputable def gFn (h d : ℕ) : ℝ := (rho h d : ℝ) / (d : ℝ)

private noncomputable def hFn (h d : ℕ) : ℝ :=
  ∏ q ∈ d.primeFactors, ((q : ℝ) - (if q ∣ h then 1 else 2)) / (if q ∣ h then 1 else 2)

private def SqFree (z : ℕ) : Finset ℕ := (Finset.Icc 1 z).filter Squarefree

private lemma rho_one (h : ℕ) : rho h 1 = 1 := by simp [rho]

private lemma rho_pos (h d : ℕ) : 0 < rho h d := by
  unfold rho
  apply Finset.prod_pos; intro q _; split_ifs <;> norm_num

private lemma rho_lcm_mul_gcd {h a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    rho h (Nat.lcm a b) * rho h (Nat.gcd a b) = rho h a * rho h b := by
  unfold rho
  rw [primeFactors_lcm_eq ha hb, Nat.primeFactors_gcd ha hb]
  exact Finset.prod_union_inter

private lemma rho_le_card_divisors {h d : ℕ} (hd : Squarefree d) :
    rho h d ≤ d.divisors.card := by
  rw [Nat.card_divisors hd.ne_zero]
  unfold rho
  apply Finset.prod_le_prod'
  intro q hq
  have h1 : 1 ≤ d.factorization q :=
    Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp (Nat.support_factorization d ▸ hq))
  split_ifs <;> omega

private lemma rho_lcm_le_mul {h a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    rho h (Nat.lcm a b) ≤ rho h a * rho h b := by
  have h1 := rho_lcm_mul_gcd (h := h) ha hb
  have h2 := rho_pos h (Nat.gcd a b)
  nlinarith

private lemma hFn_one (h : ℕ) : hFn h 1 = 1 := by simp [hFn]

private lemma hFn_prime {h q : ℕ} (hq : q.Prime) :
    hFn h q = ((q : ℝ) - (if q ∣ h then 1 else 2)) / (if q ∣ h then 1 else 2) := by
  simp [hFn, hq.primeFactors]

private lemma hFn_pos {h : ℕ} (hEven : Even h) (d : ℕ) : 0 < hFn h d := by
  unfold hFn
  apply Finset.prod_pos; intro q hq
  have hqp := Nat.prime_of_mem_primeFactors hq
  have h2h : 2 ∣ h := even_iff_two_dvd.mp hEven
  split_ifs with hqh
  · have : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hqp.two_le
    linarith
  · have hq3 : 3 ≤ q := by
      have hne2 : q ≠ 2 := fun h2 => hqh (h2 ▸ h2h)
      have := hqp.two_le; omega
    have : (3 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq3
    linarith

private lemma hFn_mul_coprime {h a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hcop : a.Coprime b) :
    hFn h (a * b) = hFn h a * hFn h b := by
  unfold hFn
  rw [Nat.primeFactors_mul ha hb, Finset.prod_union]
  rw [Finset.disjoint_left]
  intro p hpa hpb
  have hp := Nat.prime_of_mem_primeFactors hpa
  exact hp.not_dvd_one (hcop.gcd_eq_one ▸ Nat.dvd_gcd (Nat.dvd_of_mem_primeFactors hpa)
    (Nat.dvd_of_mem_primeFactors hpb))

private lemma gFn_one (h : ℕ) : gFn h 1 = 1 := by simp [gFn, rho_one]

private lemma gFn_pos {h d : ℕ} (hd : d ≠ 0) : 0 < gFn h d := by
  unfold gFn
  exact div_pos (Nat.cast_pos.mpr (rho_pos h d)) (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hd))

private lemma gFn_lcm_eq {h a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    gFn h (Nat.lcm a b) = gFn h a * gFn h b / gFn h (Nat.gcd a b) := by
  unfold gFn
  have hrho : (rho h (Nat.lcm a b) : ℝ) * (rho h (Nat.gcd a b) : ℝ) =
      (rho h a : ℝ) * (rho h b : ℝ) := by exact_mod_cast rho_lcm_mul_gcd ha hb
  have hmul : (Nat.gcd a b : ℝ) * (Nat.lcm a b : ℝ) = (a : ℝ) * (b : ℝ) := by
    exact_mod_cast Nat.gcd_mul_lcm a b
  have haR : (a : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr ha
  have hbR : (b : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hb
  have hgR : (Nat.gcd a b : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.gcd_ne_zero_left ha)
  have hlR : (Nat.lcm a b : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.lcm_ne_zero ha hb)
  have hrg : (rho h (Nat.gcd a b) : ℝ) ≠ 0 := (Nat.cast_pos.mpr (rho_pos h _)).ne'
  field_simp
  linear_combination (a : ℝ) * (b : ℝ) * hrho - (rho h a : ℝ) * (rho h b : ℝ) * hmul

private lemma inv_gFn_eq_sum_hFn {h d : ℕ} (hd : Squarefree d) :
    1 / gFn h d = ∑ r ∈ d.divisors, hFn h r := by
  rw [sum_divisors_of_squarefree hd (hFn h) (hFn_one h)
    (fun _ _ ha hb hc => hFn_mul_coprime ha hb hc)]
  conv_lhs => unfold gFn rho
  rw [one_div, inv_div]
  have hd_prod : (d : ℝ) = ∏ q ∈ d.primeFactors, (q : ℝ) := by
    rw [← Nat.cast_prod]; exact_mod_cast (Nat.prod_primeFactors_of_squarefree hd).symm
  rw [hd_prod, Nat.cast_prod, ← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl; intro q hq
  have hqp := Nat.prime_of_mem_primeFactors hq
  rw [hFn_prime hqp]
  split_ifs
  · simp
  · simp; ring

private lemma inv_gFn_hFn_eq_sum_inv_hFn {h : ℕ} (hEven : Even h) {d : ℕ} (hd : Squarefree d) :
    1 / (gFn h d * hFn h d) = ∑ k ∈ d.divisors, 1 / hFn h k := by
  have hmul : ∀ a b, a ≠ 0 → b ≠ 0 → a.Coprime b →
      1 / hFn h (a * b) = (1 / hFn h a) * (1 / hFn h b) := by
    intro a b ha hb hc; rw [hFn_mul_coprime ha hb hc]; ring
  rw [sum_divisors_of_squarefree hd (fun k => 1 / hFn h k) (by simp [hFn_one]) hmul]
  conv_lhs => unfold gFn rho hFn
  have hd_prod : (d : ℝ) = ∏ q ∈ d.primeFactors, (q : ℝ) := by
    rw [← Nat.cast_prod]; exact_mod_cast (Nat.prod_primeFactors_of_squarefree hd).symm
  rw [hd_prod, Nat.cast_prod, ← Finset.prod_div_distrib, ← Finset.prod_mul_distrib,
      one_div, ← Finset.prod_inv_distrib]
  apply Finset.prod_congr rfl; intro q hq
  have hqp := Nat.prime_of_mem_primeFactors hq
  rw [hFn_prime hqp]
  have h2h : 2 ∣ h := even_iff_two_dvd.mp hEven
  split_ifs with hqh
  · have hq1 : (q : ℝ) - 1 ≠ 0 := by
      have : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hqp.two_le
      linarith
    have hq0 : (q : ℝ) ≠ 0 := (Nat.cast_pos.mpr hqp.pos).ne'
    field_simp; ring
  · have hq3 : 3 ≤ q := by
      have hne2 : q ≠ 2 := fun h2 => hqh (h2 ▸ h2h)
      have := hqp.two_le; omega
    have hq2 : (q : ℝ) - 2 ≠ 0 := by
      have : (3 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq3
      linarith
    have hq0 : (q : ℝ) ≠ 0 := (Nat.cast_pos.mpr hqp.pos).ne'
    field_simp; ring

private lemma zmod_card_quad_solutions_prod (h : ℕ) (S : Finset ℕ) (hS : ∀ q ∈ S, q.Prime) :
    ∀ (D : ℕ) [NeZero D], ∏ q ∈ S, q = D →
      (Finset.univ.filter (fun a : ZMod D => a * (a + (h : ZMod D)) = 0)).card =
        ∏ q ∈ S, if q ∣ h then 1 else 2 := by
  induction S using Finset.induction_on with
  | empty =>
    intro D _ hD
    rw [Finset.prod_empty] at hD ⊢
    subst hD
    have huniv : Finset.univ.filter (fun a : ZMod 1 => a * (a + (h : ZMod 1)) = 0) = {0} := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact ⟨fun _ => Subsingleton.elim a 0, fun _ => Subsingleton.elim _ _⟩
    rw [huniv, Finset.card_singleton]
  | insert p s hps ih =>
    intro D _ hD
    have hp : p.Prime := hS p (Finset.mem_insert_self p s)
    have hs : ∀ q ∈ s, q.Prime := fun q hq => hS q (Finset.mem_insert_of_mem hq)
    set m := ∏ q ∈ s, q
    have hm_pos : 0 < m := Finset.prod_pos fun q hq => (hs q hq).pos
    have : NeZero p := ⟨hp.ne_zero⟩
    have : NeZero m := ⟨hm_pos.ne'⟩
    have hcop : p.Coprime m := by
      refine (hp.coprime_iff_not_dvd).mpr fun hdvd => ?_
      rcases (hp.prime.dvd_finsetProd_iff _).mp hdvd with ⟨q, hqs, hpq⟩
      exact hps ((Nat.prime_dvd_prime_iff_eq hp (hs q hqs)).mp hpq ▸ hqs)
    rw [Finset.prod_insert hps] at hD ⊢
    subst hD
    let e := ZMod.chineseRemainder hcop
    have hmul_card : (Finset.univ.filter (fun a : ZMod (p * m) => a * (a + (h : ZMod (p * m))) = 0)).card =
        (Finset.univ.filter (fun a : ZMod p => a * (a + (h : ZMod p)) = 0)).card *
        (Finset.univ.filter (fun b : ZMod m => b * (b + (h : ZMod m)) = 0)).card := by
      rw [← Finset.card_product]
      apply Finset.card_bij (fun a _ => e a)
      · intro a ha
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product] at ha ⊢
        have hmap : e (a * (a + (h : ZMod (p * m)))) = 0 := by rw [ha, map_zero]
        rw [map_mul, map_add, map_natCast] at hmap
        exact ⟨congrArg Prod.fst hmap, congrArg Prod.snd hmap⟩
      · intro a1 _ a2 _ h1; exact e.injective h1
      · intro x hx
        simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at hx
        refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        apply e.injective
        rw [map_mul, map_add, map_natCast, map_zero, e.apply_symm_apply]
        exact Prod.ext hx.1 hx.2
    rw [hmul_card, ih hs m rfl]
    congr 1
    have : Fact p.Prime := ⟨hp⟩
    by_cases hph : p ∣ h
    · rw [if_pos hph]
      have hh0 : (h : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff h p).mpr hph
      have hset : Finset.univ.filter (fun a : ZMod p => a * (a + (h : ZMod p)) = 0) = {0} := by
        ext a; simp [hh0]
      rw [hset, Finset.card_singleton]
    · rw [if_neg hph]
      have hhne : (h : ZMod p) ≠ 0 := mt (ZMod.natCast_eq_zero_iff h p).mp hph
      have hne : (0 : ZMod p) ≠ -(h : ZMod p) := fun h0 => hhne (neg_eq_zero.mp h0.symm)
      have hset : Finset.univ.filter (fun a : ZMod p => a * (a + (h : ZMod p)) = 0) =
          {0, -(h : ZMod p)} := by
        ext a
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          Finset.mem_singleton, mul_eq_zero, add_eq_zero_iff_eq_neg]
      rw [hset, Finset.card_pair hne]

private lemma zmod_card_quad_solutions {h D : ℕ} (hD : Squarefree D) [NeZero D] :
    (Finset.univ.filter (fun a : ZMod D => a * (a + (h : ZMod D)) = 0)).card = rho h D :=
  zmod_card_quad_solutions_prod h D.primeFactors
    (fun _q hq => Nat.prime_of_mem_primeFactors hq) D (Nat.prod_primeFactors_of_squarefree hD)

private lemma crt_decomp_solutions (h D x : ℕ) [NeZero D] :
    ((Finset.Icc 1 x).filter (fun n : ℕ => D ∣ n * (n + h))).card =
      ∑ r ∈ Finset.univ.filter (fun a : ZMod D => a * (a + (h : ZMod D)) = 0),
        ((Finset.Icc 1 x).filter (fun n : ℕ => (n : ZMod D) = r)).card := by
  set R : Finset (ZMod D) := Finset.univ.filter (fun a : ZMod D => a * (a + (h : ZMod D)) = 0)
  have hdisj : (R : Set (ZMod D)).PairwiseDisjoint
      (fun r => (Finset.Icc 1 x).filter (fun n : ℕ => (n : ZMod D) = r)) := by
    intro r1 _ r2 _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro n h1 h2
    simp only [Finset.mem_filter] at h1 h2
    exact hne (h1.2.symm.trans h2.2)
  rw [← Finset.card_biUnion hdisj]
  congr 1
  ext n
  simp only [Finset.mem_filter, Finset.mem_biUnion, R, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hn, hdvd⟩
    refine ⟨(n : ZMod D), ?_, hn, rfl⟩
    have h0 : ((n * (n + h) : ℕ) : ZMod D) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
    simpa [Nat.cast_mul, Nat.cast_add] using h0
  · rintro ⟨r, hr, hn, rfl⟩
    refine ⟨hn, (ZMod.natCast_eq_zero_iff _ _).mp ?_⟩
    simpa [Nat.cast_mul, Nat.cast_add] using hr

private lemma crt_count_solutions_bounds (h D x : ℕ) (hD : Squarefree D) :
    (x : ℝ) * gFn h D - (rho h D : ℝ) ≤
      (((Finset.Icc 1 x).filter (fun n : ℕ => D ∣ n * (n + h))).card : ℝ) ∧
    (((Finset.Icc 1 x).filter (fun n : ℕ => D ∣ n * (n + h))).card : ℝ) ≤
      (x : ℝ) * gFn h D + (rho h D : ℝ) := by
  have hD_pos : 0 < D := Nat.pos_of_ne_zero hD.ne_zero
  have : NeZero D := ⟨hD.ne_zero⟩
  set R : Finset (ZMod D) := Finset.univ.filter (fun a : ZMod D => a * (a + (h : ZMod D)) = 0)
  have hR_card : R.card = rho h D := zmod_card_quad_solutions hD
  have hdecomp := crt_decomp_solutions h D x
  constructor
  · -- Lower bound
    have hfib_low : ∀ r : ZMod D,
        x / D ≤ ((Finset.Icc 1 x).filter (fun n : ℕ => (n : ZMod D) = r)).card := by
      intro r
      let b0 : ℕ := if r.val = 0 then D else r.val
      have hb0_pos : 1 ≤ b0 := by
        dsimp only [b0]; split_ifs with h0; exact hD_pos; omega
      have hb0_le : b0 ≤ D := by
        dsimp only [b0]; split_ifs with h0; exact le_rfl; exact le_of_lt (ZMod.val_lt r)
      have hb0_cast : (b0 : ZMod D) = r := by
        dsimp only [b0]; split_ifs with h0
        · rw [ZMod.natCast_self]; exact ((ZMod.val_eq_zero r).mp h0).symm
        · exact ZMod.natCast_zmod_val r
      let g : ℕ → ℕ := fun q => q * D + b0
      have hinj : Set.InjOn g (Finset.range (x / D) : Set ℕ) := by
        intro q1 _ q2 _ heq; dsimp only [g] at heq
        exact Nat.eq_of_mul_eq_mul_right hD_pos (by omega)
      have hsub : (Finset.range (x / D)).image g ⊆ (Finset.Icc 1 x).filter (fun n : ℕ => (n : ZMod D) = r) := by
        intro n hn
        rcases Finset.mem_image.mp hn with ⟨q, hq, rfl⟩
        rw [Finset.mem_range] at hq
        simp only [Finset.mem_filter, Finset.mem_Icc, g]
        refine ⟨⟨by omega, ?_⟩, ?_⟩
        · have : (q + 1) * D ≤ (x / D) * D := Nat.mul_le_mul_right D hq
          have := Nat.div_mul_le_self x D
          nlinarith
        · rw [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, mul_zero, zero_add, hb0_cast]
      calc x / D = (Finset.range (x / D)).card := (Finset.card_range _).symm
        _ = ((Finset.range (x / D)).image g).card := (Finset.card_image_of_injOn hinj).symm
        _ ≤ ((Finset.Icc 1 x).filter (fun n : ℕ => (n : ZMod D) = r)).card := Finset.card_le_card hsub
    have hnat_ge : rho h D * (x / D) ≤ ((Finset.Icc 1 x).filter (fun n : ℕ => D ∣ n * (n + h))).card := by
      rw [hdecomp]
      calc rho h D * (x / D) = R.card * (x / D) := by rw [hR_card]
        _ = ∑ _r ∈ R, (x / D) := by rw [Finset.sum_const, smul_eq_mul]
        _ ≤ ∑ r ∈ R, ((Finset.Icc 1 x).filter (fun n : ℕ => (n : ZMod D) = r)).card :=
            Finset.sum_le_sum fun r _ => hfib_low r
    have hcast : (rho h D : ℝ) * ((x / D : ℕ) : ℝ) ≤
        (((Finset.Icc 1 x).filter (fun n : ℕ => D ∣ n * (n + h))).card : ℝ) := by exact_mod_cast hnat_ge
    have hfl : (x : ℝ) / (D : ℝ) - 1 ≤ ((x / D : ℕ) : ℝ) := by
      have h1 : x < (x / D + 1) * D := by
        have := Nat.div_add_mod x D; have := Nat.mod_lt x hD_pos; nlinarith
      have h1R : (x : ℝ) < (((x / D : ℕ) : ℝ) + 1) * (D : ℝ) := by exact_mod_cast h1
      rw [sub_le_iff_le_add, div_le_iff₀ (Nat.cast_pos.mpr hD_pos)]; linarith
    have hmul := mul_le_mul_of_nonneg_left hfl (Nat.cast_nonneg (rho h D))
    have hrew : (rho h D : ℝ) * ((x : ℝ) / (D : ℝ) - 1) = (x : ℝ) * gFn h D - (rho h D : ℝ) := by
      unfold gFn; ring
    linarith
  · -- Upper bound
    have hfib_upp : ∀ r : ZMod D,
        ((Finset.Icc 1 x).filter (fun n : ℕ => (n : ZMod D) = r)).card ≤ x / D + 1 := by
      intro r
      set F : Finset ℕ := (Finset.Icc 1 x).filter (fun n : ℕ => (n : ZMod D) = r)
      have hinj : Set.InjOn (fun n => (n - 1) / D) (F : Set ℕ) := by
        intro a ha b hb hq
        dsimp only at hq
        simp only [Finset.mem_coe, F, Finset.mem_filter, Finset.mem_Icc] at ha hb
        have h1 : (a - 1) % D = (b - 1) % D := by
          have ha1 : a = (a - 1) + 1 := (Nat.sub_add_cancel ha.1.1).symm
          have hb1 : b = (b - 1) + 1 := (Nat.sub_add_cancel hb.1.1).symm
          have hca : ((a - 1 : ℕ) : ZMod D) = ((b - 1 : ℕ) : ZMod D) := by
            have : ((a - 1 : ℕ) : ZMod D) + 1 = ((b - 1 : ℕ) : ZMod D) + 1 := by
              have := ha.2.trans hb.2.symm
              rw [ha1, hb1] at this; simpa [Nat.cast_add] using this
            exact add_right_cancel this
          exact (ZMod.natCast_eq_natCast_iff' (a - 1) (b - 1) D).mp hca
        have e1 := Nat.div_add_mod (a - 1) D
        have e2 := Nat.div_add_mod (b - 1) D
        have hmul : D * ((a - 1) / D) = D * ((b - 1) / D) := congrArg (D * ·) hq
        have ha1 : 1 ≤ a := ha.1.1
        have hb1 : 1 ≤ b := hb.1.1
        omega
      have hsub : F.image (fun n => (n - 1) / D) ⊆ Finset.range (x / D + 1) := by
        intro k hk
        rcases Finset.mem_image.mp hk with ⟨n, hn, rfl⟩
        simp only [F, Finset.mem_filter, Finset.mem_Icc] at hn
        rw [Finset.mem_range]
        exact Nat.lt_succ_of_le (Nat.div_le_div_right (by omega))
      calc F.card = (F.image (fun n => (n - 1) / D)).card := (Finset.card_image_of_injOn hinj).symm
        _ ≤ (Finset.range (x / D + 1)).card := Finset.card_le_card hsub
        _ = x / D + 1 := Finset.card_range _
    have hnat_le : ((Finset.Icc 1 x).filter (fun n : ℕ => D ∣ n * (n + h))).card ≤
        rho h D * (x / D + 1) := by
      rw [hdecomp]
      calc ∑ r ∈ R, ((Finset.Icc 1 x).filter (fun n : ℕ => (n : ZMod D) = r)).card
        _ ≤ ∑ _r ∈ R, (x / D + 1) := Finset.sum_le_sum fun r _ => hfib_upp r
        _ = R.card * (x / D + 1) := by rw [Finset.sum_const, smul_eq_mul]
        _ = rho h D * (x / D + 1) := by rw [hR_card]
    have hcast : (((Finset.Icc 1 x).filter (fun n : ℕ => D ∣ n * (n + h))).card : ℝ) ≤
        (rho h D : ℝ) * (((x / D : ℕ) : ℝ) + 1) := by exact_mod_cast hnat_le
    have hdiv : ((x / D : ℕ) : ℝ) ≤ (x : ℝ) / (D : ℝ) := by
      rw [le_div_iff₀ (Nat.cast_pos.mpr hD_pos)]
      exact_mod_cast Nat.div_mul_le_self x D
    calc (((Finset.Icc 1 x).filter (fun n : ℕ => D ∣ n * (n + h))).card : ℝ)
      _ ≤ (rho h D : ℝ) * (((x / D : ℕ) : ℝ) + 1) := hcast
      _ ≤ (rho h D : ℝ) * ((x : ℝ) / (D : ℝ) + 1) :=
          mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
      _ = (x : ℝ) * gFn h D + (rho h D : ℝ) := by unfold gFn; ring

private lemma geom_sum_inv_le (q : ℝ) (hq : 1 < q) (Y : ℕ) :
    ∑ e ∈ Finset.range (Y + 1), (1 / q) ^ e ≤ q / (q - 1) := by
  have hq0 : 0 < q := by linarith
  have h1q : (1 / q) ≠ 1 := by
    intro h; rw [div_eq_one_iff_eq hq0.ne'] at h; linarith
  rw [geom_sum_eq h1q]
  have hpos : 0 < 1 - 1 / q := by rw [sub_pos, div_lt_one hq0]; exact hq
  have hneg : 1 / q - 1 ≠ 0 := by linarith
  have hpow : 0 ≤ (1 / q) ^ (Y + 1) := by positivity
  have hrew : ((1 / q) ^ (Y + 1) - 1) / (1 / q - 1) = (1 - (1 / q) ^ (Y + 1)) / (1 - 1 / q) := by
    rw [div_eq_div_iff hneg hpos.ne']; ring
  rw [hrew]
  calc (1 - (1 / q) ^ (Y + 1)) / (1 - 1 / q)
    _ ≤ 1 / (1 - 1 / q) := div_le_div_of_nonneg_right (by linarith) hpos.le
    _ = q / (q - 1) := by
        rw [div_eq_div_iff hpos.ne' (by linarith : q - 1 ≠ 0)]; field_simp

private lemma arith_geom_sum_le (q : ℝ) (hq : 2 < q) (z : ℕ) :
    ∑ e ∈ Finset.Icc 1 z, ((e : ℝ) + 1) / q ^ e ≤ (2 * q - 1) / (q - 1) ^ 2 := by
  have hq0 : 0 < q := by linarith
  have hq1 : 0 < q - 1 := by linarith
  have hexact : ∀ m : ℕ, ∑ e ∈ Finset.Icc 1 m, ((e : ℝ) + 1) / q ^ e =
      (2 * q - 1) / (q - 1) ^ 2 -
        (((m : ℝ) + 2) * q - ((m : ℝ) + 1)) / (q ^ m * (q - 1) ^ 2) := by
    intro m
    induction m with
    | zero =>
      simp only [show Finset.Icc 1 0 = ∅ by decide, Finset.sum_empty, Nat.cast_zero, pow_zero,
        one_mul]
      ring
    | succ k ih =>
      have hIcc : Finset.Icc 1 (k + 1) = insert (k + 1) (Finset.Icc 1 k) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      have hnot : k + 1 ∉ Finset.Icc 1 k := by simp
      rw [hIcc, Finset.sum_insert hnot, ih]
      have hqk : q ^ k ≠ 0 := (pow_pos hq0 k).ne'
      have hqk1 : q ^ (k + 1) = q ^ k * q := pow_succ q k
      have hq12 : (q - 1) ^ 2 ≠ 0 := (sq_pos_of_pos hq1).ne'
      rw [hqk1]; push_cast
      field_simp
      ring
  rw [hexact z]
  have hrem_nn : 0 ≤ (((z : ℝ) + 2) * q - ((z : ℝ) + 1)) / (q ^ z * (q - 1) ^ 2) := by
    apply div_nonneg
    · nlinarith [Nat.cast_nonneg (α := ℝ) z]
    · positivity
  linarith

private lemma selberg_G_step1 (h Y : ℕ) (hh : 0 < h) (hY : 2 ≤ Y) :
    Real.log (Y : ℝ) ≤
      (∑ k ∈ (Finset.Icc 1 Y).filter (fun k => k.Coprime h), (1 : ℝ) / (k : ℝ)) *
        ((h : ℝ) / (h.totient : ℝ)) := by
  set Ch := (Finset.Icc 1 Y).filter (fun k => k.Coprime h)
  set Sh := ∑ k ∈ Ch, (1 : ℝ) / (k : ℝ)
  set Uh := (Finset.Icc 1 Y).filter (fun u => u.primeFactors ⊆ h.primeFactors)
  have hharm : Real.log (Y : ℝ) ≤ ∑ m ∈ Finset.Icc 1 Y, (1 : ℝ) / (m : ℝ) :=
    harmonic_lower_bound Y (by omega)
  have hfac_prod : ∑ m ∈ Finset.Icc 1 Y, (1 : ℝ) / (m : ℝ) ≤
      Sh * ∑ u ∈ Uh, (1 : ℝ) / (u : ℝ) := by
    let splitU : ℕ → ℕ := fun m =>
      ∏ q ∈ m.primeFactors ∩ h.primeFactors, q ^ (m.factorization q)
    let splitK : ℕ → ℕ := fun m =>
      ∏ q ∈ m.primeFactors \ h.primeFactors, q ^ (m.factorization q)
    have hsplit_eq : ∀ m ∈ Finset.Icc 1 Y, splitK m * splitU m = m := by
      intro m hm
      have hm0 : m ≠ 0 := by rw [Finset.mem_Icc] at hm; omega
      have hdisj : Disjoint (m.primeFactors \ h.primeFactors) (m.primeFactors ∩ h.primeFactors) :=
        Finset.sdiff_disjoint.mono_right Finset.inter_subset_right
      have hunion : (m.primeFactors \ h.primeFactors) ∪ (m.primeFactors ∩ h.primeFactors) =
          m.primeFactors := Finset.sdiff_union_inter _ _
      simp only [splitK, splitU, ← Finset.prod_union hdisj, hunion]
      exact (eq_prod_primeFactors_pow hm0).symm
    have hmem : ∀ m ∈ Finset.Icc 1 Y, (splitK m, splitU m) ∈ Ch ×ˢ Uh := by
      intro m hm
      have hmY : m ≤ Y := (Finset.mem_Icc.mp hm).2
      have hku := hsplit_eq m hm
      have hk_pos : 1 ≤ splitK m := Finset.prod_pos fun q hq =>
        pow_pos (Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.mp hq).1).pos _
      have hu_pos : 1 ≤ splitU m := Finset.prod_pos fun q hq =>
        pow_pos (Nat.prime_of_mem_primeFactors (Finset.mem_inter.mp hq).1).pos _
      have hk_le : splitK m ≤ Y := by
        have : splitK m ≤ splitK m * splitU m := Nat.le_mul_of_pos_right _ hu_pos
        omega
      have hu_le : splitU m ≤ Y := by
        have : splitU m ≤ splitK m * splitU m := Nat.le_mul_of_pos_left _ hk_pos
        omega
      have hk_cop : (splitK m).Coprime h := by
        rw [Nat.coprime_iff_gcd_eq_one]
        by_contra hne
        obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hne
        have hpk : p ∣ splitK m := dvd_trans hpdvd (Nat.gcd_dvd_left _ _)
        have hph : p ∣ h := dvd_trans hpdvd (Nat.gcd_dvd_right _ _)
        rcases (hp.prime.dvd_finsetProd_iff _).mp hpk with ⟨q, hq, hpq⟩
        have hqp := Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.mp hq).1
        have hp_eq_q : p = q :=
          (Nat.prime_dvd_prime_iff_eq hp hqp).mp (hp.dvd_of_dvd_pow hpq)
        exact (Finset.mem_sdiff.mp hq).2 (hp_eq_q ▸ Nat.mem_primeFactors.mpr ⟨hp, hph, hh.ne'⟩)
      have hu_pf : (splitU m).primeFactors ⊆ h.primeFactors := by
        intro p hp
        have hpp := Nat.prime_of_mem_primeFactors hp
        have hpdvd := Nat.dvd_of_mem_primeFactors hp
        rcases (hpp.prime.dvd_finsetProd_iff _).mp hpdvd with ⟨q, hq, hpq⟩
        have hqp := Nat.prime_of_mem_primeFactors (Finset.mem_inter.mp hq).1
        have hp_eq_q : p = q :=
          (Nat.prime_dvd_prime_iff_eq hpp hqp).mp (hpp.dvd_of_dvd_pow hpq)
        exact hp_eq_q ▸ (Finset.mem_inter.mp hq).2
      simp only [Finset.mem_product, Ch, Uh, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨⟨hk_pos, hk_le⟩, hk_cop⟩, ⟨⟨hu_pos, hu_le⟩, hu_pf⟩⟩
    have hinj : ∀ m1 ∈ Finset.Icc 1 Y, ∀ m2 ∈ Finset.Icc 1 Y,
        (splitK m1, splitU m1) = (splitK m2, splitU m2) → m1 = m2 := by
      intro m1 hm1 m2 hm2 heq
      rw [Prod.mk.injEq] at heq
      rw [← hsplit_eq m1 hm1, ← hsplit_eq m2 hm2, heq.1, heq.2]
    let Fp : ℕ × ℕ → ℝ := fun p => (1 : ℝ) / ((p.1 : ℝ) * (p.2 : ℝ))
    have hprod_sum : Sh * ∑ u ∈ Uh, (1 : ℝ) / (u : ℝ) = ∑ p ∈ Ch ×ˢ Uh, Fp p := by
      rw [Finset.sum_product]
      simp only [Sh, Fp]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl; intro k _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro u _; ring
    rw [hprod_sum]
    calc ∑ m ∈ Finset.Icc 1 Y, (1 : ℝ) / (m : ℝ)
      _ = ∑ m ∈ Finset.Icc 1 Y, Fp (splitK m, splitU m) := by
          apply Finset.sum_congr rfl; intro m hm
          dsimp only [Fp]
          conv_lhs => rw [← hsplit_eq m hm]
          push_cast; rfl
      _ = ∑ p ∈ (Finset.Icc 1 Y).image (fun m => (splitK m, splitU m)), Fp p :=
          (Finset.sum_image (f := Fp) hinj).symm
      _ ≤ ∑ p ∈ Ch ×ˢ Uh, Fp p := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro p hp
            rcases Finset.mem_image.mp hp with ⟨m, hm, rfl⟩
            exact hmem m hm
          · intro _ _ _; dsimp only [Fp]; positivity
  have hUh_le : ∑ u ∈ Uh, (1 : ℝ) / (u : ℝ) ≤ (h : ℝ) / (h.totient : ℝ) := by
    rw [div_totient_eq_prod hh.ne']
    let P := h.primeFactors
    let E := P.pi (fun _ => Finset.range (Y + 1))
    let enc : ℕ → ∀ q ∈ P, ℕ := fun u q _ => u.factorization q
    have hu_eq : ∀ u ∈ Uh, u = ∏ q ∈ P, q ^ (u.factorization q) := by
      intro u hu
      simp only [Uh, Finset.mem_filter, Finset.mem_Icc] at hu
      conv_lhs => rw [eq_prod_primeFactors_pow (by omega : u ≠ 0)]
      apply Finset.prod_subset hu.2
      intro q _ hqu
      have : u.factorization q = 0 :=
        Finsupp.notMem_support_iff.mp (Nat.support_factorization u ▸ hqu)
      simp [this]
    have henc_mem : ∀ u ∈ Uh, enc u ∈ E := by
      intro u hu
      simp only [Uh, Finset.mem_filter, Finset.mem_Icc] at hu
      rw [Finset.mem_pi]; intro q hq; rw [Finset.mem_range]
      have hqp := Nat.prime_of_mem_primeFactors hq
      have hpow_le : q ^ (u.factorization q) ≤ u :=
        Nat.le_of_dvd (by omega) (Nat.ordProj_dvd u q)
      have hlt : u.factorization q < 2 ^ (u.factorization q) :=
        Nat.lt_two_pow_self (n := u.factorization q)
      have h2q : 2 ^ (u.factorization q) ≤ q ^ (u.factorization q) :=
        Nat.pow_le_pow_left hqp.two_le _
      have huY : u ≤ Y := hu.1.2
      dsimp only [enc]
      omega
    have henc_val : ∀ u ∈ Uh,
        (1 : ℝ) / (u : ℝ) = ∏ q ∈ P.attach, (1 / (q.1 : ℝ)) ^ (enc u q.1 q.2) := by
      intro u hu
      have hprodR : (u : ℝ) = ∏ q ∈ P.attach, (q.1 : ℝ) ^ (enc u q.1 q.2) := by
        dsimp only [enc]
        rw [Finset.prod_attach P (fun q => (q : ℝ) ^ (u.factorization q))]
        simp_rw [← Nat.cast_pow]; rw [← Nat.cast_prod]
        exact_mod_cast hu_eq u hu
      rw [hprodR, one_div, ← Finset.prod_inv_distrib]
      apply Finset.prod_congr rfl; intro q _
      rw [one_div, inv_pow]
    have henc_inj : ∀ u1 ∈ Uh, ∀ u2 ∈ Uh, enc u1 = enc u2 → u1 = u2 := by
      intro u1 hu1 u2 hu2 heq
      rw [hu_eq u1 hu1, hu_eq u2 hu2]
      apply Finset.prod_congr rfl; intro q hq
      have := congrFun (congrFun heq q) hq
      simp only [enc] at this
      rw [this]
    let Fe : (∀ q ∈ P, ℕ) → ℝ := fun f => ∏ q ∈ P.attach, (1 / (q.1 : ℝ)) ^ (f q.1 q.2)
    calc ∑ u ∈ Uh, (1 : ℝ) / (u : ℝ)
      _ = ∑ u ∈ Uh, Fe (enc u) := Finset.sum_congr rfl henc_val
      _ = ∑ f ∈ Uh.image enc, Fe f := (Finset.sum_image (f := Fe) henc_inj).symm
      _ ≤ ∑ f ∈ E, Fe f := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro f hf
            rcases Finset.mem_image.mp hf with ⟨u, hu, rfl⟩
            exact henc_mem u hu
          · intro _ _ _; dsimp only [Fe]; exact Finset.prod_nonneg (fun _ _ => by positivity)
      _ = ∏ q ∈ P, ∑ e ∈ Finset.range (Y + 1), (1 / (q : ℝ)) ^ e := by
          rw [Finset.prod_sum]
      _ ≤ ∏ q ∈ P, (q : ℝ) / ((q : ℝ) - 1) := by
          apply Finset.prod_le_prod
          · intro _ _; exact Finset.sum_nonneg (fun _ _ => by positivity)
          · intro q hq
            have hq1 : (1 : ℝ) < (q : ℝ) := by
              exact_mod_cast (Nat.prime_of_mem_primeFactors hq).one_lt
            exact geom_sum_inv_le (q : ℝ) hq1 Y
  have hSh_nn : 0 ≤ Sh := Finset.sum_nonneg (fun _ _ => by positivity)
  exact le_trans hharm (le_trans hfac_prod (mul_le_mul_of_nonneg_left hUh_le hSh_nn))

private lemma selberg_G_step2 (h z : ℕ) (hEven : Even h) :
    (∑ k ∈ (Finset.Icc 1 (Nat.sqrt z)).filter (fun k => k.Coprime h), (1 : ℝ) / (k : ℝ)) ^ 2 ≤
      ∑ r ∈ SqFree z, 1 / hFn h r := by
  set Y := Nat.sqrt z
  have hY2_le : Y * Y ≤ z := Nat.sqrt_le z
  set Ch := (Finset.Icc 1 Y).filter (fun k => k.Coprime h)
  set Sh := ∑ k ∈ Ch, (1 : ℝ) / (k : ℝ)
  set Cz := (Finset.Icc 1 z).filter (fun n => n.Coprime h)
  have hSh2_le : Sh ^ 2 ≤ ∑ n ∈ Cz, (n.divisors.card : ℝ) / (n : ℝ) := by
    have hprod_eq : Sh ^ 2 = ∑ p ∈ Ch ×ˢ Ch, (1 : ℝ) / ((p.1 * p.2 : ℕ) : ℝ) := by
      rw [sq, Finset.sum_product]
      simp only [Sh]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl; intro a _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro b _; push_cast; ring
    rw [hprod_eq]
    have hmaps : ∀ p ∈ Ch ×ˢ Ch, p.1 * p.2 ∈ Cz := by
      intro p hp
      simp only [Finset.mem_product, Ch, Cz, Finset.mem_filter, Finset.mem_Icc] at hp ⊢
      exact ⟨⟨Nat.mul_pos hp.1.1.1 hp.2.1.1, le_trans (Nat.mul_le_mul hp.1.1.2 hp.2.1.2) hY2_le⟩,
        hp.1.2.mul_left hp.2.2⟩
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    apply Finset.sum_le_sum; intro n hn
    have hcongr : ∑ p ∈ (Ch ×ˢ Ch).filter (fun p => p.1 * p.2 = n),
        (1 : ℝ) / ((p.1 * p.2 : ℕ) : ℝ) =
        (((Ch ×ˢ Ch).filter (fun p => p.1 * p.2 = n)).card : ℝ) / (n : ℝ) := by
      rw [Finset.sum_congr rfl (fun p hp => by rw [(Finset.mem_filter.mp hp).2])]
      rw [Finset.sum_const, nsmul_eq_mul, mul_one_div]
    rw [hcongr]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
    have hcard : ((Ch ×ˢ Ch).filter (fun p => p.1 * p.2 = n)).card ≤ n.divisors.card := by
      have hinj : Set.InjOn Prod.fst
          (((Ch ×ˢ Ch).filter (fun p => p.1 * p.2 = n) : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) := by
        intro p1 hp1 p2 hp2 hfst
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Ch, Finset.mem_Icc] at hp1 hp2
        ext
        · exact hfst
        · have hmul : p1.1 * p1.2 = p1.1 * p2.2 := by rw [hp1.2, hfst, hp2.2]
          exact Nat.eq_of_mul_eq_mul_left hp1.1.1.1.1 hmul
      have hsub : ((Ch ×ˢ Ch).filter (fun p => p.1 * p.2 = n)).image Prod.fst ⊆ n.divisors := by
        intro d hd
        rcases Finset.mem_image.mp hd with ⟨p, hp, rfl⟩
        simp only [Finset.mem_filter] at hp
        simp only [Cz, Finset.mem_filter, Finset.mem_Icc] at hn
        exact Nat.mem_divisors.mpr ⟨⟨p.2, hp.2.symm⟩, by omega⟩
      calc ((Ch ×ˢ Ch).filter (fun p => p.1 * p.2 = n)).card
        _ = (((Ch ×ˢ Ch).filter (fun p => p.1 * p.2 = n)).image Prod.fst).card :=
            (Finset.card_image_of_injOn hinj).symm
        _ ≤ n.divisors.card := Finset.card_le_card hsub
    exact_mod_cast hcard
  let rad : ℕ → ℕ := fun n => ∏ q ∈ n.primeFactors, q
  set SqCop := (SqFree z).filter (fun r => r.Coprime h)
  have hrad_maps : ∀ n ∈ Cz, rad n ∈ SqCop := by
    intro n hn
    simp only [Cz, SqCop, SqFree, Finset.mem_filter, Finset.mem_Icc] at hn ⊢
    have hrad_pos : 1 ≤ rad n := Finset.prod_pos fun q hq => (Nat.prime_of_mem_primeFactors hq).pos
    have hrad_dvd : rad n ∣ n := rad_dvd_self (by omega)
    have hrad_le : rad n ≤ z := le_trans (Nat.le_of_dvd (by omega) hrad_dvd) hn.1.2
    exact ⟨⟨⟨hrad_pos, hrad_le⟩, rad_squarefree n⟩, hn.2.coprime_dvd_left hrad_dvd⟩
  have hfiber_le : ∀ r ∈ SqCop,
      ∑ n ∈ Cz.filter (fun n => rad n = r), (n.divisors.card : ℝ) / (n : ℝ) ≤ 1 / hFn h r := by
    intro r hr
    simp only [SqCop, SqFree, Finset.mem_filter, Finset.mem_Icc] at hr
    let P := r.primeFactors
    let E := P.pi (fun _ => Finset.Icc 1 z)
    let enc : ℕ → ∀ q ∈ P, ℕ := fun n q _ => n.factorization q
    set F := Cz.filter (fun n => rad n = r)
    have hpf_eq : ∀ n ∈ F, n.primeFactors = P := by
      intro n hn
      simp only [F, Cz, Finset.mem_filter, Finset.mem_Icc] at hn
      have hrad_eq : (∏ q ∈ n.primeFactors, q) = r := hn.2
      rw [← rad_primeFactors_eq n, hrad_eq]
    have henc_mem : ∀ n ∈ F, enc n ∈ E := by
      intro n hn
      have hnF := hn
      simp only [F, Cz, Finset.mem_filter, Finset.mem_Icc] at hnF
      rw [Finset.mem_pi]; intro q hq; rw [Finset.mem_Icc]
      have hqn : q ∈ n.primeFactors := (hpf_eq n hn).symm ▸ hq
      have hqp := Nat.prime_of_mem_primeFactors hqn
      have h1 : 1 ≤ n.factorization q :=
        Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp (Nat.support_factorization n ▸ hqn))
      have hpow : q ^ (n.factorization q) ≤ n :=
        Nat.le_of_dvd (by omega) (Nat.ordProj_dvd n q)
      have hlt : n.factorization q < 2 ^ (n.factorization q) :=
        Nat.lt_two_pow_self (n := n.factorization q)
      have h2q : 2 ^ (n.factorization q) ≤ q ^ (n.factorization q) :=
        Nat.pow_le_pow_left hqp.two_le _
      have hnz : n ≤ z := hnF.1.1.2
      dsimp only [enc]
      exact ⟨h1, by omega⟩
    have henc_inj : ∀ n1 ∈ F, ∀ n2 ∈ F, enc n1 = enc n2 → n1 = n2 := by
      intro n1 hn1 n2 hn2 heq
      have h10 : n1 ≠ 0 := by simp only [F, Cz, Finset.mem_filter, Finset.mem_Icc] at hn1; omega
      have h20 : n2 ≠ 0 := by simp only [F, Cz, Finset.mem_filter, Finset.mem_Icc] at hn2; omega
      rw [eq_prod_primeFactors_pow h10, eq_prod_primeFactors_pow h20, hpf_eq n1 hn1, hpf_eq n2 hn2]
      apply Finset.prod_congr rfl; intro q hq
      have := congrFun (congrFun heq q) hq
      simp only [enc] at this
      rw [this]
    let Fe : (∀ q ∈ P, ℕ) → ℝ := fun f =>
      ∏ q ∈ P.attach, (((f q.1 q.2 : ℝ) + 1) / (q.1 : ℝ) ^ (f q.1 q.2))
    have henc_val : ∀ n ∈ F, (n.divisors.card : ℝ) / (n : ℝ) = Fe (enc n) := by
      intro n hn
      have hn0 : n ≠ 0 := by simp only [F, Cz, Finset.mem_filter, Finset.mem_Icc] at hn; omega
      have hpf := hpf_eq n hn
      dsimp only [Fe, enc]
      have hnum : (n.divisors.card : ℝ) = ∏ q ∈ P.attach, ((n.factorization q.1 : ℝ) + 1) := by
        rw [Finset.prod_attach P (fun q => ((n.factorization q : ℝ) + 1)), Nat.card_divisors hn0, hpf, Nat.cast_prod]
        apply Finset.prod_congr rfl; intro q _; push_cast; rfl
      have hden : (n : ℝ) = ∏ q ∈ P.attach, (q.1 : ℝ) ^ (n.factorization q.1) := by
        rw [Finset.prod_attach P (fun q => (q : ℝ) ^ (n.factorization q))]
        simp_rw [← Nat.cast_pow]; rw [← Nat.cast_prod]
        have hnat := eq_prod_primeFactors_pow hn0
        rw [hpf] at hnat
        exact_mod_cast hnat
      rw [hnum, hden, ← Finset.prod_div_distrib]
    calc ∑ n ∈ F, (n.divisors.card : ℝ) / (n : ℝ)
      _ = ∑ n ∈ F, Fe (enc n) := Finset.sum_congr rfl henc_val
      _ = ∑ f ∈ F.image enc, Fe f := (Finset.sum_image (f := Fe) henc_inj).symm
      _ ≤ ∑ f ∈ E, Fe f := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro f hf
            rcases Finset.mem_image.mp hf with ⟨n, hn, rfl⟩
            exact henc_mem n hn
          · intro _ _ _; dsimp only [Fe]; exact Finset.prod_nonneg (fun _ _ => by positivity)
      _ = ∏ q ∈ P, ∑ e ∈ Finset.Icc 1 z, ((e : ℝ) + 1) / (q : ℝ) ^ e := by
          rw [Finset.prod_sum]
      _ ≤ ∏ q ∈ P, 2 / ((q : ℝ) - 2) := by
          apply Finset.prod_le_prod
          · intro _ _; exact Finset.sum_nonneg (fun _ _ => by positivity)
          · intro q hq
            have hqp := Nat.prime_of_mem_primeFactors hq
            have hq_not_dvd : ¬ q ∣ h := fun hqh =>
              hqp.not_dvd_one (hr.2.gcd_eq_one ▸ Nat.dvd_gcd (Nat.dvd_of_mem_primeFactors hq) hqh)
            have hq3 : 3 ≤ q := by
              have h2h := even_iff_two_dvd.mp hEven
              have hne2 : q ≠ 2 := fun h2 => hq_not_dvd (h2 ▸ h2h)
              have := hqp.two_le; omega
            have hqR : (2 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 2 < q)
            have h1 := arith_geom_sum_le (q : ℝ) hqR z
            have h2 : (2 * (q : ℝ) - 1) / ((q : ℝ) - 1) ^ 2 ≤ 2 / ((q : ℝ) - 2) := by
              rw [div_le_div_iff₀ (sq_pos_of_pos (by linarith)) (by linarith)]
              nlinarith
            linarith
      _ = 1 / hFn h r := by
          unfold hFn
          rw [one_div, ← Finset.prod_inv_distrib]
          apply Finset.prod_congr rfl; intro q hq
          have hqp := Nat.prime_of_mem_primeFactors hq
          have hq_not_dvd : ¬ q ∣ h := fun hqh =>
            hqp.not_dvd_one (hr.2.gcd_eq_one ▸ Nat.dvd_gcd (Nat.dvd_of_mem_primeFactors hq) hqh)
          rw [if_neg hq_not_dvd, inv_div]
  calc Sh ^ 2 ≤ ∑ n ∈ Cz, (n.divisors.card : ℝ) / (n : ℝ) := hSh2_le
    _ = ∑ r ∈ SqCop, ∑ n ∈ Cz.filter (fun n => rad n = r), (n.divisors.card : ℝ) / (n : ℝ) :=
        (Finset.sum_fiberwise_of_maps_to hrad_maps _).symm
    _ ≤ ∑ r ∈ SqCop, 1 / hFn h r := Finset.sum_le_sum hfiber_le
    _ ≤ ∑ r ∈ SqFree z, 1 / hFn h r :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun r _ _ => (div_pos one_pos (hFn_pos hEven r)).le)

private lemma selberg_G_lower_bound (h z : ℕ) (hh : 0 < h) (hEven : Even h) (hz : 4 ≤ z) :
    ((h.totient : ℝ) / (h : ℝ)) ^ 2 * (Real.log ((Nat.sqrt z : ℕ) : ℝ)) ^ 2 ≤
      ∑ r ∈ SqFree z, 1 / hFn h r := by
  set Y := Nat.sqrt z
  have hY2 : 2 ≤ Y := by rw [Nat.le_sqrt]; omega
  set Sh := ∑ k ∈ (Finset.Icc 1 Y).filter (fun k => k.Coprime h), (1 : ℝ) / (k : ℝ)
  have hStep1 := selberg_G_step1 h Y hh hY2
  have hStep2 := selberg_G_step2 h z hEven
  have hht_pos : 0 < (h.totient : ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr hh)
  have hh_pos : 0 < (h : ℝ) := Nat.cast_pos.mpr hh
  have hlogY_nn : 0 ≤ Real.log (Y : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ Y))
  have hSh_ge : ((h.totient : ℝ) / (h : ℝ)) * Real.log (Y : ℝ) ≤ Sh := by
    have hmul := mul_le_mul_of_nonneg_left hStep1 (div_nonneg hht_pos.le hh_pos.le)
    have hcancel : ((h.totient : ℝ) / (h : ℝ)) * (Sh * ((h : ℝ) / (h.totient : ℝ))) = Sh := by
      field_simp
    linarith [hcancel]
  have hsq : (((h.totient : ℝ) / (h : ℝ)) * Real.log (Y : ℝ)) ^ 2 ≤ Sh ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg (div_nonneg hht_pos.le hh_pos.le) hlogY_nn) hSh_ge 2
  calc ((h.totient : ℝ) / (h : ℝ)) ^ 2 * (Real.log (Y : ℝ)) ^ 2
    _ = (((h.totient : ℝ) / (h : ℝ)) * Real.log (Y : ℝ)) ^ 2 := by ring
    _ ≤ Sh ^ 2 := hsq
    _ ≤ ∑ r ∈ SqFree z, 1 / hFn h r := hStep2

private noncomputable def selbergG (h z : ℕ) : ℝ := ∑ r ∈ SqFree z, 1 / hFn h r

private noncomputable def selbergLam (h z d : ℕ) : ℝ :=
  if d ∈ SqFree z then
    (muSq d / (gFn h d * selbergG h z)) * ∑ r ∈ (SqFree z).filter (fun r => d ∣ r), 1 / hFn h r
  else 0

private lemma selbergG_pos {h z : ℕ} (hEven : Even h) (hz : 1 ≤ z) : 0 < selbergG h z := by
  have h1_mem : 1 ∈ SqFree z := by
    simp only [SqFree, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨le_rfl, hz⟩, squarefree_one⟩
  have h1 : 0 < 1 / hFn h 1 := div_pos one_pos (hFn_pos hEven 1)
  have hle : 1 / hFn h 1 ≤ selbergG h z :=
    Finset.single_le_sum (fun r _ => (div_pos one_pos (hFn_pos hEven r)).le) h1_mem
  linarith

private lemma selbergLam_one {h z : ℕ} (hEven : Even h) (hz : 1 ≤ z) : selbergLam h z 1 = 1 := by
  have h1_mem : 1 ∈ SqFree z := by
    simp only [SqFree, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨le_rfl, hz⟩, squarefree_one⟩
  have hG_pos := selbergG_pos hEven hz
  simp only [selbergLam, if_pos h1_mem, muSq_one, gFn_one, one_mul, one_dvd, Finset.filter_true]
  change 1 / selbergG h z * selbergG h z = 1
  exact one_div_mul_cancel hG_pos.ne'

private lemma selbergLam_abs_le_one {h z : ℕ} (hEven : Even h) (hz : 1 ≤ z)
    {d : ℕ} (hd : d ∈ SqFree z) : |selbergLam h z d| ≤ 1 := by
  have hd' := hd
  simp only [SqFree, Finset.mem_filter, Finset.mem_Icc] at hd'
  have hG_pos := selbergG_pos hEven hz
  simp only [selbergLam, if_pos hd]
  have hmu_abs : |muSq d| = 1 := by simp [muSq]
  have hg_pos : 0 < gFn h d := gFn_pos (by omega)
  have hsum_nn : 0 ≤ ∑ r ∈ (SqFree z).filter (fun r => d ∣ r), 1 / hFn h r :=
    Finset.sum_nonneg fun r _ => (div_pos one_pos (hFn_pos hEven r)).le
  rw [abs_mul, abs_div, hmu_abs, abs_of_pos (mul_pos hg_pos hG_pos), abs_of_nonneg hsum_nn]
  have hfactor : ∑ r ∈ (SqFree z).filter (fun r => d ∣ r), 1 / hFn h r =
      (1 / hFn h d) * ∑ m ∈ (SqFree (z / d)).filter (fun m => m.Coprime d), 1 / hFn h m := by
    rw [Finset.mul_sum]
    apply Finset.sum_bij (fun r _ => r / d)
    · intro r hr
      simp only [Finset.mem_filter, SqFree, Finset.mem_Icc] at hr ⊢
      have hdm : d * (r / d) = r := Nat.mul_div_cancel' hr.2
      have hm1 : 1 ≤ r / d := Nat.div_pos (Nat.le_of_dvd (by omega) hr.2) (by omega)
      have hmle : r / d ≤ z / d := Nat.div_le_div_right hr.1.1.2
      have hmsq : Squarefree (r / d) := hr.1.2.squarefree_of_dvd ⟨d, by linarith [hdm]⟩
      have hmcop : (r / d).Coprime d := by
        rw [Nat.coprime_iff_gcd_eq_one]
        by_contra hne
        obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hne
        exact hp.not_isUnit (hr.1.2 p (hdm ▸ Nat.mul_dvd_mul
          (dvd_trans hpdvd (Nat.gcd_dvd_right _ _)) (dvd_trans hpdvd (Nat.gcd_dvd_left _ _))))
      exact ⟨⟨⟨hm1, hmle⟩, hmsq⟩, hmcop⟩
    · intro r1 hr1 r2 hr2 hq
      simp only [Finset.mem_filter] at hr1 hr2
      rw [← Nat.mul_div_cancel' hr1.2, ← Nat.mul_div_cancel' hr2.2, hq]
    · intro m hm
      simp only [Finset.mem_filter, SqFree, Finset.mem_Icc] at hm
      refine ⟨d * m, ?_, Nat.mul_div_cancel_left m (by omega)⟩
      simp only [Finset.mem_filter, SqFree, Finset.mem_Icc]
      have hdm_le : d * m ≤ z :=
        le_trans (Nat.mul_le_mul_left d hm.1.1.2) (Nat.mul_div_le z d)
      have hdm_sq : Squarefree (d * m) :=
        (Nat.squarefree_mul hm.2.symm).mpr ⟨hd'.2, hm.1.2⟩
      exact ⟨⟨⟨Nat.mul_pos (by omega) hm.1.1.1, hdm_le⟩, hdm_sq⟩, dvd_mul_right d m⟩
    · intro r hr
      simp only [Finset.mem_filter, SqFree, Finset.mem_Icc] at hr
      have hdm : d * (r / d) = r := Nat.mul_div_cancel' hr.2
      have hm0 : r / d ≠ 0 := (Nat.div_pos (Nat.le_of_dvd (by omega) hr.2) (by omega)).ne'
      have hmcop : d.Coprime (r / d) := by
        rw [Nat.coprime_iff_gcd_eq_one]
        by_contra hne
        obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hne
        exact hp.not_isUnit (hr.1.2 p (hdm ▸ Nat.mul_dvd_mul
          (dvd_trans hpdvd (Nat.gcd_dvd_left _ _)) (dvd_trans hpdvd (Nat.gcd_dvd_right _ _))))
      conv_lhs => rw [← hdm, hFn_mul_coprime (by omega) hm0 hmcop]
      ring
  rw [hfactor, show 1 / (gFn h d * selbergG h z) * ((1 / hFn h d) *
      ∑ m ∈ (SqFree (z / d)).filter (fun m => m.Coprime d), 1 / hFn h m) =
      ((1 / (gFn h d * hFn h d)) *
      ∑ m ∈ (SqFree (z / d)).filter (fun m => m.Coprime d), 1 / hFn h m) / selbergG h z by ring]
  rw [div_le_one hG_pos, inv_gFn_hFn_eq_sum_inv_hFn hEven hd'.2]
  set S2 := (SqFree (z / d)).filter (fun m => m.Coprime d)
  rw [Finset.sum_mul]
  have hprod_sum : ∑ k ∈ d.divisors, (1 / hFn h k) * ∑ m ∈ S2, 1 / hFn h m =
      ∑ p ∈ d.divisors ×ˢ S2, 1 / hFn h (p.1 * p.2) := by
    rw [Finset.sum_product]
    apply Finset.sum_congr rfl; intro k hk
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro m hm
    simp only [S2, Finset.mem_filter, SqFree, Finset.mem_Icc] at hm
    have hk0 : k ≠ 0 := (Nat.pos_of_mem_divisors hk).ne'
    have hm0 : m ≠ 0 := by omega
    have hcop : k.Coprime m := hm.2.symm.coprime_dvd_left (Nat.dvd_of_mem_divisors hk)
    rw [hFn_mul_coprime hk0 hm0 hcop]; ring
  rw [hprod_sum]
  have hinj : ∀ p1 ∈ d.divisors ×ˢ S2, ∀ p2 ∈ d.divisors ×ˢ S2, p1.1 * p1.2 = p2.1 * p2.2 → p1 = p2 := by
    intro p1 hp1 p2 hp2 heq
    simp only [Finset.mem_product, S2, Finset.mem_filter, SqFree, Finset.mem_Icc] at hp1 hp2
    have h1d : p1.1 ∣ d := Nat.dvd_of_mem_divisors hp1.1
    have h2d : p2.1 ∣ d := Nat.dvd_of_mem_divisors hp2.1
    have hk1 : p1.1 = Nat.gcd (p1.1 * p1.2) d := by
      rw [Nat.Coprime.gcd_mul_right_cancel p1.1 hp1.2.2, Nat.gcd_eq_left h1d]
    have hk2 : p2.1 = Nat.gcd (p2.1 * p2.2) d := by
      rw [Nat.Coprime.gcd_mul_right_cancel p2.1 hp2.2.2, Nat.gcd_eq_left h2d]
    have hfst : p1.1 = p2.1 := by rw [hk1, hk2, heq]
    ext
    · exact hfst
    · rw [hfst] at heq
      exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_mem_divisors hp2.1) heq
  have hsub : (d.divisors ×ˢ S2).image (fun p => p.1 * p.2) ⊆ SqFree z := by
    intro r hr
    rcases Finset.mem_image.mp hr with ⟨p, hp, rfl⟩
    simp only [Finset.mem_product, S2, Finset.mem_filter, SqFree, Finset.mem_Icc] at hp ⊢
    have h1d := Nat.dvd_of_mem_divisors hp.1
    have hk_le : p.1 ≤ d := Nat.le_of_dvd (by omega) h1d
    have hkm_le : p.1 * p.2 ≤ z :=
      le_trans (Nat.mul_le_mul hk_le hp.2.1.1.2) (Nat.mul_div_le z d)
    have hk_sq : Squarefree p.1 := hd'.2.squarefree_of_dvd h1d
    have hcop : p.1.Coprime p.2 := hp.2.2.symm.coprime_dvd_left h1d
    exact ⟨⟨Nat.mul_pos (Nat.pos_of_mem_divisors hp.1) hp.2.1.1.1, hkm_le⟩,
      (Nat.squarefree_mul hcop).mpr ⟨hk_sq, hp.2.1.2⟩⟩
  calc ∑ p ∈ d.divisors ×ˢ S2, 1 / hFn h (p.1 * p.2)
    _ = ∑ r ∈ (d.divisors ×ˢ S2).image (fun p => p.1 * p.2), 1 / hFn h r :=
        (Finset.sum_image (f := fun r => 1 / hFn h r) hinj).symm
    _ ≤ selbergG h z := Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun r _ _ => (div_pos one_pos (hFn_pos hEven r)).le)

private lemma selberg_main_quad {h z : ℕ} (hEven : Even h) (hz : 1 ≤ z) :
    ∑ d1 ∈ SqFree z, ∑ d2 ∈ SqFree z,
      selbergLam h z d1 * selbergLam h z d2 * gFn h (Nat.lcm d1 d2) = 1 / selbergG h z := by
  have hG_pos := selbergG_pos hEven hz
  have h1 : ∑ d1 ∈ SqFree z, ∑ d2 ∈ SqFree z,
      selbergLam h z d1 * selbergLam h z d2 * gFn h (Nat.lcm d1 d2) =
      ∑ r ∈ SqFree z, hFn h r *
        (∑ d ∈ (SqFree z).filter (fun d => r ∣ d), selbergLam h z d * gFn h d) ^ 2 := by
    have hexp : ∀ d1 ∈ SqFree z, ∀ d2 ∈ SqFree z,
        selbergLam h z d1 * selbergLam h z d2 * gFn h (Nat.lcm d1 d2) =
        ∑ r ∈ SqFree z, if r ∣ d1 ∧ r ∣ d2 then
          hFn h r * (selbergLam h z d1 * gFn h d1) * (selbergLam h z d2 * gFn h d2) else 0 := by
      intro d1 hd1 d2 hd2
      simp only [SqFree, Finset.mem_filter, Finset.mem_Icc] at hd1 hd2
      rw [gFn_lcm_eq (by omega) (by omega)]
      have hgcd_sq : Squarefree (Nat.gcd d1 d2) := hd1.2.squarefree_of_dvd (Nat.gcd_dvd_left _ _)
      have hinv := inv_gFn_eq_sum_hFn (h := h) hgcd_sq
      have hfilt : (SqFree z).filter (fun r => r ∣ d1 ∧ r ∣ d2) = (Nat.gcd d1 d2).divisors := by
        ext r
        simp only [Finset.mem_filter, SqFree, Finset.mem_Icc, Nat.mem_divisors,
          Nat.dvd_gcd_iff, ne_eq, Nat.gcd_ne_zero_left (by omega : d1 ≠ 0), not_false_eq_true, and_true]
        constructor
        · exact fun h => h.2
        · rintro ⟨hr1, hr2⟩
          refine ⟨⟨⟨Nat.pos_of_dvd_of_pos hr1 (by omega),
            le_trans (Nat.le_of_dvd (by omega) hr1) hd1.1.2⟩,
            hd1.2.squarefree_of_dvd hr1⟩, hr1, hr2⟩
      rw [← Finset.sum_filter, hfilt, ← Finset.sum_mul, ← Finset.sum_mul, ← hinv]
      ring
    calc ∑ d1 ∈ SqFree z, ∑ d2 ∈ SqFree z,
          selbergLam h z d1 * selbergLam h z d2 * gFn h (Nat.lcm d1 d2)
      _ = ∑ d1 ∈ SqFree z, ∑ d2 ∈ SqFree z, ∑ r ∈ SqFree z,
            if r ∣ d1 ∧ r ∣ d2 then
              hFn h r * (selbergLam h z d1 * gFn h d1) * (selbergLam h z d2 * gFn h d2) else 0 :=
          Finset.sum_congr rfl fun d1 hd1 => Finset.sum_congr rfl fun d2 hd2 => hexp d1 hd1 d2 hd2
      _ = ∑ r ∈ SqFree z, ∑ d1 ∈ SqFree z, ∑ d2 ∈ SqFree z,
            if r ∣ d1 ∧ r ∣ d2 then
              hFn h r * (selbergLam h z d1 * gFn h d1) * (selbergLam h z d2 * gFn h d2) else 0 := by
          rw [Finset.sum_comm]
          trans ∑ d2 ∈ SqFree z, ∑ r ∈ SqFree z, ∑ d1 ∈ SqFree z,
              if r ∣ d1 ∧ r ∣ d2 then
                hFn h r * (selbergLam h z d1 * gFn h d1) * (selbergLam h z d2 * gFn h d2) else 0
          · apply Finset.sum_congr rfl; intro d2 _; exact Finset.sum_comm
          · rw [Finset.sum_comm]
            apply Finset.sum_congr rfl; intro r _; exact Finset.sum_comm
      _ = ∑ r ∈ SqFree z, hFn h r *
            (∑ d ∈ (SqFree z).filter (fun d => r ∣ d), selbergLam h z d * gFn h d) ^ 2 := by
          apply Finset.sum_congr rfl; intro r _
          simp only [sq, Finset.sum_filter]
          rw [Finset.sum_mul, Finset.mul_sum]
          apply Finset.sum_congr rfl; intro d1 _
          rw [Finset.mul_sum, Finset.mul_sum]
          apply Finset.sum_congr rfl; intro d2 _
          by_cases h1 : r ∣ d1 <;> by_cases h2 : r ∣ d2 <;> simp [h1, h2]; ring
  rw [h1]
  have hinner : ∀ r ∈ SqFree z,
      ∑ d ∈ (SqFree z).filter (fun d => r ∣ d), selbergLam h z d * gFn h d =
        muSq r / (selbergG h z * hFn h r) := by
    intro r hr
    have hr' := hr
    simp only [SqFree, Finset.mem_filter, Finset.mem_Icc] at hr'
    have hterm : ∀ d ∈ (SqFree z).filter (fun d => r ∣ d),
        selbergLam h z d * gFn h d =
          (1 / selbergG h z) * (muSq d * ∑ u ∈ (SqFree z).filter (fun u => d ∣ u), 1 / hFn h u) := by
      intro d hd
      have hd_mem := (Finset.mem_filter.mp hd).1
      have hd0 : d ≠ 0 := by
        simp only [SqFree, Finset.mem_filter, Finset.mem_Icc] at hd_mem; omega
      simp only [selbergLam, if_pos hd_mem]
      have hgne := (gFn_pos (h := h) hd0).ne'
      field_simp
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    have hswap : ∑ d ∈ (SqFree z).filter (fun d => r ∣ d),
        muSq d * ∑ u ∈ (SqFree z).filter (fun u => d ∣ u), 1 / hFn h u =
        ∑ u ∈ (SqFree z).filter (fun u => r ∣ u),
          (1 / hFn h u) * ∑ d ∈ (SqFree z).filter (fun d => r ∣ d ∧ d ∣ u), muSq d := by
      have hL : ∑ d ∈ (SqFree z).filter (fun d => r ∣ d),
          muSq d * ∑ u ∈ (SqFree z).filter (fun u => d ∣ u), 1 / hFn h u =
          ∑ d ∈ SqFree z, ∑ u ∈ SqFree z, if r ∣ d ∧ d ∣ u then muSq d * (1 / hFn h u) else 0 := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl; intro d _
        by_cases hrd : r ∣ d
        · rw [if_pos hrd, Finset.mul_sum, Finset.sum_filter]
          apply Finset.sum_congr rfl; intro u _
          by_cases hdu : d ∣ u <;> simp [hrd, hdu]
        · rw [if_neg hrd, Finset.sum_eq_zero]
          intro u _; simp [hrd]
      have hR : ∑ u ∈ (SqFree z).filter (fun u => r ∣ u),
          (1 / hFn h u) * ∑ d ∈ (SqFree z).filter (fun d => r ∣ d ∧ d ∣ u), muSq d =
          ∑ u ∈ SqFree z, ∑ d ∈ SqFree z, if r ∣ d ∧ d ∣ u then muSq d * (1 / hFn h u) else 0 := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl; intro u _
        by_cases hru : r ∣ u
        · rw [if_pos hru, Finset.mul_sum, Finset.sum_filter]
          apply Finset.sum_congr rfl; intro d _
          by_cases h1 : r ∣ d ∧ d ∣ u
          · simp [h1, mul_comm]
          · simp [h1]
        · rw [if_neg hru, Finset.sum_eq_zero]
          intro d _
          have hnot : ¬ (r ∣ d ∧ d ∣ u) := fun ⟨a, b⟩ => hru (dvd_trans a b)
          simp [hnot]
      rw [hL, hR, Finset.sum_comm]
    rw [hswap]
    have hmob : ∀ u ∈ (SqFree z).filter (fun u => r ∣ u),
        ∑ d ∈ (SqFree z).filter (fun d => r ∣ d ∧ d ∣ u), muSq d =
        if u = r then muSq r else 0 := by
      intro u hu
      simp only [Finset.mem_filter, SqFree, Finset.mem_Icc] at hu
      set m := u / r
      have hrm : r * m = u := Nat.mul_div_cancel' hu.2
      have hm0 : m ≠ 0 := (Nat.div_pos (Nat.le_of_dvd (by omega) hu.2) (by omega)).ne'
      have hmsq : Squarefree m := hu.1.2.squarefree_of_dvd ⟨r, by linarith [hrm]⟩
      have hrcop : r.Coprime m := by
        rw [Nat.coprime_iff_gcd_eq_one]
        by_contra hne
        obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hne
        exact hp.not_isUnit (hu.1.2 p (hrm ▸ Nat.mul_dvd_mul
          (dvd_trans hpdvd (Nat.gcd_dvd_left _ _)) (dvd_trans hpdvd (Nat.gcd_dvd_right _ _))))
      have hsum_eq : ∑ d ∈ (SqFree z).filter (fun d => r ∣ d ∧ d ∣ u), muSq d =
          muSq r * ∑ k ∈ m.divisors, muSq k := by
        rw [Finset.mul_sum]
        apply Finset.sum_bij (fun d _ => d / r)
        · intro d hd
          simp only [Finset.mem_filter] at hd
          refine Nat.mem_divisors.mpr ⟨?_, hm0⟩
          have hd_eq : r * (d / r) = d := Nat.mul_div_cancel' hd.2.1
          have : r * (d / r) ∣ r * m := by rw [hd_eq, hrm]; exact hd.2.2
          exact (Nat.mul_dvd_mul_iff_left (show 0 < r by omega)).mp this
        · intro d1 hd1 d2 hd2 hq
          simp only [Finset.mem_filter] at hd1 hd2
          rw [← Nat.mul_div_cancel' hd1.2.1, ← Nat.mul_div_cancel' hd2.2.1, hq]
        · intro k hk
          have hkm := Nat.dvd_of_mem_divisors hk
          have hk_pos := Nat.pos_of_mem_divisors hk
          refine ⟨r * k, ?_, Nat.mul_div_cancel_left k (by omega)⟩
          simp only [Finset.mem_filter, SqFree, Finset.mem_Icc]
          have hrk_dvd : r * k ∣ u := hrm ▸ Nat.mul_dvd_mul_left r hkm
          exact ⟨⟨⟨Nat.mul_pos (by omega) hk_pos,
            le_trans (Nat.le_of_dvd (by omega) hrk_dvd) hu.1.1.2⟩,
            hu.1.2.squarefree_of_dvd hrk_dvd⟩, dvd_mul_right r k, hrk_dvd⟩
        · intro d hd
          simp only [Finset.mem_filter] at hd
          have hd_eq : r * (d / r) = d := Nat.mul_div_cancel' hd.2.1
          have hk_dvd : d / r ∣ m :=
            (Nat.mul_dvd_mul_iff_left (show 0 < r by omega)).mp (by rw [hd_eq, hrm]; exact hd.2.2)
          have hk0 : d / r ≠ 0 := (Nat.pos_of_dvd_of_pos hk_dvd (Nat.pos_of_ne_zero hm0)).ne'
          have hcop_k : r.Coprime (d / r) := hrcop.coprime_dvd_right hk_dvd
          conv_lhs => rw [← hd_eq, muSq_mul (by omega) hk0 hcop_k]
      rw [hsum_eq, sum_divisors_muSq hmsq]
      by_cases hur : u = r
      · have hm1 : m = 1 := by subst hur; exact Nat.div_self (by omega)
        simp [hur, hm1]
      · have hm1 : m ≠ 1 := fun h1 => hur (by rw [← hrm, h1, mul_one])
        simp [hur, hm1]
    rw [Finset.sum_congr rfl (fun u hu => by rw [hmob u hu])]
    have hsingle : ∑ u ∈ (SqFree z).filter (fun u => r ∣ u),
        (1 / hFn h u) * (if u = r then muSq r else 0) = (1 / hFn h r) * muSq r := by
      rw [Finset.sum_eq_single r]
      · simp
      · intro u _ hne; simp [hne]
      · intro hnot; exfalso; exact hnot (Finset.mem_filter.mpr ⟨hr, dvd_rfl⟩)
    rw [hsingle]; ring
  calc ∑ r ∈ SqFree z, hFn h r *
        (∑ d ∈ (SqFree z).filter (fun d => r ∣ d), selbergLam h z d * gFn h d) ^ 2
    _ = ∑ r ∈ SqFree z, hFn h r * (muSq r / (selbergG h z * hFn h r)) ^ 2 :=
        Finset.sum_congr rfl fun r hr => by rw [hinner r hr]
    _ = (1 / (selbergG h z) ^ 2) * ∑ r ∈ SqFree z, 1 / hFn h r := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro r _
        have hpos := (hFn_pos hEven r).ne'
        have hGne := hG_pos.ne'
        have hmu2 := muSq_sq r
        rw [div_pow, hmu2]; field_simp
    _ = 1 / selbergG h z := by
        change (1 / (selbergG h z) ^ 2) * selbergG h z = 1 / selbergG h z
        field_simp

private lemma selberg_err_bound (h z : ℕ) (hz : 1 ≤ z) :
    ∑ d1 ∈ SqFree z, ∑ d2 ∈ SqFree z, (rho h (Nat.lcm d1 d2) : ℝ) ≤
      (z : ℝ) ^ 2 * (Real.log (z : ℝ) + 1) ^ 2 := by
  have h1 : ∑ d1 ∈ SqFree z, ∑ d2 ∈ SqFree z, (rho h (Nat.lcm d1 d2) : ℝ) ≤
      (∑ d ∈ Finset.Icc 1 z, (d.divisors.card : ℝ)) ^ 2 := by
    calc ∑ d1 ∈ SqFree z, ∑ d2 ∈ SqFree z, (rho h (Nat.lcm d1 d2) : ℝ)
      _ ≤ ∑ d1 ∈ SqFree z, ∑ d2 ∈ SqFree z, (rho h d1 : ℝ) * (rho h d2 : ℝ) := by
          apply Finset.sum_le_sum; intro d1 hd1
          apply Finset.sum_le_sum; intro d2 hd2
          have hd10 : d1 ≠ 0 := (Finset.mem_filter.mp hd1).2.ne_zero
          have hd20 : d2 ≠ 0 := (Finset.mem_filter.mp hd2).2.ne_zero
          exact_mod_cast rho_lcm_le_mul (h := h) hd10 hd20
      _ = (∑ d ∈ SqFree z, (rho h d : ℝ)) ^ 2 := by
          rw [sq, Finset.sum_mul]; apply Finset.sum_congr rfl; intro d1 _; rw [Finset.mul_sum]
      _ ≤ (∑ d ∈ Finset.Icc 1 z, (d.divisors.card : ℝ)) ^ 2 := by
          apply pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _))
          calc ∑ d ∈ SqFree z, (rho h d : ℝ)
            _ ≤ ∑ d ∈ SqFree z, (d.divisors.card : ℝ) :=
                Finset.sum_le_sum fun d hd => by exact_mod_cast rho_le_card_divisors (Finset.mem_filter.mp hd).2
            _ ≤ ∑ d ∈ Finset.Icc 1 z, (d.divisors.card : ℝ) :=
                Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
                  (fun _ _ _ => Nat.cast_nonneg _)
  have hdiv_sum : ∑ d ∈ Finset.Icc 1 z, (d.divisors.card : ℝ) ≤
      (z : ℝ) * (Real.log (z : ℝ) + 1) := by
    have hcount : ∑ d ∈ Finset.Icc 1 z, (d.divisors.card : ℝ) =
        ∑ a ∈ Finset.Icc 1 z, (((Finset.Icc 1 z).filter (fun d => a ∣ d)).card : ℝ) := by
      have h1 : ∀ d ∈ Finset.Icc 1 z, (d.divisors.card : ℝ) =
          ∑ a ∈ Finset.Icc 1 z, if a ∣ d then (1 : ℝ) else 0 := by
        intro d hd
        rw [Finset.mem_Icc] at hd
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
        congr 1; congr 1; ext a
        have hd0 : d ≠ 0 := by omega
        simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors, hd0, ne_eq,
          not_false_eq_true, and_true]
        exact ⟨fun h => ⟨⟨Nat.pos_of_dvd_of_pos h (by omega), le_trans (Nat.le_of_dvd (by omega) h) hd.2⟩, h⟩,
          fun h => h.2⟩
      rw [Finset.sum_congr rfl h1, Finset.sum_comm]
      apply Finset.sum_congr rfl; intro a _
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [hcount]
    calc ∑ a ∈ Finset.Icc 1 z, (((Finset.Icc 1 z).filter (fun d => a ∣ d)).card : ℝ)
      _ ≤ ∑ a ∈ Finset.Icc 1 z, (z : ℝ) / (a : ℝ) := by
          apply Finset.sum_le_sum; intro a ha
          exact card_multiples_Icc_le z a (Finset.mem_Icc.mp ha).1
      _ = (z : ℝ) * ∑ a ∈ Finset.Icc 1 z, (1 : ℝ) / (a : ℝ) := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro a _; ring
      _ ≤ (z : ℝ) * (Real.log (z : ℝ) + 1) :=
          mul_le_mul_of_nonneg_left (harmonic_upper_bound z hz) (Nat.cast_nonneg z)
  calc ∑ d1 ∈ SqFree z, ∑ d2 ∈ SqFree z, (rho h (Nat.lcm d1 d2) : ℝ)
    _ ≤ (∑ d ∈ Finset.Icc 1 z, (d.divisors.card : ℝ)) ^ 2 := h1
    _ ≤ ((z : ℝ) * (Real.log (z : ℝ) + 1)) ^ 2 :=
        pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)) hdiv_sum 2
    _ = (z : ℝ) ^ 2 * (Real.log (z : ℝ) + 1) ^ 2 := by ring

private lemma selberg_roots_log (x : ℕ) (hx : 1000000 ^ 4 ≤ x) :
    let z := Nat.sqrt (Nat.sqrt x)
    let Y := Nat.sqrt z
    let W := Nat.sqrt Y
    1000000 ≤ z ∧ 1000 ≤ Y ∧ 31 ≤ W ∧ z ^ 4 ≤ x ∧ Y ^ 2 ≤ z ∧ W ^ 2 ≤ Y ∧ 2 ≤ x ∧
      Real.log (x : ℝ) / 10 ≤ Real.log (Y : ℝ) ∧ Real.log (x : ℝ) ≤ 24 * (W : ℝ) := by
  intro z Y W
  have hz_ge : 1000000 ≤ z := by
    have h1 : 1000000 ^ 2 ≤ Nat.sqrt x := by
      rw [Nat.le_sqrt]
      calc 1000000 ^ 2 * 1000000 ^ 2 = 1000000 ^ 4 := by ring
        _ ≤ x := hx
    rw [Nat.le_sqrt]
    calc 1000000 * 1000000 = 1000000 ^ 2 := by ring
      _ ≤ Nat.sqrt x := h1
  have hY_ge : 1000 ≤ Y := by
    rw [Nat.le_sqrt]; exact le_trans (by norm_num) hz_ge
  have hW_ge : 31 ≤ W := by
    rw [Nat.le_sqrt]; exact le_trans (by norm_num) hY_ge
  have hz4_le : z ^ 4 ≤ x := by
    have ha : z ^ 2 ≤ Nat.sqrt x := by have := Nat.sqrt_le (Nat.sqrt x); nlinarith
    have hb : (Nat.sqrt x) ^ 2 ≤ x := by have := Nat.sqrt_le x; nlinarith
    calc z ^ 4 = (z ^ 2) ^ 2 := by ring
      _ ≤ (Nat.sqrt x) ^ 2 := Nat.pow_le_pow_left ha 2
      _ ≤ x := hb
  have hx_ge_2 : 2 ≤ x := by
    have : 2 ≤ z ^ 4 := by
      calc 2 ≤ 1000000 := by norm_num
        _ ≤ z := hz_ge
        _ ≤ z ^ 4 := le_self_pow₀ (by omega) (by norm_num)
    omega
  clear hx
  have hY2_le : Y ^ 2 ≤ z := by have := Nat.sqrt_le z; nlinarith
  have hW2_le : W ^ 2 ≤ Y := by have := Nat.sqrt_le Y; nlinarith
  have hx_lt_Y10 : x < Y ^ 10 := by
    have h1 : x < (Nat.sqrt x + 1) ^ 2 := by have := Nat.lt_succ_sqrt x; nlinarith
    have h2 : Nat.sqrt x + 1 ≤ (z + 1) ^ 2 := by have := Nat.lt_succ_sqrt (Nat.sqrt x); nlinarith
    have h3 : z + 1 ≤ (Y + 1) ^ 2 := by have := Nat.lt_succ_sqrt z; nlinarith
    have hx_lt_z4 : x < (z + 1) ^ 4 :=
      lt_of_lt_of_le h1 (by calc (Nat.sqrt x + 1) ^ 2 ≤ ((z + 1) ^ 2) ^ 2 := Nat.pow_le_pow_left h2 2
        _ = (z + 1) ^ 4 := by ring)
    have hY1_le : Y + 1 ≤ 2 * Y := by omega
    calc x < (z + 1) ^ 4 := hx_lt_z4
      _ ≤ ((Y + 1) ^ 2) ^ 4 := Nat.pow_le_pow_left h3 4
      _ = (Y + 1) ^ 8 := by ring
      _ ≤ (2 * Y) ^ 8 := Nat.pow_le_pow_left hY1_le 8
      _ = 256 * Y ^ 8 := by ring
      _ ≤ Y ^ 2 * Y ^ 8 := Nat.mul_le_mul_right _ (by nlinarith)
      _ = Y ^ 10 := by ring
  have hY_lt_W2 : Y < 2 * W ^ 2 := by
    have h1 : Y < (W + 1) ^ 2 := by have := Nat.lt_succ_sqrt Y; nlinarith
    nlinarith
  have hx_lt_W24 : x < W ^ 24 := by
    have hW4 : 1024 ≤ W ^ 4 := by
      have : 32 ≤ W ^ 2 := by nlinarith
      calc 1024 = 32 * 32 := by norm_num
        _ ≤ W ^ 2 * W ^ 2 := Nat.mul_le_mul this this
        _ = W ^ 4 := by ring
    calc x < Y ^ 10 := hx_lt_Y10
      _ ≤ (2 * W ^ 2) ^ 10 := Nat.pow_le_pow_left hY_lt_W2.le 10
      _ = 1024 * W ^ 20 := by ring
      _ ≤ W ^ 4 * W ^ 20 := Nat.mul_le_mul_right _ hW4
      _ = W ^ 24 := by ring
  have hlogY_ge : Real.log (x : ℝ) / 10 ≤ Real.log (Y : ℝ) := by
    have h := Real.log_le_log (Nat.cast_pos.mpr (by omega))
      (by exact_mod_cast hx_lt_Y10.le : (x : ℝ) ≤ (Y : ℝ) ^ 10)
    rw [Real.log_pow] at h; norm_num at h; linarith
  have hlogx_le_W : Real.log (x : ℝ) ≤ 24 * (W : ℝ) := by
    have h := Real.log_le_log (Nat.cast_pos.mpr (by omega))
      (by exact_mod_cast hx_lt_W24.le : (x : ℝ) ≤ (W : ℝ) ^ 24)
    rw [Real.log_pow] at h
    have hWlog := Real.log_le_sub_one_of_pos (Nat.cast_pos.mpr (by omega : 0 < W))
    norm_num at h; linarith
  exact ⟨hz_ge, hY_ge, hW_ge, hz4_le, hY2_le, hW2_le, hx_ge_2, hlogY_ge, hlogx_le_W⟩

private lemma selberg_roots_err (x z Y W : ℕ)
    (hz_ge : 1000000 ≤ z) (hY_ge : 1000 ≤ Y) (hW_ge : 31 ≤ W)
    (hz4_le : z ^ 4 ≤ x) (hY2_le : Y ^ 2 ≤ z) (hW2_le : W ^ 2 ≤ Y)
    (hx_ge_2 : 2 ≤ x) (hlogx_le_W : Real.log (x : ℝ) ≤ 24 * (W : ℝ)) :
    (z : ℝ) ≤ (x : ℝ) / (Real.log (x : ℝ)) ^ 2 ∧
      (z : ℝ) ^ 2 * (Real.log (z : ℝ) + 1) ^ 2 ≤ (x : ℝ) / (Real.log (x : ℝ)) ^ 2 := by
  have hlogx_pos : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < x))
  constructor
  · rw [le_div_iff₀ (sq_pos_of_pos hlogx_pos)]
    have hlog2 : (Real.log (x : ℝ)) ^ 2 ≤ (24 * (W : ℝ)) ^ 2 :=
      pow_le_pow_left₀ hlogx_pos.le hlogx_le_W 2
    have hnat : z * (576 * W ^ 2) ≤ x := by
      have h1 : 576 * W ^ 2 ≤ z := by
        have : 576 * W ^ 2 ≤ 576 * Y := Nat.mul_le_mul_left 576 hW2_le
        have : 576 * Y ≤ Y ^ 2 := by nlinarith
        omega
      have hz2_le_z4 : z ^ 2 ≤ z ^ 4 := by
        have : 1 ≤ z ^ 2 := by nlinarith
        calc z ^ 2 = z ^ 2 * 1 := (mul_one _).symm
          _ ≤ z ^ 2 * z ^ 2 := Nat.mul_le_mul_left _ this
          _ = z ^ 4 := by ring
      calc z * (576 * W ^ 2) ≤ z * z := Nat.mul_le_mul_left z h1
        _ = z ^ 2 := (sq z).symm
        _ ≤ z ^ 4 := hz2_le_z4
        _ ≤ x := hz4_le
    have hreal : (z : ℝ) * (576 * (W : ℝ) ^ 2) ≤ (x : ℝ) := by exact_mod_cast hnat
    have hmul := mul_le_mul_of_nonneg_left hlog2 (Nat.cast_nonneg z)
    nlinarith
  · rw [le_div_iff₀ (sq_pos_of_pos hlogx_pos)]
    have hzx : z ≤ x := by
      have : z ≤ z ^ 4 := le_self_pow₀ (by omega) (by norm_num)
      omega
    have hlogz_le : Real.log (z : ℝ) ≤ Real.log (x : ℝ) :=
      Real.log_le_log (Nat.cast_pos.mpr (by omega)) (by exact_mod_cast hzx)
    have hlog_add : Real.log (x : ℝ) + 1 ≤ 25 * (W : ℝ) := by
      have hW1 : (1 : ℝ) ≤ (W : ℝ) := by exact_mod_cast (by omega : 1 ≤ W)
      linarith
    have hlog4 : (Real.log (z : ℝ) + 1) ^ 2 * (Real.log (x : ℝ)) ^ 2 ≤ (25 * (W : ℝ)) ^ 4 := by
      have hlogz_nn : 0 ≤ Real.log (z : ℝ) :=
        Real.log_nonneg (show (1 : ℝ) ≤ (z : ℝ) by exact_mod_cast (by omega : 1 ≤ z))
      have h1 : (Real.log (z : ℝ) + 1) ^ 2 ≤ (25 * (W : ℝ)) ^ 2 :=
        pow_le_pow_left₀ (by linarith) (by linarith) 2
      have h2 : (Real.log (x : ℝ)) ^ 2 ≤ (25 * (W : ℝ)) ^ 2 :=
        pow_le_pow_left₀ hlogx_pos.le (by linarith) 2
      have := mul_le_mul h1 h2 (sq_nonneg _) (sq_nonneg _)
      linarith [show (25 * (W : ℝ)) ^ 2 * (25 * (W : ℝ)) ^ 2 = (25 * (W : ℝ)) ^ 4 by ring]
    have hnat : z ^ 2 * (390625 * W ^ 4) ≤ x := by
      have hW4 : W ^ 4 ≤ Y ^ 2 := by
        calc W ^ 4 = (W ^ 2) ^ 2 := by ring
          _ ≤ Y ^ 2 := Nat.pow_le_pow_left hW2_le 2
      have h390 : 390625 * Y ^ 2 ≤ z ^ 2 := by
        have hY4 : Y ^ 4 ≤ z ^ 2 := by
          calc Y ^ 4 = (Y ^ 2) ^ 2 := by ring
            _ ≤ z ^ 2 := Nat.pow_le_pow_left hY2_le 2
        have hY2_big : 390625 ≤ Y ^ 2 := by nlinarith
        calc 390625 * Y ^ 2 ≤ Y ^ 2 * Y ^ 2 := Nat.mul_le_mul_right _ hY2_big
          _ = Y ^ 4 := by ring
          _ ≤ z ^ 2 := hY4
      calc z ^ 2 * (390625 * W ^ 4) ≤ z ^ 2 * (390625 * Y ^ 2) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hW4)
        _ ≤ z ^ 2 * z ^ 2 := Nat.mul_le_mul_left _ h390
        _ = z ^ 4 := by ring
        _ ≤ x := hz4_le
    have hreal : (z : ℝ) ^ 2 * (390625 * (W : ℝ) ^ 4) ≤ (x : ℝ) := by exact_mod_cast hnat
    have hmul := mul_le_mul_of_nonneg_left hlog4 (sq_nonneg (z : ℝ))
    have hpow25 : (25 * (W : ℝ)) ^ 4 = 390625 * (W : ℝ) ^ 4 := by ring
    linarith [hpow25]

private lemma selberg_sieve_upper (x h z : ℕ) (hz : 1 ≤ z) (hEven : Even h) :
    (((Finset.Icc 1 x).filter (fun p => p.Prime ∧ (p + h).Prime)).card : ℝ) ≤
      (z : ℝ) + (x : ℝ) / selbergG h z + (z : ℝ) ^ 2 * (Real.log (z : ℝ) + 1) ^ 2 := by
  set P := (Finset.Icc 1 x).filter (fun p => p.Prime ∧ (p + h).Prime)
  set P1 := P.filter (fun p => p ≤ z)
  set P2 := P.filter (fun p => ¬ (p ≤ z))
  have hP_split : (P.card : ℝ) = (P1.card : ℝ) + (P2.card : ℝ) := by
    exact_mod_cast (Finset.card_filter_add_card_filter_not (s := P) (p := fun p => p ≤ z)).symm
  have hP1_le : (P1.card : ℝ) ≤ (z : ℝ) := by
    have hsub : P1 ⊆ Finset.Icc 1 z := fun p hp => by
      simp only [P1, P, Finset.mem_filter, Finset.mem_Icc] at hp ⊢
      exact ⟨hp.1.1.1, hp.2⟩
    exact_mod_cast le_trans (Finset.card_le_card hsub) (by simp)
  have hP2_le : (P2.card : ℝ) ≤
      ∑ n ∈ Finset.Icc 1 x, (∑ d ∈ (SqFree z).filter (fun d => d ∣ n * (n + h)), selbergLam h z d) ^ 2 := by
    have hsub : P2 ⊆ Finset.Icc 1 x := fun p hp => (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1
    calc (P2.card : ℝ) = ∑ _p ∈ P2, (1 : ℝ) := by simp
      _ = ∑ p ∈ P2, (∑ d ∈ (SqFree z).filter (fun d => d ∣ p * (p + h)), selbergLam h z d) ^ 2 := by
          apply Finset.sum_congr rfl; intro p hp
          simp only [P2, P, Finset.mem_filter, Finset.mem_Icc] at hp
          have honly1 : (SqFree z).filter (fun d => d ∣ p * (p + h)) = {1} := by
            ext d
            simp only [Finset.mem_filter, SqFree, Finset.mem_Icc, Finset.mem_singleton]
            constructor
            · rintro ⟨⟨⟨hd1, hdz⟩, _⟩, hdvd⟩
              by_contra hne1
              obtain ⟨q, hqp, hqd⟩ := Nat.exists_prime_and_dvd hne1
              have hq_le : q ≤ z := le_trans (Nat.le_of_dvd (by omega) hqd) hdz
              rcases hqp.dvd_mul.mp (dvd_trans hqd hdvd) with hq1 | hq2
              · have : q = p := (Nat.prime_dvd_prime_iff_eq hqp hp.1.2.1).mp hq1; omega
              · have : q = p + h := (Nat.prime_dvd_prime_iff_eq hqp hp.1.2.2).mp hq2; omega
            · rintro rfl
              exact ⟨⟨⟨le_rfl, hz⟩, squarefree_one⟩, one_dvd _⟩
          rw [honly1, Finset.sum_singleton, selbergLam_one hEven hz]; norm_num
      _ ≤ ∑ n ∈ Finset.Icc 1 x,
            (∑ d ∈ (SqFree z).filter (fun d => d ∣ n * (n + h)), selbergLam h z d) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)
  have hexpand : ∑ n ∈ Finset.Icc 1 x,
      (∑ d ∈ (SqFree z).filter (fun d => d ∣ n * (n + h)), selbergLam h z d) ^ 2 =
      ∑ d1 ∈ SqFree z, ∑ d2 ∈ SqFree z,
        selbergLam h z d1 * selbergLam h z d2 *
          (((Finset.Icc 1 x).filter (fun n => Nat.lcm d1 d2 ∣ n * (n + h))).card : ℝ) := by
    have h1 : ∀ n ∈ Finset.Icc 1 x,
        (∑ d ∈ (SqFree z).filter (fun d => d ∣ n * (n + h)), selbergLam h z d) ^ 2 =
        ∑ d1 ∈ SqFree z, ∑ d2 ∈ SqFree z,
          if Nat.lcm d1 d2 ∣ n * (n + h) then selbergLam h z d1 * selbergLam h z d2 else 0 := by
      intro n _
      simp only [sq, Finset.sum_filter]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl; intro d1 _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro d2 _
      by_cases h1 : d1 ∣ n * (n + h) <;> by_cases h2 : d2 ∣ n * (n + h) <;>
        simp [Nat.lcm_dvd_iff, h1, h2]
    rw [Finset.sum_congr rfl h1, Finset.sum_comm]
    apply Finset.sum_congr rfl; intro d1 _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro d2 _
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hsieve_le : ∑ d1 ∈ SqFree z, ∑ d2 ∈ SqFree z,
      selbergLam h z d1 * selbergLam h z d2 *
        (((Finset.Icc 1 x).filter (fun n => Nat.lcm d1 d2 ∣ n * (n + h))).card : ℝ) ≤
      (x : ℝ) / selbergG h z +
        ∑ d1 ∈ SqFree z, ∑ d2 ∈ SqFree z, (rho h (Nat.lcm d1 d2) : ℝ) := by
    have hstep : ∀ d1 ∈ SqFree z, ∀ d2 ∈ SqFree z,
        selbergLam h z d1 * selbergLam h z d2 *
          (((Finset.Icc 1 x).filter (fun n => Nat.lcm d1 d2 ∣ n * (n + h))).card : ℝ) ≤
        selbergLam h z d1 * selbergLam h z d2 * ((x : ℝ) * gFn h (Nat.lcm d1 d2)) +
          (rho h (Nat.lcm d1 d2) : ℝ) := by
      intro d1 hd1 d2 hd2
      have hlcm_sq := squarefree_lcm (Finset.mem_filter.mp hd1).2 (Finset.mem_filter.mp hd2).2
      have hbds := crt_count_solutions_bounds h (Nat.lcm d1 d2) x hlcm_sq
      set C := (((Finset.Icc 1 x).filter (fun n => Nat.lcm d1 d2 ∣ n * (n + h))).card : ℝ)
      set M := (x : ℝ) * gFn h (Nat.lcm d1 d2)
      set E := (rho h (Nat.lcm d1 d2) : ℝ)
      have hdiff : |C - M| ≤ E := abs_le.mpr ⟨by linarith [hbds.1], by linarith [hbds.2]⟩
      have hlam_prod : |selbergLam h z d1 * selbergLam h z d2| ≤ 1 := by
        rw [abs_mul]
        calc |selbergLam h z d1| * |selbergLam h z d2| ≤ 1 * 1 :=
              mul_le_mul (selbergLam_abs_le_one hEven hz hd1)
                (selbergLam_abs_le_one hEven hz hd2) (abs_nonneg _) zero_le_one
          _ = 1 := one_mul 1
      have hbound : selbergLam h z d1 * selbergLam h z d2 * (C - M) ≤ E := by
        calc selbergLam h z d1 * selbergLam h z d2 * (C - M)
          _ ≤ |selbergLam h z d1 * selbergLam h z d2 * (C - M)| := le_abs_self _
          _ = |selbergLam h z d1 * selbergLam h z d2| * |C - M| := abs_mul _ _
          _ ≤ 1 * E := mul_le_mul hlam_prod hdiff (abs_nonneg _) zero_le_one
          _ = E := one_mul E
      linarith
    calc ∑ d1 ∈ SqFree z, ∑ d2 ∈ SqFree z,
          selbergLam h z d1 * selbergLam h z d2 *
            (((Finset.Icc 1 x).filter (fun n => Nat.lcm d1 d2 ∣ n * (n + h))).card : ℝ)
      _ ≤ ∑ d1 ∈ SqFree z, ∑ d2 ∈ SqFree z,
            (selbergLam h z d1 * selbergLam h z d2 * ((x : ℝ) * gFn h (Nat.lcm d1 d2)) +
              (rho h (Nat.lcm d1 d2) : ℝ)) :=
          Finset.sum_le_sum fun d1 hd1 => Finset.sum_le_sum fun d2 hd2 => hstep d1 hd1 d2 hd2
      _ = (x : ℝ) * (∑ d1 ∈ SqFree z, ∑ d2 ∈ SqFree z,
            selbergLam h z d1 * selbergLam h z d2 * gFn h (Nat.lcm d1 d2)) +
          ∑ d1 ∈ SqFree z, ∑ d2 ∈ SqFree z, (rho h (Nat.lcm d1 d2) : ℝ) := by
          simp_rw [Finset.sum_add_distrib]
          congr 1
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro d1 _
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro d2 _; ring
      _ = (x : ℝ) / selbergG h z +
          ∑ d1 ∈ SqFree z, ∑ d2 ∈ SqFree z, (rho h (Nat.lcm d1 d2) : ℝ) := by
          rw [selberg_main_quad hEven hz]; ring
  have herr_le := selberg_err_bound h z hz
  linarith

private lemma selberg_shifted_primes (x h : ℕ) (hx : 1000000 ^ 4 ≤ x) (hh : 0 < h) (hEven : Even h) :
    (((Finset.Icc 1 x).filter (fun p => p.Prime ∧ (p + h).Prime)).card : ℝ) ≤
      200 * (x : ℝ) / (Real.log (x : ℝ)) ^ 2 * ((h : ℝ) / (h.totient : ℝ)) ^ 2 := by
  set z := Nat.sqrt (Nat.sqrt x)
  set Y := Nat.sqrt z
  set W := Nat.sqrt Y
  obtain ⟨hz_ge, hY_ge, hW_ge, hz4_le, hY2_le, hW2_le, hx_ge_2, hlogY_ge, hlogx_le_W⟩ :=
    selberg_roots_log x hx
  clear hx
  obtain ⟨hz_le_main, herr_le_main⟩ :=
    selberg_roots_err x z Y W hz_ge hY_ge hW_ge hz4_le hY2_le hW2_le hx_ge_2 hlogx_le_W
  have hsieve := selberg_sieve_upper x h z (by omega) hEven
  have hlogx_pos : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < x))
  have hht_pos : 0 < (h.totient : ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr hh)
  have hh_pos : 0 < (h : ℝ) := Nat.cast_pos.mpr hh
  have hratio_ge1 : (1 : ℝ) ≤ (h : ℝ) / (h.totient : ℝ) := by
    rw [one_le_div hht_pos]; exact_mod_cast Nat.totient_le h
  have hG_lb : ((h.totient : ℝ) / (h : ℝ)) ^ 2 * (Real.log (Y : ℝ)) ^ 2 ≤ selbergG h z :=
    selberg_G_lower_bound h z hh hEven (by omega)
  have hmain_le : (x : ℝ) / selbergG h z ≤
      100 * (x : ℝ) / (Real.log (x : ℝ)) ^ 2 * ((h : ℝ) / (h.totient : ℝ)) ^ 2 := by
    have h1 : ((h.totient : ℝ) / (h : ℝ)) ^ 2 * (Real.log (x : ℝ) / 10) ^ 2 ≤ selbergG h z := by
      have hsq : (Real.log (x : ℝ) / 10) ^ 2 ≤ (Real.log (Y : ℝ)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hlogY_ge 2
      have := mul_le_mul_of_nonneg_left hsq (sq_nonneg ((h.totient : ℝ) / (h : ℝ)))
      linarith
    have hden_pos : 0 < ((h.totient : ℝ) / (h : ℝ)) ^ 2 * (Real.log (x : ℝ) / 10) ^ 2 := by positivity
    calc (x : ℝ) / selbergG h z
      _ ≤ (x : ℝ) / (((h.totient : ℝ) / (h : ℝ)) ^ 2 * (Real.log (x : ℝ) / 10) ^ 2) :=
          div_le_div_of_nonneg_left (Nat.cast_nonneg x) hden_pos h1
      _ = 100 * (x : ℝ) / (Real.log (x : ℝ)) ^ 2 * ((h : ℝ) / (h.totient : ℝ)) ^ 2 := by
          field_simp; ring
  have hsq_ratio_ge1 : (1 : ℝ) ≤ ((h : ℝ) / (h.totient : ℝ)) ^ 2 := by nlinarith
  have hxlog_nn : 0 ≤ (x : ℝ) / (Real.log (x : ℝ)) ^ 2 := by positivity
  have h2_le : 2 * ((x : ℝ) / (Real.log (x : ℝ)) ^ 2) ≤
      100 * (x : ℝ) / (Real.log (x : ℝ)) ^ 2 * ((h : ℝ) / (h.totient : ℝ)) ^ 2 := by
    have := mul_le_mul_of_nonneg_left hsq_ratio_ge1 hxlog_nn
    linarith [show 100 * (x : ℝ) / (Real.log (x : ℝ)) ^ 2 * ((h : ℝ) / (h.totient : ℝ)) ^ 2 =
      100 * ((x : ℝ) / (Real.log (x : ℝ)) ^ 2 * ((h : ℝ) / (h.totient : ℝ)) ^ 2) by ring]
  have h200 : 100 * (x : ℝ) / (Real.log (x : ℝ)) ^ 2 * ((h : ℝ) / (h.totient : ℝ)) ^ 2 +
      100 * (x : ℝ) / (Real.log (x : ℝ)) ^ 2 * ((h : ℝ) / (h.totient : ℝ)) ^ 2 =
      200 * (x : ℝ) / (Real.log (x : ℝ)) ^ 2 * ((h : ℝ) / (h.totient : ℝ)) ^ 2 := by ring
  linarith [hsieve, hmain_le, hz_le_main, herr_le_main, h2_le, h200]

/-! ### Section 6: Romanoff's Convergent Sum & Positive Lower Density -/

private noncomputable def ord2 (d : ℕ) : ℕ := orderOf (2 : ZMod d)

private lemma ord2_pos_of_odd {d : ℕ} (hd : Odd d) : 1 ≤ ord2 d := by
  have hcop : (2 : ℕ).Coprime d := Nat.Coprime.symm (Nat.coprime_two_right.mpr hd)
  have hd0 : d ≠ 0 := by rcases hd with ⟨k, rfl⟩; omega
  have : NeZero d := ⟨hd0⟩
  have hunit : IsUnit (2 : ZMod d) := (ZMod.isUnit_iff_coprime 2 d).mpr hcop
  rcases hunit with ⟨u, hu⟩
  have hfin : IsOfFinOrder u := isOfFinOrder_of_finite u
  have hord_eq : ord2 d = orderOf u := by
    unfold ord2; rw [← hu, orderOf_units]
  rw [hord_eq]
  exact Nat.pos_of_ne_zero (orderOf_pos_iff.mpr hfin).ne'

private lemma ord2_dvd_of_dvd_two_pow_sub_one {d m : ℕ} (hd : d ∣ 2 ^ m - 1) :
    ord2 d ∣ m := by
  apply orderOf_dvd_of_pow_eq_one
  have h0 : ((2 ^ m - 1 : ℕ) : ZMod d) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hd
  have h1 : (2 : ZMod d) ^ m - 1 = 0 := by
    have hge : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    rw [Nat.cast_sub hge, Nat.cast_pow] at h0
    simpa using h0
  exact sub_eq_zero.mp h1

private lemma dvd_two_pow_ord2_sub_one (d : ℕ) :
    d ∣ 2 ^ ord2 d - 1 := by
  have hpow : (2 : ZMod d) ^ ord2 d = 1 := pow_orderOf_eq_one (2 : ZMod d)
  rw [← ZMod.natCast_eq_zero_iff]
  have hge : 1 ≤ 2 ^ ord2 d := Nat.one_le_two_pow
  rw [Nat.cast_sub hge, Nat.cast_pow]
  simpa using sub_eq_zero.mpr hpow

private noncomputable def romW (d : ℕ) : ℝ := (3 : ℝ) ^ d.primeFactors.card / (d.totient : ℝ)

private lemma romW_one : romW 1 = 1 := by simp [romW]

private lemma romW_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hcop : a.Coprime b) :
    romW (a * b) = romW a * romW b := by
  simp only [romW, Nat.totient_mul hcop, Nat.primeFactors_mul ha hb]
  have hdisj : Disjoint a.primeFactors b.primeFactors := by
    rw [Finset.disjoint_left]; intro p hpa hpb
    have hp := Nat.prime_of_mem_primeFactors hpa
    exact hp.not_dvd_one (hcop.gcd_eq_one ▸ Nat.dvd_gcd (Nat.dvd_of_mem_primeFactors hpa)
      (Nat.dvd_of_mem_primeFactors hpb))
  rw [Finset.card_union_of_disjoint hdisj, pow_add, Nat.cast_mul]; ring

private lemma romW_prime {q : ℕ} (hq : q.Prime) : romW q = 3 / ((q : ℝ) - 1) := by
  simp only [romW, hq.primeFactors, Finset.card_singleton, pow_one, Nat.totient_prime hq,
    Nat.cast_sub hq.pos, Nat.cast_one]

private lemma prod_two_pow_sub_one_odd (s : Finset ℕ) (hs : ∀ j ∈ s, 1 ≤ j) :
    Odd (∏ j ∈ s, (2 ^ j - 1)) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a t hat ih =>
    rw [Finset.prod_insert hat]
    apply Odd.mul
    · have ha1 := hs a (Finset.mem_insert_self a t)
      rcases even_iff_two_dvd.mpr (dvd_pow_self 2 (by omega : a ≠ 0)) with ⟨c, hc⟩
      have : 2 ≤ 2 ^ a := le_trans (by norm_num : 2 ≤ 2 ^ 1) (Nat.pow_le_pow_right (by norm_num) ha1)
      exact ⟨c - 1, by omega⟩
    · exact ih fun j hj => hs j (Finset.mem_insert_of_mem hj)

private lemma romanoff_prod_bound (C0 : ℝ)
    (hC0 : ∀ Y : ℕ, 1 ≤ Y → ∑ p ∈ primesUpTo Y, (1 : ℝ) / (p : ℝ) ≤ C0 + Real.log (Y : ℝ) / 24)
    (T : ℕ) (hT : 2 ≤ T) (M : ℕ) (hM_pos : 0 < M) (hM_lt : M < 2 ^ (T ^ 2)) :
    ∏ q ∈ M.primeFactors, (1 + 3 / ((q : ℝ) - 1)) ≤
      Real.exp (6 * C0 + 3) * Real.sqrt (T : ℝ) := by
  have hsplit_p : ∏ q ∈ M.primeFactors, (1 + 3 / ((q : ℝ) - 1)) =
      (∏ q ∈ M.primeFactors.filter (fun q => q ≤ T ^ 2), (1 + 3 / ((q : ℝ) - 1))) *
      (∏ q ∈ M.primeFactors.filter (fun q => ¬ (q ≤ T ^ 2)), (1 + 3 / ((q : ℝ) - 1))) := by
    rw [Finset.prod_filter_mul_prod_filter_not]
  rw [hsplit_p]
  have hcard_M : M.primeFactors.card ≤ T ^ 2 := by
    have hpow : 2 ^ M.primeFactors.card ≤ M := by
      calc 2 ^ M.primeFactors.card = ∏ _q ∈ M.primeFactors, 2 := (Finset.prod_const 2).symm
        _ ≤ ∏ q ∈ M.primeFactors, q :=
            Finset.prod_le_prod' fun q hq => (Nat.prime_of_mem_primeFactors hq).two_le
        _ ≤ M := Nat.le_of_dvd hM_pos (rad_dvd_self hM_pos.ne')
    have hlt : 2 ^ M.primeFactors.card < 2 ^ (T ^ 2) := lt_of_le_of_lt hpow hM_lt
    exact le_of_lt ((Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp hlt)
  have hlarge : ∏ q ∈ M.primeFactors.filter (fun q => ¬ (q ≤ T ^ 2)), (1 + 3 / ((q : ℝ) - 1)) ≤
      Real.exp 3 := by
    calc ∏ q ∈ M.primeFactors.filter (fun q => ¬ (q ≤ T ^ 2)), (1 + 3 / ((q : ℝ) - 1))
      _ ≤ ∏ _q ∈ M.primeFactors.filter (fun q => ¬ (q ≤ T ^ 2)), Real.exp (3 / ((T ^ 2 : ℕ) : ℝ)) := by
          apply Finset.prod_le_prod
          · intro q hq
            have hq2 : (2 : ℝ) ≤ (q : ℝ) := by
              exact_mod_cast (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1).two_le
            have : (0 : ℝ) < (q : ℝ) - 1 := by linarith
            positivity
          · intro q hq
            simp only [Finset.mem_filter] at hq
            have hq_ge : T ^ 2 ≤ q - 1 := by omega
            have hT2_pos : (0 : ℝ) < ((T ^ 2 : ℕ) : ℝ) := Nat.cast_pos.mpr (by nlinarith)
            have hle : 3 / ((q : ℝ) - 1) ≤ 3 / ((T ^ 2 : ℕ) : ℝ) := by
              apply div_le_div_of_nonneg_left (by norm_num) hT2_pos
              have : ((T ^ 2 : ℕ) : ℝ) ≤ ((q - 1 : ℕ) : ℝ) := by exact_mod_cast hq_ge
              rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hq.1).pos, Nat.cast_one] at this
              exact this
            linarith [Real.add_one_le_exp (3 / ((T ^ 2 : ℕ) : ℝ))]
      _ = Real.exp (((M.primeFactors.filter (fun q => ¬ (q ≤ T ^ 2))).card : ℝ) *
            (3 / ((T ^ 2 : ℕ) : ℝ))) := by
          rw [Finset.prod_const, ← Real.exp_nat_mul]
      _ ≤ Real.exp 3 := by
          apply Real.exp_le_exp.mpr
          have hc : ((M.primeFactors.filter (fun q => ¬ (q ≤ T ^ 2))).card : ℝ) ≤ ((T ^ 2 : ℕ) : ℝ) := by
            exact_mod_cast le_trans (Finset.card_le_card (Finset.filter_subset _ _)) hcard_M
          have hT2_pos : (0 : ℝ) < ((T ^ 2 : ℕ) : ℝ) := Nat.cast_pos.mpr (by nlinarith)
          calc ((M.primeFactors.filter (fun q => ¬ (q ≤ T ^ 2))).card : ℝ) * (3 / ((T ^ 2 : ℕ) : ℝ))
            _ ≤ ((T ^ 2 : ℕ) : ℝ) * (3 / ((T ^ 2 : ℕ) : ℝ)) :=
                mul_le_mul_of_nonneg_right hc (by positivity)
            _ = 3 := by field_simp
  have hsmall : ∏ q ∈ M.primeFactors.filter (fun q => q ≤ T ^ 2), (1 + 3 / ((q : ℝ) - 1)) ≤
      Real.exp (6 * C0) * Real.sqrt (T : ℝ) := by
    have hsub_p : M.primeFactors.filter (fun q => q ≤ T ^ 2) ⊆ primesUpTo (T ^ 2) := by
      intro q hq
      simp only [Finset.mem_filter, primesUpTo, Finset.mem_range] at hq ⊢
      exact ⟨by omega, Nat.prime_of_mem_primeFactors hq.1⟩
    have h1 : ∏ q ∈ M.primeFactors.filter (fun q => q ≤ T ^ 2), (1 + 3 / ((q : ℝ) - 1)) ≤
        Real.exp (6 * ∑ q ∈ primesUpTo (T ^ 2), (1 : ℝ) / (q : ℝ)) := by
      calc ∏ q ∈ M.primeFactors.filter (fun q => q ≤ T ^ 2), (1 + 3 / ((q : ℝ) - 1))
        _ ≤ ∏ q ∈ M.primeFactors.filter (fun q => q ≤ T ^ 2), Real.exp (6 / (q : ℝ)) := by
            apply Finset.prod_le_prod
            · intro q hq
              have hq2 : (2 : ℝ) ≤ (q : ℝ) := by
                exact_mod_cast (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1).two_le
              have : (0 : ℝ) < (q : ℝ) - 1 := by linarith
              positivity
            · intro q hq
              have hqp := Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1
              have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hqp.two_le
              have hle : 3 / ((q : ℝ) - 1) ≤ 6 / (q : ℝ) := by
                rw [div_le_div_iff₀ (by linarith) (by linarith)]; linarith
              linarith [Real.add_one_le_exp (6 / (q : ℝ))]
        _ = Real.exp (∑ q ∈ M.primeFactors.filter (fun q => q ≤ T ^ 2), 6 / (q : ℝ)) := by
            rw [Real.exp_sum]
        _ ≤ Real.exp (∑ q ∈ primesUpTo (T ^ 2), 6 / (q : ℝ)) := by
            apply Real.exp_le_exp.mpr
            exact Finset.sum_le_sum_of_subset_of_nonneg hsub_p (fun _ _ _ => by positivity)
        _ = Real.exp (6 * ∑ q ∈ primesUpTo (T ^ 2), (1 : ℝ) / (q : ℝ)) := by
            congr 1; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro q _; ring
    have hinv := hC0 (T ^ 2) (by nlinarith)
    have hlogT2 : Real.log ((T ^ 2 : ℕ) : ℝ) = 2 * Real.log (T : ℝ) := by
      push_cast; rw [Real.log_pow]; norm_num
    have h6 : 6 * ∑ q ∈ primesUpTo (T ^ 2), (1 : ℝ) / (q : ℝ) ≤
        6 * C0 + Real.log (T : ℝ) / 2 := by
      linarith [hinv, hlogT2]
    have hT_pos : (0 : ℝ) < (T : ℝ) := Nat.cast_pos.mpr (by omega)
    have hexp_sqrt : Real.exp (Real.log (T : ℝ) / 2) = Real.sqrt (T : ℝ) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hT_pos]; ring_nf
    calc ∏ q ∈ M.primeFactors.filter (fun q => q ≤ T ^ 2), (1 + 3 / ((q : ℝ) - 1))
      _ ≤ Real.exp (6 * ∑ q ∈ primesUpTo (T ^ 2), (1 : ℝ) / (q : ℝ)) := h1
      _ ≤ Real.exp (6 * C0 + Real.log (T : ℝ) / 2) := Real.exp_le_exp.mpr h6
      _ = Real.exp (6 * C0) * Real.sqrt (T : ℝ) := by rw [Real.exp_add, hexp_sqrt]
  have hlarge_nn : 0 ≤ ∏ q ∈ M.primeFactors.filter (fun q => ¬ (q ≤ T ^ 2)), (1 + 3 / ((q : ℝ) - 1)) :=
    Finset.prod_nonneg fun q hq => by
      have hq2 : (2 : ℝ) ≤ (q : ℝ) := by
        exact_mod_cast (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1).two_le
      have : (0 : ℝ) < (q : ℝ) - 1 := by linarith
      positivity
  calc (∏ q ∈ M.primeFactors.filter (fun q => q ≤ T ^ 2), (1 + 3 / ((q : ℝ) - 1))) *
        (∏ q ∈ M.primeFactors.filter (fun q => ¬ (q ≤ T ^ 2)), (1 + 3 / ((q : ℝ) - 1)))
    _ ≤ (Real.exp (6 * C0) * Real.sqrt (T : ℝ)) * Real.exp 3 :=
        mul_le_mul hsmall hlarge hlarge_nn (by positivity)
    _ = Real.exp (6 * C0 + 3) * Real.sqrt (T : ℝ) := by
        rw [mul_right_comm, ← Real.exp_add]

private noncomputable def romF (m : ℕ) : ℝ :=
  (((2 ^ m - 1 : ℕ) : ℝ) / (((2 ^ m - 1).totient : ℕ) : ℝ)) ^ 2

private noncomputable def romSqSum (m : ℕ) : ℝ :=
  ∑ d ∈ (2 ^ m - 1).divisors.filter Squarefree, romW d

private lemma romanoff_term_le (m : ℕ) (hm : 1 ≤ m) :
    romF m ≤ romSqSum m := by
  unfold romF romSqSum
  have hm_ne : 2 ^ m - 1 ≠ 0 := by
    have : 2 ≤ 2 ^ m := le_trans (by norm_num : 2 ≤ 2 ^ 1) (Nat.pow_le_pow_right (by norm_num) hm)
    omega
  have hsum_eq : ∑ d ∈ (2 ^ m - 1).divisors.filter Squarefree, romW d =
      ∏ q ∈ (2 ^ m - 1).primeFactors, (1 + romW q) := by
    rw [← rad_divisors_eq hm_ne,
        sum_divisors_of_squarefree (rad_squarefree _) romW romW_one (fun _ _ ha hb hc => romW_mul ha hb hc),
        rad_primeFactors_eq]
  rw [div_totient_eq_prod hm_ne, ← Finset.prod_pow, hsum_eq]
  apply Finset.prod_le_prod
  · intro _ _; positivity
  · intro q hq
    have hqp := Nat.prime_of_mem_primeFactors hq
    rw [romW_prime hqp]
    have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hqp.two_le
    have hq1_pos : (0 : ℝ) < (q : ℝ) - 1 := by linarith
    have heq1 : ((q : ℝ) / ((q : ℝ) - 1)) ^ 2 = 1 + (2 * (q : ℝ) - 1) / ((q : ℝ) - 1) ^ 2 := by
      field_simp; ring
    rw [heq1]
    have hcmp : (2 * (q : ℝ) - 1) / ((q : ℝ) - 1) ^ 2 ≤ 3 / ((q : ℝ) - 1) := by
      rw [div_le_div_iff₀ (sq_pos_of_pos hq1_pos) hq1_pos]; nlinarith
    linarith

private def romMall (K : ℕ) : ℕ := ∏ j ∈ Finset.Icc 1 K, (2 ^ j - 1)

private noncomputable def romDset (K : ℕ) : Finset ℕ :=
  (romMall K).divisors.filter (fun d => Squarefree d ∧ ord2 d ≤ K)

private lemma romanoff_swap_sum (K : ℕ) :
    ∑ m ∈ Finset.Icc 1 K, romSqSum m ≤
      (K : ℝ) * ∑ d ∈ romDset K, romW d / (ord2 d : ℝ) := by
  simp only [romSqSum]
  have hMall_pos : 0 < romMall K := Finset.prod_pos fun j hj => by
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    have : 2 ≤ 2 ^ j := le_trans (by norm_num : 2 ≤ 2 ^ 1) (Nat.pow_le_pow_right (by norm_num) hj1)
    omega
  have hMall_odd : Odd (romMall K) :=
    prod_two_pow_sub_one_odd (Finset.Icc 1 K) (fun j hj => (Finset.mem_Icc.mp hj).1)
  have hre : ∑ m ∈ Finset.Icc 1 K, ∑ d ∈ (2 ^ m - 1).divisors.filter Squarefree, romW d =
      ∑ d ∈ romDset K, (((Finset.Icc 1 K).filter (fun m => d ∣ 2 ^ m - 1)).card : ℝ) * romW d := by
    have h1 : ∀ m ∈ Finset.Icc 1 K,
        ∑ d ∈ (2 ^ m - 1).divisors.filter Squarefree, romW d =
        ∑ d ∈ romDset K, if d ∣ 2 ^ m - 1 then romW d else 0 := by
      intro m hm
      rw [← Finset.sum_filter]
      congr 1; ext d
      have hm_ne : 2 ^ m - 1 ≠ 0 := by
        have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
        have : 2 ≤ 2 ^ m := le_trans (by norm_num : 2 ≤ 2 ^ 1) (Nat.pow_le_pow_right (by norm_num) hm1)
        omega
      simp only [Finset.mem_filter, romDset, Nat.mem_divisors, hMall_pos.ne', hm_ne, ne_eq,
        not_false_eq_true, and_true]
      constructor
      · rintro ⟨hdvd, hsq⟩
        have hdvd_all : d ∣ romMall K := dvd_trans hdvd (Finset.dvd_prod_of_mem _ hm)
        have hord_le : ord2 d ≤ K :=
          le_trans (Nat.le_of_dvd (by have := (Finset.mem_Icc.mp hm).1; omega)
            (ord2_dvd_of_dvd_two_pow_sub_one hdvd)) (Finset.mem_Icc.mp hm).2
        exact ⟨⟨hdvd_all, hsq, hord_le⟩, hdvd⟩
      · rintro ⟨⟨_, hsq, _⟩, hdvd⟩; exact ⟨hdvd, hsq⟩
    rw [Finset.sum_congr rfl h1, Finset.sum_comm]
    apply Finset.sum_congr rfl; intro d _
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  rw [hre, Finset.mul_sum]
  apply Finset.sum_le_sum; intro d hd
  have hd_odd : Odd d := hMall_odd.of_dvd_nat (Nat.mem_divisors.mp (Finset.mem_filter.mp hd).1).1
  have hord_pos : 1 ≤ ord2 d := ord2_pos_of_odd hd_odd
  have hcnt : (((Finset.Icc 1 K).filter (fun m => d ∣ 2 ^ m - 1)).card : ℝ) ≤
      (K : ℝ) / (ord2 d : ℝ) := by
    have hsubm : (Finset.Icc 1 K).filter (fun m => d ∣ 2 ^ m - 1) ⊆
        (Finset.Icc 1 K).filter (fun m => ord2 d ∣ m) := by
      intro m hm; simp only [Finset.mem_filter] at hm ⊢
      exact ⟨hm.1, ord2_dvd_of_dvd_two_pow_sub_one hm.2⟩
    exact le_trans (by exact_mod_cast Finset.card_le_card hsubm) (card_multiples_Icc_le K (ord2 d) hord_pos)
  have hw_nn : 0 ≤ romW d := by unfold romW; positivity
  calc (((Finset.Icc 1 K).filter (fun m => d ∣ 2 ^ m - 1)).card : ℝ) * romW d
    _ ≤ ((K : ℝ) / (ord2 d : ℝ)) * romW d := mul_le_mul_of_nonneg_right hcnt hw_nn
    _ = (K : ℝ) * (romW d / (ord2 d : ℝ)) := by ring

private lemma romanoff_dyadic_slice (C0 : ℝ)
    (hC0 : ∀ Y : ℕ, 1 ≤ Y → ∑ p ∈ primesUpTo Y, (1 : ℝ) / (p : ℝ) ≤ C0 + Real.log (Y : ℝ) / 24)
    (Dset : Finset ℕ) (hD : ∀ d ∈ Dset, Odd d ∧ Squarefree d) (s : ℕ) :
    ∑ d ∈ Dset.filter (fun d => Nat.log 2 (ord2 d) = s), romW d / (ord2 d : ℝ) ≤
      2 * Real.exp (6 * C0 + 3) * (1 / Real.sqrt 2) ^ s := by
  set T := 2 ^ (s + 1)
  have hT2 : 2 ≤ T := le_trans (by norm_num : 2 ≤ 2 ^ 1) (Nat.pow_le_pow_right (by norm_num) (by omega))
  set MT := ∏ j ∈ Finset.Icc 1 (T - 1), (2 ^ j - 1)
  have hMT_pos : 0 < MT := Finset.prod_pos fun j hj => by
    have hj1 := (Finset.mem_Icc.mp hj).1
    have : 2 ≤ 2 ^ j := le_trans (by norm_num : 2 ≤ 2 ^ 1) (Nat.pow_le_pow_right (by norm_num) hj1)
    omega
  have hMT_lt : MT < 2 ^ (T ^ 2) := by
    calc MT = ∏ j ∈ Finset.Icc 1 (T - 1), (2 ^ j - 1) := rfl
      _ < ∏ _j ∈ Finset.Icc 1 (T - 1), 2 ^ T := by
          apply Finset.prod_lt_prod_of_nonempty
          · intro j hj; exact Nat.sub_pos_of_lt (by
              have := (Finset.mem_Icc.mp hj).1
              calc 1 < 2 ^ 1 := by norm_num
                _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) this)
          · intro j hj
            have hjT : j ≤ T - 1 := (Finset.mem_Icc.mp hj).2
            have : 2 ^ j ≤ 2 ^ T := Nat.pow_le_pow_right (by norm_num) (by omega)
            have : 1 ≤ 2 ^ j := Nat.one_le_two_pow
            omega
          · exact ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩⟩
      _ = (2 ^ T) ^ (T - 1) := by rw [Finset.prod_const]; simp
      _ = 2 ^ (T * (T - 1)) := by rw [← pow_mul]
      _ ≤ 2 ^ (T ^ 2) := Nat.pow_le_pow_right (by norm_num) (by rw [sq]; exact Nat.mul_le_mul_left T (Nat.sub_le T 1))
  have hsub_MT : Dset.filter (fun d => Nat.log 2 (ord2 d) = s) ⊆ MT.divisors.filter Squarefree := by
    intro d hd
    simp only [Finset.mem_filter, Nat.mem_divisors] at hd ⊢
    obtain ⟨hd_odd, hd_sq⟩ := hD d hd.1
    have hord_pos : 1 ≤ ord2 d := ord2_pos_of_odd hd_odd
    have hord_lt : ord2 d < T := by
      have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (ord2 d)
      rw [hd.2] at this; exact this
    have hmem_Icc : ord2 d ∈ Finset.Icc 1 (T - 1) := Finset.mem_Icc.mpr ⟨hord_pos, by omega⟩
    have hdvd_MT : d ∣ MT := dvd_trans (dvd_two_pow_ord2_sub_one d) (Finset.dvd_prod_of_mem _ hmem_Icc)
    exact ⟨⟨hdvd_MT, hMT_pos.ne'⟩, hd_sq⟩
  have hdiv_ge : ∀ d ∈ Dset.filter (fun d => Nat.log 2 (ord2 d) = s),
      romW d / (ord2 d : ℝ) ≤ (2 / (T : ℝ)) * romW d := by
    intro d hd
    simp only [Finset.mem_filter] at hd
    have hord_pos : 1 ≤ ord2 d := ord2_pos_of_odd (hD d hd.1).1
    have hord_ge : 2 ^ s ≤ ord2 d := by
      have := Nat.pow_log_le_self 2 (by omega : ord2 d ≠ 0)
      rw [hd.2] at this; exact this
    have h2s : (T : ℝ) / 2 ≤ (ord2 d : ℝ) := by
      have hT_eq : T = 2 * 2 ^ s := by simp [T, pow_succ, mul_comm]
      have hR : (T : ℝ) = 2 * ((2 ^ s : ℕ) : ℝ) := by exact_mod_cast hT_eq
      have hgeR : ((2 ^ s : ℕ) : ℝ) ≤ (ord2 d : ℝ) := by exact_mod_cast hord_ge
      linarith
    have hT_pos : (0 : ℝ) < (T : ℝ) := Nat.cast_pos.mpr (by omega)
    have hord_posR : (0 : ℝ) < (ord2 d : ℝ) := Nat.cast_pos.mpr hord_pos
    have hw_nn : 0 ≤ romW d := by unfold romW; positivity
    rw [div_eq_mul_inv, mul_comm (2 / (T : ℝ))]
    apply mul_le_mul_of_nonneg_left _ hw_nn
    rw [inv_eq_one_div, div_le_div_iff₀ hord_posR hT_pos]; linarith
  have hsum_MT : ∑ d ∈ MT.divisors.filter Squarefree, romW d =
      ∏ q ∈ MT.primeFactors, (1 + 3 / ((q : ℝ) - 1)) := by
    rw [← rad_divisors_eq hMT_pos.ne',
        sum_divisors_of_squarefree (rad_squarefree MT) romW romW_one (fun _ _ ha hb hc => romW_mul ha hb hc),
        rad_primeFactors_eq]
    apply Finset.prod_congr rfl; intro q hq
    rw [romW_prime (Nat.prime_of_mem_primeFactors hq)]
  have hprod_bd := romanoff_prod_bound C0 hC0 T hT2 MT hMT_pos hMT_lt
  have hsqrt_T : Real.sqrt (T : ℝ) / (T : ℝ) = (1 / Real.sqrt 2) ^ (s + 1) := by
    have hT_eq : (T : ℝ) = (2 : ℝ) ^ (s + 1) := by exact_mod_cast (rfl : T = 2 ^ (s + 1))
    have h2_eq : (2 : ℝ) ^ (s + 1) = (Real.sqrt 2) ^ (s + 1) * (Real.sqrt 2) ^ (s + 1) := by
      rw [← mul_pow, Real.mul_self_sqrt (by norm_num)]
    have hsqrt_pow : Real.sqrt ((2 : ℝ) ^ (s + 1)) = (Real.sqrt 2) ^ (s + 1) := by
      rw [h2_eq, ← sq, Real.sqrt_sq (by positivity)]
    have hne : (Real.sqrt 2) ^ (s + 1) ≠ 0 := by positivity
    rw [hT_eq, hsqrt_pow, h2_eq, div_mul_eq_div_div, div_self hne, one_div_pow]
  have hle_s : (1 / Real.sqrt 2) ^ (s + 1) ≤ (1 / Real.sqrt 2) ^ s := by
    rw [pow_succ]
    have h1 : 1 / Real.sqrt 2 ≤ 1 := by
      rw [div_le_one (Real.sqrt_pos.mpr (by norm_num))]
      exact Real.one_le_sqrt.mpr (by norm_num)
    exact mul_le_of_le_one_right (by positivity) h1
  calc ∑ d ∈ Dset.filter (fun d => Nat.log 2 (ord2 d) = s), romW d / (ord2 d : ℝ)
    _ ≤ ∑ d ∈ Dset.filter (fun d => Nat.log 2 (ord2 d) = s), (2 / (T : ℝ)) * romW d :=
        Finset.sum_le_sum hdiv_ge
    _ = (2 / (T : ℝ)) * ∑ d ∈ Dset.filter (fun d => Nat.log 2 (ord2 d) = s), romW d := by
        rw [← Finset.mul_sum]
    _ ≤ (2 / (T : ℝ)) * ∑ d ∈ MT.divisors.filter Squarefree, romW d := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Finset.sum_le_sum_of_subset_of_nonneg hsub_MT (fun _ _ _ => by unfold romW; positivity)
    _ = (2 / (T : ℝ)) * ∏ q ∈ MT.primeFactors, (1 + 3 / ((q : ℝ) - 1)) := by rw [hsum_MT]
    _ ≤ (2 / (T : ℝ)) * (Real.exp (6 * C0 + 3) * Real.sqrt (T : ℝ)) :=
        mul_le_mul_of_nonneg_left hprod_bd (by positivity)
    _ = 2 * Real.exp (6 * C0 + 3) * (Real.sqrt (T : ℝ) / (T : ℝ)) := by ring
    _ = 2 * Real.exp (6 * C0 + 3) * (1 / Real.sqrt 2) ^ (s + 1) := by rw [hsqrt_T]
    _ ≤ 2 * Real.exp (6 * C0 + 3) * (1 / Real.sqrt 2) ^ s :=
        mul_le_mul_of_nonneg_left hle_s (by positivity)

private lemma romanoff_geom_sum (K : ℕ) :
    ∑ s ∈ Finset.range (K + 1), (1 / Real.sqrt 2) ^ s ≤ 4 := by
  have hr_lt : (1 / Real.sqrt 2) < 1 := by
    rw [div_lt_one (Real.sqrt_pos.mpr (by norm_num))]
    rw [← Real.sqrt_one]; exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  rw [geom_sum_eq hr_lt.ne]
  have hneg : 1 / Real.sqrt 2 - 1 ≠ 0 := by linarith
  have hpos : 0 < 1 - 1 / Real.sqrt 2 := by linarith
  have hrew : ((1 / Real.sqrt 2) ^ (K + 1) - 1) / (1 / Real.sqrt 2 - 1) =
      (1 - (1 / Real.sqrt 2) ^ (K + 1)) / (1 - 1 / Real.sqrt 2) := by
    rw [div_eq_div_iff hneg hpos.ne']; ring
  rw [hrew]
  have hden_ge : (1 : ℝ) / 4 ≤ 1 - 1 / Real.sqrt 2 := by
    have hsqrt2 : (4 : ℝ) / 3 ≤ Real.sqrt 2 := by
      rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
    have hinv : 1 / Real.sqrt 2 ≤ 3 / 4 := by
      rw [div_le_div_iff₀ (Real.sqrt_pos.mpr (by norm_num)) (by norm_num)]; linarith
    linarith
  have hnum_le : 1 - (1 / Real.sqrt 2) ^ (K + 1) ≤ 1 := by
    have : 0 ≤ (1 / Real.sqrt 2) ^ (K + 1) := by positivity
    linarith
  calc (1 - (1 / Real.sqrt 2) ^ (K + 1)) / (1 - 1 / Real.sqrt 2)
    _ ≤ 1 / (1 - 1 / Real.sqrt 2) := div_le_div_of_nonneg_right hnum_le hpos.le
    _ ≤ 1 / (1 / 4) := div_le_div_of_nonneg_left zero_le_one (by norm_num) hden_ge
    _ = 4 := by norm_num

private lemma romanoff_sum_bound :
    ∃ C_R : ℝ, 0 < C_R ∧ ∀ K : ℕ, 1 ≤ K →
      ∑ m ∈ Finset.Icc 1 K, romF m ≤ C_R * (K : ℝ) := by
  rcases sum_inv_prime_le with ⟨C0, _, hC0⟩
  let C_const : ℝ := 6 * C0 + 3
  refine ⟨8 * Real.exp C_const, by positivity, fun K _ => ?_⟩
  have hMall_odd : Odd (romMall K) :=
    prod_two_pow_sub_one_odd (Finset.Icc 1 K) (fun j hj => (Finset.mem_Icc.mp hj).1)
  have hD : ∀ d ∈ romDset K, Odd d ∧ Squarefree d := fun d hd => by
    simp only [romDset, Finset.mem_filter, Nat.mem_divisors] at hd
    exact ⟨hMall_odd.of_dvd_nat hd.1.1, hd.2.1⟩
  have hmaps : ∀ d ∈ romDset K, Nat.log 2 (ord2 d) ∈ Finset.range (K + 1) := fun d hd => by
    simp only [romDset, Finset.mem_filter] at hd
    rw [Finset.mem_range]
    have : Nat.log 2 (ord2 d) ≤ ord2 d := Nat.log_le_self 2 (ord2 d)
    omega
  have hdyadic : ∑ d ∈ romDset K, romW d / (ord2 d : ℝ) ≤ 8 * Real.exp C_const := by
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    calc ∑ s ∈ Finset.range (K + 1), ∑ d ∈ (romDset K).filter (fun d => Nat.log 2 (ord2 d) = s),
          romW d / (ord2 d : ℝ)
      _ ≤ ∑ s ∈ Finset.range (K + 1), 2 * Real.exp C_const * (1 / Real.sqrt 2) ^ s :=
          Finset.sum_le_sum fun s _ => romanoff_dyadic_slice C0 hC0 (romDset K) hD s
      _ = 2 * Real.exp C_const * ∑ s ∈ Finset.range (K + 1), (1 / Real.sqrt 2) ^ s := by
          rw [← Finset.mul_sum]
      _ ≤ 2 * Real.exp C_const * 4 := mul_le_mul_of_nonneg_left (romanoff_geom_sum K) (by positivity)
      _ = 8 * Real.exp C_const := by ring
  calc ∑ m ∈ Finset.Icc 1 K, romF m
    _ ≤ ∑ m ∈ Finset.Icc 1 K, romSqSum m :=
        Finset.sum_le_sum fun m hm => romanoff_term_le m (Finset.mem_Icc.mp hm).1
    _ ≤ (K : ℝ) * ∑ d ∈ romDset K, romW d / (ord2 d : ℝ) := romanoff_swap_sum K
    _ ≤ (K : ℝ) * (8 * Real.exp C_const) :=
        mul_le_mul_of_nonneg_left hdyadic (Nat.cast_nonneg K)
    _ = 8 * Real.exp C_const * (K : ℝ) := by ring

private lemma romanoff_second_moment_identity (K : ℕ) (P A : Finset ℕ)
    (hmaps : ∀ rp ∈ Finset.range K ×ˢ P, rp.2 + (2 ^ (rp.1 + 1) - 1) ∈ A) :
    ∑ n ∈ A, (((Finset.range K ×ˢ P).filter (fun rp => rp.2 + (2 ^ (rp.1 + 1) - 1) = n)).card : ℝ) ^ 2 =
      ∑ r1 ∈ Finset.range K, ∑ r2 ∈ Finset.range K,
        ((P.filter (fun p1 => ∃ p2 ∈ P, p1 + (2 ^ (r1 + 1) - 1) = p2 + (2 ^ (r2 + 1) - 1))).card : ℝ) := by
  let φ : ℕ × ℕ → ℕ := fun rp => rp.2 + (2 ^ (rp.1 + 1) - 1)
  set Q := ((Finset.range K ×ˢ P) ×ˢ (Finset.range K ×ˢ P)).filter (fun q => φ q.1 = φ q.2)
  have hLHS : ∑ n ∈ A, (((Finset.range K ×ˢ P).filter (fun rp => φ rp = n)).card) ^ 2 = Q.card := by
    have hmapsQ : ∀ q ∈ Q, φ q.1 ∈ A := fun q hq =>
      hmaps q.1 (Finset.mem_product.mp (Finset.mem_filter.mp hq).1).1
    have hQsum : Q.card = ∑ _q ∈ Q, (1 : ℕ) := by simp
    rw [hQsum, ← Finset.sum_fiberwise_of_maps_to hmapsQ (fun _ => (1 : ℕ))]
    apply Finset.sum_congr rfl; intro n _
    rw [Finset.sum_const, smul_eq_mul, mul_one, sq, ← Finset.card_product]
    congr 1; ext q
    simp only [Q, Finset.mem_filter, Finset.mem_product]
    constructor
    · rintro ⟨⟨hq1, h1n⟩, ⟨hq2, h2n⟩⟩; exact ⟨⟨⟨hq1, hq2⟩, h1n.trans h2n.symm⟩, h1n⟩
    · rintro ⟨⟨⟨hq1, hq2⟩, h12⟩, h1n⟩; exact ⟨⟨hq1, h1n⟩, ⟨hq2, h12.symm.trans h1n⟩⟩
  have hRHS : ∑ r1 ∈ Finset.range K, ∑ r2 ∈ Finset.range K,
      (P.filter (fun p1 => ∃ p2 ∈ P, p1 + (2 ^ (r1 + 1) - 1) = p2 + (2 ^ (r2 + 1) - 1))).card = Q.card := by
    let proj : (ℕ × ℕ) × (ℕ × ℕ) → ℕ × ℕ := fun q => (q.1.1, q.2.1)
    have hmapsP : ∀ q ∈ Q, proj q ∈ Finset.range K ×ˢ Finset.range K := by
      intro q hq
      simp only [Q, Finset.mem_filter, Finset.mem_product] at hq
      exact Finset.mem_product.mpr ⟨hq.1.1.1, hq.1.2.1⟩
    have hQsum : Q.card = ∑ _q ∈ Q, (1 : ℕ) := by simp
    rw [hQsum, ← Finset.sum_fiberwise_of_maps_to hmapsP (fun _ => (1 : ℕ))]
    simp only [Finset.sum_const, smul_eq_mul, mul_one, Finset.sum_product]
    apply Finset.sum_congr rfl; intro r1 hr1
    apply Finset.sum_congr rfl; intro r2 hr2
    apply Finset.card_bij (fun p1 _ => ((r1, p1), (r2, p1 + (2 ^ (r1 + 1) - 1) - (2 ^ (r2 + 1) - 1))))
    · intro p1 hp1
      simp only [Finset.mem_filter] at hp1 ⊢
      rcases hp1.2 with ⟨p2, hp2P, heq⟩
      have hp2_eq : p1 + (2 ^ (r1 + 1) - 1) - (2 ^ (r2 + 1) - 1) = p2 := by omega
      rw [hp2_eq]
      simp only [Q, proj, Finset.mem_filter, Finset.mem_product, φ]
      exact ⟨⟨⟨⟨hr1, hp1.1⟩, ⟨hr2, hp2P⟩⟩, heq⟩, trivial⟩
    · intro a1 _ a2 _ heq; exact congrArg (fun x => x.1.2) heq
    · intro q hq
      simp only [Finset.mem_filter, Q, proj, Finset.mem_product, Prod.mk.injEq, φ] at hq
      rcases hq with ⟨⟨⟨⟨_, hp1⟩, ⟨_, hp2⟩⟩, hφeq⟩, rfl, rfl⟩
      refine ⟨q.1.2, Finset.mem_filter.mpr ⟨hp1, ⟨q.2.2, hp2, hφeq⟩⟩, ?_⟩
      have hq2 : q.1.2 + (2 ^ (q.1.1 + 1) - 1) - (2 ^ (q.2.1 + 1) - 1) = q.2.2 := by omega
      ext <;> simp [hq2]
  have hnat : ∑ n ∈ A, (((Finset.range K ×ˢ P).filter (fun rp => φ rp = n)).card) ^ 2 =
      ∑ r1 ∈ Finset.range K, ∑ r2 ∈ Finset.range K,
        (P.filter (fun p1 => ∃ p2 ∈ P, p1 + (2 ^ (r1 + 1) - 1) = p2 + (2 ^ (r2 + 1) - 1))).card :=
    hLHS.trans hRHS.symm
  exact_mod_cast hnat

private lemma ten6_pow4_le_div2 {N : ℕ} (hN : 2 * 1000000 ^ 4 ≤ N) :
    1000000 ^ 4 ≤ N / 2 :=
  (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).mpr (by rw [mul_comm]; exact hN)

private lemma two_pow30_le_two_ten6_pow4 : 2 ^ 30 ≤ 2 * 1000000 ^ 4 := by
  have h10 : 2 ^ 10 ≤ 1000000 := by norm_num
  have h30 : 2 ^ 30 ≤ 1000000 ^ 3 := by
    calc 2 ^ 30 = (2 ^ 10) ^ 3 := by norm_num
      _ ≤ 1000000 ^ 3 := Nat.pow_le_pow_left h10 3
  have h34 : 1000000 ^ 3 ≤ 1000000 ^ 4 :=
    Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have h42 : 1000000 ^ 4 ≤ 2 * 1000000 ^ 4 := Nat.le_mul_of_pos_left _ (by norm_num)
  exact le_trans h30 (le_trans h34 h42)

private noncomputable def pairCount (N r1 r2 : ℕ) : ℝ :=
  let P := (Finset.Ioc (N / 20) (N / 2)).filter Nat.Prime
  ((P.filter (fun p1 => ∃ p2 ∈ P, p1 + (2 ^ (r1 + 1) - 1) = p2 + (2 ^ (r2 + 1) - 1))).card : ℝ)

private lemma pairCount_symm (N r1 r2 : ℕ) : pairCount N r1 r2 = pairCount N r2 r1 := by
  set P := (Finset.Ioc (N / 20) (N / 2)).filter Nat.Prime
  change ((P.filter (fun p1 => ∃ p2 ∈ P, p1 + (2 ^ (r1 + 1) - 1) = p2 + (2 ^ (r2 + 1) - 1))).card : ℝ) =
    ((P.filter (fun p1 => ∃ p2 ∈ P, p1 + (2 ^ (r2 + 1) - 1) = p2 + (2 ^ (r1 + 1) - 1))).card : ℝ)
  congr 1
  apply Finset.card_bij (fun p1 _ => p1 + (2 ^ (r1 + 1) - 1) - (2 ^ (r2 + 1) - 1))
  · intro p1 hp1
    simp only [Finset.mem_filter] at hp1 ⊢
    rcases hp1.2 with ⟨p2, hp2, heq⟩
    have hp2_eq : p1 + (2 ^ (r1 + 1) - 1) - (2 ^ (r2 + 1) - 1) = p2 := by omega
    rw [hp2_eq]; exact ⟨hp2, p1, hp1.1, heq.symm⟩
  · intro a1 ha1 a2 ha2 heq
    simp only [Finset.mem_filter] at ha1 ha2
    rcases ha1.2 with ⟨_, _, e1⟩; rcases ha2.2 with ⟨_, _, e2⟩; omega
  · intro p2 hp2
    simp only [Finset.mem_filter] at hp2
    rcases hp2.2 with ⟨p1, hp1, heq⟩
    exact ⟨p1, Finset.mem_filter.mpr ⟨hp1, p2, hp2.1, heq.symm⟩, by omega⟩

private lemma pairCount_le_shifted (N r1 r2 : ℕ) (hlt : r1 < r2) :
    pairCount N r1 r2 ≤
      (((Finset.Icc 1 (N / 2)).filter
        (fun p => p.Prime ∧ (p + 2 ^ (r1 + 1) * (2 ^ (r2 - r1) - 1)).Prime)).card : ℝ) := by
  rw [pairCount_symm]
  simp only [pairCount]
  set P := (Finset.Ioc (N / 20) (N / 2)).filter Nat.Prime
  set h := 2 ^ (r1 + 1) * (2 ^ (r2 - r1) - 1)
  have hh_diff : 2 ^ (r2 + 1) - 2 ^ (r1 + 1) = h := by
    have hpow : 2 ^ (r2 + 1) = 2 ^ (r1 + 1) * 2 ^ (r2 - r1) := by
      rw [← pow_add]; congr 1; omega
    rw [hpow, show h = 2 ^ (r1 + 1) * (2 ^ (r2 - r1) - 1) from rfl, Nat.mul_sub_left_distrib, mul_one]
  have hsub : P.filter (fun p2 => ∃ p1 ∈ P, p2 + (2 ^ (r2 + 1) - 1) = p1 + (2 ^ (r1 + 1) - 1)) ⊆
      (Finset.Icc 1 (N / 2)).filter (fun p => p.Prime ∧ (p + h).Prime) := by
    intro p2 hp2
    simp only [Finset.mem_filter, P, Finset.mem_Ioc, Finset.mem_Icc] at hp2 ⊢
    rcases hp2 with ⟨⟨⟨hlo, hhi⟩, hp2p⟩, ⟨p1, ⟨_, hp1p⟩, heq⟩⟩
    have h1 : 1 ≤ 2 ^ (r1 + 1) := Nat.one_le_two_pow
    have h2 : 2 ^ (r1 + 1) ≤ 2 ^ (r2 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hp2h : p2 + h = p1 := by omega
    exact ⟨⟨by omega, hhi⟩, hp2p, hp2h ▸ hp1p⟩
  exact_mod_cast Finset.card_le_card hsub

private lemma totient_ratio_two_pow_mul (r1 m : ℕ) (hm1 : 1 ≤ m) :
    ((2 ^ (r1 + 1) * (2 ^ m - 1) : ℕ) : ℝ) /
      (((2 ^ (r1 + 1) * (2 ^ m - 1)).totient : ℕ) : ℝ) =
      2 * (((2 ^ m - 1 : ℕ) : ℝ) / (((2 ^ m - 1).totient : ℕ) : ℝ)) := by
  have h2m_gt1 : 1 < 2 ^ m := by
    calc 1 < 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm1
  have hodd : Odd (2 ^ m - 1) := by
    rcases even_iff_two_dvd.mpr (dvd_pow_self 2 (by omega : m ≠ 0)) with ⟨c, hc⟩
    exact ⟨c - 1, by omega⟩
  have hcop : (2 ^ (r1 + 1)).Coprime (2 ^ m - 1) :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hodd)
  have htot_mul : (2 ^ (r1 + 1) * (2 ^ m - 1)).totient = (2 ^ (r1 + 1)).totient * (2 ^ m - 1).totient :=
    Nat.totient_mul hcop
  have htot_2 : (2 ^ (r1 + 1)).totient = 2 ^ r1 := by
    rw [Nat.totient_prime_pow Nat.prime_two (by omega)]; simp
  have h2r_ne : ((2 : ℝ) ^ r1) ≠ 0 := by positivity
  have htot_ne : (((2 ^ m - 1).totient : ℕ) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr (by omega)).ne'
  have hcast_h : ((2 ^ (r1 + 1) * (2 ^ m - 1) : ℕ) : ℝ) = (2 : ℝ) ^ r1 * 2 * ((2 ^ m - 1 : ℕ) : ℝ) := by
    have : 2 ^ (r1 + 1) * (2 ^ m - 1) = 2 ^ r1 * 2 * (2 ^ m - 1) := by simp [pow_succ]
    exact_mod_cast this
  have hcast_t : (((2 ^ (r1 + 1) * (2 ^ m - 1)).totient : ℕ) : ℝ) =
      (2 : ℝ) ^ r1 * (((2 ^ m - 1).totient : ℕ) : ℝ) := by
    rw [htot_mul, htot_2]; push_cast; rfl
  rw [hcast_h, hcast_t]
  field_simp

private lemma log_half_ge (N : ℕ) (hN : 2 ^ 30 ≤ N) :
    0.9 * Real.log (N : ℝ) ≤ Real.log ((N / 2 : ℕ) : ℝ) := by
  have hlogN_ge : 20 ≤ Real.log (N : ℝ) := by
    have h2 : (2 : ℝ) ^ (30 : ℕ) ≤ (N : ℝ) := by exact_mod_cast hN
    have h1 := Real.log_le_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ (30 : ℕ)) h2
    rw [Real.log_pow] at h1; norm_num at h1
    linarith [Real.log_two_gt_d9]
  have h3 : (N : ℝ) ≤ 3 * ((N / 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : N ≤ 3 * (N / 2))
  have hlog3 : Real.log (3 : ℝ) ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num); linarith
  have h1 := Real.log_le_log (Nat.cast_pos.mpr (by omega)) h3
  rw [Real.log_mul (by norm_num) (Nat.cast_pos.mpr (by omega)).ne'] at h1
  linarith

private lemma pairCount_offdiag_step1 (N r1 r2 : ℕ) (hN : 2 * 1000000 ^ 4 ≤ N) (hlt : r1 < r2) :
    pairCount N r1 r2 ≤
      200 * ((N / 2 : ℕ) : ℝ) / (Real.log ((N / 2 : ℕ) : ℝ)) ^ 2 *
        (((2 ^ (r1 + 1) * (2 ^ (r2 - r1) - 1) : ℕ) : ℝ) /
          (((2 ^ (r1 + 1) * (2 ^ (r2 - r1) - 1)).totient : ℕ) : ℝ)) ^ 2 := by
  have hm1 : 1 ≤ r2 - r1 := Nat.sub_pos_of_lt hlt
  have h2m_gt1 : 1 < 2 ^ (r2 - r1) :=
    lt_of_lt_of_le (by norm_num : 1 < 2 ^ 1) (Nat.pow_le_pow_right (by norm_num) hm1)
  have hh_pos : 0 < 2 ^ (r1 + 1) * (2 ^ (r2 - r1) - 1) :=
    Nat.mul_pos (Nat.two_pow_pos _) (Nat.sub_pos_of_lt h2m_gt1)
  have hh_even : Even (2 ^ (r1 + 1) * (2 ^ (r2 - r1) - 1)) :=
    even_iff_two_dvd.mpr (dvd_mul_of_dvd_left (dvd_pow_self 2 (Nat.succ_ne_zero r1)) _)
  exact le_trans (pairCount_le_shifted N r1 r2 hlt)
    (selberg_shifted_primes (N / 2) (2 ^ (r1 + 1) * (2 ^ (r2 - r1) - 1))
      (ten6_pow4_le_div2 hN) hh_pos hh_even)

private lemma pairCount_offdiag_coeff (N : ℕ) (hN_ge_2_30 : 2 ^ 30 ≤ N) :
    200 * ((N / 2 : ℕ) : ℝ) / (Real.log ((N / 2 : ℕ) : ℝ)) ^ 2 * 4 ≤
      2000 * (N : ℝ) / (Real.log (N : ℝ)) ^ 2 := by
  have hlogN_pos : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hlog_half_ge : 0.9 * Real.log (N : ℝ) ≤ Real.log ((N / 2 : ℕ) : ℝ) := log_half_ge N hN_ge_2_30
  have hN2_le : ((N / 2 : ℕ) : ℝ) ≤ (N : ℝ) / 2 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
    exact_mod_cast Nat.div_mul_le_self N 2
  have hsq_log : (0.9 * Real.log (N : ℝ)) ^ 2 ≤ (Real.log ((N / 2 : ℕ) : ℝ)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hlog_half_ge 2
  calc 200 * ((N / 2 : ℕ) : ℝ) / (Real.log ((N / 2 : ℕ) : ℝ)) ^ 2 * 4
    _ ≤ 200 * ((N : ℝ) / 2) / (Real.log ((N / 2 : ℕ) : ℝ)) ^ 2 * 4 := by
        have h1 := div_le_div_of_nonneg_right
          (show 200 * ((N / 2 : ℕ) : ℝ) ≤ 200 * ((N : ℝ) / 2) by linarith)
          (sq_nonneg (Real.log ((N / 2 : ℕ) : ℝ)))
        linarith
    _ ≤ 200 * ((N : ℝ) / 2) / (0.9 * Real.log (N : ℝ)) ^ 2 * 4 := by
        have h1 := div_le_div_of_nonneg_left (by positivity : 0 ≤ 200 * ((N : ℝ) / 2))
          (sq_pos_of_pos (by positivity)) hsq_log
        linarith
    _ = (400 / 0.81) * (N : ℝ) / (Real.log (N : ℝ)) ^ 2 := by ring
    _ ≤ 2000 * (N : ℝ) / (Real.log (N : ℝ)) ^ 2 := by
        apply div_le_div_of_nonneg_right _ (sq_nonneg _)
        have : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N; linarith

private lemma pairCount_offdiag_bound (N r1 r2 : ℕ) (hN : 2 * 1000000 ^ 4 ≤ N) (hlt : r1 < r2) :
    pairCount N r1 r2 ≤
      2000 * (N : ℝ) / (Real.log (N : ℝ)) ^ 2 * romF (r2 - r1) := by
  have hm1 : 1 ≤ r2 - r1 := Nat.sub_pos_of_lt hlt
  have hstep12 := pairCount_offdiag_step1 N r1 r2 hN hlt
  have hcoeff := pairCount_offdiag_coeff N (le_trans two_pow30_le_two_ten6_pow4 hN)
  clear hN
  rw [totient_ratio_two_pow_mul r1 (r2 - r1) hm1] at hstep12
  have hsq : (2 * (((2 ^ (r2 - r1) - 1 : ℕ) : ℝ) / (((2 ^ (r2 - r1) - 1).totient : ℕ) : ℝ))) ^ 2 =
      4 * romF (r2 - r1) := by
    rw [mul_pow, show (2 : ℝ) ^ 2 = 4 by norm_num]; rfl
  rw [hsq, ← mul_assoc] at hstep12
  exact le_trans hstep12 (mul_le_mul_of_nonneg_right hcoeff (sq_nonneg _))

private lemma romanoff_K_bounds (N : ℕ) (hN : 2 ^ 30 ≤ N) :
    let K := Nat.log 2 (N / 20)
    1 ≤ K ∧ 0.5 * Real.log (N : ℝ) ≤ (K : ℝ) ∧ (K : ℝ) ≤ 2 * Real.log (N : ℝ) := by
  intro K
  have hlogN_ge : 20 ≤ Real.log (N : ℝ) := by
    have h2 : (2 : ℝ) ^ (30 : ℕ) ≤ (N : ℝ) := by exact_mod_cast hN
    have h := Real.log_le_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ (30 : ℕ)) h2
    rw [Real.log_pow] at h; norm_num at h
    linarith [Real.log_two_gt_d9]
  have hK_pow_le : 2 ^ K ≤ N / 20 := Nat.pow_log_le_self 2 (by omega)
  have hK_pow_gt : N / 20 < 2 ^ (K + 1) := Nat.lt_pow_succ_log_self (by norm_num) (N / 20)
  have hK_ge_1 : 1 ≤ K := Nat.le_log_of_pow_le (by norm_num) (by omega : 2 ^ 1 ≤ N / 20)
  have hK_lower : 0.5 * Real.log (N : ℝ) ≤ (K : ℝ) := by
    have h1 : (N : ℝ) / 21 ≤ ((N / 20 : ℕ) : ℝ) := by
      rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 21)]
      exact_mod_cast (by omega : N ≤ (N / 20) * 21)
    have h2 : (N : ℝ) / 21 < (2 : ℝ) ^ (K + 1) := lt_of_le_of_lt h1 (by exact_mod_cast hK_pow_gt)
    have hlog := Real.log_le_log (by positivity) h2.le
    rw [Real.log_div (Nat.cast_pos.mpr (by omega)).ne' (by norm_num), Real.log_pow] at hlog
    have hlog21 : Real.log 21 ≤ 3.5 := by
      have h1' := Real.log_le_log (by norm_num : (0 : ℝ) < 21) (show (21 : ℝ) ≤ (2 : ℝ) ^ (5 : ℕ) by norm_num)
      rw [Real.log_pow] at h1'; norm_num at h1'
      linarith [Real.log_two_lt_d9]
    push_cast at hlog
    nlinarith [Real.log_two_lt_d9]
  have hK_upper : (K : ℝ) ≤ 2 * Real.log (N : ℝ) := by
    have h1 : (2 : ℝ) ^ K ≤ (N : ℝ) := by
      exact_mod_cast le_trans hK_pow_le (Nat.div_le_self N 20)
    have hlog := Real.log_le_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ K) h1
    rw [Real.log_pow] at hlog
    nlinarith [Real.log_two_gt_d9]
  exact ⟨hK_ge_1, hK_lower, hK_upper⟩

private lemma romanoff_split_tri (N K : ℕ) :
    ∑ r1 ∈ Finset.range K, ∑ r2 ∈ Finset.range K, pairCount N r1 r2 =
      (∑ r ∈ Finset.range K, pairCount N r r) +
        2 * ∑ r1 ∈ Finset.range K, ∑ r2 ∈ (Finset.range K).filter (fun r2 => r1 < r2), pairCount N r1 r2 := by
  have h1 : ∀ r1 ∈ Finset.range K, ∑ r2 ∈ Finset.range K, pairCount N r1 r2 =
      pairCount N r1 r1 +
      (∑ r2 ∈ (Finset.range K).filter (fun r2 => r1 < r2), pairCount N r1 r2) +
      (∑ r2 ∈ (Finset.range K).filter (fun r2 => r2 < r1), pairCount N r1 r2) := by
    intro r1 hr1
    have hdisj1 : Disjoint ({r1} : Finset ℕ) ((Finset.range K).filter (fun r2 => r1 < r2)) := by simp
    have hdisj2 : Disjoint ({r1} ∪ (Finset.range K).filter (fun r2 => r1 < r2))
        ((Finset.range K).filter (fun r2 => r2 < r1)) := by
      rw [Finset.disjoint_left]; intro x hx1 hx2
      simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_filter] at hx1 hx2; omega
    have hunion : Finset.range K = ({r1} ∪ (Finset.range K).filter (fun r2 => r1 < r2)) ∪
        (Finset.range K).filter (fun r2 => r2 < r1) := by
      ext x
      simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_filter, Finset.mem_range]
      rw [Finset.mem_range] at hr1; omega
    conv_lhs => rw [hunion]
    rw [Finset.sum_union hdisj2, Finset.sum_union hdisj1, Finset.sum_singleton]
  rw [Finset.sum_congr rfl h1]
  simp_rw [Finset.sum_add_distrib]
  have hlower : ∑ r1 ∈ Finset.range K, ∑ r2 ∈ (Finset.range K).filter (fun r2 => r2 < r1), pairCount N r1 r2 =
      ∑ r1 ∈ Finset.range K, ∑ r2 ∈ (Finset.range K).filter (fun r2 => r1 < r2), pairCount N r1 r2 := by
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro r2 _
    apply Finset.sum_congr rfl; intro r1 _
    by_cases hlt : r2 < r1
    · rw [if_pos hlt, if_pos hlt, pairCount_symm]
    · rw [if_neg hlt, if_neg hlt]
  rw [hlower]; ring

private lemma romanoff_diag_bound (N : ℕ) (hN : 2 ^ 30 ≤ N) :
    ∑ r ∈ Finset.range (Nat.log 2 (N / 20)), pairCount N r r ≤ 10 * (N : ℝ) := by
  set K := Nat.log 2 (N / 20)
  set P := (Finset.Ioc (N / 20) (N / 2)).filter Nat.Prime
  have hK_upper : (K : ℝ) ≤ 2 * Real.log (N : ℝ) := (romanoff_K_bounds N hN).2.2
  have hlogN_pos : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hpc_diag : ∀ r, pairCount N r r = (P.card : ℝ) := by
    intro r; simp only [pairCount, P]; congr 1; congr 1; ext p
    simp only [Finset.mem_filter, and_iff_left_iff_imp]; intro hp; exact ⟨p, hp, rfl⟩
  simp_rw [hpc_diag, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hP_le : (P.card : ℝ) ≤ 3 * ((N / 2 : ℕ) : ℝ) / Real.log ((N / 2 : ℕ) : ℝ) := by
    have hsub : P ⊆ primesUpTo (N / 2) := by
      intro p hp
      simp only [P, primesUpTo, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_range] at hp ⊢
      exact ⟨by omega, hp.2⟩
    exact le_trans (by exact_mod_cast Finset.card_le_card hsub) (pi_upper (N / 2) (by omega))
  have hlog_half_ge : 0.9 * Real.log (N : ℝ) ≤ Real.log ((N / 2 : ℕ) : ℝ) := log_half_ge N hN
  have hN2_le : ((N / 2 : ℕ) : ℝ) ≤ (N : ℝ) / 2 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
    exact_mod_cast Nat.div_mul_le_self N 2
  have hP_le2 : (P.card : ℝ) ≤ 5 * (N : ℝ) / Real.log (N : ℝ) := by
    calc (P.card : ℝ) ≤ 3 * ((N / 2 : ℕ) : ℝ) / Real.log ((N / 2 : ℕ) : ℝ) := hP_le
      _ ≤ 3 * ((N : ℝ) / 2) / Real.log ((N / 2 : ℕ) : ℝ) :=
          div_le_div_of_nonneg_right (by linarith) (by linarith)
      _ ≤ 3 * ((N : ℝ) / 2) / (0.9 * Real.log (N : ℝ)) :=
          div_le_div_of_nonneg_left (by positivity) (by linarith) hlog_half_ge
      _ = (5 / 3) * (N : ℝ) / Real.log (N : ℝ) := by ring
      _ ≤ 5 * (N : ℝ) / Real.log (N : ℝ) := by
          apply div_le_div_of_nonneg_right _ hlogN_pos.le
          have : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N; linarith
  calc (K : ℝ) * (P.card : ℝ)
    _ ≤ (2 * Real.log (N : ℝ)) * (5 * (N : ℝ) / Real.log (N : ℝ)) :=
        mul_le_mul hK_upper hP_le2 (Nat.cast_nonneg _) (by positivity)
    _ = 10 * (N : ℝ) := by field_simp; ring

private lemma romanoff_offdiag_bound (C_R : ℝ) (hCR_pos : 0 < C_R)
    (hCR : ∀ K : ℕ, 1 ≤ K → ∑ m ∈ Finset.Icc 1 K, romF m ≤ C_R * (K : ℝ))
    (N : ℕ) (hN : 2 * 1000000 ^ 4 ≤ N) :
    let K := Nat.log 2 (N / 20)
    ∑ r1 ∈ Finset.range K, ∑ r2 ∈ (Finset.range K).filter (fun r2 => r1 < r2), pairCount N r1 r2 ≤
      8000 * C_R * (N : ℝ) := by
  intro K
  have hN_ge_2_30 : 2 ^ 30 ≤ N := le_trans two_pow30_le_two_ten6_pow4 hN
  have hstep1 : ∑ r1 ∈ Finset.range K, ∑ r2 ∈ (Finset.range K).filter (fun r2 => r1 < r2), pairCount N r1 r2 ≤
      ∑ r1 ∈ Finset.range K, ∑ r2 ∈ (Finset.range K).filter (fun r2 => r1 < r2),
        (2000 * (N : ℝ) / (Real.log (N : ℝ)) ^ 2) * romF (r2 - r1) :=
    Finset.sum_le_sum fun r1 _ => Finset.sum_le_sum fun r2 hr2 =>
      pairCount_offdiag_bound N r1 r2 hN (Finset.mem_filter.mp hr2).2
  clear hN
  obtain ⟨hK_ge_1, _, hK_upper⟩ := romanoff_K_bounds N hN_ge_2_30
  have hlogN_pos : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  calc ∑ r1 ∈ Finset.range K, ∑ r2 ∈ (Finset.range K).filter (fun r2 => r1 < r2), pairCount N r1 r2
    _ ≤ ∑ r1 ∈ Finset.range K, ∑ r2 ∈ (Finset.range K).filter (fun r2 => r1 < r2),
          (2000 * (N : ℝ) / (Real.log (N : ℝ)) ^ 2) * romF (r2 - r1) := hstep1
    _ = (2000 * (N : ℝ) / (Real.log (N : ℝ)) ^ 2) *
          ∑ r1 ∈ Finset.range K, ∑ r2 ∈ (Finset.range K).filter (fun r2 => r1 < r2), romF (r2 - r1) := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro r1 _; rw [Finset.mul_sum]
    _ ≤ (2000 * (N : ℝ) / (Real.log (N : ℝ)) ^ 2) *
          ∑ _r1 ∈ Finset.range K, ∑ m ∈ Finset.Icc 1 K, romF m := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Finset.sum_le_sum; intro r1 hr1
        have hinj : ∀ a ∈ (Finset.range K).filter (fun r2 => r1 < r2),
            ∀ b ∈ (Finset.range K).filter (fun r2 => r1 < r2), a - r1 = b - r1 → a = b := by
          intro a ha b hb heq
          simp only [Finset.mem_filter] at ha hb; omega
        have hsub : ((Finset.range K).filter (fun r2 => r1 < r2)).image (fun r2 => r2 - r1) ⊆
            Finset.Icc 1 K := by
          intro m hm
          rcases Finset.mem_image.mp hm with ⟨r2, hr2, rfl⟩
          simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc] at hr2 ⊢; omega
        rw [← Finset.sum_image (f := romF) hinj]
        exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)
    _ ≤ (2000 * (N : ℝ) / (Real.log (N : ℝ)) ^ 2) * ((K : ℝ) * (C_R * (K : ℝ))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_left (hCR K hK_ge_1) (Nat.cast_nonneg K)
    _ ≤ (2000 * (N : ℝ) / (Real.log (N : ℝ)) ^ 2) * (C_R * (2 * Real.log (N : ℝ)) ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have hK2 : (K : ℝ) ^ 2 ≤ (2 * Real.log (N : ℝ)) ^ 2 :=
          pow_le_pow_left₀ (Nat.cast_nonneg K) hK_upper 2
        nlinarith [hCR_pos]
    _ = 8000 * C_R * (N : ℝ) := by field_simp; ring

private lemma romanoff_lower_density :
    ∃ c0 : ℝ, 0 < c0 ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      c0 * (N : ℝ) ≤
        (((Finset.Icc 1 N).filter (fun n => N ≤ 20 * n ∧ Representable n)).card : ℝ) := by
  rcases romanoff_sum_bound with ⟨C_R, hCR_pos, hCR⟩
  refine ⟨(0.025 : ℝ) ^ 2 / (10 + 16000 * C_R), by positivity, 2 * 1000000 ^ 4, fun N hN => ?_⟩
  have hN_ge_2_30 : 2 ^ 30 ≤ N := le_trans two_pow30_le_two_ten6_pow4 hN
  have hoff := romanoff_offdiag_bound C_R hCR_pos hCR N hN
  clear hN
  set K := Nat.log 2 (N / 20)
  set P := (Finset.Ioc (N / 20) (N / 2)).filter Nat.Prime
  set A := (Finset.Icc 1 N).filter (fun n => N ≤ 20 * n ∧ Representable n)
  obtain ⟨_, hK_lower, _⟩ := romanoff_K_bounds N hN_ge_2_30
  have hK_pow_le : 2 ^ K ≤ N / 20 := Nat.pow_log_le_self 2 (by omega)
  have hlogN_pos : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hφ_maps : ∀ rp ∈ Finset.range K ×ˢ P, rp.2 + (2 ^ (rp.1 + 1) - 1) ∈ A := by
    intro rp hrp
    simp only [Finset.mem_product, Finset.mem_range, P, Finset.mem_filter, Finset.mem_Ioc] at hrp
    rcases hrp with ⟨hr, ⟨hp_lo, hp_hi⟩, hp_prime⟩
    have h2r1_le : 2 ^ (rp.1 + 1) ≤ N / 20 :=
      le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) hK_pow_le
    have h2r_lt : 2 ^ rp.1 < rp.2 := by
      have : 2 ^ rp.1 ≤ 2 ^ (rp.1 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hrep := representable_prime_add_pow_two rp.1 rp.2 hp_prime h2r_lt
    simp only [A, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨by omega, by omega⟩, by omega, hrep⟩
  let repCnt : ℕ → ℝ := fun n =>
    (((Finset.range K ×ˢ P).filter (fun rp => rp.2 + (2 ^ (rp.1 + 1) - 1) = n)).card : ℝ)
  have hfirst : 0.025 * (N : ℝ) ≤ ∑ n ∈ A, repCnt n := by
    have hsum_eq : ∑ n ∈ A, repCnt n = (K : ℝ) * (P.card : ℝ) := by
      have hnat : ∑ n ∈ A, ((Finset.range K ×ˢ P).filter (fun rp => rp.2 + (2 ^ (rp.1 + 1) - 1) = n)).card =
          (Finset.range K ×ˢ P).card := by
        simpa using Finset.sum_fiberwise_of_maps_to hφ_maps (fun _ => (1 : ℕ))
      have hcast : ∑ n ∈ A, repCnt n = ((Finset.range K ×ˢ P).card : ℝ) := by
        simp only [repCnt]; exact_mod_cast hnat
      rw [hcast, Finset.card_product, Finset.card_range, Nat.cast_mul]
    rw [hsum_eq]
    calc 0.025 * (N : ℝ) = (0.5 * Real.log (N : ℝ)) * (0.05 * (N : ℝ) / Real.log (N : ℝ)) := by
          field_simp; ring
      _ ≤ (K : ℝ) * (P.card : ℝ) :=
          mul_le_mul hK_lower (primes_in_band N hN_ge_2_30) (by positivity) (by positivity)
  have hsecond : ∑ n ∈ A, (repCnt n) ^ 2 ≤ (10 + 16000 * C_R) * (N : ℝ) := by
    have hsq_eq : ∑ n ∈ A, (repCnt n) ^ 2 =
        ∑ r1 ∈ Finset.range K, ∑ r2 ∈ Finset.range K, pairCount N r1 r2 :=
      romanoff_second_moment_identity K P A hφ_maps
    rw [hsq_eq, romanoff_split_tri]
    have hdiag := romanoff_diag_bound N hN_ge_2_30
    linarith
  have hcs := cauchy_schwarz_finset A repCnt
  have hN_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (by omega)
  have hden_pos : (0 : ℝ) < 10 + 16000 * C_R := by linarith
  have hsq_first : (0.025 * (N : ℝ)) ^ 2 ≤ (∑ n ∈ A, repCnt n) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hfirst 2
  have hcs2 : (0.025 * (N : ℝ)) ^ 2 ≤ (A.card : ℝ) * ((10 + 16000 * C_R) * (N : ℝ)) :=
    le_trans hsq_first (le_trans hcs (mul_le_mul_of_nonneg_left hsecond (Nat.cast_nonneg _)))
  rw [div_mul_eq_mul_div, div_le_iff₀ hden_pos]
  nlinarith

/-! ### Section 7: Final Disproof -/

theorem prove_disproof :
    ¬ ((∀ ε > (0 : ℝ),
      Tendsto (fun N : ℕ =>
        (((Finset.Icc 1 N).filter (fun n => (f n : ℝ) ≤ ε * n)).card : ℝ) / N)
        atTop (𝓝 1)) ∧
      (∀ C : ℝ, ∃ᶠ n : ℕ in atTop, C * n < (f n : ℝ))) := by
  intro ⟨h1, _⟩
  rcases romanoff_lower_density with ⟨c0, hc0_pos, N0, hN0⟩
  set δ : ℝ := min (1 / 2) (c0 / 12800)
  have hδ_pos : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ_le1 : δ ≤ 1 := le_trans (min_le_left _ _) (by norm_num)
  have hδ_le_c : δ ≤ c0 / 12800 := min_le_right _ _
  have hδ3 : 6400 * δ ^ 3 ≤ c0 / 2 := by
    have h1 : δ ^ 3 ≤ δ := by nlinarith [sq_nonneg δ]
    linarith
  have htend := h1 δ hδ_pos
  have hev : ∀ᶠ N : ℕ in atTop,
      (((Finset.Icc 1 N).filter (fun n => (f n : ℝ) ≤ δ * (n : ℝ))).card : ℝ) / (N : ℝ) ≤
      1 - c0 / 2 := by
    rw [Filter.eventually_atTop]
    refine ⟨max N0 1, fun N hN => ?_⟩
    have hN_ge : N0 ≤ N := le_trans (le_max_left _ _) hN
    have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
    have hN_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (by omega)
    set A := (Finset.Icc 1 N).filter (fun n => N ≤ 20 * n ∧ Representable n)
    set B := (Finset.Icc 1 N).filter (fun n => N ≤ 20 * n ∧ Representable n ∧ (f n : ℝ) ≤ δ * (n : ℝ))
    set F := (Finset.Icc 1 N).filter (fun n => (f n : ℝ) ≤ δ * (n : ℝ))
    have hA_lb : c0 * (N : ℝ) ≤ (A.card : ℝ) := hN0 N hN_ge
    have hB_ub : (B.card : ℝ) ≤ (c0 / 2) * (N : ℝ) := by
      have htao := tao_upper_bound N δ hδ_pos
      have : 6400 * δ ^ 3 * (N : ℝ) ≤ (c0 / 2) * (N : ℝ) :=
        mul_le_mul_of_nonneg_right hδ3 hN_pos.le
      linarith
    have hB_sub : B ⊆ A := by
      intro n hn; simp only [B, A, Finset.mem_filter] at hn ⊢
      exact ⟨hn.1, hn.2.1, hn.2.2.1⟩
    have hdisj : Disjoint F (A \ B) := by
      rw [Finset.disjoint_left]; intro n hnF hnAB
      simp only [Finset.mem_sdiff, A, B, F, Finset.mem_filter] at hnF hnAB
      exact hnAB.2 ⟨hnF.1, hnAB.1.2.1, hnAB.1.2.2, hnF.2⟩
    have hunion_sub : F ∪ (A \ B) ⊆ Finset.Icc 1 N := by
      intro n hn
      rcases Finset.mem_union.mp hn with hF | hAB
      · exact (Finset.mem_filter.mp hF).1
      · exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp hAB).1).1
    have hcard_sum : F.card + (A \ B).card ≤ N := by
      calc F.card + (A \ B).card = (F ∪ (A \ B)).card := (Finset.card_union_of_disjoint hdisj).symm
        _ ≤ (Finset.Icc 1 N).card := Finset.card_le_card hunion_sub
        _ = N := by simp
    have hAB_card : (A.card : ℝ) - (B.card : ℝ) ≤ ((A \ B).card : ℝ) := by
      rw [Finset.card_sdiff_of_subset hB_sub, Nat.cast_sub (Finset.card_le_card hB_sub)]
    have hcard_real : (F.card : ℝ) + ((A \ B).card : ℝ) ≤ (N : ℝ) := by exact_mod_cast hcard_sum
    have hF_le : (F.card : ℝ) ≤ (1 - c0 / 2) * (N : ℝ) := by linarith
    rw [div_le_iff₀ hN_pos]
    exact hF_le
  have hlim_le : (1 : ℝ) ≤ 1 - c0 / 2 := le_of_tendsto htend hev
  linarith

end OMA.P_erdos_1054

theorem OMA.disproof : ¬ (type_of% @OMA.S_erdos_1054.main) :=
  OMA.P_erdos_1054.prove_disproof
