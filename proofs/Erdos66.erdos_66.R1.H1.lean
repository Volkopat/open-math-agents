import OMAReductions.R_Erdos66_erdos_66_R1
import Mathlib

/-! # Verification of Erdos66.erdos_66.R1.H1

Proof of monotonicity, nonnegativity, and the normalized self-convolution limit `a^2 * pi`
for the decreasing weight function via `arcsin (2*t - 1)` mean-value bounds.
-/

namespace OMA.P_Erdos66_erdos_66_R1_H1

open AdditiveCombinatorics Finset Filter
open scoped Topology

private noncomputable def q (i : ℕ) : ℝ :=
  Real.sqrt ((1 + Real.log ((i : ℝ) + 1)) / ((i : ℝ) + 1))

private lemma q_nonneg (i : ℕ) : 0 ≤ q i :=
  Real.sqrt_nonneg _

private lemma q_antitone : Antitone q := by
  intro i j hij
  unfold q
  apply Real.sqrt_le_sqrt
  set x : ℝ := (i : ℝ) + 1
  set y : ℝ := (j : ℝ) + 1
  have hx1 : 1 ≤ x := by simp [x]
  have hx0 : 0 < x := by positivity
  have hxy : x ≤ y := by
    have hij' : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
    dsimp only [x, y]
    linarith
  have hy0 : 0 < y := hx0.trans_le hxy
  have hlog : Real.log (y / x) ≤ y / x - 1 := Real.log_le_sub_one_of_pos (div_pos hy0 hx0)
  rw [Real.log_div hy0.ne' hx0.ne'] at hlog
  have hmul : x * (Real.log y - Real.log x) ≤ x * (y / x - 1) :=
    mul_le_mul_of_nonneg_left hlog hx0.le
  rw [mul_sub, mul_sub, mul_div_cancel₀ y hx0.ne', mul_one] at hmul
  have h0 : 0 ≤ (y - x) * Real.log x :=
    mul_nonneg (sub_nonneg.mpr hxy) (Real.log_nonneg hx1)
  have hcross : (1 + Real.log y) * x ≤ (1 + Real.log x) * y := by linarith
  exact (div_le_div_iff₀ hy0 hx0).mpr hcross

private noncomputable def f (t : ℝ) : ℝ :=
  1 / Real.sqrt (t * (1 - t))

private noncomputable def G (t : ℝ) : ℝ :=
  Real.arcsin (2 * t - 1)

private lemma G_continuous : Continuous G :=
  Real.continuous_arcsin.comp ((continuous_const.mul continuous_id).sub continuous_const)

private lemma G_mono : Monotone G := by
  intro s t hst
  exact Real.arcsin_le_arcsin (by linarith)

private lemma G_zero : G 0 = -(Real.pi / 2) := by
  simp [G]

private lemma G_one : G 1 = Real.pi / 2 := by
  norm_num [G]

private lemma G_hasDerivAt {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) : HasDerivAt G (f t) t := by
  have hinner : HasDerivAt (fun x : ℝ => 2 * x - 1) 2 t := by
    simpa using ((hasDerivAt_id t).const_mul 2).sub_const 1
  have hne1 : 2 * t - 1 ≠ -1 := by linarith
  have hne2 : 2 * t - 1 ≠ 1 := by linarith
  have hcomp := (Real.hasDerivAt_arcsin hne1 hne2).comp t hinner
  have hprod_pos : 0 < t * (1 - t) := mul_pos ht0 (sub_pos.mpr ht1)
  have hsq : Real.sqrt (1 - (2 * t - 1) ^ 2) = 2 * Real.sqrt (t * (1 - t)) := by
    rw [show 1 - (2 * t - 1) ^ 2 = 4 * (t * (1 - t)) by ring,
      Real.sqrt_mul (by norm_num), show Real.sqrt 4 = 2 by norm_num]
  rw [hsq] at hcomp
  have hrt : Real.sqrt (t * (1 - t)) ≠ 0 := (Real.sqrt_pos.mpr hprod_pos).ne'
  have hval : 1 / (2 * Real.sqrt (t * (1 - t))) * 2 = f t := by
    unfold f
    field_simp
  exact hval ▸ hcomp

private lemma f_antitone_left {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) (ht : t ≤ 1 / 2) :
    f t ≤ f s := by
  unfold f
  have hs0 : 0 < s * (1 - s) := mul_pos hs (by linarith)
  have hmul : s * (1 - s) ≤ t * (1 - t) := by
    have : 0 ≤ (t - s) * (1 - s - t) := mul_nonneg (by linarith) (by linarith)
    linarith
  exact one_div_le_one_div_of_le (Real.sqrt_pos.mpr hs0) (Real.sqrt_le_sqrt hmul)

private lemma f_mono_right {s t : ℝ} (hs : 1 / 2 ≤ s) (hst : s ≤ t) (ht : t < 1) :
    f s ≤ f t := by
  unfold f
  have ht0 : 0 < t * (1 - t) := mul_pos (by linarith) (sub_pos.mpr ht)
  have hmul : t * (1 - t) ≤ s * (1 - s) := by
    have : 0 ≤ (t - s) * (s + t - 1) := mul_nonneg (by linarith) (by linarith)
    linarith
  exact one_div_le_one_div_of_le (Real.sqrt_pos.mpr ht0) (Real.sqrt_le_sqrt hmul)

private lemma mvt_left {u v : ℝ} (hu : 0 < u) (huv : u < v) (hv : v ≤ 1 / 2) :
    f v * (v - u) ≤ G v - G u ∧ G v - G u ≤ f u * (v - u) := by
  obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope G f huv G_continuous.continuousOn
    (fun t ht => G_hasDerivAt (hu.trans ht.1) (ht.2.trans_le (by linarith)))
  have hvu : 0 < v - u := sub_pos.mpr huv
  have hEq : G v - G u = f c * (v - u) := by
    rw [hslope, div_mul_cancel₀ _ hvu.ne']
  rw [hEq]
  refine ⟨mul_le_mul_of_nonneg_right (f_antitone_left (hu.trans hc.1) hc.2.le hv) hvu.le,
    mul_le_mul_of_nonneg_right (f_antitone_left hu hc.1.le (hc.2.le.trans hv)) hvu.le⟩

private lemma mvt_right {u v : ℝ} (hu : 1 / 2 ≤ u) (huv : u < v) (hv : v < 1) :
    f u * (v - u) ≤ G v - G u ∧ G v - G u ≤ f v * (v - u) := by
  obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope G f huv G_continuous.continuousOn
    (fun t ht => G_hasDerivAt (lt_of_lt_of_le (by norm_num) (hu.trans ht.1.le)) (ht.2.trans hv))
  have hvu : 0 < v - u := sub_pos.mpr huv
  have hEq : G v - G u = f c * (v - u) := by
    rw [hslope, div_mul_cancel₀ _ hvu.ne']
  rw [hEq]
  refine ⟨mul_le_mul_of_nonneg_right (f_mono_right hu hc.1.le (hc.2.trans hv)) hvu.le,
    mul_le_mul_of_nonneg_right (f_mono_right (hu.trans hc.1.le) hc.2.le hv) hvu.le⟩

private lemma f_grid {N k : ℕ} (hk1 : 1 ≤ k) (hkN : k < N) :
    f ((k : ℝ) / N) * (1 / (N : ℝ)) = 1 / Real.sqrt ((k : ℝ) * ((N : ℝ) - k)) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast lt_of_lt_of_le hk1 hkN.le
  have hk : (0 : ℝ) < k := by exact_mod_cast hk1
  have hNk : (0 : ℝ) < (N : ℝ) - k := by
    have : (k : ℝ) < N := by exact_mod_cast hkN
    linarith
  unfold f
  have harg : (k : ℝ) / N * (1 - (k : ℝ) / N) = ((k : ℝ) * ((N : ℝ) - k)) / (N : ℝ) ^ 2 := by
    field_simp
  rw [harg, Real.sqrt_div (mul_nonneg hk.le hNk.le), Real.sqrt_sq hN.le]
  have hsqrt : Real.sqrt ((k : ℝ) * ((N : ℝ) - k)) ≠ 0 :=
    (Real.sqrt_pos.mpr (mul_pos hk hNk)).ne'
  field_simp

private lemma sum_Ico_sub (g : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b) :
    ∑ k ∈ Finset.Ico a b, (g (k + 1) - g k) = g b - g a := by
  induction b with
  | zero =>
    have ha : a = 0 := by omega
    subst ha
    simp
  | succ b ih =>
    rcases eq_or_lt_of_le hab with rfl | hlt
    · simp
    · rw [Finset.sum_Ico_succ_top (by omega), ih (by omega)]
      ring

private noncomputable def S0 (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 (n + 1), 1 / Real.sqrt ((k : ℝ) * ((n + 2 : ℝ) - k))

private lemma sum_union_le_of_nonneg (A B : Finset ℕ) (h : ℕ → ℝ) (hnonneg : ∀ x, 0 ≤ h x) :
    ∑ x ∈ A ∪ B, h x ≤ (∑ x ∈ A, h x) + ∑ x ∈ B, h x := by
  have hiu := Finset.sum_union_inter (s₁ := A) (s₂ := B) (f := h)
  have hinter : 0 ≤ ∑ x ∈ A ∩ B, h x := Finset.sum_nonneg (fun x _ => hnonneg x)
  linarith

private lemma S0_upper {n : ℕ} (hn : 2 ≤ n) :
    S0 n ≤ Real.pi + 2 / Real.sqrt ((n : ℝ) + 1) := by
  set N : ℕ := n + 2
  have hN4 : 4 ≤ N := by omega
  have hNpos : (0 : ℝ) < N := by positivity
  set m1 : ℕ := N / 2
  set m2 : ℕ := (N + 1) / 2
  have hm1_2 : 2 ≤ m1 := by omega
  have hm12 : m1 ≤ m2 := by omega
  have hm21 : m2 ≤ m1 + 1 := by omega
  have hm2N : m2 ≤ N - 2 := by omega
  have hm1_half : (m1 : ℝ) / N ≤ 1 / 2 := by
    have : 2 * (m1 : ℝ) ≤ N := by exact_mod_cast (by omega : 2 * m1 ≤ N)
    rw [div_le_div_iff₀ hNpos (by norm_num)]
    linarith
  have hm2_half : 1 / 2 ≤ (m2 : ℝ) / N := by
    have : (N : ℝ) ≤ 2 * m2 := by exact_mod_cast (by omega : N ≤ 2 * m2)
    rw [div_le_div_iff₀ (by norm_num) hNpos]
    linarith
  let term : ℕ → ℝ := fun k => 1 / Real.sqrt ((k : ℝ) * ((N : ℝ) - k))
  have hterm_nonneg (k : ℕ) : 0 ≤ term k := by positivity
  have hleft : ∑ j ∈ Finset.Icc 2 m1, term j ≤ G ((m1 : ℝ) / N) - G (1 / (N : ℝ)) := by
    have hshift : ∑ j ∈ Finset.Icc 2 m1, term j =
        ∑ k ∈ Finset.Ico 1 m1, term (k + 1) := by
      refine Finset.sum_nbij' (fun j => j - 1) (fun k => k + 1) ?_ ?_ ?_ ?_ ?_
      · intro j hj; rw [mem_Icc] at hj; rw [mem_Ico]; omega
      · intro k hk; rw [mem_Ico] at hk; rw [mem_Icc]; omega
      · intro j hj; rw [mem_Icc] at hj; omega
      · intro k _; omega
      · intro j hj; rw [mem_Icc] at hj; congr 1; omega
    rw [hshift]
    calc
      ∑ k ∈ Finset.Ico 1 m1, term (k + 1)
          ≤ ∑ k ∈ Finset.Ico 1 m1, (G (((k + 1 : ℕ) : ℝ) / N) - G ((k : ℝ) / N)) := by
        refine Finset.sum_le_sum fun k hk => ?_
        rw [mem_Ico] at hk
        have hkN : k + 1 < N := by omega
        have hk1 : 1 ≤ k + 1 := by omega
        have hv : ((k + 1 : ℕ) : ℝ) / N ≤ 1 / 2 := by
          have : ((k + 1 : ℕ) : ℝ) ≤ m1 := by exact_mod_cast hk.2
          exact (div_le_div_of_nonneg_right this hNpos.le).trans hm1_half
        have huv : (k : ℝ) / N < ((k + 1 : ℕ) : ℝ) / N := by
          apply div_lt_div_of_pos_right _ hNpos
          exact_mod_cast Nat.lt_succ_self k
        have hstep : (((k + 1 : ℕ) : ℝ) / N - (k : ℝ) / N) = 1 / (N : ℝ) := by
          push_cast; ring
        have hkpos : 0 < (k : ℝ) / N := div_pos (by exact_mod_cast hk.1) hNpos
        have hmvt := (mvt_left hkpos huv hv).1
        rw [hstep, f_grid hk1 hkN] at hmvt
        dsimp only [term]
        simpa only [Nat.cast_add, Nat.cast_one] using hmvt
      _ = G ((m1 : ℝ) / N) - G (1 / (N : ℝ)) := by
        simpa [Nat.cast_one] using sum_Ico_sub (fun k => G ((k : ℝ) / N)) (by omega : 1 ≤ m1)
  have hright : ∑ k ∈ Finset.Icc m2 (N - 2), term k ≤
      G (((N - 1 : ℕ) : ℝ) / N) - G ((m2 : ℝ) / N) := by
    rw [show Finset.Icc m2 (N - 2) = Finset.Ico m2 (N - 1) by
      ext k; simp only [mem_Icc, mem_Ico]; omega]
    calc
      ∑ k ∈ Finset.Ico m2 (N - 1), term k
          ≤ ∑ k ∈ Finset.Ico m2 (N - 1), (G (((k + 1 : ℕ) : ℝ) / N) - G ((k : ℝ) / N)) := by
        refine Finset.sum_le_sum fun k hk => ?_
        rw [mem_Ico] at hk
        have hk1 : 1 ≤ k := by omega
        have hkN : k < N := by omega
        have hu : 1 / 2 ≤ (k : ℝ) / N := by
          have : (m2 : ℝ) ≤ k := by exact_mod_cast hk.1
          exact hm2_half.trans (div_le_div_of_nonneg_right this hNpos.le)
        have huv : (k : ℝ) / N < ((k + 1 : ℕ) : ℝ) / N := by
          apply div_lt_div_of_pos_right _ hNpos
          exact_mod_cast Nat.lt_succ_self k
        have hv : ((k + 1 : ℕ) : ℝ) / N < 1 := by
          rw [div_lt_one hNpos]
          exact_mod_cast (by omega : k + 1 < N)
        have hstep : (((k + 1 : ℕ) : ℝ) / N - (k : ℝ) / N) = 1 / (N : ℝ) := by
          push_cast; ring
        have hmvt := (mvt_right hu huv hv).1
        rw [hstep, f_grid hk1 hkN] at hmvt
        exact hmvt
      _ = G (((N - 1 : ℕ) : ℝ) / N) - G ((m2 : ℝ) / N) :=
        sum_Ico_sub (fun k => G ((k : ℝ) / N)) (by omega : m2 ≤ N - 1)
  have hsub : Finset.Icc 1 (n + 1) ⊆
      ({1, n + 1} : Finset ℕ) ∪ (Finset.Icc 2 m1 ∪ Finset.Icc m2 (N - 2)) := by
    intro k hk
    rw [mem_Icc] at hk
    simp only [mem_union, mem_insert, mem_singleton, mem_Icc]
    omega
  have hcov := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x _ _ => hterm_nonneg x)
  have hu1 := sum_union_le_of_nonneg {1, n + 1} (Finset.Icc 2 m1 ∪ Finset.Icc m2 (N - 2))
    term hterm_nonneg
  have hu2 := sum_union_le_of_nonneg (Finset.Icc 2 m1) (Finset.Icc m2 (N - 2))
    term hterm_nonneg
  have hpair : ∑ k ∈ ({1, n + 1} : Finset ℕ), term k = 2 / Real.sqrt ((n : ℝ) + 1) := by
    have hne : (1 : ℕ) ≠ n + 1 := by omega
    rw [Finset.sum_pair hne]
    have ht1 : term 1 = 1 / Real.sqrt ((n : ℝ) + 1) := by
      simp [term, N]; ring_nf
    have ht2 : term (n + 1) = 1 / Real.sqrt ((n : ℝ) + 1) := by
      have hcast : ((n + 1 : ℕ) : ℝ) * ((N : ℝ) - ((n + 1 : ℕ) : ℝ)) = (n : ℝ) + 1 := by
        simp [N]; ring
      dsimp only [term]
      rw [hcast]
    rw [ht1, ht2]
    ring
  have hmG : G ((m1 : ℝ) / N) ≤ G ((m2 : ℝ) / N) :=
    G_mono (div_le_div_of_nonneg_right (by exact_mod_cast hm12) hNpos.le)
  have hG0 : -(Real.pi / 2) ≤ G (1 / (N : ℝ)) := by
    rw [← G_zero]
    exact G_mono (by positivity)
  have hG1 : G (((N - 1 : ℕ) : ℝ) / N) ≤ Real.pi / 2 := by
    rw [← G_one]
    exact G_mono ((div_le_one hNpos).mpr (by exact_mod_cast (by omega : N - 1 ≤ N)))
  have hS0 : S0 n = ∑ k ∈ Finset.Icc 1 (n + 1), term k := by
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [term, N]
  rw [hS0]
  linarith

private lemma S0_mid_lower {n a b : ℕ} (hn : 4 ≤ n) (ha1 : 1 ≤ a) (ham : a ≤ (n + 2) / 2)
    (hmb : (n + 3) / 2 ≤ b) (hbn : b ≤ n + 1) :
    (G ((b : ℝ) / (n + 2 : ℝ)) - G ((a : ℝ) / (n + 2 : ℝ))) -
      (G ((((n + 3) / 2 : ℕ) : ℝ) / (n + 2 : ℝ)) - G ((((n + 2) / 2 : ℕ) : ℝ) / (n + 2 : ℝ))) ≤
      ∑ k ∈ Finset.Icc a b, 1 / Real.sqrt ((k : ℝ) * ((n + 2 : ℝ) - k)) := by
  set N : ℕ := n + 2
  have hNpos : (0 : ℝ) < N := by positivity
  set m1 : ℕ := N / 2
  set m2 : ℕ := (N + 1) / 2
  have hm12 : m1 ≤ m2 := by omega
  have hm1_half : (m1 : ℝ) / N ≤ 1 / 2 := by
    have : 2 * (m1 : ℝ) ≤ N := by exact_mod_cast (by omega : 2 * m1 ≤ N)
    rw [div_le_div_iff₀ hNpos (by norm_num)]
    linarith
  have hm2_half : 1 / 2 ≤ (m2 : ℝ) / N := by
    have : (N : ℝ) ≤ 2 * m2 := by exact_mod_cast (by omega : N ≤ 2 * m2)
    rw [div_le_div_iff₀ (by norm_num) hNpos]
    linarith
  let term : ℕ → ℝ := fun k => 1 / Real.sqrt ((k : ℝ) * ((N : ℝ) - k))
  have hleft : G ((m1 : ℝ) / N) - G ((a : ℝ) / N) ≤ ∑ k ∈ Finset.Ico a m1, term k := by
    rw [← sum_Ico_sub (fun k => G ((k : ℝ) / N)) ham]
    refine Finset.sum_le_sum fun k hk => ?_
    rw [mem_Ico] at hk
    have hk1 : 1 ≤ k := by omega
    have hkN : k < N := by omega
    have hu : 0 < (k : ℝ) / N := by
      apply div_pos _ hNpos
      exact_mod_cast hk1
    have huv : (k : ℝ) / N < ((k + 1 : ℕ) : ℝ) / N := by
      apply div_lt_div_of_pos_right _ hNpos
      exact_mod_cast Nat.lt_succ_self k
    have hv : ((k + 1 : ℕ) : ℝ) / N ≤ 1 / 2 := by
      have : ((k + 1 : ℕ) : ℝ) ≤ m1 := by exact_mod_cast hk.2
      exact (div_le_div_of_nonneg_right this hNpos.le).trans hm1_half
    have hstep : (((k + 1 : ℕ) : ℝ) / N - (k : ℝ) / N) = 1 / (N : ℝ) := by
      push_cast; ring
    have hmvt := (mvt_left hu huv hv).2
    rw [hstep, f_grid hk1 hkN] at hmvt
    exact hmvt
  have hright : G ((b : ℝ) / N) - G ((m2 : ℝ) / N) ≤
      ∑ j ∈ Finset.Icc (m2 + 1) b, term j := by
    have hshift : ∑ j ∈ Finset.Icc (m2 + 1) b, term j =
        ∑ k ∈ Finset.Ico m2 b, term (k + 1) := by
      refine Finset.sum_nbij' (fun j => j - 1) (fun k => k + 1) ?_ ?_ ?_ ?_ ?_
      · intro j hj; rw [mem_Icc] at hj; rw [mem_Ico]; omega
      · intro k hk; rw [mem_Ico] at hk; rw [mem_Icc]; omega
      · intro j hj; rw [mem_Icc] at hj; omega
      · intro k _; omega
      · intro j hj; rw [mem_Icc] at hj; congr 1; omega
    rw [hshift, ← sum_Ico_sub (fun k => G ((k : ℝ) / N)) hmb]
    refine Finset.sum_le_sum fun k hk => ?_
    rw [mem_Ico] at hk
    have hk1 : 1 ≤ k + 1 := by omega
    have hkN : k + 1 < N := by omega
    have hu : 1 / 2 ≤ (k : ℝ) / N := by
      have : (m2 : ℝ) ≤ k := by exact_mod_cast hk.1
      exact hm2_half.trans (div_le_div_of_nonneg_right this hNpos.le)
    have huv : (k : ℝ) / N < ((k + 1 : ℕ) : ℝ) / N := by
      apply div_lt_div_of_pos_right _ hNpos
      exact_mod_cast Nat.lt_succ_self k
    have hv : ((k + 1 : ℕ) : ℝ) / N < 1 := by
      rw [div_lt_one hNpos]
      exact_mod_cast hkN
    have hstep : (((k + 1 : ℕ) : ℝ) / N - (k : ℝ) / N) = 1 / (N : ℝ) := by
      push_cast; ring
    have hmvt := (mvt_right hu huv hv).2
    rw [hstep, f_grid hk1 hkN] at hmvt
    dsimp only [term]
    simpa only [Nat.cast_add, Nat.cast_one] using hmvt
  have hdisj : Disjoint (Finset.Ico a m1) (Finset.Icc (m2 + 1) b) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    rw [mem_Ico] at hx1
    rw [mem_Icc] at hx2
    omega
  have hsub : Finset.Ico a m1 ∪ Finset.Icc (m2 + 1) b ⊆ Finset.Icc a b := by
    intro x hx
    simp only [mem_union, mem_Ico, mem_Icc] at hx ⊢
    omega
  have hsum : (∑ k ∈ Finset.Ico a m1, term k) + ∑ j ∈ Finset.Icc (m2 + 1) b, term j ≤
      ∑ k ∈ Finset.Icc a b, term k := by
    rw [← Finset.sum_union hdisj]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x _ _ => by positivity)
  have heq : (∑ k ∈ Finset.Icc a b, term k) =
      ∑ k ∈ Finset.Icc a b, 1 / Real.sqrt ((k : ℝ) * ((n + 2 : ℝ) - k)) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [term, N]
  dsimp only [m1, m2, N] at hleft hright
  have hadd3 : n + 2 + 1 = n + 3 := by omega
  rw [hadd3] at hright
  rw [← heq]
  push_cast at hleft hright ⊢
  linarith

private lemma sumConv_q_eq (n : ℕ) :
    sumConv q q n = ∑ k ∈ Finset.Icc 1 (n + 1),
      Real.sqrt ((1 + Real.log (k : ℝ)) * (1 + Real.log ((n + 2 : ℝ) - k))) /
        Real.sqrt ((k : ℝ) * ((n + 2 : ℝ) - k)) := by
  rw [sumConv, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  have hshift : ∑ i ∈ Finset.range (n + 1), q i * q (n - i) =
      ∑ k ∈ Finset.Icc 1 (n + 1), q (k - 1) * q (n + 1 - k) := by
    refine Finset.sum_nbij' (fun i => i + 1) (fun k => k - 1) ?_ ?_ ?_ ?_ ?_
    · intro i hi; rw [mem_range] at hi; rw [mem_Icc]; omega
    · intro k hk; rw [mem_Icc] at hk; rw [mem_range]; omega
    · intro i _; omega
    · intro k hk; rw [mem_Icc] at hk; omega
    · intro i hi; rw [mem_range] at hi; simp only [Nat.add_sub_cancel]; rw [show n + 1 - (i + 1) = n - i by omega]
  rw [hshift]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [mem_Icc] at hk
  have hk1 : ((k - 1 : ℕ) : ℝ) + 1 = (k : ℝ) := by
    rw [Nat.cast_sub hk.1]
    simp
  have hk2 : ((n + 1 - k : ℕ) : ℝ) + 1 = (n + 2 : ℝ) - k := by
    rw [Nat.cast_sub hk.2]
    push_cast
    ring
  have h1 : 0 ≤ (1 + Real.log (k : ℝ)) / (k : ℝ) := by
    have hk_one : (1 : ℝ) ≤ k := by exact_mod_cast hk.1
    exact div_nonneg (by linarith [Real.log_nonneg hk_one]) (by linarith)
  have h2 : 0 ≤ (1 + Real.log ((n + 2 : ℝ) - k)) / ((n + 2 : ℝ) - k) := by
    have hnk_one : (1 : ℝ) ≤ (n + 2 : ℝ) - k := by
      have : (k : ℝ) ≤ n + 1 := by exact_mod_cast hk.2
      linarith
    exact div_nonneg (by linarith [Real.log_nonneg hnk_one]) (by linarith)
  have hkpos : (0 : ℝ) ≤ k := by positivity
  have hnkpos : (0 : ℝ) ≤ (n + 2 : ℝ) - k := by
    have : (k : ℝ) ≤ n + 1 := by exact_mod_cast hk.2
    linarith
  have hnum : 0 ≤ (1 + Real.log (k : ℝ)) * (1 + Real.log ((n + 2 : ℝ) - k)) := by
    have hk_one : (1 : ℝ) ≤ k := by exact_mod_cast hk.1
    have hnk_one : (1 : ℝ) ≤ (n + 2 : ℝ) - k := by
      have : (k : ℝ) ≤ n + 1 := by exact_mod_cast hk.2
      linarith
    exact mul_nonneg (by linarith [Real.log_nonneg hk_one]) (by linarith [Real.log_nonneg hnk_one])
  unfold q
  rw [hk1, hk2, ← Real.sqrt_mul h1]
  have hdiv_arg : (1 + Real.log (k : ℝ)) / (k : ℝ) *
      ((1 + Real.log ((n + 2 : ℝ) - k)) / ((n + 2 : ℝ) - k)) =
      ((1 + Real.log (k : ℝ)) * (1 + Real.log ((n + 2 : ℝ) - k))) /
        ((k : ℝ) * ((n + 2 : ℝ) - k)) := div_mul_div_comm _ _ _ _
  rw [hdiv_arg, Real.sqrt_div hnum]

private lemma tendsto_log_ratio :
    Tendsto (fun n : ℕ => (1 + Real.log ((n : ℝ) + 1)) / Real.log n) atTop (𝓝 1) := by
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun n : ℕ => 1 + 1 / (n : ℝ)) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).add
      ((tendsto_const_nhds (x := (1 : ℝ))).div_atTop tendsto_natCast_atTop_atTop)
  have hlog1 : Tendsto (fun n : ℕ => 1 + Real.log (1 + 1 / (n : ℝ))) atTop (𝓝 1) := by
    have := (tendsto_const_nhds (x := (1 : ℝ))).add ((Real.continuousAt_log one_ne_zero).tendsto.comp hinv)
    simpa using this
  have hquot : Tendsto (fun n : ℕ => (1 + Real.log (1 + 1 / (n : ℝ))) / Real.log n + 1)
      atTop (𝓝 1) := by
    simpa using (hlog1.div_atTop hlog).add (tendsto_const_nhds (x := (1 : ℝ)))
  refine hquot.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hlog_ne : Real.log (n : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (by omega : 1 < n))).ne'
  have hadd : (n : ℝ) + 1 = (n : ℝ) * (1 + 1 / (n : ℝ)) := by field_simp
  rw [hadd, Real.log_mul hn0.ne' (by positivity)]
  field_simp
  ring

private lemma tendsto_sumConv_q :
    Tendsto (fun n : ℕ => sumConv q q n / Real.log n) atTop (𝓝 Real.pi) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  wlog hε_lt : ε < Real.pi generalizing ε
  · obtain ⟨N, hN⟩ := this (Real.pi / 2) (by positivity) (by linarith [Real.pi_pos])
    exact ⟨N, fun n hn => (hN n hn).trans (by linarith [Real.pi_pos])⟩
  have hupper_tend : Tendsto (fun n : ℕ =>
      ((1 + Real.log ((n : ℝ) + 1)) / Real.log n) * (Real.pi + 2 / Real.sqrt ((n : ℝ) + 1)))
      atTop (𝓝 Real.pi) := by
    have hsqrt : Tendsto (fun n : ℕ => Real.sqrt ((n : ℝ) + 1)) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    have hrhs : Tendsto (fun n : ℕ => Real.pi + 2 / Real.sqrt ((n : ℝ) + 1)) atTop (𝓝 Real.pi) := by
      simpa using tendsto_const_nhds.add (tendsto_const_nhds.div_atTop hsqrt)
    simpa using tendsto_log_ratio.mul hrhs
  have hev_upper : ∀ᶠ n : ℕ in atTop, sumConv q q n / Real.log n < Real.pi + ε := by
    filter_upwards [eventually_ge_atTop 2,
      hupper_tend.eventually (gt_mem_nhds (by linarith : Real.pi < Real.pi + ε))] with n hn hlim
    have hlog_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
    have hterm_le : sumConv q q n / Real.log n ≤
        ((1 + Real.log ((n : ℝ) + 1)) / Real.log n) * S0 n := by
      rw [sumConv_q_eq, S0, Finset.sum_div, Finset.mul_sum]
      refine Finset.sum_le_sum fun k hk => ?_
      rw [mem_Icc] at hk
      have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk.1
      have hkn : (k : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast hk.2
      have hnk1 : (1 : ℝ) ≤ (n + 2 : ℝ) - k := by linarith
      have hnkn : (n + 2 : ℝ) - k ≤ (n : ℝ) + 1 := by linarith
      have ha_nonneg : 0 ≤ 1 + Real.log (k : ℝ) := by linarith [Real.log_nonneg hk1]
      have hb_nonneg : 0 ≤ 1 + Real.log ((n + 2 : ℝ) - k) := by linarith [Real.log_nonneg hnk1]
      have ha_le : 1 + Real.log (k : ℝ) ≤ 1 + Real.log ((n : ℝ) + 1) := by
        linarith [Real.log_le_log (by linarith : (0 : ℝ) < k) hkn]
      have hb_le : 1 + Real.log ((n + 2 : ℝ) - k) ≤ 1 + Real.log ((n : ℝ) + 1) := by
        linarith [Real.log_le_log (by linarith : (0 : ℝ) < (n + 2 : ℝ) - k) hnkn]
      have hprod_le : (1 + Real.log (k : ℝ)) * (1 + Real.log ((n + 2 : ℝ) - k)) ≤
          (1 + Real.log ((n : ℝ) + 1)) ^ 2 := by
        rw [sq]
        exact mul_le_mul ha_le hb_le hb_nonneg (by linarith)
      have hsqrt_le : Real.sqrt ((1 + Real.log (k : ℝ)) * (1 + Real.log ((n + 2 : ℝ) - k))) ≤
          1 + Real.log ((n : ℝ) + 1) := by
        calc
          _ ≤ Real.sqrt ((1 + Real.log ((n : ℝ) + 1)) ^ 2) := Real.sqrt_le_sqrt hprod_le
          _ = 1 + Real.log ((n : ℝ) + 1) :=
            Real.sqrt_sq (by linarith [Real.log_nonneg (by linarith : (1 : ℝ) ≤ (n : ℝ) + 1)])
      have hden_nonneg : 0 ≤ Real.sqrt ((k : ℝ) * ((n + 2 : ℝ) - k)) := Real.sqrt_nonneg _
      calc
        Real.sqrt ((1 + Real.log (k : ℝ)) * (1 + Real.log ((n + 2 : ℝ) - k))) /
            Real.sqrt ((k : ℝ) * ((n + 2 : ℝ) - k)) / Real.log (n : ℝ)
            ≤ (1 + Real.log ((n : ℝ) + 1)) /
                Real.sqrt ((k : ℝ) * ((n + 2 : ℝ) - k)) / Real.log (n : ℝ) := by
          gcongr
        _ = (1 + Real.log ((n : ℝ) + 1)) / Real.log (n : ℝ) *
              (1 / Real.sqrt ((k : ℝ) * ((n + 2 : ℝ) - k))) := by ring
    have hnonneg_rat : 0 ≤ (1 + Real.log ((n : ℝ) + 1)) / Real.log (n : ℝ) := by
      have : 0 ≤ 1 + Real.log ((n : ℝ) + 1) := by
        linarith [Real.log_nonneg (by linarith : (1 : ℝ) ≤ (n : ℝ) + 1)]
      exact div_nonneg this hlog_pos.le
    exact (hterm_le.trans (mul_le_mul_of_nonneg_left (S0_upper hn) hnonneg_rat)).trans_lt hlim
  have hG_at0 : Tendsto (fun t : ℝ => G (1 - t) - G t) (𝓝 0) (𝓝 Real.pi) := by
    have hcont : Continuous (fun t : ℝ => G (1 - t) - G t) :=
      (G_continuous.comp (continuous_const.sub continuous_id)).sub G_continuous
    have hval : G (1 - (0 : ℝ)) - G 0 = Real.pi := by
      rw [sub_zero, G_one, G_zero]
      ring
    have ht : Tendsto (fun t : ℝ => G (1 - t) - G t) (𝓝 0) (𝓝 (G (1 - (0 : ℝ)) - G 0)) :=
      (hcont.continuousAt (x := (0 : ℝ))).tendsto
    rwa [hval] at ht
  have hδ_ev := (Metric.tendsto_nhds.mp hG_at0) (ε / 2) (by positivity)
  rw [Metric.eventually_nhds_iff] at hδ_ev
  obtain ⟨r, hr_pos, hr⟩ := hδ_ev
  set δ : ℝ := min (r / 2) (1 / 16)
  have hδ_pos : 0 < δ := lt_min (by positivity) (by positivity)
  have hδ_small : δ ≤ 1 / 16 := min_le_right _ _
  have hG_δ : Real.pi - ε / 2 < G (1 - δ) - G δ := by
    have hdr : dist δ 0 < r := by
      rw [Real.dist_eq, sub_zero, abs_of_pos hδ_pos]
      exact (min_le_left _ _).trans_lt (by linarith)
    have hd := hr hdr
    rw [Real.dist_eq] at hd
    linarith [abs_lt.mp hd]
  set η : ℝ := min (1 / 4) (ε / (4 * Real.pi))
  have hη_pos : 0 < η := lt_min (by positivity) (div_pos hε (by positivity))
  have hη_le1 : η ≤ 1 / 4 := min_le_left _ _
  have hη_le2 : η ≤ ε / (4 * Real.pi) := min_le_right _ _
  have hη_prod : Real.pi - ε < (1 - η) * (Real.pi - ε / 2) := by
    have h1 : η * (Real.pi - ε / 2) ≤ η * Real.pi :=
      mul_le_mul_of_nonneg_left (by linarith) hη_pos.le
    have h2 : η * Real.pi ≤ ε / 4 := by
      calc
        η * Real.pi ≤ (ε / (4 * Real.pi)) * Real.pi :=
          mul_le_mul_of_nonneg_right hη_le2 Real.pi_pos.le
        _ = ε / 4 := by field_simp
    linarith
  let a : ℕ → ℕ := fun n => Nat.ceil (δ * (n + 2 : ℝ))
  let b : ℕ → ℕ := fun n => (n + 2) - a n
  have ha_tend : Tendsto (fun n : ℕ => (a n : ℝ) / (n + 2 : ℝ)) atTop (𝓝 δ) := by
    have hinvN : Tendsto (fun n : ℕ => δ + 1 / (n + 2 : ℝ)) atTop (𝓝 δ) := by
      simpa using (tendsto_const_nhds (x := δ)).add
        ((tendsto_const_nhds (x := (1 : ℝ))).div_atTop
          (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds))
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hinvN ?_ ?_
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have hN : (0 : ℝ) < n + 2 := by positivity
      rw [le_div_iff₀ hN]
      exact Nat.le_ceil _
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have hN : (0 : ℝ) < n + 2 := by positivity
      rw [div_le_iff₀ hN]
      have hceil := Nat.ceil_lt_add_one (mul_nonneg hδ_pos.le hN.le)
      have hring : (δ + 1 / (n + 2 : ℝ)) * (n + 2 : ℝ) = δ * (n + 2 : ℝ) + 1 := by field_simp
      linarith
  have hb_tend : Tendsto (fun n : ℕ => (b n : ℝ) / (n + 2 : ℝ)) atTop (𝓝 (1 - δ)) := by
    have h1 : Tendsto (fun n : ℕ => 1 - (a n : ℝ) / (n + 2 : ℝ)) atTop (𝓝 (1 - δ)) :=
      (tendsto_const_nhds (x := (1 : ℝ))).sub ha_tend
    refine h1.congr' ?_
    have hev_lt : ∀ᶠ n : ℕ in atTop, (a n : ℝ) / (n + 2 : ℝ) < 1 / 4 :=
      ha_tend.eventually (gt_mem_nhds (by linarith))
    filter_upwards [hev_lt, eventually_ge_atTop 4] with n hlt hn
    have hN : (0 : ℝ) < n + 2 := by positivity
    have ha_lt_N : (a n : ℝ) < (n + 2 : ℝ) := (div_lt_one hN).mp (by linarith)
    have ha_le : a n ≤ n + 2 := by
      exact_mod_cast ha_lt_N.le
    dsimp [b]
    rw [Nat.cast_sub ha_le]
    push_cast
    field_simp
  have hm1_tend : Tendsto (fun n : ℕ => (((n + 2) / 2 : ℕ) : ℝ) / (n + 2 : ℝ)) atTop (𝓝 (1 / 2)) := by
    have hlo : Tendsto (fun n : ℕ => (1 : ℝ) / 2 - 1 / (n + 2 : ℝ)) atTop (𝓝 (1 / 2)) := by
      simpa using (tendsto_const_nhds (x := (1 / 2 : ℝ))).sub
        ((tendsto_const_nhds (x := (1 : ℝ))).div_atTop
          (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds))
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds ?_ ?_
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have hN : (0 : ℝ) < n + 2 := by positivity
      have hnat : n + 2 ≤ 2 * ((n + 2) / 2) + 1 := by omega
      have hreal : (n : ℝ) + 2 ≤ 2 * (((n + 2) / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast hnat
      have hring : (1 / 2 - 1 / (n + 2 : ℝ)) * (n + 2 : ℝ) = ((n + 2 : ℝ) - 2) / 2 := by
        field_simp
      rw [le_div_iff₀ hN, hring]
      linarith
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have hN : (0 : ℝ) < n + 2 := by positivity
      have hreal : 2 * (((n + 2) / 2 : ℕ) : ℝ) ≤ (n : ℝ) + 2 := by
        exact_mod_cast (by omega : 2 * ((n + 2) / 2) ≤ n + 2)
      rw [div_le_div_iff₀ hN (by norm_num)]
      linarith
  have hm2_tend : Tendsto (fun n : ℕ => (((n + 3) / 2 : ℕ) : ℝ) / (n + 2 : ℝ)) atTop (𝓝 (1 / 2)) := by
    have hhi : Tendsto (fun n : ℕ => (1 : ℝ) / 2 + 1 / (n + 2 : ℝ)) atTop (𝓝 (1 / 2)) := by
      simpa using (tendsto_const_nhds (x := (1 / 2 : ℝ))).add
        ((tendsto_const_nhds (x := (1 : ℝ))).div_atTop
          (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds))
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hhi ?_ ?_
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have hN : (0 : ℝ) < n + 2 := by positivity
      have hreal : (n : ℝ) + 2 ≤ 2 * (((n + 3) / 2 : ℕ) : ℝ) := by
        exact_mod_cast (by omega : n + 2 ≤ 2 * ((n + 3) / 2))
      rw [div_le_div_iff₀ (by norm_num) hN]
      linarith
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have hN : (0 : ℝ) < n + 2 := by positivity
      have hreal : 2 * (((n + 3) / 2 : ℕ) : ℝ) ≤ (n : ℝ) + 4 := by
        exact_mod_cast (by omega : 2 * ((n + 3) / 2) ≤ n + 4)
      have hring : (1 / 2 + 1 / (n + 2 : ℝ)) * (n + 2 : ℝ) = ((n + 2 : ℝ) + 2) / 2 := by
        field_simp
      rw [div_le_iff₀ hN, hring]
      linarith
  have hgeom_tend : Tendsto (fun n : ℕ =>
      (G ((b n : ℝ) / (n + 2 : ℝ)) - G ((a n : ℝ) / (n + 2 : ℝ))) -
        (G ((((n + 3) / 2 : ℕ) : ℝ) / (n + 2 : ℝ)) -
          G ((((n + 2) / 2 : ℕ) : ℝ) / (n + 2 : ℝ))))
      atTop (𝓝 (G (1 - δ) - G δ)) := by
    have hG := ((G_continuous.tendsto (1 - δ)).comp hb_tend).sub ((G_continuous.tendsto δ).comp ha_tend)
    have hmid : Tendsto (fun n : ℕ =>
        G ((((n + 3) / 2 : ℕ) : ℝ) / (n + 2 : ℝ)) -
          G ((((n + 2) / 2 : ℕ) : ℝ) / (n + 2 : ℝ)))
        atTop (𝓝 (G (1 / 2) - G (1 / 2))) :=
      ((G_continuous.tendsto (1 / 2)).comp hm2_tend).sub ((G_continuous.tendsto (1 / 2)).comp hm1_tend)
    simpa [sub_self] using hG.sub hmid
  have hlog_δ : Tendsto (fun n : ℕ => (1 + Real.log (δ * (n : ℝ))) / Real.log n) atTop (𝓝 1) := by
    have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have hmain : Tendsto (fun n : ℕ => (1 + Real.log δ) / Real.log n + 1) atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds.div_atTop hlog).add (tendsto_const_nhds (x := (1 : ℝ)))
    refine hmain.congr' ?_
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hlog_ne : Real.log (n : ℝ) ≠ 0 :=
      (Real.log_pos (by exact_mod_cast (by omega : 1 < n))).ne'
    rw [Real.log_mul hδ_pos.ne' hn0.ne']
    field_simp
    ring
  have hev_lower : ∀ᶠ n : ℕ in atTop, Real.pi - ε < sumConv q q n / Real.log n := by
    filter_upwards [eventually_ge_atTop 16,
      ha_tend.eventually (gt_mem_nhds (by linarith : δ < 1 / 4)),
      hgeom_tend.eventually (lt_mem_nhds hG_δ),
      hlog_δ.eventually (lt_mem_nhds (by linarith : 1 - η < 1)),
      (Tendsto.const_mul_atTop hδ_pos tendsto_natCast_atTop_atTop).eventually_ge_atTop 1]
      with n hn ha_lt hgeom hlog_ge hδn
    have hN : (0 : ℝ) < n + 2 := by positivity
    have hlog_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
    have ha1 : 1 ≤ a n := by
      have : (0 : ℝ) < a n := by
        have := Nat.le_ceil (δ * (n + 2 : ℝ))
        nlinarith
      exact_mod_cast this
    have ham : a n ≤ (n + 2) / 2 := by
      have hreal : (a n : ℝ) < (n + 2 : ℝ) / 4 := by
        have := (div_lt_iff₀ hN).mp ha_lt
        linarith
      have : a n ≤ (n + 2) / 2 := by
        have hnat : 4 * a n < n + 2 := by exact_mod_cast (by linarith : (4 * a n : ℝ) < n + 2)
        omega
      exact this
    have hmb : (n + 3) / 2 ≤ b n := by
      have hnat : 4 * a n < n + 2 := by
        have hreal : (a n : ℝ) < (n + 2 : ℝ) / 4 := by
          have := (div_lt_iff₀ hN).mp ha_lt
          linarith
        exact_mod_cast (by linarith : (4 * a n : ℝ) < n + 2)
      dsimp [b]
      omega
    have hbn : b n ≤ n + 1 := by dsimp [b]; omega
    have hsub_mid : Finset.Icc (a n) (b n) ⊆ Finset.Icc 1 (n + 1) := by
      intro k hk
      rw [mem_Icc] at hk ⊢
      omega
    have hweight : ∀ k ∈ Finset.Icc (a n) (b n),
        (1 - η) * (1 / Real.sqrt ((k : ℝ) * ((n + 2 : ℝ) - k))) ≤
          Real.sqrt ((1 + Real.log (k : ℝ)) * (1 + Real.log ((n + 2 : ℝ) - k))) /
            Real.sqrt ((k : ℝ) * ((n + 2 : ℝ) - k)) / Real.log (n : ℝ) := by
      intro k hk
      rw [mem_Icc] at hk
      have hk_ge : δ * (n : ℝ) ≤ k := by
        have h1 : δ * (n + 2 : ℝ) ≤ a n := Nat.le_ceil _
        have h2 : (a n : ℝ) ≤ k := by exact_mod_cast hk.1
        nlinarith
      have hnk_ge : δ * (n : ℝ) ≤ (n + 2 : ℝ) - k := by
        have h1 : δ * (n + 2 : ℝ) ≤ a n := Nat.le_ceil _
        have h2 : (k : ℝ) ≤ b n := by exact_mod_cast hk.2
        have hbn_eq : (b n : ℝ) = (n + 2 : ℝ) - (a n : ℝ) := by
          dsimp [b]
          rw [Nat.cast_sub (by omega : a n ≤ n + 2)]
          push_cast
          ring
        linarith
      have hdn_pos : 0 < δ * (n : ℝ) := by positivity
      have hk_log : 1 + Real.log (δ * (n : ℝ)) ≤ 1 + Real.log (k : ℝ) := by
        linarith [Real.log_le_log hdn_pos hk_ge]
      have hnk_log : 1 + Real.log (δ * (n : ℝ)) ≤ 1 + Real.log ((n + 2 : ℝ) - k) := by
        linarith [Real.log_le_log hdn_pos hnk_ge]
      have hbase_nn : 0 ≤ 1 + Real.log (δ * (n : ℝ)) := by
        linarith [Real.log_nonneg hδn]
      have hprod_ge : (1 + Real.log (δ * (n : ℝ))) ^ 2 ≤
          (1 + Real.log (k : ℝ)) * (1 + Real.log ((n + 2 : ℝ) - k)) := by
        rw [sq]
        exact mul_le_mul hk_log hnk_log hbase_nn (hbase_nn.trans hk_log)
      have hsqrt_ge : 1 + Real.log (δ * (n : ℝ)) ≤
          Real.sqrt ((1 + Real.log (k : ℝ)) * (1 + Real.log ((n + 2 : ℝ) - k))) := by
        calc
          1 + Real.log (δ * (n : ℝ)) = Real.sqrt ((1 + Real.log (δ * (n : ℝ))) ^ 2) :=
            (Real.sqrt_sq hbase_nn).symm
          _ ≤ _ := Real.sqrt_le_sqrt hprod_ge
      calc
        (1 - η) * (1 / Real.sqrt ((k : ℝ) * ((n + 2 : ℝ) - k)))
            ≤ ((1 + Real.log (δ * (n : ℝ))) / Real.log (n : ℝ)) *
                (1 / Real.sqrt ((k : ℝ) * ((n + 2 : ℝ) - k))) := by
          exact mul_le_mul_of_nonneg_right hlog_ge.le (by positivity)
        _ = (1 + Real.log (δ * (n : ℝ))) /
              Real.sqrt ((k : ℝ) * ((n + 2 : ℝ) - k)) / Real.log (n : ℝ) := by ring
        _ ≤ Real.sqrt ((1 + Real.log (k : ℝ)) * (1 + Real.log ((n + 2 : ℝ) - k))) /
              Real.sqrt ((k : ℝ) * ((n + 2 : ℝ) - k)) / Real.log (n : ℝ) := by
          gcongr
    have hsum_ge : (1 - η) * (Real.pi - ε / 2) ≤ sumConv q q n / Real.log n := by
      have h1 : Real.pi - ε / 2 ≤
          ∑ k ∈ Finset.Icc (a n) (b n), 1 / Real.sqrt ((k : ℝ) * ((n + 2 : ℝ) - k)) :=
        hgeom.le.trans (S0_mid_lower (by omega) ha1 ham hmb hbn)
      have h2 : (1 - η) * (Real.pi - ε / 2) ≤
          (1 - η) * ∑ k ∈ Finset.Icc (a n) (b n), 1 / Real.sqrt ((k : ℝ) * ((n + 2 : ℝ) - k)) :=
        mul_le_mul_of_nonneg_left h1 (by linarith)
      have h3 : (1 - η) * ∑ k ∈ Finset.Icc (a n) (b n), 1 / Real.sqrt ((k : ℝ) * ((n + 2 : ℝ) - k)) ≤
          ∑ k ∈ Finset.Icc (a n) (b n),
            Real.sqrt ((1 + Real.log (k : ℝ)) * (1 + Real.log ((n + 2 : ℝ) - k))) /
              Real.sqrt ((k : ℝ) * ((n + 2 : ℝ) - k)) / Real.log (n : ℝ) := by
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum hweight
      have h4 : ∑ k ∈ Finset.Icc (a n) (b n),
            Real.sqrt ((1 + Real.log (k : ℝ)) * (1 + Real.log ((n + 2 : ℝ) - k))) /
              Real.sqrt ((k : ℝ) * ((n + 2 : ℝ) - k)) / Real.log (n : ℝ) ≤
          sumConv q q n / Real.log n := by
        rw [sumConv_q_eq, Finset.sum_div]
        refine Finset.sum_le_sum_of_subset_of_nonneg hsub_mid ?_
        intro k _ _
        exact div_nonneg (div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hlog_pos.le
      exact h2.trans (h3.trans h4)
    linarith
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp (hev_upper.and hev_lower)
  refine ⟨N0, fun n hn => ?_⟩
  obtain ⟨hu, hl⟩ := hN0 n hn
  rw [Real.dist_eq, abs_lt]
  exact ⟨by linarith, by linarith⟩

lemma h1_proof : OMA.R_Erdos66_erdos_66_R1.H1 := by
  intro a ha
  have hanti : Antitone (fun i : ℕ => a * q i) := fun i j hij =>
    mul_le_mul_of_nonneg_left (q_antitone hij) ha.le
  have hnonneg : ∀ i : ℕ, 0 ≤ a * q i := fun i => mul_nonneg ha.le (q_nonneg i)
  refine ⟨hanti, hnonneg, a ^ 2 * Real.pi, mul_pos (sq_pos_of_pos ha) Real.pi_pos, ?_⟩
  have hmul : Tendsto (fun n : ℕ => a ^ 2 * (sumConv q q n / Real.log n))
      atTop (𝓝 (a ^ 2 * Real.pi)) :=
    tendsto_sumConv_q.const_mul (a ^ 2)
  refine hmul.congr fun n => ?_
  have hconv : sumConv (fun i => a * q i) (fun i => a * q i) n = a ^ 2 * sumConv q q n := by
    simp only [sumConv, Finset.mul_sum]
    refine Finset.sum_congr rfl fun xy _ => ?_
    ring
  change a ^ 2 * (sumConv q q n / Real.log n) =
    sumConv (fun i => a * q i) (fun i => a * q i) n / Real.log n
  rw [hconv]
  ring

end OMA.P_Erdos66_erdos_66_R1_H1

theorem OMA.solution : OMA.R_Erdos66_erdos_66_R1.H1 :=
  OMA.P_Erdos66_erdos_66_R1_H1.h1_proof
