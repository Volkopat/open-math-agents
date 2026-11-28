import OMAStatements.S_oeis_a293766

-- Problem: OEIS A293766, Kimberling's conjecture a(n)/a(n-1) -> (1 + sqrt(5))/2
-- Statement: statements/oeis-a293766.lean (declaration OMA.S_oeis_a293766.main)
-- Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)
--
-- Proof. Write the equation as a(n+2) = a(n+1) + a(n) + p(n). Here p(n) >= 2, so the terms of
-- a differ by at least 2. Thus one of two consecutive integers is a term of b, and
-- b(n+1) <= b(n) + 2, b(n) <= 2n + 2. So p(n) is at most linear in n. Let phi be the golden
-- ratio and d(n) = a(n+1) - phi a(n). Then d(n+1) = (1 - phi) d(n) + p(n) and |1 - phi| <= 1,
-- so |d(n)| is at most quadratic in n. But a(n) >= (3/2)^n, so d(n)/a(n) tends to 0, and
-- a(n+1)/a(n) = phi + d(n)/a(n).

namespace OMA.K293766

open Filter Topology

/-- The shifted ratio `(n + 1) ^ 2 / (3 / 2) ^ n` tends to zero. -/
lemma poly_over_exp :
    Tendsto (fun n : ℕ => ((n : ℝ) + 1) ^ 2 / ((3 : ℝ) / 2) ^ n) atTop (𝓝 0) := by
  have h := tendsto_pow_const_div_const_pow_of_one_lt 2 (show (1 : ℝ) < 3 / 2 by norm_num)
  have h2 := (tendsto_add_atTop_iff_nat 1).mpr h
  have h3 := h2.const_mul ((3 : ℝ) / 2)
  rw [mul_zero] at h3
  refine h3.congr fun n => ?_
  push_cast
  field_simp
  ring

/-- A Fibonacci-type recurrence with a perturbation of linear size has consecutive ratios that
tend to the golden ratio. -/
lemma ratio_tendsto (a p : ℕ → ℕ) (C : ℕ) (h0 : 1 ≤ a 0) (h1 : 2 ≤ a 1)
    (hrec : ∀ n, a (n + 2) = a (n + 1) + a n + p n) (hp : ∀ n, p n ≤ C * (n + 1)) :
    Tendsto (fun n : ℕ => (a (n + 1) : ℝ) / (a n : ℝ)) atTop (𝓝 ((1 + Real.sqrt 5) / 2)) := by
  have hphi : ((1 + Real.sqrt 5) / 2 : ℝ) = Real.goldenRatio := rfl
  rw [hphi]
  -- exponential growth
  have hgrow : ∀ n, ((3 : ℝ) / 2) ^ n ≤ (a n : ℝ) ∧ ((3 : ℝ) / 2) ^ (n + 1) ≤ (a (n + 1) : ℝ) := by
    intro n
    induction n with
    | zero =>
      constructor
      · simpa using (show (1 : ℝ) ≤ (a 0 : ℝ) by exact_mod_cast h0)
      · have : (2 : ℝ) ≤ (a 1 : ℝ) := by exact_mod_cast h1
        simp only [zero_add, pow_one]
        linarith
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      have hr : (a (n + 2) : ℝ) = (a (n + 1) : ℝ) + (a n : ℝ) + (p n : ℝ) := by
        exact_mod_cast hrec n
      have hpn : (0 : ℝ) ≤ (p n : ℝ) := Nat.cast_nonneg _
      have hpos : (0 : ℝ) < ((3 : ℝ) / 2) ^ n := by positivity
      rw [show n + 1 + 1 = n + 2 by ring, hr]
      have e1 : ((3 : ℝ) / 2) ^ (n + 2) = ((3 : ℝ) / 2) ^ n * (9 / 4) := by ring
      have e2 : ((3 : ℝ) / 2) ^ (n + 1) = ((3 : ℝ) / 2) ^ n * (3 / 2) := by ring
      rw [e1]
      rw [e2] at ih
      nlinarith [ih.1, ih.2]
  have hpos : ∀ n, (0 : ℝ) < (a n : ℝ) := fun n =>
    lt_of_lt_of_le (by positivity) (hgrow n).1
  -- the defect `d n = a (n + 1) - φ a n`
  set d : ℕ → ℝ := fun n => (a (n + 1) : ℝ) - Real.goldenRatio * (a n : ℝ) with hd
  have hdrec : ∀ n, d (n + 1) = Real.goldenConj * d n + (p n : ℝ) := by
    intro n
    have hr : (a (n + 2) : ℝ) = (a (n + 1) : ℝ) + (a n : ℝ) + (p n : ℝ) := by
      exact_mod_cast hrec n
    have hs : Real.goldenRatio + Real.goldenConj = 1 := Real.goldenRatio_add_goldenConj
    have hm : Real.goldenRatio * Real.goldenConj = -1 := Real.goldenRatio_mul_goldenConj
    simp only [hd]
    rw [show n + 1 + 1 = n + 2 by ring, hr]
    have e3 : Real.goldenConj = 1 - Real.goldenRatio := by linarith
    rw [e3] at hm ⊢
    nlinarith [hm]
  have hconj : |Real.goldenConj| ≤ 1 := by
    rw [abs_le]
    exact ⟨Real.neg_one_lt_goldenConj.le, (Real.goldenConj_neg.trans zero_lt_one).le⟩
  set E : ℝ := |d 0| + (C : ℝ) with hE
  have hE0 : 0 ≤ E := by positivity
  have hdb : ∀ n : ℕ, |d n| ≤ E * ((n : ℝ) + 1) ^ 2 := by
    intro n
    induction n with
    | zero =>
      have : (0 : ℝ) ≤ (C : ℝ) := Nat.cast_nonneg _
      simp only [Nat.cast_zero, zero_add, one_pow, mul_one, hE]
      linarith
    | succ n ih =>
      have hpC : (p n : ℝ) ≤ (C : ℝ) * ((n : ℝ) + 1) := by exact_mod_cast hp n
      have hpn : (0 : ℝ) ≤ (p n : ℝ) := Nat.cast_nonneg _
      have hC0 : (0 : ℝ) ≤ (C : ℝ) := Nat.cast_nonneg _
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
      have h4 : |d (n + 1)| ≤ |d n| + (p n : ℝ) := by
        rw [hdrec n]
        calc |Real.goldenConj * d n + (p n : ℝ)|
            ≤ |Real.goldenConj * d n| + |(p n : ℝ)| := abs_add_le _ _
          _ = |Real.goldenConj| * |d n| + (p n : ℝ) := by rw [abs_mul, abs_of_nonneg hpn]
          _ ≤ 1 * |d n| + (p n : ℝ) := by
              have := mul_le_mul_of_nonneg_right hconj (abs_nonneg (d n))
              linarith
          _ = |d n| + (p n : ℝ) := by ring
      have hEC : (C : ℝ) ≤ E := by
        have := abs_nonneg (d 0)
        simp only [hE]
        linarith
      push_cast
      nlinarith [mul_nonneg hE0 hn0, mul_nonneg hC0 hn0, mul_le_mul_of_nonneg_right hEC
        (show (0 : ℝ) ≤ (n : ℝ) + 1 by linarith)]
  -- the ratio is `φ + d n / a n`
  have hratio : ∀ n : ℕ, (a (n + 1) : ℝ) / (a n : ℝ) = Real.goldenRatio + d n / (a n : ℝ) := by
    intro n
    have := (hpos n).ne'
    simp only [hd]
    field_simp
    ring
  have hzero : Tendsto (fun n : ℕ => d n / (a n : ℝ)) atTop (𝓝 0) := by
    have hbound : Tendsto (fun n : ℕ => E * (((n : ℝ) + 1) ^ 2 / ((3 : ℝ) / 2) ^ n)) atTop (𝓝 0) := by
      have := poly_over_exp.const_mul E
      rwa [mul_zero] at this
    refine squeeze_zero_norm (fun n => ?_) hbound
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (hpos n)]
    have hg := (hgrow n).1
    have hgp : (0 : ℝ) < ((3 : ℝ) / 2) ^ n := by positivity
    calc |d n| / (a n : ℝ) ≤ E * ((n : ℝ) + 1) ^ 2 / (a n : ℝ) :=
          div_le_div_of_nonneg_right (hdb n) (hpos n).le
      _ ≤ E * ((n : ℝ) + 1) ^ 2 / ((3 : ℝ) / 2) ^ n :=
          div_le_div_of_nonneg_left (by positivity) hgp hg
      _ = E * (((n : ℝ) + 1) ^ 2 / ((3 : ℝ) / 2) ^ n) := by ring
  have hfin : Tendsto (fun n : ℕ => Real.goldenRatio + d n / (a n : ℝ)) atTop
      (𝓝 (Real.goldenRatio + 0)) := tendsto_const_nhds.add hzero
  rw [add_zero] at hfin
  exact hfin.congr fun n => (hratio n).symm

/-- The complement of a sequence with gaps of size at least two grows at most like `2 n + 2`. -/
lemma compl_bound (a b : ℕ → ℕ) (ha : StrictMono a) (hb : StrictMono b)
    (hpart : ∀ m : ℕ, 0 < m → (m ∈ Set.range a ↔ m ∉ Set.range b))
    (hgap : ∀ k, a k + 2 ≤ a (k + 1)) (hb0 : b 0 = 2) : ∀ n, b n ≤ 2 * n + 2 := by
  have hnot : ∀ m : ℕ, ¬ (m ∈ Set.range a ∧ m + 1 ∈ Set.range a) := by
    rintro m ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
    have hij : i < j := by
      rw [← ha.lt_iff_lt]
      omega
    have h1 : a (i + 1) ≤ a j := ha.monotone hij
    have h2 := hgap i
    omega
  intro n
  induction n with
  | zero => omega
  | succ n ih =>
    have hstep : b (n + 1) ≤ b n + 2 := by
      by_cases h1 : b n + 1 ∈ Set.range a
      · have h2 : b n + 2 ∉ Set.range a := fun h2 => hnot (b n + 1) ⟨h1, h2⟩
        have h3 : b n + 2 ∈ Set.range b := by
          by_contra hcon
          exact h2 ((hpart (b n + 2) (by omega)).mpr hcon)
        obtain ⟨j, hj⟩ := h3
        have hnj : n < j := by
          rw [← hb.lt_iff_lt]
          omega
        have := hb.monotone (show n + 1 ≤ j from hnj)
        omega
      · have h3 : b n + 1 ∈ Set.range b := by
          by_contra hcon
          exact h1 ((hpart (b n + 1) (by omega)).mpr hcon)
        obtain ⟨j, hj⟩ := h3
        have hnj : n < j := by
          rw [← hb.lt_iff_lt]
          omega
        have := hb.monotone (show n + 1 ≤ j from hnj)
        omega
    omega

theorem result (a b : ℕ → ℕ) (ha : StrictMono a) (hb : StrictMono b)
    (hpart : ∀ m : ℕ, 0 < m → (m ∈ Set.range a ↔ m ∉ Set.range b))
    (ha0 : a 0 = 1) (ha1 : a 1 = 3) (hb0 : b 0 = 2) (_hb1 : b 1 = 4)
    (hrec : ∀ n : ℕ, 2 ≤ n → a n = a (n - 1) + a (n - 2) + b (n - 1) + 3) :
    Tendsto (fun n : ℕ => (a (n + 1) : ℝ) / (a n : ℝ)) atTop (𝓝 ((1 + Real.sqrt 5) / 2)) := by
  have hrec' : ∀ n, a (n + 2) = a (n + 1) + a n + (b (n + 1) + 0 * n + 3) := by
    intro n
    have h := hrec (n + 2) (by omega)
    rw [show n + 2 - 1 = n + 1 by omega, show n + 2 - 2 = n by omega] at h
    omega
  have hb2 : ∀ n, 2 ≤ b n := by
    intro n
    have := hb.monotone (Nat.zero_le n)
    omega
  have hapos : ∀ n, 1 ≤ a n := by
    intro n
    have := ha.monotone (Nat.zero_le n)
    omega
  have hgap : ∀ k, a k + 2 ≤ a (k + 1) := by
    intro k
    cases k with
    | zero =>
      show a 0 + 2 ≤ a 1
      omega
    | succ k =>
      have h := hrec' k
      have h2 := hb2 (k + 1)
      have h3 := hapos k
      rw [show k + 1 + 1 = k + 2 by ring]
      omega
  have hbb := compl_bound a b ha hb hpart hgap hb0
  refine ratio_tendsto a (fun n => b (n + 1) + 0 * n + 3) 7 (by omega) (by omega) hrec' ?_
  intro n
  have h := hbb (n + 1)
  show b (n + 1) + 0 * n + 3 ≤ 7 * (n + 1)
  omega

end OMA.K293766

theorem OMA.solution : type_of% @OMA.S_oeis_a293766.main :=
  fun a b ha hb hpart ha0 ha1 hb0 hb1 hrec => OMA.K293766.result a b ha hb hpart ha0 ha1 hb0 hb1 hrec
