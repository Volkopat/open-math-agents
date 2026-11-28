import OMAStatements.S_mse_4398439

namespace OMA.P_mse_4398439

private lemma sqrt2_lt : Real.sqrt 2 < 14143 / 10000 := by
  rw [Real.sqrt_lt' (by norm_num)]
  norm_num

private lemma gt_sqrt2 : (14142 / 10000 : ℝ) < Real.sqrt 2 := by
  rw [Real.lt_sqrt (by norm_num)]
  norm_num

private lemma three_sqrt2_sub_four_pos : (0 : ℝ) < 3 * Real.sqrt 2 - 4 := by
  have h := gt_sqrt2; linarith

private lemma C1_q19_nonneg (p : ℝ) (hlo : 13 / 10 ≤ p) (hhi : p ≤ 43 / 10) :
    0 ≤ 4 * (p ^ 2 - 2 * (19 / 40 : ℝ) + 2) -
      (3 * (14143 / 10000 : ℝ) - p) ^ 2 *
        (2 * (19 / 40 : ℝ) ^ 2 + p ^ 2 - 2 * (19 / 40 : ℝ)) := by
  by_cases h1 : p ≤ 154 / 100
  · set t : ℝ := p - 13 / 10
    set s : ℝ := 154 / 100 - p
    have ht : 0 ≤ t := by simp only [t]; linarith
    have hs : 0 ≤ s := by simp only [s]; linarith
    have hts : s + t = 24 / 100 := by simp only [t, s]; ring
    have hp : p = (13 / 10 * s + 154 / 100 * t) / (s + t) := by
      have hne : s + t ≠ 0 := by linarith
      field_simp; simp only [t, s]; ring
    have hmul : (s + t) ^ 4 * (4 * (p ^ 2 - 2 * (19 / 40 : ℝ) + 2) -
        (3 * (14143 / 10000 : ℝ) - p) ^ 2 *
          (2 * (19 / 40 : ℝ) ^ 2 + p ^ 2 - 2 * (19 / 40 : ℝ))) =
      (7957836663 / 2000000000000 : ℝ) * t ^ 4 +
    (14822577399 / 500000000000 : ℝ) * t ^ 3 * s +
    (725811460389 / 1000000000000 : ℝ) * t ^ 2 * s ^ 2 +
    (134645127051 / 100000000000 : ℝ) * t * s ^ 3 +
    (51439062927 / 80000000000 : ℝ) * s ^ 4 := by
      have hne : s + t ≠ 0 := by linarith
      rw [hp]; field_simp; ring
    have hpos : 0 ≤ (s + t) ^ 4 * (4 * (p ^ 2 - 2 * (19 / 40 : ℝ) + 2) -
        (3 * (14143 / 10000 : ℝ) - p) ^ 2 *
          (2 * (19 / 40 : ℝ) ^ 2 + p ^ 2 - 2 * (19 / 40 : ℝ))) := by
      rw [hmul]; positivity
    have hst4 : 0 < (s + t) ^ 4 := by
      have : 0 < s + t := by linarith
      positivity
    nlinarith
  · by_cases h2 : p ≤ 16 / 10
    · set t : ℝ := p - 154 / 100
      set s : ℝ := 16 / 10 - p
      have ht : 0 ≤ t := by simp only [t]; linarith
      have hs : 0 ≤ s := by simp only [s]; linarith
      have hts : s + t = 6 / 100 := by simp only [t, s]; ring
      have hp : p = (154 / 100 * s + 16 / 10 * t) / (s + t) := by
        have hne : s + t ≠ 0 := by linarith
        field_simp; simp only [t, s]; ring
      have hmul : (s + t) ^ 4 * (4 * (p ^ 2 - 2 * (19 / 40 : ℝ) + 2) -
          (3 * (14143 / 10000 : ℝ) - p) ^ 2 *
            (2 * (19 / 40 : ℝ) ^ 2 + p ^ 2 - 2 * (19 / 40 : ℝ))) =
        (3386624391 / 80000000000 : ℝ) * t ^ 4 +
    (8871462327 / 100000000000 : ℝ) * t ^ 3 * s +
    (54873243009 / 1000000000000 : ℝ) * t ^ 2 * s ^ 2 +
    (6241651479 / 500000000000 : ℝ) * t * s ^ 3 +
    (7957836663 / 2000000000000 : ℝ) * s ^ 4 := by
        have hne : s + t ≠ 0 := by linarith
        rw [hp]; field_simp; ring
      have hpos : 0 ≤ (s + t) ^ 4 * (4 * (p ^ 2 - 2 * (19 / 40 : ℝ) + 2) -
          (3 * (14143 / 10000 : ℝ) - p) ^ 2 *
            (2 * (19 / 40 : ℝ) ^ 2 + p ^ 2 - 2 * (19 / 40 : ℝ))) := by
        rw [hmul]; positivity
      have hst4 : 0 < (s + t) ^ 4 := by
        have : 0 < s + t := by linarith
        positivity
      nlinarith
    · set t : ℝ := p - 16 / 10
      set s : ℝ := 43 / 10 - p
      have ht : 0 ≤ t := by simp only [t]; linarith
      have hs : 0 ≤ s := by simp only [s]; linarith
      have hts : s + t = 27 / 10 := by simp only [t, s]; ring
      have hp : p = (16 / 10 * s + 43 / 10 * t) / (s + t) := by
        have hne : s + t ≠ 0 := by linarith
        field_simp; simp only [t, s]; ring
      have hmul : (s + t) ^ 4 * (4 * (p ^ 2 - 2 * (19 / 40 : ℝ) + 2) -
          (3 * (14143 / 10000 : ℝ) - p) ^ 2 *
            (2 * (19 / 40 : ℝ) ^ 2 + p ^ 2 - 2 * (19 / 40 : ℝ))) =
        (6248107291887 / 80000000000 : ℝ) * t ^ 4 +
    (4502969866791 / 20000000000 : ℝ) * t ^ 3 * s +
    (3906311897529 / 40000000000 : ℝ) * t ^ 2 * s ^ 2 +
    (75941561043 / 20000000000 : ℝ) * t * s ^ 3 +
    (3386624391 / 80000000000 : ℝ) * s ^ 4 := by
        have hne : s + t ≠ 0 := by linarith
        rw [hp]; field_simp; ring
      have hpos : 0 ≤ (s + t) ^ 4 * (4 * (p ^ 2 - 2 * (19 / 40 : ℝ) + 2) -
          (3 * (14143 / 10000 : ℝ) - p) ^ 2 *
            (2 * (19 / 40 : ℝ) ^ 2 + p ^ 2 - 2 * (19 / 40 : ℝ))) := by
        rw [hmul]; positivity
      have hst4 : 0 < (s + t) ^ 4 := by
        have : 0 < s + t := by linarith
        positivity
      nlinarith

private lemma C1_qp_nonneg (p : ℝ) (hlo : 0 ≤ p) (hhi : p ≤ 7 / 5) :
    0 ≤ 4 * (p ^ 2 / 2 + 2) -
      (3 * (14143 / 10000 : ℝ) - p) ^ 2 * (p ^ 4 / 8 + p ^ 2 / 2) := by
  set t : ℝ := p
  set s : ℝ := 7 / 5 - p
  have ht : 0 ≤ t := hlo
  have hs : 0 ≤ s := by simp only [s]; linarith
  have hts : s + t = 7 / 5 := by simp only [t, s]; ring
  have hp : p = ((0 : ℝ) * s + (7 / 5 : ℝ) * t) / (s + t) := by
    have hne : s + t ≠ 0 := by linarith
    field_simp; simp only [t, s]; ring
  have hmul : (s + t) ^ 6 * (4 * (p ^ 2 / 2 + 2) -
      (3 * (14143 / 10000 : ℝ) - p) ^ 2 * (p ^ 4 / 8 + p ^ 2 / 2)) =
    (59273092659 / 500000000000 : ℝ) * t ^ 6 +
    (3153211885759 / 250000000000 : ℝ) * t ^ 5 * s +
    (31014578876159 / 500000000000 : ℝ) * t ^ 4 * s ^ 2 +
    (145942364991 / 1250000000 : ℝ) * t ^ 3 * s ^ 3 +
    (531389217991 / 5000000000 : ℝ) * t ^ 2 * s ^ 4 +
    (48 : ℝ) * t * s ^ 5 +
    (8 : ℝ) * s ^ 6 := by
    have hne : s + t ≠ 0 := by linarith
    rw [hp]; field_simp; ring
  have hpos : 0 ≤ (s + t) ^ 6 * (4 * (p ^ 2 / 2 + 2) -
      (3 * (14143 / 10000 : ℝ) - p) ^ 2 * (p ^ 4 / 8 + p ^ 2 / 2)) := by
    rw [hmul]; positivity
  have hst6 : 0 < (s + t) ^ 6 := by
    have : 0 < s + t := by linarith
    positivity
  nlinarith

private lemma case1_pq (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (hpq : 4 * q ≤ p ^ 2)
    (hq19 : q ≤ 19 / 40) :
    3 * Real.sqrt 2 ≤ p + 2 * Real.sqrt ((p ^ 2 - 2 * q + 2) / (2 * q ^ 2 + p ^ 2 - 2 * q)) := by
  by_cases hpbig : 3 * Real.sqrt 2 ≤ p
  · have hsqrt : 0 ≤ Real.sqrt ((p ^ 2 - 2 * q + 2) / (2 * q ^ 2 + p ^ 2 - 2 * q)) :=
      Real.sqrt_nonneg _
    linarith
  · push Not at hpbig
    have hden : 0 < 2 * q ^ 2 + p ^ 2 - 2 * q := by nlinarith
    have hnum : 0 < p ^ 2 - 2 * q + 2 := by nlinarith
    have hgoal : (3 * Real.sqrt 2 - p) ^ 2 ≤
        4 * ((p ^ 2 - 2 * q + 2) / (2 * q ^ 2 + p ^ 2 - 2 * q)) := by
      rw [mul_div_assoc', le_div_iff₀ hden]
      let g : ℝ → ℝ := fun x =>
        4 * (p ^ 2 - 2 * x + 2) - (3 * Real.sqrt 2 - p) ^ 2 * (2 * x ^ 2 + p ^ 2 - 2 * x)
      have hg0 : 0 ≤ g 0 := by
        simp only [g]
        have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
        have hfac : 4 * (p ^ 2 - 2 * 0 + 2) - (3 * Real.sqrt 2 - p) ^ 2 * (2 * 0 ^ 2 + p ^ 2 - 2 * 0) =
            (p - Real.sqrt 2) ^ 2 * (p * (4 * Real.sqrt 2 - p) + 4) := by
          have hL : 4 * (p ^ 2 - 2 * 0 + 2) - (3 * Real.sqrt 2 - p) ^ 2 * (2 * 0 ^ 2 + p ^ 2 - 2 * 0) =
              -p ^ 4 + 6 * p ^ 3 * Real.sqrt 2 - 14 * p ^ 2 + 8 := by
            linear_combination -9 * p ^ 2 * hs2
          have hR : (p - Real.sqrt 2) ^ 2 * (p * (4 * Real.sqrt 2 - p) + 4) =
              -p ^ 4 + 6 * p ^ 3 * Real.sqrt 2 - 14 * p ^ 2 + 8 := by
            linear_combination (-9 * p ^ 2 + 4 * p * Real.sqrt 2 + 4) * hs2
          linarith
        rw [hfac]
        have hsq : 0 ≤ (p - Real.sqrt 2) ^ 2 := sq_nonneg _
        have hpos2 : 0 ≤ p * (4 * Real.sqrt 2 - p) + 4 := by
          have h1 : 0 < 4 * Real.sqrt 2 - p := by
            have := gt_sqrt2; linarith
          nlinarith
        exact mul_nonneg hsq hpos2
      have hconcave : ∀ u : ℝ, 0 < u → q ≤ u → 0 ≤ g u → 0 ≤ g q := by
        intro u hu hqu hgu
        have hident : u * g q = (u - q) * g 0 + q * g u +
            2 * (3 * Real.sqrt 2 - p) ^ 2 * u * q * (u - q) := by
          simp only [g]; ring
        have hrhs : 0 ≤ u * g q := by
          rw [hident]
          have h1 : 0 ≤ (u - q) * g 0 := mul_nonneg (by linarith) hg0
          have h2 : 0 ≤ q * g u := mul_nonneg (le_of_lt hq) hgu
          have h3 : 0 ≤ 2 * (3 * Real.sqrt 2 - p) ^ 2 * u * q * (u - q) := by
            have h4 : 0 ≤ u - q := by linarith
            positivity
          linarith
        nlinarith
      have hshi_sub : 0 < 3 * Real.sqrt 2 - p := by linarith
      have hshi_le : (3 * Real.sqrt 2 - p) ^ 2 ≤ (3 * (14143 / 10000 : ℝ) - p) ^ 2 := by
        have hs := sqrt2_lt
        nlinarith
      have hgq : 0 ≤ g q := by
        by_cases hp19 : p ^ 2 ≤ 19 / 10
        · apply hconcave (p ^ 2 / 4) (by positivity) (by linarith)
          have hp75 : p ≤ 7 / 5 := by nlinarith
          have hc := C1_qp_nonneg p (le_of_lt hp) hp75
          have hdenp : 0 ≤ p ^ 4 / 8 + p ^ 2 / 2 := by positivity
          have heq : g (p ^ 2 / 4) =
              4 * (p ^ 2 / 2 + 2) - (3 * Real.sqrt 2 - p) ^ 2 * (p ^ 4 / 8 + p ^ 2 / 2) := by
            simp only [g]; ring
          rw [heq]
          nlinarith
        · push Not at hp19
          apply hconcave (19 / 40) (by norm_num) hq19
          have hp13 : 13 / 10 ≤ p := by nlinarith
          have hp43 : p ≤ 43 / 10 := by
            have := sqrt2_lt; linarith
          have hc := C1_q19_nonneg p hp13 hp43
          have hden19 : 0 ≤ 2 * (19 / 40 : ℝ) ^ 2 + p ^ 2 - 2 * (19 / 40 : ℝ) := by nlinarith
          simp only [g]
          nlinarith
      simp only [g] at hgq
      linarith
    have hsqrt_le : 3 * Real.sqrt 2 - p ≤
        2 * Real.sqrt ((p ^ 2 - 2 * q + 2) / (2 * q ^ 2 + p ^ 2 - 2 * q)) := by
      have hr : 0 ≤ 2 * Real.sqrt ((p ^ 2 - 2 * q + 2) / (2 * q ^ 2 + p ^ 2 - 2 * q)) := by
        positivity
      have hsq : (3 * Real.sqrt 2 - p) ^ 2 ≤
          (2 * Real.sqrt ((p ^ 2 - 2 * q + 2) / (2 * q ^ 2 + p ^ 2 - 2 * q))) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (div_nonneg (le_of_lt hnum) (le_of_lt hden))]
        linarith
      nlinarith
    linarith

private lemma ineq6_pq (p q : ℝ) (hp : 0 < p) (hpq : 4 * q ≤ p ^ 2) (hq19 : 19 / 40 ≤ q) :
    (9 * p ^ 4 + 8 * p ^ 2 + (32 - 20 * p ^ 2) * q) / (2 * p ^ 3 * (p ^ 2 + 4)) ≤
      Real.sqrt ((p ^ 2 - 2 * q + 2) / (2 * q ^ 2 + p ^ 2 - 2 * q)) := by
  have hden : 0 < 2 * q ^ 2 + p ^ 2 - 2 * q := by nlinarith
  have hnum : 0 < p ^ 2 - 2 * q + 2 := by nlinarith
  have hdenL : 0 < 2 * p ^ 3 * (p ^ 2 + 4) := by positivity
  by_cases hneg : (9 * p ^ 4 + 8 * p ^ 2 + (32 - 20 * p ^ 2) * q) / (2 * p ^ 3 * (p ^ 2 + 4)) ≤ 0
  · exact le_trans hneg (Real.sqrt_nonneg _)
  · push Not at hneg
    have hsq : ((9 * p ^ 4 + 8 * p ^ 2 + (32 - 20 * p ^ 2) * q) / (2 * p ^ 3 * (p ^ 2 + 4))) ^ 2 ≤
        (p ^ 2 - 2 * q + 2) / (2 * q ^ 2 + p ^ 2 - 2 * q) := by
      rw [div_pow, div_le_div_iff₀ (by positivity) hden]
      set u : ℝ := p ^ 2 - 4 * q
      set v : ℝ := q - 19 / 40
      have hu : 0 ≤ u := by simp only [u]; linarith
      have hv : 0 ≤ v := by simp only [v]; linarith
      have hp2 : p ^ 2 = 4 * q + u := by simp only [u]; ring
      have hqv : q = 19 / 40 + v := by simp only [v]; ring
      have hdiff : (p ^ 2 - 2 * q + 2) * (2 * p ^ 3 * (p ^ 2 + 4)) ^ 2 -
          (9 * p ^ 4 + 8 * p ^ 2 + (32 - 20 * p ^ 2) * q) ^ 2 * (2 * q ^ 2 + p ^ 2 - 2 * q) =
          u * ((u - 5 / 2) ^ 2 * ((4 : ℝ) * u ^ 3 +
    (104 / 5 : ℝ) * u ^ 2 +
    (27999 / 800 : ℝ) * u +
    (2077 / 250 : ℝ)) + ((228823 / 10000 : ℝ) * u +
    (18683679 / 100000 : ℝ)) + ((88 : ℝ) * u ^ 4 * v +
    (638 : ℝ) * u ^ 3 * v ^ 2 +
    (2441 / 10 : ℝ) * u ^ 3 * v +
    (1968 : ℝ) * u ^ 2 * v ^ 3 +
    (10822 / 5 : ℝ) * u ^ 2 * v ^ 2 +
    (37209 / 100 : ℝ) * u ^ 2 * v +
    (2528 : ℝ) * u * v ^ 4 +
    (29616 / 5 : ℝ) * u * v ^ 3 +
    (99857 / 25 : ℝ) * u * v ^ 2 +
    (626511 / 500 : ℝ) * u * v +
    (1024 : ℝ) * v ^ 5 +
    (4480 : ℝ) * v ^ 4 +
    (36128 / 5 : ℝ) * v ^ 3 +
    (133228 / 25 : ℝ) * v ^ 2 +
    (915857 / 500 : ℝ) * v)) := by
        have hstep1 : (p ^ 2 - 2 * q + 2) * (2 * p ^ 3 * (p ^ 2 + 4)) ^ 2 -
            (9 * p ^ 4 + 8 * p ^ 2 + (32 - 20 * p ^ 2) * q) ^ 2 * (2 * q ^ 2 + p ^ 2 - 2 * q) =
            (p ^ 2 - 4 * q) * (4 * (p ^ 2) ^ 5 + 8 * (p ^ 2) ^ 4 * q - 41 * (p ^ 2) ^ 4 -
              130 * (p ^ 2) ^ 3 * q ^ 2 + 294 * (p ^ 2) ^ 3 * q - 16 * (p ^ 2) ^ 3 +
              200 * (p ^ 2) ^ 2 * q ^ 3 - 232 * (p ^ 2) ^ 2 * q ^ 2 - 160 * (p ^ 2) ^ 2 * q +
              64 * (p ^ 2) ^ 2 - 640 * (p ^ 2) * q ^ 3 + 1024 * (p ^ 2) * q ^ 2 -
              128 * (p ^ 2) * q + 512 * q ^ 3 - 512 * q ^ 2) := by ring
        rw [hstep1, show p ^ 2 - 4 * q = u from rfl, hp2, hqv]
        ring
      have hpos : 0 ≤ u * ((u - 5 / 2) ^ 2 * ((4 : ℝ) * u ^ 3 +
    (104 / 5 : ℝ) * u ^ 2 +
    (27999 / 800 : ℝ) * u +
    (2077 / 250 : ℝ)) + ((228823 / 10000 : ℝ) * u +
    (18683679 / 100000 : ℝ)) + ((88 : ℝ) * u ^ 4 * v +
    (638 : ℝ) * u ^ 3 * v ^ 2 +
    (2441 / 10 : ℝ) * u ^ 3 * v +
    (1968 : ℝ) * u ^ 2 * v ^ 3 +
    (10822 / 5 : ℝ) * u ^ 2 * v ^ 2 +
    (37209 / 100 : ℝ) * u ^ 2 * v +
    (2528 : ℝ) * u * v ^ 4 +
    (29616 / 5 : ℝ) * u * v ^ 3 +
    (99857 / 25 : ℝ) * u * v ^ 2 +
    (626511 / 500 : ℝ) * u * v +
    (1024 : ℝ) * v ^ 5 +
    (4480 : ℝ) * v ^ 4 +
    (36128 / 5 : ℝ) * v ^ 3 +
    (133228 / 25 : ℝ) * v ^ 2 +
    (915857 / 500 : ℝ) * v)) := by
        positivity
      linarith
    have hsqrt_sq : (Real.sqrt ((p ^ 2 - 2 * q + 2) / (2 * q ^ 2 + p ^ 2 - 2 * q))) ^ 2 =
        (p ^ 2 - 2 * q + 2) / (2 * q ^ 2 + p ^ 2 - 2 * q) :=
      Real.sq_sqrt (div_nonneg (le_of_lt hnum) (le_of_lt hden))
    have hsr : 0 ≤ Real.sqrt ((p ^ 2 - 2 * q + 2) / (2 * q ^ 2 + p ^ 2 - 2 * q)) :=
      Real.sqrt_nonneg _
    nlinarith

private lemma term4_lb (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (hpq : 4 * q ≤ p ^ 2) :
    ((8 * p ^ 4 + 384) * q - 64 * p ^ 2) / (p ^ 4 + 16) ^ 2 ≤
      1 / (p ^ 2 - 2 * q + (p ^ 2 - 2 * q) / q ^ 2) := by
  have hp2q : 0 < p ^ 2 - 2 * q := by nlinarith
  have hq2 : 0 < q ^ 2 := by positivity
  have hden1 : 0 < p ^ 2 - 2 * q + (p ^ 2 - 2 * q) / q ^ 2 := by positivity
  have hden2 : 0 < (p ^ 4 + 16) ^ 2 := by positivity
  rw [div_le_div_iff₀ hden2 hden1]
  have hmul : q ^ 2 * (1 * (p ^ 4 + 16) ^ 2 -
      ((8 * p ^ 4 + 384) * q - 64 * p ^ 2) * (p ^ 2 - 2 * q + (p ^ 2 - 2 * q) / q ^ 2)) =
      ((p ^ 2 * q - 4) ^ 2 + 48 * q ^ 2 + 48) * (p ^ 2 - 4 * q) ^ 2 := by
    field_simp; ring
  have hpos : 0 ≤ ((p ^ 2 * q - 4) ^ 2 + 48 * q ^ 2 + 48) * (p ^ 2 - 4 * q) ^ 2 := by positivity
  nlinarith

private lemma ineq7_at_p2div4 (p : ℝ) (hp : 0 < p) :
    3 * Real.sqrt 2 ≤
      p + (9 * p ^ 4 + 8 * p ^ 2 + (32 - 20 * p ^ 2) * (p ^ 2 / 4)) / (p ^ 3 * (p ^ 2 + 4)) +
        4 * (3 * Real.sqrt 2 - 4) * ((8 * p ^ 4 + 384) * (p ^ 2 / 4) - 64 * p ^ 2) /
          (p ^ 4 + 16) ^ 2 := by
  have hden1 : 0 < p ^ 3 * (p ^ 2 + 4) := by positivity
  have hden2 : 0 < (p ^ 4 + 16) ^ 2 := by positivity
  have hden : 0 < p * (p ^ 4 + 16) := by positivity
  have hident :
      p + (9 * p ^ 4 + 8 * p ^ 2 + (32 - 20 * p ^ 2) * (p ^ 2 / 4)) / (p ^ 3 * (p ^ 2 + 4)) +
        4 * (3 * Real.sqrt 2 - 4) * ((8 * p ^ 4 + 384) * (p ^ 2 / 4) - 64 * p ^ 2) /
          (p ^ 4 + 16) ^ 2 - 3 * Real.sqrt 2 =
      (p - 2) ^ 2 *
        (p ^ 4 + (4 - 3 * Real.sqrt 2) * p ^ 3 + (16 - 12 * Real.sqrt 2) * p ^ 2 +
          (16 - 12 * Real.sqrt 2) * p + 16) / (p * (p ^ 4 + 16)) := by
    have hne1 : p ^ 3 * (p ^ 2 + 4) ≠ 0 := ne_of_gt hden1
    have hne2 : (p ^ 4 + 16) ^ 2 ≠ 0 := ne_of_gt hden2
    have hne3 : p * (p ^ 4 + 16) ≠ 0 := ne_of_gt hden
    field_simp; ring
  have hquart : 0 ≤ p ^ 4 + (4 - 3 * Real.sqrt 2) * p ^ 3 + (16 - 12 * Real.sqrt 2) * p ^ 2 +
      (16 - 12 * Real.sqrt 2) * p + 16 := by
    have hs := sqrt2_lt
    have h1 : 4 - 3 * Real.sqrt 2 ≥ -(1 / 4 : ℝ) := by linarith
    have h2 : 16 - 12 * Real.sqrt 2 ≥ -(1 : ℝ) := by linarith
    have hp3 : 0 ≤ p ^ 3 := by positivity
    have hp2 : 0 ≤ p ^ 2 := by positivity
    have hlb : p ^ 4 - (1 / 4 : ℝ) * p ^ 3 - p ^ 2 - p + 16 ≤
        p ^ 4 + (4 - 3 * Real.sqrt 2) * p ^ 3 + (16 - 12 * Real.sqrt 2) * p ^ 2 +
          (16 - 12 * Real.sqrt 2) * p + 16 := by nlinarith
    have hpos : 0 ≤ p ^ 4 - (1 / 4 : ℝ) * p ^ 3 - p ^ 2 - p + 16 := by
      have : p ^ 4 - (1 / 4 : ℝ) * p ^ 3 - p ^ 2 - p + 16 =
          (p ^ 2 - p / 8 - 1) ^ 2 + (63 / 64 : ℝ) * (p - 40 / 63) ^ 2 + 920 / 63 := by ring
      rw [this]; positivity
    linarith
  have hnonneg : 0 ≤ (p - 2) ^ 2 *
      (p ^ 4 + (4 - 3 * Real.sqrt 2) * p ^ 3 + (16 - 12 * Real.sqrt 2) * p ^ 2 +
        (16 - 12 * Real.sqrt 2) * p + 16) / (p * (p ^ 4 + 16)) :=
    div_nonneg (mul_nonneg (sq_nonneg _) hquart) (le_of_lt hden)
  linarith

private def P7_poly (p : ℝ) : ℝ :=
  (50000 : ℝ) * p ^ 14 +
    (-212145 : ℝ) * p ^ 13 +
    (650000 : ℝ) * p ^ 12 +
    (-848580 : ℝ) * p ^ 11 +
    (1525000 : ℝ) * p ^ 10 +
    (-6604036 : ℝ) * p ^ 9 +
    (21560000 : ℝ) * p ^ 8 +
    (-29525264 : ℝ) * p ^ 7 +
    (10400000 : ℝ) * p ^ 6 +
    (-57884608 : ℝ) * p ^ 5 +
    (190720000 : ℝ) * p ^ 4 +
    (-181792512 : ℝ) * p ^ 3 +
    (-19200000 : ℝ) * p ^ 2 +
    (194560000 : ℝ)

private lemma P7_lo_nonneg (p : ℝ) (hp13 : 13 / 10 ≤ p) (hp17 : p ≤ 17 / 10) :
    0 ≤ P7_poly p := by
  set t : ℝ := p - 13 / 10
  set s : ℝ := 17 / 10 - p
  have ht : 0 ≤ t := by simp only [t]; linarith
  have hs : 0 ≤ s := by simp only [s]; linarith
  have hmul : (4 / 10 : ℝ) ^ 14 * P7_poly p =
      (93312404441906821227 / 2000000000000 : ℝ) * t ^ 14 +
    (571425645973769479583 / 1000000000000 : ℝ) * t ^ 13 * s +
    (1382751378158154829273 / 400000000000 : ℝ) * t ^ 12 * s ^ 2 +
    (6809761464727624692711 / 500000000000 : ℝ) * t ^ 11 * s ^ 3 +
    (77111718376634081320923 / 2000000000000 : ℝ) * t ^ 10 * s ^ 4 +
    (81760938733099049602953 / 1000000000000 : ℝ) * t ^ 9 * s ^ 5 +
    (264482612953479017194053 / 2000000000000 : ℝ) * t ^ 8 * s ^ 6 +
    (8209826825209031346117 / 50000000000 : ℝ) * t ^ 7 * s ^ 7 +
    (312661128200781705519097 / 2000000000000 : ℝ) * t ^ 6 * s ^ 8 +
    (113176367267320193934657 / 1000000000000 : ℝ) * t ^ 5 * s ^ 9 +
    (122425577398177731700367 / 2000000000000 : ℝ) * t ^ 4 * s ^ 10 +
    (11982246710697827562039 / 500000000000 : ℝ) * t ^ 3 * s ^ 11 +
    (2567218101611217788941 / 400000000000 : ℝ) * t ^ 2 * s ^ 12 +
    (1052595423508346686967 / 1000000000000 : ℝ) * t * s ^ 13 +
    (159563117772912081263 / 2000000000000 : ℝ) * s ^ 14 := by
    simp only [P7_poly, t, s]
    ring
  have hpos : 0 ≤ (4 / 10 : ℝ) ^ 14 * P7_poly p := by
    rw [hmul]; positivity
  have hc : (0 : ℝ) < (4 / 10 : ℝ) ^ 14 := by positivity
  nlinarith

private lemma P7_hi_nonneg (p : ℝ) (hp17 : 17 / 10 ≤ p) :
    0 ≤ P7_poly p := by
  set u : ℝ := p - 17 / 10
  have hu : 0 ≤ u := by simp only [u]; linarith
  have hp_eq : p = 17 / 10 + u := by simp only [u]; ring
  have hid : P7_poly p = (50000 : ℝ) * u ^ 14 +
    (977855 : ℝ) * u ^ 13 +
    (18222191 / 2 : ℝ) * u ^ 12 +
    (540062941 / 10 : ℝ) * u ^ 11 +
    (22957140089 / 100 : ℝ) * u ^ 10 +
    (296559123213 / 400 : ℝ) * u ^ 9 +
    (37316944524589 / 20000 : ℝ) * u ^ 8 +
    (185030531386671 / 50000 : ℝ) * u ^ 7 +
    (2909834594374557 / 500000 : ℝ) * u ^ 6 +
    (143613265862005957 / 20000000 : ℝ) * u ^ 5 +
    (265950054814276741 / 40000000 : ℝ) * u ^ 4 +
    (4291806840037774197 / 1000000000 : ℝ) * u ^ 3 +
    (17128715615196512777 / 10000000000 : ℝ) * u ^ 2 +
    (40880592559789134503 / 200000000000 : ℝ) * u +
    (93312404441906821227 / 2000000000000 : ℝ) := by
    simp only [P7_poly]
    rw [hp_eq]; ring
  rw [hid]; positivity

private lemma P7_clear_eq (p : ℝ) :
    50000 * p ^ 3 * (p ^ 2 + 4) * (p ^ 4 + 16) ^ 2 * (p - 3 * (14143 / 10000)) +
    50000 * (p ^ 4 + 16) ^ 2 * (9 * p ^ 4 + 8 * p ^ 2 + (32 - 20 * p ^ 2) * (19 / 40)) +
    50000 * p ^ 3 * (p ^ 2 + 4) * (4 * (3 * (14143 / 10000) - 4) *
      ((8 * p ^ 4 + 384) * (19 / 40) - 64 * p ^ 2)) = P7_poly p := by
  simp only [P7_poly]; ring

private lemma ineq7_at_19div40 (p : ℝ) (hp13 : 13 / 10 ≤ p) :
    3 * Real.sqrt 2 ≤
      p + (9 * p ^ 4 + 8 * p ^ 2 + (32 - 20 * p ^ 2) * (19 / 40 : ℝ)) / (p ^ 3 * (p ^ 2 + 4)) +
        4 * (3 * Real.sqrt 2 - 4) * ((8 * p ^ 4 + 384) * (19 / 40 : ℝ) - 64 * p ^ 2) /
          (p ^ 4 + 16) ^ 2 := by
  have hp : 0 < p := by linarith
  have hden1 : 0 < p ^ 3 * (p ^ 2 + 4) := by positivity
  have hden2 : 0 < (p ^ 4 + 16) ^ 2 := by positivity
  have hcoeff_s2 :
      12 * ((8 * p ^ 4 + 384) * (19 / 40 : ℝ) - 64 * p ^ 2) / (p ^ 4 + 16) ^ 2 - 3 ≤ 0 := by
    have hfac : 12 * ((8 * p ^ 4 + 384) * (19 / 40 : ℝ) - 64 * p ^ 2) / (p ^ 4 + 16) ^ 2 - 3 =
        -(3 * (5 * p ^ 8 + 84 * p ^ 4 + 1280 * p ^ 2 - 2368)) / (5 * (p ^ 4 + 16) ^ 2) := by
      have hne : (p ^ 4 + 16) ^ 2 ≠ 0 := ne_of_gt hden2
      field_simp; ring
    rw [hfac]
    have hp2 : 169 / 100 ≤ p ^ 2 := by nlinarith
    have hp4 : (169 / 100 : ℝ) ^ 2 ≤ p ^ 4 := by nlinarith
    have hp8 : 0 ≤ p ^ 8 := by positivity
    have hnum_pos : 0 ≤ 3 * (5 * p ^ 8 + 84 * p ^ 4 + 1280 * p ^ 2 - 2368) := by nlinarith
    have hden_pos : 0 < 5 * (p ^ 4 + 16) ^ 2 := by positivity
    rw [neg_div]
    linarith [div_nonneg hnum_pos (le_of_lt hden_pos)]
  have hstep_s2 :
      p + (9 * p ^ 4 + 8 * p ^ 2 + (32 - 20 * p ^ 2) * (19 / 40 : ℝ)) / (p ^ 3 * (p ^ 2 + 4)) +
        4 * (3 * (14143 / 10000 : ℝ) - 4) * ((8 * p ^ 4 + 384) * (19 / 40 : ℝ) - 64 * p ^ 2) /
          (p ^ 4 + 16) ^ 2 - 3 * (14143 / 10000 : ℝ) ≤
      p + (9 * p ^ 4 + 8 * p ^ 2 + (32 - 20 * p ^ 2) * (19 / 40 : ℝ)) / (p ^ 3 * (p ^ 2 + 4)) +
        4 * (3 * Real.sqrt 2 - 4) * ((8 * p ^ 4 + 384) * (19 / 40 : ℝ) - 64 * p ^ 2) /
          (p ^ 4 + 16) ^ 2 - 3 * Real.sqrt 2 := by
    have hdiff :
        (p + (9 * p ^ 4 + 8 * p ^ 2 + (32 - 20 * p ^ 2) * (19 / 40 : ℝ)) / (p ^ 3 * (p ^ 2 + 4)) +
          4 * (3 * Real.sqrt 2 - 4) * ((8 * p ^ 4 + 384) * (19 / 40 : ℝ) - 64 * p ^ 2) /
            (p ^ 4 + 16) ^ 2 - 3 * Real.sqrt 2) -
        (p + (9 * p ^ 4 + 8 * p ^ 2 + (32 - 20 * p ^ 2) * (19 / 40 : ℝ)) / (p ^ 3 * (p ^ 2 + 4)) +
          4 * (3 * (14143 / 10000 : ℝ) - 4) * ((8 * p ^ 4 + 384) * (19 / 40 : ℝ) - 64 * p ^ 2) /
            (p ^ 4 + 16) ^ 2 - 3 * (14143 / 10000 : ℝ)) =
        (Real.sqrt 2 - 14143 / 10000) *
          (12 * ((8 * p ^ 4 + 384) * (19 / 40 : ℝ) - 64 * p ^ 2) / (p ^ 4 + 16) ^ 2 - 3) := by ring
    have hs := sqrt2_lt
    have hprod : 0 ≤ (Real.sqrt 2 - 14143 / 10000) *
        (12 * ((8 * p ^ 4 + 384) * (19 / 40 : ℝ) - 64 * p ^ 2) / (p ^ 4 + 16) ^ 2 - 3) :=
      mul_nonneg_of_nonpos_of_nonpos (by linarith) hcoeff_s2
    linarith
  have hrat : 0 ≤
      p + (9 * p ^ 4 + 8 * p ^ 2 + (32 - 20 * p ^ 2) * (19 / 40 : ℝ)) / (p ^ 3 * (p ^ 2 + 4)) +
        4 * (3 * (14143 / 10000 : ℝ) - 4) * ((8 * p ^ 4 + 384) * (19 / 40 : ℝ) - 64 * p ^ 2) /
          (p ^ 4 + 16) ^ 2 - 3 * (14143 / 10000 : ℝ) := by
    have hbigden : 0 < 50000 * p ^ 3 * (p ^ 2 + 4) * (p ^ 4 + 16) ^ 2 := by positivity
    suffices hnum : 0 ≤ 50000 * p ^ 3 * (p ^ 2 + 4) * (p ^ 4 + 16) ^ 2 *
        (p + (9 * p ^ 4 + 8 * p ^ 2 + (32 - 20 * p ^ 2) * (19 / 40 : ℝ)) / (p ^ 3 * (p ^ 2 + 4)) +
          4 * (3 * (14143 / 10000 : ℝ) - 4) * ((8 * p ^ 4 + 384) * (19 / 40 : ℝ) - 64 * p ^ 2) /
            (p ^ 4 + 16) ^ 2 - 3 * (14143 / 10000 : ℝ)) by
      nlinarith
    have hclear : 50000 * p ^ 3 * (p ^ 2 + 4) * (p ^ 4 + 16) ^ 2 *
        (p + (9 * p ^ 4 + 8 * p ^ 2 + (32 - 20 * p ^ 2) * (19 / 40 : ℝ)) / (p ^ 3 * (p ^ 2 + 4)) +
          4 * (3 * (14143 / 10000 : ℝ) - 4) * ((8 * p ^ 4 + 384) * (19 / 40 : ℝ) - 64 * p ^ 2) /
            (p ^ 4 + 16) ^ 2 - 3 * (14143 / 10000 : ℝ)) = P7_poly p := by
      have hne1 : p ^ 3 * (p ^ 2 + 4) ≠ 0 := ne_of_gt hden1
      have hne2 : (p ^ 4 + 16) ^ 2 ≠ 0 := ne_of_gt hden2
      rw [← P7_clear_eq p]
      field_simp; ring
    rw [hclear]
    by_cases hp17 : p ≤ 17 / 10
    · exact P7_lo_nonneg p hp13 hp17
    · exact P7_hi_nonneg p (by linarith)
  linarith

private lemma main_pq (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (hpq : 4 * q ≤ p ^ 2) :
    3 * Real.sqrt 2 ≤
      p + 2 * Real.sqrt ((p ^ 2 - 2 * q + 2) / (2 * q ^ 2 + p ^ 2 - 2 * q)) +
        4 * (3 * Real.sqrt 2 - 4) / (p ^ 2 - 2 * q + (p ^ 2 - 2 * q) / q ^ 2) := by
  by_cases hq19 : q ≤ 19 / 40
  · have h1 := case1_pq p q hp hq hpq hq19
    have h4pos : 0 < 4 * (3 * Real.sqrt 2 - 4) := by have := three_sqrt2_sub_four_pos; linarith
    have hp2q : 0 < p ^ 2 - 2 * q := by nlinarith
    have hden : 0 < p ^ 2 - 2 * q + (p ^ 2 - 2 * q) / q ^ 2 := by positivity
    have hterm : 0 ≤ 4 * (3 * Real.sqrt 2 - 4) / (p ^ 2 - 2 * q + (p ^ 2 - 2 * q) / q ^ 2) :=
      div_nonneg (le_of_lt h4pos) (le_of_lt hden)
    linarith
  · push Not at hq19
    have h6 := ineq6_pq p q hp hpq (le_of_lt hq19)
    have h4 := term4_lb p q hp hq hpq
    have h4c : 0 < 4 * (3 * Real.sqrt 2 - 4) := by have := three_sqrt2_sub_four_pos; linarith
    have hterm4 :
        4 * (3 * Real.sqrt 2 - 4) * (((8 * p ^ 4 + 384) * q - 64 * p ^ 2) / (p ^ 4 + 16) ^ 2) ≤
        4 * (3 * Real.sqrt 2 - 4) / (p ^ 2 - 2 * q + (p ^ 2 - 2 * q) / q ^ 2) := by
      have hmul := mul_le_mul_of_nonneg_left h4 (le_of_lt h4c)
      rwa [mul_one_div] at hmul
    have hp13 : 13 / 10 ≤ p := by nlinarith
    have hlo := ineq7_at_19div40 p hp13
    have hhi := ineq7_at_p2div4 p hp
    let L : ℝ → ℝ := fun x =>
      p + (9 * p ^ 4 + 8 * p ^ 2 + (32 - 20 * p ^ 2) * x) / (p ^ 3 * (p ^ 2 + 4)) +
        4 * (3 * Real.sqrt 2 - 4) * ((8 * p ^ 4 + 384) * x - 64 * p ^ 2) / (p ^ 4 + 16) ^ 2
    have hlin : (p ^ 2 / 4 - 19 / 40) * L q =
        (p ^ 2 / 4 - q) * L (19 / 40) + (q - 19 / 40) * L (p ^ 2 / 4) := by
      simp only [L]; ring
    have hspan : 0 < p ^ 2 / 4 - 19 / 40 := by linarith
    have hLq : 3 * Real.sqrt 2 ≤ L q := by
      have h1 : (p ^ 2 / 4 - q) * (3 * Real.sqrt 2) ≤ (p ^ 2 / 4 - q) * L (19 / 40) :=
        mul_le_mul_of_nonneg_left hlo (by linarith)
      have h2 : (q - 19 / 40) * (3 * Real.sqrt 2) ≤ (q - 19 / 40) * L (p ^ 2 / 4) :=
        mul_le_mul_of_nonneg_left hhi (by linarith)
      nlinarith
    have hL_eq : L q =
        p + 2 * ((9 * p ^ 4 + 8 * p ^ 2 + (32 - 20 * p ^ 2) * q) / (2 * p ^ 3 * (p ^ 2 + 4))) +
          4 * (3 * Real.sqrt 2 - 4) * (((8 * p ^ 4 + 384) * q - 64 * p ^ 2) / (p ^ 4 + 16) ^ 2) := by
      have hne1 : p ^ 3 * (p ^ 2 + 4) ≠ 0 := by positivity
      have hne2 : (p ^ 4 + 16) ^ 2 ≠ 0 := by positivity
      simp only [L]; field_simp
    linarith

private lemma ordered_case (a b c d : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hab : b ≤ a) (hbc : c ≤ b) (hcd : d ≤ c)
    (hsum : 1 / (1 + a) + 1 / (1 + b) + 1 / (1 + c) + 1 / (1 + d) = 2) :
    3 * Real.sqrt 2 ≤
      1 / Real.sqrt a + 1 / Real.sqrt b + 1 / Real.sqrt c + 1 / Real.sqrt d +
        4 * (3 * Real.sqrt 2 - 4) / (a + b + c + d) := by
  have hac : 1 ≤ a * c := by
    have h1 : 1 / (1 + a) ≤ 1 / (1 + b) := one_div_le_one_div_of_le (by linarith) (by linarith)
    have h2 : 1 / (1 + c) ≤ 1 / (1 + d) := one_div_le_one_div_of_le (by linarith) (by linarith)
    have hle1 : 1 / (1 + a) + 1 / (1 + c) ≤ 1 := by linarith
    have hclear : (1 + a) * (1 + c) * (1 / (1 + a) + 1 / (1 + c)) = 2 + a + c := by
      have ha1 : (1 + a) ≠ 0 := by linarith
      have hc1 : (1 + c) ≠ 0 := by linarith
      field_simp; ring
    have hpos : 0 < (1 + a) * (1 + c) := by positivity
    nlinarith
  have hab1 : 1 ≤ a * b := by nlinarith
  have hd_eq : (2 * a * b * c + a * b + b * c + c * a - 1) * d = a + b + c + 2 - a * b * c := by
    have ha1 : (1 + a) ≠ 0 := by linarith
    have hb1 : (1 + b) ≠ 0 := by linarith
    have hc1 : (1 + c) ≠ 0 := by linarith
    have hd1 : (1 + d) ≠ 0 := by linarith
    have hclear := congrArg (fun x => x * ((1 + a) * (1 + b) * (1 + c) * (1 + d))) hsum
    field_simp at hclear
    linarith
  have hden_d : 0 < 2 * a * b * c + a * b + b * c + c * a - 1 := by nlinarith
  have hnum_d : 0 < a + b + c + 2 - a * b * c := by nlinarith
  -- Inequality (1): b + c <= 1/a + 1/d
  have hineq1 : b + c ≤ 1 / a + 1 / d := by
    have h1 : 0 ≤ (b + c + 2) * (a * c - 1) * (a * b - 1) := by
      have h0 : 0 ≤ b + c + 2 := by linarith
      have h1' : 0 ≤ a * c - 1 := by linarith
      have h2' : 0 ≤ a * b - 1 := by linarith
      positivity
    have hne_a : a ≠ 0 := ne_of_gt ha
    have hne_d : d ≠ 0 := ne_of_gt hd
    have hinv_d : (a + b + c + 2 - a * b * c) / d = 2 * a * b * c + a * b + b * c + c * a - 1 := by
      rw [div_eq_iff hne_d]
      linarith
    have hident : a * (a + b + c + 2 - a * b * c) * (1 / a + 1 / d - (b + c)) =
        (b + c + 2) * (a * c - 1) * (a * b - 1) := by
      calc a * (a + b + c + 2 - a * b * c) * (1 / a + 1 / d - (b + c))
          = (a + b + c + 2 - a * b * c) + a * ((a + b + c + 2 - a * b * c) / d) -
              a * (b + c) * (a + b + c + 2 - a * b * c) := by field_simp
        _ = (a + b + c + 2 - a * b * c) + a * (2 * a * b * c + a * b + b * c + c * a - 1) -
              a * (b + c) * (a + b + c + 2 - a * b * c) := by rw [hinv_d]
        _ = (b + c + 2) * (a * c - 1) * (a * b - 1) := by ring
    have hpos : 0 < a * (a + b + c + 2 - a * b * c) := by positivity
    nlinarith only [h1, hident, hpos]
  -- Relation (2ad + a + d) / (a + d + 2) = (b + c + 2) / (2bc + b + c)
  have hratio : (2 * a * d + a + d) / (a + d + 2) = (b + c + 2) / (2 * b * c + b + c) := by
    have ha1 : (1 + a) ≠ 0 := by linarith
    have hb1 : (1 + b) ≠ 0 := by linarith
    have hc1 : (1 + c) ≠ 0 := by linarith
    have hd1 : (1 + d) ≠ 0 := by linarith
    have had_pos : 0 < a + d + 2 := by linarith
    have hbc_pos : 0 < 2 * b * c + b + c := by positivity
    rw [div_eq_div_iff (ne_of_gt had_pos) (ne_of_gt hbc_pos)]
    have hclear := congrArg (fun x => x * ((1 + a) * (1 + b) * (1 + c) * (1 + d))) hsum
    field_simp at hclear
    linear_combination -2 * hclear
  -- Show b * c <= 4
  have hbc4 : b * c ≤ 4 := by
    have h1 : 1 / (1 + a) ≤ 1 / (1 + b) := one_div_le_one_div_of_le (by linarith) (by linarith)
    have h2 : 1 / (1 + d) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    have h2b : 1 / (1 + b) + 1 / (1 + b) = 2 / (1 + b) := by ring
    have hge1 : 1 ≤ 2 / (1 + b) + 1 / (1 + c) := by linarith
    have hclear : (1 + b) * (1 + c) * (2 / (1 + b) + 1 / (1 + c)) = 2 * (1 + c) + (1 + b) := by
      have hb1 : (1 + b) ≠ 0 := by linarith
      have hc1 : (1 + c) ≠ 0 := by linarith
      field_simp
    have hpos : 0 < (1 + b) * (1 + c) := by positivity
    have hbc_le : b * c ≤ 2 + c := by nlinarith only [hge1, hclear, hpos]
    have hc2 : c ≤ 2 := by nlinarith only [hbc_le, hbc, hc]
    linarith
  -- Inequality (2): 2 * sqrt((2ad + a + d) / (a + d + 2)) <= 1/sqrt b + 1/sqrt c
  have hineq2 : 2 * Real.sqrt ((2 * a * d + a + d) / (a + d + 2)) ≤
      1 / Real.sqrt b + 1 / Real.sqrt c := by
    rw [hratio]
    set xb : ℝ := Real.sqrt b
    set xc : ℝ := Real.sqrt c
    have hxb : 0 < xb := Real.sqrt_pos.mpr hb
    have hxc : 0 < xc := Real.sqrt_pos.mpr hc
    have hxb2 : xb ^ 2 = b := Real.sq_sqrt (le_of_lt hb)
    have hxc2 : xc ^ 2 = c := Real.sq_sqrt (le_of_lt hc)
    have hxy2 : xb * xc ≤ 2 := by
      have hsq : (xb * xc) ^ 2 = b * c := by rw [mul_pow, hxb2, hxc2]
      nlinarith only [hsq, hbc4, hxb, hxc]
    have hden : 0 < 2 * b * c + b + c := by positivity
    have hnum : 0 < b + c + 2 := by linarith
    have hsq_le : 4 * ((b + c + 2) / (2 * b * c + b + c)) ≤ (1 / xb + 1 / xc) ^ 2 := by
      have hdiff : (1 / xb + 1 / xc) ^ 2 - 4 * ((b + c + 2) / (2 * b * c + b + c)) =
          (xb - xc) ^ 2 * (xb ^ 2 + xc ^ 2 + 2 * xb * xc * (2 - xb * xc)) /
            (xb ^ 2 * xc ^ 2 * (2 * b * c + b + c)) := by
        have hne1 : xb ≠ 0 := ne_of_gt hxb
        have hne2 : xc ≠ 0 := ne_of_gt hxc
        have hne3 : 2 * b * c + b + c ≠ 0 := ne_of_gt hden
        rw [← hxb2, ← hxc2]
        field_simp; ring
      have hnonneg : 0 ≤ (xb - xc) ^ 2 * (xb ^ 2 + xc ^ 2 + 2 * xb * xc * (2 - xb * xc)) /
          (xb ^ 2 * xc ^ 2 * (2 * b * c + b + c)) := by
        have h1 : 0 ≤ 2 - xb * xc := by linarith
        positivity
      linarith
    have hL : 0 ≤ 2 * Real.sqrt ((b + c + 2) / (2 * b * c + b + c)) := by positivity
    have hR : 0 ≤ 1 / xb + 1 / xc := by positivity
    have hsq2 : (2 * Real.sqrt ((b + c + 2) / (2 * b * c + b + c))) ^ 2 ≤ (1 / xb + 1 / xc) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (div_nonneg (le_of_lt hnum) (le_of_lt hden))]
      linarith
    nlinarith only [hL, hR, hsq2]
  -- Substitute p = 1/sqrt a + 1/sqrt d, q = 1/sqrt(a*d) = (1/sqrt a)*(1/sqrt d)
  set xa : ℝ := 1 / Real.sqrt a
  set xd : ℝ := 1 / Real.sqrt d
  set p : ℝ := xa + xd
  set q : ℝ := xa * xd
  have hxa : 0 < xa := by positivity
  have hxd : 0 < xd := by positivity
  have hp : 0 < p := by positivity
  have hq : 0 < q := by positivity
  have hpq : 4 * q ≤ p ^ 2 := by
    have : p ^ 2 - 4 * q = (xa - xd) ^ 2 := by simp only [p, q]; ring
    nlinarith [sq_nonneg (xa - xd)]
  have hxa2 : a = 1 / xa ^ 2 := by
    simp only [xa, one_div, inv_pow, inv_inv, Real.sq_sqrt (le_of_lt ha)]
  have hxd2 : d = 1 / xd ^ 2 := by
    simp only [xd, one_div, inv_pow, inv_inv, Real.sq_sqrt (le_of_lt hd)]
  have hrad : (2 * a * d + a + d) / (a + d + 2) =
      (p ^ 2 - 2 * q + 2) / (2 * q ^ 2 + p ^ 2 - 2 * q) := by
    have hne_a : xa ≠ 0 := ne_of_gt hxa
    have hne_d : xd ≠ 0 := ne_of_gt hxd
    have hne1 : a + d + 2 ≠ 0 := by linarith
    have hne2 : 2 * q ^ 2 + p ^ 2 - 2 * q ≠ 0 := by nlinarith
    rw [hxa2, hxd2] at hne1 ⊢
    simp only [p, q] at hne2 ⊢
    field_simp at hne1 hne2 ⊢
    ring
  have hden_eq : a + d + 1 / a + 1 / d = p ^ 2 - 2 * q + (p ^ 2 - 2 * q) / q ^ 2 := by
    have hne_a : xa ≠ 0 := ne_of_gt hxa
    have hne_d : xd ≠ 0 := ne_of_gt hxd
    rw [hxa2, hxd2]
    simp only [p, q]
    field_simp; ring
  have h4pos : 0 < 4 * (3 * Real.sqrt 2 - 4) := by have := three_sqrt2_sub_four_pos; linarith
  have hterm4 : 4 * (3 * Real.sqrt 2 - 4) / (a + d + 1 / a + 1 / d) ≤
      4 * (3 * Real.sqrt 2 - 4) / (a + b + c + d) := by
    exact div_le_div_of_nonneg_left (le_of_lt h4pos) (by linarith) (by linarith)
  have hmain := main_pq p q hp hq hpq
  rw [← hrad, ← hden_eq] at hmain
  linarith

-- 4-variable sorting helper
private lemma sort4 {P : ℝ → ℝ → ℝ → ℝ → Prop}
    (h12 : ∀ a b c d, P a b c d → P b a c d)
    (h23 : ∀ a b c d, P a b c d → P a c b d)
    (h34 : ∀ a b c d, P a b c d → P a b d c)
    (hord : ∀ a b c d, b ≤ a → c ≤ b → d ≤ c → P a b c d) :
    ∀ a b c d, P a b c d := by
  have step12 : ∀ a b c d, (b ≤ a → P a b c d) → (a ≤ b → P b a c d) → P a b c d := by
    intro a b c d h1 h2
    rcases le_total b a with h | h
    · exact h1 h
    · exact h12 b a c d (h2 h)
  have step34 : ∀ a b c d, (d ≤ c → P a b c d) → (c ≤ d → P a b d c) → P a b c d := by
    intro a b c d h1 h2
    rcases le_total d c with h | h
    · exact h1 h
    · exact h34 a b d c (h2 h)
  have step23 : ∀ a b c d, (c ≤ b → P a b c d) → (b ≤ c → P a c b d) → P a b c d := by
    intro a b c d h1 h2
    rcases le_total c b with h | h
    · exact h1 h
    · exact h23 a c b d (h2 h)
  have h13 : ∀ a b c d, P a b c d → P c b a d := fun a b c d h =>
    h12 b c a d (h23 b a c d (h12 a b c d h))
  have h24 : ∀ a b c d, P a b c d → P a d c b := fun a b c d h =>
    h23 a c d b (h34 a c b d (h23 a b c d h))
  -- Standard 5-comparator sorting network: (1,2), (3,4), (1,3), (2,4), (2,3)
  intro a b c d
  -- First enforce b <= a and d <= c
  suffices hpair : ∀ a b c d, b ≤ a → d ≤ c → P a b c d by
    refine step12 a b c d (fun hab => ?_) (fun hba => ?_)
    · exact step34 a b c d (hpair a b c d hab) (hpair a b d c hab)
    · exact step34 b a c d (hpair b a c d hba) (hpair b a d c hba)
  -- Next enforce c <= a (by swapping (a,c) if a < c, wait: preserve b<=a and d<=c by swapping (a,b) with (c,d)!)
  intro a b c d hab hdc
  suffices hmax : ∀ a b c d, b ≤ a → c ≤ a → d ≤ a → P a b c d by
    rcases le_total c a with hca | hac
    · exact hmax a b c d hab hca (le_trans hdc hca)
    · exact h24 a d c b (h13 c d a b (hmax c d a b hdc hac (le_trans hab hac)))
  -- Now a is the maximum! Sort (b, c, d) in 3 steps!
  intro a b c d hba hca hda
  suffices hbc_ord : ∀ a b c d, b ≤ a → c ≤ a → d ≤ a → c ≤ b → P a b c d by
    exact step23 a b c d (hbc_ord a b c d hba hca hda) (hbc_ord a c b d hca hba hda)
  intro a b c d hba hca hda hcb
  rcases le_total d c with hdc | hcd
  · exact hord a b c d hba hcb hdc
  · rcases le_total d b with hdb | hbd
    · exact h34 a b d c (hord a b d c hba hdb hcd)
    · exact h34 a b d c (h23 a d b c (hord a d b c hda hbd hcb))

private theorem main_proof : type_of% @OMA.S_mse_4398439.main := by
  let P : ℝ → ℝ → ℝ → ℝ → Prop := fun a b c d =>
    0 < a → 0 < b → 0 < c → 0 < d →
      1 / (1 + a) + 1 / (1 + b) + 1 / (1 + c) + 1 / (1 + d) = 2 →
      1 / Real.sqrt a + 1 / Real.sqrt b + 1 / Real.sqrt c + 1 / Real.sqrt d +
        4 * (3 * Real.sqrt 2 - 4) / (a + b + c + d) ≥ 3 * Real.sqrt 2
  change ∀ a b c d, P a b c d
  apply sort4
  · intro a b c d h ha hb hc hd hs
    have h' := h hb ha hc hd (by linarith)
    have heq : 1 / Real.sqrt b + 1 / Real.sqrt a + 1 / Real.sqrt c + 1 / Real.sqrt d +
        4 * (3 * Real.sqrt 2 - 4) / (b + a + c + d) =
        1 / Real.sqrt a + 1 / Real.sqrt b + 1 / Real.sqrt c + 1 / Real.sqrt d +
        4 * (3 * Real.sqrt 2 - 4) / (a + b + c + d) := by ring
    linarith
  · intro a b c d h ha hb hc hd hs
    have h' := h ha hc hb hd (by linarith)
    have heq : 1 / Real.sqrt a + 1 / Real.sqrt c + 1 / Real.sqrt b + 1 / Real.sqrt d +
        4 * (3 * Real.sqrt 2 - 4) / (a + c + b + d) =
        1 / Real.sqrt a + 1 / Real.sqrt b + 1 / Real.sqrt c + 1 / Real.sqrt d +
        4 * (3 * Real.sqrt 2 - 4) / (a + b + c + d) := by ring
    linarith
  · intro a b c d h ha hb hc hd hs
    have h' := h ha hb hd hc (by linarith)
    have heq : 1 / Real.sqrt a + 1 / Real.sqrt b + 1 / Real.sqrt d + 1 / Real.sqrt c +
        4 * (3 * Real.sqrt 2 - 4) / (a + b + d + c) =
        1 / Real.sqrt a + 1 / Real.sqrt b + 1 / Real.sqrt c + 1 / Real.sqrt d +
        4 * (3 * Real.sqrt 2 - 4) / (a + b + c + d) := by ring
    linarith
  · intro a b c d hab hbc hcd ha hb hc hd hs
    exact ordered_case a b c d ha hb hc hd hab hbc hcd hs

end OMA.P_mse_4398439

theorem OMA.solution : type_of% @OMA.S_mse_4398439.main :=
  OMA.P_mse_4398439.main_proof
