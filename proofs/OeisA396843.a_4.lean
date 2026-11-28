import FormalConjectures.OEIS.«396843»

/-! Retain an integral witness for the epsilon-defined series, then compare the
low coefficients of its defining equation with explicit normalized truncations. -/

namespace A396843Proof
open PowerSeries
noncomputable section
variable {R : Type*} [CommRing R]

/-- The inner argument in Hanna's functional equation. -/
def argument (f : PowerSeries R) : PowerSeries R := X * f - 3 * X * f ^ 2

/-- The left side of Hanna's functional equation. -/
def output (f : PowerSeries R) : PowerSeries R := f.subst (argument f)

lemma argument_constant (f : PowerSeries R) : constantCoeff (argument f) = 0 := by
  simp [argument]

lemma argument_hasSubst (f : PowerSeries R) : HasSubst (argument f) :=
  .of_constantCoeff_zero' (argument_constant f)

lemma argument_dvd {f : PowerSeries R} (h : constantCoeff f = 0) :
    (X : PowerSeries R) ^ 2 ∣ argument f := by
  obtain ⟨q, rfl⟩ := X_dvd_iff.mpr h
  refine ⟨q - 3 * X * q ^ 2, ?_⟩
  dsimp [argument]
  ring

lemma coeff_eq_of_dvd {f g : PowerSeries R} {d n : ℕ}
    (h : (X : PowerSeries R) ^ d ∣ f - g) (hn : n < d) : coeff n f = coeff n g := by
  have := X_pow_dvd_iff.mp h n hn
  simpa only [map_sub, sub_eq_zero] using this

lemma pow_difference_dvd {u v : PowerSeries R} {e k : ℕ}
    (hu : (X : PowerSeries R) ^ 2 ∣ u) (hv : (X : PowerSeries R) ^ 2 ∣ v)
    (he : (X : PowerSeries R) ^ e ∣ u - v) (hk : 2 ≤ k) :
    (X : PowerSeries R) ^ (e + 2) ∣ u ^ k - v ^ k := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hk
  clear hk
  induction k with
  | zero =>
      have h := mul_dvd_mul he (dvd_add hu hv)
      rw [← pow_add] at h
      convert h using 1
      all_goals ring
  | succ k ih =>
      have hvk : X ^ 2 ∣ v ^ (k + 2) := hv.trans (dvd_pow_self v (by omega))
      have hsecond : X ^ (e + 2) ∣ (u - v) * v ^ (k + 2) := by
        simpa only [pow_add] using mul_dvd_mul he hvk
      have h := dvd_add (dvd_mul_of_dvd_right ih u) hsecond
      convert h using 1
      all_goals ring

lemma subst_outer_dvd {f g u : PowerSeries R} {d : ℕ}
    (hu : constantCoeff u = 0) (hu2 : (X : PowerSeries R) ^ 2 ∣ u)
    (h : (X : PowerSeries R) ^ d ∣ f - g) :
    (X : PowerSeries R) ^ (2 * d) ∣ f.subst u - g.subst u := by
  have hs : HasSubst u := .of_constantCoeff_zero' hu
  obtain ⟨q, hq⟩ := h
  have he := congrArg (fun p : PowerSeries R => p.subst u) hq
  rw [subst_sub hs, subst_mul hs, subst_pow hs, subst_X hs] at he
  rw [he]
  have hp : X ^ (2 * d) ∣ u ^ d := by
    simpa only [pow_mul] using pow_dvd_pow_of_dvd hu2 d
  exact hp.mul_right _

lemma subst_tail_dvd {f u v : PowerSeries R} {e : ℕ}
    (hf : coeff 1 f = 1) (hu : constantCoeff u = 0) (hv : constantCoeff v = 0)
    (hu2 : (X : PowerSeries R) ^ 2 ∣ u) (hv2 : (X : PowerSeries R) ^ 2 ∣ v)
    (he : (X : PowerSeries R) ^ e ∣ u - v) :
    (X : PowerSeries R) ^ (e + 2) ∣ f.subst u - f.subst v - (u - v) := by
  have hsu : HasSubst u := .of_constantCoeff_zero' hu
  have hsv : HasSubst v := .of_constantCoeff_zero' hv
  apply X_pow_dvd_iff.mpr
  intro n hn
  have h : coeff n ((f - X).subst u) = coeff n ((f - X).subst v) := by
    rw [coeff_subst' hsu, coeff_subst' hsv]
    apply finsum_congr
    intro k
    rcases k with _ | k
    · simp
    rcases k with _ | k
    · simp [hf]
    · rw [coeff_eq_of_dvd (pow_difference_dvd hu2 hv2 he (by omega : 2 ≤ k + 2)) hn]
  rw [subst_sub hsu, subst_sub hsv, subst_X hsu, subst_X hsv] at h
  simp only [map_sub] at h ⊢
  linear_combination h

/-- Changing a normalized input in degree $d$ changes its output in degree $d+1$
by the same amount, with error divisible by $X^{d+2}$. -/
lemma output_linearization {f g : PowerSeries R} {d : ℕ} (hd : 2 ≤ d)
    (hf : constantCoeff f = 0) (hg : constantCoeff g = 0) (hf1 : coeff 1 f = 1)
    (h : (X : PowerSeries R) ^ d ∣ f - g) :
    (X : PowerSeries R) ^ (d + 2) ∣ output f - output g - X * (f - g) := by
  have ha : X ^ (d + 1) ∣ argument f - argument g := by
    have ht := mul_dvd_mul (dvd_refl (X : PowerSeries R)) h
    rw [← pow_succ'] at ht
    convert ht.mul_right (1 - 3 * (f + g)) using 1
    all_goals (dsimp [argument]; ring)
  have hb : X ^ (d + 2) ∣ argument f - argument g - X * (f - g) := by
    have hz : X ∣ f + g := X_dvd_iff.mpr (by simp [hf, hg])
    have ht' := mul_dvd_mul (mul_dvd_mul (dvd_refl (X : PowerSeries R)) h) hz
    rw [show X * X ^ d * X = (X : PowerSeries R) ^ (d + 2) by ring] at ht'
    convert ht'.mul_left (-3) using 1
    all_goals (dsimp [argument]; ring)
  have ho := subst_outer_dvd (argument_constant g) (argument_dvd hg) h
  have ho' : X ^ (d + 2) ∣ f.subst (argument g) - g.subst (argument g) :=
    (pow_dvd_pow X (by omega : d + 2 ≤ 2 * d)).trans ho
  have hi := subst_tail_dvd hf1 (argument_constant f) (argument_constant g)
    (argument_dvd hf) (argument_dvd hg) ha
  have hi' : X ^ (d + 2) ∣
      f.subst (argument f) - f.subst (argument g) - (argument f - argument g) :=
    (pow_dvd_pow X (by omega : d + 2 ≤ d + 1 + 2)).trans hi
  convert dvd_add (dvd_add hi' ho') hb using 1
  all_goals (dsimp [output]; ring)

lemma normalized_difference {f g : PowerSeries R}
    (h0 : constantCoeff f = constantCoeff g) (h1 : coeff 1 f = coeff 1 g) :
    (X : PowerSeries R) ^ 2 ∣ f - g := by
  apply X_pow_dvd_iff.mpr
  intro n hn
  interval_cases n <;> simp_all [coeff_zero_eq_constantCoeff]

lemma output_congr {f g : PowerSeries R} {d : ℕ} (hd : 2 ≤ d)
    (hf : constantCoeff f = 0) (hg : constantCoeff g = 0) (hf1 : coeff 1 f = 1)
    (h : (X : PowerSeries R) ^ d ∣ f - g) :
    (X : PowerSeries R) ^ (d + 1) ∣ output f - output g := by
  have ht := output_linearization hd hf hg hf1 h
  have hs : X ^ (d + 1) ∣ X * (f - g) := by
    simpa only [pow_succ'] using mul_dvd_mul (dvd_refl (X : PowerSeries R)) h
  have ht' := (pow_dvd_pow X (by omega : d + 1 ≤ d + 2)).trans ht
  convert dvd_add ht' hs using 1
  all_goals ring

lemma output_next {f g : PowerSeries R} {d : ℕ} (hd : 2 ≤ d)
    (hf : constantCoeff f = 0) (hg : constantCoeff g = 0) (hf1 : coeff 1 f = 1)
    (h : (X : PowerSeries R) ^ d ∣ f - g) :
    coeff (d + 1) (output f) - coeff (d + 1) (output g) = coeff d f - coeff d g := by
  have ht := X_pow_dvd_iff.mp (output_linearization hd hf hg hf1 h) (d + 1) (by omega)
  simpa only [map_sub, coeff_succ_X_mul, sub_eq_zero] using ht

/-- The division-free correction sequence, beginning with $X$. -/
def stage : ℕ → PowerSeries R
  | 0 => X
  | n + 1 => stage n - monomial (n + 2) (coeff (n + 3) (output (stage n)))

@[simp] lemma stage_constant (n : ℕ) : constantCoeff (stage n : PowerSeries R) = 0 := by
  induction n with
  | zero => simp [stage]
  | succ n ih =>
      rw [stage, map_sub, ih, zero_sub, neg_eq_zero]
      rw [← coeff_zero_eq_constantCoeff_apply, coeff_monomial]
      simp

@[simp] lemma stage_linear (n : ℕ) : coeff 1 (stage n : PowerSeries R) = 1 := by
  induction n with
  | zero => simp [stage]
  | succ n ih => simp [stage, coeff_monomial, ih]

lemma stage_change (n : ℕ) :
    (X : PowerSeries R) ^ (n + 2) ∣ stage (n + 1) - stage n := by
  refine ⟨- C (coeff (n + 3) (output (stage n))), ?_⟩
  rw [stage, monomial_eq_C_mul_X_pow]
  ring

lemma stage_correct (n : ℕ) :
    (X : PowerSeries R) ^ (n + 3) ∣ output (stage n) - X ^ 2 := by
  induction n with
  | zero =>
      refine ⟨-3, ?_⟩
      change X.subst (argument X) - X ^ 2 = X ^ 3 * (-3 : PowerSeries R)
      rw [subst_X (argument_hasSubst _)]
      dsimp [argument]
      ring
  | succ n ih =>
      have hd := stage_change (R := R) n
      have hl := output_linearization (by omega : 2 ≤ n + 2)
        (stage_constant (n + 1)) (stage_constant n) (stage_linear (n + 1)) hd
      apply X_pow_dvd_iff.mpr
      intro j hj
      have he := X_pow_dvd_iff.mp hl j (by omega)
      simp only [map_sub] at he
      have hc : coeff j (X * (stage (n + 1) - stage n) : PowerSeries R) =
          if j = n + 3 then -coeff (n + 3) (output (stage n) : PowerSeries R) else 0 := by
        cases j with
        | zero => simp
        | succ j =>
            rw [coeff_succ_X_mul]
            simp only [stage, sub_sub_cancel_left, map_neg, coeff_monomial]
            split_ifs <;> simp_all
      rw [hc] at he
      by_cases hj' : j < n + 3
      · rw [if_neg (by omega)] at he
        have hi := X_pow_dvd_iff.mp ih j hj'
        simp only [map_sub] at hi ⊢
        linear_combination he + hi
      · have hje : j = n + 3 := by omega
        subst j
        rw [if_pos rfl] at he
        simp only [map_sub, coeff_X_pow, show ¬ n + 3 = 2 by omega, ite_false]
        linear_combination he

lemma stage_stable {m n k : ℕ} (hmn : m ≤ n) (hk : k < m + 2) :
    coeff k (stage n : PowerSeries R) = coeff k (stage m : PowerSeries R) := by
  induction n, hmn using Nat.le_induction with
  | base => rfl
  | succ n hmn ih =>
      exact (coeff_eq_of_dvd (stage_change n) (by omega)).trans ih

/-- The integral series obtained by stabilizing each coefficient. -/
def series : PowerSeries R := mk fun n => coeff n (stage n)

lemma series_approximation (n : ℕ) :
    (X : PowerSeries R) ^ (n + 2) ∣ series - stage n := by
  apply X_pow_dvd_iff.mpr
  intro k hk
  simp only [map_sub, coeff_mk, series, sub_eq_zero]
  exact (stage_stable (m := k) (n := max n k) (by omega) (by omega)).symm.trans
    (stage_stable (m := n) (n := max n k) (by omega) hk)

@[simp] lemma series_constant : constantCoeff (series : PowerSeries R) = 0 := by
  simpa using coeff_eq_of_dvd (series_approximation (R := R) 0) (by omega : 0 < 0 + 2)

@[simp] lemma series_linear : coeff 1 (series : PowerSeries R) = 1 := by
  simpa using coeff_eq_of_dvd (series_approximation (R := R) 0) (by omega : 1 < 0 + 2)

/-- Existence of an integral solution of the OEIS generating-function equation. -/
theorem series_equation : output (series : PowerSeries R) = X ^ 2 := by
  ext n
  have h := output_congr (R := R) (by omega : 2 ≤ n + 2) series_constant (stage_constant n)
    series_linear (series_approximation n)
  exact (coeff_eq_of_dvd h (by omega)).trans
    (coeff_eq_of_dvd (stage_correct n) (by omega))

end
end A396843Proof

open PowerSeries A396843Proof in
theorem OMA.solution : type_of% @OeisA396843.a_4 := by
  have hs : OeisA396843.SourceEquation OeisA396843.series :=
    Classical.epsilon_spec (show ∃ A, OeisA396843.SourceEquation A from
      ⟨series, series_constant, series_linear, series_equation⟩)
  have he : output OeisA396843.series = X ^ 2 := hs.2.2
  have h2 : coeff 2 OeisA396843.series = 3 := by
    have hx : output (X : PowerSeries ℤ) = X ^ 2 - 3 * X ^ 3 := by
      rw [output, subst_X (argument_hasSubst _)]
      dsimp [argument]
      ring
    have h := output_next (d := 2) (by decide) hs.1
      (by simp : constantCoeff (X : PowerSeries ℤ) = 0) hs.2.1
      (normalized_difference (by simpa using hs.1) (by simpa using hs.2.1))
    rw [he, hx] at h
    norm_num at h
    simpa [coeff_X, coeff_mul_X_pow', map_ofNat] using h.symm
  have h3 : coeff 3 OeisA396843.series = 15 := by
    let P : PowerSeries ℤ := X + C 3 * X ^ 2
    have hd : (X : PowerSeries ℤ) ^ 3 ∣ OeisA396843.series - P := by
      apply X_pow_dvd_iff.2
      intro n hn
      interval_cases n <;>
        simp only [P, map_sub, map_add, coeff_X, coeff_C_mul_X_pow,
          coeff_zero_eq_constantCoeff_apply, hs.1, hs.2.1, h2] <;> norm_num
    have hpout : output P = argument P + C 3 * argument P ^ 2 := by
      change (X + C (3 : ℤ) * X ^ 2).subst (argument P) = _
      rw [subst_add (argument_hasSubst _), subst_mul (argument_hasSubst _),
        subst_pow (argument_hasSubst _), subst_X (argument_hasSubst _), subst_C]
      rfl
    have hp : coeff 4 (output P) = -15 := by
      rw [hpout]
      conv_lhs => arg 2; simp only [P, argument, map_ofNat]; ring_nf
      norm_num [coeff_mul_X_pow', coeff_X_pow_mul', coeff_X, map_ofNat]
    have h := output_next (d := 3) (by decide) hs.1
      (by simp [P] : constantCoeff P = 0) hs.2.1 hd
    rw [he, hp] at h
    simp only [P, map_add, coeff_X, coeff_X_pow, coeff_C_mul_X_pow] at h
    norm_num at h
    simpa using h.symm
  let P : PowerSeries ℤ := X + C 3 * X ^ 2 + C 15 * X ^ 3
  have hd : (X : PowerSeries ℤ) ^ 4 ∣ OeisA396843.series - P := by
    apply X_pow_dvd_iff.2
    intro n hn
    interval_cases n <;>
      simp only [P, map_sub, map_add, coeff_X, coeff_C_mul_X_pow,
        coeff_zero_eq_constantCoeff_apply, hs.1, hs.2.1, h2, h3] <;> norm_num
  have hpout : output P = argument P + C 3 * argument P ^ 2 + C 15 * argument P ^ 3 := by
    change (X + C (3 : ℤ) * X ^ 2 + C 15 * X ^ 3).subst (argument P) = _
    simp only [subst_add (argument_hasSubst _), subst_mul (argument_hasSubst _),
      subst_pow (argument_hasSubst _), subst_X (argument_hasSubst _), subst_C]
    rfl
  have hp : coeff 5 (output P) = -117 := by
    rw [hpout]
    conv_lhs => arg 2; simp only [P, argument, map_ofNat]; ring_nf
    norm_num [coeff_mul_X_pow', coeff_X_pow_mul', coeff_X, map_ofNat]
  have h := output_next (d := 4) (by decide) hs.1
    (by simp [P] : constantCoeff P = 0) hs.2.1 hd
  rw [he, hp] at h
  simp only [P, map_add, coeff_X, coeff_X_pow, coeff_C_mul_X_pow] at h
  norm_num at h
  simpa [OeisA396843.a] using h.symm
