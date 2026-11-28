import OMAStatements.S_oeis_a166168
import Mathlib

namespace OMA.S_oeis_a166168

open PowerSeries BigOperators

private def expLogCoeffs (C : ℕ → ℤ) : ℕ → ℚ
  | 0 => 1
  | n + 1 =>
      (∑ k : Fin (n + 1), (C (k.val + 1) : ℚ) * expLogCoeffs C (n - k.val)) / ((n + 1 : ℕ) : ℚ)
termination_by n => n
decreasing_by
  have := k.isLt
  omega

private noncomputable def expLogSeries (C : ℕ → ℤ) : PowerSeries ℚ :=
  PowerSeries.mk (expLogCoeffs C)

private def isIntegerSeries (F : PowerSeries ℚ) : Prop :=
  ∀ n : ℕ, ∃ z : ℤ, PowerSeries.coeff n F = (z : ℚ)

/-- Differential equation characterizing `expLogSeries C`:
`X * (expLogSeries C)' = (expLogSeries C) * (∑_{n ≥ 1} C(n) * X^n)`. -/
private lemma expLogSeries_ode (C : ℕ → ℤ) :
    PowerSeries.X * PowerSeries.derivative ℚ (expLogSeries C) =
      expLogSeries C * PowerSeries.mk fun n => if n = 0 then 0 else (C n : ℚ) := by
  apply PowerSeries.ext; intro n
  cases n with
  | zero =>
      rw [PowerSeries.coeff_zero_X_mul, PowerSeries.coeff_zero_eq_constantCoeff, map_mul,
          ← PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.coeff_mk]
      simp
  | succ n =>
      rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative, expLogSeries,
          PowerSeries.coeff_mk, PowerSeries.coeff_mul,
          Finset.Nat.sum_antidiagonal_eq_sum_range_succ
            (fun i j => PowerSeries.coeff i (PowerSeries.mk (expLogCoeffs C)) *
              PowerSeries.coeff j (PowerSeries.mk fun m => if m = 0 then 0 else (C m : ℚ)))]
      rw [expLogCoeffs]
      have hpos : ((n : ℚ) + 1) ≠ 0 := by positivity
      push_cast
      rw [div_mul_cancel₀ _ hpos]
      rw [Finset.sum_range_succ, PowerSeries.coeff_mk, PowerSeries.coeff_mk, Nat.sub_self]
      simp only [↓reduceIte, mul_zero, add_zero]
      -- Reverse the sum `i ↦ n - i`!
      rw [Fin.sum_univ_eq_sum_range (fun k => (C (k + 1) : ℚ) * expLogCoeffs C (n - k)) (n + 1)]
      rw [← Finset.sum_range_reflect (fun k => (C (k + 1) : ℚ) * expLogCoeffs C (n - k)) (n + 1)]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hilt : i < n + 1 := Finset.mem_range.mp hi
      rw [PowerSeries.coeff_mk, PowerSeries.coeff_mk]
      have hne : n + 1 - i ≠ 0 := by omega
      have h1 : n + 1 - 1 - i + 1 = n + 1 - i := by omega
      have h2 : n - (n + 1 - 1 - i) = i := by omega
      simp only [hne, ↓reduceIte, h1, h2]
      ring

/-- Uniqueness of `expLogSeries C`: any `F` with `F(0) = 1` and `X * F' = F * (∑_{n ≥ 1} C(n) X^n)`
equals `expLogSeries C`. -/
private lemma eq_expLogSeries_of_ode (C : ℕ → ℤ) (F : PowerSeries ℚ)
    (h0 : PowerSeries.coeff 0 F = 1)
    (hode : PowerSeries.X * PowerSeries.derivative ℚ F =
      F * PowerSeries.mk fun n => if n = 0 then 0 else (C n : ℚ)) :
    F = expLogSeries C := by
  apply PowerSeries.ext; intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero =>
        rw [h0, expLogSeries, PowerSeries.coeff_mk, expLogCoeffs]
    | succ n =>
        have hF := congr_arg (PowerSeries.coeff (n + 1)) hode
        have hE := congr_arg (PowerSeries.coeff (n + 1)) (expLogSeries_ode C)
        rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative, PowerSeries.coeff_mul,
            Finset.Nat.sum_antidiagonal_eq_sum_range_succ
              (fun i j => PowerSeries.coeff i F *
                PowerSeries.coeff j (PowerSeries.mk fun m => if m = 0 then 0 else (C m : ℚ)))] at hF
        rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative, PowerSeries.coeff_mul,
            Finset.Nat.sum_antidiagonal_eq_sum_range_succ
              (fun i j => PowerSeries.coeff i (expLogSeries C) *
                PowerSeries.coeff j (PowerSeries.mk fun m => if m = 0 then 0 else (C m : ℚ)))] at hE
        rw [Finset.sum_range_succ, PowerSeries.coeff_mk, Nat.sub_self, if_pos rfl, mul_zero, add_zero] at hF hE
        have hsum_eq :
            ∑ k ∈ Finset.range (n + 1),
              PowerSeries.coeff k F * PowerSeries.coeff (n + 1 - k)
                (PowerSeries.mk fun m => if m = 0 then 0 else (C m : ℚ)) =
            ∑ k ∈ Finset.range (n + 1),
              PowerSeries.coeff k (expLogSeries C) * PowerSeries.coeff (n + 1 - k)
                (PowerSeries.mk fun m => if m = 0 then 0 else (C m : ℚ)) := by
          refine Finset.sum_congr rfl fun k hk => ?_
          rw [ih k (Finset.mem_range.mp hk)]
        rw [hsum_eq, ← hE] at hF
        have hpos : ((n : ℚ) + 1) ≠ 0 := by positivity
        exact mul_right_cancel₀ hpos hF

/-- Integer-coefficient power series `(1 - X^d)^(-m)` for `d ≥ 1` and `m : ℤ`. -/
private noncomputable def eulerFactor (d : ℕ) (m : ℤ) : PowerSeries ℚ :=
  if 0 ≤ m then
    ((PowerSeries.mk fun n => if d ∣ n then (1 : ℚ) else 0) ^ m.toNat)
  else
    ((1 - PowerSeries.X ^ d) ^ (-m).toNat)

private lemma isIntegerSeries_mul {f g : PowerSeries ℚ}
    (hf : isIntegerSeries f) (hg : isIntegerSeries g) : isIntegerSeries (f * g) := by
  intro n
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => PowerSeries.coeff i f * PowerSeries.coeff j g)]
  choose zf hzf using hf
  choose zg hzg using hg
  refine ⟨∑ k ∈ Finset.range (n + 1), zf k * zg (n - k), ?_⟩
  rw [Int.cast_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hzf k, hzg (n - k), Int.cast_mul]

private lemma isIntegerSeries_one : isIntegerSeries (1 : PowerSeries ℚ) := by
  intro n
  rw [PowerSeries.coeff_one]
  split_ifs
  · exact ⟨1, by simp⟩
  · exact ⟨0, by simp⟩

private lemma isIntegerSeries_pow {f : PowerSeries ℚ} (hf : isIntegerSeries f) :
    ∀ k : ℕ, isIntegerSeries (f ^ k)
  | 0 => by simpa using isIntegerSeries_one
  | k + 1 => by rw [pow_succ]; exact isIntegerSeries_mul (isIntegerSeries_pow hf k) hf

private lemma isIntegerSeries_prod {ι : Type*} (s : Finset ι) (f : ι → PowerSeries ℚ)
    (hf : ∀ i ∈ s, isIntegerSeries (f i)) : isIntegerSeries (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isIntegerSeries_one
  | @insert a s has ih =>
      rw [Finset.prod_insert has]
      exact isIntegerSeries_mul (hf a (Finset.mem_insert_self a s))
        (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

private lemma isIntegerSeries_eulerFactor (d : ℕ) (m : ℤ) : isIntegerSeries (eulerFactor d m) := by
  unfold eulerFactor
  split_ifs
  · apply isIntegerSeries_pow
    intro n; rw [PowerSeries.coeff_mk]
    split_ifs
    · exact ⟨1, by simp⟩
    · exact ⟨0, by simp⟩
  · apply isIntegerSeries_pow
    intro n; rw [map_sub, PowerSeries.coeff_one, PowerSeries.coeff_X_pow]
    refine ⟨(if n = 0 then 1 else 0) - (if n = d then 1 else 0), ?_⟩
    push_cast; split_ifs <;> ring

private lemma geom_mul_one_sub (d : ℕ) (hd : 1 ≤ d) :
    (1 - PowerSeries.X ^ d) * (PowerSeries.mk fun n => if d ∣ n then (1 : ℚ) else 0) = 1 := by
  apply PowerSeries.ext; intro n
  rw [sub_mul, one_mul, map_sub, PowerSeries.coeff_mk, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_one]
  by_cases hn0 : n = 0
  · subst hn0
    have hnot : ¬ d ≤ 0 := by omega
    simp [hnot]
  · simp only [hn0, ↓reduceIte]
    by_cases hle : d ≤ n
    · simp only [hle, ↓reduceIte, PowerSeries.coeff_mk]
      have hiff : d ∣ n - d ↔ d ∣ n := by
        constructor
        · intro h; rw [← Nat.sub_add_cancel hle]; exact dvd_add h (dvd_refl d)
        · intro h; exact (Nat.dvd_sub_self_right.mpr (Or.inl h))
      by_cases hdiv : d ∣ n
      · simp [hdiv, hiff.mpr hdiv]
      · simp [hdiv, mt hiff.mp hdiv]
    · simp only [hle, ↓reduceIte, sub_zero]
      have hndiv : ¬ d ∣ n := fun h => hle (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) h)
      simp [hndiv]

private lemma coeff_zero_eulerFactor (d : ℕ) (hd : 1 ≤ d) (m : ℤ) :
    PowerSeries.coeff 0 (eulerFactor d m) = 1 := by
  unfold eulerFactor
  split_ifs
  · rw [PowerSeries.coeff_zero_eq_constantCoeff, map_pow, ← PowerSeries.coeff_zero_eq_constantCoeff,
        PowerSeries.coeff_mk]
    simp
  · rw [PowerSeries.coeff_zero_eq_constantCoeff, map_pow, map_sub, map_one, map_pow,
        PowerSeries.constantCoeff_X, zero_pow (by omega), sub_zero, one_pow]

private lemma eulerFactor_ode (d : ℕ) (hd : 1 ≤ d) (m : ℤ) :
    PowerSeries.X * PowerSeries.derivative ℚ (eulerFactor d m) =
      eulerFactor d m * PowerSeries.mk fun n => if n ≠ 0 ∧ d ∣ n then ((d : ℚ) * (m : ℚ)) else 0 := by
  set G : PowerSeries ℚ := PowerSeries.mk fun n => if d ∣ n then (1 : ℚ) else 0
  have hG : (1 - PowerSeries.X ^ d) * G = 1 := geom_mul_one_sub d hd
  have hG_tail : PowerSeries.mk (fun n => if n ≠ 0 ∧ d ∣ n then (1 : ℚ) else 0) =
      PowerSeries.X ^ d * G := by
    apply PowerSeries.ext; intro n
    rw [PowerSeries.coeff_mk, PowerSeries.coeff_X_pow_mul']
    by_cases hle : d ≤ n
    · have hn0 : n ≠ 0 := by omega
      simp only [hle, hn0, ne_eq, not_false_eq_true, true_and, ↓reduceIte, G, PowerSeries.coeff_mk]
      have hiff : d ∣ n - d ↔ d ∣ n := by
        constructor
        · intro h; rw [← Nat.sub_add_cancel hle]; exact dvd_add h (dvd_refl d)
        · intro h; exact Nat.dvd_sub_self_right.mpr (Or.inl h)
      by_cases hdiv : d ∣ n
      · simp [hdiv, hiff.mpr hdiv]
      · simp [hdiv, mt hiff.mp hdiv]
    · simp only [hle, ↓reduceIte]
      split_ifs with h
      · exfalso; exact hle (Nat.le_of_dvd (Nat.pos_of_ne_zero h.1) h.2)
      · rfl
  have hRHS_eq :
      PowerSeries.mk (fun n => if n ≠ 0 ∧ d ∣ n then ((d : ℚ) * (m : ℚ)) else 0) =
      PowerSeries.C ((d : ℚ) * (m : ℚ)) * (PowerSeries.X ^ d * G) := by
    rw [← hG_tail]
    apply PowerSeries.ext; intro n
    rw [PowerSeries.coeff_mk, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk]
    split_ifs <;> ring
  rw [hRHS_eq]
  have hd_one_sub : PowerSeries.X * PowerSeries.derivative ℚ (1 - PowerSeries.X ^ d) =
      -PowerSeries.C (d : ℚ) * PowerSeries.X ^ d := by
    rw [map_sub, Derivation.map_one_eq_zero, zero_sub, mul_neg, Derivation.leibniz_pow,
        PowerSeries.derivative_X, smul_eq_mul, mul_one, nsmul_eq_mul]
    have hX : PowerSeries.X * ((d : PowerSeries ℚ) * PowerSeries.X ^ (d - 1)) =
        PowerSeries.C (d : ℚ) * PowerSeries.X ^ d := by
      have hpow : (PowerSeries.X : PowerSeries ℚ) * PowerSeries.X ^ (d - 1) = PowerSeries.X ^ d := by
        rw [← pow_succ']; congr 1; omega
      rw [show (d : PowerSeries ℚ) = PowerSeries.C (d : ℚ) by rw [map_natCast]]
      linear_combination PowerSeries.C (d : ℚ) * hpow
    rw [hX]; ring
  have hdG : PowerSeries.X * PowerSeries.derivative ℚ G =
      PowerSeries.C (d : ℚ) * PowerSeries.X ^ d * G * G := by
    have hdiff := congr_arg (fun f => PowerSeries.X * PowerSeries.derivative ℚ f) hG
    rw [Derivation.leibniz, Derivation.map_one_eq_zero, mul_zero, mul_add] at hdiff
    simp only [smul_eq_mul] at hdiff
    have h1 : PowerSeries.X * (G * PowerSeries.derivative ℚ (1 - PowerSeries.X ^ d)) =
        -PowerSeries.C (d : ℚ) * PowerSeries.X ^ d * G := by
      calc
        PowerSeries.X * (G * PowerSeries.derivative ℚ (1 - PowerSeries.X ^ d))
          = G * (PowerSeries.X * PowerSeries.derivative ℚ (1 - PowerSeries.X ^ d)) := by ring
        _ = G * (-PowerSeries.C (d : ℚ) * PowerSeries.X ^ d) := by rw [hd_one_sub]
        _ = -PowerSeries.C (d : ℚ) * PowerSeries.X ^ d * G := by ring
    have h2 : (1 - PowerSeries.X ^ d) * (PowerSeries.X * PowerSeries.derivative ℚ G) =
        PowerSeries.C (d : ℚ) * PowerSeries.X ^ d * G := by
      linear_combination hdiff - h1
    calc
      PowerSeries.X * PowerSeries.derivative ℚ G
        = ((1 - PowerSeries.X ^ d) * G) * (PowerSeries.X * PowerSeries.derivative ℚ G) := by
            rw [hG, one_mul]
      _ = G * ((1 - PowerSeries.X ^ d) * (PowerSeries.X * PowerSeries.derivative ℚ G)) := by ring
      _ = G * (PowerSeries.C (d : ℚ) * PowerSeries.X ^ d * G) := by rw [h2]
      _ = PowerSeries.C (d : ℚ) * PowerSeries.X ^ d * G * G := by ring
  unfold eulerFactor
  split_ifs with hm
  · cases hk : m.toNat with
    | zero =>
        have hm0 : (m : ℚ) = 0 := by
          have h1 : (m.toNat : ℤ) = m := Int.toNat_of_nonneg hm
          rw [hk] at h1
          exact_mod_cast h1.symm
        simp [hm0]
    | succ k =>
        have hmk : ((k + 1 : ℕ) : ℚ) = (m : ℚ) := by
          have : ((k + 1 : ℕ) : ℤ) = m := by rw [← hk]; exact Int.toNat_of_nonneg hm
          exact_mod_cast this
        rw [Derivation.leibniz_pow, nsmul_eq_mul]
        simp only [Nat.add_sub_cancel]
        change PowerSeries.X * (((k + 1 : ℕ) : PowerSeries ℚ) * (G ^ k * PowerSeries.derivative ℚ G)) = _
        calc
          PowerSeries.X * (((k + 1 : ℕ) : PowerSeries ℚ) * (G ^ k * PowerSeries.derivative ℚ G))
            = ((k + 1 : ℕ) : PowerSeries ℚ) * G ^ k * (PowerSeries.X * PowerSeries.derivative ℚ G) := by ring
          _ = ((k + 1 : ℕ) : PowerSeries ℚ) * G ^ k * (PowerSeries.C (d : ℚ) * PowerSeries.X ^ d * G * G) := by
                rw [hdG]
          _ = G ^ (k + 1) * (PowerSeries.C ((d : ℚ) * (m : ℚ)) * (PowerSeries.X ^ d * G)) := by
                rw [pow_succ, ← hmk, map_mul, show ((k + 1 : ℕ) : PowerSeries ℚ) =
                  PowerSeries.C ((k + 1 : ℕ) : ℚ) by rw [map_natCast]]
                ring
  · cases hk : (-m).toNat with
    | zero =>
        have hm0 : (m : ℚ) = 0 := by
          have h1 : ((-m).toNat : ℤ) = -m := Int.toNat_of_nonneg (by omega)
          rw [hk] at h1
          have hmz : m = 0 := by omega
          exact_mod_cast hmz
        simp [hm0]
    | succ k =>
        have hmk : ((k + 1 : ℕ) : ℚ) = -(m : ℚ) := by
          have : ((k + 1 : ℕ) : ℤ) = -m := by rw [← hk]; exact Int.toNat_of_nonneg (by omega)
          exact_mod_cast this
        rw [Derivation.leibniz_pow, nsmul_eq_mul]
        simp only [Nat.add_sub_cancel]
        calc
          PowerSeries.X * (((k + 1 : ℕ) : PowerSeries ℚ) * ((1 - PowerSeries.X ^ d) ^ k *
              PowerSeries.derivative ℚ (1 - PowerSeries.X ^ d)))
            = ((k + 1 : ℕ) : PowerSeries ℚ) * (1 - PowerSeries.X ^ d) ^ k *
                (PowerSeries.X * PowerSeries.derivative ℚ (1 - PowerSeries.X ^ d)) := by ring
          _ = ((k + 1 : ℕ) : PowerSeries ℚ) * (1 - PowerSeries.X ^ d) ^ k *
                (-PowerSeries.C (d : ℚ) * PowerSeries.X ^ d) := by rw [hd_one_sub]
          _ = ((k + 1 : ℕ) : PowerSeries ℚ) * (1 - PowerSeries.X ^ d) ^ k *
                (-PowerSeries.C (d : ℚ) * PowerSeries.X ^ d) * ((1 - PowerSeries.X ^ d) * G) := by
                rw [hG, mul_one]
          _ = (1 - PowerSeries.X ^ d) ^ (k + 1) *
                (PowerSeries.C ((d : ℚ) * (m : ℚ)) * (PowerSeries.X ^ d * G)) := by
                have hm_eq : PowerSeries.C (m : ℚ) = -((k + 1 : ℕ) : PowerSeries ℚ) := by
                  have h1 : (m : ℚ) = -((k + 1 : ℕ) : ℚ) := by linarith
                  rw [h1, map_neg, map_natCast]
                rw [pow_succ, map_mul, hm_eq]
                ring

/-- Product rule for `X * (∏ f_i)' = (∏ f_i) * ∑ (X * f_i' / f_i)`. -/
private lemma prod_eulerFactor_ode (N : ℕ) (M : ℕ → ℤ) :
    PowerSeries.X * PowerSeries.derivative ℚ (∏ d ∈ Finset.Icc 1 N, eulerFactor d (M d)) =
      (∏ d ∈ Finset.Icc 1 N, eulerFactor d (M d)) *
        ∑ d ∈ Finset.Icc 1 N,
          PowerSeries.mk fun n => if n ≠ 0 ∧ d ∣ n then ((d : ℚ) * (M d : ℚ)) else 0 := by
  induction N with
  | zero =>
      simp
  | succ N ih =>
      have hIcc : Finset.Icc 1 (N + 1) = insert (N + 1) (Finset.Icc 1 N) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      have hnot : N + 1 ∉ Finset.Icc 1 N := by simp
      rw [hIcc, Finset.prod_insert hnot, Finset.sum_insert hnot, Derivation.leibniz,
          smul_eq_mul, smul_eq_mul, mul_add]
      set P := ∏ d ∈ Finset.Icc 1 N, eulerFactor d (M d)
      set F := eulerFactor (N + 1) (M (N + 1))
      have hF := eulerFactor_ode (N + 1) (by omega) (M (N + 1))
      calc
        PowerSeries.X * (F * PowerSeries.derivative ℚ P) +
            PowerSeries.X * (P * PowerSeries.derivative ℚ F)
          = F * (PowerSeries.X * PowerSeries.derivative ℚ P) +
              P * (PowerSeries.X * PowerSeries.derivative ℚ F) := by ring
        _ = F * (P * ∑ d ∈ Finset.Icc 1 N,
                PowerSeries.mk fun n => if n ≠ 0 ∧ d ∣ n then ((d : ℚ) * (M d : ℚ)) else 0) +
              P * (F * PowerSeries.mk fun n =>
                if n ≠ 0 ∧ (N + 1) ∣ n then (((N + 1 : ℕ) : ℚ) * (M (N + 1) : ℚ)) else 0) := by
              rw [ih, hF]
        _ = F * P * (PowerSeries.mk (fun n =>
                if n ≠ 0 ∧ (N + 1) ∣ n then (((N + 1 : ℕ) : ℚ) * (M (N + 1) : ℚ)) else 0) +
              ∑ d ∈ Finset.Icc 1 N,
                PowerSeries.mk fun n => if n ≠ 0 ∧ d ∣ n then ((d : ℚ) * (M d : ℚ)) else 0) := by
              ring

/-- **Direction ⇐**: If `C(n) = ∑_{d ∣ n} d * M(d)` for some `M : ℕ → ℤ`,
then `expLogSeries C` has integer coefficients! -/
private lemma isIntegerSeries_of_euler_decomp (C M : ℕ → ℤ)
    (hCM : ∀ n : ℕ, 1 ≤ n → C n = ∑ d ∈ Nat.divisors n, (d : ℤ) * M d) :
    isIntegerSeries (expLogSeries C) := by
  intro N
  set P : PowerSeries ℚ := ∏ d ∈ Finset.Icc 1 N, eulerFactor d (M d)
  have hP_int : isIntegerSeries P :=
    isIntegerSeries_prod _ _ fun d _ => isIntegerSeries_eulerFactor d (M d)
  -- Show `coeff n P = coeff n (expLogSeries C)` for all `n ≤ N`!
  have hagree : ∀ n ≤ N, PowerSeries.coeff n P = PowerSeries.coeff n (expLogSeries C) := by
    intro n hn
    induction n using Nat.strong_induction_on with
    | h n ih =>
      cases n with
      | zero =>
          have hP0 : PowerSeries.coeff 0 P = 1 := by
            rw [PowerSeries.coeff_zero_eq_constantCoeff, map_prod]
            refine Finset.prod_eq_one fun d hd => ?_
            rw [← PowerSeries.coeff_zero_eq_constantCoeff]
            exact coeff_zero_eulerFactor d (Finset.mem_Icc.mp hd).1 (M d)
          rw [hP0, expLogSeries, PowerSeries.coeff_mk, expLogCoeffs]
      | succ n =>
          have hP_ode := congr_arg (PowerSeries.coeff (n + 1)) (prod_eulerFactor_ode N M)
          have hE_ode := congr_arg (PowerSeries.coeff (n + 1)) (expLogSeries_ode C)
          rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative, PowerSeries.coeff_mul,
              Finset.Nat.sum_antidiagonal_eq_sum_range_succ
                (fun i j => PowerSeries.coeff i P *
                  PowerSeries.coeff j (∑ d ∈ Finset.Icc 1 N,
                    PowerSeries.mk fun m => if m ≠ 0 ∧ d ∣ m then ((d : ℚ) * (M d : ℚ)) else 0))] at hP_ode
          rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative, PowerSeries.coeff_mul,
              Finset.Nat.sum_antidiagonal_eq_sum_range_succ
                (fun i j => PowerSeries.coeff i (expLogSeries C) *
                  PowerSeries.coeff j (PowerSeries.mk fun m => if m = 0 then 0 else (C m : ℚ)))] at hE_ode
          have hsum_eq :
              ∑ k ∈ Finset.range (n + 2),
                PowerSeries.coeff k P *
                  PowerSeries.coeff (n + 1 - k) (∑ d ∈ Finset.Icc 1 N,
                    PowerSeries.mk fun m => if m ≠ 0 ∧ d ∣ m then ((d : ℚ) * (M d : ℚ)) else 0) =
              ∑ k ∈ Finset.range (n + 2),
                PowerSeries.coeff k (expLogSeries C) *
                  PowerSeries.coeff (n + 1 - k) (PowerSeries.mk fun m => if m = 0 then 0 else (C m : ℚ)) := by
            refine Finset.sum_congr rfl fun k hk => ?_
            have hkl : k ≤ n + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
            by_cases hkeq : k = n + 1
            · subst hkeq; simp [map_sum]
            · rw [ih k (by omega) (by omega)]
              congr 1
              rw [map_sum, PowerSeries.coeff_mk]
              have hm_pos : 1 ≤ n + 1 - k := by omega
              have hm_ne : n + 1 - k ≠ 0 := by omega
              simp only [hm_ne, ne_eq, not_false_eq_true, true_and, ↓reduceIte, PowerSeries.coeff_mk]
              rw [← Finset.sum_filter]
              have hfilt : (Finset.Icc 1 N).filter (fun d => d ∣ n + 1 - k) = Nat.divisors (n + 1 - k) := by
                ext d
                simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
                constructor
                · intro ⟨_, hd⟩; exact ⟨hd, hm_ne⟩
                · intro ⟨hd, _⟩
                  exact ⟨⟨Nat.pos_of_dvd_of_pos hd hm_pos,
                    le_trans (Nat.le_of_dvd hm_pos hd) (by omega)⟩, hd⟩
              rw [hfilt, hCM (n + 1 - k) hm_pos, Int.cast_sum]
              refine Finset.sum_congr rfl fun d _ => by push_cast; ring
          rw [hsum_eq, ← hE_ode] at hP_ode
          have hpos : ((n : ℚ) + 1) ≠ 0 := by positivity
          exact mul_right_cancel₀ hpos hP_ode
  obtain ⟨z, hz⟩ := hP_int N
  exact ⟨z, (hagree N (le_refl N)).symm.trans hz⟩

/-- **Direction ⇒**: If `expLogSeries C` has integer coefficients, then there exists `M : ℕ → ℤ`
such that `C n = ∑_{d ∣ n} d * M d` for all `n ≥ 1`! -/
private lemma exists_euler_decomp_of_isIntegerSeries (C : ℕ → ℤ)
    (hC : isIntegerSeries (expLogSeries C)) :
    ∃ M : ℕ → ℤ, ∀ n : ℕ, 1 ≤ n → C n = ∑ d ∈ Nat.divisors n, (d : ℤ) * M d := by
  -- Greedy construction: for each `N`, there exists `M : ℕ → ℤ` such that
  -- `∏_{d=1}^N eulerFactor d (M d)` agrees with `expLogSeries C` on all `n ≤ N`!
  -- Actually define `M` by strong recursion using `Classical.choose` on the remainder series!
  -- Even simpler: prove by induction on `N` that there exists `M : ℕ → ℤ` with
  -- `∀ n, 1 ≤ n → n ≤ N → C n = ∑ d ∈ Nat.divisors n, (d : ℤ) * M d`!
  -- Wait: since `M n` is UNIQUELY determined by `C` (`n * M n = C n - ∑_{d ∣ n, d < n} d * M d`),
  -- we can just define `M` directly by strong recursion in `ℚ` and prove `M n ∈ ℤ`!
  have hM_exists : ∀ N : ℕ, ∃ M : ℕ → ℤ,
      ∀ n : ℕ, n ≤ N →
        PowerSeries.coeff n (∏ d ∈ Finset.Icc 1 N, eulerFactor d (M d)) =
          PowerSeries.coeff n (expLogSeries C) := by
    intro N
    induction N with
    | zero =>
        refine ⟨fun _ => 0, fun n hn => ?_⟩
        have hn0 : n = 0 := by omega
        subst hn0
        simp [expLogSeries, expLogCoeffs]
    | succ N ih =>
        obtain ⟨M, hM⟩ := ih
        set P := ∏ d ∈ Finset.Icc 1 N, eulerFactor d (M d)
        have hP_int : isIntegerSeries P :=
          isIntegerSeries_prod _ _ fun d _ => isIntegerSeries_eulerFactor d (M d)
        obtain ⟨zE, hzE⟩ := hC (N + 1)
        obtain ⟨zP, hzP⟩ := hP_int (N + 1)
        let m : ℤ := zE - zP
        let M' : ℕ → ℤ := Function.update M (N + 1) m
        refine ⟨M', fun n hn => ?_⟩
        have hIcc : Finset.Icc 1 (N + 1) = insert (N + 1) (Finset.Icc 1 N) := by
          ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
        have hnot : N + 1 ∉ Finset.Icc 1 N := by simp
        rw [hIcc, Finset.prod_insert hnot]
        have hprod_eq : ∏ d ∈ Finset.Icc 1 N, eulerFactor d (M' d) = P := by
          refine Finset.prod_congr rfl fun d hd => ?_
          have hne : d ≠ N + 1 := by have := (Finset.mem_Icc.mp hd).2; omega
          simp [M', hne]
        rw [hprod_eq]
        have hM'N : M' (N + 1) = m := Function.update_self (N + 1) m M
        rw [hM'N]
        -- Compute `coeff k (eulerFactor (N + 1) m)` for `k ≤ N + 1`:
        -- `1` at `k = 0`, `m` at `k = N + 1`, `0` for `0 < k < N + 1`!
        have hF_coeff : ∀ k ≤ N + 1,
            PowerSeries.coeff k (eulerFactor (N + 1) m) =
              if k = 0 then 1 else if k = N + 1 then (m : ℚ) else 0 := by
          intro k hk
          cases k with
          | zero =>
              simp [coeff_zero_eulerFactor (N + 1) (by omega) m]
          | succ k =>
              have hode := congr_arg (PowerSeries.coeff (k + 1))
                (eulerFactor_ode (N + 1) (by omega) m)
              rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative, PowerSeries.coeff_mul,
                  Finset.Nat.sum_antidiagonal_eq_sum_range_succ
                    (fun i j => PowerSeries.coeff i (eulerFactor (N + 1) m) *
                      PowerSeries.coeff j (PowerSeries.mk fun r =>
                        if r ≠ 0 ∧ (N + 1) ∣ r then (((N + 1 : ℕ) : ℚ) * (m : ℚ)) else 0))] at hode
              by_cases hkN : k + 1 = N + 1
              · rw [hkN] at hode ⊢
                rw [Finset.sum_range_succ'] at hode
                have htail :
                    ∑ j ∈ Finset.range (N + 1),
                      PowerSeries.coeff (j + 1) (eulerFactor (N + 1) m) *
                        PowerSeries.coeff (N + 1 - (j + 1)) (PowerSeries.mk fun r =>
                          if r ≠ 0 ∧ (N + 1) ∣ r then (((N + 1 : ℕ) : ℚ) * (m : ℚ)) else 0) = 0 := by
                  refine Finset.sum_eq_zero fun j hj => ?_
                  rw [PowerSeries.coeff_mk]
                  have hlt : N + 1 - (j + 1) < N + 1 := by omega
                  have hnotd : ¬ (N + 1 - (j + 1) ≠ 0 ∧ (N + 1) ∣ (N + 1 - (j + 1))) := by
                    rintro ⟨hne, hd⟩
                    exact absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hd) (by omega)
                  rw [if_neg hnotd, mul_zero]
                rw [htail, zero_add, Nat.sub_zero, coeff_zero_eulerFactor (N + 1) (by omega) m,
                    one_mul, PowerSeries.coeff_mk] at hode
                simp only [Nat.succ_ne_zero, ne_eq, not_false_eq_true, dvd_refl, and_self,
                  ↓reduceIte] at hode ⊢
                have hkN_q : ((k : ℚ) + 1) = ((N + 1 : ℕ) : ℚ) := by exact_mod_cast hkN
                rw [hkN_q] at hode
                have hpos : ((N + 1 : ℕ) : ℚ) ≠ 0 := by positivity
                exact mul_left_cancel₀ hpos (by linarith)
              · have hzero :
                    ∑ j ∈ Finset.range (k + 2),
                      PowerSeries.coeff j (eulerFactor (N + 1) m) *
                        PowerSeries.coeff (k + 1 - j) (PowerSeries.mk fun r =>
                          if r ≠ 0 ∧ (N + 1) ∣ r then (((N + 1 : ℕ) : ℚ) * (m : ℚ)) else 0) = 0 := by
                  refine Finset.sum_eq_zero fun j hj => ?_
                  rw [PowerSeries.coeff_mk]
                  have hnotd : ¬ (k + 1 - j ≠ 0 ∧ (N + 1) ∣ (k + 1 - j)) := by
                    rintro ⟨hne, hd⟩
                    exact absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hd) (by omega)
                  rw [if_neg hnotd, mul_zero]
                rw [hzero] at hode
                have hpos : ((k : ℚ) + 1) ≠ 0 := by positivity
                simp only [Nat.succ_ne_zero, hkN, ↓reduceIte]
                exact (mul_eq_zero.mp hode).resolve_right hpos
        rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
          (fun i j => PowerSeries.coeff i (eulerFactor (N + 1) m) * PowerSeries.coeff j P)]
        by_cases hnN : n = N + 1
        · subst hnN
          rw [Finset.sum_range_succ', Finset.sum_range_succ]
          have hmid :
              ∑ k ∈ Finset.range N,
                PowerSeries.coeff (k + 1) (eulerFactor (N + 1) m) * PowerSeries.coeff (N + 1 - (k + 1)) P = 0 := by
            refine Finset.sum_eq_zero fun k hk => ?_
            have hkl : k < N := Finset.mem_range.mp hk
            rw [hF_coeff (k + 1) (by omega), if_neg (Nat.succ_ne_zero k),
                if_neg (by omega : k + 1 ≠ N + 1), zero_mul]
          rw [hmid, zero_add, hF_coeff 0 (by omega), hF_coeff (N + 1) (le_refl _),
              Nat.sub_zero, Nat.sub_self]
          have hP0 : PowerSeries.coeff 0 P = 1 := by
            rw [hM 0 (Nat.zero_le N), expLogSeries, PowerSeries.coeff_mk, expLogCoeffs]
          simp only [↓reduceIte, Nat.succ_ne_zero, one_mul, hP0, mul_one]
          rw [hzP, hzE]
          simp only [m, Int.cast_sub]
          ring
        · rw [Finset.sum_range_succ']
          have htail :
              ∑ k ∈ Finset.range n,
                PowerSeries.coeff (k + 1) (eulerFactor (N + 1) m) * PowerSeries.coeff (n - (k + 1)) P = 0 := by
            refine Finset.sum_eq_zero fun k hk => ?_
            have hkl : k < n := Finset.mem_range.mp hk
            rw [hF_coeff (k + 1) (by omega), if_neg (Nat.succ_ne_zero k),
                if_neg (by omega : k + 1 ≠ N + 1), zero_mul]
          rw [htail, zero_add, hF_coeff 0 (by omega), Nat.sub_zero]
          simp only [↓reduceIte, one_mul]
          exact hM n (by omega)
  -- Define `M_nat n` by extracting `M_N n` from `hM_exists n` (it is unique for `d ≤ N`)!
  -- Actually we can show that for any `N` and `M` from `hM_exists N`,
  -- `C n = ∑ d ∈ Nat.divisors n, (d : ℤ) * M d` for all `1 ≤ n ≤ N`!
  -- Even cleaner: prove `∀ N, ∃ M : ℕ → ℤ, ∀ n, 1 ≤ n → n ≤ N → C n = ∑ d ∈ Nat.divisors n, d * M d`,
  -- AND note `M d` is uniquely determined by `C` (Möbius inversion / strong recursion)!
  have hM_div : ∀ (N : ℕ) (M : ℕ → ℤ),
      (∀ n ≤ N, PowerSeries.coeff n (∏ d ∈ Finset.Icc 1 N, eulerFactor d (M d)) =
        PowerSeries.coeff n (expLogSeries C)) →
      ∀ n : ℕ, 1 ≤ n → n ≤ N → C n = ∑ d ∈ Nat.divisors n, (d : ℤ) * M d := by
    intro N M hM n hn1 hnN
    induction n using Nat.strong_induction_on with
    | h n ih =>
      set P := ∏ d ∈ Finset.Icc 1 N, eulerFactor d (M d)
      have hP_ode := congr_arg (PowerSeries.coeff n) (prod_eulerFactor_ode N M)
      have hE_ode := congr_arg (PowerSeries.coeff n) (expLogSeries_ode C)
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
      rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative] at hP_ode hE_ode
      rw [hM (m + 1) hnN] at hP_ode
      have heq := hP_ode.symm.trans hE_ode
      rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul,
          Finset.Nat.sum_antidiagonal_eq_sum_range_succ
            (fun i j => PowerSeries.coeff i P *
              PowerSeries.coeff j (∑ d ∈ Finset.Icc 1 N,
                PowerSeries.mk fun r => if r ≠ 0 ∧ d ∣ r then ((d : ℚ) * (M d : ℚ)) else 0)),
          Finset.Nat.sum_antidiagonal_eq_sum_range_succ
            (fun i j => PowerSeries.coeff i (expLogSeries C) *
              PowerSeries.coeff j (PowerSeries.mk fun r => if r = 0 then 0 else (C r : ℚ)))] at heq
      conv_lhs at heq => rw [Finset.sum_range_succ']
      conv_rhs at heq => rw [Finset.sum_range_succ']
      have htail :
          ∑ k ∈ Finset.range (m + 1),
            PowerSeries.coeff (k + 1) P *
              PowerSeries.coeff (m + 1 - (k + 1)) (∑ d ∈ Finset.Icc 1 N,
                PowerSeries.mk fun r => if r ≠ 0 ∧ d ∣ r then ((d : ℚ) * (M d : ℚ)) else 0) =
          ∑ k ∈ Finset.range (m + 1),
            PowerSeries.coeff (k + 1) (expLogSeries C) *
              PowerSeries.coeff (m + 1 - (k + 1)) (PowerSeries.mk fun r => if r = 0 then 0 else (C r : ℚ)) := by
        refine Finset.sum_congr rfl fun k hk => ?_
        have hkl : k < m + 1 := Finset.mem_range.mp hk
        rw [hM (k + 1) (by omega)]
        congr 1
        by_cases hkm : k = m
        · subst hkm; simp [map_sum]
        · have hpos : 1 ≤ m + 1 - (k + 1) := by omega
          have hne : m + 1 - (k + 1) ≠ 0 := by omega
          rw [map_sum, PowerSeries.coeff_mk]
          simp only [hne, ne_eq, not_false_eq_true, true_and, ↓reduceIte, PowerSeries.coeff_mk]
          rw [← Finset.sum_filter]
          have hfilt : (Finset.Icc 1 N).filter (fun d => d ∣ m + 1 - (k + 1)) =
              Nat.divisors (m + 1 - (k + 1)) := by
            ext d; simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
            constructor
            · intro ⟨_, hd⟩; exact ⟨hd, hne⟩
            · intro ⟨hd, _⟩
              exact ⟨⟨Nat.pos_of_dvd_of_pos hd hpos,
                le_trans (Nat.le_of_dvd hpos hd) (by omega)⟩, hd⟩
          rw [hfilt, ih (m + 1 - (k + 1)) (by omega) hpos (by omega), Int.cast_sum]
          refine Finset.sum_congr rfl fun d _ => by push_cast; ring
      rw [htail, Nat.sub_zero, hM 0 (Nat.zero_le N)] at heq
      have hE0 : PowerSeries.coeff 0 (expLogSeries C) = 1 := by simp [expLogSeries, expLogCoeffs]
      rw [hE0, one_mul, one_mul] at heq
      have hterm :
          PowerSeries.coeff (m + 1) (∑ d ∈ Finset.Icc 1 N,
            PowerSeries.mk fun r => if r ≠ 0 ∧ d ∣ r then ((d : ℚ) * (M d : ℚ)) else 0) =
          PowerSeries.coeff (m + 1) (PowerSeries.mk fun r => if r = 0 then 0 else (C r : ℚ)) := by
        linarith
      rw [map_sum, PowerSeries.coeff_mk] at hterm
      simp only [Nat.succ_ne_zero, ne_eq, not_false_eq_true, true_and, ↓reduceIte,
        PowerSeries.coeff_mk] at hterm
      rw [← Finset.sum_filter] at hterm
      have hfilt : (Finset.Icc 1 N).filter (fun d => d ∣ m + 1) = Nat.divisors (m + 1) := by
        ext d; simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
        constructor
        · intro ⟨_, hd⟩; exact ⟨hd, Nat.succ_ne_zero m⟩
        · intro ⟨hd, _⟩
          exact ⟨⟨Nat.pos_of_dvd_of_pos hd (by omega),
            le_trans (Nat.le_of_dvd (by omega) hd) hnN⟩, hd⟩
      rw [hfilt] at hterm
      have hq : ((C (m + 1) : ℤ) : ℚ) = ((∑ d ∈ Nat.divisors (m + 1), (d : ℤ) * M d : ℤ) : ℚ) := by
        rw [Int.cast_sum, ← hterm]
        refine Finset.sum_congr rfl fun d _ => by push_cast; ring
      exact_mod_cast hq
  -- Global `M`: for each `d`, pick `M_d` from `hM_exists d` (and show `M_N d = M_d d` for all `d ≤ N`)!
  choose Mfam hMfam using hM_exists
  refine ⟨fun d => Mfam d d, fun n hn => ?_⟩
  have huniq : ∀ (N₁ N₂ : ℕ) (M₁ M₂ : ℕ → ℤ),
      (∀ k, 1 ≤ k → k ≤ N₁ → C k = ∑ d ∈ Nat.divisors k, (d : ℤ) * M₁ d) →
      (∀ k, 1 ≤ k → k ≤ N₂ → C k = ∑ d ∈ Nat.divisors k, (d : ℤ) * M₂ d) →
      ∀ d, 1 ≤ d → d ≤ N₁ → d ≤ N₂ → M₁ d = M₂ d := by
    intro N₁ N₂ M₁ M₂ h1 h2 d hd1 hdN₁ hdN₂
    induction d using Nat.strong_induction_on with
    | h d ih =>
      have heq := (h1 d hd1 hdN₁).symm.trans (h2 d hd1 hdN₂)
      have hmem : d ∈ Nat.divisors d := Nat.mem_divisors.mpr ⟨dvd_refl d, by omega⟩
      rw [← Finset.add_sum_erase _ _ hmem, ← Finset.add_sum_erase _ _ hmem] at heq
      have hrest :
          ∑ x ∈ (Nat.divisors d).erase d, (x : ℤ) * M₁ x =
          ∑ x ∈ (Nat.divisors d).erase d, (x : ℤ) * M₂ x := by
        refine Finset.sum_congr rfl fun x hx => ?_
        have hne : x ≠ d := (Finset.mem_erase.mp hx).1
        have hxd : x ∣ d := (Nat.mem_divisors.mp (Finset.mem_erase.mp hx).2).1
        have hx1 : 1 ≤ x := Nat.pos_of_dvd_of_pos hxd (by omega)
        have hxlt : x < d := lt_of_le_of_ne (Nat.le_of_dvd (by omega) hxd) hne
        rw [ih x hxlt hx1 (by omega) (by omega)]
      rw [hrest] at heq
      have hmul : (d : ℤ) * M₁ d = (d : ℤ) * M₂ d := by linarith
      exact mul_left_cancel₀ (by omega : (d : ℤ) ≠ 0) hmul
  have hn_eq := hM_div n (Mfam n) (hMfam n) n hn (le_refl n)
  rw [hn_eq]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdn : d ∣ n := (Nat.mem_divisors.mp hd).1
  have hd1 : 1 ≤ d := Nat.pos_of_dvd_of_pos hdn (by omega)
  have hdle : d ≤ n := Nat.le_of_dvd (by omega) hdn
  congr 1
  exact huniq n d (Mfam n) (Mfam d)
    (hM_div n (Mfam n) (hMfam n)) (hM_div d (Mfam d) (hMfam d)) d hd1 hdle (le_refl d)

/-- Gauss congruence from Euler decomposition:
if `C n = ∑_{d ∣ n} d * M d`, then `p^r ∣ (C (p^r * m) - C (p^(r-1) * m))` for `p` prime, `r ≥ 1`, `p ∤ m`. -/
private lemma gauss_cong_of_euler_decomp (C M : ℕ → ℤ)
    (hCM : ∀ n : ℕ, 1 ≤ n → C n = ∑ d ∈ Nat.divisors n, (d : ℤ) * M d)
    {p r m : ℕ} (hp : p.Prime) (hr : 1 ≤ r) (hm : 1 ≤ m) (hpm : ¬ p ∣ m) :
    ((p ^ r : ℕ) : ℤ) ∣ (C (p ^ r * m) - C (p ^ (r - 1) * m)) := by
  have hpos1 : 1 ≤ p ^ r * m := Nat.mul_pos (pow_pos hp.pos r) hm
  have hpos2 : 1 ≤ p ^ (r - 1) * m := Nat.mul_pos (pow_pos hp.pos (r - 1)) hm
  rw [hCM _ hpos1, hCM _ hpos2]
  have hsub : Nat.divisors (p ^ (r - 1) * m) ⊆ Nat.divisors (p ^ r * m) := by
    intro d hd
    have hdiv := (Nat.mem_divisors.mp hd).1
    refine Nat.mem_divisors.mpr ⟨dvd_trans hdiv ?_, by omega⟩
    exact Nat.mul_dvd_mul_right (Nat.pow_dvd_pow p (by omega)) m
  rw [← Finset.sum_sdiff hsub, add_sub_cancel_right]
  refine Finset.dvd_sum fun d hd => ?_
  have hmem1 := (Finset.mem_sdiff.mp hd).1
  have hnot2 := (Finset.mem_sdiff.mp hd).2
  have hd_div : d ∣ p ^ r * m := (Nat.mem_divisors.mp hmem1).1
  have hd_ndiv : ¬ d ∣ p ^ (r - 1) * m := fun h => hnot2 (Nat.mem_divisors.mpr ⟨h, by omega⟩)
  have hpr_dvd : p ^ r ∣ d := by
    have hd_pos : 0 < d := Nat.pos_of_dvd_of_pos hd_div hpos1
    have hcop : Nat.Coprime (p ^ r) m := (hp.coprime_iff_not_dvd.mpr hpm).pow_left r
    -- Write `d = g * u` where `g = gcd(d, p^r)` divides `p^r` and `u` divides `m`!
    obtain ⟨a, b, ha, hb, rfl⟩ := Nat.dvd_mul.mp hd_div
    have hpow := (Nat.dvd_prime_pow hp).mp ha
    obtain ⟨k, hk, rfl⟩ := hpow
    by_cases hkr : k = r
    · subst hkr; exact dvd_mul_right (p ^ k) b
    · exfalso; apply hd_ndiv
      exact Nat.mul_dvd_mul (Nat.pow_dvd_pow p (by omega)) hb
  exact dvd_mul_of_dvd_left (Int.natCast_dvd_natCast.mpr hpr_dvd) (M d)

/-- Binomial lifting: for any `b : ℤ`, prime `p`, `r ≥ 1`, `p^r ∣ (b^(p^r) - b^(p^(r-1)))`. -/
private lemma pow_prime_pow_sub_dvd {p : ℕ} (hp : p.Prime) (b : ℤ) :
    ∀ r : ℕ, 1 ≤ r → ((p ^ r : ℕ) : ℤ) ∣ (b ^ (p ^ r) - b ^ (p ^ (r - 1)))
  | 0, h => by omega
  | 1, _ => by
      simp only [pow_one, Nat.sub_self, pow_zero]
      have : Fact p.Prime := ⟨hp⟩
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      simp [ZMod.pow_card]
  | r + 2, _ => by
      have ih := pow_prime_pow_sub_dvd hp b (r + 1) (by omega)
      simp only [Nat.add_sub_cancel] at ih ⊢
      obtain ⟨t, ht⟩ := ih
      set u : ℤ := b ^ (p ^ r)
      have hbu : b ^ (p ^ (r + 1)) = u + ((p ^ (r + 1) : ℕ) : ℤ) * t := by linarith
      have hpow1 : b ^ (p ^ (r + 2)) = (b ^ (p ^ (r + 1))) ^ p := by
        rw [← pow_mul, ← pow_succ]
      have hpow2 : b ^ (p ^ (r + 1)) = u ^ p := by
        simp only [u, ← pow_mul, ← pow_succ]
      have hr2 : r + 2 - 1 = r + 1 := by omega
      rw [hr2, hpow1]
      nth_rw 1 [hbu]
      rw [add_comm u, add_pow, Finset.sum_range_succ', Nat.sub_zero, ← hpow2]
      simp only [pow_zero, Nat.choose_zero_right, Nat.cast_one, mul_one, one_mul,
        add_sub_cancel_right]
      refine Finset.dvd_sum fun j hj => ?_
      have hjlt : j < p := Finset.mem_range.mp hj
      by_cases hjp : j + 1 = p
      · rw [hjp]
        have hdvd : ((p ^ (r + 2) : ℕ) : ℤ) ∣ (((p ^ (r + 1) : ℕ) : ℤ) * t) ^ p := by
          rw [mul_pow, ← Nat.cast_pow, ← pow_mul]
          refine dvd_mul_of_dvd_left (Int.natCast_dvd_natCast.mpr (Nat.pow_dvd_pow p ?_)) _
          have hp2 : 2 ≤ p := hp.two_le
          nlinarith
        exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hdvd _) _
      · have hch : p ∣ Nat.choose p (j + 1) := hp.dvd_choose_self (by omega) (by omega)
        have hch_z : (p : ℤ) ∣ (Nat.choose p (j + 1) : ℤ) := Int.natCast_dvd_natCast.mpr hch
        have hpow_z : ((p ^ (r + 1) : ℕ) : ℤ) ∣ (((p ^ (r + 1) : ℕ) : ℤ) * t) ^ (j + 1) := by
          conv_rhs => rw [pow_succ']
          exact dvd_mul_of_dvd_left (dvd_mul_right _ t) _
        have hprod : ((p ^ (r + 2) : ℕ) : ℤ) ∣
            (((p ^ (r + 1) : ℕ) : ℤ) * t) ^ (j + 1) * (Nat.choose p (j + 1) : ℤ) := by
          rw [pow_succ, Nat.cast_mul]
          exact mul_dvd_mul hpow_z hch_z
        have hre : (((p ^ (r + 1) : ℕ) : ℤ) * t) ^ (j + 1) * u ^ (p - (j + 1)) *
            (Nat.choose p (j + 1) : ℤ) =
            u ^ (p - (j + 1)) * ((((p ^ (r + 1) : ℕ) : ℤ) * t) ^ (j + 1) * (Nat.choose p (j + 1) : ℤ)) := by
          ring
        rw [hre]
        exact dvd_mul_of_dvd_right hprod _

/-- Gauss congruence for `C' n = (C n)^n` when `C` satisfies the Gauss congruence! -/
private lemma gauss_cong_pow_self (C : ℕ → ℤ)
    (hC : ∀ {p r m : ℕ}, p.Prime → 1 ≤ r → 1 ≤ m → ¬ p ∣ m →
      ((p ^ r : ℕ) : ℤ) ∣ (C (p ^ r * m) - C (p ^ (r - 1) * m)))
    {p r m : ℕ} (hp : p.Prime) (hr : 1 ≤ r) (hm : 1 ≤ m) (hpm : ¬ p ∣ m) :
    ((p ^ r : ℕ) : ℤ) ∣
      ((C (p ^ r * m)) ^ (p ^ r * m) - (C (p ^ (r - 1) * m)) ^ (p ^ (r - 1) * m)) := by
  set a := C (p ^ r * m)
  set b := C (p ^ (r - 1) * m)
  have hab : ((p ^ r : ℕ) : ℤ) ∣ (a - b) := hC hp hr hm hpm
  have h1 : ((p ^ r : ℕ) : ℤ) ∣ (a ^ (p ^ r * m) - b ^ (p ^ r * m)) :=
    dvd_trans hab (sub_dvd_pow_sub_pow a b (p ^ r * m))
  have h2 : ((p ^ r : ℕ) : ℤ) ∣ (b ^ (p ^ r * m) - b ^ (p ^ (r - 1) * m)) := by
    rw [pow_mul, pow_mul]
    exact dvd_trans (pow_prime_pow_sub_dvd hp b r hr) (sub_dvd_pow_sub_pow _ _ m)
  have hsum : a ^ (p ^ r * m) - b ^ (p ^ (r - 1) * m) =
      (a ^ (p ^ r * m) - b ^ (p ^ r * m)) + (b ^ (p ^ r * m) - b ^ (p ^ (r - 1) * m)) := by ring
  rw [hsum]
  exact dvd_add h1 h2

/-- Divisibility of the Möbius convolution by `d` from Gauss congruences:
if `C` satisfies Gauss congruences at all prime powers, then
`d ∣ ∑_{k ∣ d} μ(d / k) * C(k)` for every `d ≥ 1`! -/
private lemma dvd_moebius_sum_of_gauss_cong (C : ℕ → ℤ)
    (hC : ∀ {p r m : ℕ}, p.Prime → 1 ≤ r → 1 ≤ m → ¬ p ∣ m →
      ((p ^ r : ℕ) : ℤ) ∣ (C (p ^ r * m) - C (p ^ (r - 1) * m)))
    (d : ℕ) (hd : 1 ≤ d) :
    (d : ℤ) ∣ ∑ k ∈ Nat.divisors d, (ArithmeticFunction.moebius (d / k) : ℤ) * C k := by
  -- Suffices to show `p^r ∣ sum` for every prime power `p^r ‖ d`, by strong induction on `d`!
  -- Better: use `Nat.Coprime` decomposition `d = p^r * u` with `p ∤ u`!
  have hprime_pow : ∀ {p r u : ℕ}, p.Prime → 1 ≤ r → 1 ≤ u → ¬ p ∣ u →
      ((p ^ r : ℕ) : ℤ) ∣
        ∑ k ∈ Nat.divisors (p ^ r * u), (ArithmeticFunction.moebius (p ^ r * u / k) : ℤ) * C k := by
    intro p r u hp hr hu hpu
    -- Reindex by `t = d / k` (`∑_{t ∣ d} μ(t) * C(d / t)`)!
    have hreidx :
        ∑ k ∈ Nat.divisors (p ^ r * u), (ArithmeticFunction.moebius (p ^ r * u / k) : ℤ) * C k =
        ∑ t ∈ Nat.divisors (p ^ r * u), (ArithmeticFunction.moebius t : ℤ) * C (p ^ r * u / t) := by
      refine Finset.sum_nbij (fun k => p ^ r * u / k) ?_ ?_ ?_ ?_
      · intro k hk
        have hkd := (Nat.mem_divisors.mp hk).1
        exact Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd hkd, Nat.mul_ne_zero (pow_ne_zero _ hp.ne_zero) (by omega)⟩
      · intro k₁ hk₁ k₂ hk₂ heq
        have h1 := (Nat.mem_divisors.mp hk₁).1
        have h2 := (Nat.mem_divisors.mp hk₂).1
        have hpos : 0 < p ^ r * u := Nat.mul_pos (pow_pos hp.pos r) hu
        have h1' : k₁ * (p ^ r * u / k₁) = p ^ r * u := Nat.mul_div_cancel' h1
        have h2' : k₂ * (p ^ r * u / k₂) = p ^ r * u := Nat.mul_div_cancel' h2
        have hdiv_pos : 0 < p ^ r * u / k₁ := Nat.div_pos (Nat.le_of_dvd hpos h1) (Nat.pos_of_dvd_of_pos h1 hpos)
        dsimp at heq
        rw [← heq] at h2'
        exact Nat.eq_of_mul_eq_mul_right hdiv_pos (h1'.trans h2'.symm)
      · intro t ht
        have htd := (Nat.mem_divisors.mp ht).1
        have hpos : 0 < p ^ r * u := Nat.mul_pos (pow_pos hp.pos r) hu
        refine ⟨p ^ r * u / t, Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd htd,
          Nat.mul_ne_zero (pow_ne_zero _ hp.ne_zero) (by omega)⟩, ?_⟩
        exact Nat.div_div_self htd (by omega)
      · intro k hk
        have hkd := (Nat.mem_divisors.mp hk).1
        have hpos : 0 < p ^ r * u := Nat.mul_pos (pow_pos hp.pos r) hu
        rw [Nat.div_div_self hkd (by omega)]
    rw [hreidx]
    -- Reindex `t ∈ divisors (p^r * u)` as `(i, s) ∈ range (r + 1) ×ˢ divisors u` via `(i, s) ↦ p^i * s`!
    have hsplit :
        ∑ t ∈ Nat.divisors (p ^ r * u), (ArithmeticFunction.moebius t : ℤ) * C (p ^ r * u / t) =
        ∑ x ∈ Finset.range (r + 1) ×ˢ Nat.divisors u,
          (ArithmeticFunction.moebius (p ^ x.1 * x.2) : ℤ) * C (p ^ r * u / (p ^ x.1 * x.2)) := by
      symm
      refine Finset.sum_nbij (fun x => p ^ x.1 * x.2) ?_ ?_ ?_ ?_
      · intro x hx
        have h1 : x.1 ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_product.mp hx).1)
        have h2 : x.2 ∣ u := (Nat.mem_divisors.mp (Finset.mem_product.mp hx).2).1
        exact Nat.mem_divisors.mpr ⟨Nat.mul_dvd_mul (Nat.pow_dvd_pow p h1) h2,
          Nat.mul_ne_zero (pow_ne_zero _ hp.ne_zero) (by omega)⟩
      · intro x₁ hx₁ x₂ hx₂ heq
        dsimp at heq
        have hs1 : x₁.2 ∣ u := (Nat.mem_divisors.mp (Finset.mem_product.mp hx₁).2).1
        have hs2 : x₂.2 ∣ u := (Nat.mem_divisors.mp (Finset.mem_product.mp hx₂).2).1
        have hnp1 : ¬ p ∣ x₁.2 := fun h => hpu (dvd_trans h hs1)
        have hnp2 : ¬ p ∣ x₂.2 := fun h => hpu (dvd_trans h hs2)
        have hi : x₁.1 = x₂.1 := by
          have h1 : (p ^ x₁.1 * x₁.2).factorization p = x₁.1 := by
            rw [Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) (Nat.pos_of_dvd_of_pos hs1 hu).ne',
                Finsupp.add_apply, hp.factorization_pow, Finsupp.single_eq_same,
                Nat.factorization_eq_zero_of_not_dvd hnp1, add_zero]
          have h2 : (p ^ x₂.1 * x₂.2).factorization p = x₂.1 := by
            rw [Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) (Nat.pos_of_dvd_of_pos hs2 hu).ne',
                Finsupp.add_apply, hp.factorization_pow, Finsupp.single_eq_same,
                Nat.factorization_eq_zero_of_not_dvd hnp2, add_zero]
          rw [← h1, heq, h2]
        have hs : x₁.2 = x₂.2 := by
          rw [hi] at heq
          exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos x₂.1) heq
        exact Prod.ext hi hs
      · intro t ht
        have htd : t ∣ p ^ r * u := (Nat.mem_divisors.mp ht).1
        obtain ⟨a, b, ha, hb, rfl⟩ := Nat.dvd_mul.mp htd
        obtain ⟨i, hi, rfl⟩ := (Nat.dvd_prime_pow hp).mp ha
        exact ⟨(i, b), Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega),
          Nat.mem_divisors.mpr ⟨hb, by omega⟩⟩, rfl⟩
      · intro _ _; rfl
    rw [hsplit, Finset.sum_product_right]
    refine Finset.dvd_sum fun s hs => ?_
    have hsu : s ∣ u := (Nat.mem_divisors.mp hs).1
    have hps : ¬ p ∣ s := fun h => hpu (dvd_trans h hsu)
    have hcop_ps : Nat.Coprime p s := hp.coprime_iff_not_dvd.mpr hps
    have hus_pos : 1 ≤ u / s := Nat.div_pos (Nat.le_of_dvd hu hsu) (Nat.pos_of_dvd_of_pos hsu hu)
    have hpus : ¬ p ∣ u / s := fun h => hpu (dvd_trans h (Nat.div_dvd_of_dvd hsu))
    -- Split `range (r + 1)` into `i = 0`, `i = 1`, and `i ≥ 2` (where `moebius (p^i * s) = 0`)!
    obtain ⟨r', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
    rw [Finset.sum_range_succ', Finset.sum_range_succ']
    dsimp only
    simp only [Nat.succ_eq_add_one]
    have hzero :
        ∑ i ∈ Finset.range r',
          (ArithmeticFunction.moebius (p ^ (i + 1 + 1) * s) : ℤ) *
            C (p ^ (r' + 1) * u / (p ^ (i + 1 + 1) * s)) = 0 := by
      refine Finset.sum_eq_zero fun i _ => ?_
      have hnsq : ¬ Squarefree (p ^ (i + 1 + 1) * s) := by
        intro hsq
        have hp2 : p * p ∣ p ^ (i + 1 + 1) * s := by
          have : p * p ∣ p ^ (i + 1 + 1) := by
            rw [← sq]; exact Nat.pow_dvd_pow p (by omega)
          exact dvd_mul_of_dvd_left this s
        exact hp.ne_one (Nat.isUnit_iff.mp (hsq p hp2))
      rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnsq, zero_mul]
    rw [hzero, zero_add]
    have h0 : p ^ (r' + 1) * u / (p ^ 0 * s) = p ^ (r' + 1) * (u / s) := by
      rw [pow_zero, one_mul, Nat.mul_div_assoc _ hsu]
    have h1 : p ^ (r' + 1) * u / (p ^ 1 * s) = p ^ r' * (u / s) := by
      rw [pow_one, pow_succ', mul_assoc, Nat.mul_div_mul_left _ _ hp.pos, Nat.mul_div_assoc _ hsu]
    have hmu1 : (ArithmeticFunction.moebius (p ^ 1 * s) : ℤ) = -(ArithmeticFunction.moebius s : ℤ) := by
      rw [pow_one, ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop_ps,
          ArithmeticFunction.moebius_apply_prime hp]
      ring
    rw [zero_add, h0, h1, hmu1, pow_zero, one_mul]
    have hcomb : -(ArithmeticFunction.moebius s : ℤ) * C (p ^ r' * (u / s)) +
        (ArithmeticFunction.moebius s : ℤ) * C (p ^ (r' + 1) * (u / s)) =
        (ArithmeticFunction.moebius s : ℤ) *
          (C (p ^ (r' + 1) * (u / s)) - C (p ^ r' * (u / s))) := by ring
    rw [hcomb]
    have hstep : ((p ^ (r' + 1) : ℕ) : ℤ) ∣
        (C (p ^ (r' + 1) * (u / s)) - C (p ^ r' * (u / s))) := by
      simpa [Nat.add_sub_cancel] using hC hp (show 1 ≤ r' + 1 by omega) hus_pos hpus
    exact dvd_mul_of_dvd_right hstep _
  -- Combine all prime-power divisibilities via `Nat.prod_factorization_pow_eq_self`!
  have hd_ne : d ≠ 0 := by omega
  have hprod_eq : (∏ p ∈ d.primeFactors, ((p ^ d.factorization p : ℕ) : ℤ)) = (d : ℤ) := by
    rw [← Nat.cast_prod, ← Nat.support_factorization d]
    exact_mod_cast Nat.prod_factorization_pow_eq_self hd_ne
  rw [← hprod_eq]
  refine Finset.prod_dvd_of_coprime ?_ ?_
  · intro p hp q hq hpq
    have hp' := Nat.prime_of_mem_primeFactors hp
    have hq' := Nat.prime_of_mem_primeFactors hq
    exact (((Nat.coprime_primes hp' hq').mpr hpq).pow _ _).isCoprime
  · intro p hp
    have hp' := Nat.prime_of_mem_primeFactors hp
    have hr : 1 ≤ d.factorization p := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp)
    have hpow_dvd : p ^ d.factorization p ∣ d := Nat.ordProj_dvd d p
    set r := d.factorization p
    set u := d / p ^ r
    have hdu : p ^ r * u = d := Nat.mul_div_cancel' hpow_dvd
    have hu_pos : 1 ≤ u := Nat.div_pos (Nat.le_of_dvd (by omega) hpow_dvd) (pow_pos hp'.pos r)
    have hpu : ¬ p ∣ u := by
      intro h
      have hpow1 : p ^ (r + 1) ∣ d := by
        rw [← hdu, pow_succ]
        exact Nat.mul_dvd_mul_left (p ^ r) h
      have hle := (hp'.pow_dvd_iff_le_factorization hd_ne).mp hpow1
      omega
    rw [← hdu]
    exact hprime_pow hp' hr hu_pos hpu

/-- **Direction ⇐ (Gauss congruence version)**:
if `C` satisfies Gauss congruences at all prime powers, then `expLogSeries C` has integer coefficients! -/
private lemma isIntegerSeries_of_gauss_cong (C : ℕ → ℤ)
    (hC : ∀ {p r m : ℕ}, p.Prime → 1 ≤ r → 1 ≤ m → ¬ p ∣ m →
      ((p ^ r : ℕ) : ℤ) ∣ (C (p ^ r * m) - C (p ^ (r - 1) * m))) :
    isIntegerSeries (expLogSeries C) := by
  let M : ℕ → ℤ := fun d =>
    if d = 0 then 0 else (∑ k ∈ Nat.divisors d, (ArithmeticFunction.moebius (d / k) : ℤ) * C k) / (d : ℤ)
  apply isIntegerSeries_of_euler_decomp C M
  intro n hn
  have hd_mul : ∀ d ∈ Nat.divisors n,
      (d : ℤ) * M d = ∑ k ∈ Nat.divisors d, (ArithmeticFunction.moebius (d / k) : ℤ) * C k := by
    intro d hd
    have hdn : d ∣ n := (Nat.mem_divisors.mp hd).1
    have hd1 : 1 ≤ d := Nat.pos_of_dvd_of_pos hdn (by omega)
    simp only [M, show d ≠ 0 by omega, ↓reduceIte]
    exact Int.mul_ediv_cancel' (dvd_moebius_sum_of_gauss_cong C hC d hd1)
  rw [Finset.sum_congr rfl hd_mul]
  -- Apply Möbius inversion: `∑_{d ∣ n} ∑_{k ∣ d} μ(d / k) * C(k) = C(n)`!
  -- Rewrite as `∑_{k ∣ n} C(k) * (∑_{t ∣ n / k} μ(t))` and use `∑_{t ∣ m} μ(t) = [m = 1]`!
  have hswap :
      ∑ d ∈ Nat.divisors n, ∑ k ∈ Nat.divisors d, (ArithmeticFunction.moebius (d / k) : ℤ) * C k =
      ∑ k ∈ Nat.divisors n, C k * ∑ t ∈ Nat.divisors (n / k), (ArithmeticFunction.moebius t : ℤ) := by
    have h1 :
        ∑ d ∈ Nat.divisors n, ∑ k ∈ Nat.divisors d, (ArithmeticFunction.moebius (d / k) : ℤ) * C k =
        ∑ p ∈ (Nat.divisors n).sigma Nat.divisors, (ArithmeticFunction.moebius (p.1 / p.2) : ℤ) * C p.2 :=
      Finset.sum_sigma' (Nat.divisors n) Nat.divisors
        (fun d k => (ArithmeticFunction.moebius (d / k) : ℤ) * C k)
    have h2 :
        ∑ k ∈ Nat.divisors n, C k * ∑ t ∈ Nat.divisors (n / k), (ArithmeticFunction.moebius t : ℤ) =
        ∑ p ∈ (Nat.divisors n).sigma (fun k => Nat.divisors (n / k)),
          C p.1 * (ArithmeticFunction.moebius p.2 : ℤ) := by
      rw [← Finset.sum_sigma' (Nat.divisors n) (fun k => Nat.divisors (n / k))
        (fun k t => C k * (ArithmeticFunction.moebius t : ℤ))]
      refine Finset.sum_congr rfl fun k _ => Finset.mul_sum _ _ _
    rw [h1, h2]
    refine Finset.sum_nbij (fun p => ⟨p.2, p.1 / p.2⟩) ?_ ?_ ?_ ?_
    · intro p hp
      have hd := (Nat.mem_divisors.mp (Finset.mem_sigma.mp hp).1).1
      have hk := (Nat.mem_divisors.mp (Finset.mem_sigma.mp hp).2).1
      have hkn : p.2 ∣ n := dvd_trans hk hd
      have hpos : 0 < p.2 := Nat.pos_of_dvd_of_pos hkn (by omega)
      have hdiv_pos : 0 < n / p.2 := Nat.div_pos (Nat.le_of_dvd (by omega) hkn) hpos
      refine Finset.mem_sigma.mpr ⟨Nat.mem_divisors.mpr ⟨hkn, by omega⟩,
        Nat.mem_divisors.mpr ⟨?_, Nat.ne_of_gt hdiv_pos⟩⟩
      obtain ⟨c, hc⟩ := hd
      obtain ⟨e, he⟩ := hk
      refine ⟨c, ?_⟩
      rw [hc, he, mul_assoc, Nat.mul_div_cancel_left _ hpos, Nat.mul_div_cancel_left _ hpos]
    · intro p₁ hp₁ p₂ hp₂ heq
      have hk1 := (Nat.mem_divisors.mp (Finset.mem_sigma.mp hp₁).2).1
      have hk2 := (Nat.mem_divisors.mp (Finset.mem_sigma.mp hp₂).2).1
      have h2eq : p₁.2 = p₂.2 := congr_arg Sigma.fst heq
      have hdiv : p₁.1 / p₁.2 = p₂.1 / p₂.2 := by
        simpa [h2eq] using (Sigma.mk.inj_iff.mp heq).2
      have h1eq : p₁.1 = p₂.1 := by
        rw [← Nat.mul_div_cancel' hk1, ← Nat.mul_div_cancel' hk2, hdiv, h2eq]
      exact Sigma.ext h1eq (heq_of_eq h2eq)
    · intro q hq
      have hkn := (Nat.mem_divisors.mp (Finset.mem_sigma.mp hq).1).1
      have htn := (Nat.mem_divisors.mp (Finset.mem_sigma.mp hq).2).1
      have hpos : 0 < q.1 := Nat.pos_of_dvd_of_pos hkn (by omega)
      refine ⟨⟨q.1 * q.2, q.1⟩, Finset.mem_sigma.mpr ⟨Nat.mem_divisors.mpr ⟨?_, by omega⟩,
        Nat.mem_divisors.mpr ⟨dvd_mul_right q.1 q.2, by
          have htpos : 0 < q.2 := Nat.pos_of_dvd_of_pos htn (Nat.div_pos (Nat.le_of_dvd (by omega) hkn) hpos)
          positivity⟩⟩, ?_⟩
      · have := Nat.mul_dvd_mul_left q.1 htn
        rwa [Nat.mul_div_cancel' hkn] at this
      · ext
        · rfl
        · exact heq_of_eq (Nat.mul_div_cancel_left q.2 hpos)
    · intro p _; ring
  rw [hswap, Finset.sum_eq_single n]
  · rw [Nat.div_self (by omega)]; simp
  · intro k hk hne
    have hkn := (Nat.mem_divisors.mp hk).1
    have hk_pos : 0 < k := Nat.pos_of_dvd_of_pos hkn (by omega)
    have hdiv_gt : n / k ≠ 1 := by
      intro h1
      have := Nat.mul_div_cancel' hkn
      rw [h1, mul_one] at this
      exact hne this
    have hmu0 : ∑ t ∈ Nat.divisors (n / k), (ArithmeticFunction.moebius t : ℤ) = 0 := by
      have h := congr_arg (fun f : ArithmeticFunction ℤ => f (n / k))
        ArithmeticFunction.moebius_mul_coe_zeta
      rw [ArithmeticFunction.mul_apply, ArithmeticFunction.one_apply, if_neg hdiv_gt] at h
      rw [← h, Nat.sum_divisorsAntidiagonal
        (fun x y => ArithmeticFunction.moebius x * ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℤ) y)]
      refine Finset.sum_congr rfl fun t ht => ?_
      have hdiv_pos : 0 < n / k := Nat.div_pos (Nat.le_of_dvd (by omega) hkn) hk_pos
      have ht_dvd := (Nat.mem_divisors.mp ht).1
      have ht_pos : 0 < t := Nat.pos_of_dvd_of_pos ht_dvd hdiv_pos
      have hq_pos : 0 < n / k / t := Nat.div_pos (Nat.le_of_dvd hdiv_pos ht_dvd) ht_pos
      simp [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply, hq_pos.ne']
    rw [hmu0, mul_zero]
  · intro h; exfalso; exact h (Nat.mem_divisors.mpr ⟨dvd_refl n, by omega⟩)


private lemma a166168Coeffs_eq_expLogCoeffs :
    ∀ n : ℕ, a166168Coeffs n = expLogCoeffs (fun m => lucas (m ^ 2)) n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => rw [a166168Coeffs, expLogCoeffs]
    | succ n =>
        rw [a166168Coeffs, expLogCoeffs]
        congr 1
        refine Finset.sum_congr rfl fun k _ => ?_
        have hlt : n - k.val < n + 1 := by omega
        rw [ih (n - k.val) hlt]

private def fibShift : ℕ → ℤ
  | 0 => 1
  | 1 => 1
  | n + 2 => fibShift (n + 1) + fibShift n

private lemma lucas_eq_fibShift :
    ∀ n : ℕ, lucas (n + 2) = fibShift (n + 1) + 2 * fibShift n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => decide
    | succ n =>
        cases n with
        | zero => decide
        | succ n =>
            rw [lucas, ih (n + 1) (by omega), ih n (by omega)]
            conv_rhs => rw [fibShift, fibShift]
            have hf : fibShift (n + 2) = fibShift (n + 1) + fibShift n := rfl
            linarith

private lemma isIntegerSeries_expLogSeries_lucas :
    isIntegerSeries (expLogSeries lucas) := by
  set G : PowerSeries ℚ := PowerSeries.mk fun n => (fibShift n : ℚ)
  have hG0 : PowerSeries.coeff 0 G = 1 := by
    simp [G, fibShift]
  have hG_inv : (1 - PowerSeries.X - PowerSeries.X ^ 2) * G = 1 := by
    apply PowerSeries.ext; intro n
    rw [sub_mul, sub_mul, one_mul, map_sub, map_sub, PowerSeries.coeff_one]
    cases n with
    | zero =>
        rw [PowerSeries.coeff_zero_X_mul, PowerSeries.coeff_X_pow_mul']
        simp [G, fibShift]
    | succ n =>
        cases n with
        | zero =>
            rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_X_pow_mul']
            simp [G, fibShift]
        | succ n =>
            rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_X_pow_mul']
            have hsub : n + 1 + 1 - 2 = n := by omega
            simp only [show 2 ≤ n + 2 by omega, Nat.succ_ne_zero, ↓reduceIte,
              hsub, G, PowerSeries.coeff_mk, fibShift, Int.cast_add]
            ring
  have hG_ode :
      PowerSeries.X * PowerSeries.derivative ℚ G =
        G * ((PowerSeries.X + PowerSeries.C 2 * PowerSeries.X ^ 2) * G) := by
    have hdiff := congr_arg (fun f => PowerSeries.X * PowerSeries.derivative ℚ f) hG_inv
    rw [Derivation.leibniz, Derivation.map_one_eq_zero, mul_zero, mul_add] at hdiff
    simp only [smul_eq_mul] at hdiff
    have hd_poly :
        PowerSeries.derivative ℚ (1 - PowerSeries.X - PowerSeries.X ^ 2) =
          -(1 + PowerSeries.C 2 * PowerSeries.X) := by
      rw [map_sub, map_sub, Derivation.map_one_eq_zero, PowerSeries.derivative_X,
          Derivation.leibniz_pow, PowerSeries.derivative_X, smul_eq_mul, mul_one, nsmul_eq_mul]
      have h2 : ((2 : ℕ) : PowerSeries ℚ) = PowerSeries.C 2 := by
        rw [show (2 : ℚ) = ((2 : ℕ) : ℚ) by norm_num, map_natCast]
      simp only [Nat.reduceSub, pow_one, h2]
      ring
    rw [hd_poly] at hdiff
    have h1 :
        (1 - PowerSeries.X - PowerSeries.X ^ 2) * (PowerSeries.X * PowerSeries.derivative ℚ G) =
          (PowerSeries.X + PowerSeries.C 2 * PowerSeries.X ^ 2) * G := by
      linear_combination hdiff
    calc
      PowerSeries.X * PowerSeries.derivative ℚ G
        = ((1 - PowerSeries.X - PowerSeries.X ^ 2) * G) *
            (PowerSeries.X * PowerSeries.derivative ℚ G) := by rw [hG_inv, one_mul]
      _ = G * ((1 - PowerSeries.X - PowerSeries.X ^ 2) *
            (PowerSeries.X * PowerSeries.derivative ℚ G)) := by ring
      _ = G * ((PowerSeries.X + PowerSeries.C 2 * PowerSeries.X ^ 2) * G) := by rw [h1]
  have hL_eq :
      (PowerSeries.X + PowerSeries.C 2 * PowerSeries.X ^ 2) * G =
        PowerSeries.mk fun n => if n = 0 then 0 else (lucas n : ℚ) := by
    apply PowerSeries.ext; intro n
    rw [add_mul, mul_assoc, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk]
    cases n with
    | zero =>
        rw [PowerSeries.coeff_zero_X_mul, PowerSeries.coeff_X_pow_mul']
        simp
    | succ n =>
        cases n with
        | zero =>
            rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_X_pow_mul']
            simp [G, fibShift, lucas]
        | succ n =>
            rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_X_pow_mul']
            have hsub : n + 1 + 1 - 2 = n := by omega
            simp only [show 2 ≤ n + 2 by omega, Nat.succ_ne_zero, ↓reduceIte,
              hsub, G, PowerSeries.coeff_mk]
            exact_mod_cast (lucas_eq_fibShift n).symm
  have hG_eq : G = expLogSeries lucas :=
    eq_expLogSeries_of_ode lucas G hG0 (by rw [← hL_eq]; exact hG_ode)
  rw [← hG_eq]
  intro n
  exact ⟨fibShift n, by simp [G]⟩

theorem main_proof :
    ∀ n : ℕ, ∃ z : ℤ, a166168Coeffs n = (z : ℚ) := by
  obtain ⟨M, hM⟩ := exists_euler_decomp_of_isIntegerSeries lucas isIntegerSeries_expLogSeries_lucas
  have hlucas_cong : ∀ {p r m : ℕ}, p.Prime → 1 ≤ r → 1 ≤ m → ¬ p ∣ m →
      ((p ^ r : ℕ) : ℤ) ∣ (lucas (p ^ r * m) - lucas (p ^ (r - 1) * m)) :=
    fun hp hr hm hpm => gauss_cong_of_euler_decomp lucas M hM hp hr hm hpm
  have hsq_int : isIntegerSeries (expLogSeries fun n => lucas (n ^ 2)) := by
    apply isIntegerSeries_of_gauss_cong (fun n => lucas (n ^ 2))
    intro p r m hp hr hm hpm
    have hm2 : 1 ≤ m ^ 2 := by nlinarith
    have hpm2 : ¬ p ∣ m ^ 2 := fun h => hpm (hp.dvd_of_dvd_pow h)
    have h1 := hlucas_cong hp (show 1 ≤ 2 * r by omega) hm2 hpm2
    have h2 := hlucas_cong hp (show 1 ≤ 2 * r - 1 by omega) hm2 hpm2
    have h1' : ((p ^ r : ℕ) : ℤ) ∣
        (lucas (p ^ (2 * r) * m ^ 2) - lucas (p ^ (2 * r - 1) * m ^ 2)) :=
      dvd_trans (Int.natCast_dvd_natCast.mpr (Nat.pow_dvd_pow p (by omega))) h1
    have h2' : ((p ^ r : ℕ) : ℤ) ∣
        (lucas (p ^ (2 * r - 1) * m ^ 2) - lucas (p ^ (2 * r - 1 - 1) * m ^ 2)) :=
      dvd_trans (Int.natCast_dvd_natCast.mpr (Nat.pow_dvd_pow p (by omega))) h2
    have hadd := dvd_add h1' h2'
    have hEq1 : (p ^ r * m) ^ 2 = p ^ (2 * r) * m ^ 2 := by
      rw [mul_pow, ← pow_mul, mul_comm r 2]
    have hEq2 : (p ^ (r - 1) * m) ^ 2 = p ^ (2 * r - 1 - 1) * m ^ 2 := by
      rw [mul_pow, ← pow_mul]
      congr 2; omega
    rw [hEq1, hEq2]
    simpa [sub_add_sub_cancel] using hadd
  intro n
  rw [a166168Coeffs_eq_expLogCoeffs n]
  simpa [expLogSeries] using hsq_int n

end OMA.S_oeis_a166168

theorem OMA.solution : type_of% @OMA.S_oeis_a166168.main :=
  OMA.S_oeis_a166168.main_proof
