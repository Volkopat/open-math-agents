import OMAStatements.S_oeis_a167894
import Mathlib

namespace OMA.S_oeis_a167894

open PowerSeries BigOperators

/-- Rising factorial `(k)_n = k * (k + 1) * ... * (k + n - 1)` in `ℚ`. -/
private def risingFact (k : ℕ) : ℕ → ℚ
  | 0 => 1
  | n + 1 => risingFact k n * ((k + n : ℕ) : ℚ)

private lemma mul_risingFact_succ (k : ℕ) :
    ∀ n : ℕ, (k : ℚ) * risingFact (k + 1) n = risingFact k (n + 1)
  | 0 => by simp [risingFact]
  | n + 1 => by
      simp only [risingFact]
      rw [← mul_assoc, mul_risingFact_succ k n]
      congr 1
      push_cast
      ring

private lemma risingFact_zero_succ (n : ℕ) : risingFact 0 (n + 1) = 0 := by
  rw [← mul_risingFact_succ 0 n, Nat.cast_zero, zero_mul]

private lemma risingFact_one : ∀ n : ℕ, risingFact 1 n = (Nat.factorial n : ℚ)
  | 0 => by simp [risingFact]
  | n + 1 => by
      simp only [risingFact, risingFact_one n, Nat.factorial_succ]
      push_cast
      ring

/-- Formal power series `B_k(x) = ∑_{n ≥ 0} (k)_n * x^n`. -/
private noncomputable def seriesB (k : ℕ) : PowerSeries ℚ :=
  PowerSeries.mk fun n => risingFact k n

private lemma coeff_zero_seriesB (k : ℕ) : PowerSeries.coeff 0 (seriesB k) = 1 := by
  simp [seriesB, risingFact]

private lemma constantCoeff_seriesB (k : ℕ) : PowerSeries.constantCoeff (seriesB k) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff, coeff_zero_seriesB]

private lemma seriesB_zero : seriesB 0 = 1 := by
  apply PowerSeries.ext; intro n
  cases n with
  | zero => simp [seriesB, risingFact]
  | succ n => simp [seriesB, risingFact_zero_succ]

private lemma seriesB_one : seriesB 1 = factorialSeries := by
  apply PowerSeries.ext; intro n
  simp [seriesB, factorialSeries, risingFact_one]

/-- Three-term linear recurrence for `B_k`:
`B_k = (1 + k * x) * B_{k+1} - (k + 1) * x * B_{k+2}`. -/
private lemma seriesB_rec (k : ℕ) :
    seriesB k =
      (1 + PowerSeries.C (k : ℚ) * PowerSeries.X) * seriesB (k + 1) -
      PowerSeries.C ((k + 1 : ℕ) : ℚ) * PowerSeries.X * seriesB (k + 2) := by
  apply PowerSeries.ext; intro n
  rw [map_sub, add_mul, one_mul, map_add, mul_assoc (PowerSeries.C (k : ℚ)),
      PowerSeries.coeff_C_mul, mul_assoc (PowerSeries.C ((k + 1 : ℕ) : ℚ)),
      PowerSeries.coeff_C_mul]
  cases n with
  | zero =>
      rw [PowerSeries.coeff_zero_X_mul, PowerSeries.coeff_zero_X_mul]
      simp [coeff_zero_seriesB]
  | succ n =>
      rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_succ_X_mul]
      simp only [seriesB, PowerSeries.coeff_mk]
      rw [mul_risingFact_succ k n, mul_risingFact_succ (k + 1) n]
      ring

private lemma seriesB_mul_inv (k : ℕ) : seriesB k * (seriesB k)⁻¹ = 1 :=
  PowerSeries.mul_inv_cancel (seriesB k) (by rw [constantCoeff_seriesB]; exact one_ne_zero)

private lemma inv_mul_seriesB (k : ℕ) : (seriesB k)⁻¹ * seriesB k = 1 := by
  rw [mul_comm]; exact seriesB_mul_inv k

/-- Exact continued fraction tail `Q_k = B_k * B_{k+1}⁻¹`. -/
private noncomputable def seriesQ (k : ℕ) : PowerSeries ℚ :=
  seriesB k * (seriesB (k + 1))⁻¹

private lemma constantCoeff_seriesQ (k : ℕ) : PowerSeries.constantCoeff (seriesQ k) = 1 := by
  have h : seriesQ k * seriesB (k + 1) = seriesB k := by
    rw [seriesQ, mul_assoc, inv_mul_seriesB, mul_one]
  have hc := congr_arg PowerSeries.constantCoeff h
  rw [map_mul, constantCoeff_seriesB, constantCoeff_seriesB, mul_one] at hc
  exact hc

private lemma seriesQ_zero : seriesQ 0 = a167894Series := by
  rw [seriesQ, seriesB_zero, one_mul, seriesB_one, a167894Series]

private lemma seriesQ_inv (k : ℕ) : (seriesQ k)⁻¹ = seriesB (k + 1) * (seriesB k)⁻¹ := by
  have hmul : seriesQ k * (seriesB (k + 1) * (seriesB k)⁻¹) = 1 := by
    rw [seriesQ]
    calc
      seriesB k * (seriesB (k + 1))⁻¹ * (seriesB (k + 1) * (seriesB k)⁻¹)
        = seriesB k * ((seriesB (k + 1))⁻¹ * seriesB (k + 1)) * (seriesB k)⁻¹ := by ring
      _ = seriesB k * (seriesB k)⁻¹ := by rw [inv_mul_seriesB, mul_one]
      _ = 1 := seriesB_mul_inv k
  have hQinv : (seriesQ k)⁻¹ * seriesQ k = 1 := by
    rw [mul_comm]
    exact PowerSeries.mul_inv_cancel (seriesQ k) (by rw [constantCoeff_seriesQ]; exact one_ne_zero)
  calc
    (seriesQ k)⁻¹ = (seriesQ k)⁻¹ * (seriesQ k * (seriesB (k + 1) * (seriesB k)⁻¹)) := by
      rw [hmul, mul_one]
    _ = ((seriesQ k)⁻¹ * seriesQ k) * (seriesB (k + 1) * (seriesB k)⁻¹) := by ring
    _ = seriesB (k + 1) * (seriesB k)⁻¹ := by rw [hQinv, one_mul]

private lemma seriesQ_rec (k : ℕ) :
    seriesQ k =
      1 + PowerSeries.C (k : ℚ) * PowerSeries.X -
        PowerSeries.C ((k + 1 : ℕ) : ℚ) * PowerSeries.X * (seriesQ (k + 1))⁻¹ := by
  have h := congr_arg (· * (seriesB (k + 1))⁻¹) (seriesB_rec k)
  rw [sub_mul, mul_assoc (1 + PowerSeries.C (k : ℚ) * PowerSeries.X), seriesB_mul_inv, mul_one] at h
  rw [seriesQ_inv (k + 1)]
  calc
    seriesQ k = seriesB k * (seriesB (k + 1))⁻¹ := rfl
    _ = 1 + PowerSeries.C (k : ℚ) * PowerSeries.X -
          PowerSeries.C ((k + 1 : ℕ) : ℚ) * PowerSeries.X * seriesB (k + 2) * (seriesB (k + 1))⁻¹ := h
    _ = 1 + PowerSeries.C (k : ℚ) * PowerSeries.X -
          PowerSeries.C ((k + 1 : ℕ) : ℚ) * PowerSeries.X * (seriesB (k + 2) * (seriesB (k + 1))⁻¹) := by
          ring

private lemma constantCoeff_cfConv : ∀ (d k : ℕ), PowerSeries.constantCoeff (cfConv k d) = 1
  | 0, k => by simp [cfConv]
  | d + 1, k => by
      simp [cfConv]

/-- If two power series with constant term `1` agree on coefficients `≤ m`,
so do their inverses! -/
private lemma coeff_inv_congr {f g : PowerSeries ℚ}
    (hf : PowerSeries.constantCoeff f = 1) (hg : PowerSeries.constantCoeff g = 1) :
    ∀ m : ℕ, (∀ n ≤ m, PowerSeries.coeff n f = PowerSeries.coeff n g) →
      ∀ n ≤ m, PowerSeries.coeff n f⁻¹ = PowerSeries.coeff n g⁻¹ := by
  intro m hfg n hn
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hf_inv : f * f⁻¹ = 1 := PowerSeries.mul_inv_cancel f (by rw [hf]; exact one_ne_zero)
    have hg_inv : g * g⁻¹ = 1 := PowerSeries.mul_inv_cancel g (by rw [hg]; exact one_ne_zero)
    have hfn := congr_arg (PowerSeries.coeff n) hf_inv
    have hgn := congr_arg (PowerSeries.coeff n) hg_inv
    rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => PowerSeries.coeff i f * PowerSeries.coeff j f⁻¹)] at hfn
    rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => PowerSeries.coeff i g * PowerSeries.coeff j g⁻¹)] at hgn
    have heq :
        ∑ k ∈ Finset.range (n + 1), PowerSeries.coeff k f * PowerSeries.coeff (n - k) f⁻¹ =
        ∑ k ∈ Finset.range (n + 1), PowerSeries.coeff k g * PowerSeries.coeff (n - k) g⁻¹ :=
      hfn.trans hgn.symm
    rw [Finset.sum_range_succ', Finset.sum_range_succ'] at heq
    have htail :
        ∑ k ∈ Finset.range n, PowerSeries.coeff (k + 1) f * PowerSeries.coeff (n - (k + 1)) f⁻¹ =
        ∑ k ∈ Finset.range n, PowerSeries.coeff (k + 1) g * PowerSeries.coeff (n - (k + 1)) g⁻¹ := by
      refine Finset.sum_congr rfl fun k hk => ?_
      have hkl : k < n := Finset.mem_range.mp hk
      rw [hfg (k + 1) (by omega), ih (n - (k + 1)) (by omega) (by omega)]
    rw [htail, Nat.sub_zero, PowerSeries.coeff_zero_eq_constantCoeff,
        hf, hg, one_mul, one_mul] at heq
    linarith

/-- Convergents `cfConv k d` agree with `seriesQ k` on all coefficients `n ≤ d`. -/
private lemma coeff_cfConv_eq_seriesQ :
    ∀ (d k n : ℕ), n ≤ d → PowerSeries.coeff n (cfConv k d) = PowerSeries.coeff n (seriesQ k)
  | 0, k, n, hn => by
      have hn0 : n = 0 := by omega
      subst hn0
      rw [PowerSeries.coeff_zero_eq_constantCoeff, constantCoeff_cfConv, constantCoeff_seriesQ]
  | d + 1, k, n, hn => by
      rw [cfConv, seriesQ_rec k]
      cases n with
      | zero =>
          simp [PowerSeries.coeff_zero_eq_constantCoeff, constantCoeff_cfConv, constantCoeff_seriesQ]
      | succ n =>
          rw [map_sub, map_sub, mul_assoc (PowerSeries.C ((k + 1 : ℕ) : ℚ)),
              mul_assoc (PowerSeries.C ((k + 1 : ℕ) : ℚ)),
              PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul,
              PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_succ_X_mul]
          congr 2
          exact coeff_inv_congr (constantCoeff_cfConv d (k + 1)) (constantCoeff_seriesQ (k + 1))
            d (fun j hj => coeff_cfConv_eq_seriesQ d (k + 1) j hj) n (by omega)

theorem main_proof :
    (∃ Q : ℕ → PowerSeries ℚ,
      Q 0 = a167894Series ∧
      ∀ k : ℕ,
        PowerSeries.constantCoeff (Q k) = 1 ∧
        Q k = 1 + PowerSeries.C (k : ℚ) * PowerSeries.X -
          PowerSeries.C ((k + 1 : ℕ) : ℚ) * PowerSeries.X * (Q (k + 1))⁻¹) ∧
    (∀ d n : ℕ, n ≤ d → PowerSeries.coeff n (cfConv 0 d) = PowerSeries.coeff n a167894Series) := by
  refine ⟨⟨seriesQ, seriesQ_zero, fun k => ⟨constantCoeff_seriesQ k, seriesQ_rec k⟩⟩, ?_⟩
  intro d n hn
  rw [coeff_cfConv_eq_seriesQ d 0 n hn, seriesQ_zero]

end OMA.S_oeis_a167894

theorem OMA.solution : type_of% @OMA.S_oeis_a167894.main :=
  OMA.S_oeis_a167894.main_proof
