import OMAStatements.S_oeis_a350410
import Mathlib

namespace OMA.S_oeis_a350410

open PowerSeries BigOperators

/-- Telescoping identity: `∑_{m=1}^M (-1)^(m^2 - 1) * m^2 / m! = (-1)^(M - 1) / (M - 1)!` for `M ≥ 1`. -/
private lemma sum_telescoping (M : ℕ) (hM : 1 ≤ M) :
    ∑ m ∈ Finset.Icc 1 M, ((-1 : ℚ) ^ (m ^ 2 - 1) * ((m ^ 2 : ℕ) : ℚ)) / ((Nat.factorial m : ℕ) : ℚ) =
      (-1 : ℚ) ^ (M - 1) / ((Nat.factorial (M - 1) : ℕ) : ℚ) := by
  induction M with
  | zero => omega
  | succ M ih =>
      cases M with
      | zero => simp
      | succ M =>
          have hIcc : Finset.Icc 1 (M + 2) = insert (M + 2) (Finset.Icc 1 (M + 1)) := by
            ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
          have hnot : M + 2 ∉ Finset.Icc 1 (M + 1) := by simp
          rw [hIcc, Finset.sum_insert hnot, ih (by omega)]
          simp only [Nat.add_sub_cancel]
          have hpar : ∀ k : ℕ, (-1 : ℚ) ^ (k ^ 2 - 1) = (-1 : ℚ) ^ (k - 1) := by
            intro k
            cases k with
            | zero => simp
            | succ k =>
                have heven : Even ((k + 1) ^ 2 - 1 - k) := by
                  have hsub : (k + 1) ^ 2 - 1 - k = k * (k + 1) := by
                    have : (k + 1) ^ 2 = k * (k + 1) + k + 1 := by ring
                    omega
                  rw [hsub]
                  exact Nat.even_mul_succ_self k
                have hle : k ≤ (k + 1) ^ 2 - 1 := by
                  have h1 : k + 1 ≤ (k + 1) ^ 2 := Nat.le_self_pow (by norm_num) (k + 1)
                  omega
                rw [show (k + 1) ^ 2 - 1 = k + ((k + 1) ^ 2 - 1 - k) by omega,
                    Nat.add_sub_cancel, pow_add, Even.neg_one_pow heven, mul_one]
          rw [hpar (M + 2), show M + 2 - 1 = M + 1 by omega]
          have hf1 : ((Nat.factorial (M + 2) : ℕ) : ℚ) =
              ((M + 2 : ℕ) : ℚ) * ((M + 1 : ℕ) : ℚ) * ((Nat.factorial M : ℕ) : ℚ) := by
            rw [Nat.factorial_succ, Nat.factorial_succ]; push_cast; ring
          have hf2 : ((Nat.factorial (M + 1) : ℕ) : ℚ) =
              ((M + 1 : ℕ) : ℚ) * ((Nat.factorial M : ℕ) : ℚ) := by
            rw [Nat.factorial_succ]; push_cast; ring
          have hfm : ((Nat.factorial M : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero M)
          have hm1 : ((M + 1 : ℕ) : ℚ) ≠ 0 := by positivity
          have hm2 : ((M + 2 : ℕ) : ℚ) ≠ 0 := by positivity
          rw [hf1, hf2, pow_succ (-1 : ℚ) M]
          push_cast
          field_simp [hfm, hm1, hm2]
          ring

/-- Coefficient of `X^n` in `(P + a * X^n)^k` when `coeff 0 P = -1` and `n ≥ 1`:
equals `[X^n] P^k + k * (-1)^(k - 1) * a`. -/
private lemma coeff_add_monomial_pow (P : PowerSeries ℚ) (hP0 : PowerSeries.coeff 0 P = -1)
    (a : ℚ) (n : ℕ) (hn : 1 ≤ n) (k : ℕ) :
    PowerSeries.coeff n ((P + PowerSeries.C a * PowerSeries.X ^ n) ^ k) =
      PowerSeries.coeff n (P ^ k) + (k : ℚ) * (-1 : ℚ) ^ (k - 1) * a := by
  rw [add_pow, map_sum]
  cases k with
  | zero => simp
  | succ k =>
      -- Only `i = k + 1` (gives `P^(k+1)`) and `i = k` (gives `(k+1) * (-1)^k * a`) survive!
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      simp only [Nat.sub_self, pow_zero, mul_one, Nat.choose_self, Nat.cast_one,
        Nat.add_sub_cancel_left, pow_one, Nat.choose_succ_self_right, Nat.add_sub_cancel]
      have hrest : ∑ i ∈ Finset.range k, PowerSeries.coeff n
          (P ^ i * (PowerSeries.C a * PowerSeries.X ^ n) ^ (k + 1 - i) * (Nat.choose (k + 1) i : PowerSeries ℚ)) = 0 := by
        refine Finset.sum_eq_zero fun i hi => ?_
        have hik : i < k := Finset.mem_range.mp hi
        have hge2 : 2 ≤ k + 1 - i := by omega
        have hrew : P ^ i * (PowerSeries.C a * PowerSeries.X ^ n) ^ (k + 1 - i) * (Nat.choose (k + 1) i : PowerSeries ℚ) =
            PowerSeries.X ^ (n * (k + 1 - i)) *
              (P ^ i * PowerSeries.C (a ^ (k + 1 - i)) * (Nat.choose (k + 1) i : PowerSeries ℚ)) := by
          rw [mul_pow, ← pow_mul, ← map_pow]; ring
        rw [hrew, PowerSeries.coeff_X_pow_mul', if_neg (by nlinarith)]
      rw [hrest, zero_add, add_comm]
      congr 1
      have hrew : P ^ k * (PowerSeries.C a * PowerSeries.X ^ n) * ((k + 1 : ℕ) : PowerSeries ℚ) =
          PowerSeries.C (((k + 1 : ℕ) : ℚ) * a) * (PowerSeries.X ^ n * P ^ k) := by
        rw [show ((k + 1 : ℕ) : PowerSeries ℚ) = PowerSeries.C ((k + 1 : ℕ) : ℚ) by rw [map_natCast],
            map_mul]
        ring
      rw [hrew, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul', if_pos (le_refl n), Nat.sub_self,
          PowerSeries.coeff_zero_eq_constantCoeff, map_pow, ← PowerSeries.coeff_zero_eq_constantCoeff, hP0]
      ring

/-- Derivative identity for integer power series: `n * [X^n] B^k = k * [X^(n-1)] (B^(k-1) * B')`.
Hence `k ∣ n * [X^n] B^k` in `ℤ`! -/
private lemma dvd_mul_coeff_pow_int (B : PowerSeries ℤ) (k n : ℕ) (_hk : 1 ≤ k) (hn : 1 ≤ n) :
    (k : ℤ) ∣ (n : ℤ) * PowerSeries.coeff n (B ^ k) := by
  have hderiv : PowerSeries.derivative ℤ (B ^ k) =
      (k : PowerSeries ℤ) * B ^ (k - 1) * PowerSeries.derivative ℤ B := by
    rw [Derivation.leibniz_pow, nsmul_eq_mul, smul_eq_mul]; ring
  have hc := congrArg (PowerSeries.coeff (n - 1)) hderiv
  rw [PowerSeries.coeff_derivative, show n - 1 + 1 = n by omega,
      show (((n - 1 : ℕ) : ℤ) + 1) = (n : ℤ) by omega, mul_comm (PowerSeries.coeff n (B ^ k)),
      mul_assoc, show (k : PowerSeries ℤ) = PowerSeries.C (k : ℤ) by rw [map_natCast],
      PowerSeries.coeff_C_mul] at hc
  exact ⟨PowerSeries.coeff (n - 1) (B ^ (k - 1) * PowerSeries.derivative ℤ B), hc⟩

/-- Integer lifting: if `P : PowerSeries ℚ` has integer coefficients, then `P = B.map (Int.castRingHom ℚ)`
and `coeff m (P ^ k) = (coeff m (B ^ k) : ℚ)`. -/
private lemma coeff_pow_int_lift (P : PowerSeries ℚ)
    (hP : ∀ j, ∃ z : ℤ, PowerSeries.coeff j P = (z : ℚ)) :
    ∃ B : PowerSeries ℤ, ∀ k m, PowerSeries.coeff m (P ^ k) = ((PowerSeries.coeff m (B ^ k) : ℤ) : ℚ) := by
  choose z hz using hP
  refine ⟨PowerSeries.mk z, fun k m => ?_⟩
  have hPeq : P = (PowerSeries.mk z).map (Int.castRingHom ℚ) := by
    apply PowerSeries.ext; intro j
    rw [PowerSeries.coeff_map, PowerSeries.coeff_mk, Int.coe_castRingHom, hz j]
  rw [hPeq, ← map_pow, PowerSeries.coeff_map, Int.coe_castRingHom]

theorem main_proof :
    ∀ A : PowerSeries ℚ,
      PowerSeries.coeff 0 A = -1 →
      PowerSeries.coeff 1 A = 1 →
      (∀ n : ℕ, 2 ≤ n →
        PowerSeries.coeff n (∑ m ∈ Finset.range (n + 1),
          PowerSeries.C ((1 : ℚ) / ((Nat.factorial m : ℕ) : ℚ)) * A ^ (m ^ 2)) = 0) →
      ∀ n : ℕ, ∃ z : ℤ, PowerSeries.coeff n A = (z : ℚ) := by
  intro A hA0 hA1 hEq n
  induction n using Nat.strong_induction_on with
  | h N ih =>
    by_cases hN0 : N = 0
    · subst hN0; exact ⟨-1, by simp [hA0]⟩
    by_cases hN1 : N = 1
    · subst hN1; exact ⟨1, by simp [hA1]⟩
    have hN2 : 2 ≤ N := by omega
    set Aprev : PowerSeries ℚ := PowerSeries.mk fun j => if j < N then PowerSeries.coeff j A else 0
    have hAprev0 : PowerSeries.coeff 0 Aprev = -1 := by simp [Aprev, show 0 < N by omega, hA0]
    have hAprev_int : ∀ j, ∃ z : ℤ, PowerSeries.coeff j Aprev = (z : ℚ) := fun j => by
      rw [PowerSeries.coeff_mk]; split_ifs with hj
      · exact ih j hj
      · exact ⟨0, by simp⟩
    obtain ⟨B, hB⟩ := coeff_pow_int_lift Aprev hAprev_int
    have hA_agree : ∀ k : ℕ, PowerSeries.coeff N (A ^ k) =
        PowerSeries.coeff N ((Aprev + PowerSeries.C (PowerSeries.coeff N A) * PowerSeries.X ^ N) ^ k) := by
      intro k
      have hbase : ∀ j ≤ N, PowerSeries.coeff j A =
          PowerSeries.coeff j (Aprev + PowerSeries.C (PowerSeries.coeff N A) * PowerSeries.X ^ N) := by
        intro j hj
        rw [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
        simp only [Aprev, PowerSeries.coeff_mk]
        by_cases hjeq : j = N
        · subst hjeq; simp
        · rw [if_pos (by omega), if_neg hjeq, mul_zero, add_zero]
      have hpow : ∀ t r, r ≤ N → PowerSeries.coeff r (A ^ t) =
          PowerSeries.coeff r ((Aprev + PowerSeries.C (PowerSeries.coeff N A) * PowerSeries.X ^ N) ^ t) := by
        intro t; induction t with
        | zero => intro r _; rfl
        | succ t iht =>
            intro r hr
            rw [pow_succ, pow_succ, PowerSeries.coeff_mul, PowerSeries.coeff_mul,
                Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a b => PowerSeries.coeff a (A ^ t) * PowerSeries.coeff b A),
                Finset.Nat.sum_antidiagonal_eq_sum_range_succ
                  (fun a b => PowerSeries.coeff a ((Aprev + PowerSeries.C (PowerSeries.coeff N A) * PowerSeries.X ^ N) ^ t) *
                    PowerSeries.coeff b (Aprev + PowerSeries.C (PowerSeries.coeff N A) * PowerSeries.X ^ N))]
            refine Finset.sum_congr rfl fun a ha => ?_
            have har : a ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
            rw [iht a (by omega), hbase (r - a) (by omega)]
      exact hpow k N (le_refl N)
    have hrec : PowerSeries.coeff N A *
          (∑ m ∈ Finset.Icc 1 (N), ((-1 : ℚ) ^ (m ^ 2 - 1) * ((m ^ 2 : ℕ) : ℚ)) / ((Nat.factorial m : ℕ) : ℚ)) +
        (∑ m ∈ Finset.Icc 1 (N), PowerSeries.coeff N (Aprev ^ (m ^ 2)) / ((Nat.factorial m : ℕ) : ℚ)) = 0 := by
      have h0 := hEq N hN2
      simp only [map_sum, PowerSeries.coeff_C_mul] at h0
      rw [Finset.sum_range_succ'] at h0
      simp only [zero_pow (by norm_num : 2 ≠ 0), pow_zero, Nat.factorial_zero, Nat.cast_one, div_one,
        one_mul, PowerSeries.coeff_one, show N ≠ 0 by omega, ↓reduceIte, add_zero] at h0
      have hIcc : ∑ k ∈ Finset.range (N),
          (1 / ((Nat.factorial (k + 1) : ℕ) : ℚ)) * PowerSeries.coeff N (A ^ ((k + 1) ^ 2)) =
          ∑ m ∈ Finset.Icc 1 (N),
            (1 / ((Nat.factorial m : ℕ) : ℚ)) * PowerSeries.coeff N (A ^ (m ^ 2)) := by
        refine Finset.sum_nbij (fun k => k + 1) ?_ ?_ ?_ ?_
        · intro k hk; simp only [Finset.mem_range, Finset.mem_Icc] at hk ⊢; omega
        · intro a _ b _ hab; dsimp only at hab; omega
        · intro m hm; simp only [Finset.mem_coe, Finset.mem_Icc] at hm
          exact ⟨m - 1, Finset.mem_coe.mpr (Finset.mem_range.mpr (by omega)), by dsimp only; omega⟩
        · intro _ _; rfl
      rw [hIcc] at h0
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← h0]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [hA_agree (m ^ 2), coeff_add_monomial_pow Aprev hAprev0 (PowerSeries.coeff N A) N (by omega) (m ^ 2)]
      ring
    -- Last term `m = N`: `(N - 1)! / N! * [X^N] B^(N^2) = (1 / N) * [X^N] B^(N^2)`!
    have hdvd_last : (N : ℤ) ∣ PowerSeries.coeff N (B ^ (N ^ 2)) := by
      have h1 := dvd_mul_coeff_pow_int B (N ^ 2) N (by nlinarith) (by omega)
      have h1' : (N : ℤ) * (N : ℤ) ∣ (N : ℤ) * PowerSeries.coeff N (B ^ (N ^ 2)) := by
        convert h1 using 1; push_cast; ring
      have hN0 : (N : ℤ) ≠ 0 := by omega
      obtain ⟨c, hc⟩ := h1'
      exact ⟨c, mul_left_cancel₀ hN0 (by linarith)⟩
    obtain ⟨c_last, hc_last⟩ := hdvd_last
    have hsum_int : ∃ S : ℤ,
        ((Nat.factorial (N - 1) : ℕ) : ℚ) *
          ∑ m ∈ Finset.Icc 1 N, PowerSeries.coeff N (Aprev ^ (m ^ 2)) / ((Nat.factorial m : ℕ) : ℚ) = (S : ℚ) := by
      have hIcc : Finset.Icc 1 N = insert N (Finset.Icc 1 (N - 1)) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      have hnot : N ∉ Finset.Icc 1 (N - 1) := by simp; omega
      rw [hIcc, Finset.sum_insert hnot, mul_add, Finset.mul_sum]
      have hrest : ∀ m ∈ Finset.Icc 1 (N - 1),
          ∃ z : ℤ, ((Nat.factorial (N - 1) : ℕ) : ℚ) *
            (PowerSeries.coeff N (Aprev ^ (m ^ 2)) / ((Nat.factorial m : ℕ) : ℚ)) = (z : ℚ) := by
        intro m hm
        have hle : m ≤ N - 1 := (Finset.mem_Icc.mp hm).2
        obtain ⟨q, hq⟩ := Nat.factorial_dvd_factorial hle
        refine ⟨(q : ℤ) * PowerSeries.coeff N (B ^ (m ^ 2)), ?_⟩
        rw [hB (m ^ 2) N, hq]
        have hfm : ((Nat.factorial m : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
        push_cast; field_simp [hfm]
      choose z hz using fun m (hm : m ∈ Finset.Icc 1 (N - 1)) => hrest m hm
      refine ⟨c_last + ∑ m ∈ (Finset.Icc 1 (N - 1)).attach, z m.1 m.2, ?_⟩
      rw [← Finset.sum_attach (Finset.Icc 1 (N - 1))]
      push_cast
      congr 1
      · rw [hB (N ^ 2) N, hc_last]
        have hfac : ((Nat.factorial N : ℕ) : ℚ) = (N : ℚ) * ((Nat.factorial (N - 1) : ℕ) : ℚ) := by
          have : Nat.factorial N = N * Nat.factorial (N - 1) := by
            rw [show N = (N - 1) + 1 by omega, Nat.factorial_succ, show N - 1 + 1 = N by omega]
          exact_mod_cast this
        have hN0 : (N : ℚ) ≠ 0 := by positivity
        have hf0 : ((Nat.factorial (N - 1) : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
        rw [hfac]; push_cast; field_simp [hN0, hf0]
      · exact Finset.sum_congr rfl fun ⟨m, hm⟩ _ => hz m hm
    obtain ⟨S, hS⟩ := hsum_int
    refine ⟨(-1 : ℤ) ^ N * S, ?_⟩
    have hcoeff_eq := congrArg (fun z : ℚ => (-1 : ℚ) ^ N * ((Nat.factorial (N - 1) : ℕ) : ℚ) * z) hrec
    rw [mul_zero] at hcoeff_eq
    have hcoef := sum_telescoping N (by omega)
    rw [hcoef] at hcoeff_eq
    have hf0 : ((Nat.factorial (N - 1) : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hsign : (-1 : ℚ) ^ N * (-1 : ℚ) ^ (N - 1) = -1 := by
      rw [← pow_add, show N + (N - 1) = 2 * (N - 1) + 1 by omega, pow_succ,
          Even.neg_one_pow ⟨N - 1, by ring⟩]
      ring
    have h1 : (-1 : ℚ) ^ N * ((Nat.factorial (N - 1) : ℕ) : ℚ) *
        (PowerSeries.coeff N A * ((-1 : ℚ) ^ (N - 1) / ((Nat.factorial (N - 1) : ℕ) : ℚ))) =
        -PowerSeries.coeff N A := by
      have : ((Nat.factorial (N - 1) : ℕ) : ℚ) * ((-1 : ℚ) ^ (N - 1) / ((Nat.factorial (N - 1) : ℕ) : ℚ)) =
          (-1 : ℚ) ^ (N - 1) := by field_simp [hf0]
      calc (-1 : ℚ) ^ N * ((Nat.factorial (N - 1) : ℕ) : ℚ) *
            (PowerSeries.coeff N A * ((-1 : ℚ) ^ (N - 1) / ((Nat.factorial (N - 1) : ℕ) : ℚ)))
        _ = PowerSeries.coeff N A * ((-1 : ℚ) ^ N * (((Nat.factorial (N - 1) : ℕ) : ℚ) *
              ((-1 : ℚ) ^ (N - 1) / ((Nat.factorial (N - 1) : ℕ) : ℚ)))) := by ring
        _ = PowerSeries.coeff N A * ((-1 : ℚ) ^ N * (-1 : ℚ) ^ (N - 1)) := by rw [this]
        _ = -PowerSeries.coeff N A := by rw [hsign]; ring
    rw [mul_add, h1] at hcoeff_eq
    have h2 : (-1 : ℚ) ^ N * ((Nat.factorial (N - 1) : ℕ) : ℚ) *
        ∑ m ∈ Finset.Icc 1 N, PowerSeries.coeff N (Aprev ^ (m ^ 2)) / ((Nat.factorial m : ℕ) : ℚ) =
        ((-1 : ℤ) ^ N * S : ℤ) := by
      rw [mul_assoc, hS]; push_cast; ring
    linarith
end OMA.S_oeis_a350410

theorem OMA.solution : type_of% @OMA.S_oeis_a350410.main :=
  OMA.S_oeis_a350410.main_proof
