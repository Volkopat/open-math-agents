import OMAStatements.S_oeis_a292395
import Mathlib

namespace OMA.S_oeis_a292395

open PowerSeries BigOperators

/-- Derivative identity for integer power series: `k ∣ n * [X^n] B^k` in `ℤ`. -/
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

/-- Key number-theoretic lemma: if `k + m = N` with `k, m ≥ 1`, `k^2 ∣ a`, and `N^2 ∣ m * c`,
then `N^2 ∣ a * c`. -/
private lemma sq_dvd_mul_of_add {N k m : ℕ} {a c : ℤ}
    (hk : 1 ≤ k) (hm : 1 ≤ m) (hkm : k + m = N)
    (ha : ((k ^ 2 : ℕ) : ℤ) ∣ a)
    (hc : ((N ^ 2 : ℕ) : ℤ) ∣ (m : ℤ) * c) :
    ((N ^ 2 : ℕ) : ℤ) ∣ a * c := by
  rw [Int.natCast_dvd] at ha hc ⊢
  rw [Int.natAbs_mul, Int.natAbs_natCast] at hc
  rw [Int.natAbs_mul]
  by_cases ha0 : a.natAbs = 0
  · rw [ha0, zero_mul]; exact dvd_zero _
  by_cases hc0 : c.natAbs = 0
  · rw [hc0, mul_zero]; exact dvd_zero _
  have hN0 : N ≠ 0 := by omega
  have hk0 : k ≠ 0 := by omega
  have hm0 : m ≠ 0 := by omega
  have hac0 : a.natAbs * c.natAbs ≠ 0 := mul_ne_zero ha0 hc0
  rw [← Nat.factorization_le_iff_dvd (pow_ne_zero 2 hN0) hac0]
  intro p
  by_cases hp : p.Prime
  · have hfa : (k ^ 2).factorization p ≤ a.natAbs.factorization p :=
      (Nat.factorization_le_iff_dvd (pow_ne_zero 2 hk0) ha0).mpr ha p
    have hfc : (N ^ 2).factorization p ≤ (m * c.natAbs).factorization p :=
      (Nat.factorization_le_iff_dvd (pow_ne_zero 2 hN0) (mul_ne_zero hm0 hc0)).mpr hc p
    rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul] at hfa hfc ⊢
    rw [Nat.factorization_mul hm0 hc0, Finsupp.add_apply] at hfc
    rw [Nat.factorization_mul ha0 hc0, Finsupp.add_apply]
    by_cases hle : N.factorization p ≤ k.factorization p
    · omega
    · have hmk : m.factorization p ≤ k.factorization p := by
        by_contra hlt
        push Not at hlt
        have hdvd_m : p ^ (k.factorization p + 1) ∣ m :=
          (hp.pow_dvd_iff_le_factorization hm0).mpr (by omega)
        have hdvd_N : p ^ (k.factorization p + 1) ∣ N :=
          (hp.pow_dvd_iff_le_factorization hN0).mpr (by omega)
        have hdvd_k : p ^ (k.factorization p + 1) ∣ k := by
          have hsub := Nat.dvd_sub hdvd_N hdvd_m
          rwa [show N - m = k by omega] at hsub
        have hbad := (hp.pow_dvd_iff_le_factorization hk0).mp hdvd_k
        omega
      omega
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

/-- Coefficient of `X^n` in `C a * (X * F)^k`: equals `a * [X^(n - k)] (F ^ k)` when `k ≤ n`,
and `0` when `k > n`. -/
private lemma coeff_C_mul_X_mul_pow (a : ℚ) (F : PowerSeries ℚ) (k n : ℕ) (hk : k ≤ n) :
    PowerSeries.coeff n (PowerSeries.C a * (PowerSeries.X * F) ^ k) =
      a * PowerSeries.coeff (n - k) (F ^ k) := by
  rw [PowerSeries.coeff_C_mul, mul_pow, PowerSeries.coeff_X_pow_mul', if_pos hk]

theorem main_proof :
    ∀ A invA : PowerSeries ℚ,
      A * invA = 1 →
      PowerSeries.coeff 0 A = 1 →
      PowerSeries.coeff 1 A = 1 →
      (∀ n : ℕ, 2 ≤ n →
        PowerSeries.coeff n (∑ k ∈ Finset.range (n + 1),
          PowerSeries.C (PowerSeries.coeff k A) * (PowerSeries.X * invA ^ (n ^ 2)) ^ k) = 0) →
      ∀ n : ℕ, 1 ≤ n → ∃ z : ℤ, PowerSeries.coeff n A / ((n ^ 2 : ℕ) : ℚ) = (z : ℚ) := by
  intro A invA hAinv hA0 hA1 hEq
  have hinvA0 : PowerSeries.coeff 0 invA = 1 := by
    have h0 := congrArg (PowerSeries.coeff 0) hAinv
    rw [PowerSeries.coeff_mul, Finset.Nat.antidiagonal_zero, Finset.sum_singleton,
        hA0, one_mul, PowerSeries.coeff_one, if_pos rfl] at h0
    exact h0
  have hmain : ∀ n : ℕ, ∃ z : ℤ, PowerSeries.coeff n A = (z : ℚ) ∧
      (1 ≤ n → ((n ^ 2 : ℕ) : ℤ) ∣ z) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h N ih =>
      by_cases hN0 : N = 0
      · subst hN0; exact ⟨1, by simp [hA0], fun h => by omega⟩
      by_cases hN1 : N = 1
      · subst hN1; exact ⟨1, by simp [hA1], fun _ => by norm_num⟩
      have hN2 : 2 ≤ N := by omega
      -- Lift the first `N` coefficients of `A` to an integer power series `B` with `B(0) = 1`.
      have hA_int' : ∀ j, ∃ z : ℤ, j < N → PowerSeries.coeff j A = (z : ℚ) := fun j =>
        if h : j < N then let ⟨z, hz, _⟩ := ih j h; ⟨z, fun _ => hz⟩ else ⟨0, fun h' => absurd h' h⟩
      choose z_prev hz_prev using hA_int'
      set B : PowerSeries ℤ := PowerSeries.mk fun j => if j < N then z_prev j else 0
      have hB0 : PowerSeries.coeff 0 B = 1 := by
        have h0 : ((PowerSeries.coeff 0 B : ℤ) : ℚ) = 1 := by
          have : PowerSeries.coeff 0 B = z_prev 0 := by simp [B, show 0 < N by omega]
          rw [this, ← hz_prev 0 (by omega), hA0]
        exact_mod_cast h0
      have hB_unit : IsUnit B := by
        rw [PowerSeries.isUnit_iff_constantCoeff, ← PowerSeries.coeff_zero_eq_constantCoeff, hB0]
        exact isUnit_one
      obtain ⟨uB, huB⟩ := hB_unit
      set Binv : PowerSeries ℤ := ((uB⁻¹ : (PowerSeries ℤ)ˣ) : PowerSeries ℤ)
      have hBBinv : B * Binv = 1 := by
        rw [← huB]
        exact Units.mul_inv uB
      have hB_agree : ∀ j < N, PowerSeries.coeff j A = ((PowerSeries.coeff j B : ℤ) : ℚ) := by
        intro j hj
        simp only [B, PowerSeries.coeff_mk, hj, ↓reduceIte]
        exact hz_prev j hj
      -- `invA` agrees with `Binv` on all coefficients `j < N`!
      have hBinv_agree : ∀ j < N, PowerSeries.coeff j invA = ((PowerSeries.coeff j Binv : ℤ) : ℚ) := by
        intro j
        induction j using Nat.strong_induction_on with
        | h m ihm =>
          intro hm
          by_cases hm0 : m = 0
          · subst hm0
            have h0 := congrArg (PowerSeries.coeff 0) hBBinv
            rw [PowerSeries.coeff_mul, Finset.Nat.antidiagonal_zero, Finset.sum_singleton,
                hB0, one_mul, PowerSeries.coeff_one, if_pos rfl] at h0
            rw [hinvA0, h0]; simp
          · have h1 := congrArg (PowerSeries.coeff m) hAinv
            have h2 := congrArg (PowerSeries.coeff m) hBBinv
            rw [PowerSeries.coeff_one, if_neg hm0, PowerSeries.coeff_mul,
                Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a b => PowerSeries.coeff a A * PowerSeries.coeff b invA),
                Finset.sum_range_succ'] at h1
            rw [PowerSeries.coeff_one, if_neg hm0, PowerSeries.coeff_mul,
                Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a b => PowerSeries.coeff a B * PowerSeries.coeff b Binv),
                Finset.sum_range_succ'] at h2
            simp only [Nat.sub_zero, hA0, one_mul] at h1
            simp only [Nat.sub_zero, hB0, one_mul] at h2
            have h2q : (∑ k ∈ Finset.range m,
                ((PowerSeries.coeff (k + 1) B : ℤ) : ℚ) * ((PowerSeries.coeff (m - (k + 1)) Binv : ℤ) : ℚ)) +
                ((PowerSeries.coeff m Binv : ℤ) : ℚ) = 0 := by
              exact_mod_cast h2
            have hsum_eq : ∑ k ∈ Finset.range m, PowerSeries.coeff (k + 1) A * PowerSeries.coeff (m - (k + 1)) invA =
                ∑ k ∈ Finset.range m, ((PowerSeries.coeff (k + 1) B : ℤ) : ℚ) * ((PowerSeries.coeff (m - (k + 1)) Binv : ℤ) : ℚ) := by
              refine Finset.sum_congr rfl fun k hk => ?_
              have hkm : k < m := Finset.mem_range.mp hk
              rw [hB_agree (k + 1) (by omega), ihm (m - (k + 1)) (by omega) (by omega)]
            rw [hsum_eq] at h1
            linarith
      -- Hence `invA ^ e` agrees with `Binv ^ e` on all coefficients `j < N`!
      have hBinv_pow : ∀ e j, j < N → PowerSeries.coeff j (invA ^ e) = ((PowerSeries.coeff j (Binv ^ e) : ℤ) : ℚ) := by
        intro e
        induction e with
        | zero =>
            intro j _
            rw [pow_zero, pow_zero, PowerSeries.coeff_one, PowerSeries.coeff_one]
            split_ifs <;> simp
        | succ e ihe =>
            intro j hj
            rw [pow_succ, pow_succ, PowerSeries.coeff_mul, PowerSeries.coeff_mul,
                Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a b => PowerSeries.coeff a (invA ^ e) * PowerSeries.coeff b invA),
                Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a b => PowerSeries.coeff a (Binv ^ e) * PowerSeries.coeff b Binv)]
            push_cast
            refine Finset.sum_congr rfl fun a ha => ?_
            have haj : a ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
            rw [ihe a (by omega), hBinv_agree (j - a) (by omega)]
      -- Extract `coeff N A` from `hEq N hN2`!
      have h0 := hEq N hN2
      rw [map_sum, Finset.sum_range_succ] at h0
      rw [show Finset.range N = Finset.range ((N - 1) + 1) by congr 1; omega,
          Finset.sum_range_succ'] at h0
      rw [coeff_C_mul_X_mul_pow _ _ N N (le_refl N), Nat.sub_self,
          PowerSeries.coeff_zero_eq_constantCoeff, map_pow, map_pow,
          ← PowerSeries.coeff_zero_eq_constantCoeff, hinvA0, one_pow, one_pow, mul_one] at h0
      rw [coeff_C_mul_X_mul_pow _ _ 0 N (Nat.zero_le N), Nat.sub_zero, pow_zero,
          PowerSeries.coeff_one, if_neg (by omega), mul_zero, add_zero] at h0
      -- Rewrite the inner sum over `k ∈ Finset.Icc 1 (N - 1)` using `Binv`!
      have hinner : ∑ x ∈ Finset.range (N - 1),
          PowerSeries.coeff N (PowerSeries.C (PowerSeries.coeff (x + 1) A) * (PowerSeries.X * invA ^ N ^ 2) ^ (x + 1)) =
          ∑ k ∈ Finset.Icc 1 (N - 1),
            ((z_prev k * PowerSeries.coeff (N - k) ((Binv ^ k) ^ (N ^ 2)) : ℤ) : ℚ) := by
        refine Finset.sum_nbij (fun x => x + 1) ?_ ?_ ?_ ?_
        · intro x hx; simp only [Finset.mem_range, Finset.mem_Icc] at hx ⊢; omega
        · intro a _ b _ hab; dsimp only at hab; omega
        · intro k hk; simp only [Finset.mem_coe, Finset.mem_Icc] at hk
          exact ⟨k - 1, Finset.mem_coe.mpr (Finset.mem_range.mpr (by omega)), by dsimp only; omega⟩
        · intro x hx
          have hxk : x + 1 < N := by simp only [Finset.mem_range] at hx; omega
          rw [coeff_C_mul_X_mul_pow _ _ (x + 1) N (by omega), ← pow_mul,
              hBinv_pow (N ^ 2 * (x + 1)) (N - (x + 1)) (by omega)]
          rw [hz_prev (x + 1) hxk, mul_comm (N ^ 2) (x + 1), pow_mul]
          push_cast; rfl
      rw [hinner] at h0
      refine ⟨-(∑ k ∈ Finset.Icc 1 (N - 1), z_prev k * PowerSeries.coeff (N - k) ((Binv ^ k) ^ (N ^ 2))), ?_, ?_⟩
      · push_cast at h0 ⊢; linarith
      · intro _
        refine dvd_neg.mpr (Finset.dvd_sum fun k hk => ?_)
        have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
        have hkN : k < N := by have := (Finset.mem_Icc.mp hk).2; omega
        have hzk_dvd : ((k ^ 2 : ℕ) : ℤ) ∣ z_prev k := by
          obtain ⟨zk, hzk_eq, hzk_d⟩ := ih k hkN
          have hEqz : z_prev k = zk := by exact_mod_cast ((hz_prev k hkN).symm.trans hzk_eq)
          rw [hEqz]
          exact hzk_d hk1
        have hpow_dvd : ((N ^ 2 : ℕ) : ℤ) ∣ ((N - k : ℕ) : ℤ) * PowerSeries.coeff (N - k) ((Binv ^ k) ^ (N ^ 2)) :=
          dvd_mul_coeff_pow_int (Binv ^ k) (N ^ 2) (N - k) (by nlinarith) (by omega)
        exact sq_dvd_mul_of_add hk1 (by omega : 1 ≤ N - k) (by omega : k + (N - k) = N) hzk_dvd hpow_dvd
  intro n hn
  obtain ⟨z, hz, hdvd⟩ := hmain n
  obtain ⟨q, hq⟩ := hdvd hn
  refine ⟨q, ?_⟩
  rw [hz, hq]
  have hn0 : ((n ^ 2 : ℕ) : ℚ) ≠ 0 := by positivity
  push_cast; field_simp [hn0]

end OMA.S_oeis_a292395

theorem OMA.solution : type_of% @OMA.S_oeis_a292395.main :=
  OMA.S_oeis_a292395.main_proof
