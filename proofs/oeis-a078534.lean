import OMAStatements.S_oeis_a078534
import Mathlib

namespace OMA.P_oeis_a078534

-- 1. Key derivative-vanishing lemma for Lagrange inversion (pure PowerSeries ℚ):
-- For every r >= 1 and A : PowerSeries ℚ, coeff r (A^(r-1) * (A - X * A')) = 0.
private lemma coeff_lagrange_vanish (A : PowerSeries ℚ) (r : ℕ) (hr : 1 ≤ r) :
    PowerSeries.coeff r (A ^ (r - 1) * (A - PowerSeries.X * PowerSeries.derivative ℚ A)) = 0 := by
  have hpow : A ^ (r - 1) * A = A ^ r := by
    rw [← pow_succ, show r - 1 + 1 = r by omega]
  have hd : PowerSeries.derivative ℚ (A ^ r) =
      (r : PowerSeries ℚ) * A ^ (r - 1) * PowerSeries.derivative ℚ A :=
    PowerSeries.derivative_pow A r
  have hmul : (r : PowerSeries ℚ) * (A ^ (r - 1) * (A - PowerSeries.X * PowerSeries.derivative ℚ A)) =
      (r : PowerSeries ℚ) * A ^ r - PowerSeries.X * PowerSeries.derivative ℚ (A ^ r) := by
    rw [mul_sub, hpow, mul_sub, hd]; ring
  have hc := congr_arg (PowerSeries.coeff r) hmul
  have hr_ne : (r : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hL : PowerSeries.coeff r
      ((r : PowerSeries ℚ) * (A ^ (r - 1) * (A - PowerSeries.X * PowerSeries.derivative ℚ A))) =
      (r : ℚ) * PowerSeries.coeff r (A ^ (r - 1) * (A - PowerSeries.X * PowerSeries.derivative ℚ A)) := by
    rw [← nsmul_eq_mul, map_nsmul, nsmul_eq_mul]
  have hR1 : PowerSeries.coeff r ((r : PowerSeries ℚ) * A ^ r) = (r : ℚ) * PowerSeries.coeff r (A ^ r) := by
    rw [← nsmul_eq_mul, map_nsmul, nsmul_eq_mul]
  have hR2 : PowerSeries.coeff r (PowerSeries.X * PowerSeries.derivative ℚ (A ^ r)) =
      (r : ℚ) * PowerSeries.coeff r (A ^ r) := by
    cases r with
    | zero => omega
    | succ m =>
      rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative]
      push_cast; ring
  rw [hL, map_sub, hR1, hR2, sub_self] at hc
  exact (mul_eq_zero.mp hc).resolve_left hr_ne

private lemma coeff_X_pow_mul_lt {R : Type*} [CommSemiring R] (k m : ℕ) (h : m < k)
    (F : PowerSeries R) : PowerSeries.coeff m (PowerSeries.X ^ k * F) = 0 := by
  rw [PowerSeries.coeff_X_pow_mul', if_neg (by omega)]

-- 2. Generalized Lagrange inversion for Φ(U) where U is the compositional inverse of G = X * B (A * B = 1):
-- Given Φ : PowerSeries ℚ and f : ℕ → ℚ with ∀ m ≤ n, ∑ k ∈ range (m+1), f k * coeff m (G^k) = coeff m Φ,
-- we have n * f n = coeff (n - 1) (Φ' * A^n)!
private lemma lagrange_inversion_gen (A B Φ : PowerSeries ℚ) (hAB : A * B = 1)
    (hA0 : PowerSeries.coeff 0 A = 1) (f : ℕ → ℚ)
    (hFG : ∀ m : ℕ,
      ∑ k ∈ Finset.range (m + 1), f k * PowerSeries.coeff m ((PowerSeries.X * B) ^ k) =
      PowerSeries.coeff m Φ) :
    ∀ n : ℕ, 1 ≤ n → (n : ℚ) * f n = PowerSeries.coeff (n - 1) (PowerSeries.derivative ℚ Φ * A ^ n) := by
  set G : PowerSeries ℚ := PowerSeries.X * B
  intro n hn
  let H : PowerSeries ℚ := ∑ k ∈ Finset.range (n + 1), PowerSeries.C (f k) * G ^ k
  have hH_agree : ∀ m : ℕ, m ≤ n → PowerSeries.coeff m H = PowerSeries.coeff m Φ := by
    intro m hm
    simp only [H, map_sum, PowerSeries.coeff_C_mul]
    have hsub : ∑ k ∈ Finset.range (n + 1), f k * PowerSeries.coeff m (G ^ k) =
        ∑ k ∈ Finset.range (m + 1), f k * PowerSeries.coeff m (G ^ k) := by
      symm
      refine Finset.sum_subset (Finset.range_mono (by omega)) fun k _ hk => ?_
      simp only [Finset.mem_range, not_lt] at hk
      have h0 : PowerSeries.coeff m (G ^ k) = 0 := by
        rw [show G ^ k = PowerSeries.X ^ k * B ^ k by simp [G, mul_pow]]
        exact coeff_X_pow_mul_lt k m (by omega) (B ^ k)
      rw [h0, mul_zero]
    rw [hsub]
    exact hFG m
  have hdH_agree : ∀ m : ℕ, m < n →
      PowerSeries.coeff m (PowerSeries.derivative ℚ H) =
      PowerSeries.coeff m (PowerSeries.derivative ℚ Φ) := by
    intro m hm
    rw [PowerSeries.coeff_derivative, PowerSeries.coeff_derivative, hH_agree (m + 1) (by omega)]
  have hmul_rhs : PowerSeries.coeff (n - 1) (PowerSeries.derivative ℚ H * A ^ n) =
      PowerSeries.coeff (n - 1) (PowerSeries.derivative ℚ Φ * A ^ n) := by
    rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (f := fun i j => PowerSeries.coeff i (PowerSeries.derivative ℚ H) * PowerSeries.coeff j (A ^ n)),
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (f := fun i j => PowerSeries.coeff i (PowerSeries.derivative ℚ Φ) * PowerSeries.coeff j (A ^ n))]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hin : i ≤ n - 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [hdH_agree i (by omega)]
  have hdH : PowerSeries.derivative ℚ H =
      ∑ k ∈ Finset.range (n + 1), PowerSeries.C ((k : ℚ) * f k) * G ^ (k - 1) * PowerSeries.derivative ℚ G := by
    simp only [H, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Derivation.leibniz, PowerSeries.derivative_C, smul_zero, add_zero,
      PowerSeries.derivative_pow, smul_eq_mul]
    have hCk : (k : PowerSeries ℚ) = PowerSeries.C (k : ℚ) := (map_natCast _ k).symm
    rw [hCk, map_mul PowerSeries.C (k : ℚ) (f k)]; ring
  have hG'_A2 : PowerSeries.derivative ℚ G * A ^ 2 = A - PowerSeries.X * PowerSeries.derivative ℚ A := by
    have hdAB := congr_arg (PowerSeries.derivative ℚ) hAB
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, Derivation.map_one_eq_zero] at hdAB
    have hdG : PowerSeries.derivative ℚ G = B + PowerSeries.X * PowerSeries.derivative ℚ B := by
      simp only [G, Derivation.leibniz, smul_eq_mul, PowerSeries.derivative_X, mul_one]
      ring
    calc PowerSeries.derivative ℚ G * A ^ 2
        = B * A ^ 2 + PowerSeries.X * (A * (A * PowerSeries.derivative ℚ B)) := by rw [hdG]; ring
      _ = (A * B) * A + PowerSeries.X * (A * (A * PowerSeries.derivative ℚ B)) := by ring
      _ = A + PowerSeries.X * (A * (A * PowerSeries.derivative ℚ B)) := by rw [hAB, one_mul]
      _ = A + PowerSeries.X * (A * (-B * PowerSeries.derivative ℚ A)) := by
            have : A * PowerSeries.derivative ℚ B = -B * PowerSeries.derivative ℚ A := by
              have : A * PowerSeries.derivative ℚ B + B * PowerSeries.derivative ℚ A = 0 := by
                linear_combination hdAB
              linear_combination this
            rw [this]
      _ = A - PowerSeries.X * ((A * B) * PowerSeries.derivative ℚ A) := by ring
      _ = A - PowerSeries.X * PowerSeries.derivative ℚ A := by rw [hAB, one_mul]
  rw [hdH, Finset.sum_mul, map_sum] at hmul_rhs
  have hterm : ∀ k ∈ Finset.range (n + 1),
      PowerSeries.coeff (n - 1) (PowerSeries.C ((k : ℚ) * f k) * G ^ (k - 1) * PowerSeries.derivative ℚ G * A ^ n) =
      if k = n then (n : ℚ) * f n else 0 := by
    intro k hk
    have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    by_cases hk0 : k = 0
    · subst hk0; simp [show (0 : ℕ) ≠ n by omega]
    · by_cases hkeq : k = n
      · subst hkeq
        simp only [↓reduceIte]
        have hrew : PowerSeries.C ((k : ℚ) * f k) * G ^ (k - 1) * PowerSeries.derivative ℚ G * A ^ k =
            PowerSeries.C ((k : ℚ) * f k) *
              (PowerSeries.X ^ (k - 1) * (B ^ (k - 1) * A ^ (k - 1)) * (PowerSeries.derivative ℚ G * A)) := by
          have hk1 : k - 1 + 1 = k := by omega
          have hAk : A ^ k = A ^ (k - 1) * A := by rw [← pow_succ, hk1]
          rw [hAk, show G ^ (k - 1) = PowerSeries.X ^ (k - 1) * B ^ (k - 1) by simp [G, mul_pow]]
          ring
        have hBA_pow : B ^ (k - 1) * A ^ (k - 1) = 1 := by
          rw [← mul_pow, mul_comm B A, hAB, one_pow]
        rw [hrew, hBA_pow, mul_one, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul']
        simp only [le_refl, ↓reduceIte, Nat.sub_self]
        have hGA0 : PowerSeries.coeff 0 (PowerSeries.derivative ℚ G * A) = 1 := by
          have h0 := congr_arg (PowerSeries.coeff 0) hG'_A2
          simp only [pow_two, ← mul_assoc, PowerSeries.coeff_zero_eq_constantCoeff, map_mul,
            map_sub, PowerSeries.constantCoeff_X, zero_mul, sub_zero] at h0
          rw [PowerSeries.coeff_zero_eq_constantCoeff] at hA0
          rw [hA0, mul_one] at h0
          rw [PowerSeries.coeff_zero_eq_constantCoeff, map_mul, hA0]
          exact h0
        rw [hGA0, mul_one]
      · simp only [hkeq, ↓reduceIte]
        set r := n - k
        have hr : 1 ≤ r := by omega
        have hrew : PowerSeries.C ((k : ℚ) * f k) * G ^ (k - 1) * PowerSeries.derivative ℚ G * A ^ n =
            PowerSeries.C ((k : ℚ) * f k) *
              (PowerSeries.X ^ (k - 1) * (B ^ (k - 1) * A ^ (k - 1)) *
                (A ^ (r - 1) * (PowerSeries.derivative ℚ G * A ^ 2))) := by
          have hAn : A ^ n = A ^ (k - 1) * A ^ (r - 1) * A ^ 2 := by
            rw [← pow_add, ← pow_add, show k - 1 + (r - 1) + 2 = n by omega]
          rw [hAn, show G ^ (k - 1) = PowerSeries.X ^ (k - 1) * B ^ (k - 1) by simp [G, mul_pow]]
          ring
        have hBA_pow : B ^ (k - 1) * A ^ (k - 1) = 1 := by
          rw [← mul_pow, mul_comm B A, hAB, one_pow]
        rw [hrew, hBA_pow, mul_one, hG'_A2, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul']
        simp only [show k - 1 ≤ n - 1 by omega, ↓reduceIte, show n - 1 - (k - 1) = r by omega]
        rw [coeff_lagrange_vanish A r hr, mul_zero]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' (Finset.range (n + 1)) n] at hmul_rhs
  simp only [Finset.mem_range, Nat.lt_succ_self, ↓reduceIte] at hmul_rhs
  exact hmul_rhs

-- 3. Recursive expansion of Φ in powers of G (when coeff k (G^k) = 1):
private noncomputable def compExpandSeq (G Φ : PowerSeries ℚ) : ℕ → ℚ
  | 0 => PowerSeries.coeff 0 Φ
  | m + 1 =>
      PowerSeries.coeff (m + 1) Φ -
        ∑ k ∈ (Finset.range (m + 1)).attach,
          compExpandSeq G Φ k.1 * PowerSeries.coeff (m + 1) (G ^ k.1)
decreasing_by
  exact Finset.mem_range.mp k.2

private lemma compExpandSeq_sum (G Φ : PowerSeries ℚ) (hdiag : ∀ k : ℕ, PowerSeries.coeff k (G ^ k) = 1)
    (m : ℕ) :
    ∑ k ∈ Finset.range (m + 1), compExpandSeq G Φ k * PowerSeries.coeff m (G ^ k) =
    PowerSeries.coeff m Φ := by
  cases m with
  | zero =>
    simp [compExpandSeq]
  | succ m =>
    rw [Finset.sum_range_succ, hdiag (m + 1), mul_one]
    conv_lhs => arg 2; rw [compExpandSeq]
    have hattach : (∑ k ∈ (Finset.range (m + 1)).attach,
          compExpandSeq G Φ k.1 * PowerSeries.coeff (m + 1) (G ^ k.1)) =
        ∑ k ∈ Finset.range (m + 1), compExpandSeq G Φ k * PowerSeries.coeff (m + 1) (G ^ k) :=
      Finset.sum_attach (Finset.range (m + 1))
        (fun k => compExpandSeq G Φ k * PowerSeries.coeff (m + 1) (G ^ k))
    rw [hattach]; ring

-- Multiplicativity of compExpandSeq: if G(0)=0, coeff k (G^k)=1, then
-- compExpandSeq G (Φ * Ψ) is the Cauchy product of compExpandSeq G Φ and compExpandSeq G Ψ!
private lemma compExpandSeq_mul (G Φ Ψ : PowerSeries ℚ)
    (hG0 : PowerSeries.coeff 0 G = 0)
    (hdiag : ∀ k : ℕ, PowerSeries.coeff k (G ^ k) = 1) :
    PowerSeries.mk (compExpandSeq G (Φ * Ψ)) =
    PowerSeries.mk (compExpandSeq G Φ) * PowerSeries.mk (compExpandSeq G Ψ) := by
  -- Prove coeff m agrees by strong induction on m!
  have hGpow_lt : ∀ k m : ℕ, m < k → PowerSeries.coeff m (G ^ k) = 0 := by
    intro k
    induction k with
    | zero => intro m hm; omega
    | succ k ih =>
      intro m hm
      rw [pow_succ, PowerSeries.coeff_mul,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ
          (f := fun i j => PowerSeries.coeff i (G ^ k) * PowerSeries.coeff j G)]
      refine Finset.sum_eq_zero fun i hi => ?_
      have him : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      by_cases hik : i < k
      · rw [ih i hik, zero_mul]
      · have hmi : m - i = 0 := by omega
        rw [hmi, hG0, mul_zero]
  set f := compExpandSeq G Φ
  set g := compExpandSeq G Ψ
  set h := compExpandSeq G (Φ * Ψ)
  set fg := fun m => PowerSeries.coeff m (PowerSeries.mk f * PowerSeries.mk g)
  have hfg_sum : ∀ m : ℕ, ∑ k ∈ Finset.range (m + 1), fg k * PowerSeries.coeff m (G ^ k) =
      PowerSeries.coeff m (Φ * Ψ) := by
    intro m
    let F_m : PowerSeries ℚ := ∑ i ∈ Finset.range (m + 1), PowerSeries.C (f i) * G ^ i
    let G_m : PowerSeries ℚ := ∑ j ∈ Finset.range (m + 1), PowerSeries.C (g j) * G ^ j
    have hFm : ∀ r : ℕ, r ≤ m → PowerSeries.coeff r F_m = PowerSeries.coeff r Φ := by
      intro r hr
      simp only [F_m, map_sum, PowerSeries.coeff_C_mul]
      have hsub : ∑ i ∈ Finset.range (m + 1), f i * PowerSeries.coeff r (G ^ i) =
          ∑ i ∈ Finset.range (r + 1), f i * PowerSeries.coeff r (G ^ i) := by
        symm
        refine Finset.sum_subset (Finset.range_mono (by omega)) fun i _ hi => ?_
        simp only [Finset.mem_range, not_lt] at hi
        rw [hGpow_lt i r (by omega), mul_zero]
      rw [hsub]; exact compExpandSeq_sum G Φ hdiag r
    have hGm : ∀ r : ℕ, r ≤ m → PowerSeries.coeff r G_m = PowerSeries.coeff r Ψ := by
      intro r hr
      simp only [G_m, map_sum, PowerSeries.coeff_C_mul]
      have hsub : ∑ j ∈ Finset.range (m + 1), g j * PowerSeries.coeff r (G ^ j) =
          ∑ j ∈ Finset.range (r + 1), g j * PowerSeries.coeff r (G ^ j) := by
        symm
        refine Finset.sum_subset (Finset.range_mono (by omega)) fun j _ hj => ?_
        simp only [Finset.mem_range, not_lt] at hj
        rw [hGpow_lt j r (by omega), mul_zero]
      rw [hsub]; exact compExpandSeq_sum G Ψ hdiag r
    have hprod_eq : PowerSeries.coeff m (F_m * G_m) = PowerSeries.coeff m (Φ * Ψ) := by
      rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ
          (f := fun i j => PowerSeries.coeff i F_m * PowerSeries.coeff j G_m),
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ
          (f := fun i j => PowerSeries.coeff i Φ * PowerSeries.coeff j Ψ)]
      refine Finset.sum_congr rfl fun r hr => ?_
      have hrm : r ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
      rw [hFm r hrm, hGm (m - r) (by omega)]
    rw [← hprod_eq]
    have hFG_expand : F_m * G_m =
        ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
          PowerSeries.C (f i * g j) * G ^ (i + j) := by
      dsimp only [F_m, G_m]
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, pow_add]; ring
    rw [hFG_expand, map_sum]
    simp only [map_sum, PowerSeries.coeff_C_mul]
    -- Group by k = i + j <= m (terms with i + j > m vanish by hGpow_lt!)
    have hsplit : ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
          f i * g j * PowerSeries.coeff m (G ^ (i + j)) =
        ∑ k ∈ Finset.range (m + 1),
          (∑ i ∈ Finset.range (k + 1), f i * g (k - i)) * PowerSeries.coeff m (G ^ k) := by
      have h1 : ∀ k ∈ Finset.range (m + 1),
          (∑ i ∈ Finset.range (k + 1), f i * g (k - i)) * PowerSeries.coeff m (G ^ k) =
          ∑ i ∈ Finset.range (k + 1), f i * g (k - i) * PowerSeries.coeff m (G ^ (i + (k - i))) := by
        intro k _
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun i hi => ?_
        have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        rw [show i + (k - i) = k by omega]
      rw [Finset.sum_congr rfl h1,
        ← Finset.sum_sigma (Finset.range (m + 1)) (fun k => Finset.range (k + 1))
            (fun s => f s.2 * g (s.1 - s.2) * PowerSeries.coeff m (G ^ (s.2 + (s.1 - s.2))))]
      rw [← Finset.sum_product']
      have hfilt : ∑ p ∈ Finset.range (m + 1) ×ˢ Finset.range (m + 1),
            f p.1 * g p.2 * PowerSeries.coeff m (G ^ (p.1 + p.2)) =
          ∑ p ∈ (Finset.range (m + 1) ×ˢ Finset.range (m + 1)).filter (fun p => p.1 + p.2 ≤ m),
            f p.1 * g p.2 * PowerSeries.coeff m (G ^ (p.1 + p.2)) := by
        symm
        refine Finset.sum_subset (Finset.filter_subset _ _) fun p _ hnot => ?_
        simp only [Finset.mem_filter, not_and, not_le] at hnot
        have hgt : m < p.1 + p.2 := hnot ‹_›
        rw [hGpow_lt (p.1 + p.2) m hgt, mul_zero]
      rw [hfilt]
      refine Finset.sum_nbij' (fun p => ⟨p.1 + p.2, p.1⟩) (fun s => (s.2, s.1 - s.2)) ?_ ?_ ?_ ?_ ?_
      · intro p hp
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
        simp only [Finset.mem_sigma, Finset.mem_range]
        omega
      · intro s hs
        simp only [Finset.mem_sigma, Finset.mem_range] at hs
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
        omega
      · intro p hp
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
        ext
        · rfl
        · dsimp; omega
      · intro s hs
        rcases s with ⟨k, i⟩
        simp only [Finset.mem_sigma, Finset.mem_range] at hs
        exact Sigma.ext (by dsimp; omega) (heq_of_eq rfl)
      · intro p _
        dsimp; rw [Nat.add_sub_cancel_left]
    rw [hsplit]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    simp only [fg, PowerSeries.coeff_mul, PowerSeries.coeff_mk]
    exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ (f := fun i j => f i * g j) k
  ext m
  simp only [PowerSeries.coeff_mk]
  change h m = fg m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    have h1 := compExpandSeq_sum G (Φ * Ψ) hdiag m
    have h2 := hfg_sum m
    have heq : ∑ k ∈ Finset.range (m + 1), h k * PowerSeries.coeff m (G ^ k) =
        ∑ k ∈ Finset.range (m + 1), fg k * PowerSeries.coeff m (G ^ k) := h1.trans h2.symm
    rw [Finset.sum_range_succ, Finset.sum_range_succ, hdiag m, mul_one, mul_one] at heq
    have hprev : ∑ k ∈ Finset.range m, h k * PowerSeries.coeff m (G ^ k) =
        ∑ k ∈ Finset.range m, fg k * PowerSeries.coeff m (G ^ k) := by
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [ih k (Finset.mem_range.mp hk)]
    linarith

-- 4. Raney / Rothe-Hagen coefficients R(r, t, k):
private def raney (r t : ℚ) : ℕ → ℚ
  | 0 => 1
  | k + 1 => r * (∏ j ∈ Finset.range k, (r + t * (k + 1 : ℚ) - (j + 1 : ℚ))) / ((k + 1).factorial : ℚ)

-- Binomial coefficient identity for (1 + X)^M in PowerSeries ℚ:
private lemma coeff_one_add_X_pow (M k : ℕ) :
    PowerSeries.coeff k ((1 + PowerSeries.X : PowerSeries ℚ) ^ M) = (Nat.choose M k : ℚ) := by
  rw [add_pow, map_sum]
  have hterm : ∀ i ∈ Finset.range (M + 1),
      PowerSeries.coeff k ((1 : PowerSeries ℚ) ^ i * PowerSeries.X ^ (M - i) * (Nat.choose M i : PowerSeries ℚ)) =
      if k = M - i then (Nat.choose M i : ℚ) else 0 := by
    intro i _
    rw [one_pow, one_mul, mul_comm, ← nsmul_eq_mul, map_nsmul, PowerSeries.coeff_X_pow, nsmul_eq_mul]
    split_ifs with h
    · rw [mul_one]
    · rw [mul_zero]
  rw [Finset.sum_congr rfl hterm]
  by_cases hkM : k ≤ M
  · rw [Finset.sum_eq_single (M - k)]
    · simp [show M - (M - k) = k by omega, Nat.choose_symm hkM]
    · intro i hi hne
      have hiM : i ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      rw [if_neg (by omega)]
    · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
  · push Not at hkM
    rw [Nat.choose_eq_zero_of_lt hkM, Nat.cast_zero]
    refine Finset.sum_eq_zero fun i hi => ?_
    have hiM : i ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [if_neg (by omega)]

-- Falling factorial matches Nat.choose for natural M:
private lemma choose_eq_prod_div_fact (M k : ℕ) :
    (Nat.choose M k : ℚ) = (∏ j ∈ Finset.range k, ((M : ℚ) - (j : ℚ))) / (k.factorial : ℚ) := by
  have h1 : (Nat.descFactorial M k : ℚ) = (k.factorial : ℚ) * (Nat.choose M k : ℚ) := by
    exact_mod_cast Nat.descFactorial_eq_factorial_mul_choose M k
  have h2 : (Nat.descFactorial M k : ℚ) = ∏ j ∈ Finset.range k, ((M : ℚ) - (j : ℚ)) := by
    clear h1
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.descFactorial_succ, Nat.cast_mul, ih, Finset.prod_range_succ, mul_comm]
      by_cases hkM : k ≤ M
      · rw [Nat.cast_sub hkM]
      · push Not at hkM
        have hz : ∏ j ∈ Finset.range k, ((M : ℚ) - (j : ℚ)) = 0 :=
          Finset.prod_eq_zero (Finset.mem_range.mpr hkM) (by simp)
        rw [hz, zero_mul, zero_mul]
  have hfact_ne : (k.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  rw [← h2, h1, mul_div_cancel_left₀ _ hfact_ne]

-- 5. Rothe-Hagen convolution for natural r, s, t >= 1 via Lagrange inversion on G = X * (1 + X)^(-t)!
private lemma rothe_hagen_nat (r s t k : ℕ) (hr : 1 ≤ r) (hs : 1 ≤ s) :
    ∑ i ∈ Finset.range (k + 1), raney (r : ℚ) (t : ℚ) i * raney (s : ℚ) (t : ℚ) (k - i) =
    raney ((r : ℚ) + (s : ℚ)) (t : ℚ) k := by
  let A : PowerSeries ℚ := (1 + PowerSeries.X) ^ t
  have hA0 : PowerSeries.coeff 0 A = 1 := by
    simp [A, PowerSeries.coeff_zero_eq_constantCoeff]
  have hA_unit : IsUnit A := by
    rw [PowerSeries.isUnit_iff_constantCoeff]
    rw [← PowerSeries.coeff_zero_eq_constantCoeff, hA0]
    exact isUnit_one
  obtain ⟨u, hu⟩ := hA_unit
  let B : PowerSeries ℚ := ↑u⁻¹
  have hAB : A * B = 1 := by
    have : (u : PowerSeries ℚ) * (↑u⁻¹ : PowerSeries ℚ) = 1 := Units.mul_inv u
    rwa [hu] at this
  have hB0 : PowerSeries.coeff 0 B = 1 := by
    have h0 := congr_arg (PowerSeries.coeff 0) hAB
    rw [PowerSeries.coeff_zero_eq_constantCoeff, map_mul, map_one] at h0
    rw [PowerSeries.coeff_zero_eq_constantCoeff] at hA0 ⊢
    rw [hA0, one_mul] at h0
    exact h0
  let G : PowerSeries ℚ := PowerSeries.X * B
  have hG0 : PowerSeries.coeff 0 G = 0 := by
    simp [G, PowerSeries.coeff_zero_eq_constantCoeff]
  have hG_diag : ∀ m : ℕ, PowerSeries.coeff m (G ^ m) = 1 := by
    intro m
    rw [show G ^ m = PowerSeries.X ^ m * B ^ m by simp [G, mul_pow], PowerSeries.coeff_X_pow_mul']
    simp only [le_refl, ↓reduceIte, Nat.sub_self, PowerSeries.coeff_zero_eq_constantCoeff, map_pow]
    rw [← PowerSeries.coeff_zero_eq_constantCoeff, hB0, one_pow]
  -- Compute compExpandSeq G ((1 + X)^m) = raney m t for any m >= 1!
  have hexp : ∀ m : ℕ, 1 ≤ m → ∀ j : ℕ,
      compExpandSeq G ((1 + PowerSeries.X : PowerSeries ℚ) ^ m) j = raney (m : ℚ) (t : ℚ) j := by
    intro m hm j
    cases j with
    | zero =>
      simp [compExpandSeq, raney, PowerSeries.coeff_zero_eq_constantCoeff]
    | succ j =>
      have hlag := lagrange_inversion_gen A B ((1 + PowerSeries.X) ^ m) hAB hA0
        (compExpandSeq G ((1 + PowerSeries.X) ^ m))
        (compExpandSeq_sum G ((1 + PowerSeries.X) ^ m) hG_diag) (j + 1) (Nat.succ_pos j)
      have hdΦ : PowerSeries.derivative ℚ ((1 + PowerSeries.X : PowerSeries ℚ) ^ m) =
          PowerSeries.C (m : ℚ) * (1 + PowerSeries.X) ^ (m - 1) := by
        rw [PowerSeries.derivative_pow, map_add, Derivation.map_one_eq_zero,
          PowerSeries.derivative_X, zero_add, mul_one, map_natCast]
      rw [hdΦ, show A ^ (j + 1) = (1 + PowerSeries.X) ^ (t * (j + 1)) by simp [A, ← pow_mul],
        mul_assoc, ← pow_add, PowerSeries.coeff_C_mul, Nat.add_sub_cancel, coeff_one_add_X_pow,
        choose_eq_prod_div_fact] at hlag
      have hj1_ne : ((j + 1 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero j)
      have hfact : ((j + 1).factorial : ℚ) = ((j + 1 : ℕ) : ℚ) * (j.factorial : ℚ) := by
        rw [Nat.factorial_succ, Nat.cast_mul]
      have hprod_eq : ∏ i ∈ Finset.range j, (((m - 1 + t * (j + 1) : ℕ) : ℚ) - (i : ℚ)) =
          ∏ i ∈ Finset.range j, ((m : ℚ) + (t : ℚ) * ((j : ℚ) + 1) - ((i : ℚ) + 1)) := by
        refine Finset.prod_congr rfl fun i _ => ?_
        have : ((m - 1 + t * (j + 1) : ℕ) : ℚ) = (m : ℚ) - 1 + (t : ℚ) * ((j : ℚ) + 1) := by
          push_cast [Nat.cast_sub hm]; ring
        rw [this]; ring
      rw [hprod_eq] at hlag
      simp only [raney]
      rw [hfact]
      have hdiv : compExpandSeq G ((1 + PowerSeries.X) ^ m) (j + 1) =
          (m : ℚ) * ((∏ i ∈ Finset.range j, ((m : ℚ) + (t : ℚ) * ((j : ℚ) + 1) - ((i : ℚ) + 1))) / (j.factorial : ℚ)) /
            ((j + 1 : ℕ) : ℚ) := by
        rw [← hlag, mul_div_cancel_left₀ _ hj1_ne]
      rw [hdiv]
      have hfj_ne : (j.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)
      field_simp [hj1_ne, hfj_ne]
  have hmul := compExpandSeq_mul G ((1 + PowerSeries.X) ^ r) ((1 + PowerSeries.X) ^ s) hG0 hG_diag
  rw [← pow_add] at hmul
  have hc := congr_arg (PowerSeries.coeff k) hmul
  rw [PowerSeries.coeff_mk, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (f := fun i j => PowerSeries.coeff i (PowerSeries.mk (compExpandSeq G ((1 + PowerSeries.X) ^ r))) *
        PowerSeries.coeff j (PowerSeries.mk (compExpandSeq G ((1 + PowerSeries.X) ^ s))))] at hc
  simp only [PowerSeries.coeff_mk, Nat.succ_eq_add_one] at hc
  rw [hexp (r + s) (by omega) k, Nat.cast_add] at hc
  rw [hc]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hexp r hr i, hexp s hs (k - i)]

-- 6. Polynomial lift from ℕ³ to ℚ³:
private lemma poly_eq_zero_of_nat (P : Polynomial ℚ) (h : ∀ m : ℕ, 1 ≤ m → P.eval (m : ℚ) = 0) :
    P = 0 := by
  by_contra hne
  have hinf : Set.Infinite {x : ℚ | P.IsRoot x} :=
    Set.infinite_of_injective_forall_mem (f := fun m : ℕ => ((m + 1 : ℕ) : ℚ))
      (fun a b hab => by
        have : (a + 1 : ℕ) = b + 1 := Nat.cast_injective hab
        omega)
      (fun m => h (m + 1) (Nat.succ_pos m))
  exact hinf (Polynomial.finite_setOfPred_isRoot hne)

private noncomputable def raneyPolyR (t : ℚ) : ℕ → Polynomial ℚ
  | 0 => 1
  | k + 1 =>
      Polynomial.C (((k + 1).factorial : ℚ)⁻¹) * Polynomial.X *
        ∏ j ∈ Finset.range k, (Polynomial.X + Polynomial.C (t * (k + 1 : ℚ) - (j + 1 : ℚ)))

private lemma eval_raneyPolyR (r t : ℚ) (k : ℕ) :
    (raneyPolyR t k).eval r = raney r t k := by
  cases k with
  | zero => simp [raneyPolyR, raney]
  | succ k =>
    simp only [raneyPolyR, raney, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
      Polynomial.eval_prod, Polynomial.eval_add, div_eq_mul_inv]
    have hprod : ∏ j ∈ Finset.range k, (r + (t * ((k : ℚ) + 1) - ((j : ℚ) + 1))) =
        ∏ j ∈ Finset.range k, (r + t * ((k : ℚ) + 1) - ((j : ℚ) + 1)) := by
      refine Finset.prod_congr rfl fun j _ => by ring
    rw [hprod]; ring

private noncomputable def raneyPolyT (r : ℚ) : ℕ → Polynomial ℚ
  | 0 => 1
  | k + 1 =>
      Polynomial.C (r * ((k + 1).factorial : ℚ)⁻¹) *
        ∏ j ∈ Finset.range k, (Polynomial.C (k + 1 : ℚ) * Polynomial.X + Polynomial.C (r - (j + 1 : ℚ)))

private lemma eval_raneyPolyT (r t : ℚ) (k : ℕ) :
    (raneyPolyT r k).eval t = raney r t k := by
  cases k with
  | zero => simp [raneyPolyT, raney]
  | succ k =>
    simp only [raneyPolyT, raney, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
      Polynomial.eval_prod, Polynomial.eval_add, div_eq_mul_inv]
    have hprod : ∏ j ∈ Finset.range k, (((k : ℚ) + 1) * t + (r - ((j : ℚ) + 1))) =
        ∏ j ∈ Finset.range k, (r + t * ((k : ℚ) + 1) - ((j : ℚ) + 1)) := by
      refine Finset.prod_congr rfl fun j _ => by ring
    rw [hprod]; ring

private lemma rothe_hagen (r s t : ℚ) (k : ℕ) :
    ∑ i ∈ Finset.range (k + 1), raney r t i * raney s t (k - i) = raney (r + s) t k := by
  -- Step 1: Lift r from ℕ≥1 to ℚ (for s, t ∈ ℕ, s ≥ 1)
  have h1 : ∀ (r : ℚ) (s t : ℕ), 1 ≤ s →
      ∑ i ∈ Finset.range (k + 1), raney r (t : ℚ) i * raney (s : ℚ) (t : ℚ) (k - i) =
      raney (r + (s : ℚ)) (t : ℚ) k := by
    intro r s t hs
    let P : Polynomial ℚ :=
      (∑ i ∈ Finset.range (k + 1), raneyPolyR (t : ℚ) i * Polynomial.C (raney (s : ℚ) (t : ℚ) (k - i))) -
      (raneyPolyR (t : ℚ) k).comp (Polynomial.X + Polynomial.C (s : ℚ))
    have hP0 : P = 0 := poly_eq_zero_of_nat P fun m hm => by
      simp only [P, Polynomial.eval_sub, Polynomial.eval_finsetSum, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, eval_raneyPolyR]
      rw [rothe_hagen_nat m s t k hm hs, sub_self]
    have hev := congr_arg (Polynomial.eval r) hP0
    simp only [P, Polynomial.eval_zero, Polynomial.eval_sub, Polynomial.eval_finsetSum,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp, Polynomial.eval_add,
      Polynomial.eval_X, eval_raneyPolyR] at hev
    exact sub_eq_zero.mp hev
  -- Step 2: Lift s from ℕ≥1 to ℚ (for r : ℚ, t ∈ ℕ)
  have h2 : ∀ (r s : ℚ) (t : ℕ),
      ∑ i ∈ Finset.range (k + 1), raney r (t : ℚ) i * raney s (t : ℚ) (k - i) =
      raney (r + s) (t : ℚ) k := by
    intro r s t
    let P : Polynomial ℚ :=
      (∑ i ∈ Finset.range (k + 1), Polynomial.C (raney r (t : ℚ) i) * raneyPolyR (t : ℚ) (k - i)) -
      (raneyPolyR (t : ℚ) k).comp (Polynomial.C r + Polynomial.X)
    have hP0 : P = 0 := poly_eq_zero_of_nat P fun m hm => by
      simp only [P, Polynomial.eval_sub, Polynomial.eval_finsetSum, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, eval_raneyPolyR]
      rw [h1 r m t hm, sub_self]
    have hev := congr_arg (Polynomial.eval s) hP0
    simp only [P, Polynomial.eval_zero, Polynomial.eval_sub, Polynomial.eval_finsetSum,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp, Polynomial.eval_add,
      Polynomial.eval_X, eval_raneyPolyR] at hev
    exact sub_eq_zero.mp hev
  -- Step 3: Lift t from ℕ to ℚ (for r, s : ℚ)
  let P : Polynomial ℚ :=
    (∑ i ∈ Finset.range (k + 1), raneyPolyT r i * raneyPolyT s (k - i)) -
    raneyPolyT (r + s) k
  have hP0 : P = 0 := poly_eq_zero_of_nat P fun m _ => by
    simp only [P, Polynomial.eval_sub, Polynomial.eval_finsetSum, Polynomial.eval_mul, eval_raneyPolyT]
    rw [h2 r s m, sub_self]
  have hev := congr_arg (Polynomial.eval t) hP0
  simp only [P, Polynomial.eval_zero, Polynomial.eval_sub, Polynomial.eval_finsetSum,
    Polynomial.eval_mul, eval_raneyPolyT] at hev
  exact sub_eq_zero.mp hev

-- 7. Raney power series B_{r,t}(y) = ∑ raney r t k * y^k satisfies B_{r,t} * B_{s,t} = B_{r+s,t}!
private noncomputable def raneySeries (r t : ℚ) : PowerSeries ℚ :=
  PowerSeries.mk (raney r t)

private lemma raneySeries_mul (r s t : ℚ) :
    raneySeries r t * raneySeries s t = raneySeries (r + s) t := by
  ext k
  simp only [raneySeries, PowerSeries.coeff_mul, PowerSeries.coeff_mk,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (f := fun i j => raney r t i * raney s t j)]
  exact rothe_hagen r s t k

private lemma raneySeries_pow (r t : ℚ) (m : ℕ) :
    raneySeries r t ^ m = raneySeries ((m : ℚ) * r) t := by
  induction m with
  | zero =>
    ext k
    cases k with
    | zero => simp [raneySeries, raney]
    | succ k => simp [raneySeries, raney]
  | succ m ih =>
    rw [pow_succ, ih, raneySeries_mul]
    congr 1; push_cast; ring

-- Fundamental identity: raney 1 t (k + 1) = raney t t k!
private lemma raney_one_succ (t : ℚ) (k : ℕ) :
    raney 1 t (k + 1) = raney t t k := by
  cases k with
  | zero => simp [raney]
  | succ k =>
    simp only [raney]
    have hprod : ∏ j ∈ Finset.range (k + 1), (1 + t * ((k : ℚ) + 1 + 1) - ((j : ℚ) + 1)) =
        (t * ((k : ℚ) + 2)) * ∏ j ∈ Finset.range k, (t + t * ((k : ℚ) + 1) - ((j : ℚ) + 1)) := by
      rw [Finset.prod_range_succ']
      have h0 : 1 + t * ((k : ℚ) + 1 + 1) - ((0 : ℕ) + 1 : ℚ) = t * ((k : ℚ) + 2) := by ring
      rw [h0, mul_comm]
      congr 1
      refine Finset.prod_congr rfl fun j _ => by push_cast; ring
    have hfact : ((k + 2).factorial : ℚ) = ((k : ℚ) + 2) * ((k + 1).factorial : ℚ) := by
      rw [Nat.factorial_succ, Nat.cast_mul]; push_cast; ring
    have hk2_ne : ((k : ℚ) + 2) ≠ 0 := by positivity
    simp only [Nat.cast_add, Nat.cast_one]
    rw [hprod, show k + 1 + 1 = k + 2 by omega, hfact]
    field_simp [hk2_ne]

-- 8. Main theorem for oeis-a078534!
private theorem main_proved :
    ∀ (n : ℕ), 2 ≤ n →
    ∀ (A : PowerSeries ℚ),
      PowerSeries.coeff 0 A = 1 →
      A ^ n - (n : PowerSeries ℚ) ^ 2 * PowerSeries.X * A ^ (n + 1) = 1 →
      PowerSeries.coeff (n - 1) A = (n : ℚ) ^ (2 * n - 3) ∧
      PowerSeries.coeff (2 * n - 1) A = (n : ℚ) ^ (4 * n - 2) := by
  intro n hn A hA0 hAeq
  have hn_ne : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  let r : ℚ := (n : ℚ)⁻¹
  let t : ℚ := 1 + (n : ℚ)⁻¹
  -- Define scaled Raney series F(x) = ∑ n^(2k) * raney r t k * x^k
  let F : PowerSeries ℚ := PowerSeries.mk (fun k => (n : ℚ) ^ (2 * k) * raney r t k)
  have hF0 : PowerSeries.coeff 0 F = 1 := by simp [F, raney]
  -- Scaling power series by c^k is a ring hom!
  have hscale_pow : ∀ (m : ℕ) (k : ℕ),
      PowerSeries.coeff k (F ^ m) = (n : ℚ) ^ (2 * k) * PowerSeries.coeff k (raneySeries r t ^ m) := by
    intro m
    induction m with
    | zero =>
      intro k
      cases k with
      | zero => simp
      | succ k => simp
    | succ m ih =>
      intro k
      rw [pow_succ, pow_succ, PowerSeries.coeff_mul, PowerSeries.coeff_mul,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ
          (f := fun i j => PowerSeries.coeff i (F ^ m) * PowerSeries.coeff j F),
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ
          (f := fun i j => PowerSeries.coeff i (raneySeries r t ^ m) * PowerSeries.coeff j (raneySeries r t)),
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      rw [ih i]
      simp only [F, raneySeries, PowerSeries.coeff_mk]
      have hpow : (n : ℚ) ^ (2 * i) * (n : ℚ) ^ (2 * (k - i)) = (n : ℚ) ^ (2 * k) := by
        rw [← pow_add, show 2 * i + 2 * (k - i) = 2 * k by omega]
      calc (n : ℚ) ^ (2 * i) * PowerSeries.coeff i (raneySeries r t ^ m) *
              ((n : ℚ) ^ (2 * (k - i)) * raney r t (k - i))
          = ((n : ℚ) ^ (2 * i) * (n : ℚ) ^ (2 * (k - i))) *
              (PowerSeries.coeff i (raneySeries r t ^ m) * raney r t (k - i)) := by ring
        _ = (n : ℚ) ^ (2 * k) * (PowerSeries.coeff i (raneySeries r t ^ m) * raney r t (k - i)) := by
              rw [hpow]
  -- Show F satisfies F^n - n^2 * X * F^(n+1) = 1!
  have hFeq : F ^ n - (n : PowerSeries ℚ) ^ 2 * PowerSeries.X * F ^ (n + 1) = 1 := by
    ext k
    rw [map_sub]
    cases k with
    | zero =>
      simp only [PowerSeries.coeff_zero_eq_constantCoeff, map_pow, map_mul, PowerSeries.constantCoeff_X,
        mul_zero, zero_mul, sub_zero, map_one]
      rw [← PowerSeries.coeff_zero_eq_constantCoeff, hF0, one_pow]
    | succ k =>
      have h1 : PowerSeries.coeff (k + 1) (1 : PowerSeries ℚ) = 0 := by simp
      rw [h1, sub_eq_zero]
      rw [hscale_pow n (k + 1), raneySeries_pow]
      have hnr : (n : ℚ) * r = 1 := mul_inv_cancel₀ hn_ne
      rw [hnr]
      have hX : PowerSeries.coeff (k + 1) ((n : PowerSeries ℚ) ^ 2 * PowerSeries.X * F ^ (n + 1)) =
          (n : ℚ) ^ 2 * PowerSeries.coeff k (F ^ (n + 1)) := by
        rw [show (n : PowerSeries ℚ) ^ 2 * PowerSeries.X * F ^ (n + 1) =
            PowerSeries.C ((n : ℚ) ^ 2) * (PowerSeries.X * F ^ (n + 1)) by
              rw [map_pow, map_natCast]; ring,
          PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul]
      rw [hX, hscale_pow (n + 1) k, raneySeries_pow]
      have hn1r : ((n + 1 : ℕ) : ℚ) * r = t := by
        simp only [r, t, Nat.cast_add, Nat.cast_one]
        field_simp [hn_ne]
      rw [hn1r]
      simp only [raneySeries, PowerSeries.coeff_mk]
      rw [raney_one_succ t k]
      have hpow : (n : ℚ) ^ (2 * (k + 1)) = (n : ℚ) ^ 2 * (n : ℚ) ^ (2 * k) := by
        rw [← pow_add, show 2 + 2 * k = 2 * (k + 1) by omega]
      rw [hpow]; ring
  -- Uniqueness: A = F by strong induction on k!
  have hAF : A = F := by
    ext k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      cases k with
      | zero => rw [hA0, hF0]
      | succ k =>
        -- Compare coeff (k+1) of A^n = 1 + n^2 * X * A^(n+1) and F^n = 1 + n^2 * X * F^(n+1)!
        have hpow_agree : ∀ (m j : ℕ), j ≤ k → PowerSeries.coeff j (A ^ m) = PowerSeries.coeff j (F ^ m) := by
          intro m
          induction m with
          | zero => intro j _; simp
          | succ m ihm =>
            intro j hj
            rw [pow_succ, pow_succ, PowerSeries.coeff_mul, PowerSeries.coeff_mul,
              Finset.Nat.sum_antidiagonal_eq_sum_range_succ
                (f := fun i l => PowerSeries.coeff i (A ^ m) * PowerSeries.coeff l A),
              Finset.Nat.sum_antidiagonal_eq_sum_range_succ
                (f := fun i l => PowerSeries.coeff i (F ^ m) * PowerSeries.coeff l F)]
            refine Finset.sum_congr rfl fun i hi => ?_
            have hij : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
            rw [ihm i (by omega), ih (j - i) (by omega)]
        -- Also coeff (k+1) (A^m) - coeff (k+1) (F^m) = m * (coeff (k+1) A - coeff (k+1) F)!
        have hpow_diff : ∀ m : ℕ,
            PowerSeries.coeff (k + 1) (A ^ m) - PowerSeries.coeff (k + 1) (F ^ m) =
            (m : ℚ) * (PowerSeries.coeff (k + 1) A - PowerSeries.coeff (k + 1) F) := by
          intro m
          induction m with
          | zero => simp
          | succ m ihm =>
            rw [pow_succ, pow_succ, PowerSeries.coeff_mul, PowerSeries.coeff_mul,
              Finset.Nat.sum_antidiagonal_eq_sum_range_succ
                (f := fun i l => PowerSeries.coeff i (A ^ m) * PowerSeries.coeff l A),
              Finset.Nat.sum_antidiagonal_eq_sum_range_succ
                (f := fun i l => PowerSeries.coeff i (F ^ m) * PowerSeries.coeff l F)]
            have hA0m : PowerSeries.coeff 0 (A ^ m) = 1 := by
              rw [PowerSeries.coeff_zero_eq_constantCoeff, map_pow, ← PowerSeries.coeff_zero_eq_constantCoeff, hA0, one_pow]
            have hF0m : PowerSeries.coeff 0 (F ^ m) = 1 := by
              rw [PowerSeries.coeff_zero_eq_constantCoeff, map_pow, ← PowerSeries.coeff_zero_eq_constantCoeff, hF0, one_pow]
            have hsplitA : ∑ x ∈ Finset.range (k + 2), PowerSeries.coeff x (A ^ m) * PowerSeries.coeff (k + 1 - x) A =
                PowerSeries.coeff (k + 1) A +
                (∑ x ∈ Finset.range k, PowerSeries.coeff (x + 1) (A ^ m) * PowerSeries.coeff (k + 1 - (x + 1)) A) +
                PowerSeries.coeff (k + 1) (A ^ m) := by
              rw [Finset.sum_range_succ, Finset.sum_range_succ', Nat.sub_self, Nat.sub_zero, hA0, hA0m, mul_one, one_mul]
              ring
            have hsplitF : ∑ x ∈ Finset.range (k + 2), PowerSeries.coeff x (F ^ m) * PowerSeries.coeff (k + 1 - x) F =
                PowerSeries.coeff (k + 1) F +
                (∑ x ∈ Finset.range k, PowerSeries.coeff (x + 1) (F ^ m) * PowerSeries.coeff (k + 1 - (x + 1)) F) +
                PowerSeries.coeff (k + 1) (F ^ m) := by
              rw [Finset.sum_range_succ, Finset.sum_range_succ', Nat.sub_self, Nat.sub_zero, hF0, hF0m, mul_one, one_mul]
              ring
            have hmid : ∑ x ∈ Finset.range k, PowerSeries.coeff (x + 1) (A ^ m) * PowerSeries.coeff (k + 1 - (x + 1)) A =
                ∑ x ∈ Finset.range k, PowerSeries.coeff (x + 1) (F ^ m) * PowerSeries.coeff (k + 1 - (x + 1)) F := by
              refine Finset.sum_congr rfl fun x hx => ?_
              have hxk : x < k := Finset.mem_range.mp hx
              rw [hpow_agree m (x + 1) (by omega), ih (k + 1 - (x + 1)) (by omega)]
            rw [hsplitA, hsplitF, hmid]
            push_cast
            linarith
        have hAn_eq : PowerSeries.coeff (k + 1) (A ^ n) = PowerSeries.coeff (k + 1) (F ^ n) := by
          have h1 := congr_arg (PowerSeries.coeff (k + 1)) hAeq
          have h2 := congr_arg (PowerSeries.coeff (k + 1)) hFeq
          rw [map_sub] at h1 h2
          have hX1 : PowerSeries.coeff (k + 1) ((n : PowerSeries ℚ) ^ 2 * PowerSeries.X * A ^ (n + 1)) =
              (n : ℚ) ^ 2 * PowerSeries.coeff k (A ^ (n + 1)) := by
            rw [show (n : PowerSeries ℚ) ^ 2 * PowerSeries.X * A ^ (n + 1) =
                PowerSeries.C ((n : ℚ) ^ 2) * (PowerSeries.X * A ^ (n + 1)) by
                  rw [map_pow, map_natCast]; ring,
              PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul]
          have hX2 : PowerSeries.coeff (k + 1) ((n : PowerSeries ℚ) ^ 2 * PowerSeries.X * F ^ (n + 1)) =
              (n : ℚ) ^ 2 * PowerSeries.coeff k (F ^ (n + 1)) := by
            rw [show (n : PowerSeries ℚ) ^ 2 * PowerSeries.X * F ^ (n + 1) =
                PowerSeries.C ((n : ℚ) ^ 2) * (PowerSeries.X * F ^ (n + 1)) by
                  rw [map_pow, map_natCast]; ring,
              PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul]
          rw [hX1] at h1
          rw [hX2] at h2
          rw [hpow_agree (n + 1) k (le_refl k)] at h1
          linarith
        have hd := hpow_diff n
        rw [hAn_eq, sub_self] at hd
        have hzero : PowerSeries.coeff (k + 1) A - PowerSeries.coeff (k + 1) F = 0 :=
          (mul_eq_zero.mp hd.symm).resolve_left hn_ne
        exact sub_eq_zero.mp hzero
  -- Now evaluate coeff (n - 1) F and coeff (2 * n - 1) F!
  rw [hAF]
  simp only [F, PowerSeries.coeff_mk]
  constructor
  · -- k = n - 1: raney (1/n) (1 + 1/n) (n - 1) = 1/n!
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    have hsub1 : m + 2 - 1 = m + 1 := by omega
    have hsub2 : 2 * (m + 2) - 3 = 2 * m + 1 := by omega
    rw [hsub1, hsub2]
    simp only [raney, r, t]
    have hprod : ∏ j ∈ Finset.range m,
        (((m + 2 : ℕ) : ℚ)⁻¹ + (1 + ((m + 2 : ℕ) : ℚ)⁻¹) * ((m : ℚ) + 1) - ((j : ℚ) + 1)) =
        ((m + 1).factorial : ℚ) := by
      have hterm : ∀ j ∈ Finset.range m,
          ((m + 2 : ℕ) : ℚ)⁻¹ + (1 + ((m + 2 : ℕ) : ℚ)⁻¹) * ((m : ℚ) + 1) - ((j : ℚ) + 1) =
          (((m + 1 - j : ℕ) : ℚ)) := by
        intro j hj
        have hjm : j < m := Finset.mem_range.mp hj
        have hne : ((m + 2 : ℕ) : ℚ) ≠ 0 := by positivity
        rw [Nat.cast_sub (by omega)]
        push_cast
        field_simp [hne]
        ring
      rw [Finset.prod_congr rfl hterm]
      have hfact_prod : ∀ d : ℕ, ∏ j ∈ Finset.range d, ((d + 1 - j : ℕ) : ℚ) = ((d + 1).factorial : ℚ) := by
        intro d
        induction d with
        | zero => simp
        | succ d ih =>
          rw [Finset.prod_range_succ']
          have h0 : ((d + 1 + 1 - 0 : ℕ) : ℚ) = ((d + 2 : ℕ) : ℚ) := by push_cast; ring
          rw [h0, mul_comm, Nat.factorial_succ, Nat.cast_mul]
          congr 1
          rw [← ih]
          refine Finset.prod_congr rfl fun j _ => ?_
          congr 1; omega
      exact hfact_prod m
    rw [hprod]
    have hfact_ne : ((m + 1).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hne : ((m + 2 : ℕ) : ℚ) ≠ 0 := by positivity
    rw [mul_div_assoc, div_self hfact_ne, mul_one]
    rw [show 2 * (m + 1) = (2 * m + 1) + 1 by omega, pow_succ, mul_assoc, mul_inv_cancel₀ hne, mul_one]
  · -- k = 2 * n - 1: raney (1/n) (1 + 1/n) (2 * n - 1) = 1!
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    have hsub1 : 2 * (m + 2) - 1 = 2 * m + 3 := by omega
    have hsub2 : 4 * (m + 2) - 2 = 4 * m + 6 := by omega
    rw [hsub1, hsub2]
    simp only [raney, r, t]
    have hprod : ∏ j ∈ Finset.range (2 * m + 2),
        (((m + 2 : ℕ) : ℚ)⁻¹ + (1 + ((m + 2 : ℕ) : ℚ)⁻¹) * ((2 * m + 2 : ℕ) + 1 : ℚ) - ((j : ℚ) + 1)) =
        (((2 * m + 4).factorial : ℚ) / 2) := by
      have hterm : ∀ j ∈ Finset.range (2 * m + 2),
          ((m + 2 : ℕ) : ℚ)⁻¹ + (1 + ((m + 2 : ℕ) : ℚ)⁻¹) * ((2 * m + 2 : ℕ) + 1 : ℚ) - ((j : ℚ) + 1) =
          (((2 * m + 4 - j : ℕ) : ℚ)) := by
        intro j hj
        have hjm : j < 2 * m + 2 := Finset.mem_range.mp hj
        have hne : ((m + 2 : ℕ) : ℚ) ≠ 0 := by positivity
        rw [Nat.cast_sub (by omega)]
        push_cast
        field_simp [hne]
        ring
      rw [Finset.prod_congr rfl hterm]
      have hfact_prod : ∀ d : ℕ, ∏ j ∈ Finset.range d, ((d + 2 - j : ℕ) : ℚ) = ((d + 2).factorial : ℚ) / 2 := by
        intro d
        induction d with
        | zero => simp
        | succ d ih =>
          rw [Finset.prod_range_succ']
          have h0 : ((d + 1 + 2 - 0 : ℕ) : ℚ) = ((d + 3 : ℕ) : ℚ) := by push_cast; ring
          rw [h0, mul_comm, Nat.factorial_succ, Nat.cast_mul, mul_div_assoc]
          congr 1
          rw [← ih]
          refine Finset.prod_congr rfl fun j _ => ?_
          congr 1; omega
      exact hfact_prod (2 * m + 2)
    rw [hprod]
    have hfact_succ : ((2 * m + 4).factorial : ℚ) = ((2 * m + 4 : ℕ) : ℚ) * ((2 * m + 3).factorial : ℚ) := by
      rw [Nat.factorial_succ, Nat.cast_mul]
    rw [hfact_succ]
    have hfact_ne : ((2 * m + 3).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hne : ((m + 2 : ℕ) : ℚ) ≠ 0 := by positivity
    have hrat : ((m + 2 : ℕ) : ℚ)⁻¹ * (((2 * m + 4 : ℕ) : ℚ) * ((2 * m + 3).factorial : ℚ) / 2) /
        ((2 * m + 3).factorial : ℚ) = 1 := by
      field_simp [hne, hfact_ne]
      push_cast; ring
    rw [hrat, mul_one]
    rw [show 2 * (2 * m + 3) = 4 * m + 6 by omega]

end OMA.P_oeis_a078534

theorem OMA.solution : type_of% @OMA.S_oeis_a078534.main :=
  OMA.P_oeis_a078534.main_proved
