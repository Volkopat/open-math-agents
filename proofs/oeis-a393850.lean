import OMAStatements.S_oeis_a393850
import Mathlib

namespace OMA.P_oeis_a393850

-- 1. Key derivative-vanishing lemma for Lagrange inversion (pure PowerSeries ℚ, zero Laurent series!):
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

-- 2. Power series X-shift divisibility helper: coeff m (X^k * F) = 0 for m < k
private lemma coeff_X_pow_mul_lt {R : Type*} [CommSemiring R] (k m : ℕ) (h : m < k)
    (F : PowerSeries R) : PowerSeries.coeff m (PowerSeries.X ^ k * F) = 0 := by
  rw [PowerSeries.coeff_X_pow_mul', if_neg (by omega)]

-- 3. Lagrange inversion: given A, B with A * B = 1, coeff 0 A = 1, G = X * B,
-- and f : ℕ → ℚ with f 0 = 0 and ∀ m ≥ 1, ∑ k ∈ range (m+1), f k * coeff m (G^k) = if m = 1 then 1 else 0,
-- we have ∀ n ≥ 1, n * f n = coeff (n - 1) (A ^ n)!
private lemma lagrange_inversion (A B : PowerSeries ℚ) (hAB : A * B = 1)
    (hA0 : PowerSeries.coeff 0 A = 1) (f : ℕ → ℚ) (hf0 : f 0 = 0)
    (hFG : ∀ m : ℕ, 1 ≤ m →
      ∑ k ∈ Finset.range (m + 1), f k * PowerSeries.coeff m ((PowerSeries.X * B) ^ k) =
      if m = 1 then 1 else 0) :
    ∀ n : ℕ, 1 ≤ n → (n : ℚ) * f n = PowerSeries.coeff (n - 1) (A ^ n) := by
  set G : PowerSeries ℚ := PowerSeries.X * B
  have hB0 : PowerSeries.coeff 0 B = 1 := by
    have h0 := congr_arg (PowerSeries.coeff 0) hAB
    rw [PowerSeries.coeff_zero_eq_constantCoeff, map_mul, map_one] at h0
    rw [PowerSeries.coeff_zero_eq_constantCoeff] at hA0 ⊢
    rw [hA0, one_mul] at h0
    exact h0
  -- Truncate F to degree n: F_n(G) ≡ X (mod X^(n+1)), so (F_n(G))' ≡ 1 (mod X^n)!
  intro n hn
  let H : PowerSeries ℚ := ∑ k ∈ Finset.range (n + 1), PowerSeries.C (f k) * G ^ k
  have hH_agree : ∀ m : ℕ, m ≤ n → PowerSeries.coeff m H = if m = 1 then 1 else 0 := by
    intro m hm
    simp only [H, map_sum, PowerSeries.coeff_C_mul]
    cases m with
    | zero =>
      refine Finset.sum_eq_zero fun k _ => ?_
      cases k with
      | zero => simp [hf0]
      | succ k =>
        have : PowerSeries.coeff 0 (G ^ (k + 1)) = 0 := by
          simp [G, mul_pow, PowerSeries.coeff_zero_eq_constantCoeff]
        rw [this, mul_zero]
    | succ m =>
      have hsub : ∑ k ∈ Finset.range (n + 1), f k * PowerSeries.coeff (m + 1) (G ^ k) =
          ∑ k ∈ Finset.range (m + 2), f k * PowerSeries.coeff (m + 1) (G ^ k) := by
        symm
        refine Finset.sum_subset (Finset.range_mono (by omega)) fun k _ hk => ?_
        simp only [Finset.mem_range, not_lt] at hk
        have h0 : PowerSeries.coeff (m + 1) (G ^ k) = 0 := by
          rw [show G ^ k = PowerSeries.X ^ k * B ^ k by simp [G, mul_pow]]
          exact coeff_X_pow_mul_lt k (m + 1) (by omega) (B ^ k)
        rw [h0, mul_zero]
      rw [hsub]
      exact hFG (m + 1) (Nat.succ_pos m)
  have hdH_agree : ∀ m : ℕ, m < n → PowerSeries.coeff m (PowerSeries.derivative ℚ H) = if m = 0 then 1 else 0 := by
    intro m hm
    rw [PowerSeries.coeff_derivative, hH_agree (m + 1) (by omega)]
    cases m with
    | zero => simp
    | succ m => simp
  -- Multiply derivative H by A^n and take coeff (n - 1)!
  have hmul_rhs : PowerSeries.coeff (n - 1) (PowerSeries.derivative ℚ H * A ^ n) =
      PowerSeries.coeff (n - 1) (A ^ n) := by
    rw [PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (f := fun i j => PowerSeries.coeff i (PowerSeries.derivative ℚ H) * PowerSeries.coeff j (A ^ n))]
    rw [Finset.sum_eq_single 0]
    · rw [hdH_agree 0 (by omega)]; simp
    · intro i hi hi0
      have hin : i ≤ n - 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      rw [hdH_agree i (by omega), if_neg hi0, zero_mul]
    · intro h; exact absurd (Finset.mem_range.mpr (Nat.succ_pos _)) h
  -- Compute derivative H directly!
  have hdH : PowerSeries.derivative ℚ H =
      ∑ k ∈ Finset.range (n + 1), PowerSeries.C ((k : ℚ) * f k) * G ^ (k - 1) * PowerSeries.derivative ℚ G := by
    simp only [H, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Derivation.leibniz, PowerSeries.derivative_C, smul_zero, add_zero,
      PowerSeries.derivative_pow, smul_eq_mul]
    have hCk : (k : PowerSeries ℚ) = PowerSeries.C (k : ℚ) := (map_natCast _ k).symm
    rw [hCk, map_mul PowerSeries.C (k : ℚ) (f k)]; ring
  -- Compute G' * A^2 = A - X * A'
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
  -- Evaluate coeff (n - 1) (derivative H * A^n) term by term!
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

-- 4. Frobenius in PowerSeries (ZMod 2): coeff (2*m) (F^2) = coeff m F, coeff (2*m+1) (F^2) = 0
private lemma coeff_sq_zmod2 (F : PowerSeries (ZMod 2)) (m : ℕ) :
    PowerSeries.coeff m (F ^ 2) = if 2 ∣ m then PowerSeries.coeff (m / 2) F else 0 := by
  rw [pow_two, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (f := fun i j => PowerSeries.coeff i F * PowerSeries.coeff j F)]
  have hchar : ∀ x : ZMod 2, x + x = 0 := by decide
  have hsq : ∀ x : ZMod 2, x * x = x := by decide
  -- Pair i with m - i!
  have hpair : ∑ i ∈ Finset.range (m + 1), PowerSeries.coeff i F * PowerSeries.coeff (m - i) F =
      ∑ i ∈ (Finset.range (m + 1)).filter (fun i => 2 * i = m),
        PowerSeries.coeff i F * PowerSeries.coeff (m - i) F := by
    have hpart : Finset.range (m + 1) =
        ((Finset.range (m + 1)).filter (fun i => 2 * i = m)) ∪
        (((Finset.range (m + 1)).filter (fun i => 2 * i < m)) ∪
         ((Finset.range (m + 1)).filter (fun i => m < 2 * i))) := by
      ext i; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_range]
      constructor
      · intro h
        rcases lt_trichotomy (2 * i) m with h1 | h2 | h3
        · exact Or.inr (Or.inl ⟨h, h1⟩)
        · exact Or.inl ⟨h, h2⟩
        · exact Or.inr (Or.inr ⟨h, h3⟩)
      · rintro (⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    have hd1 : Disjoint ((Finset.range (m + 1)).filter (fun i => 2 * i = m))
        (((Finset.range (m + 1)).filter (fun i => 2 * i < m)) ∪
         ((Finset.range (m + 1)).filter (fun i => m < 2 * i))) := by
      rw [Finset.disjoint_left]; intro i h1 h2
      simp only [Finset.mem_filter, Finset.mem_union] at h1 h2
      rcases h2 with ⟨_, hlt⟩ | ⟨_, hgt⟩ <;> omega
    have hd2 : Disjoint ((Finset.range (m + 1)).filter (fun i => 2 * i < m))
        ((Finset.range (m + 1)).filter (fun i => m < 2 * i)) := by
      rw [Finset.disjoint_left]; intro i h1 h2
      simp only [Finset.mem_filter] at h1 h2; omega
    conv_lhs => rw [hpart]
    rw [Finset.sum_union hd1, Finset.sum_union hd2]
    have hswap : ∑ i ∈ (Finset.range (m + 1)).filter (fun i => m < 2 * i),
          PowerSeries.coeff i F * PowerSeries.coeff (m - i) F =
        ∑ i ∈ (Finset.range (m + 1)).filter (fun i => 2 * i < m),
          PowerSeries.coeff i F * PowerSeries.coeff (m - i) F := by
      refine Finset.sum_nbij' (fun i => m - i) (fun i => m - i) ?_ ?_ ?_ ?_ ?_
      · intro i hi; simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢; omega
      · intro i hi; simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢; omega
      · intro i hi; simp only [Finset.mem_filter, Finset.mem_range] at hi; omega
      · intro i hi; simp only [Finset.mem_filter, Finset.mem_range] at hi; omega
      · intro i hi
        simp only [Finset.mem_filter, Finset.mem_range] at hi
        rw [Nat.sub_sub_self (by omega), mul_comm]
    rw [hswap, hchar, add_zero]
  rw [hpair]
  by_cases h2m : 2 ∣ m
  · obtain ⟨q, rfl⟩ := h2m
    simp only [dvd_mul_right, ↓reduceIte, Nat.mul_div_right _ (by omega : 0 < 2)]
    rw [Finset.sum_eq_single q]
    · rw [show 2 * q - q = q by omega, hsq]
    · intro i hi hiq
      simp only [Finset.mem_filter] at hi; omega
    · intro h
      have hq : q ∈ (Finset.range (2 * q + 1)).filter (fun i => 2 * i = 2 * q) :=
        Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), rfl⟩
      exact absurd hq h
  · simp only [h2m, ↓reduceIte]
    refine Finset.sum_eq_zero fun i hi => ?_
    simp only [Finset.mem_filter] at hi
    exfalso; apply h2m; exact ⟨i, hi.2.symm⟩

-- 5. Recursive integer compositional inverse sequence of G (with coeff 0 G = 0, coeff 1 G = 1)
private noncomputable def compInvSeq (G : PowerSeries ℤ) : ℕ → ℤ
  | 0 => 0
  | m + 1 =>
      (if m = 0 then 1 else 0) -
        ∑ k ∈ (Finset.range (m + 1)).attach,
          compInvSeq G k.1 * PowerSeries.coeff (m + 1) (G ^ k.1)
decreasing_by
  exact Finset.mem_range.mp k.2

private lemma compInvSeq_sum (G : PowerSeries ℤ) (hdiag : ∀ k : ℕ, PowerSeries.coeff k (G ^ k) = 1)
    (m : ℕ) (hm : 1 ≤ m) :
    ∑ k ∈ Finset.range (m + 1), compInvSeq G k * PowerSeries.coeff m (G ^ k) =
    if m = 1 then 1 else 0 := by
  cases m with
  | zero => omega
  | succ m =>
    rw [Finset.sum_range_succ, hdiag (m + 1), mul_one]
    conv_lhs => arg 2; rw [compInvSeq]
    have hattach : (∑ k ∈ (Finset.range (m + 1)).attach,
          compInvSeq G k.1 * PowerSeries.coeff (m + 1) (G ^ k.1)) =
        ∑ k ∈ Finset.range (m + 1), compInvSeq G k * PowerSeries.coeff (m + 1) (G ^ k) :=
      Finset.sum_attach (Finset.range (m + 1))
        (fun k => compInvSeq G k * PowerSeries.coeff (m + 1) (G ^ k))
    rw [hattach]
    have hiff : m = 0 ↔ m + 1 = 1 := by omega
    simp only [hiff]
    ring

-- 6. Frobenius for even power: coeff (2*m) (F^(2*r)) = coeff m (F^r) in PowerSeries (ZMod 2)
private lemma coeff_pow_two_mul_zmod2 (F : PowerSeries (ZMod 2)) (r m : ℕ) :
    PowerSeries.coeff (2 * m) (F ^ (2 * r)) = PowerSeries.coeff m (F ^ r) := by
  rw [mul_comm 2 r, pow_mul, coeff_sq_zmod2]
  simp [dvd_mul_right, Nat.mul_div_right _ (by omega : 0 < 2)]

private theorem main_proved :
    ∀ a : ℕ → ℤ,
      a 0 = 1 →
      a 1 = 1 →
      (let A : PowerSeries ℤ := PowerSeries.mk a
       ∀ n : ℕ, 1 ≤ n →
         PowerSeries.coeff n (A ^ (n + 1)) =
           (n : ℤ) * ((n : ℤ) + 1) * PowerSeries.coeff (n - 1) (A ^ (n + 1))) →
      ∀ n : ℕ, 1 ≤ n →
        (Odd (a n) ↔ ∃ k : ℕ, n = 2 ^ k) := by
  intro a ha0 ha1 hcond
  let A_Z : PowerSeries ℤ := PowerSeries.mk a
  let A_Q : PowerSeries ℚ := PowerSeries.map (Int.castRingHom ℚ) A_Z
  have hA_Q_0 : PowerSeries.coeff 0 A_Q = 1 := by
    simp [A_Q, A_Z, ha0]
  have hA_Z_unit : IsUnit A_Z := by
    rw [PowerSeries.isUnit_iff_constantCoeff]; simp [A_Z, ha0]
  obtain ⟨u, hu⟩ := hA_Z_unit
  let B_Z : PowerSeries ℤ := ↑u⁻¹
  have hAB_Z : A_Z * B_Z = 1 := by
    have : (u : PowerSeries ℤ) * (↑u⁻¹ : PowerSeries ℤ) = 1 := Units.mul_inv u
    rw [hu] at this
    exact this
  let B_Q : PowerSeries ℚ := PowerSeries.map (Int.castRingHom ℚ) B_Z
  have hAB_Q : A_Q * B_Q = 1 := by
    have := congr_arg (PowerSeries.map (Int.castRingHom ℚ)) hAB_Z
    simp only [map_mul, map_one] at this
    exact this
  let G_Z : PowerSeries ℤ := PowerSeries.X * B_Z
  have hB_Z_0 : PowerSeries.coeff 0 B_Z = 1 := by
    have h0 := congr_arg (PowerSeries.coeff 0) hAB_Z
    rw [PowerSeries.coeff_zero_eq_constantCoeff, map_mul, map_one] at h0
    have hA0' : PowerSeries.constantCoeff A_Z = 1 := by simp [A_Z, ha0]
    rw [hA0', one_mul] at h0
    rwa [PowerSeries.coeff_zero_eq_constantCoeff]
  have hG_diag : ∀ k : ℕ, PowerSeries.coeff k (G_Z ^ k) = 1 := by
    intro k
    rw [show G_Z ^ k = PowerSeries.X ^ k * B_Z ^ k by simp [G_Z, mul_pow],
      PowerSeries.coeff_X_pow_mul']
    simp only [le_refl, ↓reduceIte, Nat.sub_self, PowerSeries.coeff_zero_eq_constantCoeff, map_pow]
    rw [← PowerSeries.coeff_zero_eq_constantCoeff, hB_Z_0, one_pow]
  -- Define integer sequence f_Z = compInvSeq G_Z
  let f_Z : ℕ → ℤ := compInvSeq G_Z
  have hf_Z_0 : f_Z 0 = 0 := by simp [f_Z, compInvSeq]
  have hf_Z_sum : ∀ m : ℕ, 1 ≤ m →
      ∑ k ∈ Finset.range (m + 1), f_Z k * PowerSeries.coeff m (G_Z ^ k) =
      if m = 1 then 1 else 0 := compInvSeq_sum G_Z hG_diag
  -- Cast to ℚ and apply Lagrange inversion!
  have hf_lag : ∀ m : ℕ, 1 ≤ m → (m : ℤ) * f_Z m = PowerSeries.coeff (m - 1) (A_Z ^ m) := by
    intro m hm
    have hFG_Q : ∀ r : ℕ, 1 ≤ r →
        ∑ k ∈ Finset.range (r + 1), (f_Z k : ℚ) * PowerSeries.coeff r ((PowerSeries.X * B_Q) ^ k) =
        if r = 1 then 1 else 0 := by
      intro r hr
      have h1 := congr_arg (Int.cast : ℤ → ℚ) (hf_Z_sum r hr)
      simp only [Int.cast_sum, Int.cast_mul, apply_ite (Int.cast : ℤ → ℚ), Int.cast_one,
        Int.cast_zero] at h1
      convert h1 using 2 with k _
      have hmap : PowerSeries.map (Int.castRingHom ℚ) (G_Z ^ k) = (PowerSeries.X * B_Q) ^ k := by
        simp [G_Z, B_Q]
      rw [← hmap, PowerSeries.coeff_map, eq_intCast]
    have hl := lagrange_inversion A_Q B_Q hAB_Q hA_Q_0 (fun k => (f_Z k : ℚ)) (by simp [hf_Z_0]) hFG_Q m hm
    have hA_map : PowerSeries.map (Int.castRingHom ℚ) (A_Z ^ m) = A_Q ^ m := by simp [A_Q]
    rw [← hA_map, PowerSeries.coeff_map, eq_intCast] at hl
    exact_mod_cast hl
  -- Now deduce f_Z 1 = 1, f_Z 2 = 1, and 2 ∣ f_Z k for ALL k ≥ 3!
  have hf_Z_1 : f_Z 1 = 1 := by
    have h1 := hf_lag 1 (by omega)
    simp [A_Z, ha0] at h1
    exact h1
  have hf_Z_2 : f_Z 2 = 1 := by
    have h2 := hf_lag 2 (by omega)
    have hc1 := hcond 1 (by omega)
    simp only [Nat.sub_self, Nat.cast_one, one_mul, show (1 : ℤ) + 1 = 2 by norm_num] at hc1
    have hc0 : PowerSeries.coeff 0 (A_Z ^ 2) = 1 := by
      rw [PowerSeries.coeff_zero_eq_constantCoeff, map_pow]; simp [A_Z, ha0]
    rw [hc1, hc0] at h2
    omega
  have hf_Z_even : ∀ k : ℕ, 3 ≤ k → (2 : ℤ) ∣ f_Z k := by
    intro k hk
    cases k with
    | zero => omega
    | succ m =>
      have hm2 : 2 ≤ m := by omega
      have hlag := hf_lag (m + 1) (by omega)
      simp only [Nat.add_sub_cancel] at hlag
      have hc := hcond m (by omega)
      change PowerSeries.coeff m (A_Z ^ (m + 1)) = _ at hc
      rw [hc] at hlag
      have hm1_ne : ((m : ℤ) + 1) ≠ 0 := by omega
      have hfm : f_Z (m + 1) = (m : ℤ) * PowerSeries.coeff (m - 1) (A_Z ^ (m + 1)) := by
        have h1 : ((m : ℤ) + 1) * f_Z (m + 1) =
            ((m : ℤ) + 1) * ((m : ℤ) * PowerSeries.coeff (m - 1) (A_Z ^ (m + 1))) := by
          push_cast at hlag; linarith
        exact mul_left_cancel₀ hm1_ne h1
      rw [hfm]
      rcases Nat.even_or_odd m with ⟨r, hr⟩ | ⟨r, hr⟩
      · have : (2 : ℤ) ∣ (m : ℤ) := ⟨(r : ℤ), by omega⟩
        exact dvd_mul_of_dvd_left this _
      · -- m = 2*r + 1 (r >= 1): coeff (2*r) (A_Z^(2*r + 2)) ≡ coeff r (A_Z^(r + 1)) = r*(r+1)*... ≡ 0 (mod 2)!
        have hr1 : 1 ≤ r := by omega
        have hA2_eq : PowerSeries.coeff (m - 1) (PowerSeries.map (Int.castRingHom (ZMod 2)) (A_Z ^ (m + 1))) = 0 := by
          rw [map_pow, show m - 1 = 2 * r by omega, show m + 1 = 2 * (r + 1) by omega,
            coeff_pow_two_mul_zmod2, ← map_pow, PowerSeries.coeff_map, eq_intCast]
          have hcr := hcond r hr1
          rw [hcr]
          have h2rr : (2 : ℤ) ∣ (r : ℤ) * ((r : ℤ) + 1) := by
            rcases Nat.even_or_odd r with ⟨t, ht⟩ | ⟨t, ht⟩
            · exact ⟨(t : ℤ) * ((r : ℤ) + 1), by push_cast [ht]; ring⟩
            · exact ⟨(r : ℤ) * ((t : ℤ) + 1), by push_cast [ht]; ring⟩
          exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mpr (dvd_mul_of_dvd_left h2rr _)
        rw [PowerSeries.coeff_map, eq_intCast] at hA2_eq
        have hdvd : (2 : ℤ) ∣ PowerSeries.coeff (m - 1) (A_Z ^ (m + 1)) :=
          (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp hA2_eq
        exact dvd_mul_of_dvd_right hdvd _
  -- Reduce to PowerSeries (ZMod 2): G2 + G2^2 = X!
  let A2 : PowerSeries (ZMod 2) := PowerSeries.map (Int.castRingHom (ZMod 2)) A_Z
  let B2 : PowerSeries (ZMod 2) := PowerSeries.map (Int.castRingHom (ZMod 2)) B_Z
  let G2 : PowerSeries (ZMod 2) := PowerSeries.map (Int.castRingHom (ZMod 2)) G_Z
  have hAB2 : A2 * B2 = 1 := by
    have := congr_arg (PowerSeries.map (Int.castRingHom (ZMod 2))) hAB_Z
    simpa [A2, B2] using this
  have hG2_eq : G2 = PowerSeries.X * B2 := by simp [G2, G_Z, B2]
  have hG2_quad : G2 + G2 ^ 2 = PowerSeries.X := by
    ext m
    rw [map_add, PowerSeries.coeff_X]
    cases m with
    | zero =>
      simp only [PowerSeries.coeff_zero_eq_constantCoeff, map_pow, hG2_eq, map_mul,
        PowerSeries.constantCoeff_X, zero_mul, zero_pow (by omega : 2 ≠ 0), add_zero]
      rfl
    | succ m =>
      have hsum := congr_arg (Int.cast : ℤ → ZMod 2) (hf_Z_sum (m + 1) (Nat.succ_pos m))
      simp only [Int.cast_sum, Int.cast_mul, apply_ite (Int.cast : ℤ → ZMod 2), Int.cast_one,
        Int.cast_zero] at hsum
      have hterm : ∀ k ∈ Finset.range (m + 2),
          (f_Z k : ZMod 2) * ((PowerSeries.coeff (m + 1) (G_Z ^ k) : ℤ) : ZMod 2) =
          if k = 1 then PowerSeries.coeff (m + 1) G2
          else if k = 2 then PowerSeries.coeff (m + 1) (G2 ^ 2)
          else 0 := by
        intro k _
        have hGk : ((PowerSeries.coeff (m + 1) (G_Z ^ k) : ℤ) : ZMod 2) = PowerSeries.coeff (m + 1) (G2 ^ k) := by
          have hmp : PowerSeries.map (Int.castRingHom (ZMod 2)) (G_Z ^ k) = G2 ^ k := by
            rw [map_pow]
          rw [← hmp, PowerSeries.coeff_map, eq_intCast]
        rw [hGk]
        rcases k with _ | _ | _ | k
        · simp [hf_Z_0]
        · simp [hf_Z_1]
        · simp [hf_Z_2]
        · have hz : (f_Z (k + 3) : ZMod 2) = 0 :=
            (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mpr (hf_Z_even (k + 3) (by omega))
          simp [hz]
      rw [Finset.sum_congr rfl hterm] at hsum
      cases m with
      | zero =>
        simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
          OfNat.zero_ne_ofNat, ↓reduceIte] at hsum
        have hG2sq1 : PowerSeries.coeff 1 (G2 ^ 2) = 0 := by
          rw [coeff_sq_zmod2]; simp
        rw [hG2sq1, add_zero]
        simpa using hsum
      | succ m =>
        have h1m : 1 ∈ Finset.range (m + 3) := Finset.mem_range.mpr (by omega)
        have h2m : 2 ∈ (Finset.range (m + 3)).erase 1 :=
          Finset.mem_erase.mpr ⟨by omega, Finset.mem_range.mpr (by omega)⟩
        rw [← Finset.add_sum_erase _ _ h1m, ← Finset.add_sum_erase _ _ h2m] at hsum
        simp only [↓reduceIte, show (2 : ℕ) ≠ 1 by omega] at hsum
        have hrest : ∑ x ∈ ((Finset.range (m + 3)).erase 1).erase 2,
              (if x = 1 then PowerSeries.coeff (m + 2) G2
               else if x = 2 then PowerSeries.coeff (m + 2) (G2 ^ 2) else 0) = 0 := by
          refine Finset.sum_eq_zero fun x hx => ?_
          have hx2 := (Finset.mem_erase.mp hx).1
          have hx1 := (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).1
          simp [hx1, hx2]
        rw [hrest, add_zero] at hsum
        simpa [show m + 2 ≠ 1 by omega] using hsum
  -- Multiply G2 + G2^2 = X by A2^2 => X * A2 + X^2 = X * A2^2 => A2^2 = A2 + X!
  have hXA2 : PowerSeries.X * (A2 ^ 2) = PowerSeries.X * (A2 + PowerSeries.X) := by
    have hmul := congr_arg (· * A2 ^ 2) hG2_quad
    have h1 : (G2 + G2 ^ 2) * A2 ^ 2 = PowerSeries.X * (A2 + PowerSeries.X) := by
      rw [hG2_eq, add_mul, mul_pow]
      calc PowerSeries.X * B2 * A2 ^ 2 + PowerSeries.X ^ 2 * B2 ^ 2 * A2 ^ 2
          = PowerSeries.X * ((A2 * B2) * A2) + PowerSeries.X ^ 2 * (A2 * B2) ^ 2 := by ring
        _ = PowerSeries.X * (1 * A2) + PowerSeries.X ^ 2 * 1 ^ 2 := by rw [hAB2]
        _ = PowerSeries.X * (A2 + PowerSeries.X) := by ring
    rw [h1] at hmul
    exact hmul.symm
  have hA2_quad : A2 ^ 2 = A2 + PowerSeries.X := by
    ext m
    have hm := congr_arg (PowerSeries.coeff (m + 1)) hXA2
    rwa [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_succ_X_mul] at hm
  -- Extract recurrence on coeff n A2 and prove coeff n A2 = 1 ↔ ∃ k, n = 2^k for n ≥ 1!
  have hA2_rec : ∀ n : ℕ, 1 ≤ n → (PowerSeries.coeff n A2 = 1 ↔ ∃ k : ℕ, n = 2 ^ k) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn
      by_cases hn1 : n = 1
      · subst hn1
        simp only [A2, A_Z, PowerSeries.coeff_map, PowerSeries.coeff_mk, eq_intCast, ha1, Int.cast_one,
          true_iff]
        exact ⟨0, rfl⟩
      · have hcn := congr_arg (PowerSeries.coeff n) hA2_quad
        rw [coeff_sq_zmod2, map_add, PowerSeries.coeff_X, if_neg hn1, add_zero] at hcn
        by_cases h2n : 2 ∣ n
        · obtain ⟨m, rfl⟩ := h2n
          have hm1 : 1 ≤ m := by omega
          simp only [dvd_mul_right, ↓reduceIte, Nat.mul_div_right _ (by omega : 0 < 2)] at hcn
          rw [← hcn, ih m (by omega) hm1]
          constructor
          · rintro ⟨k, rfl⟩; exact ⟨k + 1, by rw [pow_succ']⟩
          · rintro ⟨k, hk⟩
            cases k with
            | zero => omega
            | succ k => exact ⟨k, by rw [pow_succ'] at hk; omega⟩
        · simp only [h2n, ↓reduceIte] at hcn
          rw [← hcn]
          constructor
          · intro h; exact absurd h (by decide)
          · rintro ⟨k, rfl⟩
            cases k with
            | zero => exact absurd rfl hn1
            | succ k => exact absurd ⟨2 ^ k, by rw [pow_succ']⟩ h2n
  intro n hn
  have hodd_iff : Odd (a n) ↔ ((a n : ℤ) : ZMod 2) = 1 := by
    constructor
    · rintro ⟨r, hr⟩
      rw [hr]; push_cast
      have h2 : (2 : ZMod 2) = 0 := by decide
      rw [h2, zero_mul, zero_add]
    · intro h
      have hne0 : ((a n : ℤ) : ZMod 2) ≠ 0 := by rw [h]; decide
      have hndvd : ¬((2 : ℤ) ∣ a n) := fun hd => hne0 ((ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mpr hd)
      have hmod : a n % 2 = 1 := by omega
      exact ⟨a n / 2, by omega⟩
  rw [hodd_iff]
  simpa [A2, A_Z, PowerSeries.coeff_map, PowerSeries.coeff_mk] using hA2_rec n hn

end OMA.P_oeis_a393850

theorem OMA.solution : type_of% @OMA.S_oeis_a393850.main :=
  OMA.P_oeis_a393850.main_proved
