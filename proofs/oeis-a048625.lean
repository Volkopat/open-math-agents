import OMAStatements.S_oeis_a048625
import Mathlib.Tactic

namespace OMA.P_oeis_a048625

private def b : ℕ → ℤ
  | 0 => 4
  | 1 => 6
  | 2 => 9
  | n + 3 => b (n + 2) + b n

private def d (n : ℕ) : ℤ :=
  b (n + 1) ^ 2 - b n * b (n + 2)

private lemma b_pos_mono (n : ℕ) : 0 < b n ∧ b n ≤ b (n + 1) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn3 : n < 3
    · interval_cases n
      · decide
      · decide
      · exact ⟨by decide, by rw [show b 3 = b 2 + b 0 from rfl]; decide⟩
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
      have ih0 := ih k (by omega)
      have ih1 := ih (k + 1) (by omega)
      have ih2 := ih (k + 2) (by omega)
      have hb12 : b (k + 1 + 1) = b (k + 2) := rfl
      have hb23 : b (k + 2 + 1) = b (k + 3) := rfl
      have hb34 : b (k + 3 + 1) = b (k + 4) := rfl
      have hb3 : b (k + 3) = b (k + 2) + b k := rfl
      have hb4 : b (k + 4) = b (k + 3) + b (k + 1) := rfl
      omega

private lemma b_seven (n : ℕ) :
    b (n + 7) = 4 * b (n + 2) + 2 * b (n + 1) + 3 * b n := by
  have h3 : b (n + 3) = b (n + 2) + b n := rfl
  have h4 : b (n + 4) = b (n + 3) + b (n + 1) := rfl
  have h5 : b (n + 5) = b (n + 4) + b (n + 2) := rfl
  have h6 : b (n + 6) = b (n + 5) + b (n + 3) := rfl
  have h7 : b (n + 7) = b (n + 6) + b (n + 4) := rfl
  omega

private lemma nine_mul_b_le (n : ℕ) : 9 * b n ≤ b (n + 7) := by
  have h0 := b_pos_mono n
  have h1 := b_pos_mono (n + 1)
  have hb12 : b (n + 1 + 1) = b (n + 2) := rfl
  have h7 := b_seven n
  omega

private lemma d_rec (n : ℕ) : d (n + 3) = d n - d (n + 1) := by
  have h3 : b (n + 3) = b (n + 2) + b n := rfl
  have h4 : b (n + 4) = b (n + 3) + b (n + 1) := rfl
  have h5 : b (n + 5) = b (n + 4) + b (n + 2) := rfl
  dsimp only [d]
  rw [h5, h4, h3]
  ring

private lemma d_seven (n : ℕ) :
    d (n + 7) = d n - 2 * d (n + 2) ∧
    d (n + 8) = -2 * d n + 3 * d (n + 1) ∧
    d (n + 9) = -2 * d (n + 1) + 3 * d (n + 2) := by
  have h3 : d (n + 3) = d n - d (n + 1) := d_rec n
  have h4 : d (n + 4) = d (n + 1) - d (n + 2) := d_rec (n + 1)
  have h5 : d (n + 5) = d (n + 2) - d (n + 3) := d_rec (n + 2)
  have h6 : d (n + 6) = d (n + 3) - d (n + 4) := d_rec (n + 3)
  have h7 : d (n + 7) = d (n + 4) - d (n + 5) := d_rec (n + 4)
  have h8 : d (n + 8) = d (n + 5) - d (n + 6) := d_rec (n + 5)
  have h9 : d (n + 9) = d (n + 6) - d (n + 7) := d_rec (n + 6)
  refine ⟨by omega, by omega, by omega⟩

private def M (n : ℕ) : ℤ :=
  max |d n| (max |d (n + 1)| |d (n + 2)|)

private lemma M_seven (n : ℕ) : M (n + 7) ≤ 5 * M n := by
  obtain ⟨h7, h8, h9⟩ := d_seven n
  have hd0 : |d n| ≤ M n := le_max_left _ _
  have hd1 : |d (n + 1)| ≤ M n := le_trans (le_max_left _ _) (le_max_right _ _)
  have hd2 : |d (n + 2)| ≤ M n := le_trans (le_max_right _ _) (le_max_right _ _)
  have habs7 : |d (n + 7)| ≤ 5 * M n := by
    rw [h7]
    calc
      |d n - 2 * d (n + 2)| ≤ |d n| + |2 * d (n + 2)| := abs_sub _ _
      _ = |d n| + 2 * |d (n + 2)| := by rw [abs_mul]; norm_num
      _ ≤ 5 * M n := by linarith [abs_nonneg (d n), abs_nonneg (d (n + 2))]
  have habs8 : |d (n + 8)| ≤ 5 * M n := by
    rw [h8]
    calc
      |-2 * d n + 3 * d (n + 1)| ≤ |-2 * d n| + |3 * d (n + 1)| := abs_add_le _ _
      _ = 2 * |d n| + 3 * |d (n + 1)| := by rw [abs_mul, abs_mul]; norm_num
      _ ≤ 5 * M n := by linarith
  have habs9 : |d (n + 9)| ≤ 5 * M n := by
    rw [h9]
    calc
      |-2 * d (n + 1) + 3 * d (n + 2)| ≤ |-2 * d (n + 1)| + |3 * d (n + 2)| := abs_add_le _ _
      _ = 2 * |d (n + 1)| + 3 * |d (n + 2)| := by rw [abs_mul, abs_mul]; norm_num
      _ ≤ 5 * M n := by linarith
  exact max_le habs7 (max_le habs8 habs9)

private lemma two_M_lt_b {n : ℕ} (hn : 3 ≤ n) : 2 * M n < b n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn10 : n < 10
    · interval_cases n <;> decide
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 7 := ⟨n - 7, by omega⟩
      have hih := ih k (by omega) (by omega)
      have hpos := (b_pos_mono k).1
      have hM := M_seven k
      have hb := nine_mul_b_le k
      omega

private lemma d_bounds (n : ℕ) : -b n < 2 * d n ∧ 2 * d n ≤ b n := by
  by_cases hn3 : n < 3
  · interval_cases n <;> decide
  · have hM := two_M_lt_b (n := n) (by omega)
    have hd : |d n| ≤ M n := le_max_left _ _
    have ha := abs_le.mp hd
    omega

private lemma a_eq_b (n : ℕ) : OMA.S_oeis_a048625.a n = b n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | m
    · rfl
    · rfl
    · have ih0 := ih m (by omega)
      have ih1 := ih (m + 1) (by omega)
      rw [OMA.S_oeis_a048625.a, ih0, ih1, Int.ceil_eq_iff]
      have hbpos : (0 : ℚ) < (b m : ℚ) := by exact_mod_cast (b_pos_mono m).1
      have hbd := d_bounds m
      have hlo : (-b m : ℚ) < 2 * (d m : ℚ) := by exact_mod_cast hbd.1
      have hhi : 2 * (d m : ℚ) ≤ (b m : ℚ) := by exact_mod_cast hbd.2
      have hdiff : (b (m + 1) : ℚ) ^ 2 / (b m : ℚ) - 1 / 2 - (b (m + 2) : ℚ) =
          (2 * (d m : ℚ) - (b m : ℚ)) / (2 * (b m : ℚ)) := by
        have hd_eq : (d m : ℚ) = (b (m + 1) : ℚ) ^ 2 - (b m : ℚ) * (b (m + 2) : ℚ) := by
          exact_mod_cast (rfl : d m = b (m + 1) ^ 2 - b m * b (m + 2))
        rw [hd_eq]
        field_simp [hbpos.ne']
        ring
      have hgt : (-1 : ℚ) < (2 * (d m : ℚ) - (b m : ℚ)) / (2 * (b m : ℚ)) := by
        rw [lt_div_iff₀ (by positivity)]
        linarith
      have hle : (2 * (d m : ℚ) - (b m : ℚ)) / (2 * (b m : ℚ)) ≤ 0 := by
        rw [div_le_iff₀ (by positivity)]
        linarith
      constructor <;> linarith

private noncomputable def invCoeff (p : PowerSeries ℚ) : ℕ → ℚ
  | 0 => 1
  | n + 1 => ∑ i ∈ Finset.range (n + 1), PowerSeries.coeff i p * invCoeff p (n - i)

private noncomputable def invOneSubX (p : PowerSeries ℚ) : PowerSeries ℚ :=
  PowerSeries.mk (invCoeff p)

private lemma one_sub_X_mul_invOneSubX (p : PowerSeries ℚ) :
    (1 - PowerSeries.X * p) * invOneSubX p = 1 := by
  ext m
  cases m with
  | zero =>
    simp only [sub_mul, one_mul, map_sub, PowerSeries.coeff_one, ↓reduceIte,
      invOneSubX, PowerSeries.coeff_mk]
    rw [mul_assoc, PowerSeries.coeff_zero_X_mul]
    simp [invCoeff]
  | succ n =>
    simp only [sub_mul, one_mul, map_sub, PowerSeries.coeff_one]
    have hne : n + 1 ≠ 0 := Nat.succ_ne_zero n
    simp only [hne, ↓reduceIte]
    rw [mul_assoc, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => PowerSeries.coeff i p * PowerSeries.coeff j (invOneSubX p)) n,
      invOneSubX]
    simp only [PowerSeries.coeff_mk, invCoeff]
    ring

private noncomputable def D (k : ℕ) : PowerSeries ℚ :=
  1 - PowerSeries.X * (PowerSeries.C (2 * (k : ℚ) + 1) + PowerSeries.X ^ 2)

private noncomputable def Q (k : ℕ) : PowerSeries ℚ :=
  (D k + 2 * PowerSeries.X) * invOneSubX (PowerSeries.C (2 * (k : ℚ) + 1) + PowerSeries.X ^ 2)

private lemma D_mul_inv (k : ℕ) :
    D k * invOneSubX (PowerSeries.C (2 * (k : ℚ) + 1) + PowerSeries.X ^ 2) = 1 :=
  one_sub_X_mul_invOneSubX _

private lemma D_succ_add (k : ℕ) : D (k + 1) + 2 * PowerSeries.X = D k := by
  dsimp only [D]
  push_cast
  simp only [map_add, map_mul, map_one, map_ofNat]
  ring

private lemma Q_tailFamily : OMA.S_oeis_a048625.TailFamily Q := by
  intro k
  constructor
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    have h1 : (D k + 2 * PowerSeries.X) *
        invOneSubX (PowerSeries.C (2 * (k : ℚ) + 1) + PowerSeries.X ^ 2) =
        1 + PowerSeries.C (2 : ℚ) * (PowerSeries.X *
          invOneSubX (PowerSeries.C (2 * (k : ℚ) + 1) + PowerSeries.X ^ 2)) := by
      rw [add_mul, D_mul_inv, map_ofNat]
      ring
    dsimp only [Q]
    rw [h1, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_zero_X_mul, mul_zero, add_zero,
      PowerSeries.coeff_one]
    simp
  · let inv0 := invOneSubX (PowerSeries.C (2 * (k : ℚ) + 1) + PowerSeries.X ^ 2)
    let inv1 := invOneSubX (PowerSeries.C (2 * ((k + 1 : ℕ) : ℚ) + 1) + PowerSeries.X ^ 2)
    have hD0 : D k * inv0 = 1 := D_mul_inv k
    have hD1 : D (k + 1) * inv1 = 1 := D_mul_inv (k + 1)
    have hQ0 : Q k = (D k + 2 * PowerSeries.X) * inv0 := rfl
    have hQ1 : Q (k + 1) = D k * inv1 := by
      dsimp only [Q]
      rw [D_succ_add]
    have hprod : Q k * Q (k + 1) = (D k + 2 * PowerSeries.X) * inv1 := by
      rw [hQ0, hQ1]
      calc
        ((D k + 2 * PowerSeries.X) * inv0) * (D k * inv1) =
            (D k + 2 * PowerSeries.X) * ((D k * inv0) * inv1) := by ring
        _ = (D k + 2 * PowerSeries.X) * (1 * inv1) := by rw [hD0]
        _ = (D k + 2 * PowerSeries.X) * inv1 := by ring
    have hrhs_mul :
        ((1 + PowerSeries.X ^ 3 + PowerSeries.C (2 * (k : ℚ) + 3) * PowerSeries.X) * Q (k + 1) -
          PowerSeries.X * (PowerSeries.C (2 * (k : ℚ) + 1) + PowerSeries.X ^ 2)) =
          (D k + 2 * PowerSeries.X) * inv1 := by
      have hA : (1 + PowerSeries.X ^ 3 + PowerSeries.C (2 * (k : ℚ) + 3) * PowerSeries.X) =
          2 - D (k + 1) := by
        dsimp only [D]
        push_cast
        simp only [map_add, map_mul, map_one, map_ofNat]
        ring
      have hB : PowerSeries.X * (PowerSeries.C (2 * (k : ℚ) + 1) + PowerSeries.X ^ 2) =
          1 - D k := by
        dsimp only [D]
        ring
      rw [hQ1, hA, hB]
      calc
        (2 - D (k + 1)) * (D k * inv1) - (1 - D k) =
            2 * D k * inv1 - D k * (D (k + 1) * inv1) - 1 + D k := by ring
        _ = 2 * D k * inv1 - D k * 1 - 1 + D k := by rw [hD1]
        _ = 2 * D k * inv1 - 1 := by ring
        _ = (2 * D k - D (k + 1)) * inv1 := by
          calc
            2 * D k * inv1 - 1 = 2 * D k * inv1 - D (k + 1) * inv1 := by rw [hD1]
            _ = (2 * D k - D (k + 1)) * inv1 := by ring
        _ = (D k + 2 * PowerSeries.X) * inv1 := by
          have hsub : 2 * D k - D (k + 1) = D k + 2 * PowerSeries.X := by
            rw [← D_succ_add k]
            ring
          rw [hsub]
    rw [hprod, hrhs_mul]

private lemma coeff_succ_mul (A B : PowerSeries ℚ)
    (hA : PowerSeries.coeff 0 A = 1) (hB : PowerSeries.coeff 0 B = 1) (m : ℕ) :
    PowerSeries.coeff (m + 1) (A * B) =
      PowerSeries.coeff (m + 1) A + PowerSeries.coeff (m + 1) B +
        ∑ i ∈ Finset.range m, PowerSeries.coeff (i + 1) A * PowerSeries.coeff (m - i) B := by
  rw [PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => PowerSeries.coeff i A * PowerSeries.coeff j B) (m + 1),
    Finset.sum_range_succ, Finset.sum_range_succ']
  simp only [Nat.sub_self, Nat.sub_zero, hA, hB, one_mul, mul_one, Nat.reduceSubDiff]
  ring

private lemma tailFamily_unique (R : ℕ → PowerSeries ℚ)
    (hR : OMA.S_oeis_a048625.TailFamily R) : R = Q := by
  funext k
  ext m
  revert k
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro k
    rcases m with _ | m
    · have h1 := (hR k).1
      have h2 := (Q_tailFamily k).1
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply] at h1 h2
      rw [h1, h2]
    · have hR0 : ∀ j, PowerSeries.coeff 0 (R j) = 1 := fun j => by
        rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
        exact (hR j).1
      have hQ0 : ∀ j, PowerSeries.coeff 0 (Q j) = 1 := fun j => by
        rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
        exact (Q_tailFamily j).1
      have eqR := congrArg (PowerSeries.coeff (m + 1)) (hR k).2
      have eqQ := congrArg (PowerSeries.coeff (m + 1)) (Q_tailFamily k).2
      rw [coeff_succ_mul (R k) (R (k + 1)) (hR0 k) (hR0 (k + 1)) m] at eqR
      rw [coeff_succ_mul (Q k) (Q (k + 1)) (hQ0 k) (hQ0 (k + 1)) m] at eqQ
      have hsplit : ∀ F : ℕ → PowerSeries ℚ,
          PowerSeries.coeff (m + 1)
            ((1 + PowerSeries.X ^ 3 + PowerSeries.C (2 * (k : ℚ) + 3) * PowerSeries.X) * F (k + 1) -
              PowerSeries.X * (PowerSeries.C (2 * (k : ℚ) + 1) + PowerSeries.X ^ 2)) =
            PowerSeries.coeff (m + 1) (F (k + 1)) +
              PowerSeries.coeff (m + 1) (PowerSeries.X ^ 3 * F (k + 1)) +
              (2 * (k : ℚ) + 3) * PowerSeries.coeff m (F (k + 1)) -
              PowerSeries.coeff (m + 1)
                (PowerSeries.X * (PowerSeries.C (2 * (k : ℚ) + 1) + PowerSeries.X ^ 2)) := by
        intro F
        have hlin : (1 + PowerSeries.X ^ 3 + PowerSeries.C (2 * (k : ℚ) + 3) * PowerSeries.X) * F (k + 1) =
            F (k + 1) + PowerSeries.X ^ 3 * F (k + 1) +
              PowerSeries.C (2 * (k : ℚ) + 3) * (PowerSeries.X * F (k + 1)) := by ring
        rw [map_sub, hlin, map_add, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul]
      rw [hsplit R] at eqR
      rw [hsplit Q] at eqQ
      have hmid : (∑ i ∈ Finset.range m,
          PowerSeries.coeff (i + 1) (R k) * PowerSeries.coeff (m - i) (R (k + 1))) =
          ∑ i ∈ Finset.range m,
          PowerSeries.coeff (i + 1) (Q k) * PowerSeries.coeff (m - i) (Q (k + 1)) := by
        refine Finset.sum_congr rfl fun i hi => ?_
        have him : i < m := Finset.mem_range.mp hi
        rw [ih (i + 1) (by omega) k, ih (m - i) (by omega) (k + 1)]
      have hm1 : PowerSeries.coeff m (R (k + 1)) = PowerSeries.coeff m (Q (k + 1)) :=
        ih m (by omega) (k + 1)
      have hm3 : PowerSeries.coeff (m + 1) (PowerSeries.X ^ 3 * R (k + 1)) =
          PowerSeries.coeff (m + 1) (PowerSeries.X ^ 3 * Q (k + 1)) := by
        have hpow3 : ∀ A : PowerSeries ℚ,
            PowerSeries.X ^ 3 * A = PowerSeries.X * (PowerSeries.X * (PowerSeries.X * A)) := by
          intro A; ring
        rw [hpow3 (R (k + 1)), hpow3 (Q (k + 1))]
        rcases m with _ | _ | r
        · simp only [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_zero_X_mul]
        · simp only [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_zero_X_mul]
        · simp only [PowerSeries.coeff_succ_X_mul]
          exact ih r (by omega) (k + 1)
      rw [hmid, hm1, hm3] at eqR
      linarith

end OMA.P_oeis_a048625

theorem OMA.solution : type_of% @OMA.S_oeis_a048625.main := by
  have ha_rec : ∀ n : ℕ, 3 ≤ n →
      OMA.S_oeis_a048625.a n = OMA.S_oeis_a048625.a (n - 1) + OMA.S_oeis_a048625.a (n - 3) := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    rw [OMA.P_oeis_a048625.a_eq_b, OMA.P_oeis_a048625.a_eq_b, OMA.P_oeis_a048625.a_eq_b]
    have h1 : m + 3 - 1 = m + 2 := by omega
    have h2 : m + 3 - 3 = m := by omega
    rw [h1, h2]
    rfl
  refine ⟨ha_rec, OMA.P_oeis_a048625.Q, OMA.P_oeis_a048625.Q_tailFamily,
    OMA.P_oeis_a048625.tailFamily_unique, ?_⟩
  let F : PowerSeries ℚ := PowerSeries.mk (fun n => (OMA.S_oeis_a048625.a n : ℚ))
  let P5 : PowerSeries ℚ := PowerSeries.X + PowerSeries.X ^ 2 + PowerSeries.X ^ 3 +
    2 * PowerSeries.X ^ 4 + 3 * PowerSeries.X ^ 5
  have hQ0 : (1 / 2 : ℚ) • (OMA.P_oeis_a048625.Q 0 - 1) =
      PowerSeries.X *
        OMA.P_oeis_a048625.invOneSubX (PowerSeries.C (2 * ((0 : ℕ) : ℚ) + 1) + PowerSeries.X ^ 2) := by
    dsimp only [OMA.P_oeis_a048625.Q]
    have hD0 : OMA.P_oeis_a048625.D 0 *
        OMA.P_oeis_a048625.invOneSubX (PowerSeries.C (2 * ((0 : ℕ) : ℚ) + 1) + PowerSeries.X ^ 2) = 1 :=
      OMA.P_oeis_a048625.D_mul_inv 0
    rw [add_mul, hD0]
    have hsmul : ∀ A : PowerSeries ℚ, (1 / 2 : ℚ) • ((1 + 2 * PowerSeries.X * A) - 1) =
        PowerSeries.X * A := by
      intro A
      ext m
      rw [add_sub_cancel_left, map_smul, smul_eq_mul,
        ← map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2, mul_assoc, PowerSeries.coeff_C_mul]
      ring
    exact hsmul _
  have hD0_eq : OMA.P_oeis_a048625.D 0 = 1 - PowerSeries.X - PowerSeries.X ^ 3 := by
    simp only [OMA.P_oeis_a048625.D, Nat.cast_zero, mul_zero, zero_add, map_one]
    ring
  have hprod_eq : OMA.P_oeis_a048625.D 0 * (PowerSeries.X ^ 6 * F + P5) = PowerSeries.X := by
    have ha0 : (OMA.S_oeis_a048625.a 0 : ℚ) = 4 := by
      rw [OMA.P_oeis_a048625.a_eq_b]; decide
    have ha1 : (OMA.S_oeis_a048625.a 1 : ℚ) = 6 := by
      rw [OMA.P_oeis_a048625.a_eq_b]; decide
    have ha2 : (OMA.S_oeis_a048625.a 2 : ℚ) = 9 := by
      rw [OMA.P_oeis_a048625.a_eq_b]; decide
    have hsplit : OMA.P_oeis_a048625.D 0 * (PowerSeries.X ^ 6 * F + P5) =
        ((PowerSeries.X ^ 6 * F - PowerSeries.X * (PowerSeries.X ^ 6 * F) -
          PowerSeries.X ^ 3 * (PowerSeries.X ^ 6 * F))) +
          (PowerSeries.X - PowerSeries.C (4 : ℚ) * PowerSeries.X ^ 6 -
            PowerSeries.C (2 : ℚ) * PowerSeries.X ^ 7 -
            PowerSeries.C (3 : ℚ) * PowerSeries.X ^ 8) := by
      rw [hD0_eq]
      dsimp only [P5]
      simp only [map_ofNat]
      ring
    rw [hsplit]
    have hpow6 : ∀ G : PowerSeries ℚ, PowerSeries.X ^ 6 * G =
        PowerSeries.X * (PowerSeries.X * (PowerSeries.X *
          (PowerSeries.X * (PowerSeries.X * (PowerSeries.X * G))))) := by
      intro G; ring
    have hpow9 : PowerSeries.X ^ 3 * (PowerSeries.X ^ 6 * F) =
        PowerSeries.X * (PowerSeries.X * (PowerSeries.X * (PowerSeries.X ^ 6 * F))) := by
      ring
    rw [hpow9]
    ext m
    by_cases hm9 : m < 9
    · interval_cases m <;>
        simp [PowerSeries.coeff_X, PowerSeries.coeff_X_pow, PowerSeries.coeff_C_mul,
          PowerSeries.coeff_zero_X_mul, PowerSeries.coeff_succ_X_mul, hpow6,
          F, ha0, ha1, ha2, PowerSeries.coeff_mk] <;> norm_num
    · obtain ⟨k, rfl⟩ : ∃ k, m = k + 9 := ⟨m - 9, by omega⟩
      have hne1 : k + 9 ≠ 1 := by omega
      have hne6 : k + 9 ≠ 6 := by omega
      have hne7 : k + 9 ≠ 7 := by omega
      have hne8 : k + 9 ≠ 8 := by omega
      have h10 : PowerSeries.coeff (k + 9) (PowerSeries.X ^ 6 * F) =
          (OMA.S_oeis_a048625.a (k + 3) : ℚ) := by
        rw [hpow6 F, show k + 9 = (k + 3) + 6 by omega]
        simp only [PowerSeries.coeff_succ_X_mul, F, PowerSeries.coeff_mk]
      have h11 : PowerSeries.coeff (k + 9) (PowerSeries.X * (PowerSeries.X ^ 6 * F)) =
          (OMA.S_oeis_a048625.a (k + 2) : ℚ) := by
        rw [show k + 9 = (k + 2) + 7 by omega, show PowerSeries.X * (PowerSeries.X ^ 6 * F) =
          PowerSeries.X * (PowerSeries.X * (PowerSeries.X * (PowerSeries.X *
            (PowerSeries.X * (PowerSeries.X * (PowerSeries.X * F)))))) by ring]
        simp only [PowerSeries.coeff_succ_X_mul, F, PowerSeries.coeff_mk]
      have h12 : PowerSeries.coeff (k + 9)
          (PowerSeries.X * (PowerSeries.X * (PowerSeries.X * (PowerSeries.X ^ 6 * F)))) =
          (OMA.S_oeis_a048625.a k : ℚ) := by
        rw [hpow6 F]
        simp only [PowerSeries.coeff_succ_X_mul, F, PowerSeries.coeff_mk]
      simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_X,
        PowerSeries.coeff_X_pow, hne1, hne6, hne7, hne8, ↓reduceIte, h10, h11, h12]
      have hrecq : (OMA.S_oeis_a048625.a (k + 3) : ℚ) =
          (OMA.S_oeis_a048625.a (k + 2) : ℚ) + (OMA.S_oeis_a048625.a k : ℚ) := by
        have hr := ha_rec (k + 3) (by omega)
        have ha_sub1 : k + 3 - 1 = k + 2 := by omega
        have ha_sub3 : k + 3 - 3 = k := by omega
        rw [ha_sub1, ha_sub3] at hr
        exact_mod_cast hr
      linarith
  have hmul_inv : PowerSeries.X ^ 6 * F + P5 =
      PowerSeries.X *
        OMA.P_oeis_a048625.invOneSubX (PowerSeries.C (2 * ((0 : ℕ) : ℚ) + 1) + PowerSeries.X ^ 2) := by
    calc
      PowerSeries.X ^ 6 * F + P5 =
          (OMA.P_oeis_a048625.D 0 *
            OMA.P_oeis_a048625.invOneSubX (PowerSeries.C (2 * ((0 : ℕ) : ℚ) + 1) + PowerSeries.X ^ 2)) *
            (PowerSeries.X ^ 6 * F + P5) := by
        rw [OMA.P_oeis_a048625.D_mul_inv 0, one_mul]
      _ = (OMA.P_oeis_a048625.D 0 * (PowerSeries.X ^ 6 * F + P5)) *
            OMA.P_oeis_a048625.invOneSubX (PowerSeries.C (2 * ((0 : ℕ) : ℚ) + 1) + PowerSeries.X ^ 2) := by
        ring
      _ = PowerSeries.X *
            OMA.P_oeis_a048625.invOneSubX (PowerSeries.C (2 * ((0 : ℕ) : ℚ) + 1) + PowerSeries.X ^ 2) := by
        rw [hprod_eq]
  rw [hQ0, ← hmul_inv]
  change PowerSeries.X ^ 6 * F = PowerSeries.X ^ 6 * F + P5 - P5
  ring
