import OMAStatements.S_oeis_a274479
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace OeisA274479Proof

open OMA.S_oeis_a274479

private noncomputable def psComp3 (F G : PowerSeries (ZMod 3)) : PowerSeries (ZMod 3) :=
  PowerSeries.mk fun n =>
    ∑ k ∈ Finset.range (n + 1), PowerSeries.coeff k F * PowerSeries.coeff n (G ^ k)

private noncomputable def geomX : PowerSeries (ZMod 3) :=
  PowerSeries.mk fun n => if n = 0 then 0 else 1

private lemma map_psComp (F G : PowerSeries ℤ) :
    PowerSeries.map (Int.castRingHom (ZMod 3)) (psComp F G) =
      psComp3 (PowerSeries.map (Int.castRingHom (ZMod 3)) F)
              (PowerSeries.map (Int.castRingHom (ZMod 3)) G) := by
  ext n
  simp only [PowerSeries.coeff_map, psComp, psComp3, PowerSeries.coeff_mk, map_sum, map_mul,
    ← map_pow]

private lemma three_eq_zero_ps3 : (3 : PowerSeries (ZMod 3)) = 0 := by
  ext k; rw [show (3 : PowerSeries (ZMod 3)) = PowerSeries.C 3 from rfl, PowerSeries.coeff_C]
  split_ifs <;> simp [show (3 : ZMod 3) = 0 by decide]

private lemma cancel_coeff0_one (U F G : PowerSeries (ZMod 3))
    (hU0 : PowerSeries.coeff 0 U = 1) (h : U * F = U * G) : F = G := by
  ext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hn := congrArg (PowerSeries.coeff n) h
    rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => PowerSeries.coeff i U * PowerSeries.coeff j F),
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => PowerSeries.coeff i U * PowerSeries.coeff j G)] at hn
    conv at hn => lhs; rw [Finset.sum_range_succ']
    conv at hn => rhs; rw [Finset.sum_range_succ']
    simp only [Nat.sub_zero, hU0, one_mul] at hn
    have htail :
        ∑ k ∈ Finset.range n, PowerSeries.coeff (k + 1) U * PowerSeries.coeff (n - (k + 1)) F =
        ∑ k ∈ Finset.range n, PowerSeries.coeff (k + 1) U * PowerSeries.coeff (n - (k + 1)) G := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mem_range] at hk
      rw [ih (n - (k + 1)) (by omega)]
    rw [htail] at hn
    exact add_left_cancel hn

private lemma coeff_X_mul_ps {R : Type*} [CommRing R] (f : PowerSeries R) (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.X * f) = if n = 0 then 0 else PowerSeries.coeff (n - 1) f := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => PowerSeries.coeff i (PowerSeries.X : PowerSeries R) * PowerSeries.coeff j f)]
  cases n with
  | zero => simp [PowerSeries.coeff_X]
  | succ n =>
    simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    rw [Finset.sum_eq_single 1]
    · simp [PowerSeries.coeff_X]
    · intro i _ hne; simp [PowerSeries.coeff_X, hne]
    · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h

private lemma one_sub_X_mul_geomX : (1 - PowerSeries.X) * geomX = PowerSeries.X := by
  ext n
  rw [sub_mul, one_mul, map_sub, coeff_X_mul_ps, PowerSeries.coeff_X]
  simp only [geomX, PowerSeries.coeff_mk]
  match n with
  | 0 => simp
  | 1 => simp
  | m + 2 => simp

private lemma coeff_pow_zero_of_lt {G : PowerSeries (ZMod 3)}
    (hG0 : PowerSeries.coeff 0 G = 0) :
    ∀ k m : ℕ, m < k → PowerSeries.coeff m (G ^ k) = 0 := by
  intro k
  induction k with
  | zero => intro m hm; omega
  | succ k ih =>
    intro m hm
    rw [pow_succ, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => PowerSeries.coeff i (G ^ k) * PowerSeries.coeff j G)]
    apply Finset.sum_eq_zero
    intro i hi
    rw [Finset.mem_range] at hi
    by_cases him : i = m
    · subst him; rw [Nat.sub_self, hG0, mul_zero]
    · rw [ih i (by omega), zero_mul]

private lemma coeff_pow_zero_of_lt2 {G : PowerSeries (ZMod 3)}
    (hG0 : PowerSeries.coeff 0 G = 0) (hG1 : PowerSeries.coeff 1 G = 0) :
    ∀ k m : ℕ, m < 2 * k → PowerSeries.coeff m (G ^ k) = 0 := by
  intro k
  induction k with
  | zero => intro m hm; omega
  | succ k ih =>
    intro m hm
    rw [pow_succ, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => PowerSeries.coeff i (G ^ k) * PowerSeries.coeff j G)]
    apply Finset.sum_eq_zero
    intro i hi
    rw [Finset.mem_range] at hi
    by_cases hlt : i < 2 * k
    · rw [ih i hlt, zero_mul]
    · have hmj : m - i = 0 ∨ m - i = 1 := by omega
      rcases hmj with h | h
      · rw [h, hG0, mul_zero]
      · rw [h, hG1, mul_zero]

private lemma one_sub_G_mul_psComp3_geomX (G : PowerSeries (ZMod 3))
    (hG0 : PowerSeries.coeff 0 G = 0) :
    (1 - G) * psComp3 geomX G = G := by
  ext n
  rw [sub_mul, one_mul, map_sub]
  have hGmul : PowerSeries.coeff n (G * psComp3 geomX G) =
      ∑ k ∈ Finset.range n, PowerSeries.coeff n (G ^ (k + 2)) := by
    rw [PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => PowerSeries.coeff i G * PowerSeries.coeff j (psComp3 geomX G))]
    simp only [psComp3, geomX, PowerSeries.coeff_mk]
    have hstep1 :
        ∑ i ∈ Finset.range (n + 1),
          PowerSeries.coeff i G *
            ∑ k ∈ Finset.range (n - i + 1),
              (if k = 0 then (0 : ZMod 3) else 1) * PowerSeries.coeff (n - i) (G ^ k) =
        ∑ i ∈ Finset.range (n + 1),
          ∑ k ∈ Finset.range n,
            PowerSeries.coeff i G * PowerSeries.coeff (n - i) (G ^ (k + 1)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mem_range] at hi
      rw [Finset.mul_sum, Finset.sum_range_succ']
      simp only [↓reduceIte, zero_mul, mul_zero, add_zero, Nat.succ_ne_zero, one_mul]
      apply Finset.sum_subset (fun k hk => by rw [Finset.mem_range] at hk ⊢; omega)
      intro k hk hnot
      rw [Finset.mem_range] at hk hnot
      by_cases hi0 : i = 0
      · subst hi0; rw [hG0, zero_mul]
      · rw [coeff_pow_zero_of_lt hG0 (k + 1) (n - i) (by omega), mul_zero]
    rw [hstep1, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    conv_rhs =>
      rw [pow_succ', PowerSeries.coeff_mul,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ
          (fun i j => PowerSeries.coeff i G * PowerSeries.coeff j (G ^ (k + 1)))]
  rw [hGmul]
  simp only [psComp3, geomX, PowerSeries.coeff_mk]
  rw [Finset.sum_range_succ']
  simp only [↓reduceIte, zero_mul, add_zero, Nat.succ_ne_zero, one_mul]
  cases n with
  | zero =>
    simp [hG0]
  | succ m =>
    conv_lhs => arg 1; rw [Finset.sum_range_succ']
    conv_lhs => arg 2; rw [Finset.sum_range_succ]
    rw [coeff_pow_zero_of_lt hG0 (m + 2) (m + 1) (by omega), add_zero]
    simp only [Nat.zero_add, pow_one]
    ring

private lemma geomX_satisfies_G (G : PowerSeries (ZMod 3))
    (hG0 : PowerSeries.coeff 0 G = 0)
    (hGdef : G * (1 - 2 * PowerSeries.X - 4 * PowerSeries.X ^ 2) = PowerSeries.X ^ 2) :
    geomX ^ 2 = psComp3 geomX G := by
  let D : PowerSeries (ZMod 3) := 1 - 2 * PowerSeries.X - 4 * PowerSeries.X ^ 2
  have hD0 : PowerSeries.coeff 0 D = 1 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff]
    simp [D]
  have h1G0 : PowerSeries.coeff 0 (1 - G) = 1 := by
    rw [map_sub, PowerSeries.coeff_one, if_pos rfl, hG0, sub_zero]
  have hD_sub : D - PowerSeries.X ^ 2 = (1 - PowerSeries.X) ^ 2 := by
    dsimp only [D]
    calc ((1 : PowerSeries (ZMod 3)) - 2 * PowerSeries.X - 4 * PowerSeries.X ^ 2 - PowerSeries.X ^ 2)
        = (1 - PowerSeries.X) ^ 2 - 3 * (2 * PowerSeries.X ^ 2) := by ring
      _ = (1 - PowerSeries.X) ^ 2 := by rw [three_eq_zero_ps3, zero_mul, sub_zero]
  have h1G_mul_geom2 : (1 - G) * geomX ^ 2 = G := by
    apply cancel_coeff0_one D _ _ hD0
    have hD1G : D * (1 - G) = (1 - PowerSeries.X) ^ 2 := by
      calc D * (1 - G) = D - G * D := by ring
        _ = D - PowerSeries.X ^ 2 := by rw [hGdef]
        _ = (1 - PowerSeries.X) ^ 2 := hD_sub
    calc D * ((1 - G) * geomX ^ 2) = (D * (1 - G)) * geomX ^ 2 := by ring
      _ = (1 - PowerSeries.X) ^ 2 * geomX ^ 2 := by rw [hD1G]
      _ = ((1 - PowerSeries.X) * geomX) ^ 2 := by ring
      _ = PowerSeries.X ^ 2 := by rw [one_sub_X_mul_geomX]
      _ = G * D := hGdef.symm
      _ = D * G := by ring
  apply cancel_coeff0_one (1 - G) _ _ h1G0
  rw [h1G_mul_geom2, one_sub_G_mul_psComp3_geomX G hG0]

private lemma unique_A3_eq_geomX (A3 G3 : PowerSeries (ZMod 3))
    (hA30 : PowerSeries.coeff 0 A3 = 0) (hA31 : PowerSeries.coeff 1 A3 = 1)
    (hG30 : PowerSeries.coeff 0 G3 = 0) (hG31 : PowerSeries.coeff 1 G3 = 0)
    (hA3eq : A3 ^ 2 = psComp3 A3 G3) (hGeq : geomX ^ 2 = psComp3 geomX G3) :
    A3 = geomX := by
  have hG0 : PowerSeries.coeff 0 geomX = 0 := by simp [geomX]
  have hG1 : PowerSeries.coeff 1 geomX = 1 := by simp [geomX]
  ext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 => rw [hA30, hG0]
    | 1 => rw [hA31, hG1]
    | m + 2 =>
      -- Compare [x^(m+3)] of A3^2 = psComp3 A3 G3 and geomX^2 = psComp3 geomX G3
      have hRHS : PowerSeries.coeff (m + 3) (psComp3 A3 G3) =
          PowerSeries.coeff (m + 3) (psComp3 geomX G3) := by
        simp only [psComp3, PowerSeries.coeff_mk]
        apply Finset.sum_congr rfl
        intro k hk
        rw [Finset.mem_range] at hk
        by_cases hlt : m + 3 < 2 * k
        · rw [coeff_pow_zero_of_lt2 hG30 hG31 k (m + 3) hlt, mul_zero, mul_zero]
        · rw [ih k (by omega)]
      have hLHS : PowerSeries.coeff (m + 3) (A3 ^ 2) = PowerSeries.coeff (m + 3) (geomX ^ 2) := by
        rw [hA3eq, hGeq, hRHS]
      rw [sq, sq, PowerSeries.coeff_mul, PowerSeries.coeff_mul,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ
          (fun i j => PowerSeries.coeff i A3 * PowerSeries.coeff j A3),
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ
          (fun i j => PowerSeries.coeff i geomX * PowerSeries.coeff j geomX)] at hLHS
      conv at hLHS => lhs; rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ', Finset.sum_range_succ']
      conv at hLHS => rhs; rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ', Finset.sum_range_succ']
      simp only [Nat.sub_self, Nat.sub_zero, hA30, hG0, zero_mul, mul_zero, add_zero, zero_add,
        show m + 3 - (m + 2) = 1 by omega, show m + 3 - (0 + 1) = m + 2 by omega,
        hA31, hG1, one_mul, mul_one] at hLHS
      have hmid :
          ∑ k ∈ Finset.range m, PowerSeries.coeff (k + 1 + 1) A3 * PowerSeries.coeff (m + 3 - (k + 1 + 1)) A3 =
          ∑ k ∈ Finset.range m, PowerSeries.coeff (k + 1 + 1) geomX * PowerSeries.coeff (m + 3 - (k + 1 + 1)) geomX := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [Finset.mem_range] at hk
        rw [ih (k + 1 + 1) (by omega), ih (m + 3 - (k + 1 + 1)) (by omega)]
      rw [hmid] at hLHS
      have h2eq : PowerSeries.coeff (m + 2) A3 + PowerSeries.coeff (m + 2) A3 =
          PowerSeries.coeff (m + 2) geomX + PowerSeries.coeff (m + 2) geomX := by
        have h1 : ∑ x ∈ Finset.range m,
            PowerSeries.coeff (x + 1 + 1) geomX * PowerSeries.coeff (m + 3 - (x + 1 + 1)) geomX +
            (PowerSeries.coeff (m + 2) A3 + PowerSeries.coeff (m + 2) A3) =
          ∑ x ∈ Finset.range m,
            PowerSeries.coeff (x + 1 + 1) geomX * PowerSeries.coeff (m + 3 - (x + 1 + 1)) geomX +
            (PowerSeries.coeff (m + 2) geomX + PowerSeries.coeff (m + 2) geomX) := by
          linear_combination hLHS
        exact add_left_cancel h1
      have h2cancel : ∀ a b : ZMod 3, a + a = b + b → a = b := by decide
      exact h2cancel _ _ h2eq

private lemma map_A_eq_geomX {A : PowerSeries ℤ} (hA : IsA274479 A) :
    PowerSeries.map (Int.castRingHom (ZMod 3)) A = geomX := by
  rcases hA with ⟨hA0, hA1, G, hGdef, hAeq⟩
  let phi : PowerSeries ℤ →+* PowerSeries (ZMod 3) := PowerSeries.map (Int.castRingHom (ZMod 3))
  have hA30 : PowerSeries.coeff 0 (phi A) = 0 := by simp [phi, hA0]
  have hA31 : PowerSeries.coeff 1 (phi A) = 1 := by simp [phi, hA1]
  have hG3def : phi G * (1 - 2 * PowerSeries.X - 4 * PowerSeries.X ^ 2) = PowerSeries.X ^ 2 := by
    have h := congrArg phi hGdef
    simp only [map_mul, map_sub, map_one, map_ofNat, map_pow] at h
    dsimp only [phi] at h
    rw [PowerSeries.map_X] at h
    exact h
  have hD0 : PowerSeries.coeff 0 (1 - 2 * PowerSeries.X - 4 * PowerSeries.X ^ 2 : PowerSeries (ZMod 3)) = 1 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff]
    simp
  have hG30 : PowerSeries.coeff 0 (phi G) = 0 := by
    have h := congrArg (PowerSeries.coeff 0) hG3def
    rw [PowerSeries.coeff_mul, Finset.Nat.antidiagonal_zero, Finset.sum_singleton, hD0, mul_one,
      PowerSeries.coeff_X_pow] at h
    simpa using h
  have hG31 : PowerSeries.coeff 1 (phi G) = 0 := by
    have h := congrArg (PowerSeries.coeff 1) hG3def
    rw [PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => PowerSeries.coeff i (phi G) *
          PowerSeries.coeff j (1 - 2 * PowerSeries.X - 4 * PowerSeries.X ^ 2)),
      PowerSeries.coeff_X_pow] at h
    simp [Finset.sum_range_succ, hG30] at h
    exact h
  have hA3eq : (phi A) ^ 2 = psComp3 (phi A) (phi G) := by
    have h := congrArg phi hAeq
    rw [map_pow, map_psComp] at h
    exact h
  have hGeq : geomX ^ 2 = psComp3 geomX (phi G) := geomX_satisfies_G (phi G) hG30 hG3def
  exact unique_A3_eq_geomX (phi A) (phi G) hA30 hA31 hG30 hG31 hA3eq hGeq

end OeisA274479Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a274479.main := by
  intro A hA n hn
  change PowerSeries.coeff n A ≡ 1 [ZMOD ((3 : ℕ) : ℤ)]
  rw [← ZMod.intCast_eq_intCast_iff]
  have h := congrArg (PowerSeries.coeff n) (OeisA274479Proof.map_A_eq_geomX hA)
  simp only [PowerSeries.coeff_map, Int.coe_castRingHom, OeisA274479Proof.geomX,
    PowerSeries.coeff_mk, show n ≠ 0 by omega, ↓reduceIte] at h
  exact h
