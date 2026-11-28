import OMAStatements.S_oeis_a141117
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic

namespace OMA.P_oeis_a141117

open PowerSeries

private lemma hasSubst_of_constantCoeff_zero {R : Type*} [CommRing R]
    {f : PowerSeries R} (hf : f.constantCoeff = 0) : PowerSeries.HasSubst f :=
  PowerSeries.HasSubst.of_constantCoeff_zero hf

private lemma coeff_pow_lt_zero {R : Type*} [CommRing R] {g : PowerSeries R}
    (hg : g.constantCoeff = 0) : ∀ k n : ℕ, n < k → PowerSeries.coeff n (g ^ k) = 0 := by
  intro k
  induction k with
  | zero => intro n hn; omega
  | succ k ih =>
    intro n hn
    rw [pow_succ, PowerSeries.coeff_mul]
    apply Finset.sum_eq_zero
    intro p hp
    have hsum := Finset.mem_antidiagonal.mp hp
    by_cases hp2 : p.2 = 0
    · rw [hp2, PowerSeries.coeff_zero_eq_constantCoeff, hg, mul_zero]
    · rw [ih p.1 (by omega), zero_mul]

private lemma coeff_subst_range {R : Type*} [CommRing R] {f g : PowerSeries R}
    (hg : g.constantCoeff = 0) (n : ℕ) :
    PowerSeries.coeff n (f.subst g) =
      ∑ k ∈ Finset.range (n + 1), PowerSeries.coeff k f * PowerSeries.coeff n (g ^ k) := by
  rw [PowerSeries.coeff_subst' (hasSubst_of_constantCoeff_zero hg)]
  simp only [smul_eq_mul]
  apply finsum_eq_sum_of_support_subset
  intro k hk
  rw [Function.mem_support] at hk
  rw [Finset.coe_range, Set.mem_Iio]
  by_contra hge
  exact hk (by rw [coeff_pow_lt_zero hg k n (by omega), mul_zero])

private lemma constantCoeff_subst_zero {R : Type*} [CommRing R] {f g : PowerSeries R}
    (hf : PowerSeries.constantCoeff f = 0) (hg : PowerSeries.constantCoeff g = 0) :
    PowerSeries.constantCoeff (f.subst g) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff, coeff_subst_range hg 0]
  simp [hf]

/-- Explicit power series `H(x) ∈ (ZMod 4)[[x]]` equal to `x*(1 + x - x^2) / (1 + x^3)`. -/
private def hCoeff (n : ℕ) : ZMod 4 :=
  if n = 0 then 0
  else if (n / 3) % 2 = 0 then 1
  else 3

private noncomputable def H4 : PowerSeries (ZMod 4) :=
  PowerSeries.mk hCoeff

/-- Explicit power series `B(x) ∈ (ZMod 4)[[x]]` equal to `(x + 2x^2 + x^4) / (1 - x^3)`. -/
private def bCoeff (n : ℕ) : ZMod 4 :=
  if n = 0 then 0
  else if n = 1 then 1
  else if n % 3 = 0 then 0
  else 2

private noncomputable def B4 : PowerSeries (ZMod 4) :=
  PowerSeries.mk bCoeff

private lemma H4_const : H4.constantCoeff = 0 := by
  simp [H4, hCoeff]

private lemma B4_const : B4.constantCoeff = 0 := by
  simp [B4, bCoeff]

private lemma H4_mul_denom :
    H4 * (1 + PowerSeries.X ^ 3) = PowerSeries.X + PowerSeries.X ^ 2 - PowerSeries.X ^ 3 := by
  ext n
  have h1 : PowerSeries.coeff n (H4 * (1 + PowerSeries.X ^ 3)) =
      hCoeff n + if 3 ≤ n then hCoeff (n - 3) else 0 := by
    rw [mul_add, mul_one, map_add, PowerSeries.coeff_mul_X_pow']
    simp [H4]
  rw [h1]
  have h2 : PowerSeries.coeff n (PowerSeries.X + PowerSeries.X ^ 2 - PowerSeries.X ^ 3 : PowerSeries (ZMod 4)) =
      (if n = 1 then (1 : ZMod 4) else 0) + (if n = 2 then 1 else 0) - (if n = 3 then 1 else 0) := by
    simp only [map_sub, map_add, PowerSeries.coeff_X, PowerSeries.coeff_X_pow]
  rw [h2]
  match n with
  | 0 => decide
  | 1 => decide
  | 2 => decide
  | 3 => decide
  | k + 4 =>
    have hge : 3 ≤ k + 4 := by omega
    rw [if_pos hge, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    have hsub : k + 4 - 3 = k + 1 := by omega
    rw [hsub]
    simp only [hCoeff, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
      show k + 4 ≠ 0 by omega]
    have hdiv : (k + 4) / 3 = (k + 1) / 3 + 1 := by omega
    rw [hdiv]
    rcases Nat.mod_two_eq_zero_or_one ((k + 1) / 3) with hm | hm
    · have hm1 : ((k + 1) / 3 + 1) % 2 = 1 := by omega
      rw [hm, hm1]; decide
    · have hm1 : ((k + 1) / 3 + 1) % 2 = 0 := by omega
      rw [hm, hm1]; decide

private lemma B4_mul_denom :
    B4 * (1 - PowerSeries.X ^ 3) = PowerSeries.X + PowerSeries.C 2 * PowerSeries.X ^ 2 + PowerSeries.X ^ 4 := by
  ext n
  have h1 : PowerSeries.coeff n (B4 * (1 - PowerSeries.X ^ 3)) =
      bCoeff n - if 3 ≤ n then bCoeff (n - 3) else 0 := by
    rw [mul_sub, mul_one, map_sub, PowerSeries.coeff_mul_X_pow']
    simp [B4]
  rw [h1]
  have h2 : PowerSeries.coeff n
      (PowerSeries.X + PowerSeries.C 2 * PowerSeries.X ^ 2 + PowerSeries.X ^ 4 : PowerSeries (ZMod 4)) =
      (if n = 1 then (1 : ZMod 4) else 0) + (if n = 2 then 2 else 0) + (if n = 4 then 1 else 0) := by
    simp only [map_add, PowerSeries.coeff_X, PowerSeries.coeff_X_pow, PowerSeries.coeff_C_mul_X_pow]
  rw [h2]
  match n with
  | 0 => decide
  | 1 => decide
  | 2 => decide
  | 3 => decide
  | 4 => decide
  | k + 5 =>
    have hge : 3 ≤ k + 5 := by omega
    rw [if_pos hge, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    have hsub : k + 5 - 3 = k + 2 := by omega
    rw [hsub]
    simp only [bCoeff, show k + 5 ≠ 0 by omega, show k + 5 ≠ 1 by omega,
      show k + 2 ≠ 0 by omega, show k + 2 ≠ 1 by omega, ↓reduceIte]
    have hmod : (k + 5) % 3 = (k + 2) % 3 := by omega
    rw [hmod]
    by_cases h3 : (k + 2) % 3 = 0
    · simp [h3]
    · simp [h3]

private lemma isUnit_of_const_one (f : PowerSeries (ZMod 4)) (hf : f.constantCoeff = 1) :
    IsUnit f :=
  PowerSeries.isUnit_iff_constantCoeff.mpr (by rw [hf]; exact isUnit_one)

private lemma mul_right_cancel_of_const_one {f g u : PowerSeries (ZMod 4)}
    (hu : u.constantCoeff = 1) (h : f * u = g * u) : f = g :=
  (isUnit_of_const_one u hu).mul_left_inj.mp h

private lemma subst_one_eq {R : Type*} [CommRing R] {a : PowerSeries R} (_ha : PowerSeries.HasSubst a) :
    (1 : PowerSeries R).subst a = 1 := by
  rw [show (1 : PowerSeries R) = PowerSeries.C 1 from rfl, PowerSeries.subst_C]
  rfl

private lemma subst_H4_eq_B4 : H4.subst H4 = B4 := by
  have hsub : PowerSeries.HasSubst H4 := hasSubst_of_constantCoeff_zero H4_const
  have h1 : (H4.subst H4) * (1 + H4 ^ 3) = H4 + H4 ^ 2 - H4 ^ 3 := by
    have h := congrArg (fun p => p.subst H4) H4_mul_denom
    simp only [PowerSeries.subst_mul hsub, PowerSeries.subst_add hsub, PowerSeries.subst_sub hsub,
      subst_one_eq hsub, PowerSeries.subst_pow hsub, PowerSeries.subst_X hsub] at h
    exact h
  set X : PowerSeries (ZMod 4) := PowerSeries.X
  set P : PowerSeries (ZMod 4) := X + X ^ 2 - X ^ 3
  set Q : PowerSeries (ZMod 4) := 1 + X ^ 3
  have hHQ : H4 * Q = P := H4_mul_denom
  have hHQ3 : (H4 * Q) ^ 3 = P ^ 3 := by rw [hHQ]
  have hBQ : B4 * (1 - X ^ 3) = X + 2 * X ^ 2 + X ^ 4 := by
    simpa [X, map_ofNat] using B4_mul_denom
  have hclear : (H4.subst H4) * (Q ^ 3 + P ^ 3) = P * (Q ^ 2 + P * Q - P ^ 2) := by
    calc (H4.subst H4) * (Q ^ 3 + P ^ 3)
        = (H4.subst H4) * (1 + H4 ^ 3) * Q ^ 3 := by
            rw [← hHQ3]; ring
      _ = (H4 + H4 ^ 2 - H4 ^ 3) * Q ^ 3 := by rw [h1]
      _ = (H4 * Q) * Q ^ 2 + (H4 * Q) ^ 2 * Q - (H4 * Q) ^ 3 := by ring
      _ = P * (Q ^ 2 + P * Q - P ^ 2) := by rw [hHQ]; ring
  have hpoly : P * (Q ^ 2 + P * Q - P ^ 2) * (1 - X ^ 3) =
      (X + 2 * X ^ 2 + X ^ 4) * (Q ^ 3 + P ^ 3) := by
    have h4 : (4 : PowerSeries (ZMod 4)) = 0 := by
      have hc : (4 : ZMod 4) = 0 := rfl
      rw [show (4 : PowerSeries (ZMod 4)) = PowerSeries.C (4 : ZMod 4) from rfl, hc, map_zero]
    have hdiff : P * (Q ^ 2 + P * Q - P ^ 2) * (1 - X ^ 3) -
        (X + 2 * X ^ 2 + X ^ 4) * (Q ^ 3 + P ^ 3) =
        4 * (-X ^ 12 + X ^ 11 - X ^ 10 - 2 * X ^ 9 - X ^ 8 - 3 * X ^ 5 - 2 * X ^ 4) := by
      simp only [P, Q]; ring
    rw [h4, zero_mul] at hdiff
    exact sub_eq_zero.mp hdiff
  have hmul : (H4.subst H4) * ((Q ^ 3 + P ^ 3) * (1 - X ^ 3)) =
      B4 * ((Q ^ 3 + P ^ 3) * (1 - X ^ 3)) := by
    calc (H4.subst H4) * ((Q ^ 3 + P ^ 3) * (1 - X ^ 3))
        = (H4.subst H4) * (Q ^ 3 + P ^ 3) * (1 - X ^ 3) := by ring
      _ = P * (Q ^ 2 + P * Q - P ^ 2) * (1 - X ^ 3) := by rw [hclear]
      _ = (X + 2 * X ^ 2 + X ^ 4) * (Q ^ 3 + P ^ 3) := hpoly
      _ = B4 * (1 - X ^ 3) * (Q ^ 3 + P ^ 3) := by rw [hBQ]
      _ = B4 * ((Q ^ 3 + P ^ 3) * (1 - X ^ 3)) := by ring
  have hu : ((Q ^ 3 + P ^ 3) * (1 - X ^ 3)).constantCoeff = 1 := by
    simp [P, Q, X]
  exact mul_right_cancel_of_const_one hu hmul

private lemma subst_H4_B4 : H4.subst B4 * (1 + PowerSeries.X ^ 3) =
    PowerSeries.X - PowerSeries.X ^ 2 - PowerSeries.X ^ 3 := by
  have hsub : PowerSeries.HasSubst B4 := hasSubst_of_constantCoeff_zero B4_const
  have h1 : (H4.subst B4) * (1 + B4 ^ 3) = B4 + B4 ^ 2 - B4 ^ 3 := by
    have h := congrArg (fun p => p.subst B4) H4_mul_denom
    simp only [PowerSeries.subst_mul hsub, PowerSeries.subst_add hsub, PowerSeries.subst_sub hsub,
      subst_one_eq hsub, PowerSeries.subst_pow hsub, PowerSeries.subst_X hsub] at h
    exact h
  set X : PowerSeries (ZMod 4) := PowerSeries.X
  set A : PowerSeries (ZMod 4) := X + 2 * X ^ 2 + X ^ 4
  set D : PowerSeries (ZMod 4) := 1 - X ^ 3
  have hBD : B4 * D = A := by
    simpa [A, D, X, map_ofNat] using B4_mul_denom
  have hBD3 : (B4 * D) ^ 3 = A ^ 3 := by rw [hBD]
  have hclear : (H4.subst B4) * (D ^ 3 + A ^ 3) = A * (D ^ 2 + A * D - A ^ 2) := by
    calc (H4.subst B4) * (D ^ 3 + A ^ 3)
        = (H4.subst B4) * (1 + B4 ^ 3) * D ^ 3 := by rw [← hBD3]; ring
      _ = (B4 + B4 ^ 2 - B4 ^ 3) * D ^ 3 := by rw [h1]
      _ = (B4 * D) * D ^ 2 + (B4 * D) ^ 2 * D - (B4 * D) ^ 3 := by ring
      _ = A * (D ^ 2 + A * D - A ^ 2) := by rw [hBD]; ring
  have hpoly : A * (D ^ 2 + A * D - A ^ 2) * (1 + X ^ 3) =
      (X - X ^ 2 - X ^ 3) * (D ^ 3 + A ^ 3) := by
    have h4 : (4 : PowerSeries (ZMod 4)) = 0 := by
      have hc : (4 : ZMod 4) = 0 := rfl
      rw [show (4 : PowerSeries (ZMod 4)) = PowerSeries.C (4 : ZMod 4) from rfl, hc, map_zero]
    have hdiff : A * (D ^ 2 + A * D - A ^ 2) * (1 + X ^ 3) -
        (X - X ^ 2 - X ^ 3) * (D ^ 3 + A ^ 3) =
        4 * (-X ^ 11 - X ^ 9 - 3 * X ^ 8 - 4 * X ^ 7 - 4 * X ^ 6 - 5 * X ^ 5 + X ^ 3 + X ^ 2) := by
      simp only [A, D]; ring
    rw [h4, zero_mul] at hdiff
    exact sub_eq_zero.mp hdiff
  have hmul : (H4.subst B4 * (1 + X ^ 3)) * (D ^ 3 + A ^ 3) =
      (X - X ^ 2 - X ^ 3) * (D ^ 3 + A ^ 3) := by
    calc (H4.subst B4 * (1 + X ^ 3)) * (D ^ 3 + A ^ 3)
        = (H4.subst B4) * (D ^ 3 + A ^ 3) * (1 + X ^ 3) := by ring
      _ = A * (D ^ 2 + A * D - A ^ 2) * (1 + X ^ 3) := by rw [hclear]
      _ = (X - X ^ 2 - X ^ 3) * (D ^ 3 + A ^ 3) := hpoly
  have hu : (D ^ 3 + A ^ 3).constantCoeff = 1 := by
    simp [A, D, X]
  exact mul_right_cancel_of_const_one hu hmul

private lemma H4_satisfies_eq :
    H4 = PowerSeries.X + PowerSeries.X * H4.subst (H4.subst H4) := by
  rw [subst_H4_eq_B4]
  apply mul_right_cancel_of_const_one (u := 1 + PowerSeries.X ^ 3) (by simp)
  rw [H4_mul_denom, add_mul, mul_assoc, subst_H4_B4]
  ring

private lemma coeff_subst_congr {R : Type*} [CommRing R] {f₁ f₂ g₁ g₂ : PowerSeries R}
    (hg₁ : g₁.constantCoeff = 0) (hg₂ : g₂.constantCoeff = 0) (n : ℕ)
    (hf : ∀ k ≤ n, PowerSeries.coeff k f₁ = PowerSeries.coeff k f₂)
    (hg : ∀ k ≤ n, PowerSeries.coeff k g₁ = PowerSeries.coeff k g₂) :
    PowerSeries.coeff n (f₁.subst g₁) = PowerSeries.coeff n (f₂.subst g₂) := by
  have hpow : ∀ k m : ℕ, m ≤ n →
      PowerSeries.coeff m (g₁ ^ k) = PowerSeries.coeff m (g₂ ^ k) := by
    intro k
    induction k with
    | zero => intro m _; simp
    | succ k ih =>
      intro m hm
      rw [pow_succ, pow_succ, PowerSeries.coeff_mul, PowerSeries.coeff_mul]
      refine Finset.sum_congr rfl fun p hp => ?_
      have hsum := Finset.mem_antidiagonal.mp hp
      rw [ih p.1 (by omega), hg p.2 (by omega)]
  rw [coeff_subst_range hg₁ n, coeff_subst_range hg₂ n]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_range] at hk
  rw [hf k (by omega), hpow k n le_rfl]

private lemma eq_H4_of_eq (G4 : PowerSeries (ZMod 4))
    (hG0 : G4.constantCoeff = 0)
    (hGeq : G4 = PowerSeries.X + PowerSeries.X * G4.subst (G4.subst G4)) :
    G4 = H4 := by
  ext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero =>
      simp only [PowerSeries.coeff_zero_eq_constantCoeff, hG0, H4_const]
    | succ m =>
      rw [hGeq, H4_satisfies_eq]
      simp only [map_add, PowerSeries.coeff_succ_X_mul]
      congr 1
      have hGG0 : (G4.subst G4).constantCoeff = 0 := constantCoeff_subst_zero hG0 hG0
      have hHH0 : (H4.subst H4).constantCoeff = 0 := by
        rw [subst_H4_eq_B4]; exact B4_const
      refine coeff_subst_congr hGG0 hHH0 m (fun k hk => ih k (by omega)) (fun k hk => ?_)
      exact coeff_subst_congr hG0 H4_const k (fun j hj => ih j (by omega)) (fun j hj => ih j (by omega))

private lemma prove_main :
    ∀ G A : PowerSeries ℤ,
      G.constantCoeff = 0 →
      G = PowerSeries.X + PowerSeries.X * G.subst (G.subst G) →
      A = G.subst G →
      PowerSeries.coeff 1 A = 1 ∧
      ∀ n : ℕ, 1 < n →
        (3 ∣ n → PowerSeries.coeff n A % 4 = 0) ∧
        (¬ (3 ∣ n) → PowerSeries.coeff n A % 4 = 2) := by
  intro G A hG0 hGeq hAeq
  have hGG0 : (G.subst G).constantCoeff = 0 := constantCoeff_subst_zero hG0 hG0
  have hG1 : PowerSeries.coeff 1 G = 1 := by
    have h := congrArg (PowerSeries.coeff 1) hGeq
    simp only [map_add, PowerSeries.coeff_X, ↓reduceIte, PowerSeries.coeff_succ_X_mul] at h
    have h0 : PowerSeries.coeff 0 (G.subst (G.subst G)) = 0 := by
      rw [PowerSeries.coeff_zero_eq_constantCoeff]
      exact constantCoeff_subst_zero hG0 hGG0
    rw [h0, add_zero] at h
    exact h
  have hA1 : PowerSeries.coeff 1 A = 1 := by
    rw [hAeq, coeff_subst_range hG0 1]
    simp [Finset.sum_range_succ, hG1, hG0]
  refine ⟨hA1, ?_⟩
  let φ : ℤ →+* ZMod 4 := Int.castRingHom (ZMod 4)
  let G4 : PowerSeries (ZMod 4) := PowerSeries.map φ G
  let A4 : PowerSeries (ZMod 4) := PowerSeries.map φ A
  have hmap_subst : ∀ f g : PowerSeries ℤ, g.constantCoeff = 0 →
      (PowerSeries.map φ g).constantCoeff = 0 →
      PowerSeries.map φ (f.subst g) = (PowerSeries.map φ f).subst (PowerSeries.map φ g) := by
    intro f g hg hgm
    ext n
    rw [PowerSeries.coeff_map, coeff_subst_range hg n, coeff_subst_range hgm n, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hpow : (PowerSeries.map φ g) ^ k = PowerSeries.map φ (g ^ k) := (map_pow (PowerSeries.map φ) g k).symm
    rw [hpow, map_mul, PowerSeries.coeff_map, PowerSeries.coeff_map]
  have hG4_0 : G4.constantCoeff = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff]
    simp [G4, PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff, hG0]
  have hGG4_0 : (PowerSeries.map φ (G.subst G)).constantCoeff = 0 := by
    have h0 : PowerSeries.constantCoeff (G.subst G) = 0 := hGG0
    rw [← PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff, h0, map_zero]
  have hG4_eq : G4 = PowerSeries.X + PowerSeries.X * G4.subst (G4.subst G4) := by
    have h := congrArg (PowerSeries.map φ) hGeq
    simp only [map_add, map_mul, PowerSeries.map_X] at h
    rw [hmap_subst G (G.subst G) hGG0 hGG4_0, hmap_subst G G hG0 hG4_0] at h
    exact h
  have hG4_H4 : G4 = H4 := eq_H4_of_eq G4 hG4_0 hG4_eq
  have hA4_B4 : A4 = B4 := by
    calc A4 = PowerSeries.map φ (G.subst G) := by simp only [A4, hAeq]
      _ = G4.subst G4 := hmap_subst G G hG0 hG4_0
      _ = H4.subst H4 := by rw [hG4_H4]
      _ = B4 := subst_H4_eq_B4
  intro n hn
  have hcoeff : ((PowerSeries.coeff n A : ℤ) : ZMod 4) = bCoeff n := by
    have h := congrArg (PowerSeries.coeff n) hA4_B4
    simpa [A4, B4, φ] using h
  have hmod_iff : ∀ r : ℤ, 0 ≤ r → r < 4 →
      (((PowerSeries.coeff n A : ℤ) : ZMod 4) = (r : ZMod 4) → PowerSeries.coeff n A % 4 = r) := by
    intro r hr0 hr4 heq
    have hdvd : (4 : ℤ) ∣ PowerSeries.coeff n A - r := by
      have h0 : ((PowerSeries.coeff n A - r : ℤ) : ZMod 4) = 0 := by
        push_cast; exact sub_eq_zero.mpr heq
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).mp h0
    omega
  constructor
  · intro h3
    have hb : bCoeff n = (0 : ZMod 4) := by
      have hm : n % 3 = 0 := Nat.dvd_iff_mod_eq_zero.mp h3
      simp [bCoeff, show n ≠ 0 by omega, show n ≠ 1 by omega, hm]
    rw [hb] at hcoeff
    exact hmod_iff 0 (by omega) (by omega) (by simpa using hcoeff)
  · intro h3
    have hb : bCoeff n = (2 : ZMod 4) := by
      have hm : n % 3 ≠ 0 := Nat.dvd_iff_mod_eq_zero.not.mp h3
      simp [bCoeff, show n ≠ 0 by omega, show n ≠ 1 by omega, hm]
    rw [hb] at hcoeff
    exact hmod_iff 2 (by omega) (by omega) (by simpa using hcoeff)

end OMA.P_oeis_a141117

theorem OMA.solution : type_of% @OMA.S_oeis_a141117.main :=
  OMA.P_oeis_a141117.prove_main
