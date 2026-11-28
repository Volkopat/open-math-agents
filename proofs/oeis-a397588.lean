import OMAStatements.S_oeis_a397588
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.MvPowerSeries.Expand

/-! Reduction modulo two sends the generating series equation to
`B = X + B²`. Frobenius doubles the index of each coefficient, so every
positive index with coefficient one is obtained by repeatedly doubling one. -/

namespace OMA.A397588

open PowerSeries

private lemma square_expand (B : PowerSeries (ZMod 2)) :
    B ^ 2 = MvPowerSeries.expand 2 (by decide) B := by
  rw [← MvPowerSeries.map_frobenius_expand 2 (by decide)]
  apply MvPowerSeries.ext
  intro m
  rw [MvPowerSeries.coeff_map]
  exact ZMod.pow_card _

private lemma square_coeff_even (B : PowerSeries (ZMod 2)) (m : ℕ) :
    coeff (2 * m) (B ^ 2) = coeff m B := by
  rw [square_expand B]
  change (MvPowerSeries.expand 2 (by decide) B).coeff (Finsupp.single () (2 * m)) =
    B.coeff m
  have h : Finsupp.single () (2 * m) = 2 • Finsupp.single () m := by
    apply Finsupp.ext
    intro i
    cases i
    simp [two_mul]
  rw [h, MvPowerSeries.coeff_expand_smul]
  exact coeff_coeToMvPowerSeries m

private lemma square_coeff_odd (B : PowerSeries (ZMod 2)) {n : ℕ} (hn : ¬ 2 ∣ n) :
    coeff n (B ^ 2) = 0 := by
  rw [square_expand B]
  exact MvPowerSeries.coeff_expand_of_not_dvd 2 (by decide) B (i := ())
    (by simpa using hn)

private lemma reduced_equation (A : PowerSeries ℤ)
    (hA : A = X + derivative ℤ (X * A ^ 2)) :
    let B := map (Int.castRingHom (ZMod 2)) A
    B = X + B ^ 2 := by
  let red := Int.castRingHom (ZMod 2)
  let B := map red A
  have hDeriv (f : PowerSeries ℤ) :
      map red (derivative ℤ f) = derivative (ZMod 2) (map red f) := by
    apply PowerSeries.ext
    intro n
    simp only [coeff_map, coeff_derivative, map_mul, map_add, map_natCast, map_one]
  have htwo : (↑(2 : ℕ) : PowerSeries (ZMod 2)) = 0 := by
    rw [← map_natCast (C (R := ZMod 2)) 2,
      show (↑(2 : ℕ) : ZMod 2) = 0 by decide, map_zero]
  have hSquareDeriv : derivative (ZMod 2) (B ^ 2) = 0 := by
    simp only [derivative_pow, htwo, zero_mul]
  have h := congrArg (map red) hA
  simp only [map_add, map_X, hDeriv, map_mul, map_pow] at h
  change B = X + derivative (ZMod 2) (X * B ^ 2) at h
  rw [Derivation.leibniz, derivative_X, hSquareDeriv, smul_zero, zero_add,
    smul_eq_mul, mul_one] at h
  exact h

private lemma coeff_eq_one_iff (B : PowerSeries (ZMod 2)) (hB : B = X + B ^ 2)
    (n : ℕ) (hn : 1 ≤ n) : coeff n B = 1 ↔ ∃ k : ℕ, n = 2 ^ k := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hcoeff := congrArg (coeff n) hB
    simp only [map_add, coeff_X] at hcoeff
    by_cases hOne : n = 1
    · subst n
      have hb : coeff 1 B = 1 := by
        simpa [square_coeff_odd B (by decide : ¬ 2 ∣ (1 : ℕ))] using hcoeff
      exact ⟨fun _ => ⟨0, by norm_num⟩, fun _ => hb⟩
    · rw [if_neg hOne, zero_add] at hcoeff
      by_cases hEven : 2 ∣ n
      · obtain ⟨m, rfl⟩ := hEven
        rw [square_coeff_even] at hcoeff
        rw [hcoeff, ih m (by omega) (by omega)]
        constructor
        · rintro ⟨k, hk⟩
          exact ⟨k + 1, by rw [hk, pow_succ']⟩
        · rintro ⟨k, hk⟩
          cases k with
          | zero => simp at hk
          | succ k =>
            rw [pow_succ'] at hk
            exact ⟨k, by omega⟩
      · rw [square_coeff_odd B hEven] at hcoeff
        constructor
        · intro h
          rw [hcoeff] at h
          exact (zero_ne_one h).elim
        · rintro ⟨k, hk⟩
          cases k with
          | zero => exact (hOne (by simpa using hk)).elim
          | succ k => exact (hEven ⟨2 ^ k, by simpa [pow_succ'] using hk⟩).elim

theorem parity (A : PowerSeries ℤ) (_hzero : coeff 0 A = 0)
    (hA : A = X + derivative ℤ (X * A ^ 2)) (n : ℕ) (hn : 1 ≤ n) :
    ((coeff n A : ℤ) : ZMod 2) = 1 ↔ ∃ k : ℕ, n = 2 ^ k := by
  simpa only [coeff_map, Int.coe_castRingHom] using
    coeff_eq_one_iff (map (Int.castRingHom (ZMod 2)) A) (reduced_equation A hA) n hn

end OMA.A397588

theorem OMA.solution : type_of% @OMA.S_oeis_a397588.main :=
  OMA.A397588.parity
