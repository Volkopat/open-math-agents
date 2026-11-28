import OMAStatements.S_oeis_a397345
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Parity in Hanna's exponential series

Put U=A−1, L=X A'/A, and D=X d/dX. The defining integral recursion gives
DU=(1+U)L and U=X+5D(UL). In characteristic two, D²=D. Differentiating
the two identities gives DU=U, DL=X and L=X(1+U). Therefore the reduced
series satisfies A=1+XA², which determines all its coefficients.

Source: https://oeis.org/A397345. Credit: @Solitude1312
-/

open PowerSeries OMA.S_oeis_a397345

namespace OMA.A397345

private noncomputable def U : PowerSeries ℤ := PowerSeries.mk fun n => (terms n).1
private noncomputable def L : PowerSeries ℤ := PowerSeries.mk fun n => (terms n).2

private lemma terms_zero : terms 0 = (0, 0) := by rw [terms]; simp

/-- Truncating each factor strictly below n leaves coefficient n of
their product unchanged, as both constant terms vanish. -/
private lemma trunc_product (n : ℕ) :
    ((PowerSeries.mk fun k => if _h : k < n then (terms k).1 else 0) *
     (PowerSeries.mk fun k => if _h : k < n then (terms k).2 else 0)).coeff n = (U * L).coeff n := by
  rw [coeff_mul, coeff_mul]
  apply Finset.sum_congr rfl
  rintro ⟨i, j⟩ hij
  have hsum : i + j = n := Finset.mem_antidiagonal.mp hij
  simp only [U, L, coeff_mk]
  by_cases hi : i < n
  · by_cases hj : j < n
    · simp [hi, hj]
    · have hi0 : i = 0 := by omega
      simp [hi0, terms_zero]
  · have hj0 : j = 0 := by omega
    simp [hi, hj0, terms_zero]

private lemma pair_rule (n : ℕ) :
    terms n = (let s := (U * L).coeff n
               let u := (if n = 1 then 1 else 0) + 5 * (n : ℤ) * s
               (u, (n : ℤ) * u - s)) := by
  by_cases hn : n = 0
  · subst n
    simp [terms_zero, U, L, coeff_zero_eq_constantCoeff]
  · conv_lhs => rw [terms]
    rw [if_neg hn]
    dsimp only
    rw [trunc_product]

private lemma first_linear : terms 1 = (1, 1) := by
  have hs : (U * L).coeff 1 = 0 := by simp [coeff_one_mul, U, L, terms_zero]
  simpa [hs] using pair_rule 1

private noncomputable def E {R : Type*} [CommRing R] (F : PowerSeries R) :=
  X * derivative R F

private lemma coeff_E {R : Type*} [CommRing R] (F : PowerSeries R) (n : ℕ) :
    (E F).coeff n = (n : R) * F.coeff n := by
  cases n with
  | zero => simp [E]
  | succ n =>
    rw [E, coeff_succ_X_mul, coeff_derivative]
    push_cast
    ring

private lemma E_add {R : Type*} [CommRing R] (F G : PowerSeries R) :
    E (F + G) = E F + E G := by simp [E, mul_add]
private lemma E_sub {R : Type*} [CommRing R] (F G : PowerSeries R) :
    E (F - G) = E F - E G := by simp [E, mul_sub]
private lemma E_mul {R : Type*} [CommRing R] (F G : PowerSeries R) :
    E (F * G) = E F * G + F * E G := by
  simp only [E, Derivation.leibniz, smul_eq_mul]
  ring
private lemma E_one {R : Type*} [CommRing R] : E (1 : PowerSeries R) = 0 := by
  simp [E]
private lemma E_X {R : Type*} [CommRing R] : E (X : PowerSeries R) = X := by simp [E]

private lemma integral_equations :
    U = X + C (5 : ℤ) * E (U * L) ∧ E U = (1 + U) * L := by
  constructor
  · ext n
    have h := congrArg Prod.fst (pair_rule n)
    change (terms n).1 = (if n = 1 then 1 else 0) + 5 * (n : ℤ) * (U * L).coeff n at h
    rw [map_add, coeff_X, coeff_C_mul, coeff_E]
    rw [show U.coeff n = (terms n).1 by simp [U]]
    linear_combination h
  · ext n
    have h := congrArg (fun p : ℤ × ℤ => (n : ℤ) * p.1 - p.2) (pair_rule n)
    simp only [add_mul, one_mul, map_add, coeff_E, U, L, coeff_mk] at h ⊢
    linear_combination h

/-- The logarithmic-derivative coefficients in OEIS formula (3), with
denominators cleared over the integers. -/
private lemma logarithmic_coeff (n : ℕ) (hn : 2 ≤ n) :
    5 * (n : ℤ) * L.coeff n = (5 * (n : ℤ) ^ 2 - 1) * series.coeff n := by
  have h := congrArg (fun p : ℤ × ℤ => 5 * (n : ℤ) * p.2 - (5 * (n : ℤ)^2 - 1) * p.1)
    (pair_rule n)
  rw [show series.coeff n = (terms n).1 by
    simp [series, coeff_one, show n ≠ 0 by omega]]
  rw [show L.coeff n = (terms n).2 by simp [L]]
  simp only [if_neg (show n ≠ 1 by omega), zero_add] at h
  linear_combination h

private abbrev S := PowerSeries (ZMod 2)

private lemma E_map (F : PowerSeries ℤ) : (E F).map (Int.castRingHom (ZMod 2)) =
    E (F.map (Int.castRingHom (ZMod 2))) := by
  ext n
  rw [coeff_map, coeff_E, coeff_E, coeff_map, map_mul, map_natCast]

private lemma E_twice (F : S) : E (E F) = E F := by
  ext n
  rw [coeff_E, coeff_E, ← mul_assoc, ← pow_two, ZMod.pow_card]

private lemma reduced_equation :
    series.map (Int.castRingHom (ZMod 2)) = 1 + X * (series.map (Int.castRingHom (ZMod 2))) ^ 2 := by
  let u := U.map (Int.castRingHom (ZMod 2))
  let l := L.map (Int.castRingHom (ZMod 2))
  have hu : u = X + E (u * l) := by
    have h := congrArg (PowerSeries.map (Int.castRingHom (ZMod 2))) integral_equations.1
    simpa only [map_add, map_mul, map_X, map_C,
      show (Int.castRingHom (ZMod 2)) 5 = 1 by decide, map_one, one_mul, E_map] using h
  have hl : E u = (1 + u) * l := by
    have h := congrArg (PowerSeries.map (Int.castRingHom (ZMod 2))) integral_equations.2
    simpa only [E_map, map_mul, map_add, map_one] using h
  have eu : E u = u := calc
    E u = E (X + E (u * l)) := congrArg E hu
    _ = X + E (u * l) := by rw [E_add, E_X, E_twice]
    _ = u := hu.symm
  have fac : u = (1 + u) * l := eu.symm.trans hl
  have eprod : u * l = u - l := by linear_combination -fac
  have el : E l = X := by
    have h := hu
    rw [eprod, E_sub, eu] at h
    linear_combination h
  have hd := congrArg E fac
  rw [eu, E_mul, E_add, E_one, zero_add, eu, el] at hd
  have shifted : l = (1 + u) * X := by linear_combination hd - fac
  have cat : 1 + u = 1 + X * (1 + u) ^ 2 := by
    rw [shifted] at fac
    linear_combination fac
  simpa only [series, map_add, map_one, u, U] using cat

private lemma square_expands (F : S) : F ^ 2 = expand 2 (by decide) F := by
  have h := MvPowerSeries.map_frobenius_expand (f := F) 2 (by decide)
  simpa [PowerSeries.expand] using h.symm

private lemma support_indices (F : S) (hF : F = 1 + X * F ^ 2) :
    ∀ n : ℕ, F.coeff n ≠ 0 ↔ ∃ k : ℕ, n + 1 = 2 ^ k := by
  have f0 : F.coeff 0 = 1 := by
    have h := congrArg (PowerSeries.coeff (R := ZMod 2) 0) hF
    simpa [coeff_one] using h
  have odd_index (m : ℕ) : F.coeff (2 * m + 1) = F.coeff m := by
    have h := congrArg (PowerSeries.coeff (R := ZMod 2) (2 * m + 1)) hF
    simpa only [map_add, coeff_one, if_neg (show 2 * m + 1 ≠ 0 by omega), zero_add,
      coeff_succ_X_mul, square_expands, coeff_expand_mul] using h
  have even_index (m : ℕ) : F.coeff (2 * (m + 1)) = 0 := by
    have h := congrArg (PowerSeries.coeff (R := ZMod 2) ((2 * m + 1) + 1)) hF
    rw [map_add, coeff_one, if_neg (by omega), zero_add, coeff_succ_X_mul,
      square_expands, coeff_expand_of_not_dvd 2 (by decide) F (by omega)] at h
    simpa only [show 2 * (m + 1) = (2 * m + 1) + 1 by omega] using h
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases Nat.even_or_odd' n with ⟨m, hm | hm⟩
    · cases m with
      | zero =>
        subst n
        rw [Nat.mul_zero, f0]
        constructor
        · intro _
          exact ⟨0, rfl⟩
        · intro _
          exact one_ne_zero
      | succ j =>
        rw [hm, even_index]
        constructor
        · exact fun h => (h rfl).elim
        · rintro ⟨k, hk⟩
          cases k with
          | zero => simp at hk
          | succ k => rw [pow_succ] at hk; omega
    · have hlt : m < n := by omega
      rw [hm, odd_index, ih m hlt]
      constructor
      · rintro ⟨k, hk⟩
        exact ⟨k + 1, by rw [pow_succ]; omega⟩
      · rintro ⟨k, hk⟩
        cases k with
        | zero => simp at hk
        | succ k => rw [pow_succ] at hk; exact ⟨k, by omega⟩

lemma parity (n : ℕ) : Odd (series.coeff n) ↔ ∃ k : ℕ, n + 1 = 2 ^ k := by
  have h := support_indices _ reduced_equation n
  rw [coeff_map] at h
  change ((series.coeff n : ℤ) : ZMod 2) ≠ 0 ↔ _ at h
  rw [ne_eq, ZMod.intCast_zmod_eq_zero_iff_dvd] at h
  change (¬ (2 : ℤ) ∣ series.coeff n) ↔ _ at h
  rwa [← even_iff_two_dvd, Int.not_even_iff_odd] at h

end OMA.A397345

theorem OMA.solution : type_of% @OMA.S_oeis_a397345.main := by
  exact OMA.A397345.parity
