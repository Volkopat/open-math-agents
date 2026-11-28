import OMAStatements.S_oeis_a303563
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The parity of A303563 from its reciprocal

The reciprocal of the source series satisfies the integral diagonal
recursion, beginning with 1-X. It reduces modulo two to the same lacunary
series B as in A230218. Multiplying B²+X=B by the inverse yields XA=B+1,
and shifts the power-of-two indices down by one.

Source: https://oeis.org/A303563. Credit: @Solitude1312
-/

open PowerSeries
open scoped Classical

namespace OMA.A303563

open OMA.S_oeis_a303563

/-- The first coefficient at which two normalized series can differ is
multiplied by the exponent on taking powers. -/
private lemma power_difference {R : Type*} [CommRing R] (F G : PowerSeries R)
    (hF : F.constantCoeff = 1) (hG : G.constantCoeff = 1) (n r : ℕ)
    (hag : ∀ k < n, F.coeff k = G.coeff k) :
    (F ^ r).coeff n - (G ^ r).coeff n = (r : R) * (F.coeff n - G.coeff n) := by
  have hdiv : (X : PowerSeries R) ^ n ∣ F - G := by
    apply X_pow_dvd_iff.mpr
    intro k hk
    simp [hag k hk]
  obtain ⟨T, hT⟩ := hdiv
  let H := ∑ i ∈ Finset.range r, F ^ i * G ^ (r - 1 - i)
  have hconst : (constantCoeff H : R) = r := by simp [H, hF, hG]
  have shift (U : PowerSeries R) : (X ^ n * U).coeff n = U.constantCoeff := by
    simpa [coeff_zero_eq_constantCoeff] using coeff_X_pow_mul U n 0
  have hdelta : F.coeff n - G.coeff n = T.constantCoeff := by
    rw [← map_sub, hT, shift]
  have hfac : F ^ r - G ^ r = X ^ n * (T * H) := by
    rw [← (Commute.all F G).mul_geom_sum₂ r, hT, mul_assoc]
  rw [← map_sub, hfac, shift, map_mul, hconst, hdelta, mul_comm]

/-- Here r=n²+n+1. Differentiation gives r ∣ n [Xⁿ] Pʳ and
r-n(n+1)=1 then gives r ∣ [Xⁿ] Pʳ. -/
private lemma exact_division (P : PowerSeries ℤ) (n : ℕ) :
    ((n : ℤ) ^ 2 + n + 1) ∣ (P ^ (n ^ 2 + n + 1)).coeff n := by
  cases n with
  | zero => simp
  | succ n =>
    let r := (n + 1) ^ 2 + (n + 1) + 1
    let v := (P ^ r).coeff (n + 1)
    let t := (P ^ (r - 1) * derivative ℤ P).coeff n
    have hd := congrArg (PowerSeries.coeff (R := ℤ) n) (derivative_pow P r)
    rw [coeff_derivative, mul_assoc, show (r : PowerSeries ℤ) = C (r : ℤ) by simp,
      coeff_C_mul] at hd
    change v * ((n : ℤ) + 1) = (r : ℤ) * t at hd
    refine ⟨v - ((n : ℤ) + 2) * t, ?_⟩
    change v = ((↑(n + 1) : ℤ) ^ 2 + ↑(n + 1) + 1) * _
    dsimp [r] at hd
    push_cast at hd ⊢
    linear_combination -((n : ℤ) + 2) * hd

private lemma first_zero : recipCoeff 0 = 1 := by rw [recipCoeff]; decide
private lemma first_one : recipCoeff 1 = -1 := by rw [recipCoeff]; decide

/-- Verify that the integer recursion gives precisely the source's
diagonal power condition, including the divisibility implicit in it. -/
private lemma source_diagonal (n : ℕ) (hn : 1 < n) :
    ((PowerSeries.mk recipCoeff) ^ (n ^ 2 + n + 1)).coeff n = 0 := by
  let P : PowerSeries ℤ := PowerSeries.mk fun k => if k < n then recipCoeff k else 0
  let r := n ^ 2 + n + 1
  have hF : (PowerSeries.mk recipCoeff).constantCoeff = 1 := by simp [first_zero]
  have hP : P.constantCoeff = 1 := by simp [P, first_zero, show 0 < n by omega]
  have hdiff := power_difference (PowerSeries.mk recipCoeff) P hF hP n r (by
    intro k hk
    simp [P, hk])
  have hrec : recipCoeff n = -((P ^ r).coeff n) / ((n : ℤ) ^ 2 + n + 1) := by
    conv_lhs => rw [recipCoeff]
    simp [P, r, show ¬n < 2 by omega]
    rfl
  have hex := Int.ediv_mul_cancel (dvd_neg.mpr (exact_division P n))
  have hr : (r : ℤ) = (n : ℤ) ^ 2 + n + 1 := by simp [r]
  change ((PowerSeries.mk recipCoeff) ^ r).coeff n = 0
  rw [coeff_mk, show P.coeff n = 0 by simp [P], sub_zero, hr, hrec, mul_comm] at hdiff
  change (-((P ^ r).coeff n) / _ * _) = -((P ^ r).coeff n) at hex
  rw [hex] at hdiff
  omega

private abbrev S := PowerSeries (ZMod 2)

private noncomputable def B : S := by
  classical
  exact PowerSeries.mk fun n => if n = 0 ∨ ∃ k : ℕ, n = 2 ^ k then 1 else 0

private lemma b_coeff (n : ℕ) : B.coeff n =
    (if n = 0 ∨ ∃ k : ℕ, n = 2 ^ k then 1 else 0 : ZMod 2) := by
  classical
  simp [B]

private lemma b_even (m : ℕ) : B.coeff (2 * m) = B.coeff m := by
  classical
  have h : (2 * m = 0 ∨ ∃ k : ℕ, 2 * m = 2 ^ k) ↔ (m = 0 ∨ ∃ k : ℕ, m = 2 ^ k) := by
    constructor
    · rintro (hz | ⟨k, hk⟩)
      · exact Or.inl (by omega)
      · cases k with
        | zero => simp at hk
        | succ k => rw [pow_succ] at hk; exact Or.inr ⟨k, by omega⟩
    · rintro (rfl | ⟨k, rfl⟩)
      · exact Or.inl rfl
      · exact Or.inr ⟨k + 1, by rw [pow_succ, Nat.mul_comm]⟩
  simp only [b_coeff, h]

private lemma b_odd (m : ℕ) : B.coeff (2 * m + 1) = if m = 0 then 1 else 0 := by
  classical
  have h : (2 * m + 1 = 0 ∨ ∃ k : ℕ, 2 * m + 1 = 2 ^ k) ↔ m = 0 := by
    constructor
    · rintro (hz | ⟨k, hk⟩)
      · omega
      · cases k with
        | zero => simp at hk; omega
        | succ k => rw [pow_succ] at hk; omega
    · rintro rfl
      exact Or.inr ⟨0, rfl⟩
  simp only [b_coeff, h]

private lemma square_expands (F : S) : F ^ 2 = expand 2 (by decide) F := by
  have h := MvPowerSeries.map_frobenius_expand (f := F) 2 (by decide)
  simpa [PowerSeries.expand] using h.symm

private lemma square_even (F : S) (m : ℕ) : (F ^ 2).coeff (2 * m) = F.coeff m := by
  rw [square_expands, coeff_expand_mul]

private lemma square_odd (F : S) (m : ℕ) : (F ^ 2).coeff (2 * m + 1) = 0 := by
  rw [square_expands]
  apply coeff_expand_of_not_dvd
  omega

private lemma b_equation : B = B ^ 2 + X := by
  ext n
  rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
  · rw [map_add, square_even, b_even, coeff_X, if_neg (by omega), add_zero]
  · rw [map_add, square_odd, b_odd, coeff_X, zero_add]
    simp

private lemma odd_power (e : ℕ) :
    B ^ (2 * e + 1) = (B ^ (e + 1)) ^ 2 + X * (B ^ e) ^ 2 := by
  calc
    _ = B * (B ^ e) ^ 2 := by rw [pow_succ, Nat.mul_comm 2 e, pow_mul, mul_comm]
    _ = (B ^ 2 + X) * (B ^ e) ^ 2 := congrArg (· * (B ^ e) ^ 2) b_equation
    _ = _ := by rw [pow_succ B e, mul_pow]; ring

private lemma odd_power_even (e m : ℕ) :
    (B ^ (2 * e + 1)).coeff (2 * m) = (B ^ (e + 1)).coeff m := by
  rw [odd_power, map_add, square_even]
  cases m with
  | zero => simp
  | succ m =>
    rw [show 2 * (m + 1) = (2 * m + 1) + 1 by omega, coeff_succ_X_mul, square_odd, add_zero]

private lemma odd_power_odd (e m : ℕ) :
    (B ^ (2 * e + 1)).coeff (2 * m + 1) = (B ^ e).coeff m := by
  rw [odd_power, map_add, square_odd, coeff_succ_X_mul, square_even, zero_add]

/-- For an odd multiplier q, [Xᵐ] B^(mq+1) vanishes for every m>0:
halve even indices until the index is odd and the exponent is even. -/
private lemma diagonal_odd_multiplier (m q : ℕ) (hm : 0 < m) (hq : Odd q) :
    (B ^ (m * q + 1)).coeff m = 0 := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    rcases Nat.even_or_odd' m with ⟨j, hj | hj⟩
    · have hlt : j < m := by omega
      have hjpos : 0 < j := by omega
      rw [hj, show 2 * j * q + 1 = 2 * (j * q) + 1 by ring, odd_power_even]
      exact ih j hlt hjpos
    · obtain ⟨t, ht⟩ := hq
      rw [hj, ht, show (2 * j + 1) * (2 * t + 1) + 1 =
        (2 * j * t + j + t + 1) * 2 by ring, pow_mul, square_odd]

private lemma b_diagonal (n : ℕ) (hn : 1 < n) : (B ^ (n ^ 2 + n + 1)).coeff n = 0 := by
  rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
  · rw [show (2 * m) ^ 2 + 2 * m + 1 = 2 * m * (2 * m + 1) + 1 by ring]
    exact diagonal_odd_multiplier _ _ (by omega) ⟨m, rfl⟩
  · rw [show (2 * m + 1) ^ 2 + (2 * m + 1) + 1 =
      2 * (m * (2 * (m + 1) + 1) + 1) + 1 by ring, odd_power_odd]
    exact diagonal_odd_multiplier _ _ (by omega) ⟨m + 1, rfl⟩

private lemma identifies : (PowerSeries.mk recipCoeff).map (Int.castRingHom (ZMod 2)) = B := by
  let F := (PowerSeries.mk recipCoeff).map (Int.castRingHom (ZMod 2))
  have f0 : F.constantCoeff = 1 := by
    rw [← coeff_zero_eq_constantCoeff_apply]
    simp [F, coeff_map, first_zero]
  have b0 : B.constantCoeff = 1 := by rw [← coeff_zero_eq_constantCoeff_apply, b_coeff]; simp
  have f1 : F.coeff 1 = 1 := by
    simp [F, coeff_map, first_one]
  have b1 : B.coeff 1 = 1 := by simpa using b_odd 0
  change F = B
  ext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : 1 < n
    · let r := n ^ 2 + n + 1
      have hF : (F ^ r).coeff n = 0 := by
        dsimp [F]
        rw [← map_pow, coeff_map, source_diagonal n hn, map_zero]
      have hr : (r : ZMod 2) = 1 := by
        rcases Nat.even_or_odd' n with ⟨m, hm | hm⟩ <;>
          simp [r, hm, show (2 : ZMod 2) = 0 by decide]
        decide
      have hd := power_difference F B f0 b0 n r ih
      rw [hF, b_diagonal n hn, sub_self, hr, one_mul] at hd
      exact sub_eq_zero.mp hd.symm
    · rcases (show n = 0 ∨ n = 1 by omega) with rfl | rfl
      · simpa [coeff_zero_eq_constantCoeff] using f0.trans b0.symm
      · exact f1.trans b1.symm

private lemma inverse_product : series * PowerSeries.mk recipCoeff = 1 := by
  apply invOfUnit_mul
  simp [first_zero]

/-- Verify the initial terms of A itself and the original indexing of
the vanishing condition on its reciprocal. -/
lemma defining_coefficients : series.constantCoeff = 1 ∧ series.coeff 1 = 1 ∧
    ∀ n : ℕ, 2 < n → ((PowerSeries.mk recipCoeff) ^ (n ^ 2 - n + 1)).coeff (n - 1) = 0 := by
  have hc : series.constantCoeff = 1 := by simp [series]
  refine ⟨hc, ?_, ?_⟩
  · have h := congrArg (PowerSeries.coeff (R := ℤ) 1) inverse_product
    simp [coeff_one_mul, coeff_one, hc, first_zero, first_one] at h
    omega
  · intro n hn
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hn)
    have hj : 1 < j := by omega
    have hpow : (j + 1) ^ 2 = (j ^ 2 + j) + (j + 1) := by ring
    simpa [Nat.succ_eq_add_one, hpow] using source_diagonal j hj

lemma parity (n : ℕ) : Odd (series.coeff n) ↔ ∃ k : ℕ, n = 2 ^ k - 1 := by
  classical
  let A := series.map (Int.castRingHom (ZMod 2))
  have hinv : A * B = 1 := by
    rw [← identifies]
    dsimp [A]
    rw [← map_mul, inverse_product, map_one]
  have hx : (X : S) = B * (1 - B) := by linear_combination -b_equation
  have hshift : X * A = 1 - B := calc
    X * A = (B * (1 - B)) * A := by rw [hx]
    _ = (A * B) * (1 - B) := by ring
    _ = 1 - B := by rw [hinv, one_mul]
  have hc := congrArg (PowerSeries.coeff (R := ZMod 2) (n + 1)) hshift
  rw [coeff_succ_X_mul, map_sub, coeff_one, if_neg (by omega), zero_sub, b_coeff] at hc
  simp only [Nat.succ_ne_zero, false_or] at hc
  change ((series.coeff n : ℤ) : ZMod 2) = _ at hc
  have he : ((series.coeff n : ℤ) : ZMod 2) ≠ 0 ↔ ∃ k : ℕ, n + 1 = 2 ^ k := by
    rw [hc, neg_ne_zero]
    split_ifs <;> simp_all
  rw [ne_eq, ZMod.intCast_zmod_eq_zero_iff_dvd] at he
  change (¬ (2 : ℤ) ∣ series.coeff n) ↔ _ at he
  rw [← even_iff_two_dvd, Int.not_even_iff_odd] at he
  apply he.trans
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, by omega⟩
  · rintro ⟨k, hk⟩
    have hkpos : 0 < 2 ^ k := Nat.pow_pos (by decide)
    exact ⟨k, by omega⟩

end OMA.A303563

open OMA.S_oeis_a303563

theorem OMA.solution : type_of% @OMA.S_oeis_a303563.main := by
  exact OMA.A303563.parity

