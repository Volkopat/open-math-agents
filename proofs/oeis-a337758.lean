import OMAStatements.S_oeis_a337758
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.PowerSeries.Catalan
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

-- Problem: A337758, parity and residue two modulo four.
-- Source: https://oeis.org/A337758
-- Statement credit: @RiverMint78.
-- The prior public PLAN suggested a direct modulo-four model and an integral
-- differentiated recurrence for odd degrees. The full model, its coefficient
-- identities, uniqueness proof, and binary-support classification are supplied here.
-- The Catalan residue ingredient is classical: Eu, Liu and Yeh, Catalan and
-- Motzkin numbers modulo 4 and 8, European J. Combinatorics 29 (2008), 1449-1466,
-- doi:10.1016/j.ejc.2007.06.019. The related A338328 proof PR30505 uses it too.
-- Its full Lean code was not used in constructing this proof.

-- Component: A337758Defs

noncomputable section

namespace A337758Proof

open PowerSeries

abbrev Z4 := ZMod 4

def shifted : PowerSeries ℤ := X * map (Nat.castRingHom ℤ) catalanSeries

theorem shifted_zero : constantCoeff shifted = 0 := by
  simp [shifted]

theorem shifted_eq : shifted = X + shifted ^ 2 := by
  have h := congrArg (map (Nat.castRingHom ℤ)) catalanSeries_sq_mul_X_add_one
  simp only [map_add, map_mul, map_pow, map_X, map_one] at h
  unfold shifted
  calc
    X * map (Nat.castRingHom ℤ) catalanSeries =
        X * ((map (Nat.castRingHom ℤ) catalanSeries)^2 * X + 1) := by rw [h]
    _ = _ := by ring

def S : PowerSeries Z4 := map (Int.castRingHom Z4) shifted

theorem S_zero : constantCoeff S = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply]
  simp [S, coeff_map, coeff_zero_eq_constantCoeff_apply, shifted_zero]

theorem S_eq : S = X + S ^ 2 := by
  have h := congrArg (map (Int.castRingHom Z4)) shifted_eq
  simpa [S] using h

def evenS : PowerSeries Z4 := expand 2 (by decide) S

def model : PowerSeries Z4 := X + 2 * X ^ 2 + evenS

theorem evenS_zero : constantCoeff evenS = 0 := by
  simp [evenS, S_zero]

theorem evenS_eq : evenS = X ^ 2 + evenS ^ 2 := by
  have h := congrArg (expand 2 (by decide) (R := Z4)) S_eq
  simpa [evenS] using h

theorem model_zero : constantCoeff model = 0 := by
  simp [model, evenS_zero]

end A337758Proof

-- Component: A337758Jets

noncomputable section

namespace A337758Proof

open PowerSeries Finset

section Jets

variable {R : Type*} [CommRing R]

def Agree (n : ℕ) (f g : PowerSeries R) : Prop :=
  ∀ j < n, coeff j f = coeff j g

theorem coeff_mul_of_zero_below (n : ℕ) (f g : PowerSeries R)
    (hf : ∀ j < n, coeff j f = 0) :
    coeff n (f * g) = coeff n f * constantCoeff g := by
  rw [coeff_mul]
  rw [Finset.sum_eq_single (n, 0)]
  · simp
  · intro p hp hne
    have hp' := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    have hlt : p.1 < n := by
      by_contra hn
      have h1 : p.1 = n := by omega
      have h2 : p.2 = 0 := by omega
      exact hne (Prod.ext h1 h2)
    rw [hf p.1 hlt, zero_mul]
  · simp

theorem agree_mul {n : ℕ} {f g u v : PowerSeries R}
    (hf : Agree n f g) (hu : Agree n u v) : Agree n (f * u) (g * v) := by
  intro j hj
  simp only [coeff_mul]
  apply Finset.sum_congr rfl
  intro p hp
  have hsum := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  rw [hf p.1 (by omega), hu p.2 (by omega)]

theorem agree_pow {n : ℕ} {f g : PowerSeries R} (h : Agree n f g) (m : ℕ) :
    Agree n (f ^ m) (g ^ m) := by
  induction m with
  | zero => intro j hj; rfl
  | succ m ih => simpa only [pow_succ] using agree_mul ih h

theorem coeff_pow_difference {n : ℕ} (m : ℕ) {f g : PowerSeries R}
    (h : Agree n f g) (hf : constantCoeff f = 1) (hg : constantCoeff g = 1) :
    coeff n (f ^ m) - coeff n (g ^ m) = (m : R) * (coeff n f - coeff n g) := by
  rw [← map_sub, ← (Commute.all f g).mul_geom_sum₂ m]
  rw [coeff_mul_of_zero_below n (f - g)]
  · simp only [map_sub, map_sum, map_mul, map_pow, hf, hg, one_pow, mul_one,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    ring
  · intro j hj
    simp [h j hj]

theorem coeff_residual_difference {n : ℕ} (hn : 0 < n) (m : ℕ)
    {f g : PowerSeries R} (h : Agree n f g) (hg : constantCoeff g = 1) :
    coeff (n - 1) (f ^ m * derivative R f) -
        coeff (n - 1) (g ^ m * derivative R g) =
      (coeff n f - coeff n g) * (n : R) := by
  have hncast : ((n - 1 : ℕ) : R) + 1 = (n : R) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      congrArg (fun k : ℕ => (k : R)) (Nat.sub_add_cancel (by omega : 1 ≤ n))
  have he : f ^ m * derivative R f - g ^ m * derivative R g =
      (f ^ m - g ^ m) * derivative R f +
        (derivative R f - derivative R g) * g ^ m := by ring
  rw [← map_sub, he, map_add]
  have hfirst : coeff (n - 1) ((f ^ m - g ^ m) * derivative R f) = 0 := by
    rw [coeff_mul_of_zero_below]
    · simp [agree_pow h m (n - 1) (by omega)]
    · intro j hj
      simp [agree_pow h m j (by omega)]
  rw [hfirst, zero_add, coeff_mul_of_zero_below]
  · simp only [map_sub, coeff_derivative, show n - 1 + 1 = n by omega,
      map_pow, hg, one_pow, mul_one, hncast]
    ring
  · intro j hj
    simp [coeff_derivative, h (j + 1) (by omega)]

theorem derivative_map (f : R →+* Z4) (A : PowerSeries R) :
    derivative Z4 (map f A) = map f (derivative R A) := by
  ext n
  simp [coeff_derivative, coeff_map]

end Jets

def base {R : Type*} [CommRing R] (A : PowerSeries R) (n : ℕ) : PowerSeries R :=
  1 + (n : PowerSeries R) * X + (n : PowerSeries R) * X ^ 2 - A

theorem base_constantCoeff {R : Type*} [CommRing R] (A : PowerSeries R) (n : ℕ)
    (hA : constantCoeff A = 0) : constantCoeff (base A n) = 1 := by
  simp [base, hA]

theorem base_agree {R : Type*} [CommRing R] {A B : PowerSeries R} {n : ℕ}
    (h : Agree n A B) : Agree n (base A n) (base B n) := by
  intro j hj
  simp [base, h j hj]

theorem base_coeff_difference {R : Type*} [CommRing R] (A B : PowerSeries R)
    (n j : ℕ) : coeff j (base A n) - coeff j (base B n) =
      -(coeff j A - coeff j B) := by
  simp only [base, map_sub]
  ring

theorem derivative_condition (A : PowerSeries ℤ)
    (hA : OMA.S_oeis_a337758.IsGeneratingSeries A) (n : ℕ) (hn : 0 < n) :
    coeff (n - 1) (base A n ^ n * derivative ℤ (base A n)) = 0 := by
  have hncast : ((n - 1 : ℕ) : ℤ) + 1 = (n : ℤ) := by omega
  have hd : coeff (n - 1) (derivative ℤ (base A n ^ (n + 1))) = 0 := by
    rw [coeff_derivative, show n - 1 + 1 = n by omega]
    rw [hncast]
    change coeff n ((1 + (n : PowerSeries ℤ) * X + (n : PowerSeries ℤ) * X ^ 2 - A) ^
      (n + 1)) * (n : ℤ) = 0
    rw [hA.2 n hn, zero_mul]
  rw [derivative_pow, Nat.add_sub_cancel, mul_assoc] at hd
  have he : coeff (n - 1) (((n + 1 : ℕ) : PowerSeries ℤ) * (base A n ^ n * derivative ℤ (base A n))) =
      ((n + 1 : ℕ) : ℤ) * coeff (n - 1) (base A n ^ n * derivative ℤ (base A n)) := by
    rw [show (((n + 1 : ℕ) : PowerSeries ℤ)) = C (((n + 1 : ℕ) : ℤ)) by simp,
      coeff_C_mul]
  rw [he] at hd
  exact (mul_eq_zero.mp hd).resolve_left (by positivity)

end A337758Proof

-- Component: A337758Unique

noncomputable section

namespace A337758Proof

open PowerSeries

theorem odd_mul_cancel {n : ℕ} (hn : Odd n) (a : Z4)
    (h : (n : Z4) * a = 0) : a = 0 := by
  have hu : IsUnit (n : Z4) := by
    rw [ZMod.isUnit_iff_coprime]
    change n.Coprime (2 ^ 2)
    exact hn.coprime_two_right.pow_right 2
  exact hu.mul_left_cancel (by simpa using h)

theorem uniqueness (A B : PowerSeries Z4)
    (hA0 : constantCoeff A = 0) (hB0 : constantCoeff B = 0)
    (hAe : ∀ n : ℕ, 0 < n → Even n → coeff n (base A n ^ (n + 1)) = 0)
    (hBe : ∀ n : ℕ, 0 < n → Even n → coeff n (base B n ^ (n + 1)) = 0)
    (hAo : ∀ n : ℕ, 0 < n → Odd n →
      coeff (n - 1) (base A n ^ n * derivative Z4 (base A n)) = 0)
    (hBo : ∀ n : ℕ, 0 < n → Odd n →
      coeff (n - 1) (base B n ^ n * derivative Z4 (base B n)) = 0) : A = B := by
  ext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · subst n
      simpa only [coeff_zero_eq_constantCoeff_apply, hA0, hB0]
    have hnpos : 0 < n := by omega
    have hj : Agree n (base A n) (base B n) := base_agree ih
    rcases Nat.even_or_odd n with he | ho
    · have h := coeff_pow_difference (n + 1) hj
        (base_constantCoeff A n hA0) (base_constantCoeff B n hB0)
      rw [hAe n hnpos he, hBe n hnpos he, sub_self, base_coeff_difference] at h
      have hz := odd_mul_cancel (he.add_odd odd_one)
        (-(coeff n A - coeff n B)) h.symm
      exact sub_eq_zero.mp (neg_eq_zero.mp hz)
    · have h := coeff_residual_difference hnpos n hj (base_constantCoeff B n hB0)
      rw [hAo n hnpos ho, hBo n hnpos ho, sub_self, base_coeff_difference] at h
      have hz := odd_mul_cancel ho (-(coeff n A - coeff n B)) (by simpa [mul_comm] using h.symm)
      exact sub_eq_zero.mp (neg_eq_zero.mp hz)

theorem mapped_even_condition (A : PowerSeries ℤ)
    (hA : OMA.S_oeis_a337758.IsGeneratingSeries A) (n : ℕ) (hn : 0 < n) :
    coeff n (base (map (Int.castRingHom Z4) A) n ^ (n + 1)) = 0 := by
  have h := congrArg (Int.castRingHom Z4) (hA.2 n hn)
  simpa only [← coeff_map, map_pow, base, map_sub, map_add, map_one, map_mul,
    map_natCast, map_X, map_zero] using h

theorem mapped_odd_condition (A : PowerSeries ℤ)
    (hA : OMA.S_oeis_a337758.IsGeneratingSeries A) (n : ℕ) (hn : 0 < n) :
    coeff (n - 1) (base (map (Int.castRingHom Z4) A) n ^ n *
      derivative Z4 (base (map (Int.castRingHom Z4) A) n)) = 0 := by
  have h := congrArg (Int.castRingHom Z4) (derivative_condition A hA n hn)
  have hb : map (Int.castRingHom Z4) (base A n) = base (map (Int.castRingHom Z4) A) n := by
    simp [base]
  simpa only [← coeff_map, map_mul, map_pow, ← derivative_map, hb, map_zero] using h

theorem model_eq_of_conditions
    (hBe : ∀ n : ℕ, 0 < n → Even n → coeff n (base model n ^ (n + 1)) = 0)
    (hBo : ∀ n : ℕ, 0 < n → Odd n →
      coeff (n - 1) (base model n ^ n * derivative Z4 (base model n)) = 0)
    (A : PowerSeries ℤ) (hA : OMA.S_oeis_a337758.IsGeneratingSeries A) :
    map (Int.castRingHom Z4) A = model := by
  apply uniqueness _ _ _ model_zero
    (fun n hn _ => mapped_even_condition A hA n hn) hBe
    (fun n hn _ => mapped_odd_condition A hA n hn) hBo
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, hA.1]
  rfl

end A337758Proof

-- Component: A337758Char4

namespace A337758Proof

open PowerSeries

lemma four_zero : (4 : PowerSeries Z4) = 0 := by
  have h := congrArg (C : Z4 →+* PowerSeries Z4) (show (4 : Z4) = 0 by decide)
  simpa only [map_ofNat, map_zero] using h

def red : Z4 →+* ZMod 2 := ZMod.castHom (by decide) (ZMod 2)

lemma red_eq_iff_two (a b : Z4) : red a = red b ↔ (2 : Z4) * a = 2 * b := by
  have h : ∀ a b : Z4, red a = red b ↔ (2 : Z4) * a = 2 * b := by decide
  exact h a b

lemma map_red_eq_iff_two (f g : PowerSeries Z4) :
    map red f = map red g ↔ (2 : PowerSeries Z4) * f = 2 * g := by
  rw [PowerSeries.ext_iff, PowerSeries.ext_iff]
  have h2 : (2 : PowerSeries Z4) = C (2 : Z4) := by simp only [map_ofNat]
  simp only [coeff_map, h2, coeff_C_mul, red_eq_iff_two]

lemma square_mod_two (f : PowerSeries (ZMod 2)) :
    f ^ 2 = expand 2 (by decide) f := by
  have hf : frobenius (ZMod 2) 2 = RingHom.id (ZMod 2) := by
    ext x
    fin_cases x <;> rfl
  have h := MvPowerSeries.map_frobenius_expand (σ := Unit) (R := ZMod 2)
    2 (by decide) (f := f)
  simpa only [hf, MvPowerSeries.map_id, PowerSeries.expand, RingHom.id_apply] using h.symm

lemma two_square (f : PowerSeries Z4) :
    (2 : PowerSeries Z4) * f ^ 2 = 2 * expand 2 (by decide) f := by
  apply (map_red_eq_iff_two _ _).mp
  rw [map_pow, map_expand, square_mod_two]

lemma two_eq_pow {f g : PowerSeries Z4} (h : (2 : PowerSeries Z4) * f = 2 * g)
    (n : ℕ) : (2 : PowerSeries Z4) * f ^ n = 2 * g ^ n := by
  apply (map_red_eq_iff_two _ _).mp
  rw [map_pow, map_pow, (map_red_eq_iff_two _ _).mpr h]

lemma two_fourth (f : PowerSeries Z4) :
    (2 : PowerSeries Z4) * f ^ 4 = 2 * expand 4 (by decide) f := by
  calc
    2 * f ^ 4 = 2 * (f ^ 2) ^ 2 := by ring
    _ = 2 * (expand 2 (by decide) f) ^ 2 := two_eq_pow (two_square f) 2
    _ = 2 * expand 2 (by decide) (expand 2 (by decide) f) := two_square _
    _ = 2 * expand 4 (by decide) f := by rw [← expand_mul]

lemma coeff_two (f : PowerSeries Z4) (n : ℕ) :
    coeff n ((2 : PowerSeries Z4) * f) = (2 : Z4) * coeff n f := by
  have h2 : (2 : PowerSeries Z4) = C (2 : Z4) := by simp only [map_ofNat]
  rw [h2, coeff_C_mul]

lemma two_coeff_pow_of_four_dvd (f : PowerSeries Z4) (n k : ℕ)
    (hn : 4 ∣ n) (hk : ¬4 ∣ k) : (2 : Z4) * coeff k (f ^ n) = 0 := by
  obtain ⟨m, rfl⟩ := hn
  rw [← coeff_two, show 4 * m = m * 4 by omega, pow_mul, two_fourth, coeff_two]
  rw [coeff_expand_of_not_dvd _ _ _ hk, mul_zero]

lemma natCast_mod_four (n : ℕ) :
    (n : PowerSeries Z4) = ((n % 4 : ℕ) : PowerSeries Z4) := by
  have h : (n : Z4) = ((n % 4 : ℕ) : Z4) := CharP.cast_eq_mod Z4 4 n
  have := congrArg C h
  simpa only [map_natCast] using this

lemma pow_add_two (f g : PowerSeries Z4) (n : ℕ) :
    (f + 2 * g) ^ (n + 1) =
      f ^ (n + 1) + 2 * ((n : PowerSeries Z4) + 1) * g * f ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, ih]
      push_cast
      calc
        _ = f ^ (n + 1 + 1) + 2 * ((n : PowerSeries Z4) + 1 + 1) * g * f ^ (n + 1) +
            4 * (((n : PowerSeries Z4) + 1) * g ^ 2 * f ^ n) := by ring
        _ = _ := by rw [four_zero]; ring

end A337758Proof

-- Component: A337758Catalan

namespace A337758Catalan

open PowerSeries
open scoped BigOperators

noncomputable def lucas : ℕ → PowerSeries ℤ
  | 0 => 1 + 1
  | 1 => 1
  | n + 2 => lucas (n + 1) - X * lucas n

lemma coeff_lucas_above (k m : ℕ) (h : k < 2 * m) :
    coeff m (lucas k) = 0 := by
  induction k using Nat.twoStepInduction generalizing m with
  | zero =>
      have hm : m ≠ 0 := by omega
      simp [lucas, hm]
  | one =>
      have hm : m ≠ 0 := by omega
      simp [lucas, hm]
  | more k ih ih1 =>
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show m ≠ 0 by omega)
      change coeff (m + 1) (lucas (k + 2)) = 0
      simp only [lucas, map_sub]
      rw [show (X : PowerSeries ℤ) = X ^ 1 by simp, coeff_X_pow_mul]
      rw [ih1 _ (by omega), ih _ (by omega), sub_self]

lemma coeff_lucas_diagonal (m : ℕ) :
    coeff m (lucas (2 * m)) = 2 * (-1 : ℤ) ^ m ∧
    coeff m (lucas (2 * m + 1)) = (2 * (m : ℤ) + 1) * (-1 : ℤ) ^ m := by
  induction m with
  | zero =>
      change coeff 0 (1 + 1 : PowerSeries ℤ) = 2 * (-1 : ℤ) ^ 0 ∧
        coeff 0 (1 : PowerSeries ℤ) = (2 * (0 : ℤ) + 1) * (-1 : ℤ) ^ 0
      simp only [map_add, coeff_zero_eq_constantCoeff, map_one]
      norm_num
  | succ m ih =>
      have he : coeff (m + 1) (lucas (2 * (m + 1))) = 2 * (-1 : ℤ) ^ (m + 1) := by
        rw [show 2 * (m + 1) = 2 * m + 2 by omega, lucas, map_sub]
        rw [coeff_lucas_above _ _ (by omega)]
        rw [show (X : PowerSeries ℤ) = X ^ 1 by simp, coeff_X_pow_mul, ih.1]
        ring
      refine ⟨he, ?_⟩
      rw [show 2 * (m + 1) + 1 = (2 * m + 1) + 2 by omega, lucas, map_sub]
      rw [show 2 * m + 1 + 1 = 2 * (m + 1) by omega, he]
      rw [show (X : PowerSeries ℤ) = X ^ 1 by simp, coeff_X_pow_mul, ih.2]
      push_cast
      ring

lemma lucas_eq (S : PowerSeries ℤ) (hS : S = X + S ^ 2) (k : ℕ) :
    lucas k = (1 - S) ^ k + S ^ k := by
  have hprod : S * (1 - S) = X := by
    calc
      S * (1 - S) = S - S ^ 2 := by ring
      _ = X := sub_eq_iff_eq_add.mpr hS
  induction k using Nat.twoStepInduction with
  | zero => simp [lucas]
  | one => simp [lucas]
  | more k ih ih1 =>
      rw [lucas, ih, ih1, ← hprod]
      ring

lemma coeff_pow_vanish (S : PowerSeries ℤ) (h0 : constantCoeff S = 0)
    (n k : ℕ) (h : n < k) : coeff n (S ^ k) = 0 := by
  apply coeff_of_lt_order
  exact lt_of_lt_of_le (by exact_mod_cast h) (le_order_pow_of_constantCoeff_eq_zero k h0)

lemma diagonal (S : PowerSeries ℤ) (h0 : constantCoeff S = 0)
    (hS : S = X + S ^ 2) (m : ℕ) :
    coeff m ((1 - S) ^ (2 * m + 1)) = (2 * (m : ℤ) + 1) * (-1 : ℤ) ^ m := by
  have h := (coeff_lucas_diagonal m).2
  rw [lucas_eq S hS, map_add, coeff_pow_vanish S h0 _ _ (by omega), add_zero] at h
  exact h

def alternatingEven (n : ℕ) : ℤ :=
  if 2 ∣ n then (-1) ^ (n / 2) else 0

lemma alternatingEven_add_two (n : ℕ) :
    alternatingEven (n + 2) = -alternatingEven n := by
  have hdiv : 2 ∣ n + 2 ↔ 2 ∣ n := by omega
  have hquot : (n + 2) / 2 = n / 2 + 1 := by omega
  simp only [alternatingEven, hdiv, hquot]
  split_ifs <;> simp [pow_succ]

def binomialSum (n j : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (n + 1), (n.choose i : ℤ) * alternatingEven (i + j)

lemma binomialSum_succ (n j : ℕ) :
    binomialSum (n + 1) j = binomialSum n j + binomialSum n (j + 1) := by
  simpa [binomialSum, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    (Finset.sum_choose_succ_mul (fun i _ => alternatingEven (i + j)) n)

lemma binomialSum_add_two (n j : ℕ) :
    binomialSum n (j + 2) = -binomialSum n j := by
  simp [binomialSum, ← Nat.add_assoc, alternatingEven_add_two, Finset.sum_neg_distrib]

lemma binomialSum_add_four (n j : ℕ) :
    binomialSum (n + 4) j = -4 * binomialSum n j := by
  simp only [show n + 4 = (n + 3) + 1 by omega, binomialSum_succ]
  have h2 : binomialSum n (j + 1 + 1) = -binomialSum n j := by
    simpa [Nat.add_assoc] using binomialSum_add_two n j
  have h3 : binomialSum n (j + 1 + 1 + 1) = -binomialSum n (j + 1) := by
    simpa [Nat.add_assoc] using binomialSum_add_two n (j + 1)
  have h4 : binomialSum n (j + 1 + 1 + 1 + 1) = binomialSum n j := by
    calc
      _ = -binomialSum n (j + 2) := by
        simpa [Nat.add_assoc] using binomialSum_add_two n (j + 2)
      _ = _ := by rw [binomialSum_add_two]; ring
  rw [h2, h3, h4]
  ring

lemma binomialSum_four_dvd (n : ℕ) (hn : 4 ≤ n) :
    4 ∣ binomialSum n 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [Nat.add_comm, binomialSum_add_four]
  exact ⟨-binomialSum m 0, by ring⟩

lemma coeff_mul_natCast (P : PowerSeries ℤ) (n c : ℕ) :
    coeff n (P * (c : PowerSeries ℤ)) = coeff n P * (c : ℤ) := by
  rw [show (c : PowerSeries ℤ) = C (c : ℤ) by simp only [map_natCast]]
  exact PowerSeries.coeff_mul_C n P (c : ℤ)

lemma expanded_piece (S : PowerSeries ℤ) (h0 : constantCoeff S = 0)
    (hS : S = X + S ^ 2) (n k : ℕ) (hk : k ≤ n) :
    coeff n ((expand 2 (by decide) (1 - S)) ^ (k + 1) * X ^ (n - k)) =
      ((k : ℤ) + 1) * alternatingEven k := by
  rw [← map_pow]
  conv_lhs => arg 1; rw [show n = k + (n - k) by omega]
  rw [coeff_mul_X_pow, coeff_expand]
  by_cases h : 2 ∣ k
  · obtain ⟨m, rfl⟩ := h
    rw [if_pos (dvd_mul_right 2 m), Nat.mul_div_right _ (by decide)]
    rw [diagonal S h0 hS]
    simp [alternatingEven]
  · simp [h, alternatingEven]

lemma expanded_diagonal (S : PowerSeries ℤ) (h0 : constantCoeff S = 0)
    (hS : S = X + S ^ 2) (n : ℕ) :
    coeff n ((1 - expand 2 (by decide) S + X) ^ (n + 1)) =
      ((n : ℤ) + 1) * binomialSum n 0 := by
  have hbase : 1 - expand 2 (by decide) S = expand 2 (by decide) (1 - S) := by
    simp
  rw [hbase, add_pow, map_sum, Finset.sum_range_succ']
  have hlast : coeff n ((expand 2 (by decide) (1 - S)) ^ 0 * X ^ (n + 1 - 0) *
      ((n + 1).choose 0 : PowerSeries ℤ)) = 0 := by simp
  rw [hlast, add_zero]
  simp only [binomialSum, Nat.add_zero, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  rw [coeff_mul_natCast, Nat.add_sub_add_right, expanded_piece S h0 hS n k hkn]
  have hchoose : ((k : ℤ) + 1) * ((n + 1).choose (k + 1) : ℤ) =
      ((n : ℤ) + 1) * (n.choose k : ℤ) := by
    have h : (k + 1) * (n + 1).choose (k + 1) = (n + 1) * n.choose k := by
      simpa [Nat.mul_comm] using (Nat.add_one_mul_choose_eq n k).symm
    exact_mod_cast h
  calc
    ((k : ℤ) + 1) * alternatingEven k * ((n + 1).choose (k + 1) : ℤ) =
        (((k : ℤ) + 1) * ((n + 1).choose (k + 1) : ℤ)) * alternatingEven k := by ring
    _ = ((n : ℤ) + 1) * ((n.choose k : ℤ) * alternatingEven k) := by rw [hchoose]; ring

lemma expanded_diagonal_four_dvd (S : PowerSeries ℤ) (h0 : constantCoeff S = 0)
    (hS : S = X + S ^ 2) (n : ℕ) (hn : 4 ≤ n) :
    4 ∣ coeff n ((1 - expand 2 (by decide) S + X) ^ (n + 1)) := by
  rw [expanded_diagonal S h0 hS]
  exact dvd_mul_of_dvd_right (binomialSum_four_dvd n hn) _

lemma expanded_diagonal_two (S : PowerSeries ℤ) (h0 : constantCoeff S = 0)
    (hS : S = X + S ^ 2) :
    coeff 2 ((1 - expand 2 (by decide) S + X) ^ 3) = 0 := by
  rw [show 3 = 2 + 1 by decide, expanded_diagonal S h0 hS]
  norm_num [binomialSum, alternatingEven, Finset.sum_range_succ]

lemma rescale_neg_expand_two (S : PowerSeries ℤ) :
    rescale (-1) (expand 2 (by decide) S) = expand 2 (by decide) S := by
  ext n
  rw [coeff_rescale]
  by_cases hn : 2 ∣ n
  · obtain ⟨m, rfl⟩ := hn
    simp [pow_mul]
  · simp [coeff_expand, hn]

lemma expanded_diagonal_neg (S : PowerSeries ℤ) (n : ℕ) :
    coeff n ((1 - expand 2 (by decide) S - X) ^ (n + 1)) =
      (-1 : ℤ) ^ n * coeff n ((1 - expand 2 (by decide) S + X) ^ (n + 1)) := by
  have h : rescale (-1) (1 - expand 2 (by decide) S + X) =
      1 - expand 2 (by decide) S - X := by
    simp [rescale_neg_expand_two, sub_eq_add_neg]
  rw [← h, ← map_pow, coeff_rescale]

lemma expanded_diagonal_neg_four_dvd (S : PowerSeries ℤ) (h0 : constantCoeff S = 0)
    (hS : S = X + S ^ 2) (n : ℕ) (hn : 4 ≤ n) :
    4 ∣ coeff n ((1 - expand 2 (by decide) S - X) ^ (n + 1)) := by
  rw [expanded_diagonal_neg]
  exact dvd_mul_of_dvd_right (expanded_diagonal_four_dvd S h0 hS n hn) _

end A337758Catalan

-- Component: A337758Model

namespace A337758Proof

open PowerSeries

lemma derivative_one_Z4 : derivative Z4 (1 : PowerSeries Z4) = 0 := by
  simpa only [map_one] using (derivative_C (R := Z4) (r := (1 : Z4)))

lemma derivative_two_Z4 : derivative Z4 (2 : PowerSeries Z4) = 0 := by
  simpa only [map_ofNat] using (derivative_C (R := Z4) (r := (2 : Z4)))

lemma evenS_derivative : derivative Z4 evenS = 2 * X := by
  have h := congrArg (derivative Z4) evenS_eq
  simp only [map_add, derivative_pow, derivative_X, Nat.reduceSub, pow_one,
    mul_one, Nat.cast_ofNat] at h
  have h' : derivative Z4 evenS = 2 * X + 2 * evenS * derivative Z4 evenS := h
  have hd : (2 : PowerSeries Z4) * derivative Z4 evenS = 0 := by
    calc
      _ = 2 * (2 * X + 2 * evenS * derivative Z4 evenS) := by rw [← h']
      _ = 4 * (X + evenS * derivative Z4 evenS) := by ring
      _ = 0 := by rw [four_zero, zero_mul]
  calc
    derivative Z4 evenS = 2 * X + 2 * evenS * derivative Z4 evenS := h'
    _ = 2 * X + evenS * (2 * derivative Z4 evenS) := by ring
    _ = 2 * X := by rw [hd]; ring

lemma plus_residual_zero (n : ℕ) (hn : n = 2 ∨ 4 ≤ n) :
    coeff n ((1 - evenS + X) ^ (n + 1)) = 0 := by
  have hd : (4 : ℤ) ∣ coeff n
      ((1 - expand 2 (by decide) shifted + X) ^ (n + 1)) := by
    rcases hn with rfl | hn
    · rw [A337758Catalan.expanded_diagonal_two shifted shifted_zero shifted_eq]
      exact dvd_zero _
    · exact A337758Catalan.expanded_diagonal_four_dvd shifted shifted_zero shifted_eq n hn
  have hc := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).mpr hd
  have hm : map (Int.castRingHom Z4)
      ((1 - expand 2 (by decide) shifted + X) ^ (n + 1)) =
        (1 - evenS + X) ^ (n + 1) := by
    simp [evenS, S]
  rw [← hm, coeff_map]
  exact hc

lemma minus_residual_zero (n : ℕ) (hn : 4 ≤ n) :
    coeff n ((1 - evenS - X) ^ (n + 1)) = 0 := by
  have hd := A337758Catalan.expanded_diagonal_neg_four_dvd
    shifted shifted_zero shifted_eq n hn
  have hc := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).mpr hd
  have hm : map (Int.castRingHom Z4)
      ((1 - expand 2 (by decide) shifted - X) ^ (n + 1)) =
        (1 - evenS - X) ^ (n + 1) := by
    simp [evenS, S]
  rw [← hm, coeff_map]
  exact hc

lemma base_mod_zero (n : ℕ) (hn : n % 4 = 0) :
    base model n = (1 - evenS - X) + 2 * (-X ^ 2) := by
  unfold base model
  rw [natCast_mod_four, hn]
  norm_num
  ring

lemma base_mod_one (n : ℕ) (hn : n % 4 = 1) :
    base model n = 1 - evenS - X ^ 2 := by
  unfold base model
  rw [natCast_mod_four, hn]
  norm_num
  ring

lemma base_mod_two (n : ℕ) (hn : n % 4 = 2) :
    base model n = 1 - evenS + X := by
  unfold base model
  rw [natCast_mod_four, hn]
  norm_num
  ring

lemma base_mod_three (n : ℕ) (hn : n % 4 = 3) :
    base model n = 1 - evenS + 2 * X + X ^ 2 := by
  unfold base model
  rw [natCast_mod_four, hn]
  norm_num
  ring

lemma model_even (n : ℕ) (hn : 0 < n) (hne : Even n) :
    coeff n (base model n ^ (n + 1)) = 0 := by
  have hcases : n % 4 = 0 ∨ n % 4 = 2 := by
    obtain ⟨k, hk⟩ := hne
    omega
  rcases hcases with hmod | hmod
  · have hn4 : 4 ≤ n := by omega
    let f : PowerSeries Z4 := 1 - evenS - X
    have hc : coeff n (X ^ 2 * (2 * f ^ n)) = 0 := by
      have he : n = (n - 2) + 2 := by omega
      conv_lhs => arg 1; rw [he]
      rw [coeff_X_pow_mul, coeff_two]
      exact two_coeff_pow_of_four_dvd f n (n - 2) (by omega) (by omega)
    have hp : base model n ^ (n + 1) =
        f ^ (n + 1) - C ((n : Z4) + 1) * (X ^ 2 * (2 * f ^ n)) := by
      rw [base_mod_zero n hmod, pow_add_two]
      simp only [map_add, map_natCast, map_one]
      dsimp [f]
      ring
    rw [hp, map_sub, coeff_C_mul, hc, mul_zero, sub_zero]
    exact minus_residual_zero n hn4
  · rw [base_mod_two n hmod]
    exact plus_residual_zero n (by omega)

lemma base_three_two (n : ℕ) (hn : n % 4 = 3) :
    (2 : PowerSeries Z4) * base model n = 2 * (1 - evenS) ^ 2 := by
  rw [base_mod_three n hn]
  calc
    _ = 2 * (1 - evenS) ^ 2 + 4 * (X + X ^ 2) -
        2 * (X ^ 2 + evenS ^ 2 - evenS) := by ring
    _ = _ := by rw [← evenS_eq, sub_self, four_zero]; ring

lemma base_three_two_pow (n : ℕ) (hn : n % 4 = 3) :
    (2 : PowerSeries Z4) * base model n ^ n =
      2 * expand 4 (by decide) ((1 - S) ^ n) := by
  calc
    _ = 2 * ((1 - evenS) ^ 2) ^ n := two_eq_pow (base_three_two n hn) n
    _ = 2 * ((1 - evenS) ^ n) ^ 2 := by rw [← pow_mul, ← pow_mul, Nat.mul_comm 2 n]
    _ = 2 * expand 2 (by decide) ((1 - evenS) ^ n) := two_square _
    _ = 2 * expand 2 (by decide) (expand 2 (by decide) ((1 - S) ^ n)) := by
      simp [evenS]
    _ = 2 * expand 4 (by decide) ((1 - S) ^ n) := by rw [← expand_mul]

lemma model_odd (n : ℕ) (hn : 0 < n) (hno : Odd n) :
    coeff (n - 1) (base model n ^ n * derivative Z4 (base model n)) = 0 := by
  have hcases : n % 4 = 1 ∨ n % 4 = 3 := by
    obtain ⟨k, hk⟩ := hno
    omega
  rcases hcases with hmod | hmod
  · have hd : derivative Z4 (base model n) = 0 := by
      rw [base_mod_one n hmod]
      simp only [map_sub, derivative_one_Z4, evenS_derivative, derivative_pow, derivative_X,
        Nat.reduceSub, pow_one, Nat.cast_ofNat, mul_one]
      calc
        _ = -(4 : PowerSeries Z4) * X := by ring
        _ = 0 := by rw [four_zero]; simp
    rw [hd, mul_zero, map_zero]
  · have hd : derivative Z4 (base model n) = 2 := by
      rw [base_mod_three n hmod]
      simp [evenS_derivative, derivative_two_Z4]
    rw [hd, mul_comm, base_three_two_pow n hmod, coeff_two]
    rw [coeff_expand_of_not_dvd _ _ _ (show ¬4 ∣ n - 1 by omega), mul_zero]

end A337758Proof

-- Component: A337758ModelEq

namespace A337758Proof

open PowerSeries

theorem model_eq (A : PowerSeries ℤ)
    (hA : OMA.S_oeis_a337758.IsGeneratingSeries A) :
    map (Int.castRingHom Z4) A = model :=
  model_eq_of_conditions model_even model_odd A hA

end A337758Proof

-- Component: A337758Binary

namespace A337758Proof

theorem pair_power_bounds {i j : ℕ} (hij : i < j) :
    2 ^ j < 2 ^ i + 2 ^ j ∧ 2 ^ i + 2 ^ j < 2 ^ (j + 1) := by
  have hi : 0 < (2 : ℕ) ^ i := by positivity
  have hl : (2 : ℕ) ^ i < 2 ^ j := Nat.pow_lt_pow_right (by decide) hij
  rw [pow_succ]
  constructor <;> omega

theorem pair_power_top_unique {i j k l : ℕ} (hij : i < j) (hkl : k < l)
    (h : 2 ^ i + 2 ^ j = 2 ^ k + 2 ^ l) : j = l := by
  have h1 := pair_power_bounds hij
  have h2 := pair_power_bounds hkl
  apply le_antisymm
  · by_contra hj
    have hl : l + 1 ≤ j := by omega
    have hp : (2 : ℕ) ^ (l + 1) ≤ 2 ^ j := pow_le_pow_right' (by decide) hl
    omega
  · by_contra hl
    have hj : j + 1 ≤ l := by omega
    have hp : (2 : ℕ) ^ (j + 1) ≤ 2 ^ l := pow_le_pow_right' (by decide) hj
    omega

theorem pair_power_unique {i j k l : ℕ} (hij : i < j) (hkl : k < l)
    (h : 2 ^ i + 2 ^ j = 2 ^ k + 2 ^ l) : i = k ∧ j = l := by
  have hj := pair_power_top_unique hij hkl h
  subst l
  have hi : (2 : ℕ) ^ i = 2 ^ k := by omega
  have hik : i = k := by
    apply le_antisymm
    · by_contra hle
      have : (2 : ℕ) ^ k < 2 ^ i := Nat.pow_lt_pow_right (by decide) (by omega)
      omega
    · by_contra hle
      have : (2 : ℕ) ^ i < 2 ^ k := Nat.pow_lt_pow_right (by decide) (by omega)
      omega
  exact ⟨hik, rfl⟩

theorem pair_power_ne_power {i j : ℕ} (hij : i < j) (k : ℕ) :
    2 ^ i + 2 ^ j ≠ 2 ^ k := by
  intro h
  have hb := pair_power_bounds hij
  by_cases hk : k ≤ j
  · have hp : (2 : ℕ) ^ k ≤ 2 ^ j := pow_le_pow_right' (by decide) hk
    omega
  · have hp : (2 : ℕ) ^ (j + 1) ≤ 2 ^ k := pow_le_pow_right' (by decide) (by omega)
    omega

theorem power_two_injective : Function.Injective (fun i : ℕ => 2 ^ i) := by
  intro i j hij
  change (2 : ℕ) ^ i = 2 ^ j at hij
  apply le_antisymm
  · by_contra hle
    have : (2 : ℕ) ^ j < 2 ^ i := Nat.pow_lt_pow_right (by decide) (by omega)
    omega
  · by_contra hle
    have : (2 : ℕ) ^ i < 2 ^ j := Nat.pow_lt_pow_right (by decide) (by omega)
    omega

theorem exponent_lt_power_two (i : ℕ) : i < 2 ^ i := by
  induction i with
  | zero => decide
  | succ i ih =>
    have hi : 0 < (2 : ℕ) ^ i := by positivity
    rw [pow_succ]
    omega

theorem sum_powers_eq_power_iff (i j k : ℕ) :
    2 ^ i + 2 ^ j = 2 ^ k ↔ i = j ∧ k = i + 1 := by
  constructor
  · intro h
    have hij : i = j := by
      rcases lt_trichotomy i j with hij | hij | hij
      · exact False.elim (pair_power_ne_power hij k h)
      · exact hij
      · exact False.elim (pair_power_ne_power hij k (by simpa [add_comm] using h))
    subst j
    have he : (2 : ℕ) ^ (i + 1) = 2 ^ k := by simpa [pow_succ, Nat.mul_two] using h
    exact ⟨rfl, (power_two_injective he).symm⟩
  · rintro ⟨rfl, rfl⟩
    simp [pow_succ, Nat.mul_two]

theorem sum_powers_eq_pair_iff (a b i j : ℕ) (hij : i < j) :
    2 ^ a + 2 ^ b = 2 ^ i + 2 ^ j ↔
      (a = i ∧ b = j) ∨ (a = j ∧ b = i) := by
  constructor
  · intro h
    rcases lt_trichotomy a b with hab | hab | hab
    · exact Or.inl (pair_power_unique hab hij h)
    · subst b
      have hh : 2 ^ i + 2 ^ j = 2 ^ (a + 1) := by
        rw [← h, pow_succ, Nat.mul_two]
      exact False.elim (pair_power_ne_power hij (a + 1) hh)
    · have hh := pair_power_unique hab hij (show 2 ^ b + 2 ^ a = 2 ^ i + 2 ^ j by
        simpa [add_comm] using h)
      exact Or.inr ⟨hh.2, hh.1⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · exact add_comm _ _

theorem quadratic_unique {R : Type*} [CommRing R] (f g : PowerSeries R)
    (hf0 : PowerSeries.constantCoeff f = 0) (hg0 : PowerSeries.constantCoeff g = 0)
    (hf : f = PowerSeries.X + f ^ 2) (hg : g = PowerSeries.X + g ^ 2) : f = g := by
  ext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hd : f - g = (f - g) * (f + g) := by
      calc
        f - g = f ^ 2 - g ^ 2 := by nth_rw 1 [hf, hg]; ring
        _ = (f - g) * (f + g) := by ring
    have hh := congrArg (PowerSeries.coeff n) hd
    rw [coeff_mul_of_zero_below] at hh
    · simp only [map_sub, map_add, hf0, hg0, zero_add, mul_zero] at hh
      exact sub_eq_zero.mp hh
    · intro j hj
      simp [ih j hj]

end A337758Proof

-- Component: A337758Lacunary

noncomputable section

namespace A337758Proof

open PowerSeries Finset

open scoped Classical

def P2 (n : ℕ) : Prop := ∃ k : ℕ, n = 2 ^ k

def P22 (n : ℕ) : Prop := ∃ i j : ℕ, i < j ∧ n = 2 ^ i + 2 ^ j

def T : PowerSeries Z4 := by
  classical
  exact mk (fun n => if P2 n then 1 else 0)

def U : PowerSeries Z4 := by
  classical
  exact mk (fun n => if P22 n then 1 else 0)

theorem coeff_T (n : ℕ) : coeff n T = if P2 n then 1 else 0 := by
  classical
  simp [T]

theorem coeff_U (n : ℕ) : coeff n U = if P22 n then 1 else 0 := by
  classical
  simp [U]

theorem P2_power (k : ℕ) : P2 (2 ^ k) := ⟨k, rfl⟩

theorem P22_pair {i j : ℕ} (hij : i < j) : P22 (2 ^ i + 2 ^ j) := ⟨i, j, hij, rfl⟩

theorem not_P22_of_P2 {n : ℕ} (h : P2 n) : ¬ P22 n := by
  rintro ⟨i, j, hij, hpair⟩
  obtain ⟨k, hk⟩ := h
  exact pair_power_ne_power hij k (hpair.symm.trans hk)

theorem not_P2_of_P22 {n : ℕ} (h : P22 n) : ¬ P2 n := fun hn => not_P22_of_P2 hn h

theorem not_P2_zero : ¬ P2 0 := by
  rintro ⟨k, hk⟩
  have : 0 < (2 : ℕ) ^ k := by positivity
  omega

theorem not_P22_zero : ¬ P22 0 := by
  rintro ⟨i, j, hij, hk⟩
  have : 0 < (2 : ℕ) ^ i := by positivity
  have : 0 ≤ (2 : ℕ) ^ j := Nat.zero_le _
  omega

theorem P2_add {a b : ℕ} (ha : P2 a) (hb : P2 b) : P2 (a + b) ∨ P22 (a + b) := by
  obtain ⟨i, rfl⟩ := ha
  obtain ⟨j, rfl⟩ := hb
  rcases lt_trichotomy i j with hij | hij | hij
  · exact Or.inr ⟨i, j, hij, rfl⟩
  · subst j
    exact Or.inl ⟨i + 1, by simp [pow_succ, Nat.mul_two]⟩
  · exact Or.inr ⟨j, i, hij, add_comm _ _⟩

theorem coeff_T_sq_other (n : ℕ) (hn : ¬ P2 n) (hnn : ¬ P22 n) : coeff n (T ^ 2) = 0 := by
  classical
  rw [sq, coeff_mul]
  apply Finset.sum_eq_zero
  intro p hp
  rw [coeff_T, coeff_T]
  by_cases ha : P2 p.1 <;> by_cases hb : P2 p.2 <;> simp only [ha, hb, if_true, if_false, mul_zero, zero_mul]
  have he := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  rcases P2_add ha hb with h | h
  · exact False.elim (hn (he ▸ h))
  · exact False.elim (hnn (he ▸ h))

theorem coeff_T_sq_one : coeff 1 (T ^ 2) = 0 := by
  classical
  rw [sq, coeff_one_mul]
  have h0 : constantCoeff T = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_T, if_neg not_P2_zero]
  simp [h0]

theorem coeff_T_sq_power (k : ℕ) : coeff (2 ^ (k + 1)) (T ^ 2) = 1 := by
  classical
  rw [sq, coeff_mul]
  rw [Finset.sum_eq_single (2 ^ k, 2 ^ k)]
  · simp [coeff_T, P2_power]
  · intro p hp hne
    rw [coeff_T, coeff_T]
    by_cases ha : P2 p.1 <;> by_cases hb : P2 p.2 <;> simp only [ha, hb, if_true, if_false, mul_zero, zero_mul]
    obtain ⟨i, hi⟩ := ha
    obtain ⟨j, hj⟩ := hb
    have he : 2 ^ i + 2 ^ j = 2 ^ (k + 1) := by
      simpa only [hi, hj] using Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    obtain ⟨hij, hki⟩ := (sum_powers_eq_power_iff i j (k + 1)).mp he
    have hik : i = k := by omega
    have hjk : j = k := by omega
    exact False.elim (hne (Prod.ext (by simpa [hik] using hi) (by simpa [hjk] using hj)))
  · intro hnot
    exact False.elim (hnot (by simp [Finset.HasAntidiagonal.mem_antidiagonal, pow_succ, Nat.mul_two]))

theorem coeff_T_sq_pair {i j : ℕ} (hij : i < j) : coeff (2 ^ i + 2 ^ j) (T ^ 2) = 2 := by
  classical
  rw [sq, coeff_mul]
  let p : ℕ × ℕ := (2 ^ i, 2 ^ j)
  let q : ℕ × ℕ := (2 ^ j, 2 ^ i)
  have hpq : p ≠ q := by
    intro h
    have hh := congrArg Prod.fst h
    change (2 : ℕ) ^ i = 2 ^ j at hh
    have := power_two_injective hh
    omega
  have hsub : ({p, q} : Finset (ℕ × ℕ)) ⊆ Finset.HasAntidiagonal.antidiagonal (2 ^ i + 2 ^ j) := by
    intro r hr
    simp only [Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl <;> simp [p, q, Finset.HasAntidiagonal.mem_antidiagonal, add_comm]
  have hz : ∀ r ∈ Finset.HasAntidiagonal.antidiagonal (2 ^ i + 2 ^ j), r ∉ ({p, q} : Finset (ℕ × ℕ)) →
      coeff r.1 T * coeff r.2 T = 0 := by
    intro r hr hnot
    rw [coeff_T, coeff_T]
    by_cases ha : P2 r.1 <;> by_cases hb : P2 r.2 <;> simp only [ha, hb, if_true, if_false, mul_zero, zero_mul]
    obtain ⟨a, ha⟩ := ha
    obtain ⟨b, hb⟩ := hb
    have he : 2 ^ a + 2 ^ b = 2 ^ i + 2 ^ j := by
      simpa only [ha, hb] using Finset.HasAntidiagonal.mem_antidiagonal.mp hr
    rcases (sum_powers_eq_pair_iff a b i j hij).mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact False.elim (hnot (by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        exact Or.inl (Prod.ext ha hb)))
    · exact False.elim (hnot (by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        exact Or.inr (Prod.ext ha hb)))
  rw [← Finset.sum_subset hsub hz]
  norm_num [hpq, p, q, coeff_T, P2_power]

theorem T_sq : T ^ 2 = T - X + 2 * U := by
  classical
  ext n
  rw [map_add, map_sub, two_mul, map_add, coeff_T, coeff_U, coeff_X]
  by_cases hn : P2 n
  · have hnn := not_P22_of_P2 hn
    rw [if_pos hn, if_neg hnn]
    obtain ⟨k, rfl⟩ := hn
    cases k with
    | zero => simpa using coeff_T_sq_one
    | succ k =>
      have hk : 2 ^ (k + 1) ≠ (1 : ℕ) := by
        have : 1 < (2 : ℕ) ^ (k + 1) := Nat.one_lt_pow (by omega) (by decide)
        omega
      simp [coeff_T_sq_power, hk, eq_comm]
  · rw [if_neg hn]
    have hn1 : n ≠ 1 := by rintro rfl; exact hn ⟨0, rfl⟩
    rw [if_neg hn1]
    by_cases hnn : P22 n
    · rw [if_pos hnn]
      obtain ⟨i, j, hij, rfl⟩ := hnn
      rw [coeff_T_sq_pair hij]
      norm_num
    · rw [if_neg hnn]
      simpa using coeff_T_sq_other n hn hnn

theorem S_split : S = T + 2 * U := by
  have h4 : (4 : PowerSeries Z4) = 0 := by
    have hh := congrArg (C : Z4 →+* PowerSeries Z4) (show (4 : Z4) = 0 by decide)
    simpa only [map_ofNat, map_zero] using hh
  have hsq : (T + 2 * U) ^ 2 = T ^ 2 := by
    calc
      (T + 2 * U) ^ 2 = T ^ 2 + 4 * (T * U + U ^ 2) := by ring
      _ = T ^ 2 := by rw [h4]; simp
  apply quadratic_unique S (T + 2 * U) S_zero
  · rw [← coeff_zero_eq_constantCoeff_apply, map_add, two_mul, map_add,
      coeff_T, coeff_U, if_neg not_P2_zero, if_neg not_P22_zero]
    simp
  · exact S_eq
  · rw [hsq, T_sq]
    ring

theorem S_coeff (n : ℕ) : coeff n S =
    if (∃ k : ℕ, n = 2 ^ k) then 1 else
      if (∃ i j : ℕ, i < j ∧ n = 2 ^ i + 2 ^ j) then 2 else 0 := by
  classical
  rw [S_split, map_add, two_mul, map_add, coeff_T, coeff_U]
  change (if P2 n then 1 else 0) + ((if P22 n then 1 else 0) + (if P22 n then 1 else 0)) =
    if P2 n then 1 else if P22 n then 2 else 0
  by_cases hn : P2 n
  · simp [hn, not_P22_of_P2 hn]
  · by_cases hnn : P22 n <;> norm_num [hn, hnn]

end A337758Proof

-- Component: A337758Final

noncomputable section

namespace A337758Proof

open PowerSeries
open scoped Classical

lemma odd_mod_four (z : ℤ) : Odd z ↔ (z : Z4) = 1 ∨ (z : Z4) = 3 := by
  change Odd z ↔ (z : ZMod 4) = ((1 : ℤ) : ZMod 4) ∨
    (z : ZMod 4) = ((3 : ℤ) : ZMod 4)
  rw [ZMod.intCast_eq_intCast_iff', ZMod.intCast_eq_intCast_iff', Int.odd_iff]
  norm_num
  omega

lemma model_coeff (n : ℕ) : coeff n model =
    (if n = 1 then 1 else 0) + (if n = 2 then 2 else 0) +
      if 2 ∣ n then coeff (n / 2) S else 0 := by
  have h2 : (2 : PowerSeries Z4) = C (2 : Z4) := by simp only [map_ofNat]
  simp only [model, evenS, map_add, h2, coeff_C_mul, coeff_X, coeff_X_pow,
    coeff_expand]
  split_ifs <;> rfl

lemma pair_sum_gt_one {m : ℕ}
    (hm : ∃ i j : ℕ, i < j ∧ m = 2 ^ i + 2 ^ j) : 1 < m := by
  rcases hm with ⟨i, j, hij, rfl⟩
  have hi : 0 < (2 : ℕ) ^ i := by positivity
  have hj : 0 < (2 : ℕ) ^ j := by positivity
  omega

lemma doubled_power (m : ℕ) :
    (∃ k : ℕ, 2 * m = 2 ^ k) ↔ ∃ k : ℕ, m = 2 ^ k := by
  constructor
  · rintro ⟨k, hk⟩
    cases k with
    | zero => norm_num at hk
    | succ k =>
      refine ⟨k, ?_⟩
      rw [pow_succ] at hk
      omega
  · rintro ⟨k, rfl⟩
    exact ⟨k + 1, by simp [pow_succ, Nat.mul_comm]⟩

lemma doubled_pair (m : ℕ) :
    (∃ i j : ℕ, i < j ∧ 2 * m = 2 * (2 ^ i + 2 ^ j)) ↔
      ∃ i j : ℕ, i < j ∧ m = 2 ^ i + 2 ^ j := by
  constructor
  · rintro ⟨i, j, hij, h⟩
    exact ⟨i, j, hij, by omega⟩
  · rintro ⟨i, j, hij, rfl⟩
    exact ⟨i, j, hij, rfl⟩

lemma power_pair_disjoint (m : ℕ) (hm : ∃ k : ℕ, m = 2 ^ k) :
    ¬ ∃ i j : ℕ, i < j ∧ m = 2 ^ i + 2 ^ j := by
  rcases hm with ⟨k, rfl⟩
  rintro ⟨i, j, hij, h⟩
  exact pair_power_ne_power hij k h.symm

lemma model_classification
    (hS : ∀ m : ℕ, coeff m S =
      if (∃ k : ℕ, m = 2 ^ k) then 1
      else if (∃ i j : ℕ, i < j ∧ m = 2 ^ i + 2 ^ j) then 2 else 0)
    (n : ℕ) (hn : 0 < n) :
    ((coeff n model = 1 ∨ coeff n model = 3) ↔ ∃ k : ℕ, n = 2 ^ k) ∧
    (coeff n model = 2 ↔ ∃ i j : ℕ, i < j ∧ n = 2 * (2 ^ i + 2 ^ j)) := by
  by_cases h1 : n = 1
  · subst n
    have hp : ∃ k : ℕ, 1 = 2 ^ k := ⟨0, rfl⟩
    have hnp : ¬ ∃ i j : ℕ, i < j ∧ 1 = 2 * (2 ^ i + 2 ^ j) := by
      rintro ⟨i, j, hij, h⟩
      omega
    norm_num [model_coeff, hp, hnp] <;> decide
  by_cases h2 : n = 2
  · subst n
    have hp : ∃ k : ℕ, 2 = 2 ^ k := ⟨1, rfl⟩
    have hp1 : ∃ k : ℕ, 1 = 2 ^ k := ⟨0, rfl⟩
    have hnp : ¬ ∃ i j : ℕ, i < j ∧ 2 = 2 * (2 ^ i + 2 ^ j) := by
      rintro ⟨i, j, hij, h⟩
      have hg := pair_sum_gt_one (m := 2 ^ i + 2 ^ j) ⟨i, j, hij, rfl⟩
      omega
    have hnp1 : ¬ ∃ i j : ℕ, i < j ∧ 2 ^ i + 2 ^ j = 1 := by
      rintro ⟨i, j, hij, h⟩
      have hg := pair_sum_gt_one (m := 2 ^ i + 2 ^ j) ⟨i, j, hij, rfl⟩
      omega
    norm_num [model_coeff, hS, hp, hp1, hnp, hnp1] <;> decide
  by_cases he : 2 ∣ n
  · obtain ⟨m, rfl⟩ := he
    have hcoeff : coeff (2 * m) model = coeff m S := by
      rw [model_coeff]
      simp [h1, h2]
    rw [hcoeff, hS, doubled_power, doubled_pair]
    by_cases hp : ∃ k : ℕ, m = 2 ^ k
    · have hq := power_pair_disjoint m hp
      norm_num [hp, hq] <;> decide
    · by_cases hq : ∃ i j : ℕ, i < j ∧ m = 2 ^ i + 2 ^ j
      · norm_num [hp, hq] <;> decide
      · norm_num [hp, hq] <;> decide
  · have hnp : ¬ ∃ k : ℕ, n = 2 ^ k := by
      rintro ⟨k, hk⟩
      cases k with
      | zero => exact h1 (by simpa using hk)
      | succ k =>
        apply he
        refine ⟨2 ^ k, ?_⟩
        simpa [pow_succ, Nat.mul_comm] using hk
    have hnq : ¬ ∃ i j : ℕ, i < j ∧ n = 2 * (2 ^ i + 2 ^ j) := by
      rintro ⟨i, j, hij, h⟩
      exact he ⟨2 ^ i + 2 ^ j, h⟩
    norm_num [model_coeff, h1, h2, he, hnp, hnq] <;> decide

theorem solution_of_S_coeff
    (hS : ∀ m : ℕ, coeff m S =
      if (∃ k : ℕ, m = 2 ^ k) then 1
      else if (∃ i j : ℕ, i < j ∧ m = 2 ^ i + 2 ^ j) then 2 else 0)
    (A : PowerSeries ℤ) (hA : map (Int.castRingHom Z4) A = model)
    (n : ℕ) (hn : 0 < n) :
    (Odd (coeff n A) ↔ ∃ k : ℕ, n = 2 ^ k) ∧
    (coeff n A ≡ 2 [ZMOD 4] ↔ ∃ i j : ℕ, i < j ∧ n = 2 * (2 ^ i + 2 ^ j)) := by
  have hc : ((coeff n A : ℤ) : Z4) = coeff n model := by
    simpa only [coeff_map, Int.coe_castRingHom] using congrArg (coeff n) hA
  rw [odd_mod_four]
  have hm : coeff n A ≡ 2 [ZMOD 4] ↔ ((coeff n A : ℤ) : Z4) = 2 := by
    exact (ZMod.intCast_eq_intCast_iff (coeff n A) 2 4).symm
  rw [hm, hc]
  exact model_classification hS n hn

end A337758Proof

-- Component: A337758Finish

theorem OMA.solution : type_of% @OMA.S_oeis_a337758.main := by
  intro A hA n hn
  exact A337758Proof.solution_of_S_coeff A337758Proof.S_coeff A
    (A337758Proof.model_eq A hA) n hn
