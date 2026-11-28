import OMAStatements.S_oeis_a158119
import Mathlib.Algebra.CharP.Two
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The continued fraction for A158119 in characteristic two

Changing the terminal normalized series changes d levels only by a
multiple of X^d. Modulo two the second numerator is zero. The first
level then gives F=1+X/F. Frobenius in the resulting quadratic equation
determines the support of the reduced coefficients.

Source: https://oeis.org/A158119. Credit: @Solitude1312
-/

open PowerSeries OMA.S_oeis_a158119

namespace OMA.A158119

private lemma inverse_congruence {R : Type*} [CommRing R] (U V : PowerSeries R)
    (hU : U.constantCoeff=1) (hV : V.constantCoeff=1) (n : ℕ)
    (hd : (X : PowerSeries R)^n ∣ U-V) :
    (X : PowerSeries R)^n ∣ U.invOfUnit 1 - V.invOfUnit 1 := by
  obtain ⟨H, hH⟩ := hd
  let I := U.invOfUnit 1
  let J := V.invOfUnit 1
  have hi : I*U=1 := invOfUnit_mul _ _ (by simpa using hU)
  have hj : V*J=1 := mul_invOfUnit _ _ (by simpa using hV)
  refine ⟨-(I*H*J), ?_⟩
  change I-J=X^n * _
  calc
    I-J = I*(V*J)-(I*U)*J := by rw [hi,hj,mul_one,one_mul]
    _ = -(I*(U-V)*J) := by ring
    _ = _ := by rw [hH]; ring

private lemma conv_constant (P T : PowerSeries ℤ) (hP : P.constantCoeff=1)
    (hT : T.constantCoeff=1) (j d : ℕ) : (convergent P T j d).constantCoeff=1 := by
  cases d <;> simp [convergent,hP,hT]

/-- The choice of normalized terminal series cannot affect any
coefficient of degree strictly below the truncation depth. -/
lemma tail_independence (P T V : PowerSeries ℤ) (hP : P.constantCoeff=1)
    (hT : T.constantCoeff=1) (hV : V.constantCoeff=1) (j d : ℕ) :
    (X : PowerSeries ℤ)^d ∣ convergent P T j d - convergent P V j d := by
  induction d generalizing j with
  | zero => simp
  | succ d ih =>
    obtain ⟨H,hH⟩ := inverse_congruence (convergent P T (j+1) d) (convergent P V (j+1) d)
      (conv_constant _ _ hP hT ..) (conv_constant _ _ hP hV ..) d (ih (j+1))
    refine ⟨-C ((j:ℤ)^2)*H,?_⟩
    rw [convergent,convergent,pow_succ]
    let W : PowerSeries ℤ := C ((j:ℤ)^2)
    let I := (convergent P T (j+1) d).invOfUnit 1
    let J := (convergent P V (j+1) d).invOfUnit 1
    change P-W*X*I-(P-W*X*J)=(X^d*X)*(-W*H)
    calc
      _ = -(W*X)*(I-J) := by ring
      _ = _ := by rw [show I-J=X^d*H from hH]; ring

private lemma map_inverse {R S : Type*} [CommRing R] [CommRing S]
    (g : R →+* S) (T : PowerSeries R) (hc : T.constantCoeff=1) :
    (T.invOfUnit 1).map g = (T.map g).invOfUnit 1 := by
  have hmc : (T.map g).constantCoeff=1 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, hc, map_one]
  have h := congrArg (PowerSeries.map g) (invOfUnit_mul T 1 (by simpa using hc))
  rw [map_mul,map_one] at h
  have hback := mul_invOfUnit (T.map g) 1 (by simpa using hmc)
  calc
    (T.invOfUnit 1).map g =
        (T.invOfUnit 1).map g * ((T.map g) * (T.map g).invOfUnit 1) := by rw [hback,mul_one]
    _ = _ := by rw [← mul_assoc,h,one_mul]

private lemma initial : a 0 = 1 := by rw [a]; simp

private abbrev φ := Int.castRingHom (ZMod 2)
private noncomputable def F := (PowerSeries.mk a).map φ

private lemma f0 : F.constantCoeff=1 := by
  rw [← coeff_zero_eq_constantCoeff_apply]
  simp [F,coeff_map,initial,φ]

private lemma shifted (n : ℕ) : F.coeff (n+1) = (F.invOfUnit 1).coeff n := by
  let P : PowerSeries ℤ := PowerSeries.mk fun k => if _h : k<n+1 then a k else 0
  let T := convergent P 1 2 (n+1)
  have hcP : P.constantCoeff=1 := by simp [P,initial]
  have hcT : T.constantCoeff=1 := conv_constant _ _ hcP (by simp) _ _
  have recval : a (n+1) = -(PowerSeries.coeff (n+1) (P-X*T.invOfUnit 1)) := by
    conv_lhs => rw [a]
    simp only [Nat.add_one_ne_zero, ↓reduceIte, convergent, Nat.cast_one, one_pow, map_one, one_mul]
    rfl
  rw [map_sub,coeff_succ_X_mul,show P.coeff (n+1) = 0 by simp [P],zero_sub,neg_neg] at recval
  have hT : T.map φ = P.map φ := by
    change (P - C (4 : ℤ) * X * (convergent P 1 3 n).invOfUnit 1).map φ = P.map φ
    rw [map_sub,map_mul,map_mul,map_C,show φ 4=0 by decide,map_zero,zero_mul,zero_mul,sub_zero]
  have hmP : (P.map φ).constantCoeff=1 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, hcP, map_one]
  have hdiv : (X : PowerSeries (ZMod 2))^(n+1) ∣ F-P.map φ := by
    apply X_pow_dvd_iff.mpr
    intro k hk
    simp [F,P,coeff_map,show k ≤ n by omega]
  have hi := X_pow_dvd_iff.mp (inverse_congruence F (P.map φ) f0 hmP (n+1) hdiv) n (by omega)
  rw [map_sub,sub_eq_zero] at hi
  change ((PowerSeries.mk a).map φ).coeff (n+1) = _
  rw [coeff_map,coeff_mk,recval,← coeff_map, map_inverse φ T hcT,hT,hi]

private lemma quadratic : F^2 = X-F := by
  have h : F = 1 + X * F.invOfUnit 1 := by
    ext n
    cases n with
    | zero => simp [coeff_zero_eq_constantCoeff, f0]
    | succ n => simpa [coeff_one] using shifted n
  have hprod := invOfUnit_mul F 1 (by simpa using f0)
  have hdiff : (F-1)*F=X := calc
    _ = (X*F.invOfUnit 1)*F := by congr 1; linear_combination h
    _ = _ := by rw [mul_assoc,hprod,mul_one]
  have hneg : -F=F := by ext n; rw [map_neg]; exact CharTwo.neg_eq _
  rw [sub_eq_add_neg,hneg]
  linear_combination hdiff

private lemma square_expands (F : PowerSeries (ZMod 2)) :
    F ^ 2 = PowerSeries.expand 2 (by decide) F := by
  have h := MvPowerSeries.map_frobenius_expand (f := F) 2 (by decide)
  simpa [PowerSeries.expand] using h.symm

private lemma parity_indices (F : PowerSeries (ZMod 2)) (hF : F ^ 2 = X - F) :
    ∀ n : ℕ, 1 ≤ n → (F.coeff n ≠ 0 ↔ ∃ k : ℕ, n = 2 ^ k) := by
  rw [square_expands] at hF
  have recur (n : ℕ) : F.coeff n = (if n = 1 then 1 else 0) -
      (if 2 ∣ n then F.coeff (n / 2) else 0) := by
    have hc := congrArg (PowerSeries.coeff (R := ZMod 2) n) hF
    rw [coeff_expand, map_sub, coeff_X] at hc
    linear_combination hc
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    by_cases h1 : n = 1
    · subst n
      constructor
      · exact fun _ => ⟨0, by decide⟩
      · intro _
        rw [recur 1]
        norm_num
    by_cases hd : 2 ∣ n
    · obtain ⟨j, hj⟩ := hd
      have hlt : j < n := by omega
      have hjpos : 1 ≤ j := by omega
      have hrec := recur n
      rw [if_neg h1, if_pos (show 2 ∣ n from ⟨j, hj⟩), show n / 2 = j by omega,
        zero_sub] at hrec
      rw [hrec, neg_ne_zero, ih j hlt hjpos]
      constructor
      · rintro ⟨k, rfl⟩
        exact ⟨k + 1, by simpa [pow_succ, Nat.mul_comm] using hj⟩
      · rintro ⟨k, hk⟩
        cases k with
        | zero => exact (h1 (by simpa using hk)).elim
        | succ k =>
          rw [pow_succ] at hk
          exact ⟨k, by omega⟩
    · rw [recur n, if_neg h1, if_neg hd, sub_self]
      constructor
      · exact fun h => (h rfl).elim
      · rintro ⟨k, hk⟩
        cases k with
        | zero => exact (h1 (by simpa using hk)).elim
        | succ k =>
          exact (hd ⟨2 ^ k, by simpa [pow_succ, Nat.mul_comm] using hk⟩).elim

lemma parity (n : ℕ) : Odd (a n) ↔ n=0 ∨ ∃ k : ℕ, n = 2^k := by
  by_cases hz : n=0
  · subst n
    simp [initial]
  have hp := parity_indices F quadratic n (by omega)
  change ((PowerSeries.mk a).map φ).coeff n ≠ 0 ↔ _ at hp
  rw [coeff_map,coeff_mk] at hp
  change (a n : ZMod 2) ≠ 0 ↔ _ at hp
  rw [ne_eq, ZMod.intCast_zmod_eq_zero_iff_dvd] at hp
  change (¬ (2 : ℤ) ∣ a n) ↔ _ at hp
  rw [← even_iff_two_dvd, Int.not_even_iff_odd] at hp
  simpa [hz] using hp

end OMA.A158119

theorem OMA.solution : type_of% @OMA.S_oeis_a158119.main := by
  exact OMA.A158119.parity

