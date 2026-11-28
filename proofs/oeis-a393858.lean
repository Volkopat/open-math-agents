import OMAStatements.S_oeis_a393858
import Mathlib.Algebra.CharP.Two
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Hanna's reversion equation modulo two and seven

Substituting X times a unit of constant term one preserves the leading
coefficient. Changing the unknown coefficient of index n in the inner
series changes its argument only from degree n+1 onwards. These facts
both justify the integral recursion and establish uniqueness over each
residue field.

Source: https://oeis.org/A393858. Credit: @Solitude1312
-/

open PowerSeries OMA.S_oeis_a393858

namespace OMA.A393858

private lemma scaled_zero {R : Type*} [CommRing R] (c : R) (F : PowerSeries R) :
    (scaled c F).constantCoeff = 0 := by simp [scaled]

private lemma argument_zero {R : Type*} [CommRing R] (c : R) (F : PowerSeries R) :
    (inner c F).constantCoeff = 0 := by simp [inner]

private lemma subst_constant {R : Type*} [CommRing R] (T H : PowerSeries R)
    (hT : T.constantCoeff = 0) : PowerSeries.constantCoeff (PowerSeries.subst T H) = H.constantCoeff := by
  have hh : HasSubst T := HasSubst.of_constantCoeff_zero hT
  have hz : (H - C H.constantCoeff).constantCoeff = 0 := by simp
  have h := PowerSeries.constantCoeff_subst_eq_zero (a := T) hT (H-C H.constantCoeff) hz
  change constantCoeff (PowerSeries.subst T (H-C H.constantCoeff)) = 0 at h
  rw [subst_sub hh, subst_C] at h
  change constantCoeff (PowerSeries.subst T H - C H.constantCoeff) = 0 at h
  rw [map_sub, constantCoeff_C, sub_eq_zero] at h
  exact h

/-- Fixed inner substitution preserves the first coefficient that can differ. -/
private lemma fixed_delta {R : Type*} [CommRing R] (V F G : PowerSeries R)
    (hV : V.constantCoeff = 1) (n : ℕ) (hag : ∀ k < n, F.coeff k = G.coeff k) :
    PowerSeries.coeff n (PowerSeries.subst (X*V) F) - PowerSeries.coeff n (PowerSeries.subst (X*V) G) =
    F.coeff n - G.coeff n := by
  have hzero : (X*V).constantCoeff = 0 := by simp
  have ht : HasSubst (X*V) := HasSubst.of_constantCoeff_zero hzero
  obtain ⟨H,hh⟩ : (X : PowerSeries R)^n ∣ F-G := by
    apply X_pow_dvd_iff.mpr
    intro k hk
    simp [hag k hk]
  have shift (B : PowerSeries R) : (X^n * B).coeff n = B.constantCoeff := by
    simpa [coeff_zero_eq_constantCoeff] using coeff_X_pow_mul B n 0
  have hd : F.coeff n - G.coeff n = H.constantCoeff := by rw [← map_sub, hh, shift]
  rw [← map_sub, ← subst_sub ht, hh, subst_mul ht, subst_pow ht, subst_X ht, mul_pow, mul_assoc,
    shift, map_mul, map_pow, hV, one_pow, one_mul, subst_constant (X*V) H hzero, hd]

private lemma fixed_injective {R : Type*} [CommRing R] (V : PowerSeries R) (hV : V.constantCoeff=1) :
    Function.Injective (PowerSeries.subst (R := R) (X*V)) := by
  intro F G h
  ext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hd := fixed_delta V F G hV n ih
    rw [h, sub_self] at hd
    exact sub_eq_zero.mp hd.symm

private lemma inner_agrees {R : Type*} [CommRing R] (c : R) (F G : PowerSeries R) (n : ℕ)
    (hag : ∀ k < n, F.coeff k = G.coeff k) :
    (X : PowerSeries R)^(n+1) ∣ inner c F - inner c G := by
  obtain ⟨D, hD⟩ : (X : PowerSeries R)^n ∣ scaled c F - scaled c G := by
    apply X_pow_dvd_iff.mpr
    intro k hk
    cases k with
    | zero => simp [scaled]
    | succ k => simp [scaled, hag (k+1) hk]
  refine ⟨-D, ?_⟩
  unfold inner
  rw [pow_succ]
  linear_combination -X * hD

private lemma subst_congr_inner {R : Type*} [CommRing R] (F P Q : PowerSeries R) (n : ℕ)
    (hP : HasSubst P) (hQ : HasSubst Q) (hd : (X : PowerSeries R)^(n+1) ∣ P-Q) :
    PowerSeries.coeff n (PowerSeries.subst P F) = PowerSeries.coeff n (PowerSeries.subst Q F) := by
  rw [coeff_subst' hP, coeff_subst' hQ]
  apply finsum_congr
  intro i
  have hdiv := hd.trans ((Commute.all P Q).sub_dvd_pow_sub_pow i)
  have hcoeff := X_pow_dvd_iff.mp hdiv n (Nat.lt_succ_self n)
  rw [map_sub, sub_eq_zero] at hcoeff
  rw [hcoeff]

private lemma diagonal {R : Type*} [CommRing R] (c : R) (F G : PowerSeries R) (n : ℕ)
    (hag : ∀ k < n, F.coeff k = G.coeff k) :
    PowerSeries.coeff n (PowerSeries.subst (inner c F) F) - PowerSeries.coeff n (PowerSeries.subst (inner c G) G) =
      F.coeff n-G.coeff n := by
  have hi := subst_congr_inner G (inner c F) (inner c G) n
    (HasSubst.of_constantCoeff_zero (argument_zero ..))
    (HasSubst.of_constantCoeff_zero (argument_zero ..)) (inner_agrees c F G n hag)
  rw [← hi]
  exact fixed_delta (1-scaled c F) F G (by simp [scaled_zero]) n hag

private lemma unique_series {R : Type*} [CommRing R] (c : R) (F G : PowerSeries R)
    (hF : PowerSeries.subst (inner c F) F = X) (hG : PowerSeries.subst (inner c G) G = X) : F=G := by
  ext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have h := diagonal c F G n ih
    rw [hF,hG,sub_self] at h
    exact sub_eq_zero.mp h.symm

private lemma source_equation :
    PowerSeries.subst (inner (6 : ℤ) (PowerSeries.mk a)) (PowerSeries.mk a) = X := by
  ext n
  let P : PowerSeries ℤ := PowerSeries.mk fun k => if _h : k < n then a k else 0
  have hrec : a n = (X : PowerSeries ℤ).coeff n - PowerSeries.coeff n (PowerSeries.subst (inner (6 : ℤ) P) P) := by
    conv_lhs => rw [a]
  have h := diagonal (6 : ℤ) (PowerSeries.mk a) P n (by intro k hk; simp [P,hk])
  rw [coeff_mk, show P.coeff n = 0 by simp [P], sub_zero, hrec] at h
  omega

private lemma map_inner {R S : Type*} [CommRing R] [CommRing S] (h : R →+* S) (c : R)
    (F : PowerSeries R) : (inner c F).map h = inner (h c) (F.map h) := by
  have hs : (scaled c F).map h = scaled (h c) (F.map h) := by
    ext n
    cases n <;> simp [scaled,coeff_map]
  simp only [inner, map_mul, map_sub, map_X, map_one, hs]

private lemma mapped_equation {R : Type*} [CommRing R] (h : ℤ →+* R) :
    PowerSeries.subst (inner (h 6) ((PowerSeries.mk a).map h)) ((PowerSeries.mk a).map h) = X := by
  have he := congrArg (PowerSeries.map h) source_equation
  have hs := PowerSeries.map_subst (a := inner (6 : ℤ) (PowerSeries.mk a))
    (HasSubst.of_constantCoeff_zero (argument_zero ..)) (h := h) (PowerSeries.mk a)
  change PowerSeries.map h (PowerSeries.subst (inner (6 : ℤ) (PowerSeries.mk a)) (PowerSeries.mk a)) =
    PowerSeries.subst ((inner (6 : ℤ) (PowerSeries.mk a)).map h) ((PowerSeries.mk a).map h) at hs
  rw [hs, map_inner, map_X] at he
  exact he

private lemma normalized {R : Type*} [CommRing R] (c : R) (F : PowerSeries R)
    (h : PowerSeries.subst (inner c F) F = X) : F.constantCoeff = 0 ∧ F.coeff 1 = 1 := by
  have hc := congrArg (PowerSeries.constantCoeff (R := R)) h
  rw [subst_constant _ F (argument_zero ..), constantCoeff_X] at hc
  refine ⟨hc, ?_⟩
  have hd := fixed_delta (1-scaled c F) F 0 (by simp [scaled_zero]) 1 (by
    intro k hk
    have : k=0 := by omega
    simp [this,coeff_zero_eq_constantCoeff,hc])
  have hs : HasSubst (inner c F) := HasSubst.of_constantCoeff_zero (argument_zero ..)
  change PowerSeries.coeff 1 (PowerSeries.subst (inner c F) F) -
    PowerSeries.coeff 1 (PowerSeries.subst (inner c F) (0 : PowerSeries R)) = _ at hd
  have hz : PowerSeries.subst (inner c F) (0 : PowerSeries R) = 0 := by
    rw [← coe_substAlgHom hs, map_zero]
  simpa only [h,hz,map_zero,sub_zero,coeff_one_X] using hd.symm

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

private lemma parity (n : ℕ) (hn : 0 < n) : Odd (a n) ↔ ∃ k : ℕ, n = 2^k := by
  let φ := Int.castRingHom (ZMod 2)
  let F := (PowerSeries.mk a).map φ
  have h := mapped_equation φ
  rw [show φ 6 = 0 by decide] at h
  change PowerSeries.subst (inner 0 F) F = X at h
  have h1 := (normalized 0 F h).2
  have hs : scaled (0 : ZMod 2) F = X := by
    ext k
    obtain (_ | _ | j) := k <;> simp [scaled, coeff_X, h1]
  rw [inner, hs] at h
  have ht : HasSubst (X * (1-X) : PowerSeries (ZMod 2)) :=
    HasSubst.of_constantCoeff_zero (show PowerSeries.constantCoeff (X*(1-X) : PowerSeries (ZMod 2))=0 by simp)
  have hneg : -(X : PowerSeries (ZMod 2)) = X := by
    ext k
    rw [map_neg]
    exact CharTwo.neg_eq _
  have hsq : F^2 + F = X := by
    apply fixed_injective (1-X) (by simp)
    rw [subst_add ht, subst_pow ht, h, subst_X ht, sub_eq_add_neg, hneg]
    ring
  have hp := parity_indices F (by linear_combination hsq) n hn
  change ((PowerSeries.mk a).map φ).coeff n ≠ 0 ↔ _ at hp
  rw [coeff_map,coeff_mk] at hp
  change (a n : ZMod 2) ≠ 0 ↔ _ at hp
  rw [ne_eq, ZMod.intCast_zmod_eq_zero_iff_dvd] at hp
  change (¬ (2 : ℤ) ∣ a n) ↔ _ at hp
  rwa [← even_iff_two_dvd, Int.not_even_iff_odd] at hp

private noncomputable def geometric : PowerSeries (ZMod 7) := X * PowerSeries.mk 1

private lemma geometric_coeff (n : ℕ) : geometric.coeff (n+1) = 1 := by
  simp [geometric]

private lemma geometric_solution :
    PowerSeries.subst (inner (6 : ZMod 7) geometric) geometric = X := by
  let B := scaled (6 : ZMod 7) geometric
  let T := inner (6 : ZMod 7) geometric
  have hb0 : B.coeff 0=0 := by simp [B,scaled]
  have hbc (n : ℕ) : B.coeff (n+1) = (6 : ZMod 7)^n := by
    simp [B,scaled,geometric_coeff]
  have hB : B*(1+X)=X := by
    ext n
    cases n with
    | zero => simp [B,scaled,coeff_zero_eq_constantCoeff]
    | succ k =>
      rw [mul_add,mul_one,map_add,coeff_succ_mul_X,coeff_X]
      cases k with
      | zero => simp [hbc,hb0]
      | succ k =>
        rw [hbc,hbc,if_neg (by omega),pow_succ]
        calc
          _ = (6 : ZMod 7)^k * (6+1) := by ring
          _ = 0 := by rw [show (6 : ZMod 7)+1=0 by decide,mul_zero]
  have hT : T*(1+X)=X := by
    change X*(1-B)*(1+X)=X
    linear_combination -X*hB
  have hG : geometric*(1-X)=X := by
    rw [geometric,mul_assoc,mk_one_mul_one_sub_eq_one,mul_one]
  have hcc : T.constantCoeff=0 := argument_zero .. 
  have ht : HasSubst T := HasSubst.of_constantCoeff_zero hcc
  have hcomp := congrArg (PowerSeries.subst T) hG
  have hone : PowerSeries.subst T (1 : PowerSeries (ZMod 7)) = 1 := by
    rw [← coe_substAlgHom ht, map_one]
  rw [subst_mul ht, subst_sub ht, hone, subst_X ht] at hcomp
  have hx : X*(1-T)=T := by linear_combination -hT
  have hunit : IsUnit (1-T) := PowerSeries.isUnit_iff_constantCoeff.mpr (by simp [hcc])
  exact hunit.mul_left_inj.mp (hcomp.trans hx.symm)

private lemma mod_seven (n : ℕ) (hn : 0<n) : Int.ModEq 7 (a n) 1 := by
  let φ := Int.castRingHom (ZMod 7)
  let F := (PowerSeries.mk a).map φ
  have h := mapped_equation φ
  rw [show φ 6 = (6 : ZMod 7) by decide] at h
  have eq := unique_series (6 : ZMod 7) F geometric h geometric_solution
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have hc := congrArg (PowerSeries.coeff (R := ZMod 7) (k+1)) eq
  change ((PowerSeries.mk a).map φ).coeff (k+1) = geometric.coeff (k+1) at hc
  rw [coeff_map,coeff_mk,geometric_coeff] at hc
  apply (ZMod.intCast_eq_intCast_iff _ _ 7).mp
  simpa [φ] using hc

end OMA.A393858

theorem OMA.solution : type_of% @OMA.S_oeis_a393858.main := by
  intro n hn
  exact ⟨OMA.A393858.parity n hn, OMA.A393858.mod_seven n hn⟩

