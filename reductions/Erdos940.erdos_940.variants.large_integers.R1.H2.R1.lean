import OMAReductions.R_Erdos940_erdos_940_variants_large_integers_R1
import Mathlib

-- Credit: @kumagi

/-!
Reduce the quartic infinitude case to two signed sums over the good odd primes.
The first is the rational quadratic contribution. The second is the split-prime
correction, which consists of the Gaussian finite-character and infinity-type-two
contributions.

The proof follows the valuation-one and simultaneous-sign argument in
https://erdosproblems.ai/wiki/research/erdos_940/quartic_complement
and uses quadratic reciprocity directly for the exceptional coefficients.
The needed prime-harmonic estimates are the two components of Equation (10) in
https://erdosproblems.ai/wiki/research/erdos_940/quartic_euler_majorant
-/

namespace Erdos940Quartic

open Finset ZMod Polynomial

/-- Ordered solutions of a weighted quartic over a finite ring. -/
private def Solutions {R : Type} [CommRing R] (a : Fin 4 → R) (u : R) :=
  {x : Fin 4 → R // (∑ i, a i * (x i)^4) = u}

private noncomputable def count {R : Type} [CommRing R] (a : Fin 4 → R) (u : R) : ℕ :=
  Nat.card (Solutions a u)

private noncomputable def exponentialSum {F : Type} [Field F] [Fintype F]
    (ψ : AddChar F ℂ) (s : F) : ℂ := ∑ x : F, ψ (s*x^4)

/-- The Fourier factorization for the zero target. -/
theorem count_zero_fourier {F : Type} [Field F] [Fintype F]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (a : Fin 4 → F) :
    (Fintype.card F : ℂ) * (count a 0 : ℂ) =
      ∑ t : F, ∏ i, exponentialSum ψ (t*a i) := by
  classical
  let f (v : Fin 4 → F) : F := ∑ i, a i * (v i)^4
  have hOrth (v : Fin 4 → F) : (∑ t : F, ψ (t * f v)) =
      if f v = 0 then (Fintype.card F : ℂ) else 0 := by
    simpa only [Nat.cast_ite, Nat.cast_zero] using AddChar.sum_mulShift (f v) hψ
  have hZero : (univ.filter (fun v : Fin 4 → F => f v = 0)).card = count a 0 := by
    simp only [count, Solutions, Nat.card_eq_fintype_card, Fintype.card_subtype, f]
  have hFactor (t : F) (v : Fin 4 → F) (S : Finset (Fin 4)) :
      ψ (∑ i ∈ S, (t*a i) * (v i)^4) = ∏ i ∈ S, ψ ((t*a i) * (v i)^4) := by
    induction S using Finset.induction_on with
    | empty => simp
    | insert j S hj ih => rw [sum_insert hj, prod_insert hj, AddChar.map_add_eq_mul, ih]
  calc
    _ = ∑ v : Fin 4 → F, (if f v = 0 then (Fintype.card F : ℂ) else 0) := by
      rw [← Finset.sum_filter, sum_const, nsmul_eq_mul, hZero, mul_comm]
    _ = ∑ v : Fin 4 → F, ∑ t : F, ψ (t * f v) := by simp [hOrth]
    _ = ∑ t : F, ∑ v : Fin 4 → F, ψ (t * f v) := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro t _
      simp only [f, mul_sum, ← mul_assoc, hFactor]
      exact (Fintype.prod_sum (fun i : Fin 4 => fun x : F => ψ (t*a i*x^4))).symm

private theorem sq_eq_one_of_fourth_eq_one {p : ℕ} [Fact p.Prime]
    (hp : p % 4 = 3) {x : ZMod p} (hx : x^4 = 1) : x^2 = 1 := by
  have hn : x ≠ 0 := fun h => by simp [h] at hx
  have hF : x^(p-1) = 1 := ZMod.pow_card_sub_one_eq_one hn
  have he : p - 1 = 4 * (p / 4) + 2 := by omega
  rwa [he, pow_add, pow_mul, hx, one_pow, one_mul] at hF

private theorem square_has_fourth_root {p : ℕ} [Fact p.Prime] (hp : p % 4 = 3)
    {y : ZMod p} (hy : IsSquare y) : ∃ x : ZMod p, x^4 = y := by
  obtain ⟨v, hv⟩ := hy
  have he : ((p+1)/4)*4 = p+1 := by omega
  refine ⟨v^((p+1)/4), ?_⟩
  rw [← pow_mul, he, pow_succ, ZMod.pow_card, hv]

private theorem fourth_fiber_eq_square_fiber {p : ℕ} [Fact p.Prime]
    (hp : p % 4 = 3) (u : ZMod p) :
    Nat.card {v : ZMod p // v^4 = u} = Nat.card {v : ZMod p // v^2 = u} := by
  classical
  by_cases hu : u = 0
  · subst u
    simp only [pow_eq_zero_iff (by decide : (4 : ℕ) ≠ 0),
      pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)]
  by_cases hs : IsSquare u
  · obtain ⟨x, hx⟩ := square_has_fourth_root hp hs
    have hx0 : x ≠ 0 := fun h => hu (by simpa [h] using hx.symm)
    let E : ZMod p ≃ ZMod p :=
      { toFun := fun v => x*v
        invFun := fun v => v/x
        left_inv := fun v => by
          change (x*v)/x = v
          rw [mul_comm, mul_div_cancel_right₀ _ hx0]
        right_inv := fun v => by
          change x*(v/x) = v
          rw [mul_comm, div_mul_cancel₀ _ hx0] }
    apply Nat.card_congr (E.subtypeEquiv ?_)
    intro v
    change v^4 = u ↔ (x*v)^2 = u
    constructor
    · intro h
      have hv : (v/x)^4 = 1 := by rw [div_pow, h, hx, div_self hu]
      have he := sq_eq_one_of_fourth_eq_one hp hv
      rw [div_pow, div_eq_iff (pow_ne_zero _ hx0), one_mul] at he
      rw [mul_pow, he, ← pow_add, hx]
    · intro h
      have hv : (x*v)^2 * (x*v)^2 = u*u := congrArg (fun z => z*z) h
      have hv' : x^4 * v^4 = u*u := by
        calc
          _ = (x*v)^2*(x*v)^2 := by ring
          _ = _ := hv
      rw [hx] at hv'
      exact mul_left_cancel₀ hu hv'
  · have h4 : IsEmpty {v : ZMod p // v^4 = u} :=
      ⟨fun v => hs ⟨v.val^2, by rw [← pow_add]; exact v.property.symm⟩⟩
    have h2 : IsEmpty {v : ZMod p // v^2 = u} := ⟨fun v => hs ⟨v.val, by rw [← pow_two]; exact v.property.symm⟩⟩
    simp

private noncomputable def quadraticComplex (F : Type) [Field F] [Fintype F] [DecidableEq F] :
    MulChar F ℂ :=
  (quadraticChar F).ringHomComp (Int.castRingHom ℂ)

private theorem quadratic_apply {F : Type} [Field F] [Fintype F] [DecidableEq F] (t : F) :
    quadraticComplex F t = (quadraticChar F t : ℂ) := rfl

private theorem quadratic_sq_one {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {t : F} (ht : t ≠ 0) : quadraticComplex F t ^ 2 = 1 := by
  rw [quadratic_apply]
  exact_mod_cast quadraticChar_sq_one ht

private theorem quadratic_ne_one {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (hF : ringChar F ≠ 2) : quadraticComplex F ≠ 1 := by
  intro h
  apply quadraticChar_ne_one hF
  apply MulChar.ext
  intro x
  have hEq := congrArg (fun χ : MulChar F ℂ => χ (x : F)) h
  rw [quadratic_apply, MulChar.one_apply_coe] at hEq
  rw [MulChar.one_apply_coe]
  exact_mod_cast hEq

private theorem quadratic_character_pow {F : Type} [Field F] [Fintype F] [DecidableEq F] :
    quadraticComplex F ^ 2 = 1 := by
  apply MulChar.ext
  intro x
  rw [(quadraticComplex F).pow_apply' (by decide : (2 : ℕ) ≠ 0), quadratic_sq_one x.ne_zero,
    MulChar.one_apply_coe]

private theorem quadratic_gauss_fourth {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (hF : ringChar F ≠ 2) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) :
    gaussSum (quadraticComplex F) ψ ^ 4 = (Fintype.card F : ℂ)^2 := by
  let χ := quadraticComplex F
  have hχ : orderOf χ = 2 := orderOf_eq_prime quadratic_character_pow (quadratic_ne_one hF)
  have h := gaussSum_mul_gaussSum_pow_orderOf_sub_one (quadratic_ne_one hF) hψ
  change gaussSum χ ψ * gaussSum (χ^(orderOf χ - 1)) ψ = _ at h
  rw [hχ, show (2 : ℕ) - 1 = 1 by decide, pow_one, ← pow_two] at h
  change gaussSum χ ψ ^ 2 = χ (-1) * (Fintype.card F : ℂ) at h
  change gaussSum χ ψ ^ 4 = _
  rw [show (4 : ℕ) = 2*2 by decide, pow_mul, h, mul_pow, quadratic_sq_one (neg_ne_zero.mpr one_ne_zero), one_mul]

private theorem inert_exponential {p : ℕ} [Fact p.Prime] (hp : p % 4 = 3)
    {ψ : AddChar (ZMod p) ℂ} (hψ : ψ.IsPrimitive) {s : ZMod p} (hs : s ≠ 0) :
    exponentialSum ψ s = quadraticComplex (ZMod p) s * gaussSum (quadraticComplex (ZMod p)) ψ := by
  classical
  let χ := quadraticComplex (ZMod p)
  have hp2 : ringChar (ZMod p) ≠ 2 := by rw [ringChar_zmod_n]; omega
  have hFiber (u : ZMod p) :
      (Nat.card {v : ZMod p // v^4 = u} : ℂ) = 1 + χ u := by
    rw [fourth_fiber_eq_square_fiber hp, Nat.card_eq_fintype_card, Fintype.card_subtype]
    have h := quadraticChar_card_sqrts hp2 u
    have h' : ((Finset.univ.filter fun v : ZMod p => v^2 = u).card : ℤ) =
        quadraticChar (ZMod p) u + 1 := by
      simpa only [Set.toFinset_ofPred] using h
    have hC := congrArg (Int.cast : ℤ → ℂ) h'
    simpa only [χ, quadratic_apply, Int.cast_add, Int.cast_natCast, Int.cast_one, add_comm] using hC
  have he : exponentialSum ψ s = ∑ y : ZMod p, (1 + χ y) * ψ (s*y) := by
    unfold exponentialSum
    rw [← Finset.sum_fiberwise' univ (fun v : ZMod p => v^4) (fun y => ψ (s*y))]
    apply Finset.sum_congr rfl
    intro y _
    rw [Finset.sum_const, nsmul_eq_mul, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card, hFiber]
  have hz : (∑ y : ZMod p, ψ (s*y)) = 0 := by
    simpa only [mul_comm s, if_neg hs, Nat.cast_zero] using AddChar.sum_mulShift s hψ
  have hInv : χ⁻¹ = χ := by
    apply inv_eq_of_mul_eq_one_right
    exact (pow_two χ).symm.trans quadratic_character_pow
  have hG := gaussSum_mulShift_eq χ ψ (Units.mk0 s hs)
  rw [hInv] at hG
  rw [he]
  simp only [add_mul, one_mul, Finset.sum_add_distrib, hz, zero_add]
  simpa only [gaussSum, AddChar.mulShift_apply, Units.val_mk0, mul_comm s] using hG

/-- The exact zero-class formula at primes congruent to 3 modulo 4,
with arbitrary nonzero quartic coefficients. -/
theorem inert_zero_count {p : ℕ} [Fact p.Prime] (hp : p % 4 = 3)
    (a : Fin 4 → ZMod p) (ha : ∀ i, a i ≠ 0) :
    (count a 0 : ℂ) = (p : ℂ)^3 +
      quadraticComplex (ZMod p) (∏ i, a i) * (p : ℂ) * ((p : ℂ)-1) := by
  classical
  let χ := quadraticComplex (ZMod p)
  let ψ : AddChar (ZMod p) ℂ := ZMod.stdAddChar
  have hψ : ψ.IsPrimitive := ZMod.isPrimitive_stdAddChar p
  let G := gaussSum χ ψ
  have hp2 : ringChar (ZMod p) ≠ 2 := by rw [ringChar_zmod_n]; omega
  have hG : G^4 = (p : ℂ)^2 := by simpa only [G, χ, ZMod.card] using quadratic_gauss_fourth hp2 hψ
  have hnonzero (t : ZMod p) (ht : t ≠ 0) :
      (∏ i, exponentialSum ψ (t*a i)) = χ (∏ i, a i) * (p : ℂ)^2 := by
    calc
      _ = ∏ i, χ t * (χ (a i) * G) := by
        apply Finset.prod_congr rfl
        intro i _
        rw [inert_exponential hp hψ (mul_ne_zero ht (ha i)), ← mul_assoc, map_mul]
      _ = χ t^4 * (χ (∏ i, a i) * G^4) := by
        simp only [Finset.prod_mul_distrib, Finset.prod_const, card_univ, Fintype.card_fin, map_prod]
      _ = _ := by
        have h4 : χ t^4 = 1 := by
          rw [show (4 : ℕ) = 2*2 by decide, pow_mul, quadratic_sq_one ht, one_pow]
        rw [hG, h4, one_mul]
  have hzero : (∏ i : Fin 4, exponentialSum ψ ((0 : ZMod p)*a i)) = (p : ℂ)^4 := by
    simp [exponentialSum, ZMod.card]
  have hS := count_zero_fourier hψ a
  rw [ZMod.card, ← Finset.sum_erase_add _ _ (mem_univ (0 : ZMod p)), hzero] at hS
  have hconst : (∑ t ∈ (univ : Finset (ZMod p)).erase 0, ∏ i, exponentialSum ψ (t*a i)) =
      ((p : ℂ)-1) * (χ (∏ i, a i) * (p : ℂ)^2) := by
    rw [Finset.sum_congr rfl (fun t ht => hnonzero t (mem_erase.mp ht).1),
      sum_const, nsmul_eq_mul, Finset.card_erase_of_mem (mem_univ (0 : ZMod p)), card_univ,
      ZMod.card, Nat.cast_sub (Fact.out : p.Prime).pos, Nat.cast_one]
  rw [hconst] at hS
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  apply mul_left_cancel₀ hp0
  rw [hS]
  ring

end Erdos940Quartic


namespace Erdos940Quartic

open Finset

private def digits (p : ℕ) [NeZero p] : ZMod p × ZMod p ≃ ZMod (p*p) where
  toFun x := ((x.1.val + p*x.2.val : ℕ) : ZMod (p*p))
  invFun x := ((x.val : ZMod p), ((x.val/p : ℕ) : ZMod p))
  left_inv x := by
    have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
    have h1 := ZMod.val_lt x.1
    have h2 := ZMod.val_lt x.2
    have hx : x.1.val + p*x.2.val < p*p := by
      calc
        _ < p + p*x.2.val := Nat.add_lt_add_right h1 _
        _ = p*(x.2.val+1) := by ring
        _ ≤ p*p := Nat.mul_le_mul_left _ h2
    have he : (↑(x.1.val + p*x.2.val) : ZMod (p*p)).val = x.1.val+p*x.2.val :=
      ZMod.val_natCast_of_lt hx
    apply Prod.ext
    · change ((↑(x.1.val + p*x.2.val) : ZMod (p*p)).val : ZMod p) = x.1
      rw [he, Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul, add_zero, ZMod.natCast_zmod_val]
    · change (((↑(x.1.val + p*x.2.val) : ZMod (p*p)).val / p : ℕ) : ZMod p) = x.2
      rw [he, Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt h1, zero_add, ZMod.natCast_zmod_val]
  right_inv x := by
    have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
    have hq : x.val / p < p := (Nat.div_lt_iff_lt_mul hp).2 x.val_lt
    change (((x.val : ZMod p).val + p*((x.val/p : ℕ) : ZMod p).val : ℕ) : ZMod (p*p)) = x
    rw [ZMod.val_natCast, ZMod.val_natCast_of_lt hq, Nat.mod_add_div, ZMod.natCast_zmod_val]

private abbrev Vec (R : Type) := Fin 4 → R

private def liftEquiv (p : ℕ) [NeZero p] : Vec (ZMod p) × Vec (ZMod p) ≃ Vec (ZMod (p*p)) where
  toFun x i := digits p (x.1 i, x.2 i)
  invFun x := (fun i => ((digits p).symm (x i)).1, fun i => ((digits p).symm (x i)).2)
  left_inv x := Prod.ext
    (funext fun i => congrArg Prod.fst ((digits p).symm_apply_apply (x.1 i, x.2 i)))
    (funext fun i => congrArg Prod.snd ((digits p).symm_apply_apply (x.1 i, x.2 i)))
  right_inv x := funext fun i => (digits p).apply_symm_apply (x i)

private theorem quartic_binomial_lift (p x y : ℕ) :
    (↑(x+p*y) : ZMod (p*p))^4 = (x : ZMod (p*p))^4 +
      (p : ZMod (p*p)) * (4*(x : ZMod (p*p))^3*(y : ZMod (p*p))) := by
  push_cast
  have hp : (p : ZMod (p*p))^2 = 0 := by
    rw [pow_two, ← Nat.cast_mul, ZMod.natCast_self]
  linear_combination ((6*(x : ZMod (p*p))^2*(y : ZMod (p*p))^2) +
    (4*(p : ZMod (p*p))*(x : ZMod (p*p))*(y : ZMod (p*p))^3) +
    (p : ZMod (p*p))^2*(y : ZMod (p*p))^4) * hp

private def carryNumerator {p : ℕ} (a : Vec ℕ) (x : Vec (ZMod p)) : ℕ :=
  ∑ i, a i*(x i).val^4

private def derivative {p : ℕ} (a : Vec ℕ) (x : Vec (ZMod p)) : Vec (ZMod p) :=
  fun i => 4*(a i : ZMod p)*(x i)^3

private def tangentNumerator {p : ℕ} (a : Vec ℕ) (x y : Vec (ZMod p)) : ℕ :=
  ∑ i, 4*a i*(x i).val^3*(y i).val

private theorem carry_cast {p : ℕ} [NeZero p] (a : Vec ℕ) (x : Vec (ZMod p)) :
    (carryNumerator a x : ZMod p) = ∑ i, (a i : ZMod p)*(x i)^4 := by
  simp only [carryNumerator, Nat.cast_sum, Nat.cast_mul, Nat.cast_pow, ZMod.natCast_zmod_val]

private theorem tangent_cast {p : ℕ} [NeZero p] (a : Vec ℕ) (x y : Vec (ZMod p)) :
    (tangentNumerator a x y : ZMod p) = ∑ i, derivative a x i * y i := by
  simp only [tangentNumerator, derivative, Nat.cast_sum, Nat.cast_mul, Nat.cast_pow,
    Nat.cast_ofNat, ZMod.natCast_zmod_val]

private theorem lifted_sum_cast {p : ℕ} [NeZero p] (a : Vec ℕ) (x y : Vec (ZMod p)) :
    (∑ i, (a i : ZMod (p*p))*((liftEquiv p (x,y)) i)^4) =
      (↑(carryNumerator a x + p*tangentNumerator a x y) : ZMod (p*p)) := by
  rw [Nat.cast_add, Nat.cast_mul]
  unfold carryNumerator tangentNumerator
  rw [Nat.cast_sum, Nat.cast_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  change (a i : ZMod (p*p)) * (↑((x i).val+p*(y i).val) : ZMod (p*p))^4 = _
  rw [quartic_binomial_lift]
  push_cast
  ring

private theorem lift_condition {p : ℕ} [NeZero p] (a : Vec ℕ) (x y : Vec (ZMod p)) :
    (∑ i, (a i : ZMod (p*p))*((liftEquiv p (x,y)) i)^4) = (p : ZMod (p*p)) ↔
      (∑ i, (a i : ZMod p)*(x i)^4 = 0) ∧
        ((carryNumerator a x / p : ℕ) : ZMod p) + ∑ i, derivative a x i * y i = 1 := by
  let A := carryNumerator a x
  let B := tangentNumerator a x y
  rw [lifted_sum_cast]
  change (↑(A+p*B) : ZMod (p*p)) = (p : ZMod (p*p)) ↔ _
  rw [ZMod.natCast_eq_natCast_iff, ← carry_cast, ← tangent_cast]
  have hD (h : p ∣ A) : A+p*B = p*(A/p+B) := by
    rw [mul_add, Nat.mul_div_cancel' h]
  constructor
  · intro h
    have hsmall := h.of_dvd (dvd_mul_right p p)
    have he := (ZMod.natCast_eq_natCast_iff (A+p*B) p p).2 hsmall
    have hA : (A : ZMod p) = 0 := by
      simpa only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul, add_zero] using he
    have hAd : p ∣ A := (ZMod.natCast_eq_zero_iff _ _).mp hA
    have h' : p*(A/p+B) ≡ p*1 [MOD p*p] := by simpa only [hD hAd, Nat.mul_one] using h
    have hh := Nat.ModEq.mul_left_cancel' (NeZero.ne p) h'
    exact ⟨hA, by
      rw [← Nat.cast_add]
      simpa only [Nat.cast_one] using (ZMod.natCast_eq_natCast_iff (A/p+B) 1 p).2 hh⟩
  · rintro ⟨hA, hB⟩
    have hAd : p ∣ A := (ZMod.natCast_eq_zero_iff _ _).mp hA
    have hh := (ZMod.natCast_eq_natCast_iff (A/p+B) 1 p).1
      (by simpa only [Nat.cast_add, Nat.cast_one] using hB)
    simpa only [hD hAd, Nat.mul_one] using hh.mul_left' p

end Erdos940Quartic

namespace Erdos940Quartic

open Finset

private abbrev Other (j : Fin 4) := {i : Fin 4 // i ≠ j}

private theorem other_card (j : Fin 4) : Nat.card (Other j) = 3 := by
  classical
  let T : Finset (Fin 4) := Finset.univ.erase j
  let e : Other j ≃ T :=
    { toFun := fun i => ⟨i.val, Finset.mem_erase.mpr ⟨i.property, Finset.mem_univ _⟩⟩
      invFun := fun i => ⟨i.val, (Finset.mem_erase.mp i.property).1⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe]
  simp [T]

private def dot {F : Type} [CommRing F] (c x : Vec F) : F := ∑ i, c i*x i

private theorem dot_fiber_card {F : Type} [Field F] [Fintype F] (c : Vec F) (u : F)
    (j : Fin 4) (hc : c j ≠ 0) :
    Nat.card {x : Vec F // dot c x = u} = Fintype.card F^3 := by
  classical
  let off (x : Other j → F) (i : Fin 4) : F :=
    if h : i ≠ j then x ⟨i,h⟩ else 0
  let total (x : Other j → F) : F := ∑ i ∈ Finset.univ.erase j, c i * off x i
  let fill (x : Other j → F) (i : Fin 4) : F :=
    if h : i ≠ j then x ⟨i,h⟩ else (u-total x)/c j
  have hOther (x : Other j → F) (i : Fin 4) (hi : i ∈ Finset.univ.erase j) :
      fill x i = off x i := by
    have hn := (Finset.mem_erase.mp hi).1
    simp [fill, off, hn]
  have hFill (x : Other j → F) : dot c (fill x) = u := by
    unfold dot
    rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ j)]
    have hS : (∑ i ∈ Finset.univ.erase j, c i * fill x i) = total x :=
      Finset.sum_congr rfl (fun i hi => by rw [hOther x i hi])
    rw [hS, show fill x j = (u-total x)/c j by simp [fill],
      mul_comm (c j), div_mul_cancel₀ _ hc]
    ring
  let e : {x : Vec F // dot c x = u} ≃ (Other j → F) :=
    { toFun := fun x i => x.val i.val
      invFun := fun x => ⟨fill x, hFill x⟩
      right_inv := by intro x; funext i; simp [fill, i.property]
      left_inv := by
        intro x
        apply Subtype.ext
        funext i
        change fill (fun k => x.val k.val) i = x.val i
        by_cases hi : i ≠ j
        · simp [fill, hi]
        · obtain rfl := not_ne_iff.mp hi
          rw [show fill (fun k => x.val k.val) i =
            (u-total (fun k => x.val k.val))/c i by simp [fill]]
          apply (div_eq_iff hc).mpr
          have hx := x.property
          unfold dot at hx
          rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ i)] at hx
          have hh : total (fun k => x.val k.val) =
              ∑ k ∈ Finset.univ.erase i, c k * x.val k := by
            apply Finset.sum_congr rfl
            intro k hk
            simp [off, (Finset.mem_erase.mp hk).1]
          rw [hh]
          linear_combination -hx }
  rw [Nat.card_congr e, Nat.card_fun, other_card, Nat.card_eq_fintype_card]

private theorem four_nonzero_mod_prime {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    (4 : ZMod p) ≠ 0 := by
  intro h
  have hd : p ∣ 2*2 := (ZMod.natCast_eq_zero_iff 4 p).mp h
  have hp : p.Prime := Fact.out
  have h2 := (hp.dvd_mul.mp hd).elim id id
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)

private theorem no_singular_lift {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (a : Vec ℕ) (ha : ∀ i, (4 : ℕ).Full (a i)) (x : Vec (ZMod p))
    (hSing : ¬ ∃ i, derivative a x i ≠ 0) :
    IsEmpty {y : Vec (ZMod p) // ((carryNumerator a x / p : ℕ) : ZMod p) +
      dot (derivative a x) y = 1} := by
  have hp : p.Prime := Fact.out
  have hz (i : Fin 4) : derivative a x i = 0 := by
    by_contra hn
    exact hSing ⟨i, hn⟩
  have hD : p*p ∣ carryNumerator a x := by
    unfold carryNumerator
    apply Finset.dvd_sum
    intro i _
    have hZI := hz i
    unfold derivative at hZI
    rcases mul_eq_zero.mp hZI with hzero | hv
    · have hA := (mul_eq_zero.mp hzero).resolve_left (four_nonzero_mod_prime hp2)
      have hpa : p ∣ a i := (ZMod.natCast_eq_zero_iff _ _).mp hA
      have hpow : p^4 ∣ a i := by
        by_cases h : a i = 0
        · simp [h]
        exact ha i p (Nat.mem_primeFactors.mpr ⟨hp, hpa, h⟩)
      exact (show p*p ∣ p^4 by simpa only [pow_two] using (pow_dvd_pow p (by decide : 2 ≤ 4))).trans
        (hpow.trans (dvd_mul_right _ _))
    · have hx : x i = 0 := (pow_eq_zero_iff (by decide : (3 : ℕ) ≠ 0)).mp hv
      simp [hx]
  have hpD : p ∣ carryNumerator a x / p := by
    obtain ⟨k, hk⟩ := hD
    rw [hk, mul_assoc, Nat.mul_div_cancel_left _ hp.pos]
    exact dvd_mul_right _ _
  have hc : ((carryNumerator a x / p : ℕ) : ZMod p) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).2 hpD
  refine ⟨fun y => ?_⟩
  have h := y.property
  simp [hc, dot, hz] at h

private abbrev Root (p : ℕ) (a : Vec ℕ) :=
  Solutions (fun i => (a i : ZMod p)) (0 : ZMod p)

private abbrev LiftFiber (p : ℕ) (a : Vec ℕ) (x : Root p a) :=
  {y : Vec (ZMod p) // ((carryNumerator a x.val / p : ℕ) : ZMod p) +
      dot (derivative a x.val) y = 1}

private theorem count_lift_sigma (p : ℕ) [NeZero p] (a : Vec ℕ) :
    count (fun i => (a i : ZMod (p*p))) (p : ZMod (p*p)) =
      Nat.card (Σ x : Root p a, LiftFiber p a x) := by
  classical
  let U := {v : Vec (ZMod p) × Vec (ZMod p) // (∑ i, (a i : ZMod p)*(v.1 i)^4 = 0) ∧
      ((carryNumerator a v.1 / p : ℕ) : ZMod p) + dot (derivative a v.1) v.2 = 1}
  let e : U ≃ Solutions (fun i => (a i : ZMod (p*p))) (p : ZMod (p*p)) :=
    (liftEquiv p).subtypeEquiv (fun v => (lift_condition a v.1 v.2).symm)
  let f : U ≃ Σ x : Root p a, LiftFiber p a x :=
    { toFun := fun v => ⟨⟨v.val.1, v.property.1⟩, ⟨v.val.2, v.property.2⟩⟩
      invFun := fun v => ⟨(v.1.val,v.2.val), v.1.property,v.2.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact Nat.card_congr (e.symm.trans f)

/-- Exact lift count at a valuation-one target. Each nonsingular zero modulo
p has p³ lifts, and a singular zero has none for fourth-full coefficients. -/
theorem valuation_one_count {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (a : Vec ℕ) (ha : ∀ i, (4 : ℕ).Full (a i)) :
    count (fun i => (a i : ZMod (p*p))) (p : ZMod (p*p)) =
      p^3 * Nat.card {x : Root p a // ∃ i, derivative a x.val i ≠ 0} := by
  classical
  have hf (x : Root p a) : Nat.card (LiftFiber p a x) =
      if ∃ i, derivative a x.val i ≠ 0 then p^3 else 0 := by
    by_cases h : ∃ i, derivative a x.val i ≠ 0
    · obtain ⟨j,hj⟩ := h
      rw [if_pos ⟨j,hj⟩]
      let e : LiftFiber p a x ≃
          {y : Vec (ZMod p) // dot (derivative a x.val) y =
            1 - ((carryNumerator a x.val / p : ℕ) : ZMod p)} :=
        (Equiv.refl _).subtypeEquiv (fun y => by
          change ((carryNumerator a x.val / p : ℕ) : ZMod p) + dot (derivative a x.val) y = 1 ↔ _
          simp only [Equiv.refl_apply]
          rw [add_comm, eq_sub_iff_add_eq])
      rw [Nat.card_congr e, dot_fiber_card _ _ j hj, ZMod.card]
    · let : IsEmpty (LiftFiber p a x) := no_singular_lift hp2 a ha x.val h
      simp [h]
  let : Fintype (Root p a) := by
    change Fintype {x : Vec (ZMod p) // (∑ i, (a i : ZMod p)*(x i)^4)=0}
    infer_instance
  rw [count_lift_sigma, Nat.card_sigma]
  simp only [hf, Nat.card_eq_fintype_card, Fintype.card_subtype, ← Finset.sum_filter,
    Finset.sum_const, nsmul_eq_mul, Nat.cast_id, mul_comm]

/-- At good primes the only excluded zero is the zero vector. -/
theorem valuation_one_count_good {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (a : Vec ℕ) (ha : ∀ i, (4 : ℕ).Full (a i)) (hGood : ∀ i, ¬p ∣ a i) :
    count (fun i => (a i : ZMod (p*p))) (p : ZMod (p*p)) =
      p^3 * (count (fun i => (a i : ZMod p)) 0 - 1) := by
  classical
  rw [valuation_one_count hp2 a ha]
  let : Fintype (Root p a) := by
    change Fintype {x : Vec (ZMod p) // (∑ i, (a i : ZMod p)*(x i)^4)=0}
    infer_instance
  let z : Root p a := ⟨fun _ => 0, by simp⟩
  have he (x : Root p a) : (∃ i, derivative a x.val i ≠ 0) ↔ x ≠ z := by
    constructor
    · rintro ⟨i,hi⟩ h
      subst x
      exact hi (by simp [derivative, z])
    · intro hx
      by_contra! h
      apply hx
      apply Subtype.ext
      funext i
      have hh := h i
      unfold derivative at hh
      have h4 := four_nonzero_mod_prime hp2
      have hai : (a i : ZMod p) ≠ 0 := fun h => hGood i ((ZMod.natCast_eq_zero_iff _ _).mp h)
      have hz := (mul_eq_zero.mp hh).resolve_left (mul_ne_zero h4 hai)
      exact (pow_eq_zero_iff (by decide : (3 : ℕ) ≠ 0)).mp hz
  have hC : Nat.card {x : Root p a // ∃ i, derivative a x.val i ≠ 0} =
      Nat.card {x : Root p a // x ≠ z} := Nat.card_congr
      ((Equiv.refl _).subtypeEquiv (fun x => he x))
  rw [hC]
  congr 1
  change Nat.card {x : Root p a // x ≠ z} = Nat.card (Root p a) - 1
  simp only [Nat.card_eq_fintype_card]
  rw [Fintype.card_subtype_compl (fun x : Root p a => x = z)]
  let e : {x : Root p a // x = z} ≃ Unit :=
    { toFun := fun _ => ()
      invFun := fun _ => ⟨z, rfl⟩
      left_inv := fun x => Subtype.ext x.property.symm
      right_inv := fun _ => rfl }
  have hZ : Fintype.card {x : Root p a // x = z} = 1 := by
    simpa only [Fintype.card_unit] using Fintype.card_congr e
  rw [hZ]


/-- A nonzero coefficient gives a four-root bound after fixing the other coordinates. -/
theorem count_le_four_mul {F : Type} [Field F] [Fintype F] (a : Vec F) (u : F)
    (j : Fin 4) (ha : a j ≠ 0) :
    count a u ≤ 4 * Fintype.card F^3 := by
  classical
  let total (x : Other j → F) : F := ∑ i ∈ Finset.univ.erase j,
    a i * (if h : i ≠ j then x ⟨i,h⟩ else 0)^4
  let P (x : Other j → F) : Polynomial F := Polynomial.X^4 - Polynomial.C ((u-total x)/a j)
  have hdeg (x : Other j → F) : (P x).natDegree = 4 := by
    unfold P
    rw [Polynomial.natDegree_sub_C, Polynomial.natDegree_X_pow]
  have hne (x : Other j → F) : P x ≠ 0 := by
    intro h
    simpa [h] using hdeg x
  let R (x : Other j → F) := {r : F // r ∈ (P x).roots.toFinset}
  let rest (v : Solutions a u) (i : Other j) : F := v.val i.val
  have hroot (v : Solutions a u) : v.val j ∈ (P (rest v)).roots.toFinset := by
    rw [Multiset.mem_toFinset, Polynomial.mem_roots (hne _)]
    change Polynomial.eval (v.val j) (P (rest v)) = 0
    have hEq : a j * (v.val j)^4 = u - total (rest v) := by
      have hsum := v.property
      rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ j)] at hsum
      have ht : total (rest v) = ∑ i ∈ Finset.univ.erase j, a i * (v.val i)^4 := by
        apply Finset.sum_congr rfl
        intro i hi
        simp [rest, (Finset.mem_erase.mp hi).1]
      rw [ht]
      linear_combination hsum
    simp only [P, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
    exact sub_eq_zero.mpr ((eq_div_iff ha).mpr (by simpa [mul_comm] using hEq))
  let : Finite (Solutions a u) := by
    unfold Solutions
    infer_instance
  let f (v : Solutions a u) : Σ x : Other j → F, R x :=
    ⟨rest v, ⟨v.val j, hroot v⟩⟩
  have hInj : Function.Injective f := by
    intro x y h
    have hRest : rest x = rest y := congrArg Sigma.fst h
    have hAt : x.val j = y.val j := congrArg (fun v => v.2.val) h
    apply Subtype.ext
    funext i
    by_cases hi : i ≠ j
    · exact congrFun hRest ⟨i,hi⟩
    · simpa [(not_ne_iff.mp hi)] using hAt
  have hR (x : Other j → F) : Nat.card (R x) ≤ 4 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    exact (Multiset.toFinset_card_le _).trans (by simpa [hdeg x] using (P x).card_roots')
  calc
    count a u = Nat.card (Solutions a u) := rfl
    _ ≤ Nat.card (Σ x : Other j → F, R x) := Nat.card_le_card_of_injective f hInj
    _ ≤ ∑ _ : Other j → F, 4 := by
      rw [Nat.card_sigma]
      exact Finset.sum_le_sum fun x _ => hR x
    _ = 4 * Fintype.card F^3 := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
      simp only [Fintype.card_fun, ← Nat.card_eq_fintype_card (α := Other j),
        other_card]
      exact Nat.mul_comm _ _

/-- The normalized valuation-one local factor is at most four at every odd prime,
including primes dividing some or all coefficients. -/
theorem valuation_one_count_le {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (a : Vec ℕ) (ha : ∀ i, (4 : ℕ).Full (a i)) :
    count (fun i => (a i : ZMod (p*p))) (p : ZMod (p*p)) ≤ 4*p^6 := by
  classical
  let : Finite (Root p a) := by
    change Finite {x : Vec (ZMod p) // (∑ i, (a i : ZMod p)*(x i)^4)=0}
    infer_instance
  rw [valuation_one_count hp2 a ha]
  by_cases h : ∃ j, (a j : ZMod p) ≠ 0
  · obtain ⟨j,hj⟩ := h
    have hEmb := Nat.card_le_card_of_injective
      (fun x : {x : Root p a // ∃ i, derivative a x.val i ≠ 0} => x.val) Subtype.val_injective
    have hCard := count_le_four_mul (fun i => (a i : ZMod p)) 0 j hj
    rw [ZMod.card] at hCard
    have hm := Nat.mul_le_mul_left (p^3) (hEmb.trans hCard)
    exact hm.trans_eq (by ring)
  · push Not at h
    let : IsEmpty {x : Root p a // ∃ i, derivative a x.val i ≠ 0} :=
      ⟨fun x => by obtain ⟨i,hi⟩ := x.property; exact hi (by simp [derivative, h i])⟩
    simp
end Erdos940Quartic


namespace Erdos940Quartic

open Finset

private theorem gaussSum_norm {F : Type} [Field F] [Fintype F]
    {χ : MulChar F ℂ} (hχ : χ ≠ 1) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) :
    ‖gaussSum χ ψ‖ = Real.sqrt (Fintype.card F) := by
  have hStar (x : F) : (starRingEnd ℂ) (ψ x) = ψ⁻¹ x := by
    rw [AddChar.inv_apply, AddChar.map_neg_eq_inv]
    exact (Complex.inv_eq_conj (AddChar.norm_apply ψ x)).symm
  have hConj : (starRingEnd ℂ) (gaussSum χ ψ) = gaussSum χ⁻¹ ψ⁻¹ := by
    simp only [gaussSum, map_sum, map_mul, hStar, ← Complex.star_def, MulChar.star_apply']
  have hgs := gaussSum_mul_gaussSum_eq_card hχ hψ
  rw [← hConj, Complex.mul_conj] at hgs
  have hR := congrArg Complex.re hgs
  simp only [Complex.ofReal_re, Complex.natCast_re, Complex.normSq_eq_norm_sq] at hR
  rw [← hR, Real.sqrt_sq (norm_nonneg _)]

private theorem orderOf_value_generator {F : Type} [Field F] [Fintype F]
    (χ : MulChar F ℂ) (g : Fˣ) (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    orderOf (χ (g : F)) = orderOf χ := by
  apply Nat.dvd_antisymm
  · apply orderOf_dvd_of_pow_eq_one
    rw [← χ.pow_apply_coe, pow_orderOf_eq_one, MulChar.one_apply_coe]
  · apply orderOf_dvd_of_pow_eq_one
    apply (MulChar.eq_iff hg _ _).2
    rw [χ.pow_apply_coe, pow_orderOf_eq_one, MulChar.one_apply_coe]

private theorem fourth_exists_iff {F : Type} [Field F] [Fintype F]
    {χ : MulChar F ℂ} (hχ : orderOf χ = 4) {y : F} (hy : y ≠ 0) :
    (∃ x : F, x^4 = y) ↔ χ y = 1 := by
  classical
  have hPow : χ ^ 4 = 1 := hχ ▸ pow_orderOf_eq_one χ
  constructor
  · rintro ⟨x,rfl⟩
    have hx : x ≠ 0 := by
      intro h
      simp [h] at hy
    rw [map_pow, ← χ.pow_apply' (by decide : (4 : ℕ) ≠ 0), hPow, MulChar.one_apply hx.isUnit]
  · intro he
    obtain ⟨g,hg⟩ := IsCyclic.exists_generator (α := Fˣ)
    obtain ⟨n,hn⟩ := mem_powers_iff_mem_zpowers.mpr (hg (Units.mk0 y hy))
    have hy' : (g : F)^n = y := by
      simpa using congrArg (fun u : Fˣ => (u : F)) hn
    have hD : 4 ∣ n := by
      have he' : χ (g : F)^n = 1 := by rwa [← map_pow, hy']
      simpa only [orderOf_value_generator χ g hg, hχ] using orderOf_dvd_of_pow_eq_one he'
    obtain ⟨m,hm⟩ := hD
    exact ⟨(g : F)^m, by rw [← pow_mul, mul_comm m 4, ← hm, hy']⟩

private theorem fourth_fiber_good {F : Type} [Field F] [Fintype F]
    (hD : 4 ∣ Fintype.card F - 1) {y : F} (hy : y ≠ 0) (h : ∃ x : F, x^4 = y) :
    Nat.card {x : F // x^4 = y} = 4 := by
  classical
  let Y : Fˣ := Units.mk0 y hy
  let f : Fˣ →* Fˣ := powMonoidHom 4
  let e : {x : F // x^4 = y} ≃ {u : Fˣ // f u = Y} :=
    { toFun := fun x => ⟨Units.mk0 x.val (fun hz => hy (by simpa [hz] using x.property.symm)),
        Units.ext (by simpa [f,Y] using x.property)⟩
      invFun := fun u => ⟨u.val, by simpa [f,Y] using congrArg (fun w : Fˣ => (w : F)) u.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => Subtype.ext (Units.ext rfl) }
  have hY : Y ∈ Set.range f := by
    obtain ⟨x,hx⟩ := h
    refine ⟨Units.mk0 x (fun h => hy (by simpa [h] using hx.symm)), Units.ext ?_⟩
    simpa [f,Y] using hx
  have hOne : (1 : Fˣ) ∈ Set.range f := ⟨1,map_one f⟩
  have hc := MonoidHom.card_fiber_eq_of_mem_range f hY hOne
  have hK := IsCyclic.card_powMonoidHom_ker Fˣ 4
  rw [Nat.card_eq_fintype_card (α := Fˣ), Fintype.card_units, Nat.gcd_eq_right hD] at hK
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype, hc]
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  exact (Nat.card_congr ((Equiv.refl _).subtypeEquiv
    (fun _ => MonoidHom.mem_ker.symm))).trans hK

private theorem fourth_fiber_characters {F : Type} [Field F] [Fintype F]
    (χ : MulChar F ℂ) (hχ : orderOf χ = 4) (y : F) :
    (Nat.card {x : F // x^4 = y} : ℂ) = 1 + χ y + (χ^2) y + (χ^3) y := by
  classical
  rcases eq_or_ne y 0 with rfl | hy
  · let e : {x : F // x^4 = 0} ≃ Unit :=
      { toFun := fun _ => ()
        invFun := fun _ => ⟨0, by simp⟩
        left_inv := fun x => Subtype.ext ((pow_eq_zero_iff (by decide : (4 : ℕ) ≠ 0)).mp x.property).symm
        right_inv := fun _ => rfl }
    simp only [Nat.card_congr e, Nat.card_unique, Nat.cast_one, MulChar.map_zero, add_zero]
  have h4 : (χ y)^4 = 1 := by
    rw [← χ.pow_apply' (by decide : (4 : ℕ) ≠ 0),
      ← hχ, pow_orderOf_eq_one, MulChar.one_apply hy.isUnit]
  by_cases hs : χ y = 1
  · have hD : 4 ∣ Fintype.card F - 1 := hχ ▸ MulChar.orderOf_dvd_card_sub_one F χ
    rw [fourth_fiber_good hD hy ((fourth_exists_iff hχ hy).mpr hs),
      χ.pow_apply' (by decide : (2 : ℕ) ≠ 0), χ.pow_apply' (by decide : (3 : ℕ) ≠ 0), hs]
    norm_num
  · let : IsEmpty {x : F // x^4 = y} :=
      ⟨fun x => hs ((fourth_exists_iff hχ hy).mp ⟨x.val,x.property⟩)⟩
    simp only [Nat.card_eq_fintype_card, Fintype.card_of_isEmpty, Nat.cast_zero,
      χ.pow_apply' (by decide : (2 : ℕ) ≠ 0), χ.pow_apply' (by decide : (3 : ℕ) ≠ 0)]
    apply mul_left_cancel₀ (sub_ne_zero.mpr hs)
    linear_combination -h4

private def exponent (j : Fin 3) : ℕ := j.val + 1

private theorem quartic_exponential {F : Type} [Field F] [Fintype F]
    {χ : MulChar F ℂ} (hχ : orderOf χ = 4) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {s : F} (hs : s ≠ 0) :
    exponentialSum ψ s = ∑ j : Fin 3, ((χ^exponent j)⁻¹) s * gaussSum (χ^exponent j) ψ := by
  classical
  have he : exponentialSum ψ s =
      ∑ y : F, (1 + χ y + (χ^2) y + (χ^3) y) * ψ (s*y) := by
    unfold exponentialSum
    rw [← Finset.sum_fiberwise' univ (fun v : F => v^4) (fun y => ψ (s*y))]
    apply Finset.sum_congr rfl
    intro y _
    rw [Finset.sum_const, nsmul_eq_mul, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card,
      fourth_fiber_characters χ hχ y]
  have hz : (∑ y : F, ψ (s*y)) = 0 := by
    simpa only [mul_comm s, if_neg hs, Nat.cast_zero] using AddChar.sum_mulShift s hψ
  have hGauss (k : ℕ) : (∑ x : F, (χ^k) x * ψ (s*x)) =
      (χ^k)⁻¹ s * gaussSum (χ^k) ψ := by
    simpa only [gaussSum, AddChar.mulShift_apply, Units.val_mk0, mul_comm s] using
      gaussSum_mulShift_eq (χ^k) ψ (Units.mk0 s hs)
  have hG1 := hGauss 1
  rw [pow_one] at hG1
  rw [he]
  simp only [add_mul, Finset.sum_add_distrib, one_mul, hz, zero_add, hGauss, hG1,
    Fin.sum_univ_three, exponent]
  rw [show (0 : Fin 3).val+1=1 by decide, show (1 : Fin 3).val+1=2 by decide,
    show (2 : Fin 3).val+1=3 by decide, pow_one]

end Erdos940Quartic


namespace Erdos940Quartic

open Finset

private abbrev Pattern := Fin 4 → Fin 3

private def totalExponent (k : Pattern) : ℕ := ∑ i, exponent (k i)

private def tracePatterns : Finset Pattern := Finset.univ.filter (fun k => 4 ∣ totalExponent k)

private theorem tracePatterns_card : tracePatterns.card = 21 := by decide

private noncomputable def traceTerm {F : Type} [Field F] [Fintype F]
    (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (a : Fin 4 → F) (k : Pattern) : ℂ :=
  ∏ i, ((χ^exponent (k i))⁻¹) (a i) * gaussSum (χ^exponent (k i)) ψ

private theorem character_pattern_product_nonzero {F : Type} [Field F]
    (χ : MulChar F ℂ) (k : Pattern) {t : F} (ht : t ≠ 0) :
    (∏ i, ((χ^exponent (k i))⁻¹) t) = (χ^(totalExponent k))⁻¹ t := by
  classical
  unfold totalExponent
  suffices ∀ S : Finset (Fin 4),
    (∏ i ∈ S, ((χ^exponent (k i))⁻¹) t) = (χ^(∑ i ∈ S, exponent (k i)))⁻¹ t from this _
  intro S
  induction S using Finset.induction_on with
  | empty => simp [MulChar.one_apply ht.isUnit]
  | insert i S hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, pow_add, mul_inv_rev, MulChar.mul_apply]
    ring

private theorem character_sum_off_zero {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (χ : MulChar F ℂ) (hχ : orderOf χ = 4) (n : ℕ) :
    (∑ t ∈ (Finset.univ : Finset F).erase 0, (χ^n)⁻¹ t) =
      if 4 ∣ n then (Fintype.card F : ℂ)-1 else 0 := by
  classical
  have he : ((χ^n)⁻¹ : MulChar F ℂ) = 1 ↔ 4 ∣ n := by
    rw [inv_eq_one, ← orderOf_dvd_iff_pow_eq_one, hχ]
  by_cases hn : 4 ∣ n
  · rw [if_pos hn, he.mpr hn]
    calc
      _ = ∑ _ ∈ (Finset.univ : Finset F).erase 0, (1 : ℂ) := by
        apply Finset.sum_congr rfl
        intro t ht
        exact MulChar.one_apply (Finset.mem_erase.mp ht).1.isUnit
      _ = _ := by
        rw [sum_const, nsmul_eq_mul, mul_one, card_erase_of_mem (mem_univ _), card_univ,
          Nat.cast_sub Fintype.card_pos, Nat.cast_one]
  · rw [if_neg hn]
    have h := MulChar.sum_eq_zero_of_ne_one (fun hr => hn (he.mp hr))
    rw [← Finset.sum_erase_add _ _ (mem_univ (0 : F)), MulChar.map_zero, add_zero] at h
    exact h

private theorem quartic_trace_identity {F : Type} [Field F] [Fintype F]
    {χ : MulChar F ℂ} (hχ : orderOf χ = 4) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (a : Fin 4 → F) (ha : ∀ i, a i ≠ 0) :
    (Fintype.card F : ℂ) * (count a 0 : ℂ) = (Fintype.card F : ℂ)^4 +
      ((Fintype.card F : ℂ)-1) * ∑ k ∈ tracePatterns, traceTerm χ ψ a k := by
  classical
  have ht (t : F) (ht : t ≠ 0) :
      (∏ i, exponentialSum ψ (t*a i)) =
        ∑ k : Pattern, (χ^totalExponent k)⁻¹ t * traceTerm χ ψ a k := by
    calc
      _ = ∏ i : Fin 4, ∑ j : Fin 3,
          ((χ^exponent j)⁻¹) (t*a i) * gaussSum (χ^exponent j) ψ :=
        Finset.prod_congr rfl (fun i _ => quartic_exponential hχ hψ (mul_ne_zero ht (ha i)))
      _ = _ := by
        rw [Fintype.prod_sum]
        apply Finset.sum_congr rfl
        intro k _
        simp_rw [map_mul, mul_assoc, Finset.prod_mul_distrib, ← mul_assoc,
          character_pattern_product_nonzero χ k ht, traceTerm]
        rw [Finset.prod_mul_distrib, mul_assoc]
  have hz : (∏ i : Fin 4, exponentialSum ψ ((0 : F)*a i)) = (Fintype.card F : ℂ)^4 := by
    simp [exponentialSum]
  have hS := count_zero_fourier hψ a
  rw [← Finset.sum_erase_add _ _ (mem_univ (0 : F)), hz, add_comm] at hS
  rw [hS]
  congr 1
  calc
    _ = ∑ k : Pattern, ∑ t ∈ (Finset.univ : Finset F).erase 0,
        (χ^totalExponent k)⁻¹ t * traceTerm χ ψ a k := by
      rw [← Finset.sum_comm]
      exact Finset.sum_congr rfl (fun t ht' => ht t (Finset.mem_erase.mp ht').1)
    _ = _ := by
      simp only [← Finset.sum_mul, character_sum_off_zero χ hχ, ite_mul, zero_mul,
        tracePatterns, Finset.mul_sum, Finset.sum_filter, mul_ite, mul_zero]

private theorem mulChar_norm_one {F : Type} [Field F] [Fintype F]
    (χ : MulChar F ℂ) {x : F} (hx : x ≠ 0) : ‖χ x‖ = 1 := by
  classical
  have hc : 0 < Fintype.card Fˣ := Fintype.card_pos
  have h : x^Fintype.card Fˣ = 1 := by
    simpa only [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one] using
      congrArg (fun u : Fˣ => (u : F)) (pow_card_eq_one (x := Units.mk0 x hx))
  exact (isOfFinOrder_iff_pow_eq_one.mpr ⟨_,hc,by rw [← map_pow,h,map_one]⟩ :
    IsOfFinOrder (χ x)).norm_eq_one

private theorem trace_bound {F : Type} [Field F] [Fintype F]
    {χ : MulChar F ℂ} (hχ : orderOf χ = 4) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (a : Fin 4 → F) (ha : ∀ i, a i ≠ 0) :
    ‖∑ k ∈ tracePatterns, traceTerm χ ψ a k‖ ≤ 21 * (Fintype.card F : ℝ)^2 := by
  have hG (j : Fin 3) : χ^exponent j ≠ 1 := by
    intro h
    have he := orderOf_dvd_of_pow_eq_one h
    rw [hχ] at he
    have hJ := j.isLt
    unfold exponent at he
    omega
  have hLocal (k : Pattern) : ‖traceTerm χ ψ a k‖ = (Fintype.card F : ℝ)^2 := by
    unfold traceTerm
    rw [norm_prod]
    simp_rw [norm_mul, mulChar_norm_one _ (ha _), one_mul, gaussSum_norm (hG _) hψ]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      show (4 : ℕ) = 2*2 by decide, pow_mul, Real.sq_sqrt (by positivity)]
  calc
    _ ≤ ∑ k ∈ tracePatterns, ‖traceTerm χ ψ a k‖ := norm_sum_le _ _
    _ = _ := by simp [hLocal, tracePatterns_card, nsmul_eq_mul]

/-- At a split prime, only the 21 exponent patterns of total exponent
divisible by four survive in the Fourier expansion. -/
theorem split_zero_count_bound {p : ℕ} [Fact p.Prime] (hp : p % 4 = 1)
    (a : Fin 4 → ZMod p) (ha : ∀ i, a i ≠ 0) :
    ‖(count a 0 : ℂ)-(p : ℂ)^3‖ ≤ 21 * (p : ℝ)*((p : ℝ)-1) := by
  obtain ⟨ζ,hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot ℂ 4
  have hD : 4 ∣ Fintype.card (ZMod p) - 1 := by rw [ZMod.card]; omega
  obtain ⟨χ,hχ⟩ := MulChar.exists_mulChar_orderOf (ZMod p) hD hζ
  let ψ : AddChar (ZMod p) ℂ := ZMod.stdAddChar
  have hψ : ψ.IsPrimitive := ZMod.isPrimitive_stdAddChar p
  have hId := quartic_trace_identity hχ hψ a ha
  have hBound := trace_bound hχ hψ a ha
  rw [ZMod.card] at hId hBound
  have hpPos : 0 < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hSub : (p : ℂ)*((count a 0 : ℂ)-(p : ℂ)^3) =
      ((p : ℂ)-1)*∑ k ∈ tracePatterns, traceTerm χ ψ a k := by
    rw [mul_sub, hId]
    ring
  have hAbs : ‖(p : ℂ)-1‖ = (p : ℝ)-1 := by
    rw [show (p : ℂ)-1 = ((p : ℝ)-1 : ℝ) by push_cast; rfl, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hp1)]
  have hMul := congrArg norm hSub
  simp only [norm_mul, Complex.norm_natCast, hAbs] at hMul
  apply (mul_le_mul_iff_right₀ hpPos).mp
  rw [hMul]
  calc
    _ ≤ ((p : ℝ)-1) * (21 * (p : ℝ)^2) :=
      mul_le_mul_of_nonneg_left hBound (sub_nonneg.mpr hp1)
    _ = _ := by ring

end Erdos940Quartic


namespace Erdos940QuarticPrimes

open Filter Set ArithmeticFunction vonMangoldt
open scoped Topology

private theorem scaled_log_over_rpow_le {n : ℕ} (hn : 0 < n) {x : ℝ} :
    ((x-1) * Real.log (n : ℝ)) / (n : ℝ)^x ≤ 1 / (n : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have he : (n : ℝ)^x = n * Real.exp ((x-1) * Real.log (n : ℝ)) := by
    conv_lhs => rw [show x = 1+(x-1) by ring, Real.rpow_add hnR, Real.rpow_one,
      Real.rpow_def_of_pos hnR, mul_comm (Real.log _)]
  rw [he]
  apply (div_le_div_iff₀ (mul_pos hnR (Real.exp_pos _)) hnR).mpr
  set t := (x-1) * Real.log (n : ℝ)
  have ht : t ≤ Real.exp t := by linarith [Real.add_one_le_exp t]
  calc
    _ = (n : ℝ) * t := by ring
    _ ≤ (n : ℝ) * Real.exp t := mul_le_mul_of_nonneg_left ht hnR.le
    _ = _ := by simp

/-- Reciprocal primes diverge in every invertible residue class. The
simple pole of the von Mangoldt series supplies the lower bound. -/
theorem not_summable_primes_in_class {q : ℕ} [NeZero q] (a : ZMod q) (ha : IsUnit a) :
    ¬ Summable (fun p : {p : ℕ // p.Prime ∧ (p : ZMod q) = a} => (1 : ℝ) / p.val) := by
  classical
  intro hS
  let P : Set ℕ := {p | p.Prime ∧ (p : ZMod q) = a}
  let W (n : ℕ) : ℝ := P.indicator (fun n => (1 : ℝ)/n) n +
    (if n.Prime then 0 else residueClass a n)/n
  have hw1 : Summable (P.indicator (fun n => (1 : ℝ)/n)) :=
    (summable_subtype_iff_indicator (s := P)).mp hS
  have hW : Summable W := hw1.add (summable_residueClass_non_primes_div a)
  let F (x : ℝ) (n : ℕ) : ℝ := (x-1) * (residueClass a n / (n : ℝ)^x)
  have hOne : Tendsto (fun x : ℝ => x-1) (𝓝[>] (1 : ℝ)) (𝓝 0) := by
    have ht : Tendsto (fun x : ℝ => x) (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℝ)) :=
      continuous_id.continuousWithinAt
    simpa only [sub_self] using ht.sub_const (1 : ℝ)
  have hPoint (n : ℕ) : Tendsto (fun x : ℝ => F x n) (𝓝[>] (1 : ℝ)) (𝓝 0) := by
    by_cases hn : n = 0
    · subst n
      simp [F, residueClass]
    have hnR : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hDen : Continuous (fun x : ℝ => (n : ℝ)^x) := Real.continuous_const_rpow (by positivity)
    have hct : Tendsto (fun x : ℝ => residueClass a n / (n : ℝ)^x) (𝓝[>] (1 : ℝ))
        (𝓝 (residueClass a n / (n : ℝ)^ (1 : ℝ))) :=
      tendsto_const_nhds.div hDen.continuousAt.continuousWithinAt (Real.rpow_pos_of_pos hnR _).ne'
    simpa only [F, zero_mul] using hOne.mul hct
  have hNear : ∀ᶠ x : ℝ in 𝓝[>] (1 : ℝ), x ∈ Ioc (1 : ℝ) 2 :=
    Ioc_mem_nhdsGT (by norm_num)
  have hMajor : ∀ᶠ x : ℝ in 𝓝[>] (1 : ℝ), ∀ n : ℕ, ‖F x n‖ ≤ W n := by
    filter_upwards [hNear] with x hx n
    have hnon : 0 ≤ F x n := mul_nonneg (sub_nonneg.mpr hx.1.le)
      (div_nonneg (residueClass_nonneg a n) (by positivity))
    rw [Real.norm_eq_abs, abs_of_nonneg hnon]
    by_cases hn : n.Prime
    · by_cases hres : (n : ZMod q) = a
      · have hin : n ∈ P := ⟨hn,hres⟩
        have hr : residueClass a n = Real.log n := by
          simp [residueClass, hres, vonMangoldt_apply_prime hn]
        simp only [W, indicator_of_mem hin, if_pos hn, zero_div, add_zero, F, hr, ← mul_div_assoc]
        exact scaled_log_over_rpow_le hn.pos
      · have hnot : n ∉ P := fun h => hres h.2
        have hr : residueClass a n = 0 := by
          simp [residueClass, hres]
        simp [W, F, indicator_of_notMem hnot, hn, hr]
    · have hnot : n ∉ P := fun h => hn h.1
      simp only [W, indicator_of_notMem hnot, if_neg hn, zero_add]
      by_cases h0 : n = 0
      · subst n
        simp [residueClass, F]
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.pos_of_ne_zero h0
      have hnR : (0 : ℝ) < n := by linarith
      have hPow : (n : ℝ) ≤ (n : ℝ)^x := by
        nth_rewrite 1 [← Real.rpow_one (n : ℝ)]
        exact Real.rpow_le_rpow_of_exponent_le hn1 hx.1.le
      calc
        _ ≤ 1 * (residueClass a n / (n : ℝ)^x) := mul_le_mul_of_nonneg_right
          (by linarith [hx.2]) (div_nonneg (residueClass_nonneg a n) (by positivity))
        _ ≤ _ := by
          rw [one_mul]
          exact div_le_div_of_nonneg_left (residueClass_nonneg a n) hnR hPow
  have hSum : Tendsto (fun x : ℝ => ∑' n, F x n) (𝓝[>] (1 : ℝ)) (𝓝 0) := by
    simpa only [tsum_zero] using tendsto_tsum_of_dominated_convergence hW hPoint hMajor
  obtain ⟨C,hC⟩ := LSeries_residueClass_lower_bound ha
  have hcompare : ∀ᶠ x : ℝ in 𝓝[>] (1 : ℝ),
      (q.totient : ℝ)⁻¹ - C*(x-1) ≤ ∑' n, F x n := by
    filter_upwards [hNear] with x hx
    have hx0 : 0 < x-1 := sub_pos.mpr hx.1
    have hm := mul_le_mul_of_nonneg_left (hC hx) hx0.le
    rw [mul_sub, mul_div_cancel₀ _ hx0.ne', ← tsum_mul_left] at hm
    simpa only [F, mul_comm C] using hm
  have hlim : Tendsto (fun x : ℝ => (q.totient : ℝ)⁻¹ - C*(x-1))
      (𝓝[>] (1 : ℝ)) (𝓝 ((q.totient : ℝ)⁻¹)) := by
    simpa only [mul_zero, sub_zero] using tendsto_const_nhds.sub (hOne.const_mul C)
  have hzero := le_of_tendsto_of_tendsto hlim hSum hcompare
  exact (not_le_of_gt (inv_pos.mpr (by exact_mod_cast q.totient.pos_of_neZero))) hzero

end Erdos940QuarticPrimes



namespace Erdos940QuarticPrimes

open Finset ZMod

/-- A nonnegative solution of any finite, pairwise coprime CRT system. -/
theorem assemble_congruences {ι : Type} (S : Finset ι) (m r : ι → ℕ)
    (hm : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → (m i).Coprime (m j)) :
    ∃ a : ℕ, ∀ i ∈ S, a ≡ r i [MOD m i] := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0, fun i hi => (Finset.notMem_empty i hi).elim⟩
  | insert i S hi ih =>
    have hSub : ∀ j ∈ S, ∀ k ∈ S, j ≠ k → (m j).Coprime (m k) :=
      fun j hj k hk hne => hm j (mem_insert_of_mem hj) k (mem_insert_of_mem hk) hne
    obtain ⟨a,ha⟩ := ih hSub
    have hcop : (m i).Coprime (∏ j ∈ S, m j) :=
      Nat.Coprime.prod_right fun j hj => hm i (mem_insert_self _ _) j (mem_insert_of_mem hj)
        (fun h => hi (h ▸ hj))
    let A := Nat.chineseRemainder hcop (r i) a
    refine ⟨A.val, fun j hj => ?_⟩
    rcases mem_insert.mp hj with rfl | hj
    · exact A.property.1
    · exact (A.property.2.of_dvd (Finset.dvd_prod_of_mem m hj)).trans (ha j hj)

private def signInt (b : ZMod 2) : ℤ := if b = 0 then 1 else -1

private theorem exists_local_symbol {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {s : ℤ}
    (hs : s = 1 ∨ s = -1) :
    letI : Fact p.Prime := ⟨hp⟩
    ∃ a : ℕ, ¬p ∣ a ∧ quadraticChar (ZMod p) (a : ZMod p) = s := by
  let : Fact p.Prime := ⟨hp⟩
  rcases hs with rfl | rfl
  · exact ⟨1, hp.not_dvd_one, by simp⟩
  · obtain ⟨a,ha⟩ := quadraticChar_exists_neg_one (F := ZMod p) (by rwa [ringChar_zmod_n])
    have h0 : a ≠ 0 := fun h => by simp [h] at ha
    refine ⟨a.val, ?_, by simpa only [ZMod.natCast_zmod_val] using ha⟩
    intro hd
    apply h0
    rw [← ZMod.natCast_zmod_val a]
    exact (ZMod.natCast_eq_zero_iff _ _).2 hd

private def eightResidue (P : Finset ℕ) (s : P → ZMod 2) : ℕ :=
  if h : 2 ∈ P then (if s ⟨2,h⟩ = 0 then 7 else 3) else 7

private theorem eightResidue_cases (P : Finset ℕ) (s : P → ZMod 2) :
    eightResidue P s = 7 ∨ eightResidue P s = 3 := by
  unfold eightResidue
  split
  · split <;> simp
  · simp

/-- Every prescribed system of quadratic symbols on finitely many rational
primes occurs in an invertible residue class of primes p = 3 mod 4. -/
theorem exists_class_for_symbols (P : Finset ℕ) (hP : ∀ l ∈ P, l.Prime) (s : P → ZMod 2) :
    ∃ (M : ℕ) (u : ZMod M), 0 < M ∧ IsUnit u ∧
      ∀ (p : ℕ) (hp : p.Prime), (p : ZMod M) = u →
        p % 4 = 3 ∧ ∀ l : P, @legendreSym p ⟨hp⟩ (l.val : ℤ) = signInt (s l) := by
  classical
  let Q := (Finset.univ : Finset P).filter (fun p => p.val ≠ 2)
  let m : P → ℕ := Subtype.val
  let sym (l : P) := if l.val % 4 = 1 then signInt (s l) else -signInt (s l)
  have hs (l : P) : sym l = 1 ∨ sym l = -1 := by
    unfold sym signInt
    split <;> split <;> norm_num
  have choose_r (l : P) : ∃ r : ℕ, l ∈ Q →
      (letI : Fact l.val.Prime := ⟨hP l.val l.property⟩
       ¬ l.val ∣ r ∧ quadraticChar (ZMod l.val) (r : ZMod l.val) = sym l) := by
    by_cases hq : l ∈ Q
    · have hn : l.val ≠ 2 := (Finset.mem_filter.mp hq).2
      obtain ⟨r,hr⟩ := exists_local_symbol (hP l.val l.property) hn (hs l)
      exact ⟨r, fun _ => hr⟩
    · exact ⟨1, fun h => (hq h).elim⟩
  choose r hr using choose_r
  obtain ⟨v,hv⟩ := assemble_congruences Q m r (by
    intro i _ j _ hne
    have hi := hP i.val i.property
    have hj := hP j.val j.property
    exact hi.coprime_iff_not_dvd.mpr
      (fun hd => hne (Subtype.ext ((Nat.prime_dvd_prime_iff_eq hi hj).mp hd))))
  let L := ∏ l ∈ Q, m l
  have hL : 0 < L := Finset.prod_pos fun l _ => (hP l.val l.property).pos
  have h8 : (8 : ℕ).Coprime L := by
    apply Nat.Coprime.prod_right
    intro l hl
    have hprime := hP l.val l.property
    have hn := (Finset.mem_filter.mp hl).2
    rw [show (8 : ℕ) = 2^3 by decide]
    apply Nat.Coprime.pow_left
    exact (Nat.prime_two.coprime_iff_not_dvd.mpr
      (fun h => hn (((Nat.prime_dvd_prime_iff_eq Nat.prime_two hprime).mp h).symm)))
  let r8 := eightResidue P s
  let A := Nat.chineseRemainder h8 r8 v
  let M := 8*L
  have hM : 0 < M := Nat.mul_pos (by decide) hL
  have hmod8 (p : ℕ) (hp : p ≡ A.val [MOD M]) : p % 8 = r8 := by
    have hsmall := (hp.of_dvd (dvd_mul_right 8 L)).trans A.property.1
    have hlt : r8 < 8 := (eightResidue_cases P s).elim (fun h => by change r8 = _ at h; omega) (fun h => by change r8 = _ at h; omega)
    exact (show p % 8 = r8 % 8 from hsmall).trans (Nat.mod_eq_of_lt hlt)
  have hmodl (p : ℕ) (hp : p ≡ A.val [MOD M]) (l : P) (hl : l ∈ Q) :
      (p : ZMod l.val) = (r l : ZMod l.val) := by
    have hD : l.val ∣ L := Finset.dvd_prod_of_mem m hl
    have h₁ : p ≡ A.val [MOD l.val] := hp.of_dvd (hD.trans (dvd_mul_left L 8))
    have h₂ : A.val ≡ v [MOD l.val] := A.property.2.of_dvd hD
    exact (ZMod.natCast_eq_natCast_iff p (r l) l.val).mpr (h₁.trans (h₂.trans (hv l hl)))
  have hUnit : IsUnit (A.val : ZMod M) := by
    apply (ZMod.isUnit_iff_coprime _ _).mpr
    have ha8 := hmod8 A.val Nat.ModEq.rfl
    have hOdd : ¬ 2 ∣ A.val := by
      rcases eightResidue_cases P s with h | h <;> change r8 = _ at h <;> omega
    have hc2 : A.val.Coprime 2 := (Nat.prime_two.coprime_iff_not_dvd.mpr hOdd).symm
    have hct : A.val.Coprime L := Nat.Coprime.prod_right fun l hl => by
      have hn : ¬ l.val ∣ A.val := by
        intro hD
        have hz : (A.val : ZMod l.val) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hD
        rw [hmodl A.val Nat.ModEq.rfl l hl] at hz
        exact (hr l hl).1 ((ZMod.natCast_eq_zero_iff _ _).1 hz)
      exact ((hP l.val l.property).coprime_iff_not_dvd.mpr hn).symm
    exact (show A.val.Coprime 8 from by
      exact hc2.pow_right 3).mul_right hct
  refine ⟨M, (A.val : ZMod M), hM, hUnit, ?_⟩
  intro p hp he
  let : Fact p.Prime := ⟨hp⟩
  have hmod := (ZMod.natCast_eq_natCast_iff _ _ _).mp he
  have hp8 := hmod8 p hmod
  have h3 : p % 4 = 3 := by
    rcases eightResidue_cases P s with h | h <;> change r8 = _ at h <;> omega
  have hp2 : p ≠ 2 := by omega
  refine ⟨h3, fun l => ?_⟩
  by_cases hl2 : l.val = 2
  · have hmem : 2 ∈ P := hl2 ▸ l.property
    have hl : l = ⟨2,hmem⟩ := Subtype.ext hl2
    subst l
    change legendreSym p 2 = signInt (s ⟨2,hmem⟩)
    rw [legendreSym.at_two hp2, ZMod.χ₈_nat_eq_if_mod_eight, hp8]
    have hodd : p%2 ≠ 0 := by omega
    rw [if_neg hodd]
    by_cases he : s ⟨2,hmem⟩ = 0
    · simp [r8, eightResidue, hmem, signInt, he]
    · simp [r8, eightResidue, hmem, signInt, he]
  · have hl : l ∈ Q := mem_filter.mpr ⟨mem_univ _, hl2⟩
    let : Fact l.val.Prime := ⟨hP l.val l.property⟩
    have hLQ : legendreSym l.val (p : ℤ) = sym l := by
      change quadraticChar (ZMod l.val) ((p : ℤ) : ZMod l.val) = _
      rw [Int.cast_natCast, hmodl p hmod l hl]
      exact (hr l hl).2
    by_cases hl1 : l.val%4 = 1
    · rw [legendreSym.quadratic_reciprocity_one_mod_four hl1 hp2, hLQ]
      exact if_pos hl1
    · have hlodd := (Nat.Prime.mod_two_eq_one_iff_ne_two Fact.out).mpr hl2
      have hl3 : l.val%4=3 := by omega
      rw [legendreSym.quadratic_reciprocity_three_mod_four hl3 h3, hLQ]
      simp [sym, hl1]

/-- Primes realizing any such finite list of quadratic symbols have divergent
reciprocal sum. -/
theorem not_summable_symbol_primes (P : Finset ℕ) (hP : ∀ l ∈ P, l.Prime) (s : P → ZMod 2) :
    ¬ Summable (fun p : {p : ℕ // ∃ hp : p.Prime, p%4=3 ∧
      ∀ l : P, @legendreSym p ⟨hp⟩ (l.val : ℤ) = signInt (s l)} => (1 : ℝ)/p.val) := by
  intro h
  obtain ⟨M,u,hM,hu,hSymbols⟩ := exists_class_for_symbols P hP s
  let : NeZero M := ⟨hM.ne'⟩
  let f (p : {p : ℕ // p.Prime ∧ (p : ZMod M) = u}) :
      {p : ℕ // ∃ hp : p.Prime, p%4=3 ∧
        ∀ l : P, @legendreSym p ⟨hp⟩ (l.val : ℤ) = signInt (s l)} :=
    ⟨p.val, ⟨p.property.1, hSymbols p.val p.property.1 p.property.2⟩⟩
  apply not_summable_primes_in_class u hu
  exact h.comp_injective (i := f) (fun _ _ h => Subtype.ext (congrArg (fun q => q.val) h))

end Erdos940QuarticPrimes


namespace Erdos940QuarticBias

open Finset

private def sign (t : ZMod 2) : ℝ := if t = 0 then 1 else -1

private theorem sign_zero : sign 0 = 1 := by simp [sign]

private theorem sign_one : sign 1 = -1 := by simp [sign]

private theorem two_cases (t : ZMod 2) : t = 0 ∨ t = 1 := by
  fin_cases t
  · exact Or.inl rfl
  · exact Or.inr rfl

private theorem one_add_one_two : (1 : ZMod 2) + 1 = 0 := by decide

private theorem sign_add (s t : ZMod 2) : sign (s+t) = sign s * sign t := by
  rcases two_cases s with rfl | rfl <;> rcases two_cases t with rfl | rfl <;>
    simp [sign_zero, sign_one, one_add_one_two]

/-- The real quadratic character indexed by a parity vector. -/
private def character {ι : Type} [Fintype ι] (a b : ι → ZMod 2) : ℝ :=
  sign (∑ i, a i * b i)

theorem abs_character {ι : Type} [Fintype ι] (a b : ι → ZMod 2) :
    |character a b| = 1 := by
  unfold character sign
  split <;> norm_num

theorem character_add_left {ι : Type} [Fintype ι] (a b g : ι → ZMod 2) :
    character (a+b) g = character a g * character b g := by
  simp only [character, Pi.add_apply, add_mul, Finset.sum_add_distrib, sign_add]

theorem character_add_right {ι : Type} [Fintype ι] (a b g : ι → ZMod 2) :
    character a (b+g) = character a b * character a g := by
  simp only [character, Pi.add_apply, mul_add, Finset.sum_add_distrib, sign_add]

private theorem character_sum {ι : Type} [Fintype ι] [DecidableEq ι] (a : ι → ZMod 2) :
    ∑ g, character a g = if a = 0 then (Fintype.card (ι → ZMod 2) : ℝ) else 0 := by
  classical
  by_cases ha : a = 0
  · simp [ha, character, sign_zero]
  rw [if_neg ha]
  have hOne : ∃ i, a i ≠ 0 := by
    by_contra! hh
    apply ha
    funext i
    exact hh i
  obtain ⟨j,hj⟩ := hOne
  let e : ι → ZMod 2 := fun i => if i = j then 1 else 0
  have hj1 : a j = 1 := (two_cases (a j)).resolve_left hj
  have he : character a e = -1 := by
    unfold character
    have hsum : (∑ i, a i * e i) = 1 := by
      rw [Finset.sum_eq_single j]
      · simp [e, hj1]
      · intro i _ hn
        simp [e, hn]
      · simp
    rw [hsum, sign_one]
  have hshift := Fintype.sum_equiv (Equiv.addLeft e)
    (fun g => character a (e+g)) (character a) (fun _ => rfl)
  have hneg : ∑ g, character a (e+g) = -(∑ g, character a g) := by
    simp only [character_add_right, he, neg_one_mul, sum_neg_distrib]
  change (∑ g, character a (e+g)) = ∑ g, character a g at hshift
  rw [hneg] at hshift
  linarith

private theorem add_eq_zero_iff_eq {ι : Type} (a b : ι → ZMod 2) :
    a+b=0 ↔ a=b := by
  constructor
  · intro h
    funext i
    have hi := congrArg (fun f : ι → ZMod 2 => f i) h
    change a i + b i = 0 at hi
    rcases two_cases (a i) with hA | hA <;> rcases two_cases (b i) with hB | hB <;>
      simp [hA, hB] at hi ⊢
  · rintro rfl
    funext i
    change a i + a i = 0
    rcases two_cases (a i) with h | h <;> simp [h, one_add_one_two]

theorem orthogonality {ι : Type} [Fintype ι] [DecidableEq ι]
    (a b : ι → ZMod 2) :
    (∑ g, character a g * character b g) =
      if a = b then (Fintype.card (ι → ZMod 2) : ℝ) else 0 := by
  simp only [← character_add_left, character_sum, add_eq_zero_iff_eq]

private noncomputable def bias {ι : Type} [Fintype ι] (S : Finset (ι → ZMod 2))
    (c : (ι → ZMod 2) → ℝ) (g : ι → ZMod 2) : ℝ :=
  1 - ∑ a ∈ S, c a * character a g

/-- A nonnegative distribution with the prescribed negative character expectations
for every selected nontrivial character at once. -/
theorem bias_distribution {ι : Type} [Fintype ι] [DecidableEq ι] (S : Finset (ι → ZMod 2))
    (c : (ι → ZMod 2) → ℝ) (h0 : 0 ∉ S) (hc : ∀ a ∈ S, 0 ≤ c a)
    (hC : ∑ a ∈ S, c a ≤ 1/2) :
    (∀ g, 1/2 ≤ bias S c g) ∧
    (∑ g, bias S c g) = (Fintype.card (ι → ZMod 2) : ℝ) ∧
    ∀ a ∈ S, (∑ g, bias S c g * character a g) = -(Fintype.card (ι → ZMod 2) : ℝ) * c a := by
  classical
  have hN (a : ι → ZMod 2) (ha : a ∈ S) : a ≠ 0 := fun h => h0 (h ▸ ha)
  have hsum (a : ι → ZMod 2) (ha : a ∈ S) : (∑ g, character a g) = 0 := by
    rw [character_sum, if_neg (hN a ha)]
  refine ⟨?_, ?_, ?_⟩
  · intro g
    have hB : (∑ a ∈ S, c a * character a g) ≤ ∑ a ∈ S, c a := by
      apply Finset.sum_le_sum
      intro a ha
      nth_rewrite 2 [← mul_one (c a)]
      exact mul_le_mul_of_nonneg_left ((le_abs_self _).trans_eq (abs_character a g)) (hc a ha)
    unfold bias
    linarith
  · unfold bias
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one, Finset.sum_comm]
    have hZ : (∑ a ∈ S, ∑ g, c a * character a g) = 0 := by
      apply Finset.sum_eq_zero
      intro a ha
      rw [← Finset.mul_sum, hsum a ha, mul_zero]
    rw [hZ, sub_zero, Finset.card_univ]
  · intro a ha
    unfold bias
    simp only [sub_mul, one_mul, Finset.sum_sub_distrib, hsum a ha, zero_sub]
    have hinner (b : ι → ZMod 2) :
        (∑ g, (c b * character b g) * character a g) =
          c b * if b = a then (Fintype.card (ι → ZMod 2) : ℝ) else 0 := by
      simp only [mul_assoc, ← Finset.mul_sum, orthogonality]
    rw [show (∑ g : ι → ZMod 2, (∑ b ∈ S, c b * character b g) * character a g) =
        ∑ b ∈ S, ∑ g, (c b * character b g) * character a g by
      simp only [Finset.sum_mul]
      exact Finset.sum_comm]
    simp only [hinner, mul_ite, mul_zero, Finset.sum_ite_eq', ha, if_true]
    ring

end Erdos940QuarticBias


namespace Erdos940QuarticPrimeWindow

open Finset

/-- A divergent nonnegative series with terms at most one has a finite
partial sum in every interval [T,T+1] for T nonnegative. -/
theorem sum_window {ι : Type} (w : ι → ℝ) (h0 : ∀ i, 0 ≤ w i) (h1 : ∀ i, w i ≤ 1)
    (hns : ¬ Summable w) (T : ℝ) (hT : 0 ≤ T) :
    ∃ S : Finset ι, T ≤ ∑ i ∈ S, w i ∧ ∑ i ∈ S, w i ≤ T + 1 := by
  classical
  have hSome : ∃ n : ℕ, ∃ S : Finset ι, S.card = n ∧ T ≤ ∑ i ∈ S, w i := by
    by_contra! h
    apply hns
    exact summable_of_sum_le h0 (fun S => (h S.card S rfl).le)
  obtain ⟨S, hn, hlo⟩ := Nat.find_spec hSome
  refine ⟨S, hlo, ?_⟩
  by_cases hs : S = ∅
  · simp [hs]
    linarith
  · obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hs
    have hsmall : (∑ j ∈ S.erase i, w j) < T := by
      by_contra! hh
      have hmin := Nat.find_min' hSome ⟨S.erase i, rfl, hh⟩
      have hl := Finset.card_erase_lt_of_mem hi
      omega
    have he := Finset.sum_erase_add S w hi
    linarith [h1 i]

end Erdos940QuarticPrimeWindow

namespace Erdos940QuarticPrimes

open Finset Filter Set Erdos940QuarticBias

/-- Arithmetic condition defining a band of primes with the same character pattern. -/
private def realizes (P : Finset ℕ) (s : P → ZMod 2) (p : ℕ) : Prop :=
  ∃ hp : p.Prime, p % 4 = 3 ∧
    ∀ l : P, @legendreSym p ⟨hp⟩ (l.val : ℤ) = signInt (s l)

theorem realizes_unique {P : Finset ℕ} {s t : P → ZMod 2} {p : ℕ}
    (hs : realizes P s p) (ht : realizes P t p) : s = t := by
  obtain ⟨hp,_,hs⟩ := hs
  obtain ⟨_,_,ht⟩ := ht
  funext l
  have h := (hs l).symm.trans (ht l)
  unfold signInt at h
  rcases Erdos940QuarticBias.two_cases (s l) with h₁ | h₁ <;>
    rcases Erdos940QuarticBias.two_cases (t l) with h₂ | h₂ <;>
    simp_all

/-- After any cutoff, a single symbol pattern realizes every nonnegative reciprocal
mass to within the reciprocal of the cutoff. -/
theorem symbol_prime_window (P : Finset ℕ) (hP : ∀ l ∈ P, l.Prime) (s : P → ZMod 2)
    (B : ℕ) (hB : 0 < B) (T : ℝ) (hT : 0 ≤ T) :
    ∃ Q : Finset ℕ, (∀ p ∈ Q, B < p ∧ realizes P s p) ∧
      T ≤ (∑ p ∈ Q, (1 : ℝ)/p) ∧ (∑ p ∈ Q, (1 : ℝ)/p) ≤ T + 1/(B : ℝ) := by
  classical
  let A := {p : ℕ // realizes P s p}
  let u (p : A) : ℝ := 1/p.val
  let w (p : A) : ℝ := if B < p.val then (B : ℝ)*u p else 0
  have hBR : 0 < (B : ℝ) := by exact_mod_cast hB
  have hns : ¬ Summable w := by
    intro h
    have he : w =ᶠ[Filter.cofinite] fun p => (B : ℝ)*u p := by
      apply Filter.eventually_cofinite.mpr
      apply (Set.Finite.preimage_embedding (⟨Subtype.val, Subtype.val_injective⟩ : A ↪ ℕ)
        (Set.finite_Iic B)).subset
      intro p hp
      change p.val ≤ B
      by_contra! hpc
      exact hp (if_pos hpc)
    apply not_summable_symbol_primes P hP s
    change Summable u
    have hm := (h.congr_cofinite he).mul_left ((B : ℝ)⁻¹)
    simpa only [← mul_assoc, inv_mul_cancel₀ hBR.ne', one_mul] using hm
  have h0 (p : A) : 0 ≤ w p := by
    unfold w u
    split <;> positivity
  have h1 (p : A) : w p ≤ 1 := by
    unfold w u
    split
    · rename_i hp
      have hpc : (B : ℝ) < p.val := by exact_mod_cast hp
      rw [mul_one_div]
      exact (div_le_one (hBR.trans hpc)).mpr hpc.le
    · norm_num
  obtain ⟨R,hlo,hhi⟩ := Erdos940QuarticPrimeWindow.sum_window w h0 h1 hns ((B : ℝ)*T)
    (mul_nonneg hBR.le hT)
  let emb : A ↪ ℕ := ⟨Subtype.val, Subtype.val_injective⟩
  let Q := (R.filter fun p => B < p.val).map emb
  have heq : (∑ p ∈ R, w p) = (B : ℝ) * ∑ p ∈ Q, (1 : ℝ)/p := by
    simp only [w, Q, Finset.sum_map, ← Finset.sum_filter, Finset.mul_sum]
    rfl
  rw [heq] at hlo hhi
  refine ⟨Q, ?_, (mul_le_mul_iff_right₀ hBR).mp hlo, (mul_le_mul_iff_right₀ hBR).mp ?_⟩
  · intro p hp
    obtain ⟨q,hq,rfl⟩ := Finset.mem_map.mp hp
    exact ⟨(Finset.mem_filter.mp hq).2, q.property⟩
  · rw [mul_add, mul_one_div, div_self hBR.ne']
    exact hhi

/-- A single finite set controls both the total reciprocal budget and all the
signed reciprocal sums. Each prime retains the pattern witnessing its local signs. -/
theorem simultaneous_signed_prime_sums (P : Finset ℕ) (hP : ∀ l ∈ P, l.Prime)
    (S : Finset (P → ZMod 2)) (c : (P → ZMod 2) → ℝ)
    (h0 : 0 ∉ S) (hc : ∀ a ∈ S, 0 ≤ c a) (hC : ∑ a ∈ S, c a ≤ 1/2)
    (B : ℕ) (hB : Fintype.card (P → ZMod 2) ≤ B) (T : ℝ) (hT : 0 ≤ T) :
    ∃ (Q : Finset ℕ) (pat : ℕ → P → ZMod 2),
      (∀ p ∈ Q, B < p ∧ realizes P (pat p) p) ∧
      (∑ p ∈ Q, (1 : ℝ)/p) ≤ T + 1 ∧
      ∀ a ∈ S, (∑ p ∈ Q, character a (pat p) / (p : ℝ)) ≤ -T * c a + 1 := by
  classical
  let G := P → ZMod 2
  let K := (Fintype.card G : ℝ)
  have hkNat : 0 < Fintype.card G := Fintype.card_pos
  have hk : 0 < K := by
    dsimp only [K]
    exact_mod_cast hkNat
  have hb : 0 < B := hkNat.trans_le hB
  have hkB : K ≤ (B : ℝ) := by
    dsimp only [K]
    exact_mod_cast hB
  obtain ⟨hpos,hsum,hsigned⟩ := bias_distribution S c h0 hc hC
  let t (g : G) := T * bias S c g / K
  have ht (g : G) : 0 ≤ t g :=
    div_nonneg (mul_nonneg hT (by linarith [hpos g])) hk.le
  have eSmall : (1 : ℝ)/(B : ℝ) ≤ 1/K :=
    one_div_le_one_div_of_le hk hkB
  have hex (g : G) : ∃ Q : Finset ℕ, (∀ p ∈ Q, B < p ∧ realizes P g p) ∧
      t g ≤ (∑ p ∈ Q, (1 : ℝ)/p) ∧ (∑ p ∈ Q, (1 : ℝ)/p) ≤ t g + 1/K := by
    obtain ⟨Q, hQ, hlo, hhi⟩ := symbol_prime_window P hP g B hb (t g) (ht g)
    exact ⟨Q, hQ, hlo, hhi.trans (add_le_add_right eSmall _)⟩
  choose D hD hLo hHi using hex
  let Q := Finset.univ.biUnion D
  have hin (p : ℕ) (hp : p ∈ Q) : ∃ g : G, p ∈ D g :=
    (mem_biUnion.mp hp).imp fun _ h => h.2
  let pat (p : ℕ) : G := if hp : p ∈ Q then (hin p hp).choose else 0
  have hPat (p : ℕ) (hp : p ∈ Q) : p ∈ D (pat p) := by
    simp only [pat, dif_pos hp]
    exact (hin p hp).choose_spec
  have hPatEq (g : G) (p : ℕ) (hp : p ∈ D g) : pat p = g :=
    realizes_unique ((hD _ p (hPat p (mem_biUnion.mpr ⟨g, mem_univ _, hp⟩))).2) ((hD _ p hp).2)
  have hd : (↑(Finset.univ : Finset G) : Set G).PairwiseDisjoint D := by
    intro g _ j _ hne
    apply Finset.disjoint_left.mpr
    intro p hg hj
    exact hne (realizes_unique ((hD _ p hg).2) ((hD _ p hj).2))
  have htSum : (∑ g, t g) = T := by
    have hm : (∑ g : G, bias S c g) = K := hsum
    simp only [t, ← Finset.sum_div, ← Finset.mul_sum, hm]
    exact mul_div_cancel_right₀ T hk.ne'
  have htWeighted (a : G) (ha : a ∈ S) : ∑ g, t g * character a g = -T * c a := by
    calc
      _ = (T / K) * ∑ g, bias S c g * character a g := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro g _
        unfold t
        ring
      _ = _ := by rw [hsigned a ha]; field_simp; ring
  have hOne : (∑ _ : G, (1 : ℝ)/K) = 1 := by
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, mul_one_div, div_self hk.ne']
  refine ⟨Q,pat, fun p hp => hD _ p (hPat p hp), ?_, ?_⟩
  · rw [Finset.sum_biUnion hd]
    calc
      _ ≤ ∑ g, (t g + 1/K) := Finset.sum_le_sum fun g _ => hHi g
      _ = T + 1 := by rw [Finset.sum_add_distrib, htSum, hOne]
  · intro a ha
    rw [Finset.sum_biUnion hd]
    have hbnd (g : G) : (∑ p ∈ D g, character a (pat p) / (p : ℝ)) ≤
        t g * character a g + 1/K := by
      have he : (∑ p ∈ D g, character a (pat p) / (p : ℝ)) =
          (∑ p ∈ D g, (1 : ℝ)/p) * character a g := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro p hp
        rw [hPatEq g p hp]
        ring
      rw [he]
      have hcases : character a g = 1 ∨ character a g = -1 := by
        have ha := abs_character a g
        rcases le_total 0 (character a g) with h | h
        · exact Or.inl (by simpa [abs_of_nonneg h] using ha)
        · exact Or.inr (by rw [abs_of_nonpos h] at ha; linarith)
      rcases hcases with h | h
      · simpa only [h, mul_one] using hHi g
      · simp only [h, mul_neg, mul_one]
        have := hLo g
        linarith [show (0 : ℝ) ≤ 1/K by positivity]
    calc
      _ ≤ ∑ g, (t g * character a g + 1/K) := Finset.sum_le_sum fun g _ => hbnd g
      _ = -T * c a + 1 := by rw [Finset.sum_add_distrib, htWeighted a ha, hOne]

end Erdos940QuarticPrimes


namespace Erdos940QuarticPrimes

open Finset Erdos940QuarticBias

private theorem signInt_mul (s t : ZMod 2) : signInt (s + t) = signInt s * signInt t := by
  rcases Erdos940QuarticBias.two_cases s with rfl | rfl <;>
    rcases Erdos940QuarticBias.two_cases t with rfl | rfl <;>
    simp [signInt, Erdos940QuarticBias.one_add_one_two]

private theorem signInt_nsmul (n : ℕ) (s : ZMod 2) :
    signInt ((n : ZMod 2) * s) = (signInt s)^n := by
  induction n with
  | zero => simp [signInt]
  | succ n ih => rw [Nat.cast_succ, add_mul, one_mul, signInt_mul, ih, pow_succ]

private theorem signInt_sum {ι : Type} (S : Finset ι) (f : ι → ZMod 2) :
    signInt (∑ i ∈ S, f i) = ∏ i ∈ S, signInt (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [signInt]
  | insert i S hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, signInt_mul, ih]

/-- The parity vector of the prime exponents of a positive coefficient product. -/
private def parity (P : Finset ℕ) (D : ℕ) (l : P) : ZMod 2 := D.factorization l.val

private theorem factorization_over {P : Finset ℕ} {D : ℕ} (hD : D ≠ 0)
    (hP : D.primeFactors ⊆ P) : D = ∏ l : P, l.val ^ D.factorization l.val := by
  calc
    D = ∏ l ∈ D.primeFactors, l ^ D.factorization l := Nat.prod_primeFactors_pow_factorization hD
    _ = ∏ l ∈ P, l ^ D.factorization l := by
      apply Finset.prod_subset hP
      intro l _ hl
      rw [← Nat.support_factorization, Finsupp.notMem_support_iff] at hl
      rw [hl, pow_zero]
    _ = _ := by simp

theorem parity_ne_zero {P : Finset ℕ} {D : ℕ} (hD : D ≠ 0)
    (hP : D.primeFactors ⊆ P) (hn : ¬ IsSquare D) : parity P D ≠ 0 := by
  intro h
  apply hn
  refine ⟨∏ l : P, l.val ^ (D.factorization l.val / 2), ?_⟩
  rw [← pow_two, ← Finset.prod_pow]
  calc
    D = ∏ l : P, l.val ^ D.factorization l.val := factorization_over hD hP
    _ = _ := by
      apply Finset.prod_congr rfl
      intro l _
      have he : (D.factorization l.val : ZMod 2) = 0 := congrFun h l
      obtain ⟨k,hk⟩ := (ZMod.natCast_eq_zero_iff (D.factorization l.val) 2).mp he
      rw [← pow_mul]
      congr 1
      omega

theorem legendre_product_of_realizes {P : Finset ℕ} {D p : ℕ} (hD : D ≠ 0)
    (hP : D.primeFactors ⊆ P) [Fact p.Prime] {s : P → ZMod 2}
    (hs : realizes P s p) :
    (legendreSym p (D : ℤ) : ℝ) = character (parity P D) s := by
  obtain ⟨hp,_,hs⟩ := hs
  have hDProd : (D : ℤ) = ∏ l : P, (l.val : ℤ) ^ D.factorization l.val := by
    exact_mod_cast factorization_over hD hP
  have hInt : legendreSym p (D : ℤ) = signInt (∑ l : P, parity P D l * s l) := by
    rw [hDProd, signInt_sum]
    change (legendreSym.hom p) (∏ l : P, (l.val : ℤ)^D.factorization l.val) = _
    rw [map_prod]
    apply Finset.prod_congr rfl
    intro l _
    rw [map_pow, parity, signInt_nsmul]
    exact congrArg (fun j : ℤ => j ^ D.factorization l.val) (hs l)
  rw [hInt]
  unfold character signInt Erdos940QuarticBias.sign
  split <;> norm_num

end Erdos940QuarticPrimes

namespace Erdos940Quartic

open Finset Erdos940QuarticPrimes Erdos940QuarticBias

/-- Local factor at a prime square with valuation-one target. -/
private noncomputable def valuationOneFactor (a : Fin 4 → ℕ) (p : ℕ) : ℝ :=
  (count (fun i => (a i : ZMod (p*p))) (p : ZMod (p*p)) : ℝ)/(p : ℝ)^6

theorem valuationOneFactor_nonneg (a : Fin 4 → ℕ) (p : ℕ) :
    0 ≤ valuationOneFactor a p := by unfold valuationOneFactor; positivity

theorem valuationOneFactor_le_four {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (a : Fin 4 → ℕ) (ha : ∀ i, (4 : ℕ).Full (a i)) :
    valuationOneFactor a p ≤ 4 := by
  have hp : 0 < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  apply (div_le_iff₀ (pow_pos hp _)).2
  exact_mod_cast valuation_one_count_le hp2 a ha

/-- Exact normalized local factor at an inert prime outside the coefficient support. -/
theorem valuationOneFactor_inert {p : ℕ} [Fact p.Prime] (hp : p % 4 = 3)
    (a : Fin 4 → ℕ) (ha : ∀ i, (4 : ℕ).Full (a i)) (hgood : ∀ i, ¬ p ∣ a i) :
    valuationOneFactor a p =
      1 + ((p : ℝ)-1)/(p : ℝ)^2 * (legendreSym p ((∏ i, a i : ℕ) : ℤ) : ℝ) -
        1/(p : ℝ)^3 := by
  classical
  let C := count (fun i => (a i : ZMod p)) 0
  let : Nonempty (Solutions (fun i => (a i : ZMod p)) 0) := ⟨⟨fun _ => 0, by simp⟩⟩
  let : Finite (Solutions (fun i => (a i : ZMod p)) 0) := by
    unfold Solutions
    infer_instance
  have hC : 1 ≤ C := Nat.card_pos (α := Solutions _ _)
  have hpPos : 0 < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  have hzero := inert_zero_count hp (fun i => (a i : ZMod p))
    (fun i h => hgood i ((ZMod.natCast_eq_zero_iff _ _).mp h))
  have hProd : quadraticComplex (ZMod p) (∏ i, (a i : ZMod p)) =
      (legendreSym p ((∏ i, a i : ℕ) : ℤ) : ℂ) := by
    simp only [quadratic_apply, legendreSym, Int.cast_natCast, Int.cast_prod, Nat.cast_prod]
  rw [hProd] at hzero
  have hReal' : (C : ℝ) = (p : ℝ)^3 +
      (legendreSym p ((∏ i, a i : ℕ) : ℤ) : ℝ) * p * ((p : ℝ)-1) := by
    simpa [C, pow_succ, Complex.mul_re, Complex.mul_im, Complex.add_re,
      Complex.sub_re, Complex.sub_im] using congrArg Complex.re hzero
  unfold valuationOneFactor
  rw [valuation_one_count_good (by omega : p ≠ 2) a ha hgood]
  change ((p^3 * (C - 1) : ℕ) : ℝ) / (p : ℝ)^6 = _
  rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_sub hC, Nat.cast_one, hReal']
  field_simp

/-- One set of auxiliary primes suppresses every prescribed nonsquare coefficient
product, even when their quadratic characters are linearly dependent. -/
theorem selected_prime_product_bound (P : Finset ℕ) (hP : ∀ l ∈ P, l.Prime)
    (S : Finset (P → ZMod 2)) (c : (P → ZMod 2) → ℝ)
    (h0 : 0 ∉ S) (hc : ∀ a ∈ S, 0 ≤ c a) (hC : ∑ a ∈ S, c a ≤ 1/2)
    (B : ℕ) (hB : Fintype.card (P → ZMod 2) ≤ B) (hPB : ∀ l ∈ P, l ≤ B)
    (T : ℝ) (hT : 0 ≤ T) (hTB : T + 1 ≤ (B : ℝ)) :
    ∃ Q : Finset ℕ, (∀ p ∈ Q, p.Prime ∧ p % 4 = 3 ∧ B < p) ∧
      (∑ p ∈ Q, (1 : ℝ)/p) ≤ T + 1 ∧
      ∀ (a : Fin 4 → ℕ), (∀ i, (4 : ℕ).Full (a i)) →
        let D := ∏ i, a i
        D ≠ 0 → D.primeFactors ⊆ P → parity P D ∈ S →
          (∏ p ∈ Q, valuationOneFactor a p) ≤ Real.exp (-T * c (parity P D) + 2) := by
  classical
  obtain ⟨Q,pat,hQ,hMass,hS⟩ := simultaneous_signed_prime_sums P hP S c h0 hc hC B hB T hT
  have hBR : 0 < (B : ℝ) := by linarith
  refine ⟨Q, (fun p hp => ?_), hMass, ?_⟩
  · obtain ⟨hBp,hprime,h3,_⟩ := hQ p hp
    exact ⟨hprime,h3,hBp⟩
  intro a ha D hD hSupport hPar
  let chi (p : ℕ) := character (parity P D) (pat p)
  have hR (p : ℕ) (hp : p ∈ Q) : 0 < (p : ℝ) :=
    hBR.trans (by exact_mod_cast (hQ p hp).1)
  have hquad : (∑ p ∈ Q, (1 : ℝ)/(p : ℝ)^2) ≤ 1 := by
    calc
      _ ≤ ∑ p ∈ Q, (1/(B : ℝ)) * (1/(p : ℝ)) := by
        apply Finset.sum_le_sum
        intro p hp
        have hPB' : (B : ℝ) ≤ p := by exact_mod_cast (hQ p hp).1.le
        rw [pow_two, ← one_div_mul_one_div]
        exact mul_le_mul_of_nonneg_right (one_div_le_one_div_of_le hBR hPB') (div_nonneg zero_le_one (hR p hp).le)
      _ = (1/(B : ℝ)) * ∑ p ∈ Q, (1 : ℝ)/p := (Finset.mul_sum _ _ _).symm
      _ ≤ (1/(B : ℝ)) * (B : ℝ) := mul_le_mul_of_nonneg_left (hMass.trans hTB) (by positivity)
      _ = 1 := one_div_mul_cancel hBR.ne'
  have hlocal (p : ℕ) (hp : p ∈ Q) :
      valuationOneFactor a p ≤ Real.exp (chi p / (p : ℝ) + 1/(p : ℝ)^2) := by
    obtain ⟨hpB,hpSym⟩ := hQ p hp
    obtain ⟨hpPrime,hp3,_⟩ := hpSym
    let : Fact p.Prime := ⟨hpPrime⟩
    have hgood (i : Fin 4) : ¬p ∣ a i := by
      intro hd
      have hdiv : p ∣ D := hd.trans (Finset.dvd_prod_of_mem a (Finset.mem_univ i))
      have hmem : p ∈ D.primeFactors := Nat.mem_primeFactors.mpr ⟨hpPrime,hdiv,hD⟩
      exact (not_le_of_gt hpB) (hPB p (hSupport hmem))
    have hSign := legendre_product_of_realizes hD hSupport (hQ p hp).2
    have h1 : -1 ≤ chi p := by
      have he : |chi p| = 1 := abs_character _ _
      exact neg_le_of_abs_le he.le
    have hp0 : (p : ℝ) ≠ 0 := (hR p hp).ne'
    have hnon : 0 ≤ (1/(p : ℝ)^3) := by positivity
    rw [valuationOneFactor_inert hp3 a ha hgood, hSign]
    change 1 + ((p : ℝ)-1)/(p : ℝ)^2 * chi p - 1/(p : ℝ)^3 ≤ _
    calc
      _ = 1 + (chi p / p - chi p / (p : ℝ)^2) - 1/(p : ℝ)^3 := by
        field_simp
      _ ≤ 1 + (chi p / p + 1/(p : ℝ)^2) := by
        have hle := div_le_div_of_nonneg_right h1 (by positivity : 0 ≤ (p : ℝ)^2)
        linarith [show -(1/(p : ℝ)^2) ≤ chi p / (p : ℝ)^2 by simpa [neg_div] using hle]
      _ ≤ _ := by
        rw [add_comm 1]
        exact Real.add_one_le_exp _
  calc
    _ ≤ ∏ p ∈ Q, Real.exp (chi p / (p : ℝ) + 1/(p : ℝ)^2) :=
      Finset.prod_le_prod (fun p _ => valuationOneFactor_nonneg a p) hlocal
    _ = Real.exp ((∑ p ∈ Q, chi p/(p : ℝ)) + (∑ p ∈ Q, (1 : ℝ)/(p : ℝ)^2)) := by
      rw [← Real.exp_sum, Finset.sum_add_distrib]
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith [hS (parity P D) hPar])

end Erdos940Quartic


namespace Erdos940QuarticPrimeHarmonic

open Finset Filter
open scoped Topology

private def primesThrough (B : ℕ) : Finset ℕ := (Finset.range (B+1)).filter Nat.Prime

theorem mem_primesThrough {B p : ℕ} : p ∈ primesThrough B ↔ p.Prime ∧ p ≤ B := by
  simp [primesThrough, and_comm]

private theorem primeFactors_factorial (B : ℕ) : B.factorial.primeFactors = primesThrough B := by
  ext p
  rw [Nat.mem_primeFactors, mem_primesThrough]
  refine ⟨fun h => ⟨h.1, h.1.dvd_factorial.mp h.2.1⟩, fun h => ?_⟩
  exact ⟨h.1,h.1.dvd_factorial.mpr h.2,Nat.factorial_ne_zero _⟩

private theorem div_le_factorial_exp {B p : ℕ} (hp : p.Prime) :
    B/p ≤ B.factorial.factorization p := by
  let k := Nat.log p B + 2
  rw [Nat.factorization_factorial hp (show Nat.log p B < k by dsimp [k]; omega)]
  have h := Finset.single_le_sum
    (s := Finset.Ico 1 k) (f := fun i => B/p^i) (fun i _ => Nat.zero_le _) (a := 1)
    (by simp [k])
  simpa only [pow_one] using h

private theorem div_real_le_twice_nat_div {B p : ℕ} (hp : 0 < p) (hb : p ≤ B) :
    (B : ℝ)/(p : ℝ) ≤ 2 * (B/p : ℕ) := by
  have hq : 0 < B/p := Nat.div_pos hb hp
  have hB : B ≤ 2*p*(B/p) := by
    calc
      B = p*(B/p)+B%p := (Nat.div_add_mod _ _).symm
      _ ≤ p*(B/p)+p*(B/p) := Nat.add_le_add_left
        ((Nat.mod_lt _ hp).le.trans (Nat.le_mul_of_pos_right p hq)) _
      _ = _ := by ring
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp
  apply (div_le_iff₀ hpR).mpr
  have hBR : (B : ℝ) ≤ 2*(p : ℝ)*(B/p : ℕ) := by exact_mod_cast hB
  linarith only [hBR]

/-- A factorial bound on the weighted prime harmonic sum, with no
asymptotic prime-counting result. -/
theorem weighted_harmonic_le {B : ℕ} (hB : 0 < B) :
    (∑ p ∈ primesThrough B, Real.log p / (p : ℝ)) ≤ 2*Real.log B := by
  have hBR : 0 < (B : ℝ) := by exact_mod_cast hB
  have hLog : (∑ p ∈ primesThrough B, (B.factorial.factorization p : ℝ)*Real.log p) =
      Real.log (B.factorial : ℝ) := by
    rw [Real.log_nat_eq_sum_factorization, Finsupp.sum, Nat.support_factorization,
      primeFactors_factorial]
  have hFact : Real.log (B.factorial : ℝ) ≤ (B : ℝ)*Real.log B := by
    rw [← Real.log_pow]
    apply Real.log_le_log (by exact_mod_cast Nat.factorial_pos B)
    exact_mod_cast Nat.factorial_le_pow B
  calc
    _ ≤ ∑ p ∈ primesThrough B,
        (2 / (B : ℝ)) * ((B.factorial.factorization p : ℝ)*Real.log p) := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨hPrime,hpB⟩ := mem_primesThrough.mp hp
      have hpR : 0 < (p : ℝ) := by exact_mod_cast hPrime.pos
      have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hPrime.pos)
      have hq := div_real_le_twice_nat_div hPrime.pos hpB
      have he : ((B/p : ℕ) : ℝ) ≤ (B.factorial.factorization p : ℝ) := by
        exact_mod_cast div_le_factorial_exp hPrime (B := B)
      have hI := hq.trans (mul_le_mul_of_nonneg_left he (by norm_num))
      have hJ := mul_le_mul_of_nonneg_right hI hlog
      apply (mul_le_mul_iff_right₀ hBR).mp
      calc
        _ = ((B : ℝ)/p)*Real.log p := by field_simp
        _ ≤ (2 * B.factorial.factorization p) * Real.log p := hJ
        _ = _ := by field_simp
    _ = (2/(B : ℝ))*Real.log (B.factorial : ℝ) := by rw [← Finset.mul_sum, hLog]
    _ ≤ (2/(B : ℝ))*((B : ℝ)*Real.log B) := mul_le_mul_of_nonneg_left hFact (by positivity)
    _ = _ := by field_simp

/-- The product estimated by the prime reciprocals grows more slowly
than every fixed positive power of the baseline cutoff. -/
theorem exp_harmonic_subpower (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ B : ℕ, 0 < B →
      Real.exp (21 * ∑ p ∈ primesThrough B, (1 : ℝ)/p) ≤ C * (B : ℝ)^η := by
  have ht : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨K,hK⟩ := eventually_atTop.mp (ht.eventually_ge_atTop (42/η))
  let small : ℝ := ∑ p ∈ primesThrough K, (21 : ℝ)/p
  refine ⟨Real.exp small,Real.exp_pos _,?_⟩
  intro B hB
  have hBR : 0 < (B : ℝ) := by exact_mod_cast hB
  have hSmall : (∑ p ∈ (primesThrough B).filter (fun p => p < K), (21 : ℝ)/p) ≤ small := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      obtain ⟨hp,hlt⟩ := Finset.mem_filter.mp hp
      exact mem_primesThrough.mpr ⟨(mem_primesThrough.mp hp).1,hlt.le⟩
    · intro p _ _
      positivity
  have hLarge : (∑ p ∈ (primesThrough B).filter (fun p => ¬p < K), (21 : ℝ)/p) ≤
      (η/2) * (∑ p ∈ primesThrough B, Real.log p/(p : ℝ)) := by
    rw [Finset.mul_sum]
    calc
      _ ≤ ∑ p ∈ (primesThrough B).filter (fun p => ¬p < K), (η/2)*(Real.log p/(p : ℝ)) := by
        apply Finset.sum_le_sum
        intro p hp
        obtain ⟨hp,hlt⟩ := Finset.mem_filter.mp hp
        have hpR : 0 < (p : ℝ) := by exact_mod_cast (mem_primesThrough.mp hp).1.pos
        have h := (div_le_iff₀ hη).mp (hK p (not_lt.mp hlt))
        rw [← mul_div_assoc]
        exact div_le_div_of_nonneg_right (by linarith) hpR.le
      _ ≤ _ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro p hp _
        have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (mem_primesThrough.mp hp).1.pos
        exact mul_nonneg (by positivity) (div_nonneg (Real.log_nonneg hp1) (by positivity))
  have hBnd := hLarge.trans (mul_le_mul_of_nonneg_left (weighted_harmonic_le hB)
    (by positivity : 0 ≤ η/2))
  have hMass : (21 * ∑ p ∈ primesThrough B, (1 : ℝ)/p) ≤ small + η*Real.log B := by
    simp only [Finset.mul_sum, mul_one_div]
    rw [← Finset.sum_filter_add_sum_filter_not (s := primesThrough B) (p := fun p => p < K)]
    linarith
  rw [Real.rpow_def_of_pos hBR, ← Real.exp_add]
  exact Real.exp_le_exp.mpr (by linarith)

end Erdos940QuarticPrimeHarmonic


namespace Erdos940Quartic

open Finset

private theorem count_ringEquiv {R S : Type} [CommRing R] [CommRing S]
    (e : R ≃+* S) (a : Fin 4 → R) (u : R) :
    count a u = count (fun i => e (a i)) (e u) := by
  let E : (Fin 4 → R) ≃ (Fin 4 → S) := Equiv.piCongrRight (fun _ => e.toEquiv)
  apply Nat.card_congr (E.subtypeEquiv ?_)
  intro x
  have he : e (∑ i, a i*(x i)^4) = ∑ i, e (a i)*(e (x i))^4 := by simp
  change (∑ i, a i*(x i)^4) = u ↔ (∑ i, e (a i)*(e (x i))^4) = e u
  rw [← he, e.injective.eq_iff]

private def count_split_prod {R S : Type} [CommRing R] [CommRing S]
    (a : Fin 4 → R × S) (u : R × S) :
    Solutions a u ≃ Solutions (fun i => (a i).1) u.1 × Solutions (fun i => (a i).2) u.2 where
  toFun v := ⟨⟨fun i => (v.val i).1, by
      have h := congrArg (RingHom.fst R S) v.property
      simpa only [map_sum,map_mul,map_pow,RingHom.coe_fst] using h⟩,
    ⟨fun i => (v.val i).2, by
      have h := congrArg (RingHom.snd R S) v.property
      simpa only [map_sum,map_mul,map_pow,RingHom.coe_snd] using h⟩⟩
  invFun v := ⟨fun i => (v.1.val i,v.2.val i), by
    apply Prod.ext
    · change RingHom.fst R S (∑ i, a i * (v.1.val i,v.2.val i)^4) = u.1
      simpa only [map_sum, map_mul, map_pow, RingHom.coe_fst] using v.1.property
    · change RingHom.snd R S (∑ i, a i * (v.1.val i,v.2.val i)^4) = u.2
      simpa only [map_sum, map_mul, map_pow, RingHom.coe_snd] using v.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Normalized local factor for an arbitrary integer target and modulus. -/
private noncomputable def localFactor (M : ℕ) (a : Fin 4 → ℕ) (u : ℕ) : ℝ :=
  (count (fun i => (a i : ZMod M)) (u : ZMod M) : ℝ) / (M : ℝ)^3

theorem localFactor_nonneg (M : ℕ) (a : Fin 4 → ℕ) (u : ℕ) : 0 ≤ localFactor M a u := by
  unfold localFactor
  positivity

theorem localFactor_mul {m n : ℕ} (hmn : m.Coprime n) (a : Fin 4 → ℕ) (u : ℕ) :
    localFactor (m*n) a u = localFactor m a u * localFactor n a u := by
  let e := ZMod.chineseRemainder hmn
  unfold localFactor
  have h := count_ringEquiv e (fun i => (a i : ZMod (m*n))) u
  simp only [map_natCast] at h
  rw [h]
  unfold count
  rw [Nat.card_congr (count_split_prod _ _), Nat.card_prod]
  simp [mul_pow, div_mul_div_comm, Nat.cast_mul]

private theorem localFactor_one (a : Fin 4 → ℕ) (u : ℕ) : localFactor 1 a u = 1 := by
  let S := Solutions (fun i => (a i : ZMod 1)) (u : ZMod 1)
  let z : S := ⟨fun _ => 0, Subsingleton.elim _ _⟩
  let : Unique S := ⟨⟨z⟩, fun _ => Subtype.ext (Subsingleton.elim _ _)⟩
  unfold localFactor count
  change (Nat.card S : ℝ) / ((1 : ℕ) : ℝ)^3 = 1
  simp

/-- CRT factors the normalized density over an arbitrary finite family of
pairwise coprime moduli. -/
theorem localFactor_prod {ι : Type} (S : Finset ι) (m : ι → ℕ)
    (hm : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → (m i).Coprime (m j))
    (a : Fin 4 → ℕ) (u : ℕ) :
    localFactor (∏ i ∈ S, m i) a u = ∏ i ∈ S, localFactor (m i) a u := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [localFactor_one]
  | insert i S hi ih =>
    have hp : (m i).Coprime (∏ j ∈ S, m j) :=
      Nat.Coprime.prod_right fun j hj => hm i (mem_insert_self _ _) j (mem_insert_of_mem hj)
        (fun h => hi (h ▸ hj))
    have hm' : ∀ v ∈ S, ∀ w ∈ S, v ≠ w → (m v).Coprime (m w) :=
      fun v hv w hw h => hm v (mem_insert_of_mem hv) w (mem_insert_of_mem hw) h
    rw [prod_insert hi, prod_insert hi, localFactor_mul hp, ih hm']

theorem localFactor_congr_target (M : ℕ) (a : Fin 4 → ℕ) {u v : ℕ} (h : u ≡ v [MOD M]) :
    localFactor M a u = localFactor M a v := by
  unfold localFactor
  rw [(ZMod.natCast_eq_natCast_iff u v M).mpr h]

theorem localFactor_prime_sq (p : ℕ) (a : Fin 4 → ℕ) :
    localFactor (p*p) a p = valuationOneFactor a p := by
  unfold localFactor valuationOneFactor
  congr 1
  push_cast
  ring

theorem localFactor_le_modulus (M : ℕ) [NeZero M] (a : Fin 4 → ℕ) (u : ℕ) :
    localFactor M a u ≤ M := by
  have hM : 0 < (M : ℝ) := by exact_mod_cast (NeZero.pos M)
  let U := Solutions (fun i => (a i : ZMod M)) (u : ZMod M)
  have hcount : Nat.card U ≤ M^4 := by
    have h := Nat.card_le_card_of_injective (fun x : U => x.val) Subtype.val_injective
    rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin 4), Fintype.card_fin,
      Nat.card_eq_fintype_card (α := ZMod M), ZMod.card] at h
    exact h
  apply (div_le_iff₀ (pow_pos hM _)).mpr
  change (Nat.card U : ℝ) ≤ (M : ℝ) * (M : ℝ)^3
  rw [← pow_succ']
  exact_mod_cast hcount

private theorem legendre_le_one {p : ℕ} [Fact p.Prime] (a : Fin 4 → ℕ)
    (hgood : ∀ i, ¬ p ∣ a i) :
    (legendreSym p ((∏ i, a i : ℕ) : ℤ) : ℝ) ≤ 1 := by
  have hu : (((∏ i, a i : ℕ) : ℤ) : ZMod p) ≠ 0 := by
    simp only [Int.cast_natCast, Int.cast_prod, Nat.cast_prod]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ h => hgood i ((ZMod.natCast_eq_zero_iff _ _).mp h))
  rcases legendreSym.eq_one_or_neg_one p hu with h | h <;> rw [h] <;> norm_num

theorem valuationOneFactor_le_inert {p : ℕ} [Fact p.Prime] (hp : p % 4 = 3)
    (a : Fin 4 → ℕ) (ha : ∀ i, (4 : ℕ).Full (a i)) (hgood : ∀ i, ¬ p ∣ a i) :
    valuationOneFactor a p ≤ 1+1/(p : ℝ) := by
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hp0 : 0 < (p : ℝ) := by linarith
  have hχ := legendre_le_one a hgood
  have hq : 0 ≤ ((p : ℝ)-1)/(p : ℝ)^2 := by positivity
  have h1 : ((p : ℝ)-1)/(p : ℝ)^2 ≤ 1/(p : ℝ) := by
    apply (div_le_div_iff₀ (pow_pos hp0 _) hp0).mpr
    nlinarith
  rw [valuationOneFactor_inert hp a ha hgood]
  have hle := mul_le_mul_of_nonneg_left hχ hq
  linarith [show 0 ≤ (1 : ℝ)/(p : ℝ)^3 by positivity]

/-- The good-prime factor is at most 1+21/p for every odd prime. -/
theorem valuationOneFactor_le_good {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (a : Fin 4 → ℕ) (ha : ∀ i, (4 : ℕ).Full (a i)) (hgood : ∀ i, ¬ p ∣ a i) :
    valuationOneFactor a p ≤ 1+21/(p : ℝ) := by
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hp0 : 0 < (p : ℝ) := by linarith
  have hpOdd := ((Fact.out : p.Prime).mod_two_eq_one_iff_ne_two).mpr hp2
  rcases Nat.odd_mod_four_iff.mp hpOdd with h1 | h3
  · let N := count (fun i => (a i : ZMod p)) 0
    have hBnd := split_zero_count_bound h1 (fun i => (a i : ZMod p))
      (fun i h => hgood i ((ZMod.natCast_eq_zero_iff _ _).mp h))
    have hN : (N : ℝ) - (p : ℝ)^3 ≤ 21*(p : ℝ)*((p : ℝ)-1) := by
      have hh : ((N : ℂ)-(p : ℂ)^3).re ≤ ‖(N : ℂ)-(p : ℂ)^3‖ := Complex.re_le_norm _
      exact (by simpa [pow_succ, Complex.sub_re, Complex.mul_re, Complex.mul_im] using
        hh.trans hBnd)
    have hLift : (count (fun i => (a i : ZMod (p*p))) (p : ZMod (p*p)) : ℝ) ≤
        (p : ℝ)^3 * N := by
      rw [valuation_one_count_good hp2 a ha hgood]
      exact_mod_cast Nat.mul_le_mul_left (p^3) (Nat.sub_le N 1)
    unfold valuationOneFactor
    calc
      _ ≤ ((p : ℝ)^3*N)/(p : ℝ)^6 := div_le_div_of_nonneg_right hLift (by positivity)
      _ = (N : ℝ)/(p : ℝ)^3 := by field_simp
      _ ≤ ((p : ℝ)^3+21*(p : ℝ)*((p : ℝ)-1))/(p : ℝ)^3 :=
        div_le_div_of_nonneg_right (by linarith) (by positivity)
      _ ≤ _ := by
        apply (div_le_iff₀ (pow_pos hp0 _)).mpr
        have hd : (1+21/(p : ℝ))*(p : ℝ)^3 = (p : ℝ)^3+21*(p : ℝ)^2 := by field_simp
        rw [hd]
        nlinarith
  · apply (valuationOneFactor_le_inert h3 a ha hgood).trans
    linarith [div_le_div_of_nonneg_right (by norm_num : (1 : ℝ) ≤ 21) hp0.le]

end Erdos940Quartic


namespace Erdos940Quartic

open Finset Erdos940QuarticPrimes Erdos940QuarticPrimeHarmonic

private def oddPrimesThrough (B : ℕ) : Finset ℕ := (primesThrough B).erase 2

private def OddPrimeSet (Q : Finset ℕ) : Prop := ∀ p ∈ Q, p.Prime ∧ p ≠ 2

private def primeSystemModulus (Q : Finset ℕ) : ℕ := 16 * ∏ p ∈ Q, p*p

private def primeSystemTarget (Q : Finset ℕ) (u : ℕ) : Prop :=
  (u ≡ 8 [MOD 16]) ∧ ∀ p ∈ Q, u ≡ p [MOD p*p]

theorem oddPrimesThrough_odd (B : ℕ) : OddPrimeSet (oddPrimesThrough B) := by
  intro p hp
  obtain ⟨hp2,hp'⟩ := Finset.mem_erase.mp hp
  exact ⟨(mem_primesThrough.mp hp').1,hp2⟩

private theorem primeSystem_coprime_squares {Q : Finset ℕ} (hQ : OddPrimeSet Q) :
    ∀ i ∈ Q, ∀ j ∈ Q, i ≠ j → (i*i).Coprime (j*j) := by
  intro i hi j hj hij
  have h := (Nat.coprime_primes (hQ i hi).1 (hQ j hj).1).mpr hij
  simpa only [pow_two] using h.pow 2 2

private theorem primeSystem_coprime_16 {Q : Finset ℕ} (hQ : OddPrimeSet Q) :
    (16 : ℕ).Coprime (∏ p ∈ Q, p*p) := by
  apply Nat.Coprime.prod_right
  intro p hp
  have h := (Nat.coprime_primes Nat.prime_two (hQ p hp).1).mpr (hQ p hp).2.symm
  simpa only [pow_two, show (2 : ℕ)^4 = 16 by decide] using h.pow 4 2

theorem primeSystemModulus_pos {Q : Finset ℕ} (hQ : OddPrimeSet Q) :
    0 < primeSystemModulus Q := by
  unfold primeSystemModulus
  exact mul_pos (by decide) (Finset.prod_pos fun p hp => mul_pos (hQ p hp).1.pos (hQ p hp).1.pos)

theorem exists_primeSystemTarget {Q : Finset ℕ} (hQ : OddPrimeSet Q) :
    ∃ u, primeSystemTarget Q u := by
  obtain ⟨a,ha⟩ := assemble_congruences Q (fun p => p*p) id (primeSystem_coprime_squares hQ)
  let u := Nat.chineseRemainder (primeSystem_coprime_16 hQ) 8 a
  refine ⟨u.val, u.property.1, fun p hp => ?_⟩
  exact (u.property.2.of_dvd (Finset.dvd_prod_of_mem (fun p : ℕ => p*p) hp)).trans (ha p hp)

theorem primeSystem_factor {Q : Finset ℕ} (hQ : OddPrimeSet Q) {u : ℕ}
    (hu : primeSystemTarget Q u) (a : Fin 4 → ℕ) :
    localFactor (primeSystemModulus Q) a u =
      localFactor 16 a 8 * ∏ p ∈ Q, valuationOneFactor a p := by
  unfold primeSystemModulus
  rw [localFactor_mul (primeSystem_coprime_16 hQ),
    localFactor_prod Q _ (primeSystem_coprime_squares hQ),
    localFactor_congr_target 16 a hu.1]
  congr 1
  apply Finset.prod_congr rfl
  intro p hp
  rw [localFactor_congr_target _ a (hu.2 p hp), localFactor_prime_sq]

private theorem odd_good_prime_of_not_dvd_product {p : ℕ} (a : Fin 4 → ℕ) (h : ¬p ∣ ∏ i, a i) :
    ∀ i, ¬ p ∣ a i := fun i hi => h (hi.trans (Finset.dvd_prod_of_mem a (Finset.mem_univ i)))

private theorem prod_valuationOneFactor_majorizes {Q : Finset ℕ} (hQ : OddPrimeSet Q)
    (a : Fin 4 → ℕ) (ha : ∀ i, (4 : ℕ).Full (a i)) (ha0 : ∀ i, 0 < a i)
    (f : ℕ → ℝ) (hf : ∀ p ∈ Q, 0 ≤ f p)
    (hGood : ∀ p ∈ Q, (∀ i, ¬p ∣ a i) → valuationOneFactor a p ≤ 1+f p) :
    (∏ p ∈ Q, valuationOneFactor a p) ≤
      (4 : ℝ)^(∏ i, a i : ℕ).primeFactors.card * Real.exp (∑ p ∈ Q, f p) := by
  classical
  let D := ∏ i, a i
  let bad := Q.filter (fun p => p ∣ D)
  let good := Q.filter (fun p => ¬p ∣ D)
  have hD : D ≠ 0 := (Finset.prod_pos fun i _ => ha0 i).ne'
  have hB : bad ⊆ D.primeFactors := by
    intro p hp
    obtain ⟨hp,hdiv⟩ := Finset.mem_filter.mp hp
    exact Nat.mem_primeFactors.mpr ⟨(hQ p hp).1,hdiv,hD⟩
  have hGoodBnd : (∏ p ∈ good, valuationOneFactor a p) ≤ Real.exp (∑ p ∈ Q, f p) := by
    calc
      _ ≤ ∏ p ∈ good, Real.exp (f p) := by
        apply Finset.prod_le_prod (fun p _ => valuationOneFactor_nonneg a p)
        intro p hp
        obtain ⟨hp,hpD⟩ := Finset.mem_filter.mp hp
        exact (hGood p hp (odd_good_prime_of_not_dvd_product a hpD)).trans (by
          rw [add_comm]
          exact Real.add_one_le_exp _)
      _ = Real.exp (∑ p ∈ good, f p) := (Real.exp_sum _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr
        (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun p hp _ => hf p hp)
  have hBadBnd : (∏ p ∈ bad, valuationOneFactor a p) ≤ (4 : ℝ)^D.primeFactors.card := by
    calc
      _ ≤ ∏ p ∈ bad, (4 : ℝ) := by
        apply Finset.prod_le_prod (fun p _ => valuationOneFactor_nonneg a p)
        intro p hp
        have h := hQ p (Finset.mem_filter.mp hp).1
        let : Fact p.Prime := ⟨h.1⟩
        exact valuationOneFactor_le_four h.2 a ha
      _ = (4 : ℝ)^bad.card := Finset.prod_const _
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) (Finset.card_le_card hB)
  rw [← Finset.prod_filter_mul_prod_filter_not (s := Q) (p := fun p => p ∣ D)]
  exact mul_le_mul hBadBnd hGoodBnd (Finset.prod_nonneg fun p _ => valuationOneFactor_nonneg a p)
    (by positivity)

/-- The universal CRT product estimate. Auxiliary primes are inert and
consume reciprocal budget with constant one. -/
theorem primeSystem_universal {B : ℕ} {Q : Finset ℕ}
    (hQ : ∀ p ∈ Q, p.Prime ∧ p%4=3 ∧ B < p)
    (a : Fin 4 → ℕ) (ha : ∀ i, (4 : ℕ).Full (a i)) (ha0 : ∀ i, 0 < a i)
    {u : ℕ} (hu : primeSystemTarget (oddPrimesThrough B ∪ Q) u) :
    localFactor (primeSystemModulus (oddPrimesThrough B ∪ Q)) a u ≤
      16 * (4 : ℝ)^(∏ i, a i : ℕ).primeFactors.card *
        (Real.exp (21 * ∑ p ∈ primesThrough B, (1 : ℝ)/p) *
          Real.exp (∑ p ∈ Q, (1 : ℝ)/p)) := by
  classical
  let R := oddPrimesThrough B
  have hDis : Disjoint R Q := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    exact (not_le_of_gt (hQ p hq).2.2) ((mem_primesThrough.mp (mem_erase.mp hp).2).2)
  have hAll : OddPrimeSet (R ∪ Q) := by
    intro p hp
    rcases Finset.mem_union.mp hp with hR | hP
    · exact oddPrimesThrough_odd B p hR
    · exact ⟨(hQ p hP).1,by have := (hQ p hP).2.1; omega⟩
  let f (p : ℕ) : ℝ := if p ∈ R then 21/(p : ℝ) else 1/(p : ℝ)
  have hf (p : ℕ) (_ : p ∈ R ∪ Q) : 0 ≤ f p := by
    unfold f
    split <;> positivity
  have hProduct := prod_valuationOneFactor_majorizes hAll a ha ha0 f hf (by
    intro p hp hgood
    let : Fact p.Prime := ⟨(hAll p hp).1⟩
    by_cases hP : p ∈ R
    · simpa only [f, if_pos hP] using valuationOneFactor_le_good (hAll p hp).2 a ha hgood
    · have hq := (Finset.mem_union.mp hp).resolve_left hP
      simpa only [f, if_neg hP] using valuationOneFactor_le_inert (hQ p hq).2.1 a ha hgood)
  have hSum : (∑ p ∈ R ∪ Q, f p) ≤
      21 * (∑ p ∈ primesThrough B, (1 : ℝ)/p) + ∑ p ∈ Q, (1 : ℝ)/p := by
    rw [Finset.sum_union hDis, Finset.mul_sum]
    have hA : (∑ p ∈ R, f p) = ∑ p ∈ R, (21 : ℝ)/p := by
      exact Finset.sum_congr rfl (fun p hp => if_pos hp)
    have hB : (∑ p ∈ Q, f p) = ∑ p ∈ Q, (1 : ℝ)/p := by
      exact Finset.sum_congr rfl (fun p hp => if_neg (fun hh => Finset.disjoint_left.mp hDis hh hp))
    rw [hA,hB]
    apply add_le_add_left
    simp only [mul_one_div]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) (fun _ _ _ => by positivity)
  rw [primeSystem_factor hAll hu a]
  calc
    _ ≤ (16 : ℝ) * ((4 : ℝ)^(∏ i, a i : ℕ).primeFactors.card * Real.exp (∑ p ∈ R ∪ Q, f p)) :=
      mul_le_mul (localFactor_le_modulus 16 a 8) hProduct
        (Finset.prod_nonneg fun p _ => valuationOneFactor_nonneg a p) (by norm_num)
    _ ≤ _ := by
      rw [mul_assoc, ← Real.exp_add]
      gcongr

end Erdos940Quartic

namespace Erdos940QuarticElimination

private theorem pow_dvd_of_full {p n : ℕ} (hp : p.Prime) (h : (4 : ℕ).Full n) (hn : p ∣ n) :
    p^4 ∣ n := by
  by_cases hz : n = 0
  · simp [hz]
  exact h p (Nat.mem_primeFactors.mpr ⟨hp, hn, hz⟩)

private theorem odd_pair_test :
    ∀ a b c : Fin 8, a.val % 2 = 1 → b.val % 2 = 1 →
      (a.val * b.val) % 8 = (c.val*c.val) % 8 → (a.val+b.val) % 8 ≠ 0 := by
  decide

/-- Odd integers with square product cannot add to a multiple of eight. -/
theorem odd_square_product_not_dvd_sum {a b : ℕ} (ha : ¬ 2 ∣ a) (hb : ¬ 2 ∣ b)
    (hSq : IsSquare (a*b)) : ¬ 8 ∣ a+b := by
  obtain ⟨c, hc⟩ := hSq
  have ha2 : a%2=1 := by have := Nat.mod_lt a (by decide : 0 < 2); omega
  have hb2 : b%2=1 := by have := Nat.mod_lt b (by decide : 0 < 2); omega
  let A : Fin 8 := ⟨a%8, Nat.mod_lt _ (by decide)⟩
  let B : Fin 8 := ⟨b%8, Nat.mod_lt _ (by decide)⟩
  let C : Fin 8 := ⟨c%8, Nat.mod_lt _ (by decide)⟩
  have hA : A.val%2=1 := by dsimp [A]; rwa [Nat.mod_mod_of_dvd _ (by decide : 2 ∣ 8)]
  have hB : B.val%2=1 := by dsimp [B]; rwa [Nat.mod_mod_of_dvd _ (by decide : 2 ∣ 8)]
  have hC : (A.val*B.val)%8 = (C.val*C.val)%8 := by
    dsimp [A,B,C]
    rw [← Nat.mul_mod, ← Nat.mul_mod, hc]
  intro hn
  apply odd_pair_test A B C hA hB hC
  change (a%8+b%8)%8=0
  rw [← Nat.add_mod]
  exact Nat.dvd_iff_mod_eq_zero.mp hn

/-- The mixed-principal case has an unchanged odd term at the target 8 modulo 16. -/
theorem unchanged_unit_at_two {a b c d : ℕ}
    (ha : (4 : ℕ).Full a) (hb : (4 : ℕ).Full b) (hc : (4 : ℕ).Full c) (hd : (4 : ℕ).Full d)
    (hSq : IsSquare (a*b)) (h : (a+b+c+d)%16=8) :
    ¬ 2 ∣ c ∨ ¬ 2 ∣ d := by
  by_contra! hcd
  have h8 : 8 ∣ a+b+c+d := by omega
  have hc16 : 16 ∣ c := pow_dvd_of_full Nat.prime_two hc hcd.1
  have hd16 : 16 ∣ d := pow_dvd_of_full Nat.prime_two hd hcd.2
  have h8a : 8 ∣ a+b := by omega
  have hab : ¬ 2 ∣ a ∧ ¬ 2 ∣ b := by
    constructor
    · intro hA
      have hB : 2 ∣ b := by omega
      have h16 : 16 ∣ a := pow_dvd_of_full Nat.prime_two ha hA
      have h16' : 16 ∣ b := pow_dvd_of_full Nat.prime_two hb hB
      omega
    · intro hB
      have hA : 2 ∣ a := by omega
      have h16 : 16 ∣ a := pow_dvd_of_full Nat.prime_two ha hA
      have h16' : 16 ∣ b := pow_dvd_of_full Nat.prime_two hb hB
      omega
  exact odd_square_product_not_dvd_sum hab.1 hab.2 hSq h8a

/-- At a valuation-one target, either an unchanged term is a unit or
both of the first two terms are units. -/
theorem units_at_valuation_one {p a b c d : ℕ} (hp : p.Prime)
    (ha : (4 : ℕ).Full a) (hb : (4 : ℕ).Full b)
    (hc : (4 : ℕ).Full c) (hd : (4 : ℕ).Full d)
    (hn : p ∣ a+b+c+d) (hn2 : ¬ p^2 ∣ a+b+c+d) :
    (¬ p ∣ c ∨ ¬ p ∣ d) ∨ (¬ p ∣ a ∧ ¬ p ∣ b) := by
  by_cases hcd : ¬ p ∣ c ∨ ¬ p ∣ d
  · exact Or.inl hcd
  push Not at hcd
  have hAB : p ∣ a+b := (Nat.dvd_add_iff_left hcd.1).mpr
    ((Nat.dvd_add_iff_left hcd.2).mpr hn)
  right
  constructor
  · intro hA
    have hB : p ∣ b := (Nat.dvd_add_iff_right hA).mpr hAB
    apply hn2
    have h₄ : p^4 ∣ a+b+c+d := Nat.dvd_add (Nat.dvd_add
      (Nat.dvd_add (pow_dvd_of_full hp ha hA) (pow_dvd_of_full hp hb hB))
      (pow_dvd_of_full hp hc hcd.1)) (pow_dvd_of_full hp hd hcd.2)
    exact (pow_dvd_pow p (by decide : 2 ≤ 4)).trans h₄
  · intro hB
    have hA : p ∣ a := (Nat.dvd_add_iff_left hB).mpr hAB
    apply hn2
    have h₄ : p^4 ∣ a+b+c+d := Nat.dvd_add (Nat.dvd_add
      (Nat.dvd_add (pow_dvd_of_full hp ha hA) (pow_dvd_of_full hp hb hB))
      (pow_dvd_of_full hp hc hcd.1)) (pow_dvd_of_full hp hd hcd.2)
    exact (pow_dvd_pow p (by decide : 2 ≤ 4)).trans h₄

private theorem square_of_even_factorization {n : ℕ} (hn : n ≠ 0)
    (h : ∀ p, 2 ∣ n.factorization p) : IsSquare n := by
  let f := n.factorization.mapRange (fun v => v/2) (by decide)
  have hf (p : ℕ) : f p = n.factorization p/2 := by simp [f]
  have hle : f ≤ n.factorization := fun p => by rw [hf]; exact Nat.div_le_self _ _
  let m := f.prod (· ^ ·)
  have hm : m ≠ 0 := fun hz => hn ((by simpa [m, hz] using Nat.prod_pow_dvd_of_le_factorization hle) : n = 0)
  have hmf : m.factorization = f := Nat.factorization_prod_pow_eq_self_of_le_factorization hle
  refine ⟨m, ?_⟩
  apply Nat.eq_of_factorization_eq hn (Nat.mul_ne_zero hm hm)
  intro p
  rw [Nat.factorization_mul hm hm, Finsupp.add_apply, hmf, hf]
  have he := Nat.mul_div_cancel' (h p)
  omega

private theorem square_of_coprime_square_product {a b : ℕ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : a.Coprime b) (hSq : IsSquare (a*b)) : IsSquare a := by
  obtain ⟨s, hs⟩ := hSq
  have hs0 : s ≠ 0 := fun he => Nat.mul_ne_zero ha hb (by simp [hs, he])
  apply square_of_even_factorization ha
  intro p
  by_cases hp : p.Prime
  · by_cases hpa : p ∣ a
    · have hpb : ¬ p ∣ b := by
        intro hpb
        have hh := Nat.dvd_gcd hpa hpb
        rw [hc.gcd_eq_one] at hh
        exact hp.not_dvd_one hh
      have hf := congrArg (fun n : ℕ => n.factorization p) hs
      simp only [Nat.factorization_mul ha hb, Nat.factorization_mul hs0 hs0, Finsupp.add_apply,
        Nat.factorization_eq_zero_of_not_dvd hpb, add_zero] at hf
      omega
    · simp [Nat.factorization_eq_zero_of_not_dvd hpa]
  · simp [Nat.factorization_eq_zero_of_not_prime a hp]

/-- A positive pair with square product admits a shared positive coefficient
times two squares. We use its gcd as the shared coefficient. -/
theorem common_square_pair {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hs : IsSquare (a*b)) :
    ∃ A s t : ℕ, 0 < A ∧ 0 < s ∧ 0 < t ∧ a = A*s^2 ∧ b = A*t^2 := by
  let A := a.gcd b
  have hA : 0 < A := Nat.gcd_pos_of_pos_left _ ha
  have hea : A*(a/A) = a := Nat.mul_div_cancel' (Nat.gcd_dvd_left a b)
  have heb : A*(b/A) = b := Nat.mul_div_cancel' (Nat.gcd_dvd_right a b)
  have hpa : 0 < a/A := by
    by_contra! h
    rw [Nat.eq_zero_of_le_zero h, mul_zero] at hea
    omega
  have hpb : 0 < b/A := by
    by_contra! h
    rw [Nat.eq_zero_of_le_zero h, mul_zero] at heb
    omega
  have hC : (a/A).Coprime (b/A) := Nat.coprime_div_gcd_div_gcd hA
  have hN : IsSquare ((a/A)*(b/A)) := by
    obtain ⟨c, hc⟩ := hs
    apply Rat.isSquare_natCast_iff.mp
    refine ⟨(c : ℚ)/A, ?_⟩
    push_cast
    have hae : (A : ℚ)*(↑(a/A : ℕ) : ℚ) = a := by exact_mod_cast hea
    have hbe : (A : ℚ)*(↑(b/A : ℕ) : ℚ) = b := by exact_mod_cast heb
    have hce : (a : ℚ)*(b : ℚ) = (c : ℚ)*c := by exact_mod_cast hc
    field_simp
    linear_combination hae*((A : ℚ)*(↑(b/A : ℕ) : ℚ)) + hbe*(a : ℚ) + hce
  obtain ⟨s, hs'⟩ := square_of_coprime_square_product hpa.ne' hpb.ne' hC hN
  obtain ⟨t, ht'⟩ := square_of_coprime_square_product hpb.ne' hpa.ne' hC.symm
    (by simpa only [mul_comm] using hN)
  refine ⟨A, s, t, hA, ?_, ?_, ?_, ?_⟩
  · by_contra! h
    apply hpa.ne'
    simpa only [Nat.eq_zero_of_le_zero h, Nat.zero_mul] using hs'
  · by_contra! h
    apply hpb.ne'
    simpa only [Nat.eq_zero_of_le_zero h, Nat.zero_mul] using ht'
  · rw [pow_two, ← hs', hea]
  · rw [pow_two, ← ht', heb]

/-- A principal mixed character gives the square determinant of the
quadratic form obtained by completing a square. -/
theorem mixed_principal_compression {a b c d w : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h : a*b^3*c^2*d^2 = 4*w^4) :
    ∃ A s t : ℕ, 0 < A ∧ 0 < s ∧ 0 < t ∧
      a = A*s^2 ∧ b = A*t^2 ∧ IsSquare (A*c*d*(2*A*s*t)) := by
  have hab : IsSquare (a*b) := by
    apply Rat.isSquare_natCast_iff.mp
    refine ⟨2*(w : ℚ)^2/((b : ℚ)*c*d), ?_⟩
    have he : (a : ℚ)*(b : ℚ)^3*(c : ℚ)^2*(d : ℚ)^2 = 4*(w : ℚ)^4 := by exact_mod_cast h
    push_cast
    field_simp
    linear_combination he
  obtain ⟨A, s, t, hA, hs, ht, ha', hb'⟩ := common_square_pair ha hb hab
  refine ⟨A, s, t, hA, hs, ht, ha', hb', ?_⟩
  have he : (A^2*s*t^3*c*d)^2 = (2*w^2)^2 := by
    rw [ha', hb'] at h
    linear_combination h
  have hroot : A^2*s*t^3*c*d = 2*w^2 :=
    (Nat.pow_left_inj (by decide : (2 : ℕ) ≠ 0)).mp he
  apply Rat.isSquare_natCast_iff.mp
  refine ⟨2*(w : ℚ)/t, ?_⟩
  have hR : (A : ℚ)^2*s*(t : ℚ)^3*c*d = 2*(w : ℚ)^2 := by exact_mod_cast hroot
  push_cast
  field_simp
  linear_combination hR

theorem completion_identity (A s t c d x y z w : ℤ) :
    (A*s^2)*x^4 + (A*t^2)*y^4 + c*z^4 + d*w^4 =
      A*(s*x^2-t*y^2)^2 + c*(z^2)^2 + d*(w^2)^2 + (2*A*s*t)*(x*y)^2 := by
  ring

end Erdos940QuarticElimination


namespace Erdos940QuarticReciprocity

open ZMod

/-- The sign at 2 for the pair of negative slots -k and -2^e*l,
where the two odd parts k and l are positive. -/
private def twoSign (k l e : ℕ) : ℤ :=
  (if k % 4 = 1 ∧ l % 4 = 1 then -1 else 1) *
    (if k % 8 = 3 ∨ k % 8 = 5 then -1 else 1)^e

private def squareResidue (i : Fin 3) : ℕ := if i.val = 2 then 4 else i.val

private theorem square_residue_test :
    ∀ n : Fin 8, ∃ i : Fin 3, (n.val^2)%8 = squareResidue i := by decide

private theorem square_residue (n : ℕ) :
    ∃ i : Fin 3, (n^2)%8 = squareResidue i := by
  obtain ⟨i,hi⟩ := square_residue_test ⟨n%8, Nat.mod_lt _ (by decide)⟩
  refine ⟨i, ?_⟩
  change ((n%8)^2)%8 = _ at hi
  rwa [← Nat.pow_mod] at hi

private theorem odd_square_test :
    ∀ n : Fin 8, n.val%2=1 → (n.val^2)%8=1 := by decide

private theorem odd_square (n : ℕ) (hn : Odd n) : (n^2)%8=1 := by
  have ho : (n%8)%2=1 := by
    rw [Nat.mod_mod_of_dvd _ (by decide : 2 ∣ 8)]
    exact Nat.odd_iff.mp hn
  have h := odd_square_test ⟨n%8,Nat.mod_lt _ (by decide)⟩ ho
  change ((n%8)^2)%8 = 1 at h
  rwa [← Nat.pow_mod] at h

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem two_test :
    ∀ (k l : Fin 8) (e : Fin 2) (b c d : Fin 3),
      k.val%2=1 → l.val%2=1 →
      (1+k.val*squareResidue b+2^e.val*l.val*squareResidue c+
        2^e.val*k.val*l.val*squareResidue d)%8=0 →
      twoSign k.val l.val e.val = 1 := by
  decide

/-- A zero modulo 8 with an odd first coordinate forces the sign at 2 to be +1. -/
theorem twoSign_of_congruence {k l e a b c d : ℕ} (hk : Odd k) (hl : Odd l) (he : e < 2)
    (ha : Odd a)
    (h : (a^2+k*b^2+2^e*l*c^2+2^e*k*l*d^2)%8=0) : twoSign k l e = 1 := by
  obtain ⟨B,hB⟩ := square_residue b
  obtain ⟨C,hC⟩ := square_residue c
  obtain ⟨D,hD⟩ := square_residue d
  have hk' : (k%8)%2=1 := by
    rw [Nat.mod_mod_of_dvd _ (by decide : 2 ∣ 8)]
    exact Nat.odd_iff.mp hk
  have hl' : (l%8)%2=1 := by
    rw [Nat.mod_mod_of_dvd _ (by decide : 2 ∣ 8)]
    exact Nat.odd_iff.mp hl
  have hy : (1+(k%8)*squareResidue B+2^e*(l%8)*squareResidue C+
      2^e*(k%8)*(l%8)*squareResidue D)%8=0 := by
    have hc : a^2+k*b^2+2^e*l*c^2+2^e*k*l*d^2 ≡
        1+(k%8)*squareResidue B+2^e*(l%8)*squareResidue C+
          2^e*(k%8)*(l%8)*squareResidue D [MOD 8] := by
      have ha' : a^2 ≡ 1 [MOD 8] := (odd_square a ha).trans (by decide : 1 = 1%8)
      have hk8 : k ≡ k%8 [MOD 8] := (Nat.mod_mod _ _).symm
      have hl8 : l ≡ l%8 [MOD 8] := (Nat.mod_mod _ _).symm
      have hb' : b^2 ≡ squareResidue B [MOD 8] := hB.trans (by fin_cases B <;> decide)
      have hc' : c^2 ≡ squareResidue C [MOD 8] := hC.trans (by fin_cases C <;> decide)
      have hd' : d^2 ≡ squareResidue D [MOD 8] := hD.trans (by fin_cases D <;> decide)
      exact ((ha'.add (hk8.mul hb')).add ((hl8.mul_left (2^e)).mul hc')).add
        (((hk8.mul_left (2^e)).mul hl8).mul hd')
    exact Eq.trans (Nat.ModEq.symm hc : _ % 8 = _ % 8) h
  have hs := two_test ⟨k%8,Nat.mod_lt _ (by decide)⟩ ⟨l%8,Nat.mod_lt _ (by decide)⟩
    ⟨e,he⟩ B C D hk' hl' hy
  change twoSign (k%8) (l%8) e = 1 at hs
  simpa [twoSign, Nat.mod_mod, Nat.mod_mod_of_dvd _ (by decide : 4 ∣ 8)] using hs

private theorem qrSign_eq_if {a b : ℕ} (ha : Odd a) (hb : Odd b) :
    qrSign a b = if a%4=3 ∧ b%4=3 then -1 else 1 := by
  unfold qrSign
  rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp ha) with hA | hA
  · simp [χ₄_nat_one_mod_four hA, hA, jacobiSym.one_left]
  · rw [χ₄_nat_three_mod_four hA, jacobiSym.at_neg_one hb]
    rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hb) with hB | hB
    · simp [χ₄_nat_one_mod_four hB, hB]
    · simp [χ₄_nat_three_mod_four hB, hA, hB]

private theorem jacobi_pair {a b : ℕ} (ha : Odd a) (hb : Odd b) (h : a.Coprime b) :
    jacobiSym a b * jacobiSym b a = qrSign a b := by
  have hSq := jacobiSym.sq_one (a := (b : ℤ)) (b := a) (by
    rw [Int.gcd_natCast_natCast]
    exact h.symm)
  rw [jacobiSym.quadratic_reciprocity' ha hb, qrSign.symm hb ha, mul_assoc, ← pow_two, hSq, mul_one]

private theorem odd_reciprocity_sign {g u v : ℕ} (hg : Odd g) (hu : Odd u) (hv : Odd v) :
    χ₄ g * χ₄ u * χ₄ v * (qrSign g u * qrSign g v * qrSign u v) =
      -(if (g*u)%4=1 ∧ (g*v)%4=1 then (-1 : ℤ) else 1) := by
  rw [qrSign_eq_if hg hu, qrSign_eq_if hg hv, qrSign_eq_if hu hv]
  rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hg) with hG | hG <;>
    rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hu) with hU | hU <;>
    rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hv) with hV | hV <;>
    rw [Nat.mul_mod g u 4, Nat.mul_mod g v 4] <;>
    rw [χ₄_nat_eq_if_mod_four, χ₄_nat_eq_if_mod_four, χ₄_nat_eq_if_mod_four] <;>
    norm_num [hG,hU,hV, Nat.odd_iff.mp hg, Nat.odd_iff.mp hu, Nat.odd_iff.mp hv]

/-- The three odd Jacobi factors for the negative slots
-(g*u) and -(2^e*g*v) multiply to the negative of their sign at 2. -/
theorem odd_place_product {g u v e : ℕ} (hg : Odd g) (hu : Odd u) (hv : Odd v)
    (hgu : g.Coprime u) (hgv : g.Coprime v) (huv : u.Coprime v) :
    jacobiSym (-((2 : ℤ)^e*g*v)) u *
      jacobiSym (-(g*(u : ℤ))) v *
      jacobiSym (-((2 : ℤ)^e*u*v)) g = -twoSign (g*u) (g*v) e := by
  rw [jacobiSym.neg _ hu, jacobiSym.neg _ hv, jacobiSym.neg _ hg]
  simp only [jacobiSym.mul_left, jacobiSym.pow_left, jacobiSym.at_two hu, jacobiSym.at_two hg]
  calc
    _ = χ₄ g * χ₄ u * χ₄ v *
        ((jacobiSym g u * jacobiSym u g) * (jacobiSym g v * jacobiSym v g) *
          (jacobiSym u v * jacobiSym v u)) * (χ₈ g * χ₈ u)^e := by
      rw [mul_pow]
      ring
    _ = _ := by
      have hOdd := Nat.odd_iff.mp (hg.mul hu)
      have hEight : χ₈ (↑(g*u) : ZMod 8) =
          if (g*u)%8=3 ∨ (g*u)%8=5 then -1 else 1 := by
        rw [χ₈_nat_eq_if_mod_eight, if_neg (by omega)]
        have h : ((g*u)%8)%2=1 := by
          rw [Nat.mod_mod_of_dvd _ (by decide : 2 ∣ 8)]
          exact hOdd
        have hlt : (g*u)%8 < 8 := Nat.mod_lt _ (by decide)
        split <;> split <;> simp_all <;> omega
      rw [jacobi_pair hg hu hgu, jacobi_pair hg hv hgv, jacobi_pair hu hv huv,
        odd_reciprocity_sign hg hu hv, ← map_mul, ← Nat.cast_mul, hEight, neg_mul, twoSign]


/-- A diagonal quadratic form has a zero at which one coefficient times
its corresponding coordinate is nonzero in the residue field. -/
private def activeZero (a b c d p : ℕ) : Prop :=
  ∃ x y z w : ZMod p,
    (a : ZMod p)*x^2+b*y^2+c*z^2+d*w^2 = 0 ∧
    ((a : ZMod p)*x ≠ 0 ∨ (b : ZMod p)*y ≠ 0 ∨
      (c : ZMod p)*z ≠ 0 ∨ (d : ZMod p)*w ≠ 0)

private theorem paired_divisibility {p a b k t : ℕ} (hp : p.Prime)
    (ha : Squarefree a) (hb : Squarefree b) (hk : ¬p ∣ k) (h : a*b = k*t^2) :
    (p ∣ a) ↔ p ∣ b := by
  have ht : t ≠ 0 := fun h0 => (mul_ne_zero ha.ne_zero hb.ne_zero) (by simp [h, h0])
  have hkk : k ≠ 0 := fun h0 => hk (h0 ▸ dvd_zero p)
  have hf := congrArg (fun n : ℕ => n.factorization p) h
  simp only [Nat.factorization_mul ha.ne_zero hb.ne_zero,
     Nat.factorization_mul hkk (pow_ne_zero _ ht), Nat.factorization_pow, Finsupp.add_apply,
     Finsupp.nsmul_apply, nsmul_eq_mul, Nat.factorization_eq_zero_of_not_dvd hk, zero_add] at hf
  have h₁ := ha.natFactorization_le_one p
  have h₂ := hb.natFactorization_le_one p
  rw [hp.dvd_iff_one_le_factorization ha.ne_zero, hp.dvd_iff_one_le_factorization hb.ne_zero]
  omega

private theorem binary_squareclass {p a b k t : ℕ} [Fact p.Prime]
    (ha : (a : ZMod p) ≠ 0) (hb : (b : ZMod p) ≠ 0)
    (hk : ¬p ∣ k) (h : a*b = k*t^2)
    {x y : ZMod p} (hz : (a : ZMod p)*x^2 + b*y^2 = 0) (hxy : x ≠ 0 ∨ y ≠ 0) :
    jacobiSym (-(k : ℤ)) p = 1 := by
  have he : (a : ZMod p)*(b : ZMod p) = (k : ZMod p)*(t : ZMod p)^2 := by
    simpa only [Nat.cast_mul, Nat.cast_pow] using congrArg (fun n : ℕ => (n : ZMod p)) h
  have hnK : (k : ZMod p) ≠ 0 := fun h0 => hk ((ZMod.natCast_eq_zero_iff _ _).mp h0)
  have hnT : (t : ZMod p) ≠ 0 := by
    intro h0
    exact mul_ne_zero ha hb (by simpa [h0] using he)
  have hnY : y ≠ 0 := by
    intro h0
    have hx : x ≠ 0 := hxy.resolve_right (fun hh => hh h0)
    exact mul_ne_zero ha (pow_ne_zero _ hx) (by simpa only [h0, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero, add_zero] using hz)
  rw [← jacobiSym.legendreSym.to_jacobiSym]
  change quadraticChar (ZMod p) ((-(k : ℤ) : ℤ) : ZMod p) = 1
  rw [Int.cast_neg, Int.cast_natCast]
  apply (quadraticChar_one_iff_isSquare (neg_ne_zero.mpr hnK)).2
  refine ⟨((a : ZMod p)*x)/(t*y), ?_⟩
  rw [← pow_two]
  field_simp
  linear_combination -(a : ZMod p)*hz + y^2*he

private theorem jacobi_of_active_pair {p a b c d k s t : ℕ} [Fact p.Prime]
    (ha : Squarefree a) (hb : Squarefree b) (hc : Squarefree c) (hd : Squarefree d)
    (hk : ¬ p ∣ k) (h₁ : a*b=k*s^2) (h₂ : c*d=k*t^2) (hCross : p ∣ a*c)
    (hl : activeZero a b c d p) :
    jacobiSym (-(k : ℤ)) p = 1 := by
  have hp : p.Prime := Fact.out
  have hab := paired_divisibility hp ha hb hk h₁
  have hcd := paired_divisibility hp hc hd hk h₂
  obtain ⟨x,y,z,w,hSum,hActive⟩ := hl
  rcases hp.dvd_mul.mp hCross with hA | hC
  · have az : (a : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hA
    have bz : (b : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr (hab.mp hA)
    simp only [az,bz,zero_mul,zero_add,ne_self_iff_false,false_or] at hSum hActive
    have hCN : ¬p ∣ c := by
      intro h
      have ec : (c : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr h
      have ed : (d : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr (hcd.mp h)
      simp [ec,ed] at hActive
    have hDN := fun h => hCN (hcd.mpr h)
    have hZ : z ≠ 0 ∨ w ≠ 0 :=
      hActive.imp (fun h e => h (by rw [e,mul_zero])) (fun h e => h (by rw [e,mul_zero]))
    exact binary_squareclass ((ZMod.natCast_eq_zero_iff _ _).not.mpr hCN)
      ((ZMod.natCast_eq_zero_iff _ _).not.mpr hDN) hk h₂ hSum hZ
  · have cz : (c : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hC
    have dz : (d : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr (hcd.mp hC)
    simp only [cz,dz,zero_mul,add_zero,ne_self_iff_false,or_false] at hSum hActive
    have hAN : ¬p ∣ a := by
      intro h
      have ea : (a : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr h
      have eb : (b : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr (hab.mp h)
      simp [ea,eb] at hActive
    have hBN := fun h => hAN (hab.mpr h)
    have hX : x ≠ 0 ∨ y ≠ 0 :=
      hActive.imp (fun h e => h (by rw [e,mul_zero])) (fun h e => h (by rw [e,mul_zero]))
    exact binary_squareclass ((ZMod.natCast_eq_zero_iff _ _).not.mpr hAN)
      ((ZMod.natCast_eq_zero_iff _ _).not.mpr hBN) hk h₁ hSum hX

private theorem jacobi_one_of_prime_divisors {a : ℤ} {b : ℕ}
    (h : ∀ p : ℕ, p.Prime → p ∣ b → jacobiSym a p = 1) : jacobiSym a b = 1 := by
  by_cases hb : b = 0
  · simp [hb]
  have hf (p) (hp : p ∈ b.primeFactorsList) : p ≠ 0 :=
    (Nat.pos_of_mem_primeFactorsList hp).ne'
  rw [← Nat.prod_primeFactorsList hb, jacobiSym.list_prod_right hf]
  apply List.prod_eq_one
  intro j hj
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hj
  exact h p (Nat.prime_of_mem_primeFactorsList hp) (Nat.dvd_of_mem_primeFactorsList hp)

private structure SquarePairs (a b c d g u v e : ℕ) : Prop where
  ab : ∃ r, a*b = (g*u)*r^2
  cd : ∃ r, c*d = (g*u)*r^2
  ac : ∃ r, a*c = (2^e*g*v)*r^2
  bd : ∃ r, b*d = (2^e*g*v)*r^2
  ad : ∃ r, a*d = (2^e*u*v)*r^2
  bc : ∃ r, b*c = (2^e*u*v)*r^2

private theorem activeZero_acbd {a b c d p : ℕ} (h : activeZero a b c d p) :
    activeZero a c b d p := by
  obtain ⟨x,y,z,w,he,ha⟩ := h
  refine ⟨x,z,y,w,?_,?_⟩
  · linear_combination he
  · tauto

private theorem activeZero_adbc {a b c d p : ℕ} (h : activeZero a b c d p) :
    activeZero a d b c p := by
  obtain ⟨x,y,z,w,he,ha⟩ := h
  refine ⟨x,w,y,z,?_,?_⟩
  · linear_combination he
  · tauto

private theorem prime_not_dvd_coprime {p a b : ℕ} (hp : p.Prime) (h : a.Coprime b)
    (hd : p ∣ a) : ¬p ∣ b := by
  intro hdb
  have hh := Nat.dvd_gcd hd hdb
  rw [h.gcd_eq_one] at hh
  exact hp.not_dvd_one hh

private theorem jacobi_factors_one {a b c d g u v e : ℕ}
    (ha : Squarefree a) (hb : Squarefree b) (hc : Squarefree c) (hd : Squarefree d)
    (hg : Odd g) (hu : Odd u) (hv : Odd v)
    (hgu : g.Coprime u) (hgv : g.Coprime v) (huv : u.Coprime v)
    (hPairs : SquarePairs a b c d g u v e)
    (hLocal : ∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ a*b*c*d → activeZero a b c d p) :
    jacobiSym (-((2 : ℤ)^e*g*v)) u *
      jacobiSym (-(g*(u : ℤ))) v *
      jacobiSym (-((2 : ℤ)^e*u*v)) g = 1 := by
  obtain ⟨⟨r,hab⟩,⟨s,hcd⟩,⟨t,hac⟩,⟨j,hbd⟩,⟨k,had⟩,⟨m,hbc⟩⟩ := hPairs
  have huJ : jacobiSym (-(↑(2^e*g*v : ℕ) : ℤ)) u = 1 := by
    apply jacobi_one_of_prime_divisors
    intro p hp hpD
    let : Fact p.Prime := ⟨hp⟩
    have hp2 := hu.ne_two_of_dvd_nat hpD
    have hn2 : ¬p ∣ 2 := fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
    have hN : ¬p ∣ 2^e*g*v := by
      simp only [hp.dvd_mul]
      exact not_or.mpr ⟨not_or.mpr ⟨fun h => hn2 (hp.dvd_of_dvd_pow h),
        prime_not_dvd_coprime hp hgu.symm hpD⟩, prime_not_dvd_coprime hp huv hpD⟩
    have hX : p ∣ a*b := by
      rw [hab]
      exact hpD.trans ((dvd_mul_left u g).trans (dvd_mul_right _ _))
    apply jacobi_of_active_pair ha hc hb hd hN hac hbd hX
    exact activeZero_acbd (hLocal p hp hp2 (hX.trans ((dvd_mul_right _ c).trans (dvd_mul_right _ d))))
  have hvJ : jacobiSym (-(↑(g*u : ℕ) : ℤ)) v = 1 := by
    apply jacobi_one_of_prime_divisors
    intro p hp hpD
    let : Fact p.Prime := ⟨hp⟩
    have hp2 := hv.ne_two_of_dvd_nat hpD
    have hN : ¬p ∣ g*u := by
      simp only [hp.dvd_mul]
      exact not_or.mpr ⟨prime_not_dvd_coprime hp hgv.symm hpD,
        prime_not_dvd_coprime hp huv.symm hpD⟩
    have hX : p ∣ a*c := by
      rw [hac]
      exact hpD.trans ((dvd_mul_left v (2^e*g)).trans (dvd_mul_right _ _))
    apply jacobi_of_active_pair ha hb hc hd hN hab hcd hX
    apply hLocal p hp hp2
    rw [show a*b*c*d = (a*c)*(b*d) by ring]
    exact hX.trans (dvd_mul_right _ _)
  have hgJ : jacobiSym (-(↑(2^e*u*v : ℕ) : ℤ)) g = 1 := by
    apply jacobi_one_of_prime_divisors
    intro p hp hpD
    let : Fact p.Prime := ⟨hp⟩
    have hp2 := hg.ne_two_of_dvd_nat hpD
    have hn2 : ¬p ∣ 2 := fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
    have hN : ¬p ∣ 2^e*u*v := by
      simp only [hp.dvd_mul]
      exact not_or.mpr ⟨not_or.mpr ⟨fun h => hn2 (hp.dvd_of_dvd_pow h),
        prime_not_dvd_coprime hp hgu hpD⟩, prime_not_dvd_coprime hp hgv hpD⟩
    have hX : p ∣ a*b := by
      rw [hab]
      exact hpD.trans ((dvd_mul_right g u).trans (dvd_mul_right _ _))
    apply jacobi_of_active_pair ha hd hb hc hN had hbc hX
    exact activeZero_adbc (hLocal p hp hp2 (hX.trans ((dvd_mul_right _ c).trans (dvd_mul_right _ d))))
  push_cast at huJ hvJ hgJ
  rw [huJ,hvJ,hgJ]
  norm_num

private theorem paired_two_sign {a b c d g u v e x y z w : ℕ}
    (ha : Odd a) (hx : Odd x) (hg : Odd g) (hu : Odd u) (hv : Odd v) (he : e < 2)
    (hPairs : SquarePairs a b c d g u v e)
    (h : (a*x^2+b*y^2+c*z^2+d*w^2)%8 = 0) :
    twoSign (g*u) (g*v) e = 1 := by
  obtain ⟨r,hab⟩ := hPairs.ab
  obtain ⟨s,hac⟩ := hPairs.ac
  obtain ⟨t,had⟩ := hPairs.ad
  have hcon : g^2 ≡ 1 [MOD 8] := (odd_square g hg).trans (by decide : 1 = 1%8)
  have hF : a*(a*x^2+b*y^2+c*z^2+d*w^2) =
      (a*x)^2+(g*u)*(r*y)^2+2^e*(g*v)*(s*z)^2+(2^e*u*v)*(t*w)^2 := by
    calc
      _ = (a*x)^2 + (a*b)*y^2 + (a*c)*z^2 + (a*d)*w^2 := by ring
      _ = _ := by rw [hab,hac,had]; ring
  have hZ : (a*(a*x^2+b*y^2+c*z^2+d*w^2))%8 = 0 := by
    rw [Nat.mul_mod, h, mul_zero, Nat.zero_mod]
  rw [hF] at hZ
  have hEq : (2^e*(g*u)*(g*v)*(t*w)^2) ≡ (2^e*u*v)*(t*w)^2 [MOD 8] := by
    have hh := hcon.mul_left ((2^e*u*v)*(t*w)^2)
    convert hh using 1 <;> ring
  have hN : ((a*x)^2+(g*u)*(r*y)^2+2^e*(g*v)*(s*z)^2+
      2^e*(g*u)*(g*v)*(t*w)^2)%8=0 :=
    Eq.trans (hEq.add_left _ : _ % 8 = _ % 8) hZ
  exact twoSign_of_congruence (hg.mul hu) (hg.mul hv) he (ha.mul hx) hN

private theorem no_active_zeros_of_square_pairs {a b c d g u v e x y z w : ℕ}
    (ha : Squarefree a) (hb : Squarefree b) (hc : Squarefree c) (hd : Squarefree d)
    (ha2 : Odd a) (hx : Odd x)
    (hg : Odd g) (hu : Odd u) (hv : Odd v) (he : e < 2)
    (hgu : g.Coprime u) (hgv : g.Coprime v) (huv : u.Coprime v)
    (hPairs : SquarePairs a b c d g u v e)
    (h₂ : (a*x^2+b*y^2+c*z^2+d*w^2)%8 = 0)
    (hLocal : ∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ a*b*c*d → activeZero a b c d p) :
    False := by
  have hn := odd_place_product (e := e) hg hu hv hgu hgv huv
  rw [paired_two_sign ha2 hx hg hu hv he hPairs h₂,
    jacobi_factors_one ha hb hc hd hg hu hv hgu hgv huv hPairs hLocal] at hn
  norm_num at hn

private theorem exp_of_square_part {n k r : ℕ} (hn : n ≠ 0) (hk : Squarefree k)
    (h : n = k*r^2) (p : ℕ) :
    k.factorization p = n.factorization p%2 := by
  have hr : r ≠ 0 := fun h0 => hn (by simp [h,h0])
  have hEq := congrArg (fun x : ℕ => Nat.factorization x p) h
  simp only [Nat.factorization_mul hk.ne_zero (pow_ne_zero 2 hr), Nat.factorization_pow,
    Finsupp.add_apply, Finsupp.nsmul_apply, nsmul_eq_mul] at hEq
  have hlt := hk.natFactorization_le_one p
  omega

private theorem exponent_even_square {n : ℕ} (hn : n ≠ 0) (h : IsSquare n) (p : ℕ) :
    n.factorization p%2 = 0 := by
  obtain ⟨k,hk⟩ := h
  have hk0 : k ≠ 0 := fun hz => hn (by simp [hk,hz])
  rw [hk, Nat.factorization_mul hk0 hk0, Finsupp.add_apply]
  omega

private theorem product_exponents {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (p : ℕ) :
    (a*b).factorization p = a.factorization p + b.factorization p := by
  rw [Nat.factorization_mul ha hb, Finsupp.add_apply]

private theorem even_total_exponents {a b c d : ℕ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0)
    (h : IsSquare (a*b*c*d)) (p : ℕ) :
    (a.factorization p+b.factorization p+c.factorization p+d.factorization p)%2=0 := by
  simpa only [product_exponents ha hb, product_exponents (mul_ne_zero ha hb) hc,
    product_exponents (mul_ne_zero (mul_ne_zero ha hb) hc) hd] using
    exponent_even_square (mul_ne_zero (mul_ne_zero (mul_ne_zero ha hb) hc) hd) h p

private theorem matched_pair_square_part {a b c d k r : ℕ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0)
    (hs : IsSquare (a*b*c*d)) (hk : Squarefree k) (h₁ : a*b=k*r^2) :
    ∃ s, c*d=k*s^2 := by
  obtain ⟨j,s,_,_,hJS,hjSq⟩ := Nat.sq_mul_squarefree_of_pos (Nat.pos_of_ne_zero (mul_ne_zero hc hd))
  have hJ : c*d = j*s^2 := by rw [← hJS, mul_comm]
  have hEq : j = k := by
    apply Nat.eq_of_factorization_eq hjSq.ne_zero hk.ne_zero
    intro p
    have hE := even_total_exponents ha hb hc hd hs p
    rw [exp_of_square_part (mul_ne_zero hc hd) hjSq hJ,
      exp_of_square_part (mul_ne_zero ha hb) hk h₁,
      product_exponents hc hd, product_exponents ha hb]
    omega
  exact ⟨s, hEq ▸ hJ⟩

private theorem square_pair_data {a b c d : ℕ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0)
    (ha₂ : Odd a) (hb₂ : Odd b) (hs : IsSquare (a*b*c*d)) :
    ∃ g u v e : ℕ, Odd g ∧ Odd u ∧ Odd v ∧ e < 2 ∧
      g.Coprime u ∧ g.Coprime v ∧ u.Coprime v ∧ SquarePairs a b c d g u v e := by
  obtain ⟨X,r,hX,_,hXR,hXS⟩ := Nat.sq_mul_squarefree_of_pos (Nat.pos_of_ne_zero (mul_ne_zero ha hb))
  obtain ⟨Y,s,hY,_,hYS,hYSF⟩ := Nat.sq_mul_squarefree_of_pos (Nat.pos_of_ne_zero (mul_ne_zero ha hc))
  obtain ⟨Z,t,_,_,hZT,hZSF⟩ := Nat.sq_mul_squarefree_of_pos (Nat.pos_of_ne_zero (mul_ne_zero ha hd))
  have hab : a*b=X*r^2 := by rw [← hXR,mul_comm]
  have hac : a*c=Y*s^2 := by rw [← hYS,mul_comm]
  have had : a*d=Z*t^2 := by rw [← hZT,mul_comm]
  obtain ⟨r',hcd⟩ := matched_pair_square_part ha hb hc hd hs hXS hab
  obtain ⟨s',hbd⟩ := matched_pair_square_part ha hc hb hd
    (by rwa [show a*c*b*d = a*b*c*d by ring]) hYSF hac
  obtain ⟨t',hbc⟩ := matched_pair_square_part ha hd hb hc
    (by rwa [show a*d*b*c = a*b*c*d by ring]) hZSF had
  let g := X.gcd Y
  let u := X/g
  let W := Y/g
  have hg : 0 < g := Nat.gcd_pos_of_pos_left Y hX
  have heX : X = g*u := (Nat.mul_div_cancel' (Nat.gcd_dvd_left X Y)).symm
  have heY : Y = g*W := (Nat.mul_div_cancel' (Nat.gcd_dvd_right X Y)).symm
  have hu : u ≠ 0 := fun h0 => hX.ne' (by simp [heX,h0])
  have hW : W ≠ 0 := fun h0 => hY.ne' (by simp [heY,h0])
  have hA := Nat.squarefree_mul_iff.mp (heX ▸ hXS)
  have hB := Nat.squarefree_mul_iff.mp (heY ▸ hYSF)
  have hUW : u.Coprime W := Nat.coprime_div_gcd_div_gcd hg
  have hTailSq := (Nat.squarefree_mul hUW).mpr ⟨hA.2.2,hB.2.2⟩
  have hXZ : Z = u*W := by
    apply Nat.eq_of_factorization_eq hZSF.ne_zero hTailSq.ne_zero
    intro p
    have hXmod := exp_of_square_part (mul_ne_zero ha hb) hXS hab p
    have hYmod := exp_of_square_part (mul_ne_zero ha hc) hYSF hac p
    have hZmod := exp_of_square_part (mul_ne_zero ha hd) hZSF had p
    rw [heX, product_exponents hg.ne' hu, product_exponents ha hb] at hXmod
    rw [heY, product_exponents hg.ne' hW, product_exponents ha hc] at hYmod
    rw [product_exponents ha hd] at hZmod
    rw [product_exponents hu hW]
    have hBound := hTailSq.natFactorization_le_one p
    rw [product_exponents hu hW] at hBound
    have hEven := even_total_exponents ha hb hc hd hs p
    omega
  have hxOdd : Odd X := by
    have hR := ha₂.mul hb₂
    rw [hab] at hR
    exact (Nat.odd_mul.mp hR).1
  have hguOdd := Nat.odd_mul.mp (heX ▸ hxOdd)
  obtain ⟨e,v,hv,hE⟩ := Nat.exists_eq_two_pow_mul_odd hW
  have he : e < 2 := by
    by_contra! hn
    have hD : 2*2 ∣ W := by
      rw [hE, ← pow_two]
      exact (pow_dvd_pow 2 hn).trans (dvd_mul_right _ _)
    exact (Nat.squarefree_iff_prime_squarefree.mp hB.2.2 2 Nat.prime_two) hD
  have hvD : v ∣ W := by rw [hE]; exact dvd_mul_left _ _
  refine ⟨g,u,v,e,hguOdd.1,hguOdd.2,hv,he,hA.1,
    hB.1.of_dvd_right hvD, hUW.of_dvd_right hvD, ?_⟩
  have hy' : Y = 2^e*g*v := by rw [heY,hE]; ring
  have hz' : Z = 2^e*u*v := by rw [hXZ,hE]; ring
  exact ⟨⟨r,heX ▸ hab⟩,⟨r',heX ▸ hcd⟩,⟨s,hy' ▸ hac⟩,⟨s',hy' ▸ hbd⟩,
    ⟨t,hz' ▸ had⟩,⟨t',hz' ▸ hbc⟩⟩

/-- A squarefree positive diagonal form of square determinant cannot have active
zeros at every odd coefficient prime and a zero modulo eight with an odd
first coordinate and two odd leading coefficients. -/
theorem no_active_zeros_squarefree {a b c d x y z w : ℕ}
    (ha : Squarefree a) (hb : Squarefree b) (hc : Squarefree c) (hd : Squarefree d)
    (ha₂ : Odd a) (hb₂ : Odd b) (hx : Odd x)
    (hs : IsSquare (a*b*c*d))
    (h₂ : (a*x^2+b*y^2+c*z^2+d*w^2)%8=0)
    (hLocal : ∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ a*b*c*d → activeZero a b c d p) :
    False := by
  obtain ⟨g,u,v,e,hg,hu,hv,he,hgu,hgv,huv,hPairs⟩ :=
    square_pair_data ha.ne_zero hb.ne_zero hc.ne_zero hd.ne_zero ha₂ hb₂ hs
  exact no_active_zeros_of_square_pairs ha hb hc hd ha₂ hx hg hu hv he hgu hgv huv hPairs h₂ hLocal

/-- The modulus-eight zero that is needed at 2, with an odd coefficient and
coordinate in at least one slot. -/
private def activeEight (a b c d : ℕ) : Prop :=
  ∃ x y z w : ℕ, (a*x^2+b*y^2+c*z^2+d*w^2)%8=0 ∧
    (Odd (a*x) ∨ Odd (b*y) ∨ Odd (c*z) ∨ Odd (d*w))

/-- Only odd primes dividing the determinant need to be checked. -/
private def activeAtOddDivisors (a b c d : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ a*b*c*d → activeZero a b c d p

private theorem activeAtOddDivisors_acbd {a b c d : ℕ} (h : activeAtOddDivisors a b c d) :
    activeAtOddDivisors a c b d := by
  intro p hp h₂ hd
  exact activeZero_acbd (h p hp h₂ (by rwa [show a*b*c*d = a*c*b*d by ring]))

private theorem activeAtOddDivisors_adbc {a b c d : ℕ} (h : activeAtOddDivisors a b c d) :
    activeAtOddDivisors a d b c := by
  intro p hp h₂ hd
  exact activeZero_adbc (h p hp h₂ (by rwa [show a*b*c*d = a*d*b*c by ring]))

private theorem activeAtOddDivisors_bacd {a b c d : ℕ} (h : activeAtOddDivisors a b c d) :
    activeAtOddDivisors b a c d := by
  intro p hp h₂ hd
  obtain ⟨x,y,z,w,he,ha⟩ := h p hp h₂ (by rwa [mul_comm a b])
  refine ⟨y,x,z,w,?_,?_⟩
  · linear_combination he
  · tauto

private theorem no_squarefree_zero_first {a b c d x y z w : ℕ}
    (ha : Squarefree a) (hb : Squarefree b) (hc : Squarefree c) (hd : Squarefree d)
    (hax : Odd (a*x)) (hSq : IsSquare (a*b*c*d))
    (hEight : (a*x^2+b*y^2+c*z^2+d*w^2)%8=0)
    (hLocal : activeAtOddDivisors a b c d) :
    False := by
  obtain ⟨haOdd,hxOdd⟩ := Nat.odd_mul.mp hax
  by_cases hbOdd : Odd b
  · exact no_active_zeros_squarefree ha hb hc hd haOdd hbOdd hxOdd hSq hEight hLocal
  by_cases hcOdd : Odd c
  · apply no_active_zeros_squarefree ha hc hb hd haOdd hcOdd hxOdd (y := z) (z := y) (w := w)
    · rwa [show a*c*b*d = a*b*c*d by ring]
    · rwa [show a*x^2+c*z^2+b*y^2+d*w^2 = a*x^2+b*y^2+c*z^2+d*w^2 by ring]
    · exact activeAtOddDivisors_acbd hLocal
  by_cases hdOdd : Odd d
  · apply no_active_zeros_squarefree ha hd hb hc haOdd hdOdd hxOdd (y := w) (z := y) (w := z)
    · rwa [show a*d*b*c = a*b*c*d by ring]
    · rwa [show a*x^2+d*w^2+b*y^2+c*z^2 = a*x^2+b*y^2+c*z^2+d*w^2 by ring]
    · exact activeAtOddDivisors_adbc hLocal
  have oddNotDvd : ¬2 ∣ a := Nat.two_dvd_ne_zero.mpr (Nat.odd_iff.mp haOdd)
  have evenDvd (n : ℕ) (hn : ¬ Odd n) : 2 ∣ n := by
    by_contra! h
    exact hn (Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp h))
  have hE := even_total_exponents ha.ne_zero hb.ne_zero hc.ne_zero hd.ne_zero hSq 2
  rw [Nat.factorization_eq_zero_of_not_dvd oddNotDvd,
    Nat.factorization_eq_one_of_squarefree hb Nat.prime_two (evenDvd _ hbOdd),
    Nat.factorization_eq_one_of_squarefree hc Nat.prime_two (evenDvd _ hcOdd),
    Nat.factorization_eq_one_of_squarefree hd Nat.prime_two (evenDvd _ hdOdd)] at hE
  norm_num at hE

private theorem no_squarefree_active_zeros {a b c d : ℕ}
    (ha : Squarefree a) (hb : Squarefree b) (hc : Squarefree c) (hd : Squarefree d)
    (hSq : IsSquare (a*b*c*d))
    (hEight : activeEight a b c d) (hLocal : activeAtOddDivisors a b c d) :
    False := by
  obtain ⟨x,y,z,w,hZero,hOdd⟩ := hEight
  rcases hOdd with hx | hy | hz | hw
  · exact no_squarefree_zero_first ha hb hc hd hx hSq hZero hLocal
  · apply no_squarefree_zero_first hb ha hc hd hy (y := x) (z := z) (w := w)
    · rwa [show b*a*c*d = a*b*c*d by ring]
    · rwa [show b*y^2+a*x^2+c*z^2+d*w^2 = a*x^2+b*y^2+c*z^2+d*w^2 by ring]
    · exact activeAtOddDivisors_bacd hLocal
  · apply no_squarefree_zero_first hc ha hb hd hz (y := x) (z := y) (w := w)
    · rwa [show c*a*b*d = a*b*c*d by ring]
    · rwa [show c*z^2+a*x^2+b*y^2+d*w^2 = a*x^2+b*y^2+c*z^2+d*w^2 by ring]
    · exact activeAtOddDivisors_bacd (activeAtOddDivisors_acbd hLocal)
  · apply no_squarefree_zero_first hd ha hb hc hw (y := x) (z := y) (w := z)
    · rwa [show d*a*b*c = a*b*c*d by ring]
    · rwa [show d*w^2+a*x^2+b*y^2+c*z^2 = a*x^2+b*y^2+c*z^2+d*w^2 by ring]
    · exact activeAtOddDivisors_bacd (activeAtOddDivisors_adbc hLocal)

private theorem activeZero_remove_squares {a b c d r s t u p : ℕ}
    (h : activeZero (a*r^2) (b*s^2) (c*t^2) (d*u^2) p) :
    activeZero a b c d p := by
  obtain ⟨x,y,z,w,he,ha⟩ := h
  push_cast at he ha
  refine ⟨(r : ZMod p)*x,(s : ZMod p)*y,(t : ZMod p)*z,(u : ZMod p)*w,?_,?_⟩
  · linear_combination he
  · have h' (n k : ℕ) (v : ZMod p) (he : (n : ZMod p)*(k : ZMod p)^2*v ≠ 0) :
        (n : ZMod p)*((k : ZMod p)*v) ≠ 0 := by
      intro hn
      apply he
      calc
        _ = (k : ZMod p)*((n : ZMod p)*((k : ZMod p)*v)) := by ring
        _ = _ := by rw [hn, mul_zero]
    exact ha.imp (h' a r x) (fun h => h.imp (h' b s y) (fun h => h.imp (h' c t z) (h' d u w)))

private theorem activeEight_remove_squares {a b c d r s t u : ℕ}
    (h : activeEight (a*r^2) (b*s^2) (c*t^2) (d*u^2)) :
    activeEight a b c d := by
  obtain ⟨x,y,z,w,he,ha⟩ := h
  refine ⟨r*x,s*y,t*z,u*w,?_,?_⟩
  · convert he using 2; ring
  · have h' (n k v : ℕ) (he : Odd (n*k^2*v)) : Odd (n*(k*v)) := by
      have he' : Odd (k*(n*(k*v))) := by convert he using 1; ring
      exact (Nat.odd_mul.mp he').2
    exact ha.imp (h' a r x) (fun h => h.imp (h' b s y) (fun h => h.imp (h' c t z) (h' d u w)))

/-- Elementary square-determinant obstruction, derived from quadratic
reciprocity and explicit congruences. -/
theorem positive_square_determinant_obstruction {a b c d : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hSq : IsSquare (a*b*c*d))
    (hEight : activeEight a b c d) (hLocal : activeAtOddDivisors a b c d) :
    False := by
  obtain ⟨A,r,_,hr,haS,haF⟩ := Nat.sq_mul_squarefree_of_pos ha
  obtain ⟨B,s,_,hs,hbS,hbF⟩ := Nat.sq_mul_squarefree_of_pos hb
  obtain ⟨C,t,_,ht,hcS,hcF⟩ := Nat.sq_mul_squarefree_of_pos hc
  obtain ⟨D,u,_,hu,hdS,hdF⟩ := Nat.sq_mul_squarefree_of_pos hd
  have habcd : a*b*c*d = (A*B*C*D)*(r*s*t*u)^2 := by
    rw [← haS,← hbS,← hcS,← hdS]
    ring
  have hSq' : IsSquare (A*B*C*D) := by
    apply Rat.isSquare_natCast_iff.mp
    obtain ⟨q,hq⟩ := hSq
    refine ⟨(q : ℚ)/(r*s*t*u), ?_⟩
    have hR : (A : ℚ)*B*C*D*((r : ℚ)*s*t*u)^2 = (q : ℚ)*q := by
      exact_mod_cast habcd.symm.trans hq
    push_cast
    field_simp
    linear_combination hR
  have hEight' : activeEight A B C D := by
    apply activeEight_remove_squares (r := r) (s := s) (t := t) (u := u)
    simpa only [mul_comm A, mul_comm B, mul_comm C, mul_comm D, haS,hbS,hcS,hdS] using hEight
  have hLocal' : activeAtOddDivisors A B C D := by
    intro p hp hp2 hpD
    have hD : p ∣ a*b*c*d := habcd ▸ hpD.trans (dvd_mul_right _ ((r*s*t*u)^2))
    apply activeZero_remove_squares (r := r) (s := s) (t := t) (u := u)
    simpa only [mul_comm A, mul_comm B, mul_comm C, mul_comm D, haS,hbS,hcS,hdS] using
      hLocal p hp hp2 hD
  exact no_squarefree_active_zeros haF hbF hcF hdF hSq' hEight' hLocal'

end Erdos940QuarticReciprocity


namespace Erdos940QuarticElimination

open Erdos940QuarticReciprocity

private theorem full_term (a x : ℕ) (ha : (4 : ℕ).Full a) : (4 : ℕ).Full (a*x^4) := by
  intro p hp
  obtain ⟨hprime,hdiv,_⟩ := Nat.mem_primeFactors.mp hp
  rcases hprime.dvd_mul.mp hdiv with ha' | hx'
  · exact (pow_dvd_of_full hprime ha ha').trans (dvd_mul_right _ _)
  · exact (pow_dvd_pow_of_dvd (hprime.dvd_of_dvd_pow hx') 4).trans (dvd_mul_left _ _)

private theorem square_term_unit {a x p : ℕ} (hp : p.Prime) (h : ¬p ∣ a*x^4) :
    ¬ p ∣ a*x^2 := by
  intro hd
  rcases hp.dvd_mul.mp hd with hA | hX
  · exact h (hA.trans (dvd_mul_right _ _))
  · exact h ((hp.dvd_of_dvd_pow hX).trans (dvd_pow_self _ (by decide : (4 : ℕ) ≠ 0))
      |>.trans (dvd_mul_left _ _))

private theorem unit_mod {a x p : ℕ} (hp : p.Prime) (h : ¬p ∣ a*x^4) :
    (a : ZMod p) * ((x : ZMod p)^2) ≠ 0 := by
  rw [← Nat.cast_pow, ← Nat.cast_mul, ne_eq, ZMod.natCast_eq_zero_iff]
  exact square_term_unit hp h

private theorem unit_odd {a x : ℕ} (h : ¬ 2 ∣ a*x^4) : Odd (a*x^2) :=
  Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp (square_term_unit Nat.prime_two h))

private theorem valuation_one {p n : ℕ} (hp : p.Prime) (hn : n % p^2 = p) :
    p ∣ n ∧ ¬p^2 ∣ n := by
  constructor
  · apply Nat.dvd_iff_mod_eq_zero.mpr
    rw [← Nat.mod_mod_of_dvd n (dvd_pow_self p (by decide : (2 : ℕ) ≠ 0)), hn, Nat.mod_self]
  · intro h
    exact hp.ne_zero (hn.symm.trans (Nat.dvd_iff_mod_eq_zero.mp h))

/-- The congruence system used to test a quartic coefficient tuple. -/
private def hasValuationTargets (a b c d : ℕ) : Prop :=
  (∃ x y z w : ℕ, (a*x^4+b*y^4+c*z^4+d*w^4)%16=8) ∧
  ∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ a*b*c*d →
    ∃ x y z w : ℕ, (a*x^4+b*y^4+c*z^4+d*w^4)%p^2=p

private theorem quartic_odd_unit {a b c d x y z w : ℕ}
    (ha : (4 : ℕ).Full a) (hb : (4 : ℕ).Full b)
    (hc : (4 : ℕ).Full c) (hd : (4 : ℕ).Full d)
    (h : (a*x^4+b*y^4+c*z^4+d*w^4)%16=8) :
    ¬2 ∣ a*x^4 ∨ ¬2 ∣ b*y^4 ∨ ¬2 ∣ c*z^4 ∨ ¬2 ∣ d*w^4 := by
  by_contra! hu
  have hD : 16 ∣ a*x^4+b*y^4+c*z^4+d*w^4 :=
    Nat.dvd_add (Nat.dvd_add (Nat.dvd_add (pow_dvd_of_full Nat.prime_two (full_term a x ha) hu.1)
      (pow_dvd_of_full Nat.prime_two (full_term b y hb) hu.2.1))
      (pow_dvd_of_full Nat.prime_two (full_term c z hc) hu.2.2.1))
      (pow_dvd_of_full Nat.prime_two (full_term d w hd) hu.2.2.2)
  omega

private theorem valuation_targets_square_form {a b c d : ℕ}
    (ha : (4 : ℕ).Full a) (hb : (4 : ℕ).Full b)
    (hc : (4 : ℕ).Full c) (hd : (4 : ℕ).Full d)
    (h : hasValuationTargets a b c d) :
    activeEight a b c d ∧ activeAtOddDivisors a b c d := by
  constructor
  · obtain ⟨x,y,z,w,h₀⟩ := h.1
    have h8 : (a*x^4+b*y^4+c*z^4+d*w^4)%8=0 := by omega
    have hOdd := quartic_odd_unit ha hb hc hd h₀
    exact ⟨x^2,y^2,z^2,w^2,by simpa only [← pow_mul] using h8,
      hOdd.imp unit_odd (fun h => h.imp unit_odd (fun h => h.imp unit_odd unit_odd))⟩
  · intro p hp hp2 hdvd
    obtain ⟨x,y,z,w,h₀⟩ := h.2 p hp hp2 hdvd
    obtain ⟨hDiv,hND⟩ := valuation_one hp h₀
    have hu := units_at_valuation_one hp (full_term a x ha) (full_term b y hb)
      (full_term c z hc) (full_term d w hd) hDiv hND
    refine ⟨(x : ZMod p)^2,(y : ZMod p)^2,(z : ZMod p)^2,(w : ZMod p)^2,?_,?_⟩
    · simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, ← pow_mul] using
        (ZMod.natCast_eq_zero_iff _ _).mpr hDiv
    · rcases hu with (hz | hw) | ⟨hx,_⟩
      · exact Or.inr (Or.inr (Or.inl (unit_mod hp hz)))
      · exact Or.inr (Or.inr (Or.inr (unit_mod hp hw)))
      · exact Or.inl (unit_mod hp hx)

private theorem mixed_principal_compression_rat {a b c d : ℕ} {w : ℚ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h : (a : ℚ)*b^3*c^2*d^2 = 4*w^4) :
    ∃ A s t : ℕ, 0 < A ∧ 0 < s ∧ 0 < t ∧
      a = A*s^2 ∧ b = A*t^2 ∧ IsSquare (A*c*d*(2*A*s*t)) := by
  have hab : IsSquare (a*b) := by
    apply Rat.isSquare_natCast_iff.mp
    refine ⟨2*w^2/((b : ℚ)*c*d), ?_⟩
    push_cast
    field_simp
    linear_combination h
  obtain ⟨A,s,t,hA,hs,ht,ha',hb'⟩ := common_square_pair ha hb hab
  refine ⟨A,s,t,hA,hs,ht,ha',hb',?_⟩
  have hS : ((A : ℚ)^2*s*t^3*c*d)^2 = (2*w^2)^2 := by
    rw [ha',hb'] at h
    push_cast at h
    linear_combination h
  have hE : (A : ℚ)^2*s*t^3*c*d = 2*w^2 := by
    have h₁ : 0 ≤ (A : ℚ)^2*s*t^3*c*d := by positivity
    have h₂ : 0 ≤ (2 : ℚ)*w^2 := by positivity
    exact (pow_left_inj₀ h₁ h₂ (by decide : (2 : ℕ) ≠ 0)).mp hS
  apply Rat.isSquare_natCast_iff.mp
  refine ⟨2*w/t,?_⟩
  push_cast
  field_simp
  linear_combination hE

private def differenceCoordinate (s t x y : ℕ) : ℕ :=
  Int.natAbs ((s : ℤ)*(x : ℤ)^2-(t : ℤ)*(y : ℤ)^2)

private theorem completion_nat (A s t c d x y z w : ℕ) :
    A*(differenceCoordinate s t x y)^2+c*(z^2)^2+d*(w^2)^2+
      (2*A*s*t)*(x*y)^2 = (A*s^2)*x^4+(A*t^2)*y^4+c*z^4+d*w^4 := by
  have he := (completion_identity A s t c d x y z w).symm
  exact_mod_cast (show
    (A : ℤ)*(↑(differenceCoordinate s t x y) : ℤ)^2+c*(z^2)^2+d*(w^2)^2+
      (2*A*s*t)*(x*y)^2 = (A*s^2)*x^4+(A*t^2)*y^4+c*z^4+d*w^4 by
    simpa [differenceCoordinate, Int.natCast_natAbs, sq_abs] using he)

private theorem odd_divisor_of_compression {a b c d A s t p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (heA : a=A*s^2) (heB : b=A*t^2)
    (h : p ∣ A*c*d*(2*A*s*t)) : p ∣ a*b*c*d := by
  have he₂ : ¬p ∣ 2 := fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
  have haA : p ∣ A → p ∣ a := fun h => heA ▸ h.trans (dvd_mul_right _ _)
  have haS : p ∣ s → p ∣ a := fun h => heA ▸
    (h.trans (dvd_pow_self _ (by decide : (2 : ℕ) ≠ 0))).trans (dvd_mul_left _ _)
  have hbT : p ∣ t → p ∣ b := fun h => heB ▸
    (h.trans (dvd_pow_self _ (by decide : (2 : ℕ) ≠ 0))).trans (dvd_mul_left _ _)
  simp only [hp.dvd_mul] at h ⊢
  tauto

private theorem cross_term_unit {p A s t x y : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hA : ¬ p ∣ (A*s^2)*x^4) (hB : ¬ p ∣ (A*t^2)*y^4) :
    (↑(2*A*s*t) : ZMod p) * ((x : ZMod p)*(y : ZMod p)) ≠ 0 := by
  rw [← Nat.cast_mul, ← Nat.cast_mul, ne_eq, ZMod.natCast_eq_zero_iff]
  have he₂ : ¬p ∣ 2 := fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
  have heS : p ∣ s → p ∣ s^2 := fun h => h.trans (dvd_pow_self _ (by decide : (2 : ℕ) ≠ 0))
  have heT : p ∣ t → p ∣ t^2 := fun h => h.trans (dvd_pow_self _ (by decide : (2 : ℕ) ≠ 0))
  have heX : p ∣ x → p ∣ x^4 := fun h => h.trans (dvd_pow_self _ (by decide : (4 : ℕ) ≠ 0))
  have heY : p ∣ y → p ∣ y^4 := fun h => h.trans (dvd_pow_self _ (by decide : (4 : ℕ) ≠ 0))
  simp only [hp.dvd_mul] at hA hB ⊢
  tauto

private theorem valuation_targets_mixed_form {a b c d A s t : ℕ}
    (ha : (4 : ℕ).Full a) (hb : (4 : ℕ).Full b) (hc : (4 : ℕ).Full c) (hd : (4 : ℕ).Full d)
    (heA : a=A*s^2) (heB : b=A*t^2) (h : hasValuationTargets a b c d) :
    activeEight A c d (2*A*s*t) ∧ activeAtOddDivisors A c d (2*A*s*t) := by
  have hQ (x y z w : ℕ) := completion_nat A s t c d x y z w
  simp only [← heA, ← heB] at hQ
  constructor
  · obtain ⟨x,y,z,w,h₀⟩ := h.1
    have h8 : (a*x^4+b*y^4+c*z^4+d*w^4)%8=0 := by omega
    have hSq : IsSquare ((a*x^4)*(b*y^4)) := by
      refine ⟨A*s*t*x^2*y^2,?_⟩
      rw [heA,heB]
      ring
    have hOdd := unchanged_unit_at_two (full_term a x ha) (full_term b y hb)
      (full_term c z hc) (full_term d w hd) hSq h₀
    refine ⟨differenceCoordinate s t x y,z^2,w^2,x*y,?_,?_⟩
    · rw [hQ]
      exact h8
    · exact Or.inr (hOdd.imp unit_odd (fun h => Or.inl (unit_odd h)))
  · intro p hp hp2 hpD
    obtain ⟨x,y,z,w,h₀⟩ := h.2 p hp hp2 (odd_divisor_of_compression hp hp2 heA heB hpD)
    obtain ⟨hDiv,hND⟩ := valuation_one hp h₀
    have hU := units_at_valuation_one hp (full_term a x ha) (full_term b y hb)
      (full_term c z hc) (full_term d w hd) hDiv hND
    refine ⟨(differenceCoordinate s t x y : ZMod p),(z : ZMod p)^2,(w : ZMod p)^2,
      (x : ZMod p)*(y : ZMod p),?_,?_⟩
    · have hv : (((A*(differenceCoordinate s t x y)^2+c*(z^2)^2+d*(w^2)^2+
          (2*A*s*t)*(x*y)^2) : ℕ) : ZMod p) = 0 := by
        rw [hQ]
        exact (ZMod.natCast_eq_zero_iff _ _).mpr hDiv
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow] using hv
    · rcases hU with (hz | hw) | ⟨hx,hy⟩
      · exact Or.inr (Or.inl (unit_mod hp hz))
      · exact Or.inr (Or.inr (Or.inl (unit_mod hp hw)))
      · exact Or.inr (Or.inr (Or.inr (cross_term_unit hp hp2 (heA ▸ hx) (heB ▸ hy))))

/-- The valuation targets eliminate both principal-character coefficient types.
The mixed type is stated using a rational fourth power. -/
theorem excludes_principal_coefficients {a b c d : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (haF : (4 : ℕ).Full a) (hbF : (4 : ℕ).Full b)
    (hcF : (4 : ℕ).Full c) (hdF : (4 : ℕ).Full d)
    (hType : IsSquare (a*b*c*d) ∨ ∃ w : ℚ, (a : ℚ)*b^3*c^2*d^2 = 4*w^4) :
    ¬ hasValuationTargets a b c d := by
  intro h
  rcases hType with hs | ⟨w,hw⟩
  · obtain ⟨h₁,h₂⟩ := valuation_targets_square_form haF hbF hcF hdF h
    exact positive_square_determinant_obstruction ha hb hc hd hs h₁ h₂
  · obtain ⟨A,s,t,hA,hs,ht,heA,heB,hSquare⟩ := mixed_principal_compression_rat ha hb hc hd hw
    obtain ⟨h₁,h₂⟩ := valuation_targets_mixed_form haF hbF hcF hdF heA heB h
    exact positive_square_determinant_obstruction hA hc hd (by positivity) hSquare h₁ h₂

end Erdos940QuarticElimination


namespace Erdos940Quartic

open Finset Erdos940QuarticPrimes Erdos940QuarticPrimeHarmonic Erdos940QuarticElimination

/-- The exceptional coefficient types are precisely the two sources of
a principal character in the regular Euler-product estimate. -/
private def PrincipalType (a : Fin 4 → ℕ) : Prop :=
  IsSquare (∏ i, a i) ∨ ∃ (σ : Equiv.Perm (Fin 4)) (w : ℚ),
    (a (σ 0) : ℚ) * (a (σ 1) : ℚ)^3 * (a (σ 2) : ℚ)^2 * (a (σ 3) : ℚ)^2 = 4*w^4

theorem coefficientProduct_reindex (a : Fin 4 → ℕ) (σ : Equiv.Perm (Fin 4)) :
    (∏ i, a (σ i)) = ∏ i, a i :=
  Fintype.prod_equiv σ _ _ (fun _ => rfl)

private theorem count_reindex {R : Type} [CommRing R] (a : Fin 4 → R) (u : R)
    (σ : Equiv.Perm (Fin 4)) : count (fun i => a (σ i)) u = count a u := by
  let e : (Fin 4 → R) ≃ (Fin 4 → R) :=
    { toFun := fun x i => x (σ.symm i)
      invFun := fun x i => x (σ i)
      left_inv := by intro x; funext i; simp
      right_inv := by intro x; funext i; simp }
  apply Nat.card_congr (e.subtypeEquiv ?_)
  intro x
  have hS : (∑ i, a (σ i) * (x i)^4) = ∑ i, a i * (x (σ.symm i))^4 :=
    Fintype.sum_equiv σ _ _ (fun i => by rw [Equiv.symm_apply_apply])
  change (∑ i, a (σ i) * (x i)^4) = u ↔ (∑ i, a i * (x (σ.symm i))^4) = u
  rw [hS]

private theorem localFactor_reindex (M : ℕ) (a : Fin 4 → ℕ) (u : ℕ)
    (σ : Equiv.Perm (Fin 4)) : localFactor M (fun i => a (σ i)) u = localFactor M a u := by
  unfold localFactor
  rw [count_reindex (fun i => (a i : ZMod M)) (u : ZMod M) σ]

private theorem exists_naturals_mod {M u : ℕ} [NeZero M] (a : Fin 4 → ℕ)
    (h : localFactor M a u ≠ 0) :
    ∃ x : Fin 4 → ℕ, (∑ i, a i * (x i)^4) ≡ u [MOD M] := by
  by_contra! hn
  let S := Solutions (fun i => (a i : ZMod M)) (u : ZMod M)
  let : IsEmpty S := ⟨fun x => by
    apply hn (fun i => (x.val i).val)
    apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
    simpa only [Nat.cast_sum,Nat.cast_mul,Nat.cast_pow,ZMod.natCast_zmod_val] using x.property⟩
  apply h
  unfold localFactor count
  change (Nat.card S : ℝ)/(M : ℝ)^3 = 0
  simp

private theorem hasValuationTargets_of_factor_nonzero {B : ℕ} {Q : Finset ℕ}
    (hQ : OddPrimeSet Q) (hsub : oddPrimesThrough B ⊆ Q)
    (a : Fin 4 → ℕ) (hSupport : ∀ p ∈ (∏ i, a i : ℕ).primeFactors, p ≤ B)
    (ha : ∀ i, 0 < a i) {u : ℕ} (hu : primeSystemTarget Q u)
    (h : localFactor (primeSystemModulus Q) a u ≠ 0) :
    hasValuationTargets (a 0) (a 1) (a 2) (a 3) := by
  rw [primeSystem_factor hQ hu a] at h
  have hTwo : localFactor 16 a 8 ≠ 0 := fun hn => h (by rw [hn,zero_mul])
  have hOdd (p : ℕ) (hp : p ∈ Q) : valuationOneFactor a p ≠ 0 :=
    Finset.prod_ne_zero_iff.mp (fun hn => h (by rw [hn,mul_zero])) p hp
  constructor
  · obtain ⟨x,hx⟩ := exists_naturals_mod a hTwo
    refine ⟨x 0,x 1,x 2,x 3,?_⟩
    have hx' : (∑ i, a i * (x i)^4)%16=8 := hx
    rwa [Fin.sum_univ_four] at hx'
  · intro p hp hp2 hpDiv
    have hpD : p ∣ ∏ i, a i := by rwa [Fin.prod_univ_four]
    have hD0 : (∏ i, a i) ≠ 0 := (Finset.prod_pos fun i _ => ha i).ne'
    have hpB := hSupport p (Nat.mem_primeFactors.mpr ⟨hp,hpD,hD0⟩)
    have hpQ : p ∈ Q := hsub (mem_erase.mpr ⟨hp2,mem_primesThrough.mpr ⟨hp,hpB⟩⟩)
    have hv : localFactor (p*p) a p ≠ 0 := by
      rw [localFactor_prime_sq]
      exact hOdd p hpQ
    let : NeZero (p*p) := ⟨Nat.mul_ne_zero hp.ne_zero hp.ne_zero⟩
    obtain ⟨x,hx⟩ := exists_naturals_mod a hv
    refine ⟨x 0,x 1,x 2,x 3,?_⟩
    have hpLt : p < p*p := by nlinarith [hp.two_le]
    have hx' : (∑ i, a i * (x i)^4)%(p*p)=p :=
      Eq.trans (show (∑ i, a i * (x i)^4)%(p*p) = p%(p*p) from hx) (Nat.mod_eq_of_lt hpLt)
    simpa only [Fin.sum_univ_four, pow_two] using hx'

/-- The CRT factor of each principal tuple vanishes whenever the
baseline contains its odd coefficient primes. -/
theorem primeSystem_excludes_principal {B : ℕ} {Q : Finset ℕ}
    (hQ : OddPrimeSet Q) (hsub : oddPrimesThrough B ⊆ Q)
    (a : Fin 4 → ℕ) (hSupport : ∀ p ∈ (∏ i, a i : ℕ).primeFactors, p ≤ B)
    (ha : ∀ i, 0 < a i) (hFull : ∀ i, (4 : ℕ).Full (a i))
    (hType : PrincipalType a) {u : ℕ} (hu : primeSystemTarget Q u) :
    localFactor (primeSystemModulus Q) a u = 0 := by
  by_contra h
  rcases hType with hSq | ⟨σ,w,hw⟩
  · have hSq' : IsSquare (a 0*a 1*a 2*a 3) := by rwa [Fin.prod_univ_four] at hSq
    exact excludes_principal_coefficients (ha 0) (ha 1) (ha 2) (ha 3)
      (hFull 0) (hFull 1) (hFull 2) (hFull 3) (Or.inl hSq')
      (hasValuationTargets_of_factor_nonzero hQ hsub a hSupport ha hu h)
  · let b (i : Fin 4) := a (σ i)
    have hB : (∏ i, b i) = ∏ i, a i := coefficientProduct_reindex a σ
    have h' : localFactor (primeSystemModulus Q) b u ≠ 0 := by
      dsimp [b]
      rwa [localFactor_reindex _ a u σ]
    apply excludes_principal_coefficients (ha (σ 0)) (ha (σ 1)) (ha (σ 2)) (ha (σ 3))
      (hFull (σ 0)) (hFull (σ 1)) (hFull (σ 2)) (hFull (σ 3)) (Or.inr ⟨w,hw⟩)
    apply hasValuationTargets_of_factor_nonzero hQ hsub b _ (fun i => ha (σ i)) hu h'
    rw [hB]
    exact hSupport

/-- The initial Euler product over the odd baseline primes outside the
coefficient support. -/
private noncomputable def baselineGoodProduct (B : ℕ) (a : Fin 4 → ℕ) : ℝ :=
  ∏ p ∈ (oddPrimesThrough B).filter (fun p => ¬p ∣ ∏ i, a i), valuationOneFactor a p

theorem primeSystem_regular_factor {B : ℕ} {Q : Finset ℕ}
    (hQ : ∀ p ∈ Q, p.Prime ∧ p%4=3 ∧ B < p)
    (a : Fin 4 → ℕ) (ha : ∀ i, 0 < a i) (hFull : ∀ i, (4 : ℕ).Full (a i))
    {u : ℕ} (hu : primeSystemTarget (oddPrimesThrough B ∪ Q) u) :
    localFactor (primeSystemModulus (oddPrimesThrough B ∪ Q)) a u ≤
      16 * (4 : ℝ)^(∏ i, a i : ℕ).primeFactors.card *
        baselineGoodProduct B a * (∏ p ∈ Q, valuationOneFactor a p) := by
  classical
  let R := oddPrimesThrough B
  have hDis : Disjoint R Q := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    exact (not_le_of_gt (hQ p hq).2.2) ((mem_primesThrough.mp (mem_erase.mp hp).2).2)
  have hAll : OddPrimeSet (R ∪ Q) := by
    intro p hp
    rcases Finset.mem_union.mp hp with hR | hP
    · exact oddPrimesThrough_odd B p hR
    · exact ⟨(hQ p hP).1,by have := (hQ p hP).2.1; omega⟩
  let D := ∏ i, a i
  let Qb := R.filter (fun p => p ∣ D)
  have hb : Qb ⊆ D.primeFactors := by
    intro p hp
    obtain ⟨hpR,hpD⟩ := Finset.mem_filter.mp hp
    exact Nat.mem_primeFactors.mpr ⟨(oddPrimesThrough_odd B p hpR).1,hpD,
      (Finset.prod_pos fun i _ => ha i).ne'⟩
  have hCard := Finset.card_le_card hb
  have hBad : (∏ p ∈ Qb, valuationOneFactor a p) ≤ (4 : ℝ)^D.primeFactors.card := by
    calc
      _ ≤ ∏ p ∈ Qb, (4 : ℝ) := Finset.prod_le_prod (fun p _ => valuationOneFactor_nonneg a p) (by
        intro p hp
        have ht := oddPrimesThrough_odd B p (Finset.mem_filter.mp hp).1
        let : Fact p.Prime := ⟨ht.1⟩
        exact valuationOneFactor_le_four ht.2 a hFull)
      _ ≤ _ := by rw [Finset.prod_const]; exact pow_le_pow_right₀ (by norm_num) hCard
  have hGood0 : 0 ≤ baselineGoodProduct B a :=
    Finset.prod_nonneg fun p _ => valuationOneFactor_nonneg a p
  have hQ0 : 0 ≤ ∏ p ∈ Q, valuationOneFactor a p :=
    Finset.prod_nonneg fun p _ => valuationOneFactor_nonneg a p
  rw [primeSystem_factor hAll hu a, Finset.prod_union hDis,
    ← Finset.prod_filter_mul_prod_filter_not (s := R) (p := fun p => p ∣ D)]
  change localFactor 16 a 8 * ((∏ p ∈ Qb, valuationOneFactor a p) *
    baselineGoodProduct B a * (∏ p ∈ Q, valuationOneFactor a p)) ≤ _
  rw [← mul_assoc, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul (localFactor_le_modulus 16 a 8) hBad
      (Finset.prod_nonneg fun p _ => valuationOneFactor_nonneg a p) (by norm_num)) hGood0) hQ0

end Erdos940Quartic

namespace Erdos940QuarticCanonicalKernel

open Nat

/-- The part remaining after the canonical rth power is removed. -/
private def IsKernel (r d : ℕ) : Prop :=
  0 < d ∧ ∀ p, d.factorization p = 0 ∨
    r < d.factorization p ∧ d.factorization p < 2 * r

private def kernelExponent (r e : ℕ) : ℕ :=
  if e % r = 0 then 0 else r + e % r

private def baseExponent (r e : ℕ) : ℕ :=
  e / r - if e % r = 0 then 0 else 1

private lemma kernelExponent_range {r e : ℕ} (hr : 0 < r) :
    kernelExponent r e = 0 ∨ r < kernelExponent r e ∧ kernelExponent r e < 2 * r := by
  unfold kernelExponent
  split
  · exact Or.inl rfl
  · have h := Nat.mod_lt e hr
    omega

private lemma exponent_split {r e : ℕ} (hr : 0 < r) (he : e = 0 ∨ r ≤ e) :
    r * baseExponent r e + kernelExponent r e = e := by
  have hDiv := Nat.div_add_mod e r
  by_cases h : e % r = 0
  · simpa [baseExponent, kernelExponent, h] using hDiv
  · have hrle : r ≤ e := by rcases he with rfl | he <;> simp_all
    have hc : 1 ≤ e / r := (Nat.le_div_iff_mul_le hr).mpr (by simpa using hrle)
    have hstep : r * (e / r - 1) + r = r * (e / r) := by
      calc
        r * (e / r - 1) + r = r * (e / r - 1) + r * 1 := by rw [Nat.mul_one]
        _ = r * ((e / r - 1) + 1) := (Nat.mul_add ..).symm
        _ = _ := by rw [Nat.sub_add_cancel hc]
    simp only [baseExponent, kernelExponent, h, if_false, ← Nat.add_assoc, hstep]
    exact hDiv

private lemma kernelExponent_of_valid {r e : ℕ} (_hr : 0 < r)
    (he : e = 0 ∨ r < e ∧ e < 2 * r) : kernelExponent r e = e := by
  rcases he with rfl | ⟨h₁, h₂⟩
  · simp [kernelExponent]
  have hx : 0 < e - r := by omega
  have hy : e - r < r := by omega
  have hm : e % r = e - r := by
    calc
      e % r = ((e - r) + r) % r := by congr 1; omega
      _ = (e - r) % r := Nat.add_mod_right _ _
      _ = _ := Nat.mod_eq_of_lt hy
  simp [kernelExponent, hm, hx.ne', Nat.add_sub_of_le h₁.le]

private lemma kernelExponent_mul_add {r a d : ℕ} (hr : 0 < r)
    (hd : d = 0 ∨ r < d ∧ d < 2 * r) : kernelExponent r (r * a + d) = d := by
  unfold kernelExponent
  have hm : (r * a + d) % r = d % r := by simp [Nat.add_mod]
  rw [hm]
  exact kernelExponent_of_valid hr hd

private lemma full_valuation {r n p : ℕ} (h : r.Full n) :
    n.factorization p = 0 ∨ r ≤ n.factorization p := by
  by_cases hp : p ∈ n.primeFactors
  · exact Or.inr ((Nat.Prime.pow_dvd_iff_le_factorization
      (Nat.prime_of_mem_primeFactors hp) ((Nat.mem_primeFactors.mp hp).2.2)).mp (h p hp))
  · exact Or.inl (Finsupp.notMem_support_iff.mp hp)

private lemma positive_product (f : ℕ →₀ ℕ) (hf : ∀ p ∈ f.support, p.Prime) :
    0 < f.prod (· ^ ·) := by
  apply Finset.prod_pos
  exact fun p hp => Nat.pow_pos (hf p hp).pos

/-- Canonical rth-power decomposition of every positive r-full integer.
The kernel contains each prime to an exponent in [r+1, 2r-1]. -/
theorem exists_unique_kernel {r n : ℕ} (hr : 0 < r) (hn : 0 < n) (hfull : r.Full n) :
    ∃! ad : ℕ × ℕ, 0 < ad.1 ∧ IsKernel r ad.2 ∧ n = ad.1 ^ r * ad.2 := by
  let f := n.factorization.mapRange (baseExponent r) (by simp [baseExponent])
  let g := n.factorization.mapRange (kernelExponent r) (by simp [kernelExponent])
  let a := f.prod (· ^ ·)
  let d := g.prod (· ^ ·)
  have hf : ∀ p ∈ f.support, p.Prime := fun p hp =>
    Nat.prime_of_mem_primeFactors (Finsupp.support_mapRange hp)
  have hg : ∀ p ∈ g.support, p.Prime := fun p hp =>
    Nat.prime_of_mem_primeFactors (Finsupp.support_mapRange hp)
  have hfa : a.factorization = f := Nat.prod_pow_factorization_eq_self hf
  have hgd : d.factorization = g := Nat.prod_pow_factorization_eq_self hg
  have ha : 0 < a := positive_product _ hf
  have hd : 0 < d := positive_product _ hg
  have hdk : IsKernel r d := by
    refine ⟨hd, fun p => ?_⟩
    rw [hgd]
    exact kernelExponent_range hr
  have he : n = a ^ r * d := by
    apply Nat.factorization_inj hn.ne' (Nat.mul_ne_zero (pow_ne_zero _ ha.ne') hd.ne')
    rw [Nat.factorization_mul (pow_ne_zero _ ha.ne') hd.ne', Nat.factorization_pow, hfa, hgd]
    ext p
    exact (exponent_split hr (full_valuation hfull)).symm
  refine ⟨(a, d), ⟨ha, hdk, he⟩, ?_⟩
  rintro ⟨a', d'⟩ ⟨ha', hd', he'⟩
  have hexp (p : ℕ) :
      r * a'.factorization p + d'.factorization p = r * a.factorization p + d.factorization p := by
    have hh := congrArg (fun n : ℕ => n.factorization p) (he'.symm.trans he)
    rw [Nat.factorization_mul (pow_ne_zero _ ha'.ne') hd'.1.ne',
      Nat.factorization_mul (pow_ne_zero _ ha.ne') hd.ne', Nat.factorization_pow,
      Nat.factorization_pow] at hh
    exact hh
  have hde : d' = d := by
    apply Nat.factorization_inj hd'.1.ne' hd.ne'
    ext p
    have hd₁ := kernelExponent_mul_add (a := a'.factorization p) hr (hd'.2 p)
    have hd₂ := kernelExponent_mul_add (a := a.factorization p) hr (hdk.2 p)
    rw [hexp] at hd₁
    exact hd₁.symm.trans hd₂
  refine Prod.ext ?_ hde
  apply Nat.factorization_inj ha'.ne' ha.ne'
  ext p
  have hp := hexp p
  rw [hde] at hp
  exact mul_left_cancel₀ hr.ne' (Nat.add_right_cancel hp)

/-- Conversely, a product of the indicated types is r-full. -/
theorem full_of_kernel {r a d : ℕ} (_hr : 0 < r) (ha : 0 < a) (hd : IsKernel r d) :
    r.Full (a ^ r * d) := by
  intro p hp
  let n := a ^ r * d
  have hn : n ≠ 0 := Nat.mul_ne_zero (pow_ne_zero _ ha.ne') hd.1.ne'
  apply (Nat.Prime.pow_dvd_iff_le_factorization (Nat.prime_of_mem_primeFactors hp) hn).2
  have hpos : 0 < n.factorization p := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp)
  rw [show n = a ^ r * d from rfl, Nat.factorization_mul (pow_ne_zero _ ha.ne') hd.1.ne',
    Nat.factorization_pow] at hpos ⊢
  change 0 < r * a.factorization p + d.factorization p at hpos
  change r ≤ r * a.factorization p + d.factorization p
  rcases hd.2 p with hz | ⟨hp, _⟩
  · have ha' : 0 < a.factorization p := by
      by_contra! hh
      simp [Nat.eq_zero_of_le_zero hh, hz] at hpos
    simpa [hz] using Nat.le_mul_of_pos_right r ha'
  · omega


open Finset Filter
open scoped Topology

theorem four_prime_factor_count_le_rpow (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n → (4 : ℝ) ^ n.primeFactors.card ≤ C * (n : ℝ) ^ ε := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ) ^ ε) atTop atTop :=
    (tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop
  obtain ⟨K, hK⟩ := eventually_atTop.mp (ht.eventually_ge_atTop (4 : ℝ))
  refine ⟨(4 : ℝ)^K, by positivity, ?_⟩
  intro n hn
  let P := n.primeFactors
  let A := P.filter (fun p => p < K)
  let B := P.filter (fun p => ¬ p < K)
  have hcard : A.card + B.card = P.card := Finset.card_filter_add_card_filter_not (s := P) (fun p => p < K)
  have hA : A.card ≤ K := by
    have hh : A ⊆ range K := fun x hx => mem_range.mpr (mem_filter.mp hx).2
    simpa using card_le_card hh
  have hSmall : (4 : ℝ)^A.card ≤ 4^K := pow_le_pow_right₀ (by norm_num) hA
  have hBig : (4 : ℝ)^B.card ≤ ∏ p ∈ B, (p : ℝ)^ε := by
    rw [← Finset.prod_const]
    apply Finset.prod_le_prod (fun _ _ => by norm_num)
    intro p hp
    exact hK p (le_of_not_gt (mem_filter.mp hp).2)
  have hProd : (∏ p ∈ B, p) ≤ n := by
    have hP : ∏ p ∈ P, p ∣ n := Nat.prod_primeFactors_dvd n
    have hsub : B ⊆ P := Finset.filter_subset _ _
    have hD : (∏ p ∈ B, p) ∣ ∏ p ∈ P, p :=
      Finset.prod_dvd_prod_of_subset _ _ _ hsub
    exact Nat.le_of_dvd hn (hD.trans hP)
  have hBig' : (4 : ℝ)^B.card ≤ (n : ℝ)^ε := by
    refine hBig.trans ?_
    rw [Real.finsetProd_rpow _ _ (fun _ _ => by positivity), ← Nat.cast_prod]
    exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hProd) hε.le
  change (4 : ℝ)^P.card ≤ (4 : ℝ)^K * (n : ℝ)^ε
  rw [← hcard, pow_add]
  exact mul_le_mul hSmall hBig' (by positivity) (by positivity)

private theorem summable_weighted_rpow {s : ℝ} (hs : 1 < s) :
    Summable (fun n : ℕ => (4 : ℝ) ^ n.primeFactors.card * (n : ℝ) ^ (-s)) := by
  let ε := (s - 1) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  obtain ⟨C, hC, hL⟩ := four_prime_factor_count_le_rpow ε hε
  have hSum : Summable (fun n : ℕ => C * (n : ℝ) ^ (ε - s)) :=
    (Real.summable_nat_rpow.mpr (by dsimp [ε]; linarith)).mul_left C
  apply hSum.of_nonneg_of_le (fun _ => by positivity)
  intro n
  by_cases hn : n = 0
  · subst n
    have h1 : -s ≠ 0 := by linarith
    have h2 : ε - s ≠ 0 := by dsimp [ε]; linarith
    simp [Real.zero_rpow h1, Real.zero_rpow h2]
  · have hR : 0 < (n : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hn)
    have hB := mul_le_mul_of_nonneg_right (hL n (Nat.pos_of_ne_zero hn))
      (show 0 ≤ (n : ℝ)^(-s) by positivity)
    rwa [mul_assoc, ← Real.rpow_add hR, ← sub_eq_add_neg] at hB

end Erdos940QuarticCanonicalKernel

namespace Erdos940QuarticWeights

open Erdos940QuarticCanonicalKernel Finset Filter

private abbrev Kernel := {d : ℕ // IsKernel 4 d}
private abbrev Tuple := Fin 4 → Kernel

private theorem kernel_vals {d : ℕ} (hd : IsKernel 4 d) (p : ℕ) :
    d.factorization p = 0 ∨ d.factorization p = 5 ∨
      d.factorization p = 6 ∨ d.factorization p = 7 := by
  rcases hd.2 p with h | h <;> omega

private theorem split {d : ℕ} (hd : IsKernel 4 d) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ d = a^5*b^6*c^7 := by
  let ff (e : ℕ) (he : e ≠ 0) :=
    d.factorization.mapRange (fun k => if k=e then 1 else 0) (by simp [Ne.symm he])
  let d₁ := ff 5 (by decide)
  let d₂ := ff 6 (by decide)
  let d₃ := ff 7 (by decide)
  let a := d₁.prod (· ^ ·)
  let b := d₂.prod (· ^ ·)
  let c := d₃.prod (· ^ ·)
  have primeSupport (e : ℕ) (he : e ≠ 0) : ∀ p ∈ (ff e he).support, p.Prime :=
    fun p hp => Nat.prime_of_mem_primeFactors (Finsupp.support_mapRange hp)
  have ha : 0 < a := Finset.prod_pos (fun p hp => Nat.pow_pos ((primeSupport 5 (by decide) p hp).pos))
  have hb : 0 < b := Finset.prod_pos (fun p hp => Nat.pow_pos ((primeSupport 6 (by decide) p hp).pos))
  have hc : 0 < c := Finset.prod_pos (fun p hp => Nat.pow_pos ((primeSupport 7 (by decide) p hp).pos))
  have hfa : a.factorization = d₁ := Nat.prod_pow_factorization_eq_self (primeSupport 5 (by decide))
  have hfb : b.factorization = d₂ := Nat.prod_pow_factorization_eq_self (primeSupport 6 (by decide))
  have hfc : c.factorization = d₃ := Nat.prod_pow_factorization_eq_self (primeSupport 7 (by decide))
  have hAB : a^5*b^6 ≠ 0 := mul_ne_zero (pow_ne_zero _ ha.ne') (pow_ne_zero _ hb.ne')
  refine ⟨a,b,c,ha,hb,hc,?_⟩
  apply Nat.factorization_inj hd.1.ne' (mul_ne_zero hAB (pow_ne_zero _ hc.ne'))
  rw [Nat.factorization_mul hAB (pow_ne_zero _ hc.ne'),
    Nat.factorization_mul (pow_ne_zero _ ha.ne') (pow_ne_zero _ hb.ne'),
    Nat.factorization_pow, Nat.factorization_pow, Nat.factorization_pow, hfa,hfb,hfc]
  ext p
  change d.factorization p = (5 * (if d.factorization p=5 then 1 else 0) +
    6 * (if d.factorization p=6 then 1 else 0)) + 7 * (if d.factorization p=7 then 1 else 0)
  rcases kernel_vals hd p with h | h | h | h <;> simp [h]

private noncomputable def numberWeight (s : ℝ) (n : ℕ) : ℝ :=
  (4 : ℝ)^n.primeFactors.card * (n : ℝ)^(-s)

private theorem numberWeight_nonneg (s : ℝ) (n : ℕ) : 0 ≤ numberWeight s n := by
  unfold numberWeight
  positivity

private theorem numberWeight_submul {s : ℝ} {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    numberWeight s (a*b) ≤ numberWeight s a * numberWeight s b := by
  have hC : (a*b).primeFactors.card ≤ a.primeFactors.card + b.primeFactors.card := by
    rw [Nat.primeFactors_mul ha.ne' hb.ne']
    exact Finset.card_union_le _ _
  have hP : (4 : ℝ)^(a*b).primeFactors.card ≤
      (4 : ℝ)^a.primeFactors.card * (4 : ℝ)^b.primeFactors.card := by
    rw [← pow_add]
    exact pow_le_pow_right₀ (by norm_num) hC
  unfold numberWeight
  rw [Nat.cast_mul, Real.mul_rpow (by positivity) (by positivity)]
  calc
    _ ≤ _ * _ := mul_le_mul_of_nonneg_right hP (by positivity)
    _ = _ := by ring

private theorem numberWeight_pow {s : ℝ} {a k : ℕ} (hk : k ≠ 0) :
    numberWeight s (a^k) = numberWeight ((k : ℝ)*s) a := by
  unfold numberWeight
  rw [Nat.primeFactors_pow _ hk, Nat.cast_pow, ← Real.rpow_natCast_mul (by positivity)]
  congr 2
  ring

/-- The canonical quartic weights are summable for every exponent strictly
larger than one fifth, including a factor of four per coefficient prime. -/
theorem summable_kernel_weight {s : ℝ} (hs : 1/5 < s) :
    Summable (fun d : Kernel => numberWeight s d.val) := by
  classical
  let w₁ := numberWeight (5*s)
  let w₂ := numberWeight (6*s)
  let w₃ := numberWeight (7*s)
  have h₁ : Summable w₁ := summable_weighted_rpow (by linarith)
  have h₂ : Summable w₂ := summable_weighted_rpow (by linarith)
  have h₃ : Summable w₃ := summable_weighted_rpow (by linarith)
  have h₂₃ : Summable (fun x : ℕ × ℕ => w₂ x.1 * w₃ x.2) :=
    summable_mul_of_summable_norm h₂.norm h₃.norm
  have hProd : Summable (fun x : ℕ × ℕ × ℕ => w₁ x.1 * (w₂ x.2.1 * w₃ x.2.2)) :=
    summable_mul_of_summable_norm h₁.norm h₂₃.norm
  choose a b c ha hb hc he using fun d : Kernel => split d.property
  let e (d : Kernel) := (a d,b d,c d)
  have heInj : Function.Injective e := by
    intro x y h
    apply Subtype.ext
    have ha' : a x = a y := congrArg Prod.fst h
    have hb' : b x = b y := congrArg (fun z => z.2.1) h
    have hc' : c x = c y := congrArg (fun z => z.2.2) h
    rw [he x,he y,ha',hb',hc']
  apply (hProd.comp_injective heInj).of_nonneg_of_le (fun _ => numberWeight_nonneg _ _)
  intro d
  dsimp [e,w₁,w₂,w₃]
  rw [he d]
  calc
    _ ≤ numberWeight s (a d^5*b d^6) * numberWeight s (c d^7) :=
      numberWeight_submul (mul_pos (pow_pos (ha d) _) (pow_pos (hb d) _)) (pow_pos (hc d) _)
    _ ≤ (numberWeight s (a d^5)*numberWeight s (b d^6))*numberWeight s (c d^7) :=
      mul_le_mul_of_nonneg_right (numberWeight_submul (pow_pos (ha d) _) (pow_pos (hb d) _))
        (numberWeight_nonneg _ _)
    _ = _ := by
      rw [numberWeight_pow (by decide),numberWeight_pow (by decide),numberWeight_pow (by decide)]
      push_cast
      ring

/-- Product of the four canonical coefficients. -/
private def coefficientProduct (d : Tuple) : ℕ := ∏ i, (d i).val

theorem coefficientProduct_pos (d : Tuple) : 0 < coefficientProduct d :=
  Finset.prod_pos (fun i _ => (d i).property.1)

private noncomputable def tupleWeight (s : ℝ) (d : Tuple) : ℝ :=
  numberWeight s (coefficientProduct d)

theorem tupleWeight_nonneg (s : ℝ) (d : Tuple) : 0 ≤ tupleWeight s d := numberWeight_nonneg _ _

set_option maxHeartbeats 1000000 in
/-- The determinant weight remains summable over ordered coefficient tuples. -/
theorem summable_tuple_weight {s : ℝ} (hs : 1/5 < s) : Summable (tupleWeight s) := by
  let f (d : Kernel) := numberWeight s d.val
  have h := summable_kernel_weight hs
  have h₂ : Summable (fun x : Kernel × Kernel => f x.1*f x.2) :=
    summable_mul_of_summable_norm h.norm h.norm
  have h₃ : Summable (fun x : Kernel × Kernel × Kernel => f x.1*(f x.2.1*f x.2.2)) :=
    summable_mul_of_summable_norm h.norm h₂.norm
  have h₄ : Summable (fun x : Kernel × Kernel × Kernel × Kernel =>
      f x.1 * (f x.2.1 * (f x.2.2.1 * f x.2.2.2))) :=
    summable_mul_of_summable_norm h.norm h₃.norm
  let e (d : Tuple) := (d 0,d 1,d 2,d 3)
  have hInj : Function.Injective e := by
    intro d d' hEq
    funext i
    fin_cases i
    · exact congrArg Prod.fst hEq
    · exact congrArg (fun z => z.2.1) hEq
    · exact congrArg (fun z => z.2.2.1) hEq
    · exact congrArg (fun z => z.2.2.2) hEq
  apply (h₄.comp_injective hInj).of_nonneg_of_le (tupleWeight_nonneg s)
  intro d
  let x := (d 0).val
  let y := (d 1).val
  let z := (d 2).val
  let w := (d 3).val
  have hx : 0 < x := (d 0).property.1
  have hy : 0 < y := (d 1).property.1
  have hz : 0 < z := (d 2).property.1
  have hw : 0 < w := (d 3).property.1
  have hEq : coefficientProduct d = x*(y*(z*w)) := by
    unfold coefficientProduct
    rw [Fin.prod_univ_four]
    change x*y*z*w = _
    ring
  change numberWeight s (coefficientProduct d) ≤
    numberWeight s x * (numberWeight s y * (numberWeight s z * numberWeight s w))
  rw [hEq]
  calc
    _ ≤ numberWeight s x * numberWeight s (y*(z*w)) := numberWeight_submul hx (by positivity)
    _ ≤ numberWeight s x * (numberWeight s y * numberWeight s (z*w)) :=
      mul_le_mul_of_nonneg_left (numberWeight_submul hy (by positivity)) (numberWeight_nonneg _ _)
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (numberWeight_submul hz hw) (numberWeight_nonneg _ _))
      (numberWeight_nonneg _ _)

/-- Keeping a fixed positive moment gives a quantitative tail in the
coefficient-product cutoff. -/
theorem large_product_tail {η : ℝ} (hη : 0 ≤ η) (hη' : η < 1/20) (B : ℕ) (hB : 0 < B) :
    (∑' d : {d : Tuple // B < coefficientProduct d}, tupleWeight (1/4) d.val) ≤
      (B : ℝ)^(-η) * (∑' d : Tuple, tupleWeight (1/4-η) d) := by
  let U := {d : Tuple // B < coefficientProduct d}
  let W := tupleWeight (1/4-η)
  have hW : Summable W := summable_tuple_weight (by linarith)
  have hSummable : Summable (tupleWeight (1/4)) := summable_tuple_weight (by norm_num)
  have hB' : 0 < (B : ℝ) := by exact_mod_cast hB
  have h₀ : 0 ≤ (B : ℝ)^(-η) := by positivity
  calc
    _ ≤ ∑' d : U, (B : ℝ)^(-η) * W d.val := by
      apply hSummable.subtype _ |>.tsum_le_tsum _ ((hW.mul_left _).subtype _)
      intro d
      have hpos : 0 < (coefficientProduct d.val : ℝ) := by
        exact_mod_cast coefficientProduct_pos d.val
      have hle : (B : ℝ) ≤ coefficientProduct d.val := by exact_mod_cast d.property.le
      have hPower := Real.rpow_le_rpow_of_nonpos hB' hle (neg_nonpos.mpr hη)
      have hEq : tupleWeight (1/4) d.val =
          (coefficientProduct d.val : ℝ)^(-η) * W d.val := by
        unfold W tupleWeight numberWeight
        rw [mul_left_comm, ← Real.rpow_add hpos]
        congr 2
        ring
      change tupleWeight (1/4) d.val ≤ (B : ℝ)^(-η) * W d.val
      rw [hEq]
      exact mul_le_mul_of_nonneg_right hPower (tupleWeight_nonneg _ d.val)
    _ = (B : ℝ)^(-η) * ∑' d : U, W d.val := tsum_mul_left
    _ ≤ _ := mul_le_mul_of_nonneg_left
      ((hW.subtype _).tsum_le_tsum_of_inj Subtype.val Subtype.val_injective
        (fun d _ => tupleWeight_nonneg _ d) (fun _ => le_rfl) hW) h₀

end Erdos940QuarticWeights


namespace Erdos940Quartic

open Finset Filter Erdos940QuarticWeights Erdos940QuarticPrimes
open Erdos940QuarticPrimeHarmonic Erdos940QuarticCanonicalKernel
open scoped Topology

private abbrev coeffs (d : Tuple) (i : Fin 4) : ℕ := (d i).val

private theorem coeffs_full (d : Tuple) (i : Fin 4) : (4 : ℕ).Full (coeffs d i) := by
  simpa using full_of_kernel (r := 4) (a := 1) (by decide) (by decide) (d i).property

private noncomputable def scaleWeight (d : Tuple) : ℝ :=
  (coefficientProduct d : ℝ)^(-(1/4) : ℝ)

/-- It suffices to prove a fixed mild power bound on the regular
good-prime baseline. The analytic research proof gives a logarithmic bound. -/
private def RegularEulerBound : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ B : ℕ, ∀ d : Tuple, ¬ PrincipalType (coeffs d) →
    baselineGoodProduct B (coeffs d) ≤ C * (coefficientProduct d : ℝ)^(1/100 : ℝ)

private theorem small_tail {ι : Type} {f : ι → ℝ} (hF : Summable f) (δ : ℝ) (hδ : 0 < δ) :
    ∃ D : Finset ι, (∑' d : {d // d ∉ D}, f d.val) < δ := by
  let W := ∑' d, f d
  have hW : Tendsto (fun D : Finset ι => ∑ d ∈ D, f d) atTop (𝓝 W) := hF.hasSum
  obtain ⟨D,hD⟩ := (hW.eventually (lt_mem_nhds (show W-δ < W by linarith))).exists
  have hE := hF.sum_add_tsum_subtype_compl D
  change (∑ d ∈ D, f d) + (∑' d : {d // d ∉ D}, f d.val) = W at hE
  exact ⟨D,by linarith⟩

private theorem choose_auxiliary_primes (T : ℝ) (hT : 0 ≤ T) (B : ℕ)
    (E₀ E : Finset Tuple) :
    let rate := (1 : ℝ)/(2*((E₀.card : ℝ)+1))
    ∃ Q : Finset ℕ, (∀ p ∈ Q, p.Prime ∧ p%4=3 ∧ B < p) ∧
      (∑ p ∈ Q, (1 : ℝ)/p) ≤ T+1 ∧
      ∀ d ∈ E, ¬PrincipalType (coeffs d) →
        (∏ p ∈ Q, valuationOneFactor (coeffs d) p) ≤
          Real.exp (-(T * (if d ∈ E₀ then rate else 0)) + 2) := by
  classical
  let rate := (1 : ℝ)/(2*((E₀.card : ℝ)+1))
  let P := E.biUnion (fun d => (coefficientProduct d).primeFactors)
  have hP (p : ℕ) (hp : p ∈ P) : p.Prime := by
    obtain ⟨_,_,hp⟩ := Finset.mem_biUnion.mp hp
    exact Nat.prime_of_mem_primeFactors hp
  let G := P → ZMod 2
  let S := (Finset.univ : Finset G).erase 0
  let pat (d : Tuple) := parity P (coefficientProduct d)
  let I := E₀.image pat
  let c (g : G) := if g ∈ I then rate else 0
  have hr : 0 ≤ rate := by positivity
  have hC : (∑ g ∈ S, c g) ≤ 1/2 := by
    simp only [c, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have hCard : (S.filter fun g => g ∈ I).card ≤ E₀.card := by
      have hSub : S.filter (fun g => g ∈ I) ⊆ I :=
        fun _ hg => (Finset.mem_filter.mp hg).2
      exact (Finset.card_le_card hSub).trans Finset.card_image_le
    calc
      _ ≤ (E₀.card : ℝ)*rate := mul_le_mul_of_nonneg_right (by exact_mod_cast hCard) hr
      _ ≤ _ := by
        unfold rate
        have hp : (0 : ℝ) < 2*((E₀.card : ℝ)+1) := by positivity
        rw [mul_one_div]
        exact (div_le_iff₀ hp).mpr (by ring_nf; linarith)
  let K := max (max B ⌈T+1⌉₊) (max (Fintype.card G) (P.sup id))
  have hKB : B ≤ K := le_trans (le_max_left _ _) (le_max_left _ _)
  have hKC : Fintype.card G ≤ K := le_trans (le_max_left _ _) (le_max_right _ _)
  have hKS (p : ℕ) (hp : p ∈ P) : p ≤ K :=
    (Finset.le_sup (f := id) hp).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hKT : T+1 ≤ (K : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast
      (show ⌈T+1⌉₊ ≤ K from (le_max_right _ _).trans (le_max_left _ _)))
  obtain ⟨Q,hQ,hBudget,hCtl⟩ :=
    selected_prime_product_bound P hP S c (by simp [S])
      (fun g _ => by unfold c; split <;> positivity) hC K hKC hKS T hT hKT
  refine ⟨Q,fun p hp => ⟨(hQ p hp).1,(hQ p hp).2.1,hKB.trans_lt (hQ p hp).2.2⟩,hBudget,?_⟩
  intro d hd hReg
  have hD : coefficientProduct d ≠ 0 := (coefficientProduct_pos d).ne'
  have hSupp : (coefficientProduct d).primeFactors ⊆ P :=
    Finset.subset_biUnion_of_mem (fun d => (coefficientProduct d).primeFactors) hd
  have hN : ¬IsSquare (coefficientProduct d) := fun h => hReg (Or.inl h)
  have hPat : parity P (coefficientProduct d) ∈ S :=
    Finset.mem_erase.mpr ⟨parity_ne_zero hD hSupp hN,Finset.mem_univ _⟩
  apply (hCtl (coeffs d) (coeffs_full d) hD hSupp hPat).trans
  apply Real.exp_le_exp.mpr
  change -T*c (parity P (coefficientProduct d))+2 ≤ -(T*(if d ∈ E₀ then rate else 0))+2
  by_cases he : d ∈ E₀
  · have hh : pat d ∈ I := Finset.mem_image_of_mem _ he
    have hh' : parity P (coefficientProduct d) ∈ I := hh
    rw [if_pos he, show c (parity P (coefficientProduct d)) = rate from if_pos hh', neg_mul]
  · rw [if_neg he]
    have hC0 : 0 ≤ c (parity P (coefficientProduct d)) := by
      unfold c
      split <;> positivity
    linarith [mul_nonneg hT hC0]

set_option maxHeartbeats 2500000 in
/-- Conditional only on the regular analytic Euler bound, a single CRT class
has arbitrarily small total weighted local factor over every coefficient tuple. -/
theorem exists_small_weighted_local_sum (hBaseline : RegularEulerBound)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (Q : Finset ℕ) (u : ℕ), OddPrimeSet Q ∧ primeSystemTarget Q u ∧
      (∑' d : Tuple, scaleWeight d * localFactor (primeSystemModulus Q) (coeffs d) u) < ε := by
  classical
  obtain ⟨C,hC,hAnalytic⟩ := hBaseline
  obtain ⟨C₀,hC₀,hUniversal⟩ := exp_harmonic_subpower (1/100) (by norm_num)
  let W := tupleWeight (1/4)
  let V := tupleWeight (6/25)
  let W₁ := tupleWeight (23/100)
  have hW : Summable W := summable_tuple_weight (by norm_num)
  have hV : Summable V := summable_tuple_weight (by norm_num)
  have hW₁ : Summable W₁ := summable_tuple_weight (by norm_num)
  let A := 16*C
  have hA : 0 < A := by positivity
  let A₀ := A * Real.exp 2
  have hA₀ : 0 < A₀ := mul_pos hA (Real.exp_pos _)
  obtain ⟨E₀,hE₀⟩ := small_tail hV (ε/(8*A₀)) (by positivity)
  let rate := (1 : ℝ)/(2*((E₀.card : ℝ)+1))
  have hRate : 0 < rate := by positivity
  have hTend : Tendsto (fun T : ℝ => (A₀*Real.exp (-(T*rate)))*(∑' d, V d)) atTop (𝓝 0) := by
    have hExp : Tendsto (fun T : ℝ => Real.exp (-(T*rate))) atTop (𝓝 0) := by
      apply Real.tendsto_exp_atBot.comp
      have hh : Tendsto (fun T : ℝ => (-rate)*T) atTop atBot :=
        (tendsto_const_mul_atBot_of_neg (neg_lt_zero.mpr hRate)).mpr tendsto_id
      simpa [mul_comm, Function.comp_def] using hh
    simpa only [mul_zero,zero_mul] using (hExp.const_mul A₀).mul_const (∑' d,V d)
  obtain ⟨T,hT,hTsmall⟩ := ((eventually_ge_atTop (0 : ℝ)).and
    (hTend.eventually (gt_mem_nhds (show 0 < ε/8 by positivity)))).exists
  let U := 16*C₀*Real.exp (T+1)
  have hU : 0 < U := by positivity
  have hPow : Tendsto (fun B : ℕ => (U*(∑' d, W₁ d))*(B : ℝ)^(-(1/100) : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, mul_zero] using
      ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1/100)).comp
        tendsto_natCast_atTop_atTop).const_mul (U*(∑' d,W₁ d))
  obtain ⟨B,hB,hBsmall⟩ := ((eventually_gt_atTop (0 : ℕ)).and
    (hPow.eventually (gt_mem_nhds (show 0 < ε/8 by positivity)))).exists
  have hBR : 0 < (B : ℝ) := by exact_mod_cast hB
  let UB := U*(B : ℝ)^(1/100 : ℝ)
  have hUB : 0 < UB := mul_pos hU (Real.rpow_pos_of_pos hBR _)
  have hTailB : UB * (∑' d : {d : Tuple // B < coefficientProduct d}, W d.val) < ε/8 := by
    calc
      _ ≤ UB * ((B : ℝ)^(-(1/50) : ℝ) * (∑' d,W₁ d)) := by
        apply mul_le_mul_of_nonneg_left _ hUB.le
        have hh := large_product_tail (η := (1/50 : ℝ)) (by norm_num) (by norm_num) B hB
        norm_num at hh
        exact hh
      _ = (U*(∑' d,W₁ d))*(B : ℝ)^(-(1/100) : ℝ) := by
        unfold UB
        rw [← mul_assoc, mul_assoc U, ← Real.rpow_add hBR]
        norm_num
        ring
      _ < _ := hBsmall
  obtain ⟨E,hE⟩ := small_tail hW (ε/(8*UB)) (by positivity)
  obtain ⟨P,hP,hBudget,hControlled⟩ := choose_auxiliary_primes T hT B E₀ E
  let Q := oddPrimesThrough B ∪ P
  have hQ : OddPrimeSet Q := by
    intro p hp
    rcases Finset.mem_union.mp hp with hB' | hP'
    · exact oddPrimesThrough_odd B p hB'
    · exact ⟨(hP p hP').1, by have := (hP p hP').2.1; omega⟩
  obtain ⟨u,hu⟩ := exists_primeSystemTarget hQ
  refine ⟨Q,u,hQ,hu,?_⟩
  let F (d : Tuple) := scaleWeight d * localFactor (primeSystemModulus Q) (coeffs d) u
  have hF0 (d : Tuple) : 0 ≤ F d :=
    mul_nonneg (by unfold scaleWeight; positivity) (localFactor_nonneg _ _ _)
  have hFUniversal (d : Tuple) : F d ≤ UB*W d := by
    have hLoc := primeSystem_universal hP (coeffs d) (coeffs_full d)
      (fun i => (d i).property.1) hu
    have hAux := Real.exp_le_exp.mpr hBudget
    have hTerm := mul_le_mul_of_nonneg_right (hUniversal B hB)
      (Real.exp_nonneg (∑ p ∈ P, (1 : ℝ)/p))
    have hAll := hTerm.trans (mul_le_mul_of_nonneg_left hAux (by positivity))
    have hscale : 0 ≤ scaleWeight d := by unfold scaleWeight; positivity
    have hLead : 0 ≤ (16 : ℝ) * (4 : ℝ)^(∏ i, coeffs d i : ℕ).primeFactors.card := by positivity
    have hmul := mul_le_mul_of_nonneg_left (hLoc.trans (mul_le_mul_of_nonneg_left hAll hLead)) hscale
    calc
      _ ≤ _ := hmul
      _ = _ := by
        unfold UB U W tupleWeight Erdos940QuarticWeights.numberWeight scaleWeight
        rw [show (∏ i, coeffs d i) = coefficientProduct d from rfl]
        ring
  have hReg (d : Tuple) (hd : d ∈ E) (hR : ¬PrincipalType (coeffs d)) :
      F d ≤ (A₀*Real.exp (-(T*(if d ∈ E₀ then rate else 0))))*V d := by
    have hL := primeSystem_regular_factor hP (coeffs d) (fun i => (d i).property.1) (coeffs_full d) hu
    have hA' := hAnalytic B d hR
    have hS : (∏ p ∈ P, valuationOneFactor (coeffs d) p) ≤
        Real.exp (-(T*(if d ∈ E₀ then rate else 0))+2) := hControlled d hd hR
    have hV0 : 0 ≤ scaleWeight d := by unfold scaleWeight; positivity
    have hD : 0 < (coefficientProduct d : ℝ) := by exact_mod_cast coefficientProduct_pos d
    have hp0 : 0 ≤ ∏ p ∈ P, valuationOneFactor (coeffs d) p :=
      Finset.prod_nonneg fun p _ => valuationOneFactor_nonneg _ _
    have hLead0 : 0 ≤ (16 : ℝ) * (4 : ℝ)^(∏ i, coeffs d i : ℕ).primeFactors.card := by positivity
    have hml := mul_le_mul (mul_le_mul_of_nonneg_left hA' hLead0) hS hp0 (by positivity)
    calc
      _ ≤ _ := mul_le_mul_of_nonneg_left (hL.trans hml) hV0
      _ = _ := by
        rw [Real.exp_add]
        unfold V tupleWeight Erdos940QuarticWeights.numberWeight scaleWeight A₀ A
        have hExp : (coefficientProduct d : ℝ)^(-(1/4) : ℝ) *
            (coefficientProduct d : ℝ)^(1/100 : ℝ) =
            (coefficientProduct d : ℝ)^(-(6/25) : ℝ) := by
          rw [← Real.rpow_add hD]
          norm_num
        rw [show (∏ i, coeffs d i) = coefficientProduct d from rfl]
        linear_combination 16*C*(4:ℝ)^(coefficientProduct d).primeFactors.card *
          Real.exp (-(T*(if d ∈ E₀ then rate else 0))) * Real.exp 2 * hExp
  have hException (d : Tuple) (hd : PrincipalType (coeffs d))
      (hD : coefficientProduct d ≤ B) : F d = 0 := by
    have hS (p : ℕ) (hp : p ∈ (∏ i, coeffs d i : ℕ).primeFactors) : p ≤ B :=
      (Nat.le_of_dvd (coefficientProduct_pos d) (Nat.dvd_of_mem_primeFactors hp)).trans hD
    unfold F
    rw [primeSystem_excludes_principal hQ Finset.subset_union_left (coeffs d) hS
      (fun i => (d i).property.1) (coeffs_full d) hd hu,mul_zero]
  let f₁ (d : Tuple) := (A₀*Real.exp (-(T*rate)))*V d
  let f₂ (d : Tuple) := ({d : Tuple | d ∉ E₀} : Set Tuple).indicator (fun d => A₀*V d) d
  let f₃ (d : Tuple) := ({d : Tuple | B < coefficientProduct d} : Set Tuple).indicator (fun d => UB*W d) d
  let f₄ (d : Tuple) := ({d : Tuple | d ∉ E} : Set Tuple).indicator (fun d => UB*W d) d
  have h₁ : Summable f₁ := hV.mul_left _
  have h₂ : Summable f₂ := (hV.mul_left _).indicator _
  have h₃ : Summable f₃ := (hW.mul_left _).indicator _
  have h₄ : Summable f₄ := (hW.mul_left _).indicator _
  have hn₁ (d : Tuple) : 0 ≤ f₁ d :=
    mul_nonneg (mul_nonneg hA₀.le (Real.exp_nonneg _)) (tupleWeight_nonneg _ _)
  have hn₂ (d : Tuple) : 0 ≤ f₂ d :=
    Set.indicator_nonneg (fun d _ => mul_nonneg hA₀.le (tupleWeight_nonneg _ _)) _
  have hn₃ (d : Tuple) : 0 ≤ f₃ d :=
    Set.indicator_nonneg (fun d _ => mul_nonneg hUB.le (tupleWeight_nonneg _ _)) _
  have hn₄ (d : Tuple) : 0 ≤ f₄ d :=
    Set.indicator_nonneg (fun d _ => mul_nonneg hUB.le (tupleWeight_nonneg _ _)) _
  have hMajor (d : Tuple) : F d ≤ f₁ d + f₂ d + f₃ d + f₄ d := by
    by_cases hd : d ∈ E
    · by_cases hR : PrincipalType (coeffs d)
      · by_cases hD : coefficientProduct d ≤ B
        · rw [hException d hR hD]
          linarith [hn₁ d,hn₂ d,hn₃ d,hn₄ d]
        · have h₃' : f₃ d = UB*W d := Set.indicator_of_mem (s := {d : Tuple | B < coefficientProduct d}) (not_le.mp hD) _
          linarith [hFUniversal d, h₃', hn₁ d,hn₂ d,hn₄ d]
      · have hb := hReg d hd hR
        by_cases hD : d ∈ E₀
        · rw [if_pos hD] at hb
          change F d ≤ f₁ d at hb
          linarith [hn₂ d,hn₃ d,hn₄ d]
        · rw [if_neg hD,mul_zero,neg_zero,Real.exp_zero,mul_one] at hb
          have h₂' : f₂ d = A₀*V d := Set.indicator_of_mem hD _
          linarith [hn₁ d,hn₃ d,hn₄ d]
    · have h₄' : f₄ d = UB*W d := Set.indicator_of_mem hd _
      linarith [hFUniversal d, h₄', hn₁ d,hn₂ d,hn₃ d]
  have hFG : Summable (fun d => f₁ d + f₂ d + f₃ d + f₄ d) := ((h₁.add h₂).add h₃).add h₄
  have hF : Summable F := hFG.of_nonneg_of_le hF0 hMajor
  have h₁' : (∑' d, f₁ d) < ε/8 := by
    simpa only [f₁,tsum_mul_left] using hTsmall
  have h₂' : (∑' d, f₂ d) < ε/8 := by
    unfold f₂
    rw [← _root_.tsum_subtype,tsum_mul_left]
    have hh := mul_lt_mul_of_pos_left hE₀ hA₀
    have hEq : A₀*(ε/(8*A₀)) = ε/8 := by field_simp
    exact hEq ▸ hh
  have h₃' : (∑' d, f₃ d) < ε/8 := by
    unfold f₃
    rw [← _root_.tsum_subtype,tsum_mul_left]
    exact hTailB
  have h₄' : (∑' d, f₄ d) < ε/8 := by
    unfold f₄
    rw [← _root_.tsum_subtype,tsum_mul_left]
    have hh := mul_lt_mul_of_pos_left hE hUB
    have hEq : UB*(ε/(8*UB)) = ε/8 := by field_simp
    exact hEq ▸ hh
  change (∑' d, F d) < ε
  apply (hF.tsum_le_tsum hMajor hFG).trans_lt
  rw [((h₁.add h₂).add h₃).tsum_add h₄, (h₁.add h₂).tsum_add h₃, h₁.tsum_add h₂]
  linarith

end Erdos940Quartic

namespace Erdos940QuarticDominatedUpper

open Filter
open scoped Topology

/-- Termwise eventual upper estimates can be summed under a common
summable upper bound. The excess over the termwise bound tends to zero. -/
theorem eventually_tsum_le {α ι : Type} {l : Filter α}
    (f : α → ι → ℝ) (bound limit : ι → ℝ)
    (hbound : Summable bound) (hlimit : Summable limit)
    (hlim_nonneg : ∀ i, 0 ≤ limit i)
    (hmajor : ∀ x i, 0 ≤ f x i ∧ f x i ≤ bound i)
    (hpoint : ∀ i ε, 0 < ε → ∀ᶠ x in l, f x i ≤ limit i + ε)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x in l, (∑' i, f x i) ≤ (∑' i, limit i) + ε := by
  let E (x : α) (i : ι) := max (f x i - limit i) 0
  have hEn (x : α) (i : ι) : 0 ≤ E x i := le_max_right _ _
  have hEb (x : α) (i : ι) : E x i ≤ bound i := by
    apply max_le
    · linarith [(hmajor x i).2, hlim_nonneg i]
    · exact (hmajor x i).1.trans (hmajor x i).2
  have hEt (i : ι) : Tendsto (fun x => E x i) l (𝓝 0) := by
    refine tendsto_order.2 ⟨?_, ?_⟩
    · intro a ha
      exact Eventually.of_forall fun x => ha.trans_le (hEn x i)
    · intro a ha
      filter_upwards [hpoint i (a / 2) (by linarith)] with x hx
      apply max_lt
      · linarith
      · exact ha
  have hT : Tendsto (fun x => ∑' i, E x i) l (𝓝 0) := by
    simpa only [tsum_zero] using
      tendsto_tsum_of_dominated_convergence hbound hEt
        (Eventually.of_forall fun x i => by
          rw [Real.norm_eq_abs, abs_of_nonneg (hEn x i)]
          exact hEb x i)
  filter_upwards [hT.eventually (gt_mem_nhds hε)] with x hx
  have hS : Summable (E x) := hbound.of_nonneg_of_le (hEn x) (hEb x)
  have hf : Summable (f x) := hbound.of_nonneg_of_le (fun i => (hmajor x i).1)
    (fun i => (hmajor x i).2)
  have hle (i : ι) : f x i ≤ limit i + E x i := by
    have hh := le_max_left (f x i - limit i) 0
    change f x i - limit i ≤ E x i at hh
    linarith
  calc
    _ ≤ ∑' i, (limit i + E x i) := hf.tsum_le_tsum hle (hlimit.add hS)
    _ = (∑' i, limit i) + ∑' i, E x i := hlimit.tsum_add hS
    _ ≤ _ := add_le_add le_rfl hx.le

end Erdos940QuarticDominatedUpper

namespace Erdos940Quartic

open Finset Filter Erdos940QuarticWeights
open scoped Topology

private noncomputable def root4 (X : ℕ) : ℝ := (X : ℝ)^(1/4 : ℝ)
private noncomputable def singleScale (a : ℕ) : ℝ := (a : ℝ)^(-(1/4) : ℝ)
private noncomputable def cap (X a : ℕ) : ℕ := ⌊root4 X * singleScale a⌋₊

private theorem root4_pow (X : ℕ) : root4 X^4 = (X : ℝ) := by
  unfold root4
  rw [← Real.rpow_mul_natCast (by positivity)]
  norm_num

private theorem cap_le {X a : ℕ} : (cap X a : ℝ) ≤ root4 X * singleScale a :=
  Nat.floor_le (by unfold root4 singleScale; positivity)

private theorem coordinate_bound {X a x : ℕ} (ha : 0 < a) (h : a*x^4 ≤ X) :
    x ≤ cap X a := by
  have haR : 0 < (a : ℝ) := by exact_mod_cast ha
  have hR : (a : ℝ)*(x : ℝ)^4 ≤ (X : ℝ) := by exact_mod_cast h
  have hp := Real.rpow_le_rpow (by positivity) hR (by norm_num : (0 : ℝ) ≤ 1/4)
  rw [Real.mul_rpow (by positivity) (by positivity),
    ← Real.rpow_natCast_mul (by positivity : (0 : ℝ) ≤ x)] at hp
  norm_num at hp
  have ha' : 0 < (a : ℝ)^(1/4 : ℝ) := Real.rpow_pos_of_pos haR _
  apply (Nat.le_floor_iff (by unfold root4 singleScale; positivity)).mpr
  unfold root4 singleScale
  rw [Real.rpow_neg haR.le, ← div_eq_mul_inv]
  apply (le_div_iff₀ ha').mpr
  simpa only [mul_comm (x : ℝ)] using hp

private theorem prod_scales (d : Tuple) :
    (∏ i, singleScale (coeffs d i)) = scaleWeight d := by
  unfold scaleWeight coefficientProduct
  simp only [singleScale, Nat.cast_prod]
  exact Real.finsetProd_rpow Finset.univ (fun i : Fin 4 => (coeffs d i : ℝ))
    (fun _ _ => by positivity) _

private def boxValue (a : Fin 4 → ℕ) (x : Fin 4 → ℕ) : ℕ := ∑ i, a i*(x i)^4

private def Box (M u X : ℕ) (d : Tuple) :=
  {x : Fin 4 → ℕ // (∀ i, 0 < x i) ∧ boxValue (coeffs d) x ≤ X ∧
    (boxValue (coeffs d) x : ZMod M) = u}

private theorem box_coordinate {M u X : ℕ} {d : Tuple} (x : Box M u X d) (i : Fin 4) :
    x.val i ≤ cap X (coeffs d i) := by
  apply coordinate_bound (d i).property.1
  have hs : coeffs d i * (x.val i)^4 ≤ boxValue (coeffs d) x.val :=
    Finset.single_le_sum (f := fun j => coeffs d j * (x.val j)^4) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ i)
  exact hs.trans x.property.2.1

private def box_to_cap {M u X : ℕ} {d : Tuple} (x : Box M u X d) (i : Fin 4) :
    Fin (cap X (coeffs d i)) :=
  ⟨x.val i-1, by have hp := x.property.1 i; have hb := box_coordinate x i; omega⟩

private theorem box_to_cap_injective {M u X : ℕ} {d : Tuple} :
    Function.Injective (box_to_cap (M := M) (u := u) (X := X) (d := d)) := by
  intro x y h
  apply Subtype.ext
  funext i
  have he := congrArg (fun v => (v i).val) h
  change x.val i-1 = y.val i-1 at he
  have hx := x.property.1 i
  have hy := y.property.1 i
  omega

private theorem box_finite (M u X : ℕ) (d : Tuple) : Finite (Box M u X d) :=
  Finite.of_injective _ box_to_cap_injective

private noncomputable def boxRatio (M u X : ℕ) (d : Tuple) : ℝ :=
  (Nat.card (Box M u X d) : ℝ)/X

private theorem box_ratio_le (M u X : ℕ) (d : Tuple) : boxRatio M u X d ≤ scaleWeight d := by
  classical
  by_cases hX : X = 0
  · simp only [boxRatio, hX, Nat.cast_zero, div_zero]
    unfold scaleWeight
    positivity
  have hXR : 0 < (X : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hX
  have hNat := Nat.card_le_card_of_injective
    (box_to_cap (M := M) (u := u) (X := X) (d := d)) box_to_cap_injective
  rw [Nat.card_eq_fintype_card (α := ∀ i : Fin 4, Fin (cap X (coeffs d i))), Fintype.card_pi] at hNat
  simp only [Fintype.card_fin] at hNat
  unfold boxRatio
  apply (div_le_iff₀ hXR).mpr
  calc
    _ ≤ ∏ i, (cap X (coeffs d i) : ℝ) := by exact_mod_cast hNat
    _ ≤ ∏ i, root4 X * singleScale (coeffs d i) :=
      Finset.prod_le_prod (by intro i _; positivity) (fun _ _ => cap_le)
    _ = _ := by
      rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin,
        root4_pow,prod_scales,mul_comm]

private theorem nat_eq_of_residue_quotient {M x y : ℕ} [NeZero M]
    (hmod : (x : ZMod M) = (y : ZMod M)) (hdiv : x/M = y/M) : x = y := by
  have he := congrArg ZMod.val hmod
  rw [ZMod.val_natCast, ZMod.val_natCast] at he
  calc
    x = M*(x/M)+x%M := (Nat.div_add_mod x M).symm
    _ = M*(y/M)+y%M := by rw [he,hdiv]
    _ = y := Nat.div_add_mod y M

private theorem box_residue_bound {M : ℕ} [NeZero M] (u X : ℕ) (d : Tuple) :
    (Nat.card (Box M u X d) : ℝ) ≤
      (count (fun i => (coeffs d i : ZMod M)) (u : ZMod M) : ℝ) *
        ∏ i, (root4 X * singleScale (coeffs d i) / M + 1) := by
  classical
  let L := Solutions (fun i => (coeffs d i : ZMod M)) (u : ZMod M)
  let H (i : Fin 4) := cap X (coeffs d i) / M + 1
  let f (x : Box M u X d) : L × (∀ i : Fin 4, Fin (H i)) :=
    ⟨⟨fun i => x.val i, by
      simpa only [boxValue, Nat.cast_sum, Nat.cast_mul, Nat.cast_pow] using x.property.2.2⟩,
      fun i => ⟨x.val i / M, (Nat.div_le_div_right (box_coordinate x i)).trans_lt (Nat.lt_succ_self _)⟩⟩
  have hInj : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    funext i
    exact nat_eq_of_residue_quotient (congrArg (fun v => v.1.val i) h)
      (congrArg (fun v => (v.2 i).val) h)
  let : Fintype L := by
    unfold L Solutions
    infer_instance
  have hNat := Nat.card_le_card_of_injective f hInj
  rw [Nat.card_prod, Nat.card_eq_fintype_card (α := ∀ i : Fin 4, Fin (H i)), Fintype.card_pi] at hNat
  simp only [Fintype.card_fin] at hNat
  have hR : (Nat.card (Box M u X d) : ℝ) ≤ (Nat.card L : ℝ)*∏ i, (H i : ℝ) := by
    exact_mod_cast hNat
  have hH (i : Fin 4) : (H i : ℝ) ≤ root4 X * singleScale (coeffs d i)/M+1 := by
    change ((cap X (coeffs d i)/M + 1 : ℕ) : ℝ) ≤ _
    push_cast
    exact add_le_add_left
      (Nat.cast_div_le.trans (div_le_div_of_nonneg_right cap_le (by positivity))) 1
  exact hR.trans (mul_le_mul_of_nonneg_left
    (Finset.prod_le_prod (by intro i _; positivity) (fun i _ => hH i)) (by positivity))

/-- The residue-count box gives the correct upper bound in the limit. -/
private theorem eventual_box_ratio_le {M : ℕ} [NeZero M] (u : ℕ) (d : Tuple)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop, boxRatio M u X d ≤
      (scaleWeight d * localFactor M (coeffs d) u)/M + ε := by
  let N : ℝ := count (fun i => (coeffs d i : ZMod M)) (u : ZMod M)
  let h (i : Fin 4) (X : ℕ) := singleScale (coeffs d i) / M + (X : ℝ)^(-(1/4) : ℝ)
  have h₀ : Tendsto (fun X : ℕ => (X : ℝ)^(-(1/4) : ℝ)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1/4)).comp tendsto_natCast_atTop_atTop
  have h₁ (i : Fin 4) : Tendsto (h i) atTop (𝓝 (singleScale (coeffs d i)/M)) := by
    simpa only [add_zero] using h₀.const_add (singleScale (coeffs d i)/M)
  have hProd : Tendsto (fun X : ℕ => N * ∏ i, h i X) atTop
      (𝓝 (N * ∏ i, singleScale (coeffs d i)/M)) :=
    (tendsto_finsetProd _ (fun i _ => h₁ i)).const_mul N
  have hEq : (N * ∏ i, singleScale (coeffs d i)/M) =
      (scaleWeight d * localFactor M (coeffs d) u)/M := by
    unfold localFactor
    rw [Finset.prod_div_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin,prod_scales]
    change N*(scaleWeight d/(M : ℝ)^4) = (scaleWeight d*(N/(M : ℝ)^3))/M
    ring
  rw [hEq] at hProd
  have hev := hProd.eventually (gt_mem_nhds (lt_add_of_pos_right _ hε))
  filter_upwards [eventually_gt_atTop (0 : ℕ),hev] with X hX hlim
  have hXR : 0 < (X : ℝ) := by exact_mod_cast hX
  have hR : 0 < root4 X := Real.rpow_pos_of_pos hXR _
  have he (i : Fin 4) :
      root4 X * singleScale (coeffs d i)/M+1 = root4 X * h i X := by
    unfold h
    rw [Real.rpow_neg hXR.le]
    change root4 X*singleScale (coeffs d i)/M+1 =
      root4 X*(singleScale (coeffs d i)/M+(root4 X)⁻¹)
    field_simp
  have hBound := box_residue_bound (M := M) u X d
  have hNat : (Nat.card (Box M u X d) : ℝ) ≤ (N * ∏ i, h i X)*X := by
    calc
      _ ≤ N * ∏ i, (root4 X * singleScale (coeffs d i)/M+1) := hBound
      _ = _ := by
        simp_rw [he]
        rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin,root4_pow]
        ring
  exact ((div_le_iff₀ hXR).mpr hNat).trans hlim.le

end Erdos940Quartic


namespace Erdos940Quartic

open Finset Filter Erdos940QuarticWeights Erdos940QuarticCanonicalKernel
open scoped Topology

private theorem scaleWeight_nonneg (d : Tuple) : 0 ≤ scaleWeight d := by
  unfold scaleWeight
  positivity

private theorem summable_scaleWeight : Summable scaleWeight :=
  (summable_tuple_weight (s := 1/4) (by norm_num)).of_nonneg_of_le scaleWeight_nonneg fun d => by
    unfold tupleWeight Erdos940QuarticWeights.numberWeight scaleWeight
    nth_rewrite 1 [← one_mul ((coefficientProduct d : ℝ)^(-(1/4) : ℝ))]
    exact mul_le_mul_of_nonneg_right (one_le_pow₀ (by norm_num)) (by positivity)

private theorem summable_singleScale : Summable (fun d : Kernel => singleScale d.val) :=
  (summable_kernel_weight (s := 1/4) (by norm_num)).of_nonneg_of_le
    (fun d => by unfold singleScale; positivity) fun d => by
      unfold Erdos940QuarticWeights.numberWeight singleScale
      nth_rewrite 1 [← one_mul ((d.val : ℝ)^(-(1/4) : ℝ))]
      exact mul_le_mul_of_nonneg_right (one_le_pow₀ (by norm_num)) (by positivity)

private noncomputable def localRatio (M u : ℕ) (d : Tuple) : ℝ :=
  (scaleWeight d * localFactor M (coeffs d) u)/M

private theorem boxRatio_nonneg (M u X : ℕ) (d : Tuple) : 0 ≤ boxRatio M u X d := by
  unfold boxRatio
  positivity

private theorem summable_boxRatio (M u X : ℕ) : Summable (boxRatio M u X) :=
  summable_scaleWeight.of_nonneg_of_le (boxRatio_nonneg M u X) (box_ratio_le M u X)

private theorem localRatio_nonneg (M u : ℕ) (d : Tuple) : 0 ≤ localRatio M u d :=
  div_nonneg (mul_nonneg (scaleWeight_nonneg d) (localFactor_nonneg _ _ _)) (by positivity)

private theorem localRatio_le {M : ℕ} [NeZero M] (u : ℕ) (d : Tuple) :
    localRatio M u d ≤ scaleWeight d := by
  have hM : 0 < (M : ℝ) := by exact_mod_cast NeZero.pos M
  apply (div_le_iff₀ hM).mpr
  exact mul_le_mul_of_nonneg_left (localFactor_le_modulus M (coeffs d) u) (scaleWeight_nonneg d)

private theorem summable_localRatio {M : ℕ} [NeZero M] (u : ℕ) : Summable (localRatio M u) :=
  summable_scaleWeight.of_nonneg_of_le (localRatio_nonneg M u) (localRatio_le u)

private theorem eventual_box_sum {M : ℕ} [NeZero M] (u : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop, (∑' d, boxRatio M u X d) ≤ (∑' d, localRatio M u d)+ε :=
  Erdos940QuarticDominatedUpper.eventually_tsum_le (fun X => boxRatio M u X) scaleWeight (localRatio M u)
    summable_scaleWeight (summable_localRatio u) (localRatio_nonneg M u)
    (fun X d => ⟨boxRatio_nonneg M u X d,box_ratio_le M u X d⟩)
    (fun d _ h => eventual_box_ratio_le u d h) hε

/-- Integers that are sums of four positive fourth-full numbers. -/
private def FourPositive : Set ℕ := {n | ∃ a : Fin 4 → ℕ,
  (∀ i, 0 < a i ∧ (4 : ℕ).Full (a i)) ∧ n = ∑ i, a i}

private def valueSet (M u X : ℕ) : Set ℕ :=
  {n | n ∈ FourPositive ∧ n ≤ X ∧ (n : ZMod M) = u}

private theorem valueSet_finite (M u X : ℕ) : (valueSet M u X).Finite :=
  (Set.finite_Iic X).subset fun _ h => h.2.1

private theorem exists_box_of_value {M u X n : ℕ} (hn : n ∈ valueSet M u X) :
    ∃ (d : Tuple) (v : Box M u X d), boxValue (coeffs d) v.val = n := by
  rcases hn with ⟨⟨a,ha,hsum⟩,hX,hmod⟩
  have h (i : Fin 4) : ∃ x k : ℕ, 0 < x ∧ IsKernel 4 k ∧ a i = x^4*k := by
    obtain ⟨⟨x,k⟩,hxk,_⟩ := exists_unique_kernel (r := 4) (by decide) (ha i).1 (ha i).2
    exact ⟨x,k,hxk⟩
  choose x k hx hk he using h
  let d (i : Fin 4) : Kernel := ⟨k i,hk i⟩
  have hS : boxValue (coeffs d) x = n := by
    unfold boxValue
    rw [hsum]
    apply Finset.sum_congr rfl
    intro i _
    exact (mul_comm _ _).trans (he i).symm
  exact ⟨d,⟨x,hx,hS.trans_le hX,(congrArg (fun n : ℕ => (n : ZMod M)) hS).trans hmod⟩,hS⟩

private theorem value_ratio_le_box_sum (M u X : ℕ) :
    ((valueSet M u X).ncard : ℝ)/X ≤ ∑' d, boxRatio M u X d := by
  classical
  let V := valueSet M u X
  let : Fintype V := (valueSet_finite M u X).fintype
  choose d v hv using fun n : V => exists_box_of_value n.property
  let S : Finset Tuple := Finset.univ.image d
  let F (p : S) := Box M u X p.val
  let hfin (p : S) : Finite (F p) := box_finite M u X p.val
  let input (n : V) : Sigma F := ⟨⟨d n,mem_image.mpr ⟨n,mem_univ _,rfl⟩⟩, v n⟩
  let output (p : Sigma F) : ℕ := boxValue (coeffs p.1.val) p.2.val
  have hinj : Function.Injective input := by
    intro x y h
    apply Subtype.ext
    exact (hv x).symm.trans ((congrArg output h).trans (hv y))
  have hcard := Nat.card_le_card_of_injective input hinj
  rw [Nat.card_sigma] at hcard
  have hNat : V.ncard ≤ ∑ p ∈ S, Nat.card (Box M u X p) := by
    rw [Set.ncard_def]
    exact hcard.trans_eq (Finset.sum_attach S (fun d => Nat.card (Box M u X d)))
  calc
    _ ≤ (↑(∑ p ∈ S, Nat.card (Box M u X p)) : ℝ)/X :=
      div_le_div_of_nonneg_right (by exact_mod_cast hNat) (by positivity)
    _ = ∑ p ∈ S, boxRatio M u X p := by rw [Nat.cast_sum,Finset.sum_div]; rfl
    _ ≤ _ := (summable_boxRatio M u X).sum_le_tsum S fun d _ => boxRatio_nonneg M u X d

private theorem eventual_value_ratio {M : ℕ} [NeZero M] (u : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop, ((valueSet M u X).ncard : ℝ)/X ≤ (∑' d, localRatio M u d)+ε := by
  filter_upwards [eventual_box_sum (M := M) u hε] with X hX
  exact (value_ratio_le_box_sum M u X).trans hX

private def smallFull (X : ℕ) : Set ℕ := {n | n ≤ X ∧ (4 : ℕ).Full n}
private def smallPosFull (X : ℕ) : Set ℕ := {n | 0 < n ∧ n ≤ X ∧ (4 : ℕ).Full n}

private theorem smallFull_finite (X : ℕ) : (smallFull X).Finite :=
  (Set.finite_Iic X).subset (fun _ h => h.1)

private theorem smallPosFull_finite (X : ℕ) : (smallPosFull X).Finite :=
  (Set.finite_Iic X).subset (fun _ h => h.2.1)

private theorem smallPosFull_upper (X : ℕ) :
    ((smallPosFull X).ncard : ℝ) ≤ root4 X * (∑' d : Kernel, singleScale d.val) := by
  classical
  let V := smallPosFull X
  let : Fintype V := (smallPosFull_finite X).fintype
  have hDec (n : V) : ∃ x : ℕ, ∃ d : Kernel, 0 < x ∧ n.val = x^4*d.val := by
    obtain ⟨⟨x,d⟩,⟨hx,hd,he⟩,_⟩ := exists_unique_kernel (r := 4) (by decide) n.property.1 n.property.2.2
    exact ⟨x,⟨d,hd⟩,hx,he⟩
  choose x d hx he using hDec
  let S : Finset Kernel := Finset.univ.image d
  let F (k : S) := Fin (cap X k.val.val)
  let input (n : V) : Sigma F :=
    ⟨⟨d n,mem_image.mpr ⟨n,mem_univ _,rfl⟩⟩, ⟨x n-1,by
      have h := coordinate_bound (d n).property.1 (x := x n) (X := X)
        (by rw [mul_comm,← he n]; exact n.property.2.1)
      have hp := hx n
      change x n-1 < cap X (d n).val
      omega⟩⟩
  let output (p : Sigma F) := (p.2.val+1)^4*p.1.val.val
  have he' (n : V) : output (input n) = n.val := by
    change (x n-1+1)^4*(d n).val = n.val
    rw [Nat.sub_add_cancel (hx n)]
    exact (he n).symm
  have hInj : Function.Injective input := by
    intro x y h
    apply Subtype.ext
    exact (he' x).symm.trans ((congrArg output h).trans (he' y))
  have hh := Nat.card_le_card_of_injective input hInj
  rw [Nat.card_sigma] at hh
  simp only [F,Nat.card_fin] at hh
  have hh' : (smallPosFull X).ncard ≤ ∑ k ∈ S, cap X k.val := by
    rw [Set.ncard_def]
    exact hh.trans_eq (Finset.sum_attach S (fun k => cap X k.val))
  calc
    _ ≤ ∑ k ∈ S, (cap X k.val : ℝ) := by exact_mod_cast hh'
    _ ≤ ∑ k ∈ S, root4 X*singleScale k.val := Finset.sum_le_sum fun _ _ => cap_le
    _ ≤ _ := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (summable_singleScale.sum_le_tsum S (fun _ _ => by
        unfold singleScale; positivity)) (by unfold root4; positivity)

private theorem smallFull_upper (X : ℕ) (hX : 0 < X) :
    ((smallFull X).ncard : ℝ) ≤ ((∑' d : Kernel, singleScale d.val)+1)*root4 X := by
  have hSub : smallFull X ⊆ insert 0 (smallPosFull X) := by
    intro n hn
    by_cases h : n=0
    · simp [h]
    · exact Or.inr ⟨Nat.pos_of_ne_zero h,hn⟩
  have hD := (Set.ncard_le_ncard hSub ((smallPosFull_finite X).insert _)).trans
    (Set.ncard_insert_le _ _)
  have hD' : ((smallFull X).ncard : ℝ) ≤ ((smallPosFull X).ncard : ℝ)+1 := by exact_mod_cast hD
  have hR : 1 ≤ root4 X := Real.one_le_rpow (by exact_mod_cast hX) (by norm_num)
  linarith [smallPosFull_upper X]

end Erdos940Quartic

namespace Erdos940Quartic

open Finset Filter Erdos940QuarticWeights
open scoped Topology

private def ThreeWeak : Set ℕ := {n | ∃ a b c : ℕ,
  (4 : ℕ).Full a ∧ (4 : ℕ).Full b ∧ (4 : ℕ).Full c ∧ n=a+b+c}

private theorem threeWeak_count_bound (X : ℕ) (hX : 0 < X) :
    ((ThreeWeak ∩ Set.Iio X).ncard : ℝ) ≤
      (((∑' d : Kernel, singleScale d.val)+1)*root4 X)^3 := by
  classical
  let B := (smallFull_finite X).toFinset
  let A := (B ×ˢ B ×ˢ B).image (fun a : ℕ × ℕ × ℕ => a.1+a.2.1+a.2.2)
  have hS : ThreeWeak ∩ Set.Iio X ⊆ (A : Set ℕ) := by
    intro n hn
    obtain ⟨⟨a,b,c,ha,hb,hc,he⟩,hn⟩ := hn
    have hX : n<X := hn
    apply Finset.mem_image.mpr
    refine ⟨(a,b,c),Finset.mem_product.mpr ⟨?_, Finset.mem_product.mpr ⟨?_,?_⟩⟩,he.symm⟩
    · exact (smallFull_finite X).mem_toFinset.mpr (show a ∈ smallFull X from ⟨by omega,ha⟩)
    · exact (smallFull_finite X).mem_toFinset.mpr (show b ∈ smallFull X from ⟨by omega,hb⟩)
    · exact (smallFull_finite X).mem_toFinset.mpr (show c ∈ smallFull X from ⟨by omega,hc⟩)
  have hCard : A.card ≤ B.card^3 := by
    calc
      _ ≤ (B ×ˢ B ×ˢ B).card := Finset.card_image_le
      _ = _ := by simp [Finset.card_product,pow_succ]; ring
  have hW : ((ThreeWeak ∩ Set.Iio X).ncard : ℝ) ≤ (B.card : ℝ)^3 := by
    have h := (Set.ncard_le_ncard hS A.finite_toSet)
    rw [Set.ncard_coe_finset] at h
    exact_mod_cast h.trans hCard
  have hB : (B.card : ℝ) ≤ ((∑' d : Kernel, singleScale d.val)+1)*root4 X := by
    simpa only [B, Set.ncard_eq_toFinset_card (smallFull X) (smallFull_finite X)] using smallFull_upper X hX
  exact hW.trans (pow_le_pow_left₀ (by positivity) hB _)

private theorem eventually_threeWeak_ratio (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop, ((ThreeWeak ∩ Set.Iio X).ncard : ℝ)/X < ε := by
  let C := ((∑' d : Kernel, singleScale d.val)+1)^3
  have h := ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1/4)).comp
        tendsto_natCast_atTop_atTop).const_mul C
  have ht : Tendsto (fun X : ℕ => C*(X : ℝ)^(-(1/4) : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_apply,mul_zero] using h
  filter_upwards [eventually_gt_atTop (0 : ℕ),ht.eventually (gt_mem_nhds hε)] with X hX hSmall
  have hXR : 0 < (X : ℝ) := by exact_mod_cast hX
  apply lt_of_le_of_lt _ hSmall
  apply (div_le_iff₀ hXR).mpr
  have hP : root4 X^3 = (X : ℝ)^(3/4 : ℝ) := by
    unfold root4
    rw [← Real.rpow_mul_natCast hXR.le]
    norm_num
  have hR : (X : ℝ)^(-(1/4) : ℝ)*X = (X : ℝ)^(3/4 : ℝ) := by
    nth_rewrite 2 [← Real.rpow_one (X : ℝ)]
    rw [← Real.rpow_add hXR]
    norm_num
  have h := threeWeak_count_bound X hX
  rw [mul_pow,hP] at h
  rwa [mul_assoc,hR]

private theorem threeWeak_of_le_three {n : ℕ} {S : Multiset ℕ} (hS : S.card≤3)
    (hFull : ∀ x ∈ S, (4 : ℕ).Full x) (hEq : n=S.sum) : n ∈ ThreeWeak := by
  have h : S.card=0 ∨ S.card=1 ∨ S.card=2 ∨ S.card=3 := by omega
  rcases h with h | h | h | h
  · rw [Multiset.card_eq_zero.mp h] at hEq
    exact ⟨0,0,0,Nat.Full.zero_right _,Nat.Full.zero_right _,Nat.Full.zero_right _,by simpa using hEq⟩
  · obtain ⟨a,rfl⟩ := Multiset.card_eq_one.mp h
    exact ⟨a,0,0,hFull a (by simp),Nat.Full.zero_right _,Nat.Full.zero_right _,by simpa using hEq⟩
  · obtain ⟨a,b,rfl⟩ := Multiset.card_eq_two.mp h
    exact ⟨a,b,0,hFull a (by simp),hFull b (by simp),Nat.Full.zero_right _,by simpa using hEq⟩
  · obtain ⟨a,b,c,rfl⟩ := Multiset.card_eq_three.mp h
    exact ⟨a,b,c,hFull a (by simp),hFull b (by simp),hFull c (by simp),by simpa [add_assoc] using hEq⟩

private theorem atMostFour_split {n : ℕ} (h : ∃ S : Multiset ℕ, S.card≤4 ∧
    (∀ x ∈ S, (4 : ℕ).Full x) ∧ n=S.sum) : n ∈ ThreeWeak ∨ n ∈ FourPositive := by
  obtain ⟨S,hS,hFull,hSum⟩ := h
  by_cases h3 : S.card≤3
  · exact Or.inl (threeWeak_of_le_three h3 hFull hSum)
  have h4 : S.card=4 := by omega
  obtain ⟨a,b,c,d,rfl⟩ := Multiset.card_eq_four.mp h4
  have ha := hFull a (by simp)
  have hb := hFull b (by simp)
  have hc := hFull c (by simp)
  have hd := hFull d (by simp)
  have hSum' : n=a+b+c+d := by simpa [add_assoc] using hSum
  by_cases ha0 : a=0
  · exact Or.inl ⟨b,c,d,hb,hc,hd,by simpa [ha0] using hSum'⟩
  by_cases hb0 : b=0
  · exact Or.inl ⟨a,c,d,ha,hc,hd,by simpa [hb0] using hSum'⟩
  by_cases hc0 : c=0
  · exact Or.inl ⟨a,b,d,ha,hb,hd,by simpa [hc0] using hSum'⟩
  by_cases hd0 : d=0
  · exact Or.inl ⟨a,b,c,ha,hb,hc,by simpa [hd0] using hSum'⟩
  apply Or.inr
  refine ⟨![a,b,c,d],?_ ,?_⟩
  · intro i
    fin_cases i
    · exact ⟨Nat.pos_of_ne_zero ha0,ha⟩
    · exact ⟨Nat.pos_of_ne_zero hb0,hb⟩
    · exact ⟨Nat.pos_of_ne_zero hc0,hc⟩
    · exact ⟨Nat.pos_of_ne_zero hd0,hd⟩
  · rw [Fin.sum_univ_four]
    exact hSum'

-- The progression bounds are the same as in the cubic proof.
private def progression (M u X : ℕ) : Set ℕ := {n | n < X ∧ (n : ZMod M) = u}

private theorem progression_card_lower {M : ℕ} [NeZero M] (u X : ℕ) :
    X / M ≤ (progression M u X).ncard := by
  have hfin : (progression M u X).Finite := (Set.finite_Iio X).subset fun _ h => h.1
  let := hfin.to_subtype
  let v := (u : ZMod M).val
  have hv : v < M := ZMod.val_lt _
  let f (k : Fin (X / M)) : progression M u X :=
    ⟨v + M * k.val, by
      constructor
      · calc
          _ < M + M * k.val := Nat.add_lt_add_right hv _
          _ = M * (k.val + 1) := by ring
          _ ≤ M * (X / M) := Nat.mul_le_mul_left M k.isLt
          _ ≤ X := by simpa only [Nat.mul_comm] using Nat.div_mul_le_self X M
      · simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul, add_zero]
        exact ZMod.natCast_zmod_val _⟩
  have hf : Function.Injective f := by
    intro a b h
    have he : v + M * a.val = v + M * b.val := congrArg Subtype.val h
    exact Fin.ext (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (NeZero.ne M))
      (Nat.add_left_cancel he))
  simpa only [Nat.card_fin, Nat.card_coe_set_eq] using Nat.card_le_card_of_injective f hf

private theorem progression_density_lower {M u X : ℕ} [NeZero M] (hX : 2 * M ≤ X) :
    1 / (2 * (M : ℝ)) ≤ ((progression M u X).ncard : ℝ) / X := by
  have hM : 0 < (M : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)
  have hXR : 2 * (M : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hXpos : 0 < (X : ℝ) := by linarith
  have hrem : ((X % M : ℕ) : ℝ) < (M : ℝ) := by exact_mod_cast Nat.mod_lt X (Nat.pos_of_ne_zero (NeZero.ne M))
  have hdiv : (M : ℝ) * ((X / M : ℕ) : ℝ) + ((X % M : ℕ) : ℝ) = X := by
    exact_mod_cast Nat.div_add_mod X M
  have hCount : ((X / M : ℕ) : ℝ) ≤ (progression M u X).ncard := by
    exact_mod_cast progression_card_lower (M := M) u X
  apply (le_div_iff₀ hXpos).mpr
  have h : (X : ℝ) ≤ (2 * (M : ℝ)) * (progression M u X).ncard := by
    nlinarith [mul_le_mul_of_nonneg_left hCount hM.le]
  rw [div_mul_eq_mul_div, one_mul]
  exact (div_le_iff₀ (by positivity : 0 < 2 * (M : ℝ))).mpr
    (by simpa only [mul_comm] using h)

private theorem progression_eventually_representable_bound {K : ℕ}
    (hK : ∀ n ≥ K, ∃ S : Multiset ℕ, S.card≤4 ∧
      (∀ x ∈ S, (4 : ℕ).Full x) ∧ n=S.sum) (M u X : ℕ) :
    (progression M u X).ncard ≤
      (valueSet M u X).ncard + (ThreeWeak ∩ Set.Iio X).ncard + K := by
  let V := valueSet M u X
  let W := ThreeWeak ∩ Set.Iio X
  have hSub : progression M u X ⊆ (V ∪ W) ∪ Set.Iio K := by
    intro n hn
    have hX : n<X := hn.1
    by_cases hk : K≤n
    · rcases atMostFour_split (hK n hk) with h₁ | h₂
      · exact Or.inl (Or.inr ⟨h₁,hX⟩)
      · exact Or.inl (Or.inl ⟨h₂,hX.le,hn.2⟩)
    · exact Or.inr (lt_of_not_ge hk)
  have hV : V.Finite := valueSet_finite M u X
  have hW : W.Finite := (Set.finite_Iio X).inter_of_right _
  have hFin := (hV.union hW).union (Set.finite_Iio K)
  have hC := (Set.ncard_le_ncard hSub hFin).trans (Set.ncard_union_le _ _)
  have hA := Set.ncard_union_le V W
  simp at hC
  exact hC.trans (Nat.add_le_add_right hA _)

/-- The quartic infinitude assertion follows from the regular analytic
Euler-product estimate alone. -/
theorem not_eventually_quartic_of_regularEulerBound (hBaseline : RegularEulerBound) :
    ¬ ∀ᶠ n : ℕ in atTop, ∃ S : Multiset ℕ, S.card≤4 ∧
      (∀ x ∈ S, (4 : ℕ).Full x) ∧ n=S.sum := by
  intro h
  obtain ⟨K,hK⟩ := eventually_atTop.mp h
  obtain ⟨Q,u,hQ,_,hSum⟩ := exists_small_weighted_local_sum hBaseline (1/8) (by norm_num)
  let M := primeSystemModulus Q
  have hMp : 0 < M := primeSystemModulus_pos hQ
  have hMr : 0 < (M : ℝ) := by exact_mod_cast hMp
  let : NeZero M := ⟨hMp.ne'⟩
  let ε := 1/(8*(M : ℝ))
  have hε : 0 < ε := by positivity
  have hLoc : (∑' d, localRatio M u d) < ε := by
    unfold localRatio
    rw [tsum_div_const]
    apply (div_lt_iff₀ hMr).mpr
    have hEq : ε*(M : ℝ) = 1/8 := by unfold ε; field_simp
    rw [hEq]
    exact hSum
  have hV := eventual_value_ratio (M := M) u hε
  have hThree := eventually_threeWeak_ratio ε hε
  have hKlim : Tendsto (fun X : ℕ => (K : ℝ)/(X : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (K : ℝ)
  have hFinal : ∀ᶠ X : ℕ in atTop, False := by
    filter_upwards [eventually_ge_atTop (2*M),hV,hThree,hKlim.eventually (gt_mem_nhds hε)] with
      X hX hV' hThree' hFinite
    have hProg := progression_density_lower (M := M) (u := u) hX
    have hC := progression_eventually_representable_bound hK M u X
    have hC' : ((progression M u X).ncard : ℝ)/X ≤
        ((valueSet M u X).ncard : ℝ)/X +
          ((ThreeWeak ∩ Set.Iio X).ncard : ℝ)/X + (K : ℝ)/X := by
      rw [← add_div,← add_div]
      exact div_le_div_of_nonneg_right (by exact_mod_cast hC) (by positivity)
    have h4 : 4*ε = 1/(2*(M : ℝ)) := by unfold ε; field_simp; norm_num
    linarith
  obtain ⟨_,hf⟩ := hFinal.exists
  exact hf

end Erdos940Quartic



namespace Erdos940Quartic

open Finset Erdos940QuarticWeights

/-- The coefficient of (p-1)/p² in the normalized zero-target count. -/
private noncomputable def primeTrace (a : Fin 4 → ℕ) (p : ℕ) : ℝ :=
  ((count (fun i => (a i : ZMod p)) 0 : ℝ)-(p : ℝ)^3)/((p : ℝ)*((p : ℝ)-1))

theorem valuationOneFactor_eq_trace {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (a : Fin 4 → ℕ) (ha : ∀ i, (4 : ℕ).Full (a i)) (hg : ∀ i, ¬p ∣ a i) :
    valuationOneFactor a p =
      1 + primeTrace a p * ((p : ℝ)-1)/(p : ℝ)^2 - 1/(p : ℝ)^3 := by
  classical
  let S := Solutions (fun i => (a i : ZMod p)) (0 : ZMod p)
  let N : ℕ := Nat.card S
  let : Nonempty S := ⟨⟨fun _ => 0,by simp⟩⟩
  let : Finite S := by
    unfold S Solutions
    infer_instance
  have hN : 1 ≤ N := Nat.card_pos
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).two_le
  have hpPos : (0 : ℝ) < p := by linarith
  have hpOne : (p : ℝ) - 1 ≠ 0 := by linarith
  unfold valuationOneFactor
  rw [valuation_one_count_good hp2 a ha hg]
  change ((p^3*(N-1) : ℕ) : ℝ)/(p : ℝ)^6 = _
  rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_sub hN, Nat.cast_one]
  change (p : ℝ)^3*((N : ℝ)-1)/(p : ℝ)^6 =
    1+(((N : ℝ)-(p : ℝ)^3)/((p : ℝ)*((p : ℝ)-1)))*((p : ℝ)-1)/(p : ℝ)^2-1/(p : ℝ)^3
  field_simp
  ring

theorem trace_abs_le {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (a : Fin 4 → ℕ) (hg : ∀ i, ¬p ∣ a i) : |primeTrace a p| ≤ 21 := by
  let N := count (fun i => (a i : ZMod p)) 0
  let u : ℂ := (N : ℂ)-(p : ℂ)^3
  have hRe : u.re = (N : ℝ)-(p : ℝ)^3 := by
    simp [u, pow_succ, Complex.sub_re, Complex.mul_re, Complex.mul_im]
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).two_le
  have hpPos : (0 : ℝ) < p := by linarith
  have hpOne : 0 < (p : ℝ)-1 := by linarith
  have hpOdd := ((Fact.out : p.Prime).mod_two_eq_one_iff_ne_two).mpr hp2
  have hgood : ∀ i, (a i : ZMod p) ≠ 0 :=
    fun i h => hg i ((ZMod.natCast_eq_zero_iff _ _).mp h)
  have hNorm : ‖u‖ ≤ 21*(p : ℝ)*((p : ℝ)-1) := by
    rcases Nat.odd_mod_four_iff.mp hpOdd with h1 | h3
    · exact split_zero_count_bound h1 _ hgood
    · have he : u = quadraticComplex (ZMod p) (∏ i, (a i : ZMod p)) *(p : ℂ)*((p : ℂ)-1) := by
        dsimp [u,N]
        rw [inert_zero_count h3 _ hgood]
        ring
      have hgProd : (∏ i, (a i : ZMod p)) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr (fun i _ => hgood i)
      have hChi := mulChar_norm_one (quadraticComplex (ZMod p)) hgProd
      rw [he, norm_mul,norm_mul,hChi,one_mul,Complex.norm_natCast]
      have hAbs : ‖(p : ℂ)-1‖ = (p : ℝ)-1 := by
        rw [show (p : ℂ)-1 = ((p : ℝ)-1 : ℝ) by push_cast; rfl, Complex.norm_real,
          Real.norm_eq_abs,abs_of_pos hpOne]
      rw [hAbs]
      nlinarith
  have hOne : |(N : ℝ)-(p : ℝ)^3| ≤ 21*(p : ℝ)*((p : ℝ)-1) :=
    hRe ▸ (Complex.abs_re_le_norm u).trans hNorm
  unfold primeTrace
  rw [abs_div, abs_of_pos (mul_pos hpPos hpOne)]
  apply (div_le_iff₀ (mul_pos hpPos hpOne)).mpr
  simpa only [mul_assoc] using hOne

private theorem trace_local_le_exp {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (a : Fin 4 → ℕ) (ha : ∀ i, (4 : ℕ).Full (a i)) (hg : ∀ i, ¬p ∣ a i) :
    valuationOneFactor a p ≤ Real.exp (primeTrace a p/(p : ℝ)+21/(p : ℝ)^2) := by
  have hpPos : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hNeg : -21 ≤ primeTrace a p := neg_le_of_abs_le (trace_abs_le hp2 a hg)
  have hDiv := div_le_div_of_nonneg_right hNeg (by positivity : (0 : ℝ) ≤ (p : ℝ)^2)
  rw [valuationOneFactor_eq_trace hp2 a ha hg]
  calc
    _ = 1+primeTrace a p/(p : ℝ)-primeTrace a p/(p : ℝ)^2-1/(p : ℝ)^3 := by field_simp; ring
    _ ≤ 1+(primeTrace a p/(p : ℝ)+21/(p : ℝ)^2) := by
      rw [neg_div] at hDiv
      linarith [show 0 ≤ (1 : ℝ)/(p : ℝ)^3 by positivity]
    _ ≤ _ := by rw [add_comm 1]; exact Real.add_one_le_exp _

private noncomputable def goodPrimeTraceSum (B : ℕ) (a : Fin 4 → ℕ) : ℝ :=
  ∑ p ∈ (oddPrimesThrough B).filter (fun p => ¬p ∣ ∏ i, a i), primeTrace a p/(p : ℝ)

/-- This is the signed prime-harmonic bound required from the Gaussian
Hecke-character argument. The research result has a stronger log-log bound. -/
private def RegularPrimeTraceBound : Prop :=
  ∃ C : ℝ, ∀ B : ℕ, ∀ d : Tuple, ¬PrincipalType (coeffs d) →
    goodPrimeTraceSum B (coeffs d) ≤ C + (1/100)*Real.log (coefficientProduct d)

/-- All local normalization and summation-error terms are accounted for
when passing from the signed trace estimate to the Euler-product estimate. -/
theorem regularEulerBound_of_primeTraceBound (h : RegularPrimeTraceBound) : RegularEulerBound := by
  obtain ⟨C,hC⟩ := h
  have hSumInvSq : Summable (fun n : ℕ => (n : ℝ)^(-(2 : ℝ))) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  let S := ∑' n : ℕ, (n : ℝ)^(-(2 : ℝ))
  refine ⟨Real.exp (C+21*S),Real.exp_pos _,?_⟩
  intro B d hReg
  classical
  let Q := (oddPrimesThrough B).filter (fun p => ¬p ∣ ∏ i, coeffs d i)
  have hE : (∏ p ∈ Q, valuationOneFactor (coeffs d) p) ≤
      Real.exp (∑ p ∈ Q, (primeTrace (coeffs d) p/(p : ℝ)+21/(p : ℝ)^2)) := by
    rw [Real.exp_sum]
    apply Finset.prod_le_prod (fun p _ => valuationOneFactor_nonneg _ p)
    intro p hp
    obtain ⟨hB,hBad⟩ := Finset.mem_filter.mp hp
    obtain ⟨hPrime,h₂⟩ := oddPrimesThrough_odd B p hB
    let : Fact p.Prime := ⟨hPrime⟩
    exact trace_local_le_exp h₂ _ (coeffs_full d) (odd_good_prime_of_not_dvd_product _ hBad)
  have hSq : (∑ p ∈ Q, 21/(p : ℝ)^2) ≤ 21*S := by
    have hF (p : ℕ) : 21/(p : ℝ)^2 = 21*(p : ℝ)^(-(2 : ℝ)) := by
      rw [Real.rpow_neg (by positivity),div_eq_mul_inv,Real.rpow_two]
    simp_rw [hF,← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hSumInvSq.sum_le_tsum Q
      (fun p _ => Real.rpow_nonneg (by positivity) _)) (by norm_num)
  change (∏ p ∈ Q, valuationOneFactor (coeffs d) p) ≤ _
  apply hE.trans
  have hD : 0 < (coefficientProduct d : ℝ) := by exact_mod_cast coefficientProduct_pos d
  rw [Real.rpow_def_of_pos hD,← Real.exp_add]
  apply Real.exp_le_exp.mpr
  rw [Finset.sum_add_distrib]
  have he : (∑ p ∈ Q, primeTrace (coeffs d) p/(p : ℝ)) ≤
      C+(1/100)*Real.log (coefficientProduct d) := hC B d hReg
  linarith

theorem not_eventually_quartic_of_regularPrimeTraceBound (h : RegularPrimeTraceBound) :
    ¬ ∀ᶠ n : ℕ in Filter.atTop, ∃ S : Multiset ℕ, S.card≤4 ∧
      (∀ x ∈ S, (4 : ℕ).Full x) ∧ n=S.sum :=
  not_eventually_quartic_of_regularEulerBound (regularEulerBound_of_primeTraceBound h)

end Erdos940Quartic



namespace Erdos940Quartic

open Finset Erdos940QuarticWeights

private noncomputable def quadraticComponent (a : Fin 4 → ℕ) (p : ℕ) : ℝ :=
  (jacobiSym ((∏ i, a i : ℕ) : ℤ) p : ℝ)

private theorem trace_eq_quadraticComponent {p : ℕ} [Fact p.Prime] (hp : p % 4 = 3)
    (a : Fin 4 → ℕ) (hg : ∀ i, ¬p ∣ a i) :
    primeTrace a p = quadraticComponent a p := by
  let N := count (fun i => (a i : ZMod p)) 0
  have hD : 0 < (p : ℝ)*((p : ℝ)-1) := by
    have hp' : (2 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).two_le
    exact mul_pos (by linarith) (by linarith)
  have hgood : ∀ i, (a i : ZMod p) ≠ 0 := fun i h => hg i ((ZMod.natCast_eq_zero_iff _ _).mp h)
  have hC := inert_zero_count hp (fun i => (a i : ZMod p)) hgood
  have hχ : quadraticComplex (ZMod p) (∏ i, (a i : ZMod p)) =
      (legendreSym p ((∏ i, a i : ℕ) : ℤ) : ℂ) := by
    simp only [quadratic_apply,legendreSym,Int.cast_natCast,Int.cast_prod,Nat.cast_prod]
  rw [hχ] at hC
  have hRe : (N : ℝ) = (p : ℝ)^3 +
      (legendreSym p ((∏ i, a i : ℕ) : ℤ) : ℝ)*(p : ℝ)*((p : ℝ)-1) := by
    simpa [N,pow_succ,Complex.mul_re,Complex.mul_im,Complex.add_re,
      Complex.sub_re,Complex.sub_im] using congrArg Complex.re hC
  unfold primeTrace quadraticComponent
  rw [← jacobiSym.legendreSym.to_jacobiSym]
  change ((N : ℝ)-(p : ℝ)^3)/((p : ℝ)*((p : ℝ)-1)) = _
  apply (div_eq_iff hD.ne').mpr
  rw [hRe]
  ring

private noncomputable def goodQuadraticSum (B : ℕ) (a : Fin 4 → ℕ) : ℝ :=
  ∑ p ∈ (oddPrimesThrough B).filter (fun p => ¬p ∣ ∏ i, a i),
    quadraticComponent a p/(p : ℝ)

private noncomputable def goodSplitCorrection (B : ℕ) (a : Fin 4 → ℕ) : ℝ :=
  ∑ p ∈ (oddPrimesThrough B).filter (fun p => ¬p ∣ ∏ i, a i ∧ p%4=1),
    (primeTrace a p-quadraticComponent a p)/(p : ℝ)

private theorem goodPrimeTraceSum_split (B : ℕ) (a : Fin 4 → ℕ) :
    goodPrimeTraceSum B a = goodQuadraticSum B a + goodSplitCorrection B a := by
  classical
  let Q := (oddPrimesThrough B).filter (fun p => ¬p ∣ ∏ i, a i)
  have hSet : (oddPrimesThrough B).filter (fun p => ¬p ∣ ∏ i, a i ∧ p%4=1) =
      Q.filter (fun p => p%4=1) := by
    ext p
    simp only [Q,Finset.mem_filter]
    tauto
  unfold goodPrimeTraceSum goodQuadraticSum goodSplitCorrection
  rw [hSet]
  have hEq : (∑ p ∈ Q.filter (fun p => p%4=1),
        (primeTrace a p-quadraticComponent a p)/(p : ℝ)) =
      ∑ p ∈ Q, if p%4=1 then (primeTrace a p-quadraticComponent a p)/(p : ℝ) else 0 := by
    rw [Finset.sum_filter]
  change (∑ p ∈ Q, primeTrace a p/(p : ℝ)) =
    (∑ p ∈ Q, quadraticComponent a p/(p : ℝ)) +
      ∑ p ∈ Q.filter (fun p => p%4=1), (primeTrace a p-quadraticComponent a p)/(p : ℝ)
  rw [hEq,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  obtain ⟨hpq,hpD⟩ := Finset.mem_filter.mp hp
  obtain ⟨hpPrime,hp2⟩ := oddPrimesThrough_odd B p hpq
  let : Fact p.Prime := ⟨hpPrime⟩
  by_cases hp1 : p%4=1
  · rw [if_pos hp1]
    ring
  · rw [if_neg hp1,add_zero]
    have hOdd := (hpPrime.mod_two_eq_one_iff_ne_two).mpr hp2
    have hp3 := (Nat.odd_mod_four_iff.mp hOdd).resolve_left hp1
    rw [trace_eq_quadraticComponent hp3 a (odd_good_prime_of_not_dvd_product a hpD)]

/-- The rational quadratic contribution to the signed prime-harmonic estimate. -/
private def RegularQuadraticBound : Prop :=
  ∃ C : ℝ, ∀ B : ℕ, ∀ d : Tuple, ¬IsSquare (coefficientProduct d) →
    goodQuadraticSum B (coeffs d) ≤ C+(1/200)*Real.log (coefficientProduct d)

/-- The remaining Gaussian-character part of the signed prime-harmonic estimate. -/
private def RegularSplitCorrectionBound : Prop :=
  ∃ C : ℝ, ∀ B : ℕ, ∀ d : Tuple, ¬PrincipalType (coeffs d) →
    goodSplitCorrection B (coeffs d) ≤ C+(1/200)*Real.log (coefficientProduct d)

theorem primeTraceBound_of_quadratic_and_split (hQ : RegularQuadraticBound)
    (hS : RegularSplitCorrectionBound) : RegularPrimeTraceBound := by
  obtain ⟨C,hC⟩ := hQ
  obtain ⟨D,hD⟩ := hS
  refine ⟨C+D,?_⟩
  intro B d hd
  have hn : ¬IsSquare (coefficientProduct d) := fun h => hd (Or.inl h)
  have hc := hC B d hn
  have hs := hD B d hd
  rw [goodPrimeTraceSum_split]
  linarith

theorem not_eventually_quartic_of_quadratic_and_split
    (hQ : RegularQuadraticBound) (hS : RegularSplitCorrectionBound) :
    ¬ ∀ᶠ n : ℕ in Filter.atTop, ∃ S : Multiset ℕ, S.card≤4 ∧
      (∀ x ∈ S, (4 : ℕ).Full x) ∧ n=S.sum :=
  not_eventually_quartic_of_regularPrimeTraceBound (primeTraceBound_of_quadratic_and_split hQ hS)

end Erdos940Quartic

namespace OMA.R_Erdos940_erdos_940_variants_large_integers_R1_H2_R1

open Finset

/-- Uniform prime-harmonic bound for the rational quadratic component. -/
def H1 : Prop :=
  ∃ C : ℝ, ∀ (B : ℕ) (a : Fin 4 → ℕ),
    (∀ i, 0 < a i ∧ ∀ p, (a i).factorization p = 0 ∨
      4 < (a i).factorization p ∧ (a i).factorization p < 8) →
    let D := ∏ i, a i
    ¬IsSquare D →
      (∑ p ∈ (((Finset.range (B+1)).filter Nat.Prime).erase 2).filter (fun p => ¬p ∣ D),
        (jacobiSym (D : ℤ) p : ℝ)/(p : ℝ)) ≤ C+(1/200)*Real.log D

/-- Uniform signed prime-harmonic bound for the remaining split-prime terms. -/
def H2 : Prop :=
  ∃ C : ℝ, ∀ (B : ℕ) (a : Fin 4 → ℕ),
    (∀ i, 0 < a i ∧ ∀ p, (a i).factorization p = 0 ∨
      4 < (a i).factorization p ∧ (a i).factorization p < 8) →
    let D := ∏ i, a i
    ¬(IsSquare D ∨ ∃ (σ : Equiv.Perm (Fin 4)) (w : ℚ),
      (a (σ 0) : ℚ)*(a (σ 1) : ℚ)^3*(a (σ 2) : ℚ)^2*(a (σ 3) : ℚ)^2 = 4*w^4) →
      (∑ p ∈ (((Finset.range (B+1)).filter Nat.Prime).erase 2).filter
        (fun p => ¬p ∣ D ∧ p%4=1),
        let N := Nat.card {x : Fin 4 → ZMod p // (∑ i, (a i : ZMod p)*(x i)^4)=0}
        (((N : ℝ)-(p : ℝ)^3)/((p : ℝ)*((p : ℝ)-1))-
          (jacobiSym (D : ℤ) p : ℝ))/(p : ℝ)) ≤ C+(1/200)*Real.log D

theorem main : H1 → H2 → OMA.R_Erdos940_erdos_940_variants_large_integers_R1.H2 := by
  intro h₁ h₂
  apply Erdos940Quartic.not_eventually_quartic_of_quadratic_and_split
  · obtain ⟨C,hC⟩ := h₁
    refine ⟨C,fun B d hd => ?_⟩
    exact hC B (fun i => (d i).val) (fun i => (d i).property) hd
  · obtain ⟨C,hC⟩ := h₂
    refine ⟨C,fun B d hd => ?_⟩
    exact hC B (fun i => (d i).val) (fun i => (d i).property) hd

end OMA.R_Erdos940_erdos_940_variants_large_integers_R1_H2_R1
