import OMAReductions.R_CongruentNumber_Tunnell_odd_R1
import Mathlib

/-!
Elementary proof that every rational torsion point on the congruent-number elliptic curve
`E_n : y^2 = x^3 - n^2 * x` (for `n : ℕ`, `n ≠ 0`) satisfies `2 • P = 0`.

1. No point of order 4: doubling formula forces `((x - n) / n)^2 = 2` in `ℚ`, impossible.
2. Point count over `ZMod p` for primes `p ≡ 3 [MOD 4]` not dividing `n`:
   `|E_n(ZMod p)| = p + 1` via `quadraticChar_card_sqrts` and oddness of `x^3 - n^2 * x`.
3. No point of odd prime order `q`: pick a prime `p ≡ 2*q + 1 [MOD 4*q]` larger than all
   denominators and relevant numerators (Dirichlet's theorem); reduction mod `p` yields an
   injective homomorphism `ZMod q →+ E_n(ZMod p)`, forcing `q ∣ p + 1`, contradicting
   `p ≡ 1 [MOD q]`.
4. Combine (1) and (3) to deduce `addOrderOf P ∣ 2`, hence `2 • P = 0`.
-/

namespace CongruentNumberTorsionH1

private abbrev E (n : ℕ) : WeierstrassCurve ℚ :=
  ⟨0, 0, 0, -((n : ℚ) ^ 2), 0⟩

private abbrev Ep (n p : ℕ) : WeierstrassCurve (ZMod p) :=
  ⟨0, 0, 0, -((n : ZMod p) ^ 2), 0⟩

/- ### Basic algebraic helpers for `E n` -/

private lemma E_equation_iff (n : ℕ) (x y : ℚ) :
    (E n).toAffine.Equation x y ↔ y ^ 2 = x ^ 3 - (n : ℚ) ^ 2 * x := by
  rw [WeierstrassCurve.Affine.equation_iff]
  dsimp [E, WeierstrassCurve.toAffine]
  constructor <;> intro h <;> linarith

private lemma E_negY (n : ℕ) (x y : ℚ) :
    (E n).toAffine.negY x y = -y := by
  simp [WeierstrassCurve.Affine.negY]

private lemma two_nsmul_some_eq_zero_iff {n : ℕ} {x y : ℚ}
    {h : (E n).toAffine.Nonsingular x y} :
    (2 : ℕ) • (WeierstrassCurve.Affine.Point.some x y h) = 0 ↔ y = 0 := by
  rw [two_nsmul, add_eq_zero_iff_eq_neg, WeierstrassCurve.Affine.Point.neg_some,
    WeierstrassCurve.Affine.Point.some.injEq, E_negY]
  exact ⟨fun ⟨_, hy⟩ => by linarith, fun hy => ⟨rfl, by linarith⟩⟩

private lemma rat_sq_ne_two (r : ℚ) : r ^ 2 ≠ 2 := by
  intro hr
  have hden : (r.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr r.den_nz
  have h1 : (r.num : ℚ) ^ 2 = 2 * (r.den : ℚ) ^ 2 := by
    have hq : (r.num : ℚ) / (r.den : ℚ) = r := r.num_div_den
    rw [← hq, div_pow] at hr
    exact (div_eq_iff (pow_ne_zero 2 hden)).mp hr
  have h1z : r.num ^ 2 = 2 * (r.den : ℤ) ^ 2 := by exact_mod_cast h1
  have h1n : r.num.natAbs ^ 2 = 2 * r.den ^ 2 := by
    have h2 : ((r.num.natAbs ^ 2 : ℕ) : ℤ) = ((2 * r.den ^ 2 : ℕ) : ℤ) := by
      push_cast
      rw [sq_abs]
      exact h1z
    exact_mod_cast h2
  have h2num : 2 ∣ r.num.natAbs :=
    Nat.Prime.dvd_of_dvd_pow Nat.prime_two ⟨r.den ^ 2, h1n⟩
  rcases h2num with ⟨k, hk⟩
  have h2den : 2 ∣ r.den := by
    have hsq : r.den ^ 2 = 2 * k ^ 2 := by nlinarith
    exact Nat.Prime.dvd_of_dvd_pow Nat.prime_two ⟨k ^ 2, hsq⟩
  have hgcd : 2 ∣ Nat.gcd r.num.natAbs r.den := Nat.dvd_gcd ⟨k, hk⟩ h2den
  rw [r.reduced] at hgcd
  omega

/- ### Step 1: No rational point of order 4 -/

private lemma no_order_four (n : ℕ) (hn : n ≠ 0) (P : (E n).toAffine.Point)
    (h2 : (2 : ℕ) • P ≠ 0) (h4 : (4 : ℕ) • P = 0) : False := by
  rcases P with _ | ⟨x, y, hns⟩
  · exact h2 (nsmul_zero 2)
  have h4' : (2 : ℕ) • ((2 : ℕ) • (WeierstrassCurve.Affine.Point.some x y hns)) = 0 := by
    have hmul : (4 : ℕ) = 2 * 2 := rfl
    rw [hmul, mul_nsmul] at h4
    exact h4
  have heq : y ^ 2 = x ^ 3 - (n : ℚ) ^ 2 * x := (E_equation_iff n x y).mp hns.1
  have hy : y ≠ 0 := mt two_nsmul_some_eq_zero_iff.mpr h2
  have hyneg : y ≠ (E n).toAffine.negY x y := by
    rw [E_negY]
    intro h
    exact hy (by linarith)
  obtain ⟨x₂, y₂, hns₂, h2P, hx₂_def⟩ :
      ∃ (x₂ y₂ : ℚ) (hns₂ : (E n).toAffine.Nonsingular x₂ y₂),
        (2 : ℕ) • (WeierstrassCurve.Affine.Point.some x y hns) =
          WeierstrassCurve.Affine.Point.some x₂ y₂ hns₂ ∧
        x₂ = (E n).toAffine.addX x x ((E n).toAffine.slope x x y y) :=
    ⟨_, _, _, by rw [two_nsmul]; exact WeierstrassCurve.Affine.Point.add_self_of_Y_ne hyneg, rfl⟩
  have h2_2P : (2 : ℕ) • (WeierstrassCurve.Affine.Point.some x₂ y₂ hns₂) = 0 := by
    rw [← h2P]
    exact h4'
  have hy₂ : y₂ = 0 := two_nsmul_some_eq_zero_iff.mp h2_2P
  have heq₂ : x₂ ^ 3 - (n : ℚ) ^ 2 * x₂ = 0 := by
    have h := (E_equation_iff n x₂ y₂).mp hns₂.1
    rw [hy₂] at h
    linarith
  have h2y : (2 : ℚ) * y ≠ 0 := mul_ne_zero (by norm_num) hy
  have hx₂ : x₂ = ((x ^ 2 + (n : ℚ) ^ 2) / (2 * y)) ^ 2 := by
    rw [hx₂_def]
    dsimp only [WeierstrassCurve.Affine.addX]
    rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hyneg]
    dsimp only [E, WeierstrassCurve.toAffine, WeierstrassCurve.Affine.negY]
    rw [show y - (-y - 0 * x - 0) = 2 * y by ring]
    field_simp [h2y]
    linear_combination -8 * x * heq
  have hnq_pos : (0 : ℚ) < (n : ℚ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hnq_ne : (n : ℚ) ≠ 0 := ne_of_gt hnq_pos
  have hfac : x₂ * (x₂ - (n : ℚ)) * (x₂ + (n : ℚ)) = 0 := by linear_combination heq₂
  rcases mul_eq_zero.mp hfac with h0 | hneg
  · rcases mul_eq_zero.mp h0 with hx0 | hxn
    · rw [hx₂] at hx0
      have hdiv0 : (x ^ 2 + (n : ℚ) ^ 2) / (2 * y) = 0 := sq_eq_zero_iff.mp hx0
      have hsum0 : x ^ 2 + (n : ℚ) ^ 2 = 0 := (div_eq_zero_iff.mp hdiv0).resolve_right h2y
      nlinarith [sq_nonneg x]
    · have hx₂_eq : x₂ = (n : ℚ) := sub_eq_zero.mp hxn
      rw [hx₂_eq] at hx₂
      have h4y : (x ^ 2 + (n : ℚ) ^ 2) ^ 2 = 4 * (n : ℚ) * y ^ 2 := by
        rw [div_pow] at hx₂
        have h := (eq_div_iff (pow_ne_zero 2 h2y)).mp hx₂
        linear_combination -h
      have hsq0 : (x ^ 2 - 2 * (n : ℚ) * x - (n : ℚ) ^ 2) ^ 2 = 0 := by
        linear_combination h4y + 4 * (n : ℚ) * heq
      have hquad : x ^ 2 - 2 * (n : ℚ) * x - (n : ℚ) ^ 2 = 0 := sq_eq_zero_iff.mp hsq0
      have hsq2 : ((x - (n : ℚ)) / (n : ℚ)) ^ 2 = 2 := by
        field_simp [hnq_ne]
        linear_combination hquad
      exact rat_sq_ne_two _ hsq2
  · have hx₂_eq : x₂ = -(n : ℚ) := eq_neg_of_add_eq_zero_left hneg
    have hx₂_nn : 0 ≤ x₂ := by rw [hx₂]; exact sq_nonneg _
    linarith

/- ### Step 2: Point count `|E_n(ZMod p)| = p + 1` for `p ≡ 3 [MOD 4]`, `p ∤ n` -/

private def pointEquivOption {R : Type*} [CommRing R] (W : WeierstrassCurve.Affine R) :
    W.Point ≃ Option {xy : R × R // W.Nonsingular xy.1 xy.2} where
  toFun
    | .zero => none
    | .some x y h => some ⟨(x, y), h⟩
  invFun
    | none => .zero
    | some ⟨(x, y), h⟩ => .some x y h
  left_inv := by rintro (_ | ⟨x, y, h⟩) <;> rfl
  right_inv := by rintro (_ | ⟨⟨x, y⟩, h⟩) <;> rfl

private lemma Ep_equation_iff (n p : ℕ) (x y : ZMod p) :
    (Ep n p).toAffine.Equation x y ↔ y ^ 2 = x ^ 3 - (n : ZMod p) ^ 2 * x := by
  rw [WeierstrassCurve.Affine.equation_iff]
  dsimp [Ep, WeierstrassCurve.toAffine]
  constructor <;> intro h <;> linear_combination h

private lemma Ep_negY (n p : ℕ) (x y : ZMod p) :
    (Ep n p).toAffine.negY x y = -y := by
  simp [WeierstrassCurve.Affine.negY]

private lemma zmod_two_ne_zero (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using h)
  have hle := Nat.le_of_dvd (by norm_num) hdvd
  have hp_ge := (Fact.out : p.Prime).two_le
  omega

private lemma Ep_nonsingular_of_equation (n p : ℕ) [Fact p.Prime]
    (hp2 : p ≠ 2) (hnp : (n : ZMod p) ≠ 0) {x y : ZMod p}
    (heq : (Ep n p).toAffine.Equation x y) : (Ep n p).toAffine.Nonsingular x y := by
  have h2 : (2 : ZMod p) ≠ 0 := zmod_two_ne_zero p hp2
  rw [WeierstrassCurve.Affine.nonsingular_iff']
  refine ⟨heq, ?_⟩
  have heq' : y ^ 2 = x ^ 3 - (n : ZMod p) ^ 2 * x := (Ep_equation_iff n p x y).mp heq
  by_cases hy : y = 0
  · left
    dsimp [Ep, WeierstrassCurve.toAffine]
    intro hder
    have h3 : 3 * x ^ 2 = (n : ZMod p) ^ 2 := by linear_combination -hder
    rw [hy] at heq'
    have hfac : x * (x - (n : ZMod p)) * (x + (n : ZMod p)) = 0 := by linear_combination -heq'
    rcases mul_eq_zero.mp hfac with h0 | h1
    · rcases mul_eq_zero.mp h0 with hx0 | hxn
      · rw [hx0] at h3
        have : (n : ZMod p) ^ 2 = 0 := by linear_combination -h3
        exact hnp (sq_eq_zero_iff.mp this)
      · have hx : x = (n : ZMod p) := sub_eq_zero.mp hxn
        rw [hx] at h3
        have : (2 : ZMod p) * (n : ZMod p) ^ 2 = 0 := by linear_combination h3
        exact mul_ne_zero h2 (pow_ne_zero 2 hnp) this
    · have hx : x = -(n : ZMod p) := eq_neg_of_add_eq_zero_left h1
      rw [hx] at h3
      have : (2 : ZMod p) * (n : ZMod p) ^ 2 = 0 := by linear_combination h3
      exact mul_ne_zero h2 (pow_ne_zero 2 hnp) this
  · right
    dsimp [Ep, WeierstrassCurve.toAffine]
    have h2y : 2 * y + 0 * x + 0 = 2 * y := by ring
    rw [h2y]
    exact mul_ne_zero h2 hy

private lemma card_Ep_point (n p : ℕ) [Fact p.Prime] [Fintype (Ep n p).toAffine.Point]
    (hp4 : p % 4 = 3) (hnp : (n : ZMod p) ≠ 0) :
    Fintype.card (Ep n p).toAffine.Point = p + 1 := by
  classical
  let W := (Ep n p).toAffine
  let f : ZMod p → ZMod p := fun x => x ^ 3 - (n : ZMod p) ^ 2 * x
  have hp2 : p ≠ 2 := by omega
  have hchar : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    exact hp2
  have h1 : Fintype.card W.Point =
      Fintype.card (Option {xy : ZMod p × ZMod p // W.Nonsingular xy.1 xy.2}) :=
    Fintype.card_congr (pointEquivOption W)
  have h2 : Fintype.card (Option {xy : ZMod p × ZMod p // W.Nonsingular xy.1 xy.2}) =
      Fintype.card {xy : ZMod p × ZMod p // W.Nonsingular xy.1 xy.2} + 1 :=
    Fintype.card_option
  let e : {xy : ZMod p × ZMod p // W.Nonsingular xy.1 xy.2} ≃
      Σ x : ZMod p, {y : ZMod p // y ^ 2 = f x} :=
    { toFun := fun ⟨⟨x, y⟩, h⟩ => ⟨x, ⟨y, (Ep_equation_iff n p x y).mp h.1⟩⟩
      invFun := fun ⟨x, ⟨y, h⟩⟩ =>
        ⟨⟨x, y⟩, Ep_nonsingular_of_equation n p hp2 hnp ((Ep_equation_iff n p x y).mpr h)⟩
      left_inv := fun ⟨⟨_, _⟩, _⟩ => rfl
      right_inv := fun ⟨_, ⟨_, _⟩⟩ => rfl }
  have h3 : Fintype.card {xy : ZMod p × ZMod p // W.Nonsingular xy.1 xy.2} =
      ∑ x : ZMod p, Fintype.card {y : ZMod p // y ^ 2 = f x} := by
    rw [Fintype.card_congr e, Fintype.card_sigma]
  have hsum_int : ((∑ x : ZMod p, Fintype.card {y : ZMod p // y ^ 2 = f x} : ℕ) : ℤ) = p := by
    push_cast
    have hterm : ∀ x : ZMod p,
        ((Fintype.card {y : ZMod p // y ^ 2 = f x} : ℕ) : ℤ) =
          quadraticChar (ZMod p) (f x) + 1 := by
      intro x
      have hcard : Fintype.card {y : ZMod p // y ^ 2 = f x} =
          {y : ZMod p | y ^ 2 = f x}.toFinset.card := by
        rw [Set.toFinset_card]
        exact Fintype.card_congr (Equiv.subtypeEquivRight fun _ => Iff.rfl)
      rw [hcard]
      exact quadraticChar_card_sqrts hchar (f x)
    simp_rw [hterm, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, ZMod.card,
      nsmul_eq_mul, mul_one]
    have hchi_neg : quadraticChar (ZMod p) (-1) = -1 := by
      rw [quadraticChar_neg_one_iff_not_isSquare, FiniteField.isSquare_neg_one_iff, ZMod.card]
      omega
    have hS : ∑ x : ZMod p, quadraticChar (ZMod p) (f x) = 0 := by
      have hsym : ∑ x : ZMod p, quadraticChar (ZMod p) (f x) =
          ∑ x : ZMod p, quadraticChar (ZMod p) (f (-x)) :=
        (Equiv.sum_comp (Equiv.neg (ZMod p)) (fun x => quadraticChar (ZMod p) (f x))).symm
      have hneg : ∀ x : ZMod p,
          quadraticChar (ZMod p) (f (-x)) = -quadraticChar (ZMod p) (f x) := by
        intro x
        have hfneg : f (-x) = (-1) * f x := by dsimp [f]; ring
        rw [hfneg, map_mul, hchi_neg, neg_one_mul]
      simp_rw [hneg, Finset.sum_neg_distrib] at hsym
      linarith
    rw [hS, zero_add]
  have hsum : ∑ x : ZMod p, Fintype.card {y : ZMod p // y ^ 2 = f x} = p := by
    exact_mod_cast hsum_int
  change Fintype.card W.Point = p + 1
  omega

/- ### Step 3: `p`-adic reduction of rationals and ruling out odd prime orders -/

private def Good (p : ℕ) (r : ℚ) : Prop :=
  (r.den : ZMod p) ≠ 0

private noncomputable def red (p : ℕ) (r : ℚ) : ZMod p :=
  (r.num : ZMod p) * (r.den : ZMod p)⁻¹

private lemma good_and_red_of_eq_div {p : ℕ} [Fact p.Prime] {r : ℚ} {a b : ℤ}
    (hb : (b : ZMod p) ≠ 0) (hr : r = (a : ℚ) / (b : ℚ)) :
    Good p r ∧ red p r = (a : ZMod p) / (b : ZMod p) := by
  have hb0 : b ≠ 0 := by
    intro h
    rw [h, Int.cast_zero] at hb
    exact hb rfl
  have hb0q : (b : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hb0
  have hden0q : (r.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr r.den_nz
  have hcross_q : (r.num : ℚ) * (b : ℚ) = (a : ℚ) * (r.den : ℚ) := by
    have hq : (r.num : ℚ) / (r.den : ℚ) = (a : ℚ) / (b : ℚ) := by
      rw [r.num_div_den, hr]
    field_simp [hden0q, hb0q] at hq
    linarith
  have hcross : r.num * b = a * (r.den : ℤ) := by exact_mod_cast hcross_q
  have hdvd_nat : r.den ∣ b.natAbs := by
    have hmul : r.den ∣ r.num.natAbs * b.natAbs := by
      have : r.num.natAbs * b.natAbs = a.natAbs * r.den := by
        rw [← Int.natAbs_mul, hcross, Int.natAbs_mul, Int.natAbs_natCast]
      exact ⟨a.natAbs, by rw [this, mul_comm]⟩
    exact r.reduced.symm.dvd_of_dvd_mul_left hmul
  have hgood : Good p r := by
    intro hden_zero
    have hpdvd : p ∣ r.den := (ZMod.natCast_eq_zero_iff r.den p).mp hden_zero
    have hpb : p ∣ b.natAbs := dvd_trans hpdvd hdvd_nat
    have hpbz : (p : ℤ) ∣ b := Int.natCast_dvd.mpr hpb
    exact hb ((ZMod.intCast_zmod_eq_zero_iff_dvd b p).mpr hpbz)
  refine ⟨hgood, ?_⟩
  have hcross_p : (r.num : ZMod p) * (b : ZMod p) = (a : ZMod p) * (r.den : ZMod p) := by
    have h := congrArg (Int.cast (R := ZMod p)) hcross
    simpa using h
  unfold red
  rw [div_eq_mul_inv]
  have hmul_eq : (r.num : ZMod p) * (r.den : ZMod p)⁻¹ * ((r.den : ZMod p) * (b : ZMod p)) =
      (a : ZMod p) * (b : ZMod p)⁻¹ * ((r.den : ZMod p) * (b : ZMod p)) := by
    calc (r.num : ZMod p) * (r.den : ZMod p)⁻¹ * ((r.den : ZMod p) * (b : ZMod p))
        = (r.num : ZMod p) * ((r.den : ZMod p)⁻¹ * (r.den : ZMod p)) * (b : ZMod p) := by ring
      _ = (r.num : ZMod p) * (b : ZMod p) := by rw [inv_mul_cancel₀ hgood, mul_one]
      _ = (a : ZMod p) * (r.den : ZMod p) := hcross_p
      _ = (a : ZMod p) * ((b : ZMod p)⁻¹ * (b : ZMod p)) * (r.den : ZMod p) := by
          rw [inv_mul_cancel₀ hb, mul_one]
      _ = (a : ZMod p) * (b : ZMod p)⁻¹ * ((r.den : ZMod p) * (b : ZMod p)) := by ring
  exact mul_right_cancel₀ (mul_ne_zero hgood hb) hmul_eq

private lemma good_and_red_intCast (p : ℕ) [Fact p.Prime] (k : ℤ) :
    Good p (k : ℚ) ∧ red p (k : ℚ) = (k : ZMod p) := by
  have h := good_and_red_of_eq_div (p := p) (r := (k : ℚ)) (a := k) (b := 1)
    (by simp) (by simp)
  simpa using h

private lemma good_and_red_natCast (p : ℕ) [Fact p.Prime] (k : ℕ) :
    Good p (k : ℚ) ∧ red p (k : ℚ) = (k : ZMod p) := by
  simpa using good_and_red_intCast p (k : ℤ)

private lemma good_and_red_add {p : ℕ} [Fact p.Prime] {r s : ℚ}
    (hr : Good p r) (hs : Good p s) :
    Good p (r + s) ∧ red p (r + s) = red p r + red p s := by
  have hb : (((r.den : ℤ) * (s.den : ℤ) : ℤ) : ZMod p) ≠ 0 := by
    push_cast
    exact mul_ne_zero hr hs
  have hrq : r + s = (((r.num * (s.den : ℤ) + s.num * (r.den : ℤ) : ℤ) : ℚ)) /
      (((r.den : ℤ) * (s.den : ℤ) : ℤ) : ℚ) := by
    have h1 : (r.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr r.den_nz
    have h2 : (s.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr s.den_nz
    conv_lhs => rw [← r.num_div_den, ← s.num_div_den]
    push_cast
    field_simp [h1, h2]
  obtain ⟨hg, hred⟩ := good_and_red_of_eq_div hb hrq
  refine ⟨hg, ?_⟩
  rw [hred]
  unfold red
  unfold Good at hr hs
  push_cast
  field_simp [hr, hs]

private lemma good_and_red_neg {p : ℕ} [Fact p.Prime] {r : ℚ} (hr : Good p r) :
    Good p (-r) ∧ red p (-r) = -red p r := by
  have hb : (((r.den : ℤ) : ZMod p)) ≠ 0 := by
    unfold Good at hr
    simpa using hr
  have hrq : -r = (((-r.num : ℤ) : ℚ)) / (((r.den : ℤ) : ℚ)) := by
    conv_lhs => rw [← r.num_div_den]
    push_cast
    ring
  obtain ⟨hg, hred⟩ := good_and_red_of_eq_div hb hrq
  refine ⟨hg, ?_⟩
  rw [hred]
  unfold red
  push_cast
  ring

private lemma good_and_red_sub {p : ℕ} [Fact p.Prime] {r s : ℚ}
    (hr : Good p r) (hs : Good p s) :
    Good p (r - s) ∧ red p (r - s) = red p r - red p s := by
  rw [sub_eq_add_neg, sub_eq_add_neg]
  obtain ⟨hg_neg, hred_neg⟩ := good_and_red_neg hs
  obtain ⟨hg, hred⟩ := good_and_red_add hr hg_neg
  exact ⟨hg, by rw [hred, hred_neg]⟩

private lemma good_and_red_mul {p : ℕ} [Fact p.Prime] {r s : ℚ}
    (hr : Good p r) (hs : Good p s) :
    Good p (r * s) ∧ red p (r * s) = red p r * red p s := by
  have hb : (((r.den : ℤ) * (s.den : ℤ) : ℤ) : ZMod p) ≠ 0 := by
    push_cast
    exact mul_ne_zero hr hs
  have hrq : r * s = (((r.num * s.num : ℤ) : ℚ)) /
      (((r.den : ℤ) * (s.den : ℤ) : ℤ) : ℚ) := by
    conv_lhs => rw [← r.num_div_den, ← s.num_div_den]
    push_cast
    ring
  obtain ⟨hg, hred⟩ := good_and_red_of_eq_div hb hrq
  refine ⟨hg, ?_⟩
  rw [hred]
  unfold red
  push_cast
  field_simp [hr, hs]

private lemma good_and_red_div {p : ℕ} [Fact p.Prime] {r s : ℚ}
    (hr : Good p r) (hs0 : red p s ≠ 0) :
    Good p (r / s) ∧ red p (r / s) = red p r / red p s := by
  have hsnum : (s.num : ZMod p) ≠ 0 := by
    intro h
    apply hs0
    unfold red
    rw [h, zero_mul]
  have hsnum0 : (s.num : ℚ) ≠ 0 := by
    intro h
    have h0 : s.num = 0 := by exact_mod_cast h
    rw [h0, Int.cast_zero] at hsnum
    exact hsnum rfl
  have hb : (((r.den : ℤ) * s.num : ℤ) : ZMod p) ≠ 0 := by
    push_cast
    exact mul_ne_zero hr hsnum
  have hrq : r / s = (((r.num * (s.den : ℤ) : ℤ) : ℚ)) /
      (((r.den : ℤ) * s.num : ℤ) : ℚ) := by
    have h1 : (r.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr r.den_nz
    have h2 : (s.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr s.den_nz
    conv_lhs => rw [← r.num_div_den, ← s.num_div_den]
    push_cast
    field_simp [h1, h2, hsnum0]
  obtain ⟨hg, hred⟩ := good_and_red_of_eq_div hb hrq
  refine ⟨hg, ?_⟩
  rw [hred]
  unfold red
  push_cast
  field_simp [hr, hsnum]

private lemma good_and_red_pow {p : ℕ} [Fact p.Prime] {r : ℚ} (hr : Good p r) :
    ∀ k : ℕ, Good p (r ^ k) ∧ red p (r ^ k) = red p r ^ k
  | 0 => by simpa using good_and_red_natCast p 1
  | k + 1 => by
    obtain ⟨hgk, hredk⟩ := good_and_red_pow hr k
    obtain ⟨hg, hred⟩ := good_and_red_mul hgk hr
    exact ⟨by simpa [pow_succ] using hg, by simpa [pow_succ, hredk] using hred⟩

private lemma good_of_den_lt {p : ℕ} [Fact p.Prime] {r : ℚ} (h : r.den < p) : Good p r := by
  intro h0
  have hd : p ∣ r.den := (ZMod.natCast_eq_zero_iff r.den p).mp h0
  have hle : p ≤ r.den := Nat.le_of_dvd (Nat.pos_of_ne_zero r.den_nz) hd
  omega

private lemma red_ne_zero_of_lt {p : ℕ} [Fact p.Prime] {r : ℚ}
    (hr : Good p r) (hr0 : r ≠ 0) (h : r.num.natAbs < p) : red p r ≠ 0 := by
  intro hred
  have hnum0 : (r.num : ZMod p) = 0 := by
    unfold red at hred
    exact (mul_eq_zero.mp hred).resolve_right (inv_ne_zero hr)
  have hpdvd_z : (p : ℤ) ∣ r.num := (ZMod.intCast_zmod_eq_zero_iff_dvd r.num p).mp hnum0
  have hpdvd : p ∣ r.num.natAbs := Int.natCast_dvd.mp hpdvd_z
  have hpos : 0 < r.num.natAbs := Int.natAbs_pos.mpr (Rat.num_ne_zero.mpr hr0)
  have hle : p ≤ r.num.natAbs := Nat.le_of_dvd hpos hpdvd
  omega

private def ptX {F : Type*} [Field F] {W : WeierstrassCurve F} : W.toAffine.Point → F
  | .zero => 0
  | .some x _ _ => x

private def ptY {F : Type*} [Field F] {W : WeierstrassCurve F} : W.toAffine.Point → F
  | .zero => 0
  | .some _ y _ => y

private lemma pt_eq_some_of_ne_zero {F : Type*} [Field F] {W : WeierstrassCurve F}
    {Q : W.toAffine.Point} (hQ : Q ≠ 0) :
    ∃ h : W.toAffine.Nonsingular (ptX Q) (ptY Q), Q = .some (ptX Q) (ptY Q) h := by
  rcases Q with _ | ⟨x, y, h⟩
  · exact (hQ rfl).elim
  · exact ⟨h, rfl⟩

private lemma no_odd_prime_order (n : ℕ) (hn : n ≠ 0) (q : ℕ) (hq : q.Prime) (hq2 : q ≠ 2)
    (P : (E n).toAffine.Point) (hP0 : P ≠ 0) (hqP : q • P = 0) : False := by
  have : Fact q.Prime := ⟨hq⟩
  have hq3 : 3 ≤ q := by
    have := hq.two_le
    omega
  have hq_odd : q % 2 = 1 := by
    rcases hq.eq_two_or_odd with h | h
    · exact (hq2 h).elim
    · exact h
  have hord : addOrderOf P = q := by
    have hdvd : addOrderOf P ∣ q := addOrderOf_dvd_of_nsmul_eq_zero hqP
    rcases (Nat.dvd_prime hq).mp hdvd with h1 | hq'
    · have h1P : (1 : ℕ) • P = 0 := by rw [← h1]; exact addOrderOf_nsmul_eq_zero P
      rw [one_nsmul] at h1P
      exact (hP0 h1P).elim
    · exact hq'
  let xk : ℕ → ℚ := fun k => ptX (k • P)
  let yk : ℕ → ℚ := fun k => ptY (k • P)
  have hmul_ne_zero : ∀ {k : ℕ}, 1 ≤ k → k < q → k • P ≠ 0 := by
    intro k hk1 hkq h0
    have hdvd : q ∣ k := by
      rw [← hord]
      exact addOrderOf_dvd_of_nsmul_eq_zero h0
    have := Nat.le_of_dvd (by omega) hdvd
    omega
  have hyk_ne_zero : ∀ {k : ℕ}, 1 ≤ k → k < q → yk k ≠ 0 := by
    intro k hk1 hkq hy0
    obtain ⟨hkns, hkeq⟩ := pt_eq_some_of_ne_zero (hmul_ne_zero hk1 hkq)
    have h2k : (2 * k) • P = 0 := by
      rw [mul_comm, mul_nsmul, hkeq]
      exact two_nsmul_some_eq_zero_iff.mpr hy0
    have hdvd : q ∣ 2 * k := by
      rw [← hord]
      exact addOrderOf_dvd_of_nsmul_eq_zero h2k
    rcases hq.dvd_mul.mp hdvd with hq_2 | hq_k
    · have := Nat.le_of_dvd (by norm_num) hq_2
      omega
    · have := Nat.le_of_dvd (by omega) hq_k
      omega
  have hxk_eq_iff : ∀ {a b : ℕ}, 1 ≤ a → a < q → 1 ≤ b → b < q →
      xk a = xk b → a = b ∨ a + b = q := by
    intro a b ha1 haq hb1 hbq hxab
    obtain ⟨hans, haeq⟩ := pt_eq_some_of_ne_zero (hmul_ne_zero ha1 haq)
    obtain ⟨hbns, hbeq⟩ := pt_eq_some_of_ne_zero (hmul_ne_zero hb1 hbq)
    have hX := (WeierstrassCurve.Affine.Point.X_eq_iff (h₁ := hans) (h₂ := hbns)).mp hxab
    rw [← haeq, ← hbeq] at hX
    rcases hX with heq | hneg
    · left
      rcases le_total a b with hab | hba
      · have hsub : (b - a) • P = 0 := by
          have : (b - a) • P + a • P = b • P := by
            rw [← add_nsmul, Nat.sub_add_cancel hab]
          rw [heq] at this
          exact add_right_cancel (this.trans (zero_add _).symm)
        have hdvd : q ∣ b - a := by
          rw [← hord]
          exact addOrderOf_dvd_of_nsmul_eq_zero hsub
        by_contra hne
        have := Nat.le_of_dvd (by omega) hdvd
        omega
      · have hsub : (a - b) • P = 0 := by
          have : (a - b) • P + b • P = a • P := by
            rw [← add_nsmul, Nat.sub_add_cancel hba]
          rw [← heq] at this
          exact add_right_cancel (this.trans (zero_add _).symm)
        have hdvd : q ∣ a - b := by
          rw [← hord]
          exact addOrderOf_dvd_of_nsmul_eq_zero hsub
        by_contra hne
        have := Nat.le_of_dvd (by omega) hdvd
        omega
    · right
      have hadd : (a + b) • P = 0 := by
        rw [add_nsmul, hneg, neg_add_cancel]
      have hdvd : q ∣ a + b := by
        rw [← hord]
        exact addOrderOf_dvd_of_nsmul_eq_zero hadd
      obtain ⟨t, ht⟩ := hdvd
      have ht1 : 1 ≤ t := by nlinarith
      have ht2 : t < 2 := by nlinarith
      have : t = 1 := by omega
      rw [this, mul_one] at ht
      exact ht
  -- Choose prime `p ≡ 2*q + 1 [MOD 4*q]` larger than all relevant denominators and numerators.
  let I : Finset ℕ := Finset.Ico 1 q
  let B₁ : ℕ := I.sup (fun k => max (xk k).den (max (yk k).den (yk k).num.natAbs))
  let B₂ : ℕ := (I ×ˢ I).sup (fun ab => (xk ab.1 - xk ab.2).num.natAbs)
  let B : ℕ := max n (max B₁ B₂)
  have hM : 4 * q ≠ 0 := by omega
  have hcop : Nat.Coprime (2 * q + 1) (4 * q) := by
    have hcop2 : Nat.Coprime (2 * q + 1) 2 := by
      rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
      omega
    have hcop4 : Nat.Coprime (2 * q + 1) 4 := by
      simpa using hcop2.pow_right 2
    have hcopq : Nat.Coprime (2 * q + 1) q := by
      rw [Nat.coprime_comm, hq.coprime_iff_not_dvd]
      intro hd
      have h1 : q ∣ 1 := (Nat.dvd_add_right ⟨2, mul_comm 2 q⟩).mp hd
      have := Nat.le_of_dvd (by norm_num) h1
      omega
    exact hcop4.mul_right hcopq
  obtain ⟨p, hpB, hp_prime, hp_mod⟩ := Nat.forall_exists_prime_gt_and_modEq B hM hcop
  have : Fact p.Prime := ⟨hp_prime⟩
  have hp4 : p % 4 = 3 := by
    have h4 : p ≡ 2 * q + 1 [MOD 4] := hp_mod.of_dvd ⟨q, rfl⟩
    change p % 4 = (2 * q + 1) % 4 at h4
    omega
  have hpq : p % q = 1 := by
    have hqmod : p ≡ 2 * q + 1 [MOD q] := hp_mod.of_dvd ⟨4, mul_comm 4 q⟩
    change p % q = (2 * q + 1) % q at hqmod
    have hmod1 : (2 * q + 1) % q = 1 := by
      rw [show 2 * q + 1 = 1 + q * 2 by ring, Nat.add_mul_mod_self_left,
        Nat.mod_eq_of_lt hq.one_lt]
    omega
  have hp2 : p ≠ 2 := by omega
  have h2p : (2 : ZMod p) ≠ 0 := zmod_two_ne_zero p hp2
  have hn_lt_p : n < p := lt_of_le_of_lt (le_max_left _ _) hpB
  have hnp : (n : ZMod p) ≠ 0 := by
    intro h0
    have hdvd : p ∣ n := (ZMod.natCast_eq_zero_iff n p).mp h0
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdvd
    omega
  have hgood_x : ∀ {k : ℕ}, 1 ≤ k → k < q → Good p (xk k) := by
    intro k hk1 hkq
    apply good_of_den_lt
    have hkI : k ∈ I := Finset.mem_Ico.mpr ⟨hk1, hkq⟩
    have hle : (xk k).den ≤ B₁ :=
      le_trans (le_max_left _ _) (Finset.le_sup (f := fun k =>
        max (xk k).den (max (yk k).den (yk k).num.natAbs)) hkI)
    exact lt_of_le_of_lt (le_trans hle (le_trans (le_max_left _ _) (le_max_right _ _))) hpB
  have hgood_y : ∀ {k : ℕ}, 1 ≤ k → k < q → Good p (yk k) := by
    intro k hk1 hkq
    apply good_of_den_lt
    have hkI : k ∈ I := Finset.mem_Ico.mpr ⟨hk1, hkq⟩
    have hle : (yk k).den ≤ B₁ :=
      le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
        (Finset.le_sup (f := fun k => max (xk k).den (max (yk k).den (yk k).num.natAbs)) hkI)
    exact lt_of_le_of_lt (le_trans hle (le_trans (le_max_left _ _) (le_max_right _ _))) hpB
  have hred_y_ne : ∀ {k : ℕ}, 1 ≤ k → k < q → red p (yk k) ≠ 0 := by
    intro k hk1 hkq
    apply red_ne_zero_of_lt (hgood_y hk1 hkq) (hyk_ne_zero hk1 hkq)
    have hkI : k ∈ I := Finset.mem_Ico.mpr ⟨hk1, hkq⟩
    have hle : (yk k).num.natAbs ≤ B₁ :=
      le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
        (Finset.le_sup (f := fun k => max (xk k).den (max (yk k).den (yk k).num.natAbs)) hkI)
    exact lt_of_le_of_lt (le_trans hle (le_trans (le_max_left _ _) (le_max_right _ _))) hpB
  have hred_x_ne : ∀ {a b : ℕ}, 1 ≤ a → a < q → 1 ≤ b → b < q →
      xk a ≠ xk b → red p (xk a) ≠ red p (xk b) := by
    intro a b ha1 haq hb1 hbq hne heq
    have hga := hgood_x ha1 haq
    have hgb := hgood_x hb1 hbq
    obtain ⟨hgsub, hredsub⟩ := good_and_red_sub hga hgb
    have hsub0 : red p (xk a - xk b) = 0 := by rw [hredsub, heq, sub_self]
    have habI : (a, b) ∈ I ×ˢ I :=
      Finset.mem_product.mpr ⟨Finset.mem_Ico.mpr ⟨ha1, haq⟩, Finset.mem_Ico.mpr ⟨hb1, hbq⟩⟩
    have hle : (xk a - xk b).num.natAbs ≤ B₂ :=
      Finset.le_sup (f := fun ab : ℕ × ℕ => (xk ab.1 - xk ab.2).num.natAbs) habI
    have hlt : (xk a - xk b).num.natAbs < p :=
      lt_of_le_of_lt (le_trans hle (le_trans (le_max_right _ _) (le_max_right _ _))) hpB
    exact red_ne_zero_of_lt hgsub (sub_ne_zero.mpr hne) hlt hsub0
  -- Reduced points lie on `Ep n p` and are nonsingular.
  have hns_red : ∀ {k : ℕ}, 1 ≤ k → k < q →
      (Ep n p).toAffine.Nonsingular (red p (xk k)) (red p (yk k)) := by
    intro k hk1 hkq
    obtain ⟨hkns, _⟩ := pt_eq_some_of_ne_zero (hmul_ne_zero hk1 hkq)
    have heq_q : (yk k) ^ 2 = (xk k) ^ 3 - (n : ℚ) ^ 2 * (xk k) :=
      (E_equation_iff n (xk k) (yk k)).mp hkns.1
    have hgx := hgood_x hk1 hkq
    have hgy := hgood_y hk1 hkq
    obtain ⟨_, hr_y2⟩ := good_and_red_pow hgy 2
    obtain ⟨hg_x3, hr_x3⟩ := good_and_red_pow hgx 3
    obtain ⟨hg_n, hr_n⟩ := good_and_red_natCast p n
    obtain ⟨hg_n2, hr_n2⟩ := good_and_red_pow hg_n 2
    obtain ⟨hg_n2x, hr_n2x⟩ := good_and_red_mul hg_n2 hgx
    obtain ⟨_, hr_rhs⟩ := good_and_red_sub hg_x3 hg_n2x
    have heq_p : (red p (yk k)) ^ 2 = (red p (xk k)) ^ 3 - (n : ZMod p) ^ 2 * (red p (xk k)) := by
      rw [← hr_y2, heq_q, hr_rhs, hr_x3, hr_n2x, hr_n2, hr_n]
    exact Ep_nonsingular_of_equation n p hp2 hnp ((Ep_equation_iff n p _ _).mpr heq_p)
  -- Build the group homomorphism `φ : ZMod q →+ (Ep n p).toAffine.Point`.
  let φfun : ZMod q → (Ep n p).toAffine.Point := fun a =>
    if ha : a = 0 then 0
    else
      have ha1 : 1 ≤ a.val := Nat.one_le_iff_ne_zero.mpr (fun h => ha ((ZMod.val_eq_zero a).mp h))
      WeierstrassCurve.Affine.Point.some (red p (xk a.val)) (red p (yk a.val))
        (hns_red ha1 (ZMod.val_lt a))
  have hval_add_smul : ∀ a b : ZMod q, (a + b).val • P = a.val • P + b.val • P := by
    intro a b
    rw [ZMod.val_add, ← add_nsmul]
    have hmod : ∀ m : ℕ, (m % q) • P = m • P := by
      intro m
      rw [← hord]
      exact mod_addOrderOf_nsmul P m
    exact hmod (a.val + b.val)
  have hφ_add : ∀ a b : ZMod q, φfun (a + b) = φfun a + φfun b := by
    intro a b
    by_cases ha : a = 0
    · subst ha; simp [φfun]
    by_cases hb : b = 0
    · subst hb; simp [φfun]
    have ha1 : 1 ≤ a.val := Nat.one_le_iff_ne_zero.mpr (fun h => ha ((ZMod.val_eq_zero a).mp h))
    have haq : a.val < q := ZMod.val_lt a
    have hb1 : 1 ≤ b.val := Nat.one_le_iff_ne_zero.mpr (fun h => hb ((ZMod.val_eq_zero b).mp h))
    have hbq : b.val < q := ZMod.val_lt b
    obtain ⟨hans, haeq⟩ := pt_eq_some_of_ne_zero (hmul_ne_zero ha1 haq)
    obtain ⟨hbns, hbeq⟩ := pt_eq_some_of_ne_zero (hmul_ne_zero hb1 hbq)
    by_cases hab : a + b = 0
    · have hsum0 : a.val • P + b.val • P = 0 := by
        rw [← hval_add_smul, hab, ZMod.val_zero, zero_nsmul]
      have hneg_pt : a.val • P = -(b.val • P) := eq_neg_of_add_eq_zero_left hsum0
      rw [haeq, hbeq, WeierstrassCurve.Affine.Point.neg_some,
        WeierstrassCurve.Affine.Point.some.injEq, E_negY] at hneg_pt
      obtain ⟨hxab, hyab⟩ := hneg_pt
      have hred_y : red p (yk a.val) = -red p (yk b.val) := by
        dsimp only [yk]
        rw [hyab]
        exact (good_and_red_neg (hgood_y hb1 hbq)).2
      simp only [φfun, dif_pos hab, dif_neg ha, dif_neg hb]
      symm
      exact WeierstrassCurve.Affine.Point.add_of_Y_eq (congrArg (red p) hxab)
        (by rw [Ep_negY]; exact hred_y)
    · have hc1 : 1 ≤ (a + b).val :=
        Nat.one_le_iff_ne_zero.mpr (fun h => hab ((ZMod.val_eq_zero (a + b)).mp h))
      have hcq : (a + b).val < q := ZMod.val_lt (a + b)
      obtain ⟨hcns, hceq⟩ := pt_eq_some_of_ne_zero (hmul_ne_zero hc1 hcq)
      have hsum_eq : a.val • P + b.val • P = (a + b).val • P := (hval_add_smul a b).symm
      by_cases heqab : a = b
      · subst heqab
        have hy_ne_q : yk a.val ≠ (E n).toAffine.negY (xk a.val) (yk a.val) := by
          rw [E_negY]
          intro h
          exact hyk_ne_zero ha1 haq (by linarith)
        have hadd_q := WeierstrassCurve.Affine.Point.add_self_of_Y_ne (h₁ := hans) hy_ne_q
        rw [← haeq, hsum_eq, hceq, WeierstrassCurve.Affine.Point.some.injEq] at hadd_q
        obtain ⟨hx3_q, hy3_q⟩ := hadd_q
        have hy_ne_p : red p (yk a.val) ≠
            (Ep n p).toAffine.negY (red p (xk a.val)) (red p (yk a.val)) := by
          rw [Ep_negY]
          intro h
          have h2y0 : (2 : ZMod p) * red p (yk a.val) = 0 := by linear_combination h
          exact mul_ne_zero h2p (hred_y_ne ha1 haq) h2y0
        simp only [φfun, dif_neg hab, dif_neg ha]
        rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne hy_ne_p,
          WeierstrassCurve.Affine.Point.some.injEq]
        set ℓq := (E n).toAffine.slope (xk a.val) (xk a.val) (yk a.val) (yk a.val)
        set ℓp := (Ep n p).toAffine.slope (red p (xk a.val)) (red p (xk a.val))
          (red p (yk a.val)) (red p (yk a.val))
        have hℓq_eq : ℓq = ((3 : ℚ) * (xk a.val) ^ 2 - (n : ℚ) ^ 2) / ((2 : ℚ) * yk a.val) := by
          dsimp [ℓq]
          rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hy_ne_q]
          simp [WeierstrassCurve.Affine.negY]
          ring
        have hℓp_eq : ℓp = ((3 : ZMod p) * (red p (xk a.val)) ^ 2 - (n : ZMod p) ^ 2) /
            ((2 : ZMod p) * red p (yk a.val)) := by
          dsimp [ℓp]
          rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hy_ne_p]
          simp [WeierstrassCurve.Affine.negY]
          ring
        have hgx := hgood_x ha1 haq
        have hgy := hgood_y ha1 haq
        obtain ⟨hg3, hr3⟩ := good_and_red_natCast p 3
        obtain ⟨hg2, hr2⟩ := good_and_red_natCast p 2
        simp only [Nat.cast_ofNat] at hg3 hr3 hg2 hr2
        obtain ⟨hgn, hrn⟩ := good_and_red_natCast p n
        obtain ⟨hgx2, hrx2⟩ := good_and_red_pow hgx 2
        obtain ⟨hgn2, hrn2⟩ := good_and_red_pow hgn 2
        obtain ⟨hg3x2, hr3x2⟩ := good_and_red_mul hg3 hgx2
        obtain ⟨hgnum, hrnum⟩ := good_and_red_sub hg3x2 hgn2
        obtain ⟨_, hrden⟩ := good_and_red_mul hg2 hgy
        have hrden_ne : red p ((2 : ℚ) * yk a.val) ≠ 0 := by
          rw [hrden, hr2]
          exact mul_ne_zero h2p (hred_y_ne ha1 haq)
        obtain ⟨hgℓ, hrℓ⟩ := good_and_red_div hgnum hrden_ne
        have hred_ℓ : Good p ℓq ∧ red p ℓq = ℓp := by
          rw [hℓq_eq, hℓp_eq]
          refine ⟨hgℓ, ?_⟩
          rw [hrℓ, hrnum, hr3x2, hr3, hrx2, hrn2, hrn, hrden, hr2]
        have hx3_eq : xk (a + a).val = ℓq ^ 2 - xk a.val - xk a.val := by
          dsimp only [xk]
          rw [hx3_q]
          dsimp [WeierstrassCurve.Affine.addX, E, WeierstrassCurve.toAffine]
          ring
        have hx3_p : (Ep n p).toAffine.addX (red p (xk a.val)) (red p (xk a.val)) ℓp =
            ℓp ^ 2 - red p (xk a.val) - red p (xk a.val) := by
          dsimp [WeierstrassCurve.Affine.addX, Ep, WeierstrassCurve.toAffine]
          ring
        have hy3_eq : yk (a + a).val = -(ℓq * (xk (a + a).val - xk a.val) + yk a.val) := by
          dsimp only [xk, yk]
          rw [hy3_q, hx3_q]
          dsimp [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY,
            WeierstrassCurve.Affine.negY, E, WeierstrassCurve.toAffine]
          ring
        have hy3_p : (Ep n p).toAffine.addY (red p (xk a.val)) (red p (xk a.val))
            (red p (yk a.val)) ℓp =
            -(ℓp * ((Ep n p).toAffine.addX (red p (xk a.val)) (red p (xk a.val)) ℓp -
              red p (xk a.val)) + red p (yk a.val)) := by
          dsimp [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY,
            WeierstrassCurve.Affine.negY, Ep, WeierstrassCurve.toAffine]
          ring
        obtain ⟨hgℓ2, hrℓ2⟩ := good_and_red_pow hred_ℓ.1 2
        obtain ⟨hgsub1, hrsub1⟩ := good_and_red_sub hgℓ2 hgx
        obtain ⟨_, hrsub2⟩ := good_and_red_sub hgsub1 hgx
        have hred_x3 : red p (xk (a + a).val) =
            (Ep n p).toAffine.addX (red p (xk a.val)) (red p (xk a.val)) ℓp := by
          rw [hx3_eq, hx3_p, hrsub2, hrsub1, hrℓ2, hred_ℓ.2]
        refine ⟨hred_x3, ?_⟩
        obtain ⟨hgdx, hrdx⟩ := good_and_red_sub (hgood_x hc1 hcq) hgx
        obtain ⟨hgm, hrm⟩ := good_and_red_mul hred_ℓ.1 hgdx
        obtain ⟨hga', hra'⟩ := good_and_red_add hgm hgy
        obtain ⟨_, hrneg⟩ := good_and_red_neg hga'
        rw [hy3_eq, hy3_p, hrneg, hra', hrm, hrdx, hred_ℓ.2, hred_x3]
      · -- Secant case: `a ≠ b` and `a + b ≠ 0`, so `xk a.val ≠ xk b.val`.
        have hxne_q : xk a.val ≠ xk b.val := by
          intro hxeq
          rcases hxk_eq_iff ha1 haq hb1 hbq hxeq with hv | hsumq
          · exact heqab (ZMod.val_injective q hv)
          · apply hab
            have h0 : ((a.val + b.val : ℕ) : ZMod q) = 0 := by
              rw [hsumq, ZMod.natCast_self]
            simpa [Nat.cast_add, ZMod.natCast_zmod_val] using h0
        have hxne_p : red p (xk a.val) ≠ red p (xk b.val) :=
          hred_x_ne ha1 haq hb1 hbq hxne_q
        have hadd_q := WeierstrassCurve.Affine.Point.add_of_X_ne (h₁ := hans) (h₂ := hbns) hxne_q
        rw [← haeq, ← hbeq, hsum_eq, hceq, WeierstrassCurve.Affine.Point.some.injEq] at hadd_q
        obtain ⟨hx3_q, hy3_q⟩ := hadd_q
        simp only [φfun, dif_neg hab, dif_neg ha, dif_neg hb]
        rw [WeierstrassCurve.Affine.Point.add_of_X_ne hxne_p,
          WeierstrassCurve.Affine.Point.some.injEq]
        set ℓq := (E n).toAffine.slope (xk a.val) (xk b.val) (yk a.val) (yk b.val)
        set ℓp := (Ep n p).toAffine.slope (red p (xk a.val)) (red p (xk b.val))
          (red p (yk a.val)) (red p (yk b.val))
        have hℓq_eq : ℓq = (yk a.val - yk b.val) / (xk a.val - xk b.val) :=
          WeierstrassCurve.Affine.slope_of_X_ne hxne_q
        have hℓp_eq : ℓp = (red p (yk a.val) - red p (yk b.val)) /
            (red p (xk a.val) - red p (xk b.val)) :=
          WeierstrassCurve.Affine.slope_of_X_ne hxne_p
        have hgxa := hgood_x ha1 haq
        have hgxb := hgood_x hb1 hbq
        have hgya := hgood_y ha1 haq
        have hgyb := hgood_y hb1 hbq
        obtain ⟨hgdy, hrdy⟩ := good_and_red_sub hgya hgyb
        obtain ⟨_, hrdx⟩ := good_and_red_sub hgxa hgxb
        have hrdx_ne : red p (xk a.val - xk b.val) ≠ 0 := by
          rw [hrdx]
          exact sub_ne_zero.mpr hxne_p
        obtain ⟨hgℓ, hrℓ⟩ := good_and_red_div hgdy hrdx_ne
        have hred_ℓ : Good p ℓq ∧ red p ℓq = ℓp := by
          rw [hℓq_eq, hℓp_eq]
          exact ⟨hgℓ, by rw [hrℓ, hrdy, hrdx]⟩
        have hx3_eq : xk (a + b).val = ℓq ^ 2 - xk a.val - xk b.val := by
          dsimp only [xk]
          rw [hx3_q]
          dsimp [WeierstrassCurve.Affine.addX, E, WeierstrassCurve.toAffine]
          ring
        have hx3_p : (Ep n p).toAffine.addX (red p (xk a.val)) (red p (xk b.val)) ℓp =
            ℓp ^ 2 - red p (xk a.val) - red p (xk b.val) := by
          dsimp [WeierstrassCurve.Affine.addX, Ep, WeierstrassCurve.toAffine]
          ring
        have hy3_eq : yk (a + b).val = -(ℓq * (xk (a + b).val - xk a.val) + yk a.val) := by
          dsimp only [xk, yk]
          rw [hy3_q, hx3_q]
          dsimp [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY,
            WeierstrassCurve.Affine.negY, E, WeierstrassCurve.toAffine]
          ring
        have hy3_p : (Ep n p).toAffine.addY (red p (xk a.val)) (red p (xk b.val))
            (red p (yk a.val)) ℓp =
            -(ℓp * ((Ep n p).toAffine.addX (red p (xk a.val)) (red p (xk b.val)) ℓp -
              red p (xk a.val)) + red p (yk a.val)) := by
          dsimp [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY,
            WeierstrassCurve.Affine.negY, Ep, WeierstrassCurve.toAffine]
          ring
        obtain ⟨hgℓ2, hrℓ2⟩ := good_and_red_pow hred_ℓ.1 2
        obtain ⟨hgsub1, hrsub1⟩ := good_and_red_sub hgℓ2 hgxa
        obtain ⟨_, hrsub2⟩ := good_and_red_sub hgsub1 hgxb
        have hred_x3 : red p (xk (a + b).val) =
            (Ep n p).toAffine.addX (red p (xk a.val)) (red p (xk b.val)) ℓp := by
          rw [hx3_eq, hx3_p, hrsub2, hrsub1, hrℓ2, hred_ℓ.2]
        refine ⟨hred_x3, ?_⟩
        obtain ⟨hgdx3, hrdx3⟩ := good_and_red_sub (hgood_x hc1 hcq) hgxa
        obtain ⟨hgm, hrm⟩ := good_and_red_mul hred_ℓ.1 hgdx3
        obtain ⟨hga', hra'⟩ := good_and_red_add hgm hgya
        obtain ⟨_, hrneg⟩ := good_and_red_neg hga'
        rw [hy3_eq, hy3_p, hrneg, hra', hrm, hrdx3, hred_ℓ.2, hred_x3]
  let φ : ZMod q →+ (Ep n p).toAffine.Point :=
    { toFun := φfun
      map_zero' := by simp [φfun]
      map_add' := hφ_add }
  have h1_ne : (1 : ZMod q) ≠ 0 := one_ne_zero
  have hQ_ne : φ 1 ≠ 0 := by
    change φfun 1 ≠ 0
    simp only [φfun, dif_neg h1_ne]
    exact WeierstrassCurve.Affine.Point.some_ne_zero _
  have hqQ : q • φ 1 = 0 := by
    rw [← map_nsmul, nsmul_eq_mul, mul_one, ZMod.natCast_self, map_zero]
  have hordQ : addOrderOf (φ 1) = q := by
    have hdvd : addOrderOf (φ 1) ∣ q := addOrderOf_dvd_of_nsmul_eq_zero hqQ
    rcases (Nat.dvd_prime hq).mp hdvd with h1 | hq'
    · have h1Q : (1 : ℕ) • φ 1 = 0 := by rw [← h1]; exact addOrderOf_nsmul_eq_zero (φ 1)
      rw [one_nsmul] at h1Q
      exact (hQ_ne h1Q).elim
    · exact hq'
  classical
  let _ : Fintype (Ep n p).toAffine.Point :=
    Fintype.ofEquiv _ (pointEquivOption (Ep n p).toAffine).symm
  have hcard : Fintype.card (Ep n p).toAffine.Point = p + 1 :=
    card_Ep_point n p hp4 hnp
  have hdvd_card : q ∣ p + 1 := by
    rw [← hordQ, ← hcard]
    exact addOrderOf_dvd_card
  have hdiv : p = q * (p / q) + p % q := (Nat.div_add_mod p q).symm
  rw [hpq] at hdiv
  have h2dvd : q ∣ 2 := by
    have hp1 : p + 1 = q * (p / q) + 2 := by omega
    rw [hp1] at hdvd_card
    exact (Nat.dvd_add_right ⟨p / q, rfl⟩).mp hdvd_card
  have := Nat.le_of_dvd (by norm_num) h2dvd
  omega

end CongruentNumberTorsionH1

theorem OMA.solution : OMA.R_CongruentNumber_Tunnell_odd_R1.H1 := by
  intro n hn P m hm hmP
  set d := addOrderOf P
  have hd_dvd : d ∣ m := addOrderOf_dvd_of_nsmul_eq_zero hmP
  have hd_pos : 0 < d := Nat.pos_of_dvd_of_pos hd_dvd hm
  have hnot4 : ¬ 4 ∣ d := by
    rintro ⟨k, hk⟩
    have hk_pos : 0 < k := by omega
    have h4k : (4 : ℕ) • (k • P) = 0 := by
      rw [← mul_nsmul, mul_comm, ← hk]
      exact addOrderOf_nsmul_eq_zero P
    have h2k : (2 : ℕ) • (k • P) ≠ 0 := by
      intro h0
      rw [← mul_nsmul, mul_comm] at h0
      have hdvd : d ∣ 2 * k := addOrderOf_dvd_of_nsmul_eq_zero h0
      have hle : d ≤ 2 * k := Nat.le_of_dvd (by omega) hdvd
      omega
    exact CongruentNumberTorsionH1.no_order_four n hn (k • P) h2k h4k
  have hprime_eq_two : ∀ q : ℕ, q.Prime → q ∣ d → q = 2 := by
    intro q hq hqd
    by_contra hq2
    obtain ⟨k, hk⟩ := hqd
    have hk_pos : 0 < k := by
      have := hq.pos
      nlinarith
    have hqk : q • (k • P) = 0 := by
      rw [← mul_nsmul, mul_comm, ← hk]
      exact addOrderOf_nsmul_eq_zero P
    have hk_ne : k • P ≠ 0 := by
      intro h0
      have hdvd : d ∣ k := addOrderOf_dvd_of_nsmul_eq_zero h0
      have hle : d ≤ k := Nat.le_of_dvd hk_pos hdvd
      have := hq.two_le
      nlinarith
    exact CongruentNumberTorsionH1.no_odd_prime_order n hn q hq hq2 (k • P) hk_ne hqk
  have hd_dvd_two : d ∣ 2 := by
    by_cases hd1 : d = 1
    · rw [hd1]; exact one_dvd 2
    · have h2d : 2 ∣ d := by
        have hmf := Nat.minFac_prime hd1
        have hmfd := Nat.minFac_dvd d
        have := hprime_eq_two d.minFac hmf hmfd
        rwa [this] at hmfd
      obtain ⟨t, ht⟩ := h2d
      by_cases ht1 : t = 1
      · rw [ht, ht1, mul_one]
      · have h2t : 2 ∣ t := by
          have hmf := Nat.minFac_prime ht1
          have hmft := Nat.minFac_dvd t
          have hmfd : t.minFac ∣ d := dvd_trans hmft ⟨2, by rw [ht, mul_comm]⟩
          have := hprime_eq_two t.minFac hmf hmfd
          rwa [this] at hmft
        obtain ⟨u, hu⟩ := h2t
        exact (hnot4 ⟨u, by rw [ht, hu]; ring⟩).elim
  exact addOrderOf_dvd_iff_nsmul_eq_zero.mp hd_dvd_two
