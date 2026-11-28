import OMAReductions.R_Erdos940_erdos_940_variants_three_powerful_R1_H2_R2
import Mathlib

-- Credit: @kumagi

/-!
Wang, arXiv:2611.14161v1, Proposition 2.2, gives the two classes in the
genus of the coefficient-25 form and their automorphism numbers, so
the genus average weights their counts by 1/5 and 4/5.
https://arxiv.org/html/2611.14161v1

The error estimate is Moroz's Theorem 1 in the coprime range. The
same theorem's genus lower estimate for the ordinary three-square
form applies to the odd admissible integers.
https://www.numdam.org/item/AST_1992__209__275_0/

We compare the genus count to the three-square count by double-counting
the incidences with the 15 planes modulo 5 whose normals have nonzero
square norm. This comparison, including the multiplicities, is proved below.
-/

namespace OMA.R_Erdos940_erdos_940_variants_three_powerful_R1_H2_R2_H2_R1

private abbrev Triple (R : Type) := R × R × R
private abbrev Plane := Fin 3 ⊕ (Fin 3 × Bool × Bool)

private def orient {R : Type} (i : Fin 3) (v : Triple R) : Triple R :=
  if i = 0 then (v.2.2, v.2.1, v.1)
  else if i = 1 then (v.1, v.2.2, v.2.1)
  else v

private lemma orient_involutive {R : Type} (i : Fin 3) (v : Triple R) :
    orient i (orient i v) = v := by
  rcases v with ⟨x, y, z⟩
  fin_cases i <;> norm_num [orient]

private def signed {R : Type} [Neg R] (s : Bool) (x : R) : R :=
  if s then -x else x

private def adjust {R : Type} [Neg R] (s t : Bool) (v : Triple R) : Triple R :=
  (signed s v.1, signed t v.2.1, v.2.2)

private lemma adjust_involutive (s t : Bool) (v : Triple ℤ) :
    adjust s t (adjust s t v) = v := by
  rcases v with ⟨x, y, z⟩
  cases s <;> cases t <;> simp [adjust, signed]

private def normSq {R : Type} [Ring R] (v : Triple R) : R :=
  v.1 ^ 2 + v.2.1 ^ 2 + v.2.2 ^ 2

private lemma normSq_orient (i : Fin 3) (v : Triple ℤ) : normSq (orient i v) = normSq v := by
  rcases v with ⟨x, y, z⟩
  fin_cases i <;> norm_num [orient, normSq] <;> ring

private lemma normSq_adjust (s t : Bool) (v : Triple ℤ) : normSq (adjust s t v) = normSq v := by
  rcases v with ⟨x, y, z⟩
  cases s <;> cases t <;> simp [adjust, signed, normSq]

private def red (v : Triple ℤ) : Triple (ZMod 5) :=
  (v.1, v.2.1, v.2.2)

private lemma red_orient (i : Fin 3) (v : Triple ℤ) : red (orient i v) = orient i (red v) := by
  fin_cases i <;> norm_num [orient, red]

private lemma red_adjust (s t : Bool) (v : Triple ℤ) : red (adjust s t v) = adjust s t (red v) := by
  cases s <;> cases t <;> simp [red, adjust, signed]

private lemma normSq_red (v : Triple ℤ) : normSq (red v) = ((normSq v : ℤ) : ZMod 5) := by
  simp [red, normSq]

private def onMixedPlane (v : Triple (ZMod 5)) : Prop :=
  v.1 + v.2.1 + 2 * v.2.2 = 0

private instance (v : Triple (ZMod 5)) : Decidable (onMixedPlane v) :=
  inferInstanceAs (Decidable (_ = _))

private def contains (p : Plane) (v : Triple (ZMod 5)) : Prop :=
  match p with
  | .inl i => (orient i v).2.2 = 0
  | .inr (i, s, t) => onMixedPlane (adjust s t (orient i v))

private instance (p : Plane) (v : Triple (ZMod 5)) : Decidable (contains p v) := by
  cases p <;> unfold contains <;> dsimp <;> infer_instance

private def incidenceCount (v : Triple (ZMod 5)) : ℕ :=
  (Finset.univ.filter (fun p : Plane => contains p v)).card

private def multiplier (a : ZMod 5) : ℕ :=
  if a = 1 ∨ a = 4 then 2 else 3

set_option maxRecDepth 6000 in
set_option maxHeartbeats 2000000 in
private theorem count_incidence :
    ∀ v : Triple (ZMod 5), normSq v ≠ 0 → incidenceCount v = multiplier (normSq v) := by
  decide +kernel

private def baseForm (v : Triple ℤ) : ℤ :=
  v.1 ^ 2 + v.2.1 ^ 2 + 25 * v.2.2 ^ 2

private def companionForm (v : Triple ℤ) : ℤ :=
  2 * v.1 ^ 2 + 3 * v.2.1 ^ 2 + 5 * v.2.2 ^ 2 +
      2 * v.1 * v.2.2 + 2 * v.2.1 * v.2.2

private def basePlaneMap (v : Triple ℤ) : Triple ℤ :=
  (v.1, v.2.1, 5 * v.2.2)

private def mixedPlaneMap (v : Triple ℤ) : Triple ℤ :=
  (-v.1 - v.2.1, v.1 - v.2.1 + v.2.2, v.2.1 + 2 * v.2.2)

private lemma basePlaneMap_norm (v : Triple ℤ) : normSq (basePlaneMap v) = baseForm v := by
  simp only [normSq, basePlaneMap, baseForm]
  ring

private lemma mixedPlaneMap_norm (v : Triple ℤ) :
    normSq (mixedPlaneMap v) = companionForm v := by
  simp only [normSq, mixedPlaneMap, companionForm]
  ring

private def basePlaneEquiv : Triple ℤ ≃ {v : Triple ℤ // (red v).2.2 = 0} where
  toFun v := ⟨basePlaneMap v, by simp [basePlaneMap, red, show (5 : ZMod 5) = 0 by decide]⟩
  invFun v := (v.val.1, v.val.2.1, v.val.2.2 / 5)
  left_inv v := by
    rcases v with ⟨x, y, z⟩
    simp [basePlaneMap, Int.mul_comm]
  right_inv v := by
    apply Subtype.ext
    obtain ⟨⟨x, y, z⟩, hv⟩ := v
    have hz : (5 : ℤ) ∣ z := (ZMod.intCast_zmod_eq_zero_iff_dvd z 5).mp hv
    change (x, y, 5 * (z / 5)) = (x, y, z)
    rw [mul_comm 5, Int.ediv_mul_cancel hz]

private def mixedPlaneInv (v : Triple ℤ) : Triple ℤ :=
  let c := (v.1 + v.2.1 + 2 * v.2.2) / 5
  let b := v.2.2 - 2 * c
  (-v.1 - b, b, c)

private def mixedPlaneEquiv : Triple ℤ ≃ {v : Triple ℤ // onMixedPlane (red v)} where
  toFun v := ⟨mixedPlaneMap v, by
    unfold onMixedPlane red mixedPlaneMap
    push_cast
    have h : (2 : ZMod 5) * 2 + 1 = 0 := by decide
    linear_combination h * (v.2.2 : ZMod 5)⟩
  invFun v := mixedPlaneInv v
  left_inv v := by
    rcases v with ⟨a, b, c⟩
    have hc : (-a - b + (a - b + c) + 2 * (b + 2 * c)) / 5 = c := by
      rw [show -a - b + (a - b + c) + 2 * (b + 2 * c) = c * 5 by ring]
      simp
    simp only [mixedPlaneInv, mixedPlaneMap, hc, Prod.mk.injEq]
    constructor <;> ring_nf <;> simp
  right_inv v := by
    apply Subtype.ext
    obtain ⟨⟨x, y, z⟩, hv⟩ := v
    have hd : (5 : ℤ) ∣ x + y + 2 * z := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 5).mp
      push_cast
      exact hv
    have hc := Int.ediv_mul_cancel hd
    simp only [mixedPlaneMap, mixedPlaneInv, Prod.mk.injEq]
    constructor
    · ring
    · constructor
      · linarith only [hc]
      · ring

private lemma orientation_and_sign (i : Fin 3) (s t : Bool) :
    ∃ e : Triple ℤ ≃ Triple ℤ, (∀ v, e v = adjust s t (orient i v)) ∧
      (∀ v, normSq (e v) = normSq v) := by
  let e : Triple ℤ ≃ Triple ℤ :=
    { toFun := fun v => adjust s t (orient i v)
      invFun := fun v => orient i (adjust s t v)
      left_inv := fun v => by dsimp; rw [adjust_involutive, orient_involutive]
      right_inv := fun v => by dsimp; rw [orient_involutive, adjust_involutive] }
  exact ⟨e, fun _ => rfl, fun v => (normSq_adjust s t _).trans (normSq_orient i v)⟩


private abbrev Sphere (n : ℕ) := {v : Triple ℤ // normSq v = (n : ℤ)}

private instance sphereFinite (n : ℕ) : Finite (Sphere n) := by
  let box := Set.Icc (-(↑n + 1) : ℤ) ((n : ℤ) + 1)
  have hbox : box.Finite := Set.finite_Icc _ _
  have hs : {v : Triple ℤ | normSq v = (n : ℤ)}.Finite := by
    refine (hbox.prod (hbox.prod hbox)).subset ?_
    intro v hv
    change v.1 ∈ box ∧ v.2.1 ∈ box ∧ v.2.2 ∈ box
    have hv' : v.1 ^ 2 + v.2.1 ^ 2 + v.2.2 ^ 2 = (n : ℤ) := hv
    have hb {x : ℤ} (hx : x ^ 2 ≤ (n : ℤ)) : x ∈ box :=
      ⟨by nlinarith only [hx, sq_nonneg (2 * x + 1)],
        by nlinarith only [hx, sq_nonneg (2 * x - 1)]⟩
    exact ⟨hb (by linarith only [hv', sq_nonneg v.2.1, sq_nonneg v.2.2]),
      hb (by linarith only [hv', sq_nonneg v.1, sq_nonneg v.2.2]),
      hb (by linarith only [hv', sq_nonneg v.1, sq_nonneg v.2.1])⟩
  exact hs.to_subtype

private noncomputable def baseCount (n : ℕ) : ℕ := Nat.card {v : Triple ℤ // baseForm v = (n : ℤ)}
private noncomputable def companionCount (n : ℕ) : ℕ := Nat.card {v : Triple ℤ // companionForm v = (n : ℤ)}
private noncomputable def threeCount (n : ℕ) : ℕ := Nat.card (Sphere n)

private abbrev PlaneSphere (n : ℕ) (p : Plane) := {v : Sphere n // contains p (red v.val)}

private lemma count_fibre {n : ℕ} {p : Plane} {form : Triple ℤ → ℤ}
    {pred : Triple ℤ → Prop} (e : Triple ℤ ≃ {v : Triple ℤ // pred v})
    (he : ∀ v, normSq (e v).val = form v) (s : Triple ℤ ≃ Triple ℤ)
    (hs : ∀ v, normSq (s v) = normSq v)
    (hp : ∀ v, contains p (red v) ↔ pred (s v)) :
    Nat.card (PlaneSphere n p) = Nat.card {v : Triple ℤ // form v = (n : ℤ)} := by
  let sphereEquiv : Sphere n ≃ Sphere n := s.subtypeEquiv (fun v => by rw [hs])
  let transport := sphereEquiv.subtypeEquiv
    (p := fun v => contains p (red v.val)) (q := fun v => pred v.val) (fun v => hp v.val)
  let reorder : {v : Sphere n // pred v.val} ≃
      {v : {w : Triple ℤ // pred w} // normSq v.val = (n : ℤ)} :=
    { toFun := fun v => ⟨⟨v.val.val, v.property⟩, v.val.property⟩
      invFun := fun v => ⟨⟨v.val.val, v.property⟩, v.val.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let parametrization := e.subtypeEquiv (p := fun v => form v = (n : ℤ))
    (q := fun v => normSq v.val = (n : ℤ)) (fun v => by rw [he])
  exact Nat.card_congr (transport.trans (reorder.trans parametrization.symm))

private lemma count_on_coordinate_plane (n : ℕ) (i : Fin 3) :
    Nat.card (PlaneSphere n (.inl i)) = baseCount n := by
  obtain ⟨s, hdef, hs⟩ := orientation_and_sign i false false
  refine count_fibre basePlaneEquiv basePlaneMap_norm s hs ?_
  intro v
  change (orient i (red v)).2.2 = 0 ↔ (red (s v)).2.2 = 0
  rw [hdef, red_adjust, red_orient]
  rfl

private lemma count_on_mixed_plane (n : ℕ) (i : Fin 3) (s t : Bool) :
    Nat.card (PlaneSphere n (.inr (i, s, t))) = companionCount n := by
  obtain ⟨e, hdef, he⟩ := orientation_and_sign i s t
  refine count_fibre mixedPlaneEquiv mixedPlaneMap_norm e he ?_
  intro v
  change onMixedPlane (adjust s t (orient i (red v))) ↔ onMixedPlane (red (e v))
  rw [hdef, red_adjust, red_orient]

private def swapIncidence (n : ℕ) :
    (Σ p : Plane, PlaneSphere n p) ≃ (Σ v : Sphere n, {p : Plane // contains p (red v.val)}) where
  toFun v := ⟨v.2.val, ⟨v.1, v.2.property⟩⟩
  invFun v := ⟨v.2.val, ⟨v.1, v.2.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

private lemma incidence_by_plane (n : ℕ) :
    Nat.card (Σ p : Plane, PlaneSphere n p) = 3 * baseCount n + 12 * companionCount n := by
  rw [Nat.card_sigma, Fintype.sum_sum_type]
  simp only [count_on_coordinate_plane, count_on_mixed_plane, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  rfl

private lemma incidence_by_sphere {n : ℕ} (hn : ¬ 5 ∣ n) :
    Nat.card (Σ v : Sphere n, {p : Plane // contains p (red v.val)}) =
      threeCount n * multiplier (n : ZMod 5) := by
  let : Fintype (Sphere n) := Fintype.ofFinite _
  rw [Nat.card_sigma]
  have hpoint (v : Sphere n) :
      Nat.card {p : Plane // contains p (red v.val)} = multiplier (n : ZMod 5) := by
    have hv : normSq (red v.val) = (n : ZMod 5) := by
      rw [normSq_red, v.property, Int.cast_natCast]
    have hnonzero : (n : ZMod 5) ≠ 0 :=
      fun h => hn ((ZMod.natCast_eq_zero_iff n 5).mp h)
    rw [Nat.card_eq_fintype_card,
      Fintype.card_of_subtype (Finset.univ.filter fun p : Plane => contains p (red v.val))
        (fun p => by simp only [Finset.mem_filter, Finset.mem_univ, true_and])]
    change incidenceCount (red v.val) = multiplier (n : ZMod 5)
    rw [count_incidence _ (hv ▸ hnonzero), hv]
  simp only [hpoint, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, threeCount,
    Nat.card_eq_fintype_card, Nat.cast_id]

private theorem representation_identity {n : ℕ} (hn : ¬ 5 ∣ n) :
    3 * (baseCount n + 4 * companionCount n) = threeCount n * multiplier (n : ZMod 5) := by
  have hh := Nat.card_congr (swapIncidence n)
  rw [incidence_by_plane, incidence_by_sphere hn] at hh
  omega

open Filter

/-- The odd, locally representable cases of the lower estimate for three squares. -/
def H1 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ c : ℝ, 0 < c ∧
    ∀ᶠ n : ℕ in atTop, Odd n → n % 8 ≠ 7 →
      c * (n : ℝ) ^ ((1 : ℝ) / 2 - ε) ≤
        (Nat.card {v : ℤ × ℤ × ℤ // v.1 ^ 2 + v.2.1 ^ 2 + v.2.2 ^ 2 = (n : ℤ)} : ℝ)

/-- The power-saving error from the two-class genus average in the coprime range. -/
def H2 : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, 0 < C ∧
    ∀ᶠ n : ℕ in atTop, Odd n → ¬ 5 ∣ n →
      let rf : ℝ := Nat.card {v : ℤ × ℤ × ℤ //
        v.1 ^ 2 + v.2.1 ^ 2 + 25 * v.2.2 ^ 2 = (n : ℤ)}
      let rg : ℝ := Nat.card {v : ℤ × ℤ × ℤ //
        2 * v.1 ^ 2 + 3 * v.2.1 ^ 2 + 5 * v.2.2 ^ 2 +
          2 * v.1 * v.2.2 + 2 * v.2.1 * v.2.2 = (n : ℤ)}
      |rf - (rf + 4 * rg) / 5| ≤ C * (n : ℝ) ^ ((1 : ℝ) / 2 - δ)

section

private noncomputable def genusCount (n : ℕ) : ℝ :=
  ((baseCount n : ℝ) + 4 * (companionCount n : ℝ)) / 5

private lemma genus_lower {n : ℕ} (hn : ¬ 5 ∣ n) :
    (2 / 15 : ℝ) * threeCount n ≤ genusCount n := by
  have hid := representation_identity hn
  have hidR : 3 * ((baseCount n : ℝ) + 4 * (companionCount n : ℝ)) =
      (threeCount n : ℝ) * (multiplier (n : ZMod 5) : ℝ) := by
    exact_mod_cast hid
  have hmult : (2 : ℝ) ≤ (multiplier (n : ZMod 5) : ℝ) := by
    unfold multiplier
    split <;> norm_num
  have hm := mul_le_mul_of_nonneg_left hmult (show (0 : ℝ) ≤ threeCount n by positivity)
  unfold genusCount
  linarith only [hidR, hm]

private lemma eventually_domination
    {a b c C : ℝ} (hab : b < a) (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, C * (n : ℝ) ^ b < c * (n : ℝ) ^ a := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ) ^ (a - b)) atTop atTop :=
    (tendsto_rpow_atTop (sub_pos.mpr hab)).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop (1 : ℕ), ht.eventually_gt_atTop (C / c)] with n hn ht
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hbPos : 0 < (n : ℝ) ^ b := Real.rpow_pos_of_pos hnR b
  rw [Real.rpow_sub hnR a b] at ht
  have hRatio := (lt_div_iff₀ hbPos).mp ht
  calc
    C * (n : ℝ) ^ b = c * (C / c * (n : ℝ) ^ b) := by field_simp
    _ < c * (n : ℝ) ^ a := mul_lt_mul_of_pos_left hRatio hc

theorem main : H1 → H2 → OMA.R_Erdos940_erdos_940_variants_three_powerful_R1_H2_R2.H2 := by
  intro hThree hError
  obtain ⟨δ, hδ, C, _, hApprox⟩ := hError
  obtain ⟨c, hc, hLower⟩ := hThree (δ / 2) (by positivity)
  have hCoe : 0 < (2 / 15 : ℝ) * c := by positivity
  have hgrowth := eventually_domination (a := (1 : ℝ) / 2 - δ / 2)
    (b := (1 : ℝ) / 2 - δ) (C := C) (by linarith) hCoe
  filter_upwards [hApprox, hLower, hgrowth] with n hApprox hLower hgrowth
  intro hOdd hFive hEight
  have h3 : c * (n : ℝ) ^ ((1 : ℝ) / 2 - δ / 2) ≤ (threeCount n : ℝ) :=
    hLower hOdd hEight
  have hgen := (mul_le_mul_of_nonneg_left h3 (show (0 : ℝ) ≤ 2 / 15 by norm_num)).trans
    (genus_lower hFive)
  rw [← mul_assoc] at hgen
  have herror : |(baseCount n : ℝ) - genusCount n| ≤ C * (n : ℝ) ^ ((1 : ℝ) / 2 - δ) :=
    hApprox hOdd hFive
  have hpos : (0 : ℝ) < baseCount n := by
    have hh := (abs_le.mp herror).1
    linarith only [hh, hgen, hgrowth]
  have hcard : 0 < baseCount n := by exact_mod_cast hpos
  unfold baseCount at hcard
  obtain ⟨⟨⟨x, y, z⟩, hv⟩⟩ := (Nat.card_ne_zero.mp hcard.ne').1
  exact ⟨x, y, z, by norm_num [baseForm] at hv ⊢; exact hv⟩

end

end OMA.R_Erdos940_erdos_940_variants_three_powerful_R1_H2_R2_H2_R1
