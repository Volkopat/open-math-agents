import OMAReductions.R_Erdos940_erdos_940_variants_three_powerful_R1_H2_R2
import Mathlib

-- Credit: @kumagi

/-!
Moroz's Theorem 1 supplies a power-saving error term for the difference
between a form's representation count and its weighted genus average,
and gives the lower estimate for the ordinary three-square genus.
https://www.numdam.org/item/AST_1992__209__275_0/

For the coefficient-125 form, the genus average can be expressed using
the coefficient-five lattice. For any lattice L in the genus, the
canonical over-lattice L + 25 L^# is in the genus of diag(1,1,5).
At 5 this adds one fifth of the third basis vector in a diagonal local
basis, and elsewhere it changes nothing. The coefficient-five genus
has one class (Oh and Sun, Lemma 3.8).
https://www.math.snu.ac.kr/~bkoh/s-uni.pdf

Its index-five sublattices in the coefficient-125 genus are exactly
the planes complementary to the radical modulo 5. The others have
Gram rank below two modulo 5. For a complementary plane, the binary
unimodular block is the identity modulo 5, and its rank-one
orthogonal complement has determinant 125 times a square unit, giving
the required local class. At other primes the index is a unit.
Isometries preserve the canonical over-lattice, so the classes are
the orbits of its automorphism group on the 25 planes. The stabilizer
weights in the genus average give the ordinary average over all planes.

The following code checks the double count over these 25 planes and
the six-to-one correspondence with three-square representations of
5n. For 5 not dividing n the result is r_3(5n)/30 for the average.
-/

namespace OMA.R_Erdos940_erdos_940_variants_three_powerful_R1_H2_R2_H1_R1

private abbrev Triple (R : Type) := R × R × R
private abbrev SectionIndex := Fin 3 × Bool

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

private def distinguished (v : Triple (ZMod 5)) : Prop :=
  v.2.2 = 0 ∧ v.1 = 2 * v.2.1

private instance (v : Triple (ZMod 5)) : Decidable (distinguished v) := by
  unfold distinguished
  infer_instance

private def liesInSection (k : SectionIndex) (v : Triple (ZMod 5)) : Prop :=
  distinguished (adjust k.2 false (orient k.1 v))

private instance (k : SectionIndex) (v : Triple (ZMod 5)) : Decidable (liesInSection k v) :=
  inferInstanceAs (Decidable (distinguished _))

set_option maxRecDepth 6000 in
set_option maxHeartbeats 1000000 in
private theorem unique_section_count :
    ∀ v : Triple (ZMod 5), normSq v = 0 → v ≠ (0, 0, 0) →
      (Finset.univ.filter (fun k : SectionIndex => liesInSection k v)).card = 1 := by
  decide +kernel

private theorem unique_section (v : Triple (ZMod 5)) (h₀ : normSq v = 0)
    (hv : v ≠ (0, 0, 0)) : ∃! k, liesInSection k v := by
  obtain ⟨k, hk⟩ := Finset.card_eq_one.mp (unique_section_count v h₀ hv)
  refine ⟨k, ?_, ?_⟩
  · have hm : k ∈ Finset.univ.filter (fun i => liesInSection i v) := by simp [hk]
    exact (Finset.mem_filter.mp hm).2
  · intro j hj
    have hm : j ∈ Finset.univ.filter (fun i => liesInSection i v) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩
    simpa [hk] using hm

private def weightedForm (v : Triple ℤ) : ℤ :=
  v.1 ^ 2 + v.2.1 ^ 2 + 5 * v.2.2 ^ 2

private def gaussMap (v : Triple ℤ) : Triple ℤ :=
  (2 * v.1 + v.2.1, v.1 - 2 * v.2.1, 5 * v.2.2)

private def gaussInv (w : Triple ℤ) : Triple ℤ :=
  ((2 * w.1 + w.2.1) / 5, (w.1 - 2 * w.2.1) / 5, w.2.2 / 5)

private lemma gauss_norm (v : Triple ℤ) : normSq (gaussMap v) = 5 * weightedForm v := by
  simp only [normSq, gaussMap, weightedForm]
  ring

private lemma gauss_in_section (v : Triple ℤ) : distinguished (red (gaussMap v)) := by
  unfold distinguished red gaussMap
  dsimp
  push_cast
  have h : (5 : ZMod 5) = 0 := by decide
  constructor
  · simp [h]
  · linear_combination h * (v.2.1 : ZMod 5)

private lemma gauss_left_inv (v : Triple ℤ) : gaussInv (gaussMap v) = v := by
  rcases v with ⟨x, y, z⟩
  unfold gaussInv gaussMap
  dsimp
  rw [show 2 * (2 * x + y) + (x - 2 * y) = x * 5 by ring,
    show 2 * x + y - 2 * (x - 2 * y) = y * 5 by ring,
    mul_comm 5 z]
  simp

private lemma gauss_right_inv {w : Triple ℤ} (hw : distinguished (red w)) :
    gaussMap (gaussInv w) = w := by
  obtain ⟨x, y, z⟩ := w
  change (z : ZMod 5) = 0 ∧ (x : ZMod 5) = 2 * (y : ZMod 5) at hw
  have hz : (5 : ℤ) ∣ z := (ZMod.intCast_zmod_eq_zero_iff_dvd z 5).mp hw.1
  have hy : (5 : ℤ) ∣ x - 2 * y := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 5).mp
    push_cast
    rw [hw.2, sub_self]
  have hx : (5 : ℤ) ∣ 2 * x + y := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 5).mp
    push_cast
    rw [hw.2]
    have h : (5 : ZMod 5) = 0 := by decide
    linear_combination h * (y : ZMod 5)
  have hdivx := Int.ediv_mul_cancel hx
  have hdivy := Int.ediv_mul_cancel hy
  have hdivz := Int.ediv_mul_cancel hz
  simp only [gaussInv, gaussMap, Prod.mk.injEq]
  refine ⟨?_, ?_, ?_⟩ <;> linarith only [hdivx, hdivy, hdivz]

private abbrev ThreeRep (n : ℕ) := {v : Triple ℤ // normSq v = (n : ℤ)}
private abbrev WeightedRep (n : ℕ) := {v : Triple ℤ // weightedForm v = (n : ℤ)}

private lemma classify_rep {n : ℕ} (hn : ¬ 5 ∣ n) (v : ThreeRep (5 * n)) :
    ∃! k, liesInSection k (red v.val) := by
  apply unique_section
  · rw [normSq_red, v.property]
    push_cast
    simp [show (5 : ZMod 5) = 0 by decide]
  · intro hzero
    obtain ⟨⟨x, y, z⟩, hv⟩ := v
    change ((x : ZMod 5), (y : ZMod 5), (z : ZMod 5)) = (0, 0, 0) at hzero
    obtain ⟨hx₀, hy₀, hz₀⟩ := (by simpa only [Prod.mk.injEq] using hzero :
      (x : ZMod 5) = 0 ∧ (y : ZMod 5) = 0 ∧ (z : ZMod 5) = 0)
    obtain ⟨a, rfl⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd x 5).mp hx₀
    obtain ⟨b, rfl⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd y 5).mp hy₀
    obtain ⟨c, rfl⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd z 5).mp hz₀
    have h : (n : ℤ) = 5 * (a ^ 2 + b ^ 2 + c ^ 2) := by
      simp only [normSq, Nat.cast_mul, Nat.cast_ofNat] at hv
      nlinarith only [hv]
    have hd : (5 : ℤ) ∣ (n : ℤ) := ⟨_, h⟩
    exact hn (by exact_mod_cast hd)

private def encode (n : ℕ) (p : SectionIndex × WeightedRep n) : ThreeRep (5 * n) :=
  ⟨orient p.1.1 (adjust p.1.2 false (gaussMap p.2.val)), by
    rw [normSq_orient, normSq_adjust, gauss_norm, p.2.property]
    push_cast; rfl⟩

private lemma encode_in_section (n : ℕ) (p : SectionIndex × WeightedRep n) :
    liesInSection p.1 (red (encode n p).val) := by
  unfold liesInSection
  have h : orient p.1.1 (orient p.1.1 (adjust p.1.2 false (gaussMap p.2.val))) =
      adjust p.1.2 false (gaussMap p.2.val) := orient_involutive _ _
  change distinguished (adjust p.1.2 false
    (orient p.1.1 (red (orient p.1.1 (adjust p.1.2 false (gaussMap p.2.val))))))
  rw [← red_orient, h, ← red_adjust, adjust_involutive]
  exact gauss_in_section _

private lemma encode_bijective {n : ℕ} (hn : ¬ 5 ∣ n) : Function.Bijective (encode n) := by
  constructor
  · intro a b hab
    obtain ⟨k, hk, hUnique⟩ := classify_rep hn (encode n a)
    have hA : a.1 = k := hUnique _ (encode_in_section n a)
    have hB : b.1 = k := hUnique _ (hab ▸ encode_in_section n b)
    have hk' : a.1 = b.1 := hA.trans hB.symm
    apply Prod.ext hk'
    apply Subtype.ext
    have hEq := congrArg Subtype.val hab
    change orient a.1.1 (adjust a.1.2 false (gaussMap a.2.val)) =
      orient b.1.1 (adjust b.1.2 false (gaussMap b.2.val)) at hEq
    rw [← hk'] at hEq
    have hs := congrArg (fun v => adjust a.1.2 false (orient a.1.1 v)) hEq
    simp only [orient_involutive, adjust_involutive] at hs
    simpa only [gauss_left_inv] using congrArg gaussInv hs
  · intro v
    obtain ⟨k, hk, _⟩ := classify_rep hn v
    let w := adjust k.2 false (orient k.1 v.val)
    have hw : distinguished (red w) := by
      dsimp [w]
      rw [red_adjust, red_orient]
      exact hk
    have hMap := gauss_right_inv hw
    have hNorm : weightedForm (gaussInv w) = (n : ℤ) := by
      have hEq := gauss_norm (gaussInv w)
      rw [hMap] at hEq
      have hh : normSq w = (5 * n : ℕ) := by
        dsimp [w]
        rw [normSq_adjust, normSq_orient]
        exact v.property
      rw [hh] at hEq
      push_cast at hEq
      omega
    refine ⟨⟨k, ⟨gaussInv w, hNorm⟩⟩, ?_⟩
    apply Subtype.ext
    change orient k.1 (adjust k.2 false (gaussMap (gaussInv w))) = v.val
    rw [hMap]
    dsimp [w]
    rw [adjust_involutive, orient_involutive]

private theorem representation_count {n : ℕ} (hn : ¬ 5 ∣ n) :
    Nat.card (ThreeRep (5 * n)) = 6 * Nat.card (WeightedRep n) := by
  rw [← Nat.card_congr (Equiv.ofBijective (encode n) (encode_bijective hn)), Nat.card_prod]
  have hIndex : Nat.card SectionIndex = 6 := by rw [Nat.card_eq_fintype_card]; decide
  rw [hIndex]

private abbrev Congruence := ZMod 5 × ZMod 5

private def onPlane (a : Congruence) (v : Triple (ZMod 5)) : Prop :=
  a.1 * v.1 + a.2 * v.2.1 + v.2.2 = 0

private instance (a : Congruence) (v : Triple (ZMod 5)) : Decidable (onPlane a v) := by
  unfold onPlane
  infer_instance

set_option maxRecDepth 6000 in
set_option maxHeartbeats 2000000 in
private theorem plane_count :
    ∀ v : Triple (ZMod 5), v.1 ^ 2 + v.2.1 ^ 2 ≠ 0 →
      (Finset.univ.filter (fun a : Congruence => onPlane a v)).card = 5 := by
  decide +kernel

private def planeMap (a : Congruence) (v : Triple ℤ) : Triple ℤ :=
  (v.1, v.2.1, 5 * v.2.2 - (a.1.val : ℤ) * v.1 - (a.2.val : ℤ) * v.2.1)

private def planeForm (a : Congruence) (v : Triple ℤ) : ℤ :=
  v.1 ^ 2 + v.2.1 ^ 2 +
    5 * (5 * v.2.2 - (a.1.val : ℤ) * v.1 - (a.2.val : ℤ) * v.2.1) ^ 2

private lemma planeMap_mem (a : Congruence) (v : Triple ℤ) : onPlane a (red (planeMap a v)) := by
  unfold onPlane red planeMap
  dsimp only
  push_cast
  simp only [ZMod.natCast_zmod_val, show (5 : ZMod 5) = 0 by decide, zero_mul]
  ring

private def planeEquiv (a : Congruence) : Triple ℤ ≃ {v : Triple ℤ // onPlane a (red v)} where
  toFun v := ⟨planeMap a v, planeMap_mem a v⟩
  invFun v := (v.val.1, v.val.2.1,
    (v.val.2.2 + (a.1.val : ℤ) * v.val.1 + (a.2.val : ℤ) * v.val.2.1) / 5)
  left_inv v := by
    obtain ⟨x, y, z⟩ := v
    change (x, y, (5 * z - (a.1.val : ℤ) * x - (a.2.val : ℤ) * y +
      (a.1.val : ℤ) * x + (a.2.val : ℤ) * y) / 5) = (x, y, z)
    rw [show 5 * z - (a.1.val : ℤ) * x - (a.2.val : ℤ) * y +
      (a.1.val : ℤ) * x + (a.2.val : ℤ) * y = z * 5 by ring]
    simp
  right_inv v := by
    apply Subtype.ext
    obtain ⟨⟨x, y, z⟩, hz⟩ := v
    have hd : (5 : ℤ) ∣ z + (a.1.val : ℤ) * x + (a.2.val : ℤ) * y := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 5).mp
      push_cast
      simp only [ZMod.natCast_zmod_val]
      have hh : a.1 * (x : ZMod 5) + a.2 * (y : ZMod 5) + (z : ZMod 5) = 0 := hz
      linear_combination hh
    change (x, y, 5 * ((z + (a.1.val : ℤ) * x + (a.2.val : ℤ) * y) / 5) -
      (a.1.val : ℤ) * x - (a.2.val : ℤ) * y) = (x, y, z)
    rw [mul_comm 5, Int.ediv_mul_cancel hd]
    congr 2
    ring

private abbrev OnPlaneRep (n : ℕ) (a : Congruence) :=
  {v : WeightedRep n // onPlane a (red v.val)}

private def planeRepEquiv (n : ℕ) (a : Congruence) :
    {v : Triple ℤ // planeForm a v = (n : ℤ)} ≃ OnPlaneRep n a :=
  ((planeEquiv a).subtypeEquiv
    (q := fun v => weightedForm v.val = (n : ℤ))
    (fun _ => Iff.rfl)).trans
    { toFun := fun v => ⟨⟨v.val.val, v.property⟩, v.val.property⟩
      invFun := fun v => ⟨⟨v.val.val, v.property⟩, v.val.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

private instance weightedFinite (n : ℕ) : Finite (WeightedRep n) := by
  let box := Set.Icc (-(↑n + 1) : ℤ) ((n : ℤ) + 1)
  have hbox : box.Finite := Set.finite_Icc _ _
  have hs : {v : Triple ℤ | weightedForm v = (n : ℤ)}.Finite := by
    refine (hbox.prod (hbox.prod hbox)).subset ?_
    intro v hv
    change v.1 ∈ box ∧ v.2.1 ∈ box ∧ v.2.2 ∈ box
    have hv' : v.1 ^ 2 + v.2.1 ^ 2 + 5 * v.2.2 ^ 2 = (n : ℤ) := hv
    have hb {x : ℤ} (hx : x ^ 2 ≤ (n : ℤ)) : x ∈ box :=
      ⟨by nlinarith only [hx, sq_nonneg (2 * x + 1)],
        by nlinarith only [hx, sq_nonneg (2 * x - 1)]⟩
    exact ⟨hb (by linarith only [hv', sq_nonneg v.2.1, sq_nonneg v.2.2]),
      hb (by linarith only [hv', sq_nonneg v.1, sq_nonneg v.2.2]),
      hb (by linarith only [hv', sq_nonneg v.1, sq_nonneg v.2.1, sq_nonneg v.2.2])⟩
  exact hs.to_subtype

private def swapIncidence (n : ℕ) :
    (Σ a : Congruence, OnPlaneRep n a) ≃
      (Σ v : WeightedRep n, {a : Congruence // onPlane a (red v.val)}) where
  toFun v := ⟨v.2.val, ⟨v.1, v.2.property⟩⟩
  invFun v := ⟨v.2.val, ⟨v.1, v.2.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem total_plane_count {n : ℕ} (hn : ¬ 5 ∣ n) :
    (∑ a : Congruence, Nat.card {v : Triple ℤ // planeForm a v = (n : ℤ)}) =
      5 * Nat.card (WeightedRep n) := by
  let : Fintype (WeightedRep n) := Fintype.ofFinite _
  have hcount (v : WeightedRep n) :
      Nat.card {a : Congruence // onPlane a (red v.val)} = 5 := by
    have hz := congrArg (fun x : ℤ => (x : ZMod 5)) v.property
    unfold weightedForm at hz
    push_cast at hz
    simp [show (5 : ZMod 5) = 0 by decide] at hz
    have hv : (red v.val).1 ^ 2 + (red v.val).2.1 ^ 2 ≠ 0 := by
      rw [show (red v.val).1 ^ 2 + (red v.val).2.1 ^ 2 = (n : ZMod 5) from hz]
      exact fun h => hn ((ZMod.natCast_eq_zero_iff n 5).mp h)
    rw [Nat.card_eq_fintype_card,
      Fintype.card_of_subtype (Finset.univ.filter fun a : Congruence => onPlane a (red v.val))
        (fun a => by simp only [Finset.mem_filter, Finset.mem_univ, true_and])]
    exact plane_count _ hv
  calc
    _ = ∑ a : Congruence, Nat.card (OnPlaneRep n a) := by
      apply Finset.sum_congr rfl
      intro a _
      exact Nat.card_congr (planeRepEquiv n a)
    _ = Nat.card (Σ a, OnPlaneRep n a) := Nat.card_sigma.symm
    _ = Nat.card (Σ v : WeightedRep n, {a : Congruence // onPlane a (red v.val)}) :=
      Nat.card_congr (swapIncidence n)
    _ = 5 * Nat.card (WeightedRep n) := by
      rw [Nat.card_sigma]
      simp only [hcount, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        Nat.card_eq_fintype_card, Nat.cast_id, mul_comm]

open Filter

/-- The odd, locally representable cases of the lower estimate for three squares. -/
def H1 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ c : ℝ, 0 < c ∧
    ∀ᶠ n : ℕ in atTop, Odd n → n % 8 ≠ 7 →
      c * (n : ℝ) ^ ((1 : ℝ) / 2 - ε) ≤
        (Nat.card {v : ℤ × ℤ × ℤ // v.1 ^ 2 + v.2.1 ^ 2 + v.2.2 ^ 2 = (n : ℤ)} : ℝ)

/-- The power-saving error from the genus average in the coprime range. -/
def H2 : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, 0 < C ∧
    ∀ᶠ n : ℕ in atTop, Odd n → ¬ 5 ∣ n →
      let rf : ℝ := Nat.card {v : ℤ × ℤ × ℤ //
        v.1 ^ 2 + v.2.1 ^ 2 + 125 * v.2.2 ^ 2 = (n : ℤ)}
      let rg : ℝ := (↑(∑ a : ZMod 5 × ZMod 5, Nat.card {v : ℤ × ℤ × ℤ //
        v.1 ^ 2 + v.2.1 ^ 2 + 5 * (5 * v.2.2 - (a.1.val : ℤ) * v.1 -
          (a.2.val : ℤ) * v.2.1) ^ 2 = (n : ℤ)}) : ℝ) / 25
      |rf - rg| ≤ C * (n : ℝ) ^ ((1 : ℝ) / 2 - δ)

section

private noncomputable def baseCount (n : ℕ) : ℕ :=
  Nat.card {v : Triple ℤ // v.1 ^ 2 + v.2.1 ^ 2 + 125 * v.2.2 ^ 2 = (n : ℤ)}

private noncomputable def genusCount (n : ℕ) : ℝ :=
  (↑(∑ a : Congruence, Nat.card {v : Triple ℤ // planeForm a v = (n : ℤ)}) : ℝ) / 25

private lemma genus_exact {n : ℕ} (hn : ¬ 5 ∣ n) :
    genusCount n = (Nat.card (ThreeRep (5 * n)) : ℝ) / 30 := by
  unfold genusCount
  rw [total_plane_count hn, representation_count hn]
  push_cast
  ring

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

theorem main : H1 → H2 → OMA.R_Erdos940_erdos_940_variants_three_powerful_R1_H2_R2.H1 := by
  intro hThree hError
  obtain ⟨δ, hδ, C, _, hApprox⟩ := hError
  obtain ⟨c, hc, hLower⟩ := hThree (δ / 2) (by positivity)
  let a : ℝ := (1 : ℝ) / 2 - δ / 2
  let b : ℝ := (1 : ℝ) / 2 - δ
  let c' : ℝ := c * (5 : ℝ) ^ a / 30
  have hc' : 0 < c' := by positivity
  have hb : b < a := by dsimp [a, b]; linarith
  have hMul : Tendsto (fun n : ℕ => 5 * n) atTop atTop :=
    tendsto_atTop.2 fun k => (eventually_ge_atTop k).mono fun n hn => by omega
  have hgrowth := eventually_domination (C := C) hb hc'
  filter_upwards [hApprox, hMul.eventually hLower, hgrowth] with n hApprox hLower hgrowth
  intro hOdd hFive hEight
  have h3 : c * ((5 * n : ℕ) : ℝ) ^ a ≤ (Nat.card (ThreeRep (5 * n)) : ℝ) :=
    hLower ((by decide : Odd 5).mul hOdd) (by omega)
  have hgen : c' * (n : ℝ) ^ a ≤ genusCount n := by
    rw [genus_exact hFive]
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 30)).2
    calc
      c' * (n : ℝ) ^ a * 30 = c * ((5 : ℝ) ^ a * (n : ℝ) ^ a) := by dsimp [c']; ring
      _ = c * ((5 * n : ℕ) : ℝ) ^ a := by
        rw [Nat.cast_mul, Nat.cast_ofNat, Real.mul_rpow (by norm_num) (by positivity)]
      _ ≤ (Nat.card (ThreeRep (5 * n)) : ℝ) := h3
  have herror : |(baseCount n : ℝ) - genusCount n| ≤ C * (n : ℝ) ^ b :=
    hApprox hOdd hFive
  have hpos : (0 : ℝ) < baseCount n := by
    have hh := (abs_le.mp herror).1
    linarith only [hh, hgen, hgrowth]
  have hcard : 0 < baseCount n := by exact_mod_cast hpos
  unfold baseCount at hcard
  obtain ⟨⟨⟨x, y, z⟩, hv⟩⟩ := (Nat.card_ne_zero.mp hcard.ne').1
  exact ⟨x, y, z, by norm_num at hv ⊢; exact hv⟩

end

end OMA.R_Erdos940_erdos_940_variants_three_powerful_R1_H2_R2_H1_R1
