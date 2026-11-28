import OMAReductions.R_SymbolLengthMilnorKTheory_symbol_length_problem_variants_zero_mem_of_lt_R1

/-!
# Proof of `SymbolLengthMilnorKTheory.symbol_length_problem.variants.zero_mem_of_lt.R1.H1`

For every odd prime `p`, `K_3^M(ℂ(x, y)) / p = 0`.
Elementary self-contained proof via:
1. Discrete valuation residue ring homomorphisms `∂_v` on `MilnorK (RatFunc E) p`;
2. Degree-2 lifting and Weil reciprocity on `K_2^M(E(t)) / p`;
3. Milnor's degree-filtration exactness on `K_3^M(E(t)) / p`;
4. Norm-symbol vanishing `of p b * of p (N_{L/E} z) = 0` for `L = E[t]/(t^p - b)`;
5. Tsen's theorem for finite extensions `E = ℂ(x)[y]/(π)` via `OMA.ZL.Artin2.exists_common_zero'`,
   giving `K_2^M(E) / p = 0`, and concluding `K_3^M(ℂ(x, y)) / p = 0` from (3) and `K_2^M(ℂ(x)) / p = 0`.
-/

namespace OMA.H1Proof

open MilnorK Polynomial

section BasicOddMilnorK

variable {F : Type*} [Field F]

theorem mk_neg_mul {p : ℕ} (x y : MilnorK F p) : (-x) * y = -(x * y) := by
  apply eq_neg_of_add_eq_zero_left
  rw [← add_mul, neg_add_cancel, zero_mul]

theorem mk_mul_neg {p : ℕ} (x y : MilnorK F p) : x * (-y) = -(x * y) := by
  apply eq_neg_of_add_eq_zero_left
  rw [← mul_add, neg_add_cancel, mul_zero]

theorem mk_neg_mul_neg {p : ℕ} (x y : MilnorK F p) : (-x) * (-y) = x * y := by
  rw [mk_neg_mul, mk_mul_neg, neg_neg]

theorem p_nsmul_eq_zero (p : ℕ) (x : MilnorK F p) : p • x = 0 := by
  rw [nsmul_eq_mul, natCast_eq_zero, zero_mul]

theorem of_pow_p (p : ℕ) (a : Fˣ) : of p (a ^ p) = 0 := by
  rw [of_pow, p_nsmul_eq_zero]

theorem of_neg_one_odd {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    of p (-1 : Fˣ) = 0 := by
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hpow : (-1 : Fˣ) ^ p = -1 := by
    ext
    simp [hodd.neg_one_pow]
  rw [← hpow, of_pow_p]

theorem of_neg_odd {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (a : Fˣ) :
    of p (-a) = of p a := by
  have : (-a : Fˣ) = (-1 : Fˣ) * a := by simp
  rw [this, of_mul, of_neg_one_odd hp hp2, zero_add]

theorem of_mul_self_odd {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (a : Fˣ) :
    of p a * of p a = 0 := by
  by_cases ha : a = 1
  · simp [ha]
  have h1 : (1 : F) - (a : F) ≠ 0 := by
    intro h
    apply ha
    apply Units.ext
    show (a : F) = 1
    linear_combination -h
  have h2 : (1 : F) - ((a⁻¹ : Fˣ) : F) ≠ 0 := by
    intro h
    apply ha
    apply Units.ext
    show (a : F) = 1
    have hinv : ((a⁻¹ : Fˣ) : F) = 1 := by linear_combination -h
    have := congrArg Inv.inv hinv
    simpa using this
  set b := Units.mk0 _ h1
  set c := Units.mk0 _ h2
  have hb : of p a * of p b = 0 := of_mul_of_eq_zero p a b (by simp [b])
  have hc : of p a⁻¹ * of p c = 0 := of_mul_of_eq_zero p a⁻¹ c (by simp [c])
  have hc' : of p a * of p c = 0 := by
    rw [of_inv, mk_neg_mul, neg_eq_zero] at hc
    exact hc
  have hneg : (-a : Fˣ) = b * c⁻¹ := by
    have ha0 : (a : F) ≠ 0 := a.ne_zero
    have ha1 : (a : F) - 1 ≠ 0 := fun h => h1 (by linear_combination -h)
    apply Units.ext
    simp only [Units.val_neg, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0, b, c]
    have h2' : (1 : F) - (a : F)⁻¹ = ((a : F) - 1) / (a : F) := by field_simp
    rw [h2']
    field_simp
    ring
  calc of p a * of p a
      = of p a * of p (-a) := by rw [of_neg_odd hp hp2]
    _ = of p a * of p (b * c⁻¹) := by rw [hneg]
    _ = of p a * of p b - of p a * of p c := by
        rw [of_mul, of_inv, mul_add, mk_mul_neg, sub_eq_add_neg]
    _ = 0 := by rw [hb, hc', sub_self]

theorem of_mul_anticomm {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (a b : Fˣ) :
    of p a * of p b = -(of p b * of p a) := by
  have h := of_mul_self_odd hp hp2 (a * b)
  rw [of_mul, mul_add, add_mul, add_mul, of_mul_self_odd hp hp2 a, of_mul_self_odd hp hp2 b,
    zero_add, add_zero] at h
  exact eq_neg_of_add_eq_zero_right h

theorem of_mul_eq_zero_of_add_eq_zero {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (a b : Fˣ)
    (h : (a : F) + (b : F) = 0) : of p a * of p b = 0 := by
  have hab : b = -a := Units.ext (by show (b : F) = -(a : F); linear_combination h)
  rw [hab, of_neg_odd hp hp2, of_mul_self_odd hp hp2]

/-- Functoriality of `MilnorK · p` along a ring homomorphism between fields. -/
noncomputable def mapRingHom {E : Type*} [Field E] (p : ℕ) (f : F →+* E) :
    MilnorK F p →+* MilnorK E p :=
  RingQuot.lift ⟨(TensorAlgebra.lift ℤ
      ((ofHom (F := E) p).comp
        (AddMonoidHom.mk' (fun a : Additive Fˣ => Additive.ofMul (Units.map f.toMonoidHom a.toMul))
          (fun a b => by simp))).toIntLinearMap).toRingHom, by
    intro x y h
    cases h with
    | steinberg a b hab =>
      simp only [RingHom.toMonoidHom_eq_coe, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        map_mul, map_zero, TensorAlgebra.lift_ι_apply, AddMonoidHom.coe_toIntLinearMap,
        AddMonoidHom.comp_apply, AddMonoidHom.mk'_apply, ofHom_apply, toMul_ofMul]
      apply of_mul_of_eq_zero
      simpa [map_add, map_one] using congrArg f hab
    | natCast =>
      simp⟩

@[simp]
theorem mapRingHom_of {E : Type*} [Field E] (p : ℕ) (f : F →+* E) (a : Fˣ) :
    mapRingHom p f (of p a) = of p (Units.map f.toMonoidHom a) := by
  simp [mapRingHom, of, RingQuot.lift_mkRingHom_apply]

theorem mapRingHom_grade {E : Type*} [Field E] (p : ℕ) (f : F →+* E) (n : ℕ)
    {x : MilnorK F p} (hx : x ∈ grade F p n) :
    mapRingHom p f x ∈ grade E p n := by
  refine AddSubgroup.closure_induction ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨s, rfl⟩
    have : mapRingHom p f (symbol p s) = symbol p (fun i => Units.map f.toMonoidHom (s i)) := by
      simp only [symbol, map_list_prod, List.map_ofFn]
      congr 1
      ext i
      simp
    rw [this]
    exact symbol_mem_grade E p _
  · simp
  · intro a b _ _ ha hb
    rw [map_add]
    exact (grade E p n).add_mem ha hb
  · intro a _ ha
    rw [map_neg]
    exact (grade E p n).neg_mem ha

theorem grade_eq_bot_of_ringEquiv {E : Type*} [Field E] (p n : ℕ) (e : F ≃+* E)
    (h : grade E p n = ⊥) : grade F p n = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have h1 : mapRingHom p (e : F →+* E) x ∈ grade E p n := mapRingHom_grade p _ n hx
  rw [h, AddSubgroup.mem_bot] at h1
  have hcomp : ∀ z : MilnorK F p,
      mapRingHom p (e.symm : E →+* F) (mapRingHom p (e : F →+* E) z) = z := by
    intro z
    obtain ⟨y, rfl⟩ := RingQuot.mkRingHom_surjective (MilnorK.Rel F p) z
    induction y using TensorAlgebra.induction with
    | algebraMap r => simp
    | ι a =>
      change mapRingHom p (e.symm : E →+* F) (mapRingHom p (e : F →+* E) (of p a.toMul)) =
        of p a.toMul
      rw [mapRingHom_of, mapRingHom_of]
      congr 1
      ext
      simp
    | add a b iha ihb => simp [map_add, iha, ihb]
    | mul a b iha ihb => simp [map_mul, iha, ihb]
  have hx0 : x = 0 := by
    rw [← hcomp x, h1, map_zero]
  simpa using hx0

/-- Parity involution on `MilnorK F p` sending `{a}` to `-{a}`. -/
noncomputable def parity (F : Type*) [Field F] (p : ℕ) : MilnorK F p →+* MilnorK F p :=
  RingQuot.lift ⟨(TensorAlgebra.lift ℤ (-(ofHom (F := F) p)).toIntLinearMap).toRingHom, by
    intro x y h
    cases h with
    | steinberg a b hab =>
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_mul, map_zero,
        TensorAlgebra.lift_ι_apply, AddMonoidHom.coe_toIntLinearMap, AddMonoidHom.neg_apply,
        ofHom_apply, toMul_ofMul]
      rw [mk_neg_mul_neg]
      exact of_mul_of_eq_zero p a b hab
    | natCast => simp⟩

@[simp]
theorem parity_of (p : ℕ) (a : Fˣ) : parity F p (of p a) = -of p a := by
  simp [parity, of, RingQuot.lift_mkRingHom_apply]

end BasicOddMilnorK

section TwistDualAndResidue

/-- Twisted dual numbers over `MilnorK κ p` with multiplication
`(a₁, b₁) * (a₂, b₂) = (a₁ * a₂, a₁ * b₂ + b₁ * parity a₂)`. -/
structure TwistDual (κ : Type*) [Field κ] (p : ℕ) where
  fst : MilnorK κ p
  snd : MilnorK κ p

namespace TwistDual

variable {κ : Type*} [Field κ] {p : ℕ}

theorem ext {x y : TwistDual κ p} (h1 : x.fst = y.fst) (h2 : x.snd = y.snd) : x = y := by
  cases x; cases y; simp_all

instance : Zero (TwistDual κ p) := ⟨⟨0, 0⟩⟩
instance : One (TwistDual κ p) := ⟨⟨1, 0⟩⟩
instance : Add (TwistDual κ p) := ⟨fun x y => ⟨x.fst + y.fst, x.snd + y.snd⟩⟩
instance : Neg (TwistDual κ p) := ⟨fun x => ⟨-x.fst, -x.snd⟩⟩
instance : Sub (TwistDual κ p) := ⟨fun x y => ⟨x.fst - y.fst, x.snd - y.snd⟩⟩
noncomputable instance : Mul (TwistDual κ p) :=
  ⟨fun x y => ⟨x.fst * y.fst, x.fst * y.snd + x.snd * parity κ p y.fst⟩⟩
instance : NatCast (TwistDual κ p) := ⟨fun n => ⟨n, 0⟩⟩
instance : IntCast (TwistDual κ p) := ⟨fun n => ⟨n, 0⟩⟩

noncomputable instance : Ring (TwistDual κ p) where
  add_assoc a b c := by apply TwistDual.ext <;> exact add_assoc _ _ _
  zero_add a := by apply TwistDual.ext <;> exact zero_add _
  add_zero a := by apply TwistDual.ext <;> exact add_zero _
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel a := by apply TwistDual.ext <;> exact neg_add_cancel _
  add_comm a b := by apply TwistDual.ext <;> exact add_comm _ _
  sub_eq_add_neg a b := by apply TwistDual.ext <;> exact sub_eq_add_neg _ _
  mul_assoc a b c := by
    apply TwistDual.ext
    · exact mul_assoc _ _ _
    · show (a.fst * b.fst) * c.snd + (a.fst * b.snd + a.snd * parity κ p b.fst) * parity κ p c.fst =
        a.fst * (b.fst * c.snd + b.snd * parity κ p c.fst) +
          a.snd * parity κ p (b.fst * c.fst)
      rw [map_mul, mul_add, add_mul, mul_assoc, mul_assoc, mul_assoc, add_assoc]
  one_mul a := by
    apply TwistDual.ext
    · exact one_mul _
    · show 1 * a.snd + 0 * parity κ p a.fst = a.snd
      simp
  mul_one a := by
    apply TwistDual.ext
    · exact mul_one _
    · show a.fst * 0 + a.snd * parity κ p 1 = a.snd
      simp
  left_distrib a b c := by
    apply TwistDual.ext
    · exact left_distrib _ _ _
    · show a.fst * (b.snd + c.snd) + a.snd * parity κ p (b.fst + c.fst) =
        (a.fst * b.snd + a.snd * parity κ p b.fst) + (a.fst * c.snd + a.snd * parity κ p c.fst)
      rw [map_add, mul_add, mul_add]
      abel
  right_distrib a b c := by
    apply TwistDual.ext
    · exact right_distrib _ _ _
    · show (a.fst + b.fst) * c.snd + (a.snd + b.snd) * parity κ p c.fst =
        (a.fst * c.snd + a.snd * parity κ p c.fst) + (b.fst * c.snd + b.snd * parity κ p c.fst)
      rw [add_mul, add_mul]
      abel
  zero_mul a := by
    apply TwistDual.ext
    · exact zero_mul _
    · show 0 * a.snd + 0 * parity κ p a.fst = 0
      simp
  mul_zero a := by
    apply TwistDual.ext
    · exact mul_zero _
    · show a.fst * 0 + a.snd * parity κ p 0 = 0
      simp
  natCast_zero := by apply TwistDual.ext <;> exact Nat.cast_zero
  natCast_succ n := by
    apply TwistDual.ext
    · exact Nat.cast_succ n
    · exact (add_zero 0).symm
  intCast_ofNat n := by apply TwistDual.ext <;> rfl
  intCast_negSucc n := by
    apply TwistDual.ext
    · exact Int.cast_negSucc n
    · exact neg_zero.symm

@[simp] theorem fst_zero : (0 : TwistDual κ p).fst = 0 := rfl
@[simp] theorem snd_zero : (0 : TwistDual κ p).snd = 0 := rfl
@[simp] theorem fst_one : (1 : TwistDual κ p).fst = 1 := rfl
@[simp] theorem snd_one : (1 : TwistDual κ p).snd = 0 := rfl
@[simp] theorem fst_add (x y : TwistDual κ p) : (x + y).fst = x.fst + y.fst := rfl
@[simp] theorem snd_add (x y : TwistDual κ p) : (x + y).snd = x.snd + y.snd := rfl
@[simp] theorem fst_neg (x : TwistDual κ p) : (-x).fst = -x.fst := rfl
@[simp] theorem snd_neg (x : TwistDual κ p) : (-x).snd = -x.snd := rfl
@[simp] theorem fst_mul (x y : TwistDual κ p) : (x * y).fst = x.fst * y.fst := rfl
@[simp] theorem snd_mul (x y : TwistDual κ p) :
    (x * y).snd = x.fst * y.snd + x.snd * parity κ p y.fst := rfl
@[simp] theorem fst_natCast (n : ℕ) : (n : TwistDual κ p).fst = (n : MilnorK κ p) := rfl
@[simp] theorem snd_natCast (n : ℕ) : (n : TwistDual κ p).snd = 0 := rfl

end TwistDual

/-- Data of a discrete valuation with a chosen uniformizer, giving a residue map on `MilnorK`. -/
structure DiscreteValData (K κ : Type*) [Field K] [Field κ] where
  val : Additive Kˣ →+ ℤ
  res : Kˣ →* κˣ
  steinberg_pos : ∀ a b : Kˣ, (a : K) + (b : K) = 1 → 0 < val (Additive.ofMul a) →
    val (Additive.ofMul b) = 0 ∧ res b = 1
  steinberg_zero_pos : ∀ a b : Kˣ, (a : K) + (b : K) = 1 →
    val (Additive.ofMul a) = 0 → 0 < val (Additive.ofMul b) → res a = 1
  steinberg_zero_zero : ∀ a b : Kˣ, (a : K) + (b : K) = 1 →
    val (Additive.ofMul a) = 0 → val (Additive.ofMul b) = 0 → (res a : κ) + (res b : κ) = 1
  steinberg_neg : ∀ a b : Kˣ, (a : K) + (b : K) = 1 → val (Additive.ofMul a) < 0 →
    val (Additive.ofMul b) = val (Additive.ofMul a) ∧ res b = -(res a)

/-- The full Milnor residue ring homomorphism `MilnorK K p →+* TwistDual κ p`. -/
noncomputable def DiscreteValData.theta {K κ : Type*} [Field K] [Field κ]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (D : DiscreteValData K κ) :
    MilnorK K p →+* TwistDual κ p :=
  let φ : Additive Kˣ →+ TwistDual κ p :=
    { toFun := fun a => ⟨of p (D.res a.toMul), (D.val a : MilnorK κ p)⟩
      map_zero' := by apply TwistDual.ext <;> simp
      map_add' := fun a b => by
        apply TwistDual.ext
        · change of p (D.res (a.toMul * b.toMul)) = of p (D.res a.toMul) + of p (D.res b.toMul)
          rw [map_mul, of_mul]
        · change ((D.val (a + b) : ℤ) : MilnorK κ p) = (D.val a : MilnorK κ p) + (D.val b : MilnorK κ p)
          rw [map_add, Int.cast_add] }
  RingQuot.lift ⟨(TensorAlgebra.lift ℤ φ.toIntLinearMap).toRingHom, by
    intro x y h
    cases h with
    | steinberg a b hab =>
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_mul, map_zero,
        TensorAlgebra.lift_ι_apply, AddMonoidHom.coe_toIntLinearMap]
      change (⟨of p (D.res a), (D.val (Additive.ofMul a) : MilnorK κ p)⟩ : TwistDual κ p) *
        ⟨of p (D.res b), (D.val (Additive.ofMul b) : MilnorK κ p)⟩ = 0
      rcases lt_trichotomy (D.val (Additive.ofMul a)) 0 with hneg | hzero | hpos
      · obtain ⟨hvb, hrb⟩ := D.steinberg_neg a b hab hneg
        apply TwistDual.ext
        · simp only [TwistDual.fst_mul, TwistDual.fst_zero, hrb, of_neg_odd hp hp2,
            of_mul_self_odd hp hp2]
        · simp only [TwistDual.snd_mul, TwistDual.snd_zero, hvb, hrb, of_neg_odd hp hp2,
            parity_of]
          rw [mk_mul_neg, ← Int.cast_comm (D.val (Additive.ofMul a)) (of p (D.res a))]
          exact add_neg_cancel _
      · rcases lt_trichotomy (D.val (Additive.ofMul b)) 0 with hbneg | hbzero | hbpos
        · have hab' : (b : K) + (a : K) = 1 := by rw [add_comm]; exact hab
          obtain ⟨hva, _⟩ := D.steinberg_neg b a hab' hbneg
          omega
        · have hres := D.steinberg_zero_zero a b hab hzero hbzero
          apply TwistDual.ext
          · simp only [TwistDual.fst_mul, TwistDual.fst_zero]
            exact of_mul_of_eq_zero p _ _ hres
          · simp [hzero, hbzero]
        · have hra := D.steinberg_zero_pos a b hab hzero hbpos
          apply TwistDual.ext
          · simp [hra]
          · simp [hzero, hra]
      · obtain ⟨hvb, hrb⟩ := D.steinberg_pos a b hab hpos
        apply TwistDual.ext
        · simp [hrb]
        · simp [hvb, hrb]
    | natCast =>
      apply TwistDual.ext
      · simp
      · simp⟩

@[simp]
theorem DiscreteValData.theta_of {K κ : Type*} [Field K] [Field κ]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (D : DiscreteValData K κ) (a : Kˣ) :
    D.theta hp hp2 (of p a) = ⟨of p (D.res a), (D.val (Additive.ofMul a) : MilnorK κ p)⟩ := by
  simp [DiscreteValData.theta, of, RingQuot.lift_mkRingHom_apply]

/-- The additive residue homomorphism `∂_v : MilnorK K p →+ MilnorK κ p`. -/
noncomputable def DiscreteValData.partialHom {K κ : Type*} [Field K] [Field κ]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (D : DiscreteValData K κ) :
    MilnorK K p →+ MilnorK κ p where
  toFun x := (D.theta hp hp2 x).snd
  map_zero' := by simp
  map_add' x y := by simp

theorem DiscreteValData.partialHom_of_mul_of_val_zero {K κ : Type*} [Field K] [Field κ]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (D : DiscreteValData K κ) (a : Kˣ)
    (ha : D.val (Additive.ofMul a) = 0) (y : MilnorK K p) :
    D.partialHom hp hp2 (of p a * y) = of p (D.res a) * D.partialHom hp hp2 y := by
  simp [DiscreteValData.partialHom, ha]

theorem DiscreteValData.partialHom_mul_of_val_zero {K κ : Type*} [Field K] [Field κ]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (D : DiscreteValData K κ)
    (x y : MilnorK K p) (hx : (D.theta hp hp2 x).snd = 0) (hy : (D.theta hp hp2 y).snd = 0) :
    D.partialHom hp hp2 (x * y) = 0 := by
  simp [DiscreteValData.partialHom, hx, hy]

theorem DiscreteValData.partialHom_grade_succ {K κ : Type*} [Field K] [Field κ]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (D : DiscreteValData K κ)
    (n : ℕ) {x : MilnorK K p} (hx : x ∈ grade K p (n + 1)) :
    D.partialHom hp hp2 x ∈ grade κ p n := by
  have hgen : ∀ (m : ℕ) (s : Fin m → Kˣ),
      (D.theta hp hp2 (symbol p s)).fst ∈ grade κ p m ∧
      (∀ k, m = k + 1 → (D.theta hp hp2 (symbol p s)).snd ∈ grade κ p k) := by
    intro m
    induction m with
    | zero =>
      intro s
      refine ⟨?_, fun k hk => by omega⟩
      simp only [symbol_zero, map_one, TwistDual.fst_one]
      exact one_mem_grade_zero κ p
    | succ m ih =>
      intro s
      obtain ⟨hfst, hsnd⟩ := ih (fun i => s i.succ)
      have hsym : symbol p s = of p (s 0) * symbol p (fun i => s i.succ) := symbol_succ p s
      have hmul_grade : ∀ (u : κˣ) (r : ℕ) {y : MilnorK κ p},
          y ∈ grade κ p r → of p u * y ∈ grade κ p (r + 1) := by
        intro u r y hy
        refine AddSubgroup.closure_induction ?_ ?_ ?_ ?_ hy
        · rintro _ ⟨t, rfl⟩
          have : of p u * symbol p t = symbol p (Fin.cons u t) := by
            rw [symbol_succ]
            simp
          rw [this]
          exact symbol_mem_grade κ p _
        · simp
        · intro a b _ _ ha hb; rw [mul_add]; exact (grade κ p (r + 1)).add_mem ha hb
        · intro a _ ha; rw [mk_mul_neg]; exact (grade κ p (r + 1)).neg_mem ha
      have hpar_grade : ∀ (r : ℕ) {y : MilnorK κ p},
          y ∈ grade κ p r → parity κ p y ∈ grade κ p r := by
        intro r y hy
        refine AddSubgroup.closure_induction ?_ ?_ ?_ ?_ hy
        · rintro _ ⟨t, rfl⟩
          have hps : ∀ (j : ℕ) (t : Fin j → κˣ),
              parity κ p (symbol p t) = (-1 : ℤ) ^ j • symbol p t := by
            intro j
            induction j with
            | zero => intro _; simp
            | succ j ihj =>
              intro t
              rw [symbol_succ, map_mul, parity_of, ihj, pow_succ, mul_comm, mul_zsmul,
                neg_one_zsmul, mk_neg_mul, zsmul_eq_mul, zsmul_eq_mul, ← mul_assoc,
                ← Int.cast_comm ((-1 : ℤ) ^ j) (of p (t 0)), mul_assoc]
          rw [hps]
          exact (grade κ p r).zsmul_mem (symbol_mem_grade κ p t) _
        · simp
        · intro a b _ _ ha hb; rw [map_add]; exact (grade κ p r).add_mem ha hb
        · intro a _ ha; rw [map_neg]; exact (grade κ p r).neg_mem ha
      refine ⟨?_, ?_⟩
      · rw [hsym, map_mul, TwistDual.fst_mul, DiscreteValData.theta_of]
        exact hmul_grade _ _ hfst
      · intro k hk
        have hmk : m = k := by omega
        subst hmk
        rw [hsym, map_mul, TwistDual.snd_mul, DiscreteValData.theta_of]
        refine (grade κ p m).add_mem ?_ ?_
        · cases m with
          | zero =>
            simp only [symbol_zero, map_one, TwistDual.snd_one, mul_zero]
            exact (grade κ p 0).zero_mem
          | succ m' =>
            exact hmul_grade _ m' (hsnd m' rfl)
        · rw [← zsmul_eq_mul]
          exact (grade κ p m).zsmul_mem (hpar_grade m hfst) _
  refine AddSubgroup.closure_induction ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨s, rfl⟩
    exact (hgen (n + 1) s).2 n rfl
  · simp
  · intro a b _ _ ha hb; rw [map_add]; exact (grade κ p n).add_mem ha hb
  · intro a _ ha; rw [map_neg]; exact (grade κ p n).neg_mem ha

end TwistDualAndResidue

section RatFuncValuations

variable {E : Type*} [Field E]

/-- Helper: `algMap` of a nonzero polynomial is a unit in `RatFunc E`. -/
noncomputable def polyUnit (f : Polynomial E) (hf : f ≠ 0) : (RatFunc E)ˣ :=
  Units.mk0 (algebraMap (Polynomial E) (RatFunc E) f)
    ((map_ne_zero_iff _ (IsFractionRing.injective (Polynomial E) (RatFunc E))).mpr hf)

@[simp]
theorem val_polyUnit (f : Polynomial E) (hf : f ≠ 0) :
    (polyUnit f hf : RatFunc E) = algebraMap (Polynomial E) (RatFunc E) f := rfl

theorem polyUnit_mul (f g : Polynomial E) (hf : f ≠ 0) (hg : g ≠ 0) :
    polyUnit (f * g) (mul_ne_zero hf hg) = polyUnit f hf * polyUnit g hg := by
  apply Units.ext
  simp [polyUnit]

theorem polyUnit_one : polyUnit (1 : Polynomial E) one_ne_zero = 1 := by
  apply Units.ext
  simp [polyUnit]

theorem ratFunc_unit_eq_div (x : (RatFunc E)ˣ) :
    x = polyUnit x.1.num (RatFunc.num_ne_zero x.ne_zero) *
      (polyUnit x.1.denom (RatFunc.denom_ne_zero x.1))⁻¹ := by
  apply Units.ext
  simp only [Units.val_mul, Units.val_inv_eq_inv_val, val_polyUnit]
  rw [← div_eq_mul_inv, RatFunc.num_div_denom]

/-- The infinite discrete valuation on `RatFunc E` with uniformizer `t⁻¹`. -/
noncomputable def valInftyData (E : Type*) [Field E] : DiscreteValData (RatFunc E) E := by
  have hinj := IsFractionRing.injective (Polynomial E) (RatFunc E)
  have hval_wd : ∀ (f₁ g₁ f₂ g₂ : Polynomial E) (hf₁ : f₁ ≠ 0) (hg₁ : g₁ ≠ 0)
      (hf₂ : f₂ ≠ 0) (hg₂ : g₂ ≠ 0),
      algebraMap (Polynomial E) (RatFunc E) f₁ / algebraMap _ _ g₁ =
      algebraMap (Polynomial E) (RatFunc E) f₂ / algebraMap _ _ g₂ →
      ((g₁.natDegree : ℤ) - (f₁.natDegree : ℤ) = (g₂.natDegree : ℤ) - (f₂.natDegree : ℤ)) ∧
      (f₁.leadingCoeff / g₁.leadingCoeff = f₂.leadingCoeff / g₂.leadingCoeff) := by
    intro f₁ g₁ f₂ g₂ hf₁ hg₁ hf₂ hg₂ h
    have hg₁' : algebraMap (Polynomial E) (RatFunc E) g₁ ≠ 0 := (map_ne_zero_iff _ hinj).mpr hg₁
    have hg₂' : algebraMap (Polynomial E) (RatFunc E) g₂ ≠ 0 := (map_ne_zero_iff _ hinj).mpr hg₂
    have hcross : f₁ * g₂ = f₂ * g₁ := by
      apply hinj
      rw [map_mul, map_mul]
      field_simp at h
      linear_combination h
    constructor
    · have hdeg := congrArg Polynomial.natDegree hcross
      rw [Polynomial.natDegree_mul hf₁ hg₂, Polynomial.natDegree_mul hf₂ hg₁] at hdeg
      omega
    · have hlc := congrArg Polynomial.leadingCoeff hcross
      rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_mul] at hlc
      have hlc1 : g₁.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hg₁
      have hlc2 : g₂.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hg₂
      field_simp
      linear_combination hlc
  refine
    { val :=
        { toFun := fun a =>
            (a.toMul.1.denom.natDegree : ℤ) - (a.toMul.1.num.natDegree : ℤ)
          map_zero' := by simp [RatFunc.num_one, RatFunc.denom_one]
          map_add' := fun a b => by
            set x := a.toMul
            set y := b.toMul
            have h1 := RatFunc.num_ne_zero x.ne_zero
            have h2 := RatFunc.denom_ne_zero x.1
            have h3 := RatFunc.num_ne_zero y.ne_zero
            have h4 := RatFunc.denom_ne_zero y.1
            have h5 := RatFunc.num_ne_zero (x * y).ne_zero
            have h6 := RatFunc.denom_ne_zero (x * y).1
            have heq : algebraMap (Polynomial E) (RatFunc E) (x * y).1.num /
                algebraMap _ _ (x * y).1.denom =
                algebraMap (Polynomial E) (RatFunc E) (x.1.num * y.1.num) /
                algebraMap _ _ (x.1.denom * y.1.denom) := by
              rw [RatFunc.num_div_denom, map_mul, map_mul, ← div_mul_div_comm,
                RatFunc.num_div_denom, RatFunc.num_div_denom]
              rfl
            have hwd := (hval_wd _ _ _ _ h5 h6 (mul_ne_zero h1 h3) (mul_ne_zero h2 h4) heq).1
            rw [Polynomial.natDegree_mul h1 h3, Polynomial.natDegree_mul h2 h4] at hwd
            change ((x * y).1.denom.natDegree : ℤ) - ((x * y).1.num.natDegree : ℤ) =
              ((x.1.denom.natDegree : ℤ) - (x.1.num.natDegree : ℤ)) +
              ((y.1.denom.natDegree : ℤ) - (y.1.num.natDegree : ℤ))
            omega }
      res :=
        { toFun := fun x =>
            Units.mk0 (x.1.num.leadingCoeff / x.1.denom.leadingCoeff)
              (div_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr (RatFunc.num_ne_zero x.ne_zero))
                (Polynomial.leadingCoeff_ne_zero.mpr (RatFunc.denom_ne_zero x.1)))
          map_one' := by
            apply Units.ext
            simp [RatFunc.num_one, RatFunc.denom_one]
          map_mul' := fun x y => by
            apply Units.ext
            have h1 := RatFunc.num_ne_zero x.ne_zero
            have h2 := RatFunc.denom_ne_zero x.1
            have h3 := RatFunc.num_ne_zero y.ne_zero
            have h4 := RatFunc.denom_ne_zero y.1
            have h5 := RatFunc.num_ne_zero (x * y).ne_zero
            have h6 := RatFunc.denom_ne_zero (x * y).1
            have heq : algebraMap (Polynomial E) (RatFunc E) (x * y).1.num /
                algebraMap _ _ (x * y).1.denom =
                algebraMap (Polynomial E) (RatFunc E) (x.1.num * y.1.num) /
                algebraMap _ _ (x.1.denom * y.1.denom) := by
              rw [RatFunc.num_div_denom, map_mul, map_mul, ← div_mul_div_comm,
                RatFunc.num_div_denom, RatFunc.num_div_denom]
              rfl
            have hwd := (hval_wd _ _ _ _ h5 h6 (mul_ne_zero h1 h3) (mul_ne_zero h2 h4) heq).2
            rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_mul, ← div_mul_div_comm] at hwd
            exact hwd }
      steinberg_pos := ?_
      steinberg_zero_pos := ?_
      steinberg_zero_zero := ?_
      steinberg_neg := ?_ }
  all_goals
    intro a b hab
    set f := a.1.num
    set g := a.1.denom
    have hf : f ≠ 0 := RatFunc.num_ne_zero a.ne_zero
    have hg : g ≠ 0 := RatFunc.denom_ne_zero a.1
    have hgf : g - f ≠ 0 := by
      intro h
      have ha1 : (a : RatFunc E) = 1 := by
        rw [← RatFunc.num_div_denom a.1, show a.1.num = a.1.denom by linear_combination -h,
          div_self ((map_ne_zero_iff _ hinj).mpr hg)]
      have : (b : RatFunc E) = 0 := by linear_combination hab - ha1
      exact b.ne_zero this
    have hb_eq : algebraMap (Polynomial E) (RatFunc E) b.1.num /
        algebraMap _ _ b.1.denom =
        algebraMap (Polynomial E) (RatFunc E) (g - f) / algebraMap _ _ g := by
      rw [RatFunc.num_div_denom, map_sub, sub_div, div_self ((map_ne_zero_iff _ hinj).mpr hg),
        RatFunc.num_div_denom]
      linear_combination hab
    have hwd := hval_wd _ _ _ _ (RatFunc.num_ne_zero b.ne_zero) (RatFunc.denom_ne_zero b.1)
      hgf hg hb_eq
  · intro hpos
    change (0 : ℤ) < (g.natDegree : ℤ) - (f.natDegree : ℤ) at hpos
    have hlt : f.natDegree < g.natDegree := by omega
    have hdeg : (g - f).natDegree = g.natDegree := by
      rw [sub_eq_add_neg, Polynomial.natDegree_add_eq_left_of_natDegree_lt (by simpa using hlt)]
    have hlc : (g - f).leadingCoeff = g.leadingCoeff := by
      rw [sub_eq_add_neg, Polynomial.leadingCoeff_add_of_degree_lt' (by
        rw [Polynomial.degree_neg]
        exact Polynomial.degree_lt_degree hlt)]
    constructor
    · change (b.1.denom.natDegree : ℤ) - (b.1.num.natDegree : ℤ) = 0
      omega
    · apply Units.ext
      change b.1.num.leadingCoeff / b.1.denom.leadingCoeff = 1
      rw [hwd.2, hlc, div_self (Polynomial.leadingCoeff_ne_zero.mpr hg)]
  · intro hz hbpos
    change (g.natDegree : ℤ) - (f.natDegree : ℤ) = 0 at hz
    have hdeg_fg : f.natDegree = g.natDegree := by omega
    have hlt : (g - f).natDegree < g.natDegree := by
      change (b.1.denom.natDegree : ℤ) - (b.1.num.natDegree : ℤ) > 0 at hbpos
      omega
    have hlc_eq : f.leadingCoeff = g.leadingCoeff := by
      by_contra hne
      have hsub : (g - f).coeff g.natDegree ≠ 0 := by
        rw [Polynomial.coeff_sub, Polynomial.coeff_natDegree, ← hdeg_fg,
          Polynomial.coeff_natDegree]
        exact sub_ne_zero.mpr (Ne.symm hne)
      have hle : g.natDegree ≤ (g - f).natDegree := Polynomial.le_natDegree_of_ne_zero hsub
      omega
    apply Units.ext
    change f.leadingCoeff / g.leadingCoeff = 1
    rw [hlc_eq, div_self (Polynomial.leadingCoeff_ne_zero.mpr hg)]
  · intro hz hbz
    change (g.natDegree : ℤ) - (f.natDegree : ℤ) = 0 at hz
    have hdeg_fg : f.natDegree = g.natDegree := by omega
    have hdeg_sub : (g - f).natDegree = g.natDegree := by
      change (b.1.denom.natDegree : ℤ) - (b.1.num.natDegree : ℤ) = 0 at hbz
      omega
    have hlc_sub : (g - f).leadingCoeff = g.leadingCoeff - f.leadingCoeff := by
      rw [Polynomial.leadingCoeff, hdeg_sub, Polynomial.coeff_sub, Polynomial.coeff_natDegree,
        ← hdeg_fg, Polynomial.coeff_natDegree]
    change f.leadingCoeff / g.leadingCoeff + b.1.num.leadingCoeff / b.1.denom.leadingCoeff = 1
    rw [hwd.2, hlc_sub]
    have hg0 : g.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hg
    field_simp
    ring
  · intro hneg
    change (g.natDegree : ℤ) - (f.natDegree : ℤ) < 0 at hneg
    have hlt : g.natDegree < f.natDegree := by omega
    have hdeg : (g - f).natDegree = f.natDegree := by
      rw [sub_eq_add_neg, Polynomial.natDegree_add_eq_right_of_natDegree_lt (by simpa using hlt),
        Polynomial.natDegree_neg]
    have hlc : (g - f).leadingCoeff = -f.leadingCoeff := by
      rw [sub_eq_add_neg, add_comm, Polynomial.leadingCoeff_add_of_degree_lt' (by
        rw [Polynomial.degree_neg]
        exact Polynomial.degree_lt_degree hlt), Polynomial.leadingCoeff_neg]
    constructor
    · change (b.1.denom.natDegree : ℤ) - (b.1.num.natDegree : ℤ) =
        (g.natDegree : ℤ) - (f.natDegree : ℤ)
      omega
    · apply Units.ext
      change b.1.num.leadingCoeff / b.1.denom.leadingCoeff = -(f.leadingCoeff / g.leadingCoeff)
      rw [hwd.2, hlc, neg_div]

theorem valInftyData_polyUnit (f : Polynomial E) (hf : f ≠ 0) :
    (valInftyData E).val (Additive.ofMul (polyUnit f hf)) = -(f.natDegree : ℤ) ∧
    ((valInftyData E).res (polyUnit f hf) : E) = f.leadingCoeff := by
  have hinj := IsFractionRing.injective (Polynomial E) (RatFunc E)
  set x := polyUnit f hf
  have h1 := RatFunc.num_ne_zero x.ne_zero
  have h2 := RatFunc.denom_ne_zero x.1
  have hcross : x.1.num * 1 = f * x.1.denom := by
    apply hinj
    rw [map_mul, map_one, map_mul]
    have hnd := RatFunc.num_div_denom x.1
    have hd0 : algebraMap (Polynomial E) (RatFunc E) x.1.denom ≠ 0 :=
      (map_ne_zero_iff _ hinj).mpr h2
    rw [div_eq_iff hd0] at hnd
    simpa [x, val_polyUnit] using hnd
  rw [mul_one] at hcross
  constructor
  · change (x.1.denom.natDegree : ℤ) - (x.1.num.natDegree : ℤ) = -(f.natDegree : ℤ)
    have hdeg := congrArg Polynomial.natDegree hcross
    rw [Polynomial.natDegree_mul hf h2] at hdeg
    omega
  · change x.1.num.leadingCoeff / x.1.denom.leadingCoeff = f.leadingCoeff
    have hlc := congrArg Polynomial.leadingCoeff hcross
    rw [Polynomial.leadingCoeff_mul] at hlc
    rw [hlc, mul_div_cancel_right₀ _ (Polynomial.leadingCoeff_ne_zero.mpr h2)]

/-- Monic irreducible polynomial over `E`. -/
structure MonicIrred (E : Type*) [Field E] where
  poly : Polynomial E
  monic : poly.Monic
  irred : Irreducible poly

theorem MonicIrred.ne_zero (π : MonicIrred E) : π.poly ≠ 0 := π.irred.ne_zero

theorem MonicIrred.natDegree_pos (π : MonicIrred E) : 0 < π.poly.natDegree := by
  by_contra h
  have h0 : π.poly.natDegree = 0 := by omega
  have h1 : π.poly = 1 := Polynomial.eq_one_of_monic_natDegree_zero π.monic h0
  exact π.irred.not_isUnit (h1 ▸ isUnit_one)

theorem MonicIrred.prime (π : MonicIrred E) : Prime π.poly :=
  UniqueFactorizationMonoid.irreducible_iff_prime.mp π.irred

/-- Order of vanishing and stripped polynomial at a monic irreducible `π`. -/
theorem exists_ord_strip (π : MonicIrred E) (f : Polynomial E) (hf : f ≠ 0) :
    ∃ (k : ℕ) (r : Polynomial E), f = π.poly ^ k * r ∧ ¬ π.poly ∣ r := by
  induction hn : f.natDegree using Nat.strong_induction_on generalizing f with
  | h n ih =>
    by_cases hdvd : π.poly ∣ f
    · obtain ⟨g, rfl⟩ := hdvd
      have hg : g ≠ 0 := right_ne_zero_of_mul hf
      have hdeg : g.natDegree < n := by
        rw [← hn, Polynomial.natDegree_mul π.ne_zero hg]
        have := π.natDegree_pos
        omega
      obtain ⟨k, r, hr, hndvd⟩ := ih g.natDegree hdeg g hg rfl
      refine ⟨k + 1, r, ?_, hndvd⟩
      rw [pow_succ', mul_assoc, ← hr]
    · exact ⟨0, f, by simp, hdvd⟩

noncomputable def ordPi (π : MonicIrred E) (f : Polynomial E) : ℕ :=
  open Classical in
  if hf : f ≠ 0 then (exists_ord_strip π f hf).choose else 0

noncomputable def stripPi (π : MonicIrred E) (f : Polynomial E) : Polynomial E :=
  open Classical in
  if hf : f ≠ 0 then (exists_ord_strip π f hf).choose_spec.choose else 0

theorem eq_pow_mul_stripPi (π : MonicIrred E) {f : Polynomial E} (hf : f ≠ 0) :
    f = π.poly ^ ordPi π f * stripPi π f := by
  classical
  simp only [ordPi, stripPi, dif_pos hf]
  exact (exists_ord_strip π f hf).choose_spec.choose_spec.1

theorem not_dvd_stripPi (π : MonicIrred E) {f : Polynomial E} (hf : f ≠ 0) :
    ¬ π.poly ∣ stripPi π f := by
  classical
  simp only [stripPi, dif_pos hf]
  exact (exists_ord_strip π f hf).choose_spec.choose_spec.2

theorem stripPi_ne_zero (π : MonicIrred E) {f : Polynomial E} (hf : f ≠ 0) :
    stripPi π f ≠ 0 := by
  intro h
  exact not_dvd_stripPi π hf (h ▸ dvd_zero _)

theorem ordPi_stripPi_unique (π : MonicIrred E) {f : Polynomial E} (hf : f ≠ 0)
    {k : ℕ} {r : Polynomial E} (hfr : f = π.poly ^ k * r) (hr : ¬ π.poly ∣ r) :
    ordPi π f = k ∧ stripPi π f = r := by
  have h1 := eq_pow_mul_stripPi π hf
  have h2 := not_dvd_stripPi π hf
  have heq : π.poly ^ ordPi π f * stripPi π f = π.poly ^ k * r := h1.symm.trans hfr
  have hk : ordPi π f = k := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_lt hlt
      have heq' : π.poly ^ ordPi π f * stripPi π f =
          π.poly ^ ordPi π f * (π.poly ^ (m + 1) * r) := by
        rw [heq, hm, add_assoc, pow_add, mul_assoc]
      have hc := mul_left_cancel₀ (pow_ne_zero (ordPi π f) π.ne_zero) heq'
      exact h2 ⟨π.poly ^ m * r, by rw [hc, pow_succ']; ring⟩
    · obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_lt hgt
      have heq' : π.poly ^ k * (π.poly ^ (m + 1) * stripPi π f) = π.poly ^ k * r := by
        rw [← mul_assoc, ← pow_add, ← add_assoc, ← hm, heq]
      have hc := mul_left_cancel₀ (pow_ne_zero k π.ne_zero) heq'
      exact hr ⟨π.poly ^ m * stripPi π f, by rw [← hc, pow_succ']; ring⟩
  refine ⟨hk, ?_⟩
  rw [hk] at heq
  exact mul_left_cancel₀ (pow_ne_zero k π.ne_zero) heq

theorem ordPi_mul_stripPi_mul (π : MonicIrred E) {f g : Polynomial E} (hf : f ≠ 0) (hg : g ≠ 0) :
    ordPi π (f * g) = ordPi π f + ordPi π g ∧ stripPi π (f * g) = stripPi π f * stripPi π g := by
  refine ordPi_stripPi_unique π (mul_ne_zero hf hg) ?_ ?_
  · rw [pow_add, mul_mul_mul_comm, ← eq_pow_mul_stripPi π hf, ← eq_pow_mul_stripPi π hg]
  · intro h
    rcases π.prime.dvd_or_dvd h with h1 | h2
    · exact not_dvd_stripPi π hf h1
    · exact not_dvd_stripPi π hg h2

theorem ordPi_stripPi_of_not_dvd (π : MonicIrred E) {f : Polynomial E} (hf : f ≠ 0)
    (hd : ¬ π.poly ∣ f) : ordPi π f = 0 ∧ stripPi π f = f :=
  ordPi_stripPi_unique π hf (by simp) hd

theorem ordPi_stripPi_self (π : MonicIrred E) :
    ordPi π π.poly = 1 ∧ stripPi π π.poly = 1 :=
  ordPi_stripPi_unique π π.ne_zero (by simp) (fun h => π.irred.not_isUnit (isUnit_of_dvd_one h))

/-- The discrete valuation on `RatFunc E` at a monic irreducible `π`, with residue field `AdjoinRoot π.poly`. -/
noncomputable def valPiData (π : MonicIrred E) :
    letI : Fact (Irreducible π.poly) := ⟨π.irred⟩
    DiscreteValData (RatFunc E) (AdjoinRoot π.poly) := by
  letI : Fact (Irreducible π.poly) := ⟨π.irred⟩
  have hinj := IsFractionRing.injective (Polynomial E) (RatFunc E)
  have hmk_ne : ∀ {r : Polynomial E}, ¬ π.poly ∣ r → AdjoinRoot.mk π.poly r ≠ 0 := by
    intro r hr h
    exact hr ((AdjoinRoot.mk_eq_zero).mp h)
  have hwd : ∀ (f₁ g₁ f₂ g₂ : Polynomial E) (hf₁ : f₁ ≠ 0) (hg₁ : g₁ ≠ 0)
      (hf₂ : f₂ ≠ 0) (hg₂ : g₂ ≠ 0),
      algebraMap (Polynomial E) (RatFunc E) f₁ / algebraMap _ _ g₁ =
      algebraMap (Polynomial E) (RatFunc E) f₂ / algebraMap _ _ g₂ →
      ((ordPi π f₁ : ℤ) - (ordPi π g₁ : ℤ) = (ordPi π f₂ : ℤ) - (ordPi π g₂ : ℤ)) ∧
      (AdjoinRoot.mk π.poly (stripPi π f₁) / AdjoinRoot.mk π.poly (stripPi π g₁) =
       AdjoinRoot.mk π.poly (stripPi π f₂) / AdjoinRoot.mk π.poly (stripPi π g₂)) := by
    intro f₁ g₁ f₂ g₂ hf₁ hg₁ hf₂ hg₂ h
    have hg₁' : algebraMap (Polynomial E) (RatFunc E) g₁ ≠ 0 := (map_ne_zero_iff _ hinj).mpr hg₁
    have hg₂' : algebraMap (Polynomial E) (RatFunc E) g₂ ≠ 0 := (map_ne_zero_iff _ hinj).mpr hg₂
    have hcross : f₁ * g₂ = f₂ * g₁ := by
      apply hinj
      rw [map_mul, map_mul]
      field_simp at h
      linear_combination h
    have h1 := ordPi_mul_stripPi_mul π hf₁ hg₂
    have h2 := ordPi_mul_stripPi_mul π hf₂ hg₁
    rw [hcross] at h1
    constructor
    · omega
    · have hst : stripPi π f₁ * stripPi π g₂ = stripPi π f₂ * stripPi π g₁ := h1.2.symm.trans h2.2
      have hmk := congrArg (AdjoinRoot.mk π.poly) hst
      rw [map_mul, map_mul] at hmk
      have hng₁ := hmk_ne (not_dvd_stripPi π hg₁)
      have hng₂ := hmk_ne (not_dvd_stripPi π hg₂)
      field_simp
      linear_combination hmk
  refine
    { val :=
        { toFun := fun a => (ordPi π a.toMul.1.num : ℤ) - (ordPi π a.toMul.1.denom : ℤ)
          map_zero' := by
            change (ordPi π (1 : RatFunc E).num : ℤ) - (ordPi π (1 : RatFunc E).denom : ℤ) = 0
            simp [RatFunc.num_one, RatFunc.denom_one]
          map_add' := fun a b => by
            set x := a.toMul
            set y := b.toMul
            have h1 := RatFunc.num_ne_zero x.ne_zero
            have h2 := RatFunc.denom_ne_zero x.1
            have h3 := RatFunc.num_ne_zero y.ne_zero
            have h4 := RatFunc.denom_ne_zero y.1
            have h5 := RatFunc.num_ne_zero (x * y).ne_zero
            have h6 := RatFunc.denom_ne_zero (x * y).1
            have heq : algebraMap (Polynomial E) (RatFunc E) (x * y).1.num /
                algebraMap _ _ (x * y).1.denom =
                algebraMap (Polynomial E) (RatFunc E) (x.1.num * y.1.num) /
                algebraMap _ _ (x.1.denom * y.1.denom) := by
              rw [RatFunc.num_div_denom, map_mul, map_mul, ← div_mul_div_comm,
                RatFunc.num_div_denom, RatFunc.num_div_denom]
              rfl
            have h := (hwd _ _ _ _ h5 h6 (mul_ne_zero h1 h3) (mul_ne_zero h2 h4) heq).1
            rw [(ordPi_mul_stripPi_mul π h1 h3).1, (ordPi_mul_stripPi_mul π h2 h4).1] at h
            change (ordPi π (x * y).1.num : ℤ) - (ordPi π (x * y).1.denom : ℤ) =
              ((ordPi π x.1.num : ℤ) - (ordPi π x.1.denom : ℤ)) +
              ((ordPi π y.1.num : ℤ) - (ordPi π y.1.denom : ℤ))
            omega }
      res :=
        { toFun := fun x =>
            Units.mk0
              (AdjoinRoot.mk π.poly (stripPi π x.1.num) /
                AdjoinRoot.mk π.poly (stripPi π x.1.denom))
              (div_ne_zero (hmk_ne (not_dvd_stripPi π (RatFunc.num_ne_zero x.ne_zero)))
                (hmk_ne (not_dvd_stripPi π (RatFunc.denom_ne_zero x.1))))
          map_one' := by
            apply Units.ext
            change AdjoinRoot.mk π.poly (stripPi π (1 : RatFunc E).num) /
              AdjoinRoot.mk π.poly (stripPi π (1 : RatFunc E).denom) = 1
            rw [RatFunc.num_one, RatFunc.denom_one,
              div_self (hmk_ne (not_dvd_stripPi π one_ne_zero))]
          map_mul' := fun x y => by
            apply Units.ext
            have h1 := RatFunc.num_ne_zero x.ne_zero
            have h2 := RatFunc.denom_ne_zero x.1
            have h3 := RatFunc.num_ne_zero y.ne_zero
            have h4 := RatFunc.denom_ne_zero y.1
            have h5 := RatFunc.num_ne_zero (x * y).ne_zero
            have h6 := RatFunc.denom_ne_zero (x * y).1
            have heq : algebraMap (Polynomial E) (RatFunc E) (x * y).1.num /
                algebraMap _ _ (x * y).1.denom =
                algebraMap (Polynomial E) (RatFunc E) (x.1.num * y.1.num) /
                algebraMap _ _ (x.1.denom * y.1.denom) := by
              rw [RatFunc.num_div_denom, map_mul, map_mul, ← div_mul_div_comm,
                RatFunc.num_div_denom, RatFunc.num_div_denom]
              rfl
            have h := (hwd _ _ _ _ h5 h6 (mul_ne_zero h1 h3) (mul_ne_zero h2 h4) heq).2
            rw [(ordPi_mul_stripPi_mul π h1 h3).2, (ordPi_mul_stripPi_mul π h2 h4).2,
              map_mul, map_mul, ← div_mul_div_comm] at h
            exact h }
      steinberg_pos := ?_
      steinberg_zero_pos := ?_
      steinberg_zero_zero := ?_
      steinberg_neg := ?_ }
  all_goals
    intro a b hab
    set f := a.1.num
    set g := a.1.denom
    have hf : f ≠ 0 := RatFunc.num_ne_zero a.ne_zero
    have hg : g ≠ 0 := RatFunc.denom_ne_zero a.1
    have hgf : g - f ≠ 0 := by
      intro h
      have ha1 : (a : RatFunc E) = 1 := by
        rw [← RatFunc.num_div_denom a.1, show a.1.num = a.1.denom by linear_combination -h,
          div_self ((map_ne_zero_iff _ hinj).mpr hg)]
      have : (b : RatFunc E) = 0 := by linear_combination hab - ha1
      exact b.ne_zero this
    have hb_eq : algebraMap (Polynomial E) (RatFunc E) b.1.num /
        algebraMap _ _ b.1.denom =
        algebraMap (Polynomial E) (RatFunc E) (g - f) / algebraMap _ _ g := by
      rw [RatFunc.num_div_denom, map_sub, sub_div, div_self ((map_ne_zero_iff _ hinj).mpr hg),
        RatFunc.num_div_denom]
      linear_combination hab
    have hw := hwd _ _ _ _ (RatFunc.num_ne_zero b.ne_zero) (RatFunc.denom_ne_zero b.1)
      hgf hg hb_eq
  · intro hpos
    change (0 : ℤ) < (ordPi π f : ℤ) - (ordPi π g : ℤ) at hpos
    have hlt : ordPi π g < ordPi π f := by omega
    obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_lt hlt
    have hfac : g - f = π.poly ^ ordPi π g *
        (stripPi π g - π.poly ^ (m + 1) * stripPi π f) := by
      conv_lhs => rw [eq_pow_mul_stripPi π hf, eq_pow_mul_stripPi π hg, hm, add_assoc, pow_add]
      ring
    have hnd : ¬ π.poly ∣ (stripPi π g - π.poly ^ (m + 1) * stripPi π f) := by
      intro hd
      have h1 : π.poly ∣ π.poly ^ (m + 1) * stripPi π f := by
        rw [pow_succ', mul_assoc]; exact dvd_mul_right _ _
      exact not_dvd_stripPi π hg ((dvd_sub_left h1).mp hd)
    obtain ⟨hord, hstr⟩ := ordPi_stripPi_unique π hgf hfac hnd
    constructor
    · change (ordPi π b.1.num : ℤ) - (ordPi π b.1.denom : ℤ) = 0
      omega
    · apply Units.ext
      change AdjoinRoot.mk π.poly (stripPi π b.1.num) /
        AdjoinRoot.mk π.poly (stripPi π b.1.denom) = 1
      rw [hw.2, hstr, map_sub, map_mul, map_pow, AdjoinRoot.mk_self,
        zero_pow (Nat.succ_ne_zero m), zero_mul, sub_zero, div_self (hmk_ne (not_dvd_stripPi π hg))]
  · intro hz hbpos
    change (ordPi π f : ℤ) - (ordPi π g : ℤ) = 0 at hz
    have heq_ord : ordPi π f = ordPi π g := by omega
    have hlt : ordPi π g < ordPi π (g - f) := by
      change (ordPi π b.1.num : ℤ) - (ordPi π b.1.denom : ℤ) > 0 at hbpos
      omega
    have hfac : g - f = π.poly ^ ordPi π g * (stripPi π g - stripPi π f) := by
      conv_lhs => rw [eq_pow_mul_stripPi π hf, eq_pow_mul_stripPi π hg, heq_ord]
      ring
    have hdvd : π.poly ∣ stripPi π g - stripPi π f := by
      conv_lhs at hfac => rw [eq_pow_mul_stripPi π hgf]
      obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_lt hlt
      have hfac' : π.poly ^ ordPi π g * (π.poly ^ (m + 1) * stripPi π (g - f)) =
          π.poly ^ ordPi π g * (stripPi π g - stripPi π f) := by
        rw [← mul_assoc, ← pow_add, ← add_assoc, ← hm, hfac]
      have hc := mul_left_cancel₀ (pow_ne_zero (ordPi π g) π.ne_zero) hfac'
      exact ⟨π.poly ^ m * stripPi π (g - f), by rw [← hc, pow_succ']; ring⟩
    have hmk_eq : AdjoinRoot.mk π.poly (stripPi π f) = AdjoinRoot.mk π.poly (stripPi π g) := by
      have h0 : AdjoinRoot.mk π.poly (stripPi π g - stripPi π f) = 0 :=
        AdjoinRoot.mk_eq_zero.mpr hdvd
      rw [map_sub] at h0
      exact (sub_eq_zero.mp h0).symm
    apply Units.ext
    change AdjoinRoot.mk π.poly (stripPi π f) / AdjoinRoot.mk π.poly (stripPi π g) = 1
    rw [hmk_eq, div_self (hmk_ne (not_dvd_stripPi π hg))]
  · intro hz hbz
    change (ordPi π f : ℤ) - (ordPi π g : ℤ) = 0 at hz
    have heq_ord : ordPi π f = ordPi π g := by omega
    have heq_sub : ordPi π (g - f) = ordPi π g := by
      change (ordPi π b.1.num : ℤ) - (ordPi π b.1.denom : ℤ) = 0 at hbz
      omega
    have hfac : g - f = π.poly ^ ordPi π g * (stripPi π g - stripPi π f) := by
      conv_lhs => rw [eq_pow_mul_stripPi π hf, eq_pow_mul_stripPi π hg, heq_ord]
      ring
    have hstr : stripPi π (g - f) = stripPi π g - stripPi π f := by
      conv_lhs at hfac => rw [eq_pow_mul_stripPi π hgf, heq_sub]
      exact mul_left_cancel₀ (pow_ne_zero (ordPi π g) π.ne_zero) hfac
    change AdjoinRoot.mk π.poly (stripPi π f) / AdjoinRoot.mk π.poly (stripPi π g) +
      AdjoinRoot.mk π.poly (stripPi π b.1.num) / AdjoinRoot.mk π.poly (stripPi π b.1.denom) = 1
    rw [hw.2, hstr, map_sub]
    have hng := hmk_ne (not_dvd_stripPi π hg)
    field_simp
    ring
  · intro hneg
    change (ordPi π f : ℤ) - (ordPi π g : ℤ) < 0 at hneg
    have hlt : ordPi π f < ordPi π g := by omega
    obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_lt hlt
    have hfac : g - f = π.poly ^ ordPi π f *
        (π.poly ^ (m + 1) * stripPi π g - stripPi π f) := by
      conv_lhs => rw [eq_pow_mul_stripPi π hf, eq_pow_mul_stripPi π hg, hm, add_assoc, pow_add]
      ring
    have hnd : ¬ π.poly ∣ (π.poly ^ (m + 1) * stripPi π g - stripPi π f) := by
      intro hd
      have h1 : π.poly ∣ π.poly ^ (m + 1) * stripPi π g := by
        rw [pow_succ', mul_assoc]; exact dvd_mul_right _ _
      exact not_dvd_stripPi π hf ((dvd_sub_right h1).mp hd)
    obtain ⟨hord, hstr⟩ := ordPi_stripPi_unique π hgf hfac hnd
    constructor
    · change (ordPi π b.1.num : ℤ) - (ordPi π b.1.denom : ℤ) =
        (ordPi π f : ℤ) - (ordPi π g : ℤ)
      omega
    · apply Units.ext
      change AdjoinRoot.mk π.poly (stripPi π b.1.num) /
        AdjoinRoot.mk π.poly (stripPi π b.1.denom) =
        -(AdjoinRoot.mk π.poly (stripPi π f) / AdjoinRoot.mk π.poly (stripPi π g))
      rw [hw.2, hstr, map_sub, map_mul, map_pow, AdjoinRoot.mk_self,
        zero_pow (Nat.succ_ne_zero m), zero_mul, zero_sub, neg_div]

theorem valPiData_polyUnit (π : MonicIrred E) (f : Polynomial E) (hf : f ≠ 0) :
    letI : Fact (Irreducible π.poly) := ⟨π.irred⟩
    (valPiData π).val (Additive.ofMul (polyUnit f hf)) = (ordPi π f : ℤ) ∧
    ((valPiData π).res (polyUnit f hf) : AdjoinRoot π.poly) =
      AdjoinRoot.mk π.poly (stripPi π f) := by
  letI : Fact (Irreducible π.poly) := ⟨π.irred⟩
  have hinj := IsFractionRing.injective (Polynomial E) (RatFunc E)
  set x := polyUnit f hf
  have h1 := RatFunc.num_ne_zero x.ne_zero
  have h2 := RatFunc.denom_ne_zero x.1
  have hcross : x.1.num = f * x.1.denom := by
    apply hinj
    rw [map_mul]
    have hnd := RatFunc.num_div_denom x.1
    have hd0 : algebraMap (Polynomial E) (RatFunc E) x.1.denom ≠ 0 :=
      (map_ne_zero_iff _ hinj).mpr h2
    rw [div_eq_iff hd0] at hnd
    simpa [x, val_polyUnit] using hnd
  have hm := ordPi_mul_stripPi_mul π hf h2
  rw [← hcross] at hm
  constructor
  · change (ordPi π x.1.num : ℤ) - (ordPi π x.1.denom : ℤ) = (ordPi π f : ℤ)
    omega
  · change AdjoinRoot.mk π.poly (stripPi π x.1.num) /
      AdjoinRoot.mk π.poly (stripPi π x.1.denom) = AdjoinRoot.mk π.poly (stripPi π f)
    rw [hm.2, map_mul]
    have hnd : AdjoinRoot.mk π.poly (stripPi π x.1.denom) ≠ 0 := by
      intro h
      exact not_dvd_stripPi π h2 (AdjoinRoot.mk_eq_zero.mp h)
    exact mul_div_cancel_right₀ _ hnd

theorem valPiData_polyUnit_not_dvd (π : MonicIrred E) (f : Polynomial E) (hf : f ≠ 0)
    (hd : ¬ π.poly ∣ f) :
    letI : Fact (Irreducible π.poly) := ⟨π.irred⟩
    (valPiData π).val (Additive.ofMul (polyUnit f hf)) = 0 ∧
    ((valPiData π).res (polyUnit f hf) : AdjoinRoot π.poly) = AdjoinRoot.mk π.poly f := by
  letI : Fact (Irreducible π.poly) := ⟨π.irred⟩
  obtain ⟨h1, h2⟩ := valPiData_polyUnit π f hf
  obtain ⟨h3, h4⟩ := ordPi_stripPi_of_not_dvd π hf hd
  rw [h3] at h1
  rw [h4] at h2
  exact ⟨by simpa using h1, h2⟩

theorem valPiData_self (π : MonicIrred E) :
    letI : Fact (Irreducible π.poly) := ⟨π.irred⟩
    (valPiData π).val (Additive.ofMul (polyUnit π.poly π.ne_zero)) = 1 ∧
    (valPiData π).res (polyUnit π.poly π.ne_zero) = 1 := by
  letI : Fact (Irreducible π.poly) := ⟨π.irred⟩
  obtain ⟨h1, h2⟩ := valPiData_polyUnit π π.poly π.ne_zero
  obtain ⟨h3, h4⟩ := ordPi_stripPi_self π
  rw [h3] at h1
  rw [h4] at h2
  refine ⟨by simpa using h1, Units.ext ?_⟩
  simpa using h2

theorem MonicIrred.not_dvd_of_ne {π₁ π₂ : MonicIrred E} (hne : π₁ ≠ π₂) :
    ¬ π₁.poly ∣ π₂.poly := by
  intro hd
  rcases π₂.irred.dvd_iff.mp hd with hu | hass
  · exact π₁.irred.not_isUnit hu
  · have heq : π₁.poly = π₂.poly := Polynomial.eq_of_monic_of_associated π₁.monic π₂.monic hass.symm
    apply hne
    cases π₁; cases π₂; simp_all

end RatFuncValuations

section DegreeTwoAndWeil

variable {E : Type*} [Field E]

/-- Helper: `ZMod p`-module structure on any `AddCommGroup` killed by `p`. -/
def zmodModule {M : Type*} [AddCommGroup M] {p : ℕ} (hp : 0 < p) (hM : ∀ x : M, p • x = 0) :
    Module (ZMod p) M :=
  haveI : NeZero p := ⟨hp.ne'⟩
  have hmod : ∀ (n : ℕ) (x : M), (n % p) • x = n • x := by
    intro n x
    have hdiv := Nat.div_add_mod n p
    calc (n % p) • x = (p * (n / p)) • x + (n % p) • x := by
            rw [mul_comm, mul_nsmul, hM, zero_add]
      _ = (p * (n / p) + n % p) • x := (add_nsmul _ _ _).symm
      _ = n • x := by rw [hdiv]
  { smul := fun z x => z.val • x
    one_smul := fun x => by
      change (1 : ZMod p).val • x = x
      by_cases hp1 : p = 1
      · subst hp1
        have hx0 : x = 0 := by simpa using hM x
        rw [hx0, smul_zero]
      · haveI : Fact (1 < p) := ⟨by omega⟩
        rw [ZMod.val_one, one_smul]
    mul_smul := fun a b x => by
      change (a * b).val • x = a.val • (b.val • x)
      rw [ZMod.val_mul, hmod, mul_comm, mul_nsmul]
    smul_zero := fun a => by change a.val • (0 : M) = 0; exact smul_zero _
    smul_add := fun a x y => by change a.val • (x + y) = a.val • x + a.val • y; exact smul_add _ _ _
    add_smul := fun a b x => by
      change (a + b).val • x = a.val • x + b.val • x
      rw [ZMod.val_add, hmod, add_nsmul]
    zero_smul := fun x => by
      change (0 : ZMod p).val • x = 0
      simp }

/-- Simple square-zero extension `ZMod p × G` for lifting degree-1 additive homomorphisms. -/
structure DualMod (p : ℕ) (G : Type*) where
  fst : ZMod p
  snd : G

namespace DualMod

variable {p : ℕ} {G : Type*}

theorem ext {x y : DualMod p G} (h1 : x.fst = y.fst) (h2 : x.snd = y.snd) : x = y := by
  cases x; cases y; simp_all

instance [Zero G] : Zero (DualMod p G) := ⟨⟨0, 0⟩⟩
instance [Zero G] : One (DualMod p G) := ⟨⟨1, 0⟩⟩
instance [Add G] : Add (DualMod p G) := ⟨fun x y => ⟨x.fst + y.fst, x.snd + y.snd⟩⟩
instance [Neg G] : Neg (DualMod p G) := ⟨fun x => ⟨-x.fst, -x.snd⟩⟩
instance [Sub G] : Sub (DualMod p G) := ⟨fun x y => ⟨x.fst - y.fst, x.snd - y.snd⟩⟩
instance [Zero G] : NatCast (DualMod p G) := ⟨fun n => ⟨n, 0⟩⟩
instance [Zero G] : IntCast (DualMod p G) := ⟨fun n => ⟨n, 0⟩⟩

instance [AddCommGroup G] [Module (ZMod p) G] : Mul (DualMod p G) :=
  ⟨fun x y => ⟨x.fst * y.fst, x.fst • y.snd + y.fst • x.snd⟩⟩

instance [AddCommGroup G] [Module (ZMod p) G] : Ring (DualMod p G) where
  add_assoc a b c := by apply DualMod.ext <;> exact add_assoc _ _ _
  zero_add a := by apply DualMod.ext <;> exact zero_add _
  add_zero a := by apply DualMod.ext <;> exact add_zero _
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel a := by apply DualMod.ext <;> exact neg_add_cancel _
  add_comm a b := by apply DualMod.ext <;> exact add_comm _ _
  sub_eq_add_neg a b := by apply DualMod.ext <;> exact sub_eq_add_neg _ _
  mul_assoc a b c := by
    apply DualMod.ext
    · exact mul_assoc _ _ _
    · change (a.fst * b.fst) • c.snd + c.fst • (a.fst • b.snd + b.fst • a.snd) =
        a.fst • (b.fst • c.snd + c.fst • b.snd) + (b.fst * c.fst) • a.snd
      rw [smul_add, smul_add, mul_smul, mul_smul, ← mul_smul c.fst a.fst, mul_comm c.fst a.fst,
        mul_smul, ← mul_smul c.fst b.fst, mul_comm c.fst b.fst, mul_smul]
      abel
  one_mul a := by
    apply DualMod.ext
    · exact one_mul _
    · change (1 : ZMod p) • a.snd + a.fst • (0 : G) = a.snd
      simp
  mul_one a := by
    apply DualMod.ext
    · exact mul_one _
    · change a.fst • (0 : G) + (1 : ZMod p) • a.snd = a.snd
      simp
  left_distrib a b c := by
    apply DualMod.ext
    · exact left_distrib _ _ _
    · change a.fst • (b.snd + c.snd) + (b.fst + c.fst) • a.snd =
        (a.fst • b.snd + b.fst • a.snd) + (a.fst • c.snd + c.fst • a.snd)
      simp only [smul_add, add_smul]; abel
  right_distrib a b c := by
    apply DualMod.ext
    · exact right_distrib _ _ _
    · change (a.fst + b.fst) • c.snd + c.fst • (a.snd + b.snd) =
        (a.fst • c.snd + c.fst • a.snd) + (b.fst • c.snd + c.fst • b.snd)
      simp only [smul_add, add_smul]; abel
  zero_mul a := by
    apply DualMod.ext
    · exact zero_mul _
    · change (0 : ZMod p) • a.snd + a.fst • (0 : G) = 0
      simp
  mul_zero a := by
    apply DualMod.ext
    · exact mul_zero _
    · change a.fst • (0 : G) + (0 : ZMod p) • a.snd = 0
      simp
  natCast_zero := by apply DualMod.ext; exact Nat.cast_zero; rfl
  natCast_succ n := by
    apply DualMod.ext
    · exact Nat.cast_succ n
    · exact (add_zero 0).symm
  intCast_ofNat n := by apply DualMod.ext; exact Int.cast_natCast n; rfl
  intCast_negSucc n := by
    apply DualMod.ext
    · exact Int.cast_negSucc n
    · exact neg_zero.symm

end DualMod

/-- Lift an additive homomorphism `Additive Fˣ →+ G` (with `p • G = 0`) to `MilnorK F p →+ G`
sending `of p u` to `φ u` and killing products of length ≥ 2. -/
noncomputable def liftDegOne {F G : Type*} [Field F] [AddCommGroup G] {p : ℕ} (hp : 0 < p)
    (hG : ∀ g : G, p • g = 0) (φ : Additive Fˣ →+ G) : MilnorK F p →+ G := by
  letI : Module (ZMod p) G := zmodModule hp hG
  let ψ : Additive Fˣ →+ DualMod p G :=
    { toFun := fun a => ⟨0, φ a⟩
      map_zero' := by apply DualMod.ext; rfl; exact map_zero φ
      map_add' := fun a b => by
        apply DualMod.ext
        · change (0 : ZMod p) = 0 + 0; simp
        · change φ (a + b) = φ a + φ b; exact map_add φ a b }
  let ringHom : MilnorK F p →+* DualMod p G :=
    RingQuot.lift ⟨(TensorAlgebra.lift ℤ ψ.toIntLinearMap).toRingHom, by
      intro x y h
      cases h with
      | steinberg a b _ =>
        simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_mul, map_zero,
          TensorAlgebra.lift_ι_apply, AddMonoidHom.coe_toIntLinearMap]
        apply DualMod.ext
        · change (0 : ZMod p) * 0 = 0; simp
        · change (0 : ZMod p) • _ + (0 : ZMod p) • _ = 0; simp
      | natCast =>
        rw [map_natCast, map_zero]
        apply DualMod.ext
        · change (p : ZMod p) = 0; simp
        · rfl⟩
  exact
    { toFun := fun x => (ringHom x).snd
      map_zero' := by simp; rfl
      map_add' := fun x y => by rw [map_add]; rfl }

@[simp]
theorem liftDegOne_of {F G : Type*} [Field F] [AddCommGroup G] {p : ℕ} (hp : 0 < p)
    (hG : ∀ g : G, p • g = 0) (φ : Additive Fˣ →+ G) (u : Fˣ) :
    liftDegOne hp hG φ (of p u) = φ (Additive.ofMul u) := by
  simp [liftDegOne, of, RingQuot.lift_mkRingHom_apply]

/-- Norm homomorphism `K_1^M(AdjoinRoot π.poly)/p → MilnorK E p` extended to `MilnorK`. -/
noncomputable def normK1 (π : MonicIrred E) {p : ℕ} (hp : p.Prime) :
    letI : Fact (Irreducible π.poly) := ⟨π.irred⟩
    MilnorK (AdjoinRoot π.poly) p →+ MilnorK E p :=
  letI : Fact (Irreducible π.poly) := ⟨π.irred⟩
  liftDegOne hp.pos (p_nsmul_eq_zero p)
    { toFun := fun u => of p (Units.map (Algebra.norm E : AdjoinRoot π.poly →* E) u.toMul)
      map_zero' := by simp
      map_add' := fun a b => by
        change of p (Units.map _ (a.toMul * b.toMul)) = _
        rw [map_mul, of_mul] }

@[simp]
theorem normK1_of (π : MonicIrred E) {p : ℕ} (hp : p.Prime)
    (u : letI : Fact (Irreducible π.poly) := ⟨π.irred⟩; (AdjoinRoot π.poly)ˣ) :
    letI : Fact (Irreducible π.poly) := ⟨π.irred⟩
    normK1 π hp (of p u) = of p (Units.map (Algebra.norm E : AdjoinRoot π.poly →* E) u) := by
  letI : Fact (Irreducible π.poly) := ⟨π.irred⟩
  simp [normK1]

/-- Finite support of `π ↦ partial_π x` for every `x : MilnorK (RatFunc E) p`. -/
theorem finite_support_partialPi {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (x : MilnorK (RatFunc E) p) :
    Set.Finite {π : MonicIrred E |
      (letI : Fact (Irreducible π.poly) := ⟨π.irred⟩; (valPiData π).partialHom hp hp2 x ≠ 0)} := by
  suffices h : ∀ y : TensorAlgebra ℤ (Additive (RatFunc E)ˣ),
      Set.Finite {π : MonicIrred E |
        (letI : Fact (Irreducible π.poly) := ⟨π.irred⟩
         (valPiData π).partialHom hp hp2 (RingQuot.mkRingHom (MilnorK.Rel (RatFunc E) p) y) ≠ 0)} by
    obtain ⟨y, rfl⟩ := RingQuot.mkRingHom_surjective (MilnorK.Rel (RatFunc E) p) x
    exact h y
  intro y
  induction y using TensorAlgebra.induction with
  | algebraMap r =>
    refine Set.Finite.subset Set.finite_empty ?_
    intro π hπ
    letI : Fact (Irreducible π.poly) := ⟨π.irred⟩
    exfalso
    apply hπ
    have hr : (algebraMap ℤ (TensorAlgebra ℤ (Additive (RatFunc E)ˣ))) r = (r : TensorAlgebra ℤ _) :=
      eq_intCast _ r
    rw [hr, map_intCast]
    change ((valPiData π).theta hp hp2 (r : MilnorK (RatFunc E) p)).snd = 0
    rw [map_intCast]
    cases r with
    | ofNat n => simp [Int.cast_natCast]
    | negSucc n => simp [Int.cast_negSucc]
  | ι a =>
    set u := a.toMul
    have hnum : u.1.num ≠ 0 := RatFunc.num_ne_zero u.ne_zero
    have hden : u.1.denom ≠ 0 := RatFunc.denom_ne_zero u.1
    have hfin_dvd : ∀ f : Polynomial E, f ≠ 0 →
        Set.Finite {π : MonicIrred E | π.poly ∣ f} := by
      intro f
      induction hn : f.natDegree using Nat.strong_induction_on generalizing f with
      | h n ih =>
        intro hf
        by_cases hex : ∃ π₀ : MonicIrred E, π₀.poly ∣ f
        · obtain ⟨π₀, g, rfl⟩ := hex
          have hg : g ≠ 0 := right_ne_zero_of_mul hf
          have hdeg : g.natDegree < n := by
            rw [← hn, Polynomial.natDegree_mul π₀.ne_zero hg]
            have := π₀.natDegree_pos
            omega
          refine ((Set.finite_singleton π₀).union (ih g.natDegree hdeg g rfl hg)).subset ?_
          intro π hπ
          rcases π.prime.dvd_or_dvd hπ with h1 | h2
          · left
            rcases π₀.irred.dvd_iff.mp h1 with hu | hass
            · exact absurd hu π.irred.not_isUnit
            · have heq := Polynomial.eq_of_monic_of_associated π.monic π₀.monic hass.symm
              cases π; cases π₀; simp_all
          · exact Or.inr h2
        · push Not at hex
          have hemp : {π : MonicIrred E | π.poly ∣ f} = ∅ := by
            ext π; simp [hex π]
          rw [hemp]
          exact Set.finite_empty
    refine ((hfin_dvd u.1.num hnum).union (hfin_dvd u.1.denom hden)).subset ?_
    intro π hπ
    letI : Fact (Irreducible π.poly) := ⟨π.irred⟩
    by_contra hnot
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or] at hnot
    apply hπ
    change ((valPiData π).theta hp hp2 (of p u)).snd = 0
    rw [DiscreteValData.theta_of]
    have h1 := (ordPi_stripPi_of_not_dvd π hnum hnot.1).1
    have h2 := (ordPi_stripPi_of_not_dvd π hden hnot.2).1
    change (((ordPi π u.1.num : ℤ) - (ordPi π u.1.denom : ℤ) : ℤ) : MilnorK (AdjoinRoot π.poly) p) = 0
    simp [h1, h2]
  | add a b iha ihb =>
    refine (iha.union ihb).subset ?_
    intro π hπ
    letI : Fact (Irreducible π.poly) := ⟨π.irred⟩
    by_contra hnot
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hnot
    apply hπ
    rw [map_add, map_add, hnot.1, hnot.2, add_zero]
  | mul a b iha ihb =>
    refine (iha.union ihb).subset ?_
    intro π hπ
    letI : Fact (Irreducible π.poly) := ⟨π.irred⟩
    by_contra hnot
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hnot
    apply hπ
    rw [map_mul]
    exact (valPiData π).partialHom_mul_of_val_zero hp hp2 _ _ hnot.1 hnot.2

/-- Resultant symmetry for norms of distinct monic irreducibles in characteristic zero. -/
theorem norm_mk_symm [CharZero E] (π₁ π₂ : MonicIrred E) :
    letI : Fact (Irreducible π₁.poly) := ⟨π₁.irred⟩
    letI : Fact (Irreducible π₂.poly) := ⟨π₂.irred⟩
    Algebra.norm E (AdjoinRoot.mk π₁.poly π₂.poly) =
      (-1 : E) ^ (π₁.poly.natDegree * π₂.poly.natDegree) *
        Algebra.norm E (AdjoinRoot.mk π₂.poly π₁.poly) := by
  classical
  letI : Fact (Irreducible π₁.poly) := ⟨π₁.irred⟩
  letI : Fact (Irreducible π₂.poly) := ⟨π₂.irred⟩
  set Ebar := AlgebraicClosure E
  set ι : E →+* Ebar := algebraMap E Ebar
  have hnorm_eq : ∀ (π q : MonicIrred E),
      letI : Fact (Irreducible π.poly) := ⟨π.irred⟩
      ι (Algebra.norm E (AdjoinRoot.mk π.poly q.poly)) =
        ((π.poly.map ι).roots.map (fun a => (q.poly.map ι).eval a)).prod := by
    intro π q
    letI : Fact (Irreducible π.poly) := ⟨π.irred⟩
    haveI : Module.Finite E (AdjoinRoot π.poly) :=
      PowerBasis.finite (AdjoinRoot.powerBasis π.ne_zero)
    have hsep : π.poly.Separable := π.irred.separable
    have hsep_map : (π.poly.map ι).Separable := hsep.map
    have hnodup : (π.poly.map ι).roots.Nodup := Polynomial.nodup_roots hsep_map
    have hnorm := Algebra.norm_eq_prod_embeddings E Ebar (AdjoinRoot.mk π.poly q.poly)
    rw [hnorm]
    have ha_ev : ∀ a : {a : Ebar // a ∈ (π.poly.map ι).roots.toFinset},
        Polynomial.eval₂ ι a.1 π.poly = 0 := fun a => by
      have ha := (Polynomial.mem_roots (Polynomial.map_ne_zero π.ne_zero)).mp
        (Multiset.mem_toFinset.mp a.2)
      rw [Polynomial.IsRoot.def, Polynomial.eval_map] at ha
      exact ha
    let invFunE : {a : Ebar // a ∈ (π.poly.map ι).roots.toFinset} → (AdjoinRoot π.poly →ₐ[E] Ebar) :=
      fun a =>
        { toRingHom := AdjoinRoot.lift ι a.1 (ha_ev a)
          commutes' := fun c => AdjoinRoot.lift_of _ }
    have hinv_root : ∀ a : {a : Ebar // a ∈ (π.poly.map ι).roots.toFinset},
        invFunE a (AdjoinRoot.root π.poly) = a.1 := fun a => by
      change AdjoinRoot.lift ι a.1 (ha_ev a) (AdjoinRoot.root π.poly) = a.1
      exact AdjoinRoot.lift_root (ha_ev a)
    let e : (AdjoinRoot π.poly →ₐ[E] Ebar) ≃ {a : Ebar // a ∈ (π.poly.map ι).roots.toFinset} :=
      { toFun := fun σ => ⟨σ (AdjoinRoot.root π.poly), by
          rw [Multiset.mem_toFinset, Polynomial.mem_roots (Polynomial.map_ne_zero π.ne_zero),
            Polynomial.IsRoot.def, Polynomial.eval_map]
          have hcomp : σ.toRingHom.comp (algebraMap E (AdjoinRoot π.poly)) = ι := by
            ext c; exact σ.commutes c
          have hev : Polynomial.eval₂ ι (σ (AdjoinRoot.root π.poly)) π.poly =
              σ.toRingHom (Polynomial.eval₂ (algebraMap E (AdjoinRoot π.poly)) (AdjoinRoot.root π.poly) π.poly) := by
            rw [← hcomp]
            exact (Polynomial.hom_eval₂ π.poly (algebraMap E (AdjoinRoot π.poly)) σ.toRingHom
              (AdjoinRoot.root π.poly)).symm
          rw [hev]
          change σ.toRingHom (Polynomial.eval₂ (AdjoinRoot.of π.poly) (AdjoinRoot.root π.poly) π.poly) = 0
          rw [AdjoinRoot.eval₂_root, map_zero]⟩
        invFun := invFunE
        left_inv := fun σ => by
          apply AdjoinRoot.algHom_ext
          exact hinv_root _
        right_inv := fun a => by
          ext
          exact hinv_root a }
    have hprod_fin : ∏ σ : AdjoinRoot π.poly →ₐ[E] Ebar, σ (AdjoinRoot.mk π.poly q.poly) =
        ∏ a : {a : Ebar // a ∈ (π.poly.map ι).roots.toFinset}, (q.poly.map ι).eval a.1 := by
      refine Fintype.prod_equiv e _ _ (fun σ => ?_)
      change σ.toRingHom (AdjoinRoot.mk π.poly q.poly) = (q.poly.map ι).eval (σ (AdjoinRoot.root π.poly))
      rw [Polynomial.eval_map]
      have hcomp : σ.toRingHom.comp (algebraMap E (AdjoinRoot π.poly)) = ι := by
        ext c; exact σ.commutes c
      have hev : Polynomial.eval₂ ι (σ (AdjoinRoot.root π.poly)) q.poly =
          σ.toRingHom (Polynomial.eval₂ (algebraMap E (AdjoinRoot π.poly)) (AdjoinRoot.root π.poly) q.poly) := by
        rw [← hcomp]
        exact (Polynomial.hom_eval₂ q.poly (algebraMap E (AdjoinRoot π.poly)) σ.toRingHom
          (AdjoinRoot.root π.poly)).symm
      rw [hev]
      congr 1
      change AdjoinRoot.mk π.poly q.poly = Polynomial.eval₂ (AdjoinRoot.of π.poly) (AdjoinRoot.root π.poly) q.poly
      rw [← AdjoinRoot.aeval_eq, Polynomial.aeval_def]
      rfl
    rw [hprod_fin]
    have hfinset : (π.poly.map ι).roots.toFinset.val = (π.poly.map ι).roots :=
      Multiset.dedup_eq_self.mpr hnodup
    rw [Finset.prod_coe_sort ((π.poly.map ι).roots.toFinset) (fun a => (q.poly.map ι).eval a),
      Finset.prod_eq_multiset_prod, hfinset]
  have hsplits : ∀ (π : MonicIrred E),
      π.poly.map ι = ((π.poly.map ι).roots.map (fun a => X - C a)).prod ∧
      (π.poly.map ι).roots.card = π.poly.natDegree := by
    intro π
    have hmon : (π.poly.map ι).Monic := π.monic.map ι
    have hsp : (π.poly.map ι).Splits := IsAlgClosed.splits _
    refine ⟨hsp.eq_prod_roots_of_monic hmon, ?_⟩
    rw [← hsp.natDegree_eq_card_roots, Polynomial.natDegree_map_eq_of_injective ι.injective]
  obtain ⟨hsp1, hcard1⟩ := hsplits π₁
  obtain ⟨hsp2, hcard2⟩ := hsplits π₂
  have hnd1 : (π₁.poly.map ι).roots.Nodup := Polynomial.nodup_roots π₁.irred.separable.map
  have hnd2 : (π₂.poly.map ι).roots.Nodup := Polynomial.nodup_roots π₂.irred.separable.map
  set S1 := (π₁.poly.map ι).roots.toFinset
  set S2 := (π₂.poly.map ι).roots.toFinset
  have hS1 : S1.val = (π₁.poly.map ι).roots := Multiset.dedup_eq_self.mpr hnd1
  have hS2 : S2.val = (π₂.poly.map ι).roots := Multiset.dedup_eq_self.mpr hnd2
  have heval2 : ∀ a : Ebar, (π₂.poly.map ι).eval a = ∏ b ∈ S2, (a - b) := by
    intro a
    rw [hsp2, Polynomial.eval_multiset_prod, Multiset.map_map]
    simp only [Function.comp_def, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    rw [← hS2, ← Finset.prod_eq_multiset_prod]
  have heval1 : ∀ b : Ebar, (π₁.poly.map ι).eval b = ∏ a ∈ S1, (b - a) := by
    intro b
    rw [hsp1, Polynomial.eval_multiset_prod, Multiset.map_map]
    simp only [Function.comp_def, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    rw [← hS1, ← Finset.prod_eq_multiset_prod]
  apply ι.injective
  rw [map_mul, map_pow, map_neg, map_one, hnorm_eq π₁ π₂, hnorm_eq π₂ π₁]
  rw [← hS1, ← Finset.prod_eq_multiset_prod, ← hS2, ← Finset.prod_eq_multiset_prod]
  simp_rw [heval2, heval1]
  calc ∏ a ∈ S1, ∏ b ∈ S2, (a - b)
      = ∏ a ∈ S1, ∏ b ∈ S2, ((-1 : Ebar) * (b - a)) := by
          refine Finset.prod_congr rfl fun a _ => Finset.prod_congr rfl fun b _ => by ring
    _ = (∏ a ∈ S1, ∏ b ∈ S2, (-1 : Ebar)) * (∏ a ∈ S1, ∏ b ∈ S2, (b - a)) := by
          simp_rw [Finset.prod_mul_distrib]
    _ = (-1 : Ebar) ^ (π₁.poly.natDegree * π₂.poly.natDegree) *
          (∏ b ∈ S2, ∏ a ∈ S1, (b - a)) := by
          congr 1
          · simp only [Finset.prod_const, ← pow_mul]
            have hc1 : S1.card = π₁.poly.natDegree := by
              rw [← hcard1, ← hS1]; rfl
            have hc2 : S2.card = π₂.poly.natDegree := by
              rw [← hcard2, ← hS2]; rfl
            rw [hc1, hc2, mul_comm]
          · exact Finset.prod_comm

/-- Weil reciprocity sum on `MilnorK (RatFunc E) p`:
`∑_π normK1 π (∂_π x) + ∂_∞ x`. -/
noncomputable def weilSum {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    MilnorK (RatFunc E) p →+ MilnorK E p where
  toFun x :=
    (∑ᶠ π : MonicIrred E,
      (letI : Fact (Irreducible π.poly) := ⟨π.irred⟩
       normK1 π hp ((valPiData π).partialHom hp hp2 x))) +
    (valInftyData E).partialHom hp hp2 x
  map_zero' := by simp
  map_add' x y := by
    have hx : (Function.support fun π : MonicIrred E =>
        letI : Fact (Irreducible π.poly) := ⟨π.irred⟩
        normK1 π hp ((valPiData π).partialHom hp hp2 x)).Finite := by
      refine (finite_support_partialPi hp hp2 x).subset ?_
      intro π hπ h0
      letI : Fact (Irreducible π.poly) := ⟨π.irred⟩
      exact hπ (by simp [h0])
    have hy : (Function.support fun π : MonicIrred E =>
        letI : Fact (Irreducible π.poly) := ⟨π.irred⟩
        normK1 π hp ((valPiData π).partialHom hp hp2 y)).Finite := by
      refine (finite_support_partialPi hp hp2 y).subset ?_
      intro π hπ h0
      letI : Fact (Irreducible π.poly) := ⟨π.irred⟩
      exact hπ (by simp [h0])
    have hadd : (fun π : MonicIrred E =>
        letI : Fact (Irreducible π.poly) := ⟨π.irred⟩
        normK1 π hp ((valPiData π).partialHom hp hp2 (x + y))) =
      (fun π : MonicIrred E =>
        (letI : Fact (Irreducible π.poly) := ⟨π.irred⟩
         normK1 π hp ((valPiData π).partialHom hp hp2 x)) +
        (letI : Fact (Irreducible π.poly) := ⟨π.irred⟩
         normK1 π hp ((valPiData π).partialHom hp hp2 y))) := by
      ext π
      letI : Fact (Irreducible π.poly) := ⟨π.irred⟩
      simp [map_add]
    rw [hadd, finsum_add_distrib hx hy, map_add]
    abel

theorem exists_mul_of_not_irreducible {R : Type*} [Monoid R] {g : R}
    (hnu : ¬ IsUnit g) (hnirr : ¬ Irreducible g) :
    ∃ a b : R, g = a * b ∧ ¬ IsUnit a ∧ ¬ IsUnit b := by
  by_contra h
  apply hnirr
  refine ⟨hnu, fun a b hab => ?_⟩
  by_contra hor
  exact h ⟨a, b, hab, fun ha => hor (Or.inl ha), fun hb => hor (Or.inr hb)⟩

/-- Every unit in `RatFunc E` belongs to the subgroup generated by constants `C c` and
monic irreducibles `π`. -/
theorem ratFunc_units_gen (H : Subgroup (RatFunc E)ˣ)
    (hC : ∀ (c : E) (hc : c ≠ 0), polyUnit (C c) (C_ne_zero.mpr hc) ∈ H)
    (hIrred : ∀ π : MonicIrred E, polyUnit π.poly π.ne_zero ∈ H)
    (u : (RatFunc E)ˣ) : u ∈ H := by
  have hpoly : ∀ (f : Polynomial E) (hf : f ≠ 0), polyUnit f hf ∈ H := by
    intro f
    induction hn : f.natDegree using Nat.strong_induction_on generalizing f with
    | h n ih =>
      intro hf
      by_cases hd0 : f.natDegree = 0
      · have hfc : f = C (f.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hd0
        have hc0 : f.coeff 0 ≠ 0 := by intro h; apply hf; rw [hfc, h, map_zero]
        have heq : polyUnit f hf = polyUnit (C (f.coeff 0)) (C_ne_zero.mpr hc0) := by
          apply Units.ext
          change algebraMap (Polynomial E) (RatFunc E) f = algebraMap _ _ (C (f.coeff 0))
          exact congrArg (algebraMap (Polynomial E) (RatFunc E)) hfc
        rw [heq]
        exact hC _ hc0
      · have hlc : f.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hf
        set g := f * C f.leadingCoeff⁻¹
        have hg_monic : g.Monic := Polynomial.monic_mul_leadingCoeff_inv hf
        have hg_ne : g ≠ 0 := hg_monic.ne_zero
        have hfg : f = C f.leadingCoeff * g := by
          simp only [g]
          rw [mul_left_comm, ← map_mul, mul_inv_cancel₀ hlc, map_one, mul_one]
        have hunit_eq : polyUnit f hf = polyUnit (C f.leadingCoeff) (C_ne_zero.mpr hlc) *
            polyUnit g hg_ne := by
          apply Units.ext
          change algebraMap (Polynomial E) (RatFunc E) f =
            algebraMap _ _ (C f.leadingCoeff) * algebraMap _ _ g
          rw [← map_mul]
          exact congrArg _ hfg
        rw [hunit_eq]
        refine H.mul_mem (hC _ hlc) ?_
        by_cases hirr : Irreducible g
        · exact hIrred ⟨g, hg_monic, hirr⟩
        · have hdg : g.natDegree = f.natDegree := by
            rw [show g = C f.leadingCoeff⁻¹ * f from mul_comm _ _,
              Polynomial.natDegree_C_mul (inv_ne_zero hlc)]
          have hnotu : ¬ IsUnit g := by
            intro hu
            have := Polynomial.natDegree_eq_zero_of_isUnit hu
            omega
          obtain ⟨a, b, hab, ha_nu, hb_nu⟩ := exists_mul_of_not_irreducible hnotu hirr
          have ha0 : a ≠ 0 := left_ne_zero_of_mul (hab ▸ hg_ne)
          have hb0 : b ≠ 0 := right_ne_zero_of_mul (hab ▸ hg_ne)
          have ha_pos : 0 < a.natDegree := by
            by_contra h
            have h0 : a.natDegree = 0 := by omega
            have := Polynomial.eq_C_of_natDegree_eq_zero h0
            apply ha_nu
            rw [this]
            exact Polynomial.isUnit_C.mpr (IsUnit.mk0 _ (by intro hc; apply ha0; rw [this, hc, map_zero]))
          have hb_pos : 0 < b.natDegree := by
            by_contra h
            have h0 : b.natDegree = 0 := by omega
            have := Polynomial.eq_C_of_natDegree_eq_zero h0
            apply hb_nu
            rw [this]
            exact Polynomial.isUnit_C.mpr (IsUnit.mk0 _ (by intro hc; apply hb0; rw [this, hc, map_zero]))
          have hdeg_sum : a.natDegree + b.natDegree = n := by
            rw [← hn, ← hdg, hab, Polynomial.natDegree_mul ha0 hb0]
          have hge : polyUnit g hg_ne = polyUnit a ha0 * polyUnit b hb0 := by
            apply Units.ext
            change algebraMap (Polynomial E) (RatFunc E) g =
              algebraMap _ _ a * algebraMap _ _ b
            rw [← map_mul]
            exact congrArg _ hab
          rw [hge]
          exact H.mul_mem (ih a.natDegree (by omega) a rfl ha0)
            (ih b.natDegree (by omega) b rfl hb0)
  rw [ratFunc_unit_eq_div u]
  exact H.mul_mem (hpoly _ _) (H.inv_mem (hpoly _ _))

/-- Weil reciprocity on `K_2^M(E(t))/p` for odd prime `p` and `CharZero E`. -/
theorem weilSum_of_mul_of [CharZero E] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (u v : (RatFunc E)ˣ) : weilSum hp hp2 (of p u * of p v) = 0 := by
  classical
  have hconst_const : ∀ (c₁ c₂ : E) (hc₁ : c₁ ≠ 0) (hc₂ : c₂ ≠ 0),
      weilSum hp hp2 (of p (polyUnit (C c₁) (C_ne_zero.mpr hc₁)) *
        of p (polyUnit (C c₂) (C_ne_zero.mpr hc₂))) = 0 := by
    intro c₁ c₂ hc₁ hc₂
    have hinf : (valInftyData E).partialHom hp hp2
        (of p (polyUnit (C c₁) (C_ne_zero.mpr hc₁)) *
          of p (polyUnit (C c₂) (C_ne_zero.mpr hc₂))) = 0 := by
      have h1 := (valInftyData_polyUnit (C c₁) (C_ne_zero.mpr hc₁)).1
      have h2 := (valInftyData_polyUnit (C c₂) (C_ne_zero.mpr hc₂)).1
      simp only [Polynomial.natDegree_C, Nat.cast_zero, neg_zero] at h1 h2
      simp [DiscreteValData.partialHom, h1, h2]
    have hfin : ∀ π : MonicIrred E,
        letI : Fact (Irreducible π.poly) := ⟨π.irred⟩
        (valPiData π).partialHom hp hp2
          (of p (polyUnit (C c₁) (C_ne_zero.mpr hc₁)) *
            of p (polyUnit (C c₂) (C_ne_zero.mpr hc₂))) = 0 := by
      intro π
      letI : Fact (Irreducible π.poly) := ⟨π.irred⟩
      have hnd1 : ¬ π.poly ∣ C c₁ := fun h =>
        π.irred.not_isUnit (isUnit_of_dvd_unit h (Polynomial.isUnit_C.mpr (IsUnit.mk0 c₁ hc₁)))
      have hnd2 : ¬ π.poly ∣ C c₂ := fun h =>
        π.irred.not_isUnit (isUnit_of_dvd_unit h (Polynomial.isUnit_C.mpr (IsUnit.mk0 c₂ hc₂)))
      have h1 := (valPiData_polyUnit_not_dvd π (C c₁) (C_ne_zero.mpr hc₁) hnd1).1
      have h2 := (valPiData_polyUnit_not_dvd π (C c₂) (C_ne_zero.mpr hc₂) hnd2).1
      simp [DiscreteValData.partialHom, h1, h2]
    simp only [weilSum, AddMonoidHom.coe_mk, ZeroHom.coe_mk, hinf, add_zero]
    rw [finsum_eq_zero_of_forall_eq_zero]
    intro π
    letI : Fact (Irreducible π.poly) := ⟨π.irred⟩
    simp [hfin π]
  have hconst_pi : ∀ (c : E) (hc : c ≠ 0) (π : MonicIrred E),
      weilSum hp hp2 (of p (polyUnit (C c) (C_ne_zero.mpr hc)) *
        of p (polyUnit π.poly π.ne_zero)) = 0 := by
    intro c hc π
    have hnd : ∀ π' : MonicIrred E, ¬ π'.poly ∣ C c := fun π' h =>
      π'.irred.not_isUnit (isUnit_of_dvd_unit h (Polynomial.isUnit_C.mpr (IsUnit.mk0 c hc)))
    have hsum : (∑ᶠ π' : MonicIrred E,
        (letI : Fact (Irreducible π'.poly) := ⟨π'.irred⟩
         normK1 π' hp ((valPiData π').partialHom hp hp2
           (of p (polyUnit (C c) (C_ne_zero.mpr hc)) *
             of p (polyUnit π.poly π.ne_zero))))) =
        (π.poly.natDegree : ℕ) • of p (Units.mk0 c hc) := by
      rw [finsum_eq_single _ π]
      · letI : Fact (Irreducible π.poly) := ⟨π.irred⟩
        have hc_val := valPiData_polyUnit_not_dvd π (C c) (C_ne_zero.mpr hc) (hnd π)
        have hpi_val := valPiData_self π
        have hpart : (valPiData π).partialHom hp hp2
            (of p (polyUnit (C c) (C_ne_zero.mpr hc)) *
              of p (polyUnit π.poly π.ne_zero)) =
            of p ((valPiData π).res (polyUnit (C c) (C_ne_zero.mpr hc))) := by
          simp [DiscreteValData.partialHom, hc_val.1, hpi_val.1, hpi_val.2]
        rw [hpart, normK1_of]
        have hres_eq : ((valPiData π).res (polyUnit (C c) (C_ne_zero.mpr hc)) : AdjoinRoot π.poly) =
            algebraMap E (AdjoinRoot π.poly) c := by
          rw [hc_val.2]
          rfl
        have hnorm_c : Algebra.norm E ((valPiData π).res (polyUnit (C c) (C_ne_zero.mpr hc)) :
            AdjoinRoot π.poly) = c ^ π.poly.natDegree := by
          rw [hres_eq, Algebra.norm_algebraMap]
          have hfinrank : Module.finrank E (AdjoinRoot π.poly) = π.poly.natDegree := by
            rw [Module.finrank_eq_card_basis (AdjoinRoot.powerBasis π.ne_zero).basis,
              Fintype.card_fin, AdjoinRoot.powerBasis_dim]
          rw [hfinrank]
        have hu_eq : Units.map (Algebra.norm E : AdjoinRoot π.poly →* E)
            ((valPiData π).res (polyUnit (C c) (C_ne_zero.mpr hc))) = (Units.mk0 c hc) ^ π.poly.natDegree := by
          apply Units.ext
          simpa using hnorm_c
        rw [hu_eq, of_pow]
      · intro π' hne
        letI : Fact (Irreducible π'.poly) := ⟨π'.irred⟩
        have hc_val := valPiData_polyUnit_not_dvd π' (C c) (C_ne_zero.mpr hc) (hnd π')
        have hpi_val := valPiData_polyUnit_not_dvd π' π.poly π.ne_zero (MonicIrred.not_dvd_of_ne hne)
        have hpart : (valPiData π').partialHom hp hp2
            (of p (polyUnit (C c) (C_ne_zero.mpr hc)) *
              of p (polyUnit π.poly π.ne_zero)) = 0 := by
          simp [DiscreteValData.partialHom, hc_val.1, hpi_val.1]
        rw [hpart, map_zero]
    have hinf : (valInftyData E).partialHom hp hp2
        (of p (polyUnit (C c) (C_ne_zero.mpr hc)) *
          of p (polyUnit π.poly π.ne_zero)) =
        -((π.poly.natDegree : ℕ) • of p (Units.mk0 c hc)) := by
      have hc_inf := valInftyData_polyUnit (C c) (C_ne_zero.mpr hc)
      have hpi_inf := valInftyData_polyUnit π.poly π.ne_zero
      have hres_c : (valInftyData E).res (polyUnit (C c) (C_ne_zero.mpr hc)) = Units.mk0 c hc := by
        apply Units.ext
        simpa using hc_inf.2
      have hres_pi : (valInftyData E).res (polyUnit π.poly π.ne_zero) = 1 := by
        apply Units.ext
        simpa [π.monic.leadingCoeff] using hpi_inf.2
      simp only [DiscreteValData.partialHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_mul,
        DiscreteValData.theta_of, TwistDual.snd_mul, hc_inf.1, hpi_inf.1, hres_c, hres_pi,
        Polynomial.natDegree_C, Nat.cast_zero, neg_zero, Int.cast_zero, zero_mul, add_zero,
        Int.cast_neg, Int.cast_natCast, mk_mul_neg]
      rw [← Nat.cast_comm, ← nsmul_eq_mul]
    simp only [weilSum, AddMonoidHom.coe_mk, ZeroHom.coe_mk, hsum, hinf, add_neg_cancel]
  have hpi_pi : ∀ π₁ π₂ : MonicIrred E,
      weilSum hp hp2 (of p (polyUnit π₁.poly π₁.ne_zero) *
        of p (polyUnit π₂.poly π₂.ne_zero)) = 0 := by
    intro π₁ π₂
    by_cases heq : π₁ = π₂
    · subst heq
      rw [of_mul_self_odd hp hp2, map_zero]
    have hinf : (valInftyData E).partialHom hp hp2
        (of p (polyUnit π₁.poly π₁.ne_zero) * of p (polyUnit π₂.poly π₂.ne_zero)) = 0 := by
      have h1 := valInftyData_polyUnit π₁.poly π₁.ne_zero
      have h2 := valInftyData_polyUnit π₂.poly π₂.ne_zero
      have hr1 : (valInftyData E).res (polyUnit π₁.poly π₁.ne_zero) = 1 :=
        Units.ext (by simpa [π₁.monic.leadingCoeff] using h1.2)
      have hr2 : (valInftyData E).res (polyUnit π₂.poly π₂.ne_zero) = 1 :=
        Units.ext (by simpa [π₂.monic.leadingCoeff] using h2.2)
      simp [DiscreteValData.partialHom, hr1, hr2]
    have hterm : ∀ π' : MonicIrred E, π' ≠ π₁ → π' ≠ π₂ →
        (letI : Fact (Irreducible π'.poly) := ⟨π'.irred⟩
         normK1 π' hp ((valPiData π').partialHom hp hp2
           (of p (polyUnit π₁.poly π₁.ne_zero) * of p (polyUnit π₂.poly π₂.ne_zero)))) = 0 := by
      intro π' h1 h2
      letI : Fact (Irreducible π'.poly) := ⟨π'.irred⟩
      have hv1 := (valPiData_polyUnit_not_dvd π' π₁.poly π₁.ne_zero (MonicIrred.not_dvd_of_ne h1)).1
      have hv2 := (valPiData_polyUnit_not_dvd π' π₂.poly π₂.ne_zero (MonicIrred.not_dvd_of_ne h2)).1
      have hp0 : (valPiData π').partialHom hp hp2
          (of p (polyUnit π₁.poly π₁.ne_zero) * of p (polyUnit π₂.poly π₂.ne_zero)) = 0 := by
        simp [DiscreteValData.partialHom, hv1, hv2]
      rw [hp0, map_zero]
    have hsum : (∑ᶠ π' : MonicIrred E,
        (letI : Fact (Irreducible π'.poly) := ⟨π'.irred⟩
         normK1 π' hp ((valPiData π').partialHom hp hp2
           (of p (polyUnit π₁.poly π₁.ne_zero) * of p (polyUnit π₂.poly π₂.ne_zero))))) =
        (letI : Fact (Irreducible π₁.poly) := ⟨π₁.irred⟩
         normK1 π₁ hp ((valPiData π₁).partialHom hp hp2
           (of p (polyUnit π₁.poly π₁.ne_zero) * of p (polyUnit π₂.poly π₂.ne_zero)))) +
        (letI : Fact (Irreducible π₂.poly) := ⟨π₂.irred⟩
         normK1 π₂ hp ((valPiData π₂).partialHom hp hp2
           (of p (polyUnit π₁.poly π₁.ne_zero) * of p (polyUnit π₂.poly π₂.ne_zero)))) := by
      rw [finsum_eq_sum_of_support_subset _ (s := ({π₁, π₂} : Finset (MonicIrred E)))]
      · rw [Finset.sum_pair heq]
      · intro π' hπ'
        simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
          Set.mem_singleton_iff]
        by_contra hnot
        push_neg at hnot
        exact hπ' (hterm π' hnot.1 hnot.2)
    simp only [weilSum, AddMonoidHom.coe_mk, ZeroHom.coe_mk, hsum, hinf, add_zero]
    letI : Fact (Irreducible π₁.poly) := ⟨π₁.irred⟩
    letI : Fact (Irreducible π₂.poly) := ⟨π₂.irred⟩
    have hv11 := valPiData_self π₁
    have hv12 := valPiData_polyUnit_not_dvd π₁ π₂.poly π₂.ne_zero (MonicIrred.not_dvd_of_ne heq)
    have hv22 := valPiData_self π₂
    have hv21 := valPiData_polyUnit_not_dvd π₂ π₁.poly π₁.ne_zero (MonicIrred.not_dvd_of_ne (Ne.symm heq))
    have hp1 : (valPiData π₁).partialHom hp hp2
        (of p (polyUnit π₁.poly π₁.ne_zero) * of p (polyUnit π₂.poly π₂.ne_zero)) =
        -(of p ((valPiData π₁).res (polyUnit π₂.poly π₂.ne_zero))) := by
      simp [DiscreteValData.partialHom, hv11.1, hv11.2, hv12.1]
    have hp2' : (valPiData π₂).partialHom hp hp2
        (of p (polyUnit π₁.poly π₁.ne_zero) * of p (polyUnit π₂.poly π₂.ne_zero)) =
        of p ((valPiData π₂).res (polyUnit π₁.poly π₁.ne_zero)) := by
      simp [DiscreteValData.partialHom, hv22.1, hv22.2, hv21.1]
    rw [hp1, hp2', map_neg, normK1_of, normK1_of]
    have hsym := norm_mk_symm π₁ π₂
    rw [← hv12.2, ← hv21.2] at hsym
    have hu : Units.map (Algebra.norm E : AdjoinRoot π₁.poly →* E)
        ((valPiData π₁).res (polyUnit π₂.poly π₂.ne_zero)) =
        ((-1 : Eˣ) ^ (π₁.poly.natDegree * π₂.poly.natDegree)) *
          Units.map (Algebra.norm E : AdjoinRoot π₂.poly →* E)
            ((valPiData π₂).res (polyUnit π₁.poly π₁.ne_zero)) := by
      apply Units.ext
      simpa using hsym
    rw [hu, of_mul, of_pow, of_neg_one_odd hp hp2, smul_zero, zero_add, neg_add_cancel]
  -- Extend from generators to all pairs `(u, v)` by subgroup induction
  let K1 : Subgroup (RatFunc E)ˣ :=
    { carrier := {u | ∀ v : (RatFunc E)ˣ, weilSum hp hp2 (of p u * of p v) = 0}
      one_mem' := fun v => by simp
      mul_mem' := fun {a b} ha hb v => by rw [of_mul, add_mul, map_add, ha v, hb v, add_zero]
      inv_mem' := fun {a} ha v => by rw [of_inv, mk_neg_mul, map_neg, ha v, neg_zero] }
  have hu : u ∈ K1 := by
    refine ratFunc_units_gen K1 ?_ ?_ u
    · intro c hc v
      let K2 : Subgroup (RatFunc E)ˣ :=
        { carrier := {v | weilSum hp hp2 (of p (polyUnit (C c) (C_ne_zero.mpr hc)) * of p v) = 0}
          one_mem' := by simp
          mul_mem' := fun {a b} ha hb => by
            show weilSum hp hp2 (of p _ * of p (a * b)) = 0
            rw [of_mul, mul_add, map_add, ha, hb, add_zero]
          inv_mem' := fun {a} ha => by
            show weilSum hp hp2 (of p _ * of p a⁻¹) = 0
            rw [of_inv, mk_mul_neg, map_neg, ha, neg_zero] }
      exact ratFunc_units_gen K2 (fun c₂ hc₂ => hconst_const c c₂ hc hc₂)
        (fun π => hconst_pi c hc π) v
    · intro π₁ v
      let K2 : Subgroup (RatFunc E)ˣ :=
        { carrier := {v | weilSum hp hp2 (of p (polyUnit π₁.poly π₁.ne_zero) * of p v) = 0}
          one_mem' := by simp
          mul_mem' := fun {a b} ha hb => by
            show weilSum hp hp2 (of p _ * of p (a * b)) = 0
            rw [of_mul, mul_add, map_add, ha, hb, add_zero]
          inv_mem' := fun {a} ha => by
            show weilSum hp hp2 (of p _ * of p a⁻¹) = 0
            rw [of_inv, mk_mul_neg, map_neg, ha, neg_zero] }
      refine ratFunc_units_gen K2 ?_ (fun π₂ => hpi_pi π₁ π₂) v
      intro c hc
      change weilSum hp hp2 (of p (polyUnit π₁.poly π₁.ne_zero) *
        of p (polyUnit (C c) (C_ne_zero.mpr hc))) = 0
      rw [of_mul_anticomm hp hp2, map_neg, hconst_pi c hc π₁, neg_zero]
  exact hu v

theorem weilSum_grade_two [CharZero E] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {x : MilnorK (RatFunc E) p} (hx : x ∈ grade (RatFunc E) p 2) :
    weilSum hp hp2 x = 0 := by
  refine AddSubgroup.closure_induction ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨s, rfl⟩
    rw [symbol_succ, symbol_one]
    exact weilSum_of_mul_of hp hp2 (s 0) (s 1)
  · exact map_zero _
  · intro a b _ _ ha hb; rw [map_add, ha, hb, add_zero]
  · intro a _ ha; rw [map_neg, ha, neg_zero]

/-- Representative of a unit `u ∈ (AdjoinRoot π.poly)ˣ` as a nonzero polynomial of degree `< deg π`. -/
noncomputable def repPi (π : MonicIrred E)
    (u : letI : Fact (Irreducible π.poly) := ⟨π.irred⟩; (AdjoinRoot π.poly)ˣ) : Polynomial E :=
  letI : Fact (Irreducible π.poly) := ⟨π.irred⟩
  (AdjoinRoot.mk_surjective (u : AdjoinRoot π.poly)).choose %ₘ π.poly

theorem repPi_mk (π : MonicIrred E)
    (u : letI : Fact (Irreducible π.poly) := ⟨π.irred⟩; (AdjoinRoot π.poly)ˣ) :
    letI : Fact (Irreducible π.poly) := ⟨π.irred⟩
    AdjoinRoot.mk π.poly (repPi π u) = (u : AdjoinRoot π.poly) := by
  letI : Fact (Irreducible π.poly) := ⟨π.irred⟩
  set f := (AdjoinRoot.mk_surjective (u : AdjoinRoot π.poly)).choose
  have hf : AdjoinRoot.mk π.poly f = (u : AdjoinRoot π.poly) :=
    (AdjoinRoot.mk_surjective (u : AdjoinRoot π.poly)).choose_spec
  have hdiv := Polynomial.modByMonic_add_div f π.poly
  have := congrArg (AdjoinRoot.mk π.poly) hdiv
  simp only [map_add, map_mul, AdjoinRoot.mk_self, zero_mul, add_zero] at this
  exact this.trans hf

theorem repPi_ne_zero (π : MonicIrred E)
    (u : letI : Fact (Irreducible π.poly) := ⟨π.irred⟩; (AdjoinRoot π.poly)ˣ) :
    repPi π u ≠ 0 := by
  letI : Fact (Irreducible π.poly) := ⟨π.irred⟩
  intro h
  have h0 := repPi_mk π u
  rw [h, map_zero] at h0
  exact u.ne_zero h0.symm

theorem repPi_not_dvd (π : MonicIrred E)
    (u : letI : Fact (Irreducible π.poly) := ⟨π.irred⟩; (AdjoinRoot π.poly)ˣ) :
    ¬ π.poly ∣ repPi π u := by
  letI : Fact (Irreducible π.poly) := ⟨π.irred⟩
  intro h
  have h0 := repPi_mk π u
  rw [AdjoinRoot.mk_eq_zero.mpr h] at h0
  exact u.ne_zero h0.symm

theorem repPi_natDegree_lt (π : MonicIrred E)
    (u : letI : Fact (Irreducible π.poly) := ⟨π.irred⟩; (AdjoinRoot π.poly)ˣ) :
    (repPi π u).natDegree < π.poly.natDegree := by
  have hlt := Polynomial.degree_modByMonic_lt
    ((AdjoinRoot.mk_surjective (letI : Fact (Irreducible π.poly) := ⟨π.irred⟩; (u : AdjoinRoot π.poly))).choose)
    π.monic
  exact Polynomial.natDegree_lt_natDegree (repPi_ne_zero π u) hlt

/-- Degree-2 lifting: for every monic irreducible `π` and unit `u ∈ (AdjoinRoot π)ˣ`,
there exists `z ∈ grade (RatFunc E) p 2` with `∂_π z = of p u` and `∂_{π'} z = 0` for `π' ≠ π`. -/
theorem exists_grade2_lift {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ∀ (d : ℕ) (π : MonicIrred E), π.poly.natDegree = d →
      ∀ (u : letI : Fact (Irreducible π.poly) := ⟨π.irred⟩; (AdjoinRoot π.poly)ˣ),
      ∃ z ∈ grade (RatFunc E) p 2,
        (letI : Fact (Irreducible π.poly) := ⟨π.irred⟩
         (valPiData π).partialHom hp hp2 z = of p u) ∧
        (∀ π' : MonicIrred E, π' ≠ π →
          letI : Fact (Irreducible π'.poly) := ⟨π'.irred⟩
          (valPiData π').partialHom hp hp2 z = 0) := by
  intro d
  classical
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro π hdeg u
    letI : Fact (Irreducible π.poly) := ⟨π.irred⟩
    set r := repPi π u
    have hr0 : r ≠ 0 := repPi_ne_zero π u
    have hrdeg : r.natDegree < d := hdeg ▸ repPi_natDegree_lt π u
    set x0 : MilnorK (RatFunc E) p := of p (polyUnit r hr0) * of p (polyUnit π.poly π.ne_zero)
    have hx0_mem : x0 ∈ grade (RatFunc E) p 2 := by
      have : x0 = symbol p ![polyUnit r hr0, polyUnit π.poly π.ne_zero] :=
        (symbol_pair p _ _).symm
      rw [this]
      exact symbol_mem_grade _ _ _
    have hx0_pi : (valPiData π).partialHom hp hp2 x0 = of p u := by
      have hr_val := valPiData_polyUnit_not_dvd π r hr0 (repPi_not_dvd π u)
      have hpi_val := valPiData_self π
      have hres : (valPiData π).res (polyUnit r hr0) = u := by
        apply Units.ext
        exact hr_val.2.trans (repPi_mk π u)
      simp [x0, DiscreteValData.partialHom, hr_val.1, hpi_val.1, hpi_val.2, hres]
    have hx0_ge : ∀ π' : MonicIrred E, π' ≠ π → d ≤ π'.poly.natDegree →
        letI : Fact (Irreducible π'.poly) := ⟨π'.irred⟩
        (valPiData π').partialHom hp hp2 x0 = 0 := by
      intro π' hne hge
      letI : Fact (Irreducible π'.poly) := ⟨π'.irred⟩
      have hnd_r : ¬ π'.poly ∣ r := by
        intro hd
        have hle := Polynomial.natDegree_le_of_dvd hd hr0
        omega
      have hv1 := (valPiData_polyUnit_not_dvd π' r hr0 hnd_r).1
      have hv2 := (valPiData_polyUnit_not_dvd π' π.poly π.ne_zero (MonicIrred.not_dvd_of_ne hne)).1
      simp [x0, DiscreteValData.partialHom, hv1, hv2]
    have hfin := finite_support_partialPi hp hp2 x0
    set S : Finset (MonicIrred E) := hfin.toFinset.erase π
    have hS_lt : ∀ π' ∈ S, π'.poly.natDegree < d := by
      intro π' hπ'
      have hne : π' ≠ π := (Finset.mem_erase.mp hπ').1
      have hnz : letI : Fact (Irreducible π'.poly) := ⟨π'.irred⟩
          (valPiData π').partialHom hp hp2 x0 ≠ 0 := by
        simpa [S, Set.Finite.mem_toFinset] using (Finset.mem_erase.mp hπ').2
      by_contra hge
      exact hnz (hx0_ge π' hne (by omega))
    have hex : ∀ π' : S, ∃ w ∈ grade (RatFunc E) p 2,
        (letI : Fact (Irreducible π'.1.poly) := ⟨π'.1.irred⟩
         (valPiData π'.1).partialHom hp hp2 w = (valPiData π'.1).partialHom hp hp2 x0) ∧
        (∀ π'' : MonicIrred E, π'' ≠ π'.1 →
          letI : Fact (Irreducible π''.poly) := ⟨π''.irred⟩
          (valPiData π'').partialHom hp hp2 w = 0) := by
      intro ⟨π', hπ'⟩
      letI : Fact (Irreducible π'.poly) := ⟨π'.irred⟩
      have hmem1 : (valPiData π').partialHom hp hp2 x0 ∈ grade (AdjoinRoot π'.poly) p 1 :=
        (valPiData π').partialHom_grade_succ hp hp2 1 hx0_mem
      rw [MilnorK.grade_one] at hmem1
      obtain ⟨v, hv⟩ := hmem1
      obtain ⟨w, hw_mem, hw_eq, hw_zero⟩ := ih π'.poly.natDegree (hS_lt π' hπ') π' rfl v.toMul
      exact ⟨w, hw_mem, hw_eq.trans hv, hw_zero⟩
    choose w hw_mem hw_eq hw_zero using hex
    refine ⟨x0 - ∑ π' : S, w π', (grade (RatFunc E) p 2).sub_mem hx0_mem
      (AddSubgroup.sum_mem _ fun i _ => hw_mem i), ?_, ?_⟩
    · rw [map_sub, map_sum, hx0_pi]
      have h0 : ∑ i : S, (valPiData π).partialHom hp hp2 (w i) = 0 := by
        refine Finset.sum_eq_zero fun i _ => ?_
        have hne : π ≠ i.1 := (Finset.mem_erase.mp i.2).1.symm
        exact hw_zero i π hne
      rw [h0, sub_zero]
    · intro π' hne
      letI : Fact (Irreducible π'.poly) := ⟨π'.irred⟩
      rw [map_sub, map_sum]
      by_cases hmem : π' ∈ S
      · rw [Finset.sum_eq_single ⟨π', hmem⟩]
        · rw [hw_eq ⟨π', hmem⟩, sub_self]
        · intro j _ hj
          exact hw_zero j π' (fun h => hj (Subtype.ext h.symm))
        · intro h; exact absurd (Finset.mem_univ _) h
      · have h0x : (valPiData π').partialHom hp hp2 x0 = 0 := by
          by_contra hnz
          apply hmem
          exact Finset.mem_erase.mpr ⟨hne, hfin.mem_toFinset.mpr hnz⟩
        have h0s : ∑ j : S, (valPiData π').partialHom hp hp2 (w j) = 0 := by
          refine Finset.sum_eq_zero fun j _ => ?_
          exact hw_zero j π' (fun h => hmem (h ▸ j.2))
        rw [h0x, h0s, sub_self]

end DegreeTwoAndWeil

section MilnorGradeThree

variable {E : Type*} [Field E]

/-- Degree-`d` filtration subgroup `L_d ⊆ K_3^M(E(t))/p`. -/
noncomputable def Lfilt (E : Type*) [Field E] (p d : ℕ) : AddSubgroup (MilnorK (RatFunc E) p) :=
  AddSubgroup.closure
    {x | ∃ (f₁ f₂ f₃ : Polynomial E) (h₁ : f₁ ≠ 0) (h₂ : f₂ ≠ 0) (h₃ : f₃ ≠ 0),
      f₁.natDegree ≤ d ∧ f₂.natDegree ≤ d ∧ f₃.natDegree ≤ d ∧
      x = of p (polyUnit f₁ h₁) * of p (polyUnit f₂ h₂) * of p (polyUnit f₃ h₃)}

theorem Lfilt_mono (p : ℕ) {d₁ d₂ : ℕ} (h : d₁ ≤ d₂) : Lfilt E p d₁ ≤ Lfilt E p d₂ := by
  rw [Lfilt, AddSubgroup.closure_le]
  rintro x ⟨f₁, f₂, f₃, h₁, h₂, h₃, hd₁, hd₂, hd₃, rfl⟩
  exact AddSubgroup.subset_closure
    ⟨f₁, f₂, f₃, h₁, h₂, h₃, hd₁.trans h, hd₂.trans h, hd₃.trans h, rfl⟩

theorem mem_Lfilt_of_deg_le (p d : ℕ) {f₁ f₂ f₃ : Polynomial E}
    (h₁ : f₁ ≠ 0) (h₂ : f₂ ≠ 0) (h₃ : f₃ ≠ 0)
    (hd₁ : f₁.natDegree ≤ d) (hd₂ : f₂.natDegree ≤ d) (hd₃ : f₃.natDegree ≤ d) :
    of p (polyUnit f₁ h₁) * of p (polyUnit f₂ h₂) * of p (polyUnit f₃ h₃) ∈ Lfilt E p d :=
  AddSubgroup.subset_closure ⟨f₁, f₂, f₃, h₁, h₂, h₃, hd₁, hd₂, hd₃, rfl⟩

theorem grade_three_le_iSup_Lfilt (p : ℕ) :
    MilnorK.grade (RatFunc E) p 3 ≤ ⨆ d : ℕ, Lfilt E p d := by
  rw [MilnorK.grade, AddSubgroup.closure_le]
  rintro _ ⟨s, rfl⟩
  have hsym : symbol p s = of p (s 0) * of p (s 1) * of p (s 2) := by
    rw [symbol_succ, symbol_succ, symbol_one, mul_assoc]
    rfl
  rw [hsym]
  have expand : ∀ u : (RatFunc E)ˣ, ∃ (n d : Polynomial E) (hn : n ≠ 0) (hd : d ≠ 0),
      of p u = of p (polyUnit n hn) - of p (polyUnit d hd) := by
    intro u
    refine ⟨u.1.num, u.1.denom, RatFunc.num_ne_zero u.ne_zero, RatFunc.denom_ne_zero u.1, ?_⟩
    conv_lhs => rw [ratFunc_unit_eq_div u]
    rw [of_mul, of_inv, sub_eq_add_neg]
  obtain ⟨n0, d0, hn0, hd0, h0⟩ := expand (s 0)
  obtain ⟨n1, d1, hn1, hd1, h1⟩ := expand (s 1)
  obtain ⟨n2, d2, hn2, hd2, h2⟩ := expand (s 2)
  set D := max (max (max n0.natDegree d0.natDegree) (max n1.natDegree d1.natDegree))
    (max n2.natDegree d2.natDegree)
  have hmem : ∀ (a b c : Polynomial E) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0),
      a.natDegree ≤ D → b.natDegree ≤ D → c.natDegree ≤ D →
      of p (polyUnit a ha) * of p (polyUnit b hb) * of p (polyUnit c hc) ∈ ⨆ d, Lfilt E p d := by
    intro a b c ha hb hc hda hdb hdc
    exact AddSubgroup.mem_iSup_of_mem D (mem_Lfilt_of_deg_le p D ha hb hc hda hdb hdc)
  rw [h0, h1, h2]
  simp only [sub_mul, mul_sub]
  refine (⨆ d, Lfilt E p d).sub_mem
    ((⨆ d, Lfilt E p d).sub_mem
      ((⨆ d, Lfilt E p d).sub_mem
        (hmem n0 n1 n2 hn0 hn1 hn2 (by omega) (by omega) (by omega))
        (hmem d0 n1 n2 hd0 hn1 hn2 (by omega) (by omega) (by omega)))
      ((⨆ d, Lfilt E p d).sub_mem
        (hmem n0 d1 n2 hn0 hd1 hn2 (by omega) (by omega) (by omega))
        (hmem d0 d1 n2 hd0 hd1 hn2 (by omega) (by omega) (by omega))))
    ((⨆ d, Lfilt E p d).sub_mem
      ((⨆ d, Lfilt E p d).sub_mem
        (hmem n0 n1 d2 hn0 hn1 hd2 (by omega) (by omega) (by omega))
        (hmem d0 n1 d2 hd0 hn1 hd2 (by omega) (by omega) (by omega)))
      ((⨆ d, Lfilt E p d).sub_mem
        (hmem n0 d1 d2 hn0 hd1 hd2 (by omega) (by omega) (by omega))
        (hmem d0 d1 d2 hd0 hd1 hd2 (by omega) (by omega) (by omega))))

theorem exists_Lfilt_of_mem_grade_three (p : ℕ) {x : MilnorK (RatFunc E) p}
    (hx : x ∈ grade (RatFunc E) p 3) : ∃ d : ℕ, x ∈ Lfilt E p d := by
  have hmem := grade_three_le_iSup_Lfilt p hx
  have hdir : Directed (· ≤ ·) (Lfilt E p) := fun a b =>
    ⟨max a b, Lfilt_mono p (le_max_left a b), Lfilt_mono p (le_max_right a b)⟩
  rw [AddSubgroup.mem_iSup_of_directed hdir] at hmem
  exact hmem

/-- Truncated degree-2 tensor ring `ZMod p × A₁ × G` for lifting a bi-additive Steinberg pairing
to `MilnorK F p →+ G`. -/
structure TruncTwo (p : ℕ) (A₁ G : Type*) where
  c0 : ZMod p
  c1 : A₁
  c2 : G

namespace TruncTwo

variable {p : ℕ} {A₁ G : Type*}

theorem ext {x y : TruncTwo p A₁ G} (h0 : x.c0 = y.c0) (h1 : x.c1 = y.c1) (h2 : x.c2 = y.c2) :
    x = y := by
  cases x; cases y; simp_all

instance [Zero A₁] [Zero G] : Zero (TruncTwo p A₁ G) := ⟨⟨0, 0, 0⟩⟩
instance [Zero A₁] [Zero G] : One (TruncTwo p A₁ G) := ⟨⟨1, 0, 0⟩⟩
instance [Add A₁] [Add G] : Add (TruncTwo p A₁ G) :=
  ⟨fun x y => ⟨x.c0 + y.c0, x.c1 + y.c1, x.c2 + y.c2⟩⟩
instance [Neg A₁] [Neg G] : Neg (TruncTwo p A₁ G) := ⟨fun x => ⟨-x.c0, -x.c1, -x.c2⟩⟩
instance [Sub A₁] [Sub G] : Sub (TruncTwo p A₁ G) :=
  ⟨fun x y => ⟨x.c0 - y.c0, x.c1 - y.c1, x.c2 - y.c2⟩⟩
instance [Zero A₁] [Zero G] : NatCast (TruncTwo p A₁ G) := ⟨fun n => ⟨n, 0, 0⟩⟩
instance [Zero A₁] [Zero G] : IntCast (TruncTwo p A₁ G) := ⟨fun n => ⟨n, 0, 0⟩⟩

noncomputable def mkRing [AddCommGroup A₁] [AddCommGroup G] [Module (ZMod p) A₁] [Module (ZMod p) G]
    (B : A₁ →ₗ[ZMod p] A₁ →ₗ[ZMod p] G) : Ring (TruncTwo p A₁ G) :=
  letI : Mul (TruncTwo p A₁ G) :=
    ⟨fun x y => ⟨x.c0 * y.c0, x.c0 • y.c1 + y.c0 • x.c1, x.c0 • y.c2 + y.c0 • x.c2 + B x.c1 y.c1⟩⟩
  { add_assoc := fun a b c => by apply TruncTwo.ext <;> exact add_assoc _ _ _
    zero_add := fun a => by apply TruncTwo.ext <;> exact zero_add _
    add_zero := fun a => by apply TruncTwo.ext <;> exact add_zero _
    nsmul := nsmulRec
    zsmul := zsmulRec
    neg_add_cancel := fun a => by apply TruncTwo.ext <;> exact neg_add_cancel _
    add_comm := fun a b => by apply TruncTwo.ext <;> exact add_comm _ _
    sub_eq_add_neg := fun a b => by apply TruncTwo.ext <;> exact sub_eq_add_neg _ _
    mul_assoc := fun a b c => by
      apply TruncTwo.ext
      · exact mul_assoc _ _ _
      · change (a.c0 * b.c0) • c.c1 + c.c0 • (a.c0 • b.c1 + b.c0 • a.c1) =
          a.c0 • (b.c0 • c.c1 + c.c0 • b.c1) + (b.c0 * c.c0) • a.c1
        rw [smul_add, smul_add, mul_smul, mul_smul, ← mul_smul c.c0 a.c0, mul_comm c.c0 a.c0,
          mul_smul, ← mul_smul c.c0 b.c0, mul_comm c.c0 b.c0, mul_smul]
        abel
      · change (a.c0 * b.c0) • c.c2 + c.c0 • (a.c0 • b.c2 + b.c0 • a.c2 + B a.c1 b.c1) +
            B (a.c0 • b.c1 + b.c0 • a.c1) c.c1 =
          a.c0 • (b.c0 • c.c2 + c.c0 • b.c2 + B b.c1 c.c1) + (b.c0 * c.c0) • a.c2 +
            B a.c1 (b.c0 • c.c1 + c.c0 • b.c1)
        simp only [smul_add, map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply]
        rw [mul_smul, mul_smul, ← mul_smul c.c0 a.c0, mul_comm c.c0 a.c0, mul_smul,
          ← mul_smul c.c0 b.c0, mul_comm c.c0 b.c0, mul_smul]
        abel
    one_mul := fun a => by
      apply TruncTwo.ext
      · exact one_mul _
      · change (1 : ZMod p) • a.c1 + a.c0 • (0 : A₁) = a.c1; simp
      · change (1 : ZMod p) • a.c2 + a.c0 • (0 : G) + B 0 a.c1 = a.c2; simp
    mul_one := fun a => by
      apply TruncTwo.ext
      · exact mul_one _
      · change a.c0 • (0 : A₁) + (1 : ZMod p) • a.c1 = a.c1; simp
      · change a.c0 • (0 : G) + (1 : ZMod p) • a.c2 + B a.c1 0 = a.c2; simp
    left_distrib := fun a b c => by
      apply TruncTwo.ext
      · exact left_distrib _ _ _
      · change a.c0 • (b.c1 + c.c1) + (b.c0 + c.c0) • a.c1 =
          (a.c0 • b.c1 + b.c0 • a.c1) + (a.c0 • c.c1 + c.c0 • a.c1)
        simp only [smul_add, add_smul]; abel
      · change a.c0 • (b.c2 + c.c2) + (b.c0 + c.c0) • a.c2 + B a.c1 (b.c1 + c.c1) =
          (a.c0 • b.c2 + b.c0 • a.c2 + B a.c1 b.c1) + (a.c0 • c.c2 + c.c0 • a.c2 + B a.c1 c.c1)
        simp only [smul_add, add_smul, map_add]; abel
    right_distrib := fun a b c => by
      apply TruncTwo.ext
      · exact right_distrib _ _ _
      · change (a.c0 + b.c0) • c.c1 + c.c0 • (a.c1 + b.c1) =
          (a.c0 • c.c1 + c.c0 • a.c1) + (b.c0 • c.c1 + c.c0 • b.c1)
        simp only [smul_add, add_smul]; abel
      · change (a.c0 + b.c0) • c.c2 + c.c0 • (a.c2 + b.c2) + B (a.c1 + b.c1) c.c1 =
          (a.c0 • c.c2 + c.c0 • a.c2 + B a.c1 c.c1) + (b.c0 • c.c2 + c.c0 • b.c2 + B b.c1 c.c1)
        simp only [smul_add, add_smul, map_add, LinearMap.add_apply]; abel
    zero_mul := fun a => by
      apply TruncTwo.ext
      · exact zero_mul _
      · change (0 : ZMod p) • a.c1 + a.c0 • (0 : A₁) = 0; simp
      · change (0 : ZMod p) • a.c2 + a.c0 • (0 : G) + B 0 a.c1 = 0; simp
    mul_zero := fun a => by
      apply TruncTwo.ext
      · exact mul_zero _
      · change a.c0 • (0 : A₁) + (0 : ZMod p) • a.c1 = 0; simp
      · change a.c0 • (0 : G) + (0 : ZMod p) • a.c2 + B a.c1 0 = 0; simp
    natCast_zero := by apply TruncTwo.ext; exact Nat.cast_zero; rfl; rfl
    natCast_succ := fun n => by
      apply TruncTwo.ext
      · exact Nat.cast_succ n
      · exact (add_zero 0).symm
      · exact (add_zero 0).symm
    intCast_ofNat := fun n => by apply TruncTwo.ext; exact Int.cast_natCast n; rfl; rfl
    intCast_negSucc := fun n => by
      apply TruncTwo.ext
      · exact Int.cast_negSucc n
      · exact neg_zero.symm
      · exact neg_zero.symm }

end TruncTwo

/-- Lift a bi-additive Steinberg pairing `B : Additive Fˣ → Additive Fˣ → G` (with `p • G = 0`)
to an additive homomorphism `MilnorK F p →+ G` sending `of p u * of p v ↦ B u v`. -/
noncomputable def liftDegTwo {F G : Type*} [Field F] [AddCommGroup G] {p : ℕ} (hp : 0 < p)
    (hG : ∀ g : G, p • g = 0)
    (B : Additive Fˣ → Additive Fˣ → G)
    (hadd_l : ∀ a₁ a₂ b, B (a₁ + a₂) b = B a₁ b + B a₂ b)
    (hadd_r : ∀ a b₁ b₂, B a (b₁ + b₂) = B a b₁ + B a b₂)
    (hSt : ∀ a b : Fˣ, (a : F) + (b : F) = 1 → B (Additive.ofMul a) (Additive.ofMul b) = 0) :
    MilnorK F p →+ G := by
  letI : Module (ZMod p) G := zmodModule hp hG
  have hzero_l : ∀ b, B 0 b = 0 := fun b => by
    have h := hadd_l 0 0 b
    rw [zero_add] at h
    calc B 0 b = B 0 b + 0 := (add_zero _).symm
      _ = B 0 b + (B 0 b + -(B 0 b)) := by rw [add_neg_cancel]
      _ = (B 0 b + B 0 b) + -(B 0 b) := (add_assoc _ _ _).symm
      _ = B 0 b + -(B 0 b) := by rw [← h]
      _ = 0 := add_neg_cancel _
  have hzero_r : ∀ a, B a 0 = 0 := fun a => by
    have h := hadd_r a 0 0
    rw [zero_add] at h
    calc B a 0 = B a 0 + 0 := (add_zero _).symm
      _ = B a 0 + (B a 0 + -(B a 0)) := by rw [add_neg_cancel]
      _ = (B a 0 + B a 0) + -(B a 0) := (add_assoc _ _ _).symm
      _ = B a 0 + -(B a 0) := by rw [← h]
      _ = 0 := add_neg_cancel _
  have hneg_nsmul : ∀ (n : ℕ) (x : Additive Fˣ), n • (-x) = -(n • x) := fun n x => by
    induction n with
    | zero => simp
    | succ k ih => rw [succ_nsmul, succ_nsmul, ih, neg_add]
  let P : AddSubgroup (Additive Fˣ) :=
    { carrier := {y | ∃ x : Additive Fˣ, p • x = y}
      zero_mem' := ⟨0, smul_zero p⟩
      add_mem' := fun ⟨a, ha⟩ ⟨b, hb⟩ => ⟨a + b, by rw [nsmul_add, ha, hb]⟩
      neg_mem' := fun ⟨a, ha⟩ => ⟨-a, by rw [hneg_nsmul, ha]⟩ }
  let A₁ := Additive Fˣ ⧸ P
  have hA₁ : ∀ x : A₁, p • x = 0 := by
    intro x
    obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective x
    rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]
    exact ⟨a, rfl⟩
  letI : Module (ZMod p) A₁ := zmodModule hp hA₁
  let Bhom : Additive Fˣ → Additive Fˣ →+ G := fun a =>
    { toFun := fun b => B a b
      map_zero' := hzero_r a
      map_add' := fun b₁ b₂ => hadd_r a b₁ b₂ }
  let B1 : Additive Fˣ →+ (A₁ →+ G) :=
    { toFun := fun a => QuotientAddGroup.lift P (Bhom a) (by
        rintro _ ⟨b, rfl⟩
        change B a (p • b) = 0
        have : Bhom a (p • b) = p • Bhom a b := map_nsmul (Bhom a) p b
        simpa [Bhom, hG] using this)
      map_zero' := AddMonoidHom.ext fun x => by
        obtain ⟨b, rfl⟩ := QuotientAddGroup.mk_surjective x
        exact hzero_l b
      map_add' := fun a₁ a₂ => AddMonoidHom.ext fun x => by
        obtain ⟨b, rfl⟩ := QuotientAddGroup.mk_surjective x
        exact hadd_l a₁ a₂ b }
  let B2 : A₁ →+ (A₁ →+ G) := QuotientAddGroup.lift P B1 (by
    rintro _ ⟨a, rfl⟩
    exact AddMonoidHom.ext fun x => by
      obtain ⟨b, rfl⟩ := QuotientAddGroup.mk_surjective x
      have h1 : B1 (p • a) = p • B1 a := map_nsmul B1 p a
      rw [h1, AddMonoidHom.nsmul_apply, hG]
      rfl)
  let Blin : A₁ →ₗ[ZMod p] A₁ →ₗ[ZMod p] G :=
    { toFun := fun a =>
        { toFun := fun b => B2 a b
          map_add' := fun b₁ b₂ => map_add (B2 a) b₁ b₂
          map_smul' := fun z b => by
            change B2 a (z.val • b) = z.val • B2 a b
            exact map_nsmul (B2 a) z.val b }
      map_add' := fun a₁ a₂ => LinearMap.ext fun b => by
        change B2 (a₁ + a₂) b = B2 a₁ b + B2 a₂ b
        rw [map_add]
        rfl
      map_smul' := fun z a => LinearMap.ext fun b => by
        change B2 (z.val • a) b = z.val • B2 a b
        rw [map_nsmul, AddMonoidHom.nsmul_apply] }
  letI : Ring (TruncTwo p A₁ G) := TruncTwo.mkRing Blin
  let φ : Additive Fˣ →+ TruncTwo p A₁ G :=
    { toFun := fun a => ⟨0, QuotientAddGroup.mk a, 0⟩
      map_zero' := by apply TruncTwo.ext <;> rfl
      map_add' := fun a b => by
        apply TruncTwo.ext
        · change (0 : ZMod p) = 0 + 0; simp
        · rfl
        · change (0 : G) = 0 + 0; simp }
  let rh : MilnorK F p →+* TruncTwo p A₁ G :=
    RingQuot.lift ⟨(TensorAlgebra.lift ℤ φ.toIntLinearMap).toRingHom, by
      intro x y h
      cases h with
      | steinberg a b hab =>
        simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_mul,
          TensorAlgebra.lift_ι_apply, AddMonoidHom.coe_toIntLinearMap]
        rw [map_zero]
        apply TruncTwo.ext
        · change (0 : ZMod p) * 0 = 0; simp
        · change (0 : ZMod p) • _ + (0 : ZMod p) • _ = (0 : A₁)
          rw [zero_smul, zero_smul, add_zero]
        · change (0 : ZMod p) • (0 : G) + (0 : ZMod p) • (0 : G) +
            B (Additive.ofMul a) (Additive.ofMul b) = 0
          rw [zero_smul, zero_add, zero_add, hSt a b hab]
      | natCast =>
        rw [map_natCast, map_zero]
        apply TruncTwo.ext
        · change (p : ZMod p) = 0; simp
        · rfl
        · rfl⟩
  exact
    { toFun := fun x => (rh x).c2
      map_zero' := by rw [map_zero]; rfl
      map_add' := fun x y => by rw [map_add]; rfl }

theorem liftDegTwo_of_mul_of {F G : Type*} [Field F] [AddCommGroup G] {p : ℕ} (hp : 0 < p)
    (hG : ∀ g : G, p • g = 0)
    (B : Additive Fˣ → Additive Fˣ → G)
    (hadd_l : ∀ a₁ a₂ b, B (a₁ + a₂) b = B a₁ b + B a₂ b)
    (hadd_r : ∀ a b₁ b₂, B a (b₁ + b₂) = B a b₁ + B a b₂)
    (hSt : ∀ a b : Fˣ, (a : F) + (b : F) = 1 → B (Additive.ofMul a) (Additive.ofMul b) = 0)
    (u v : Fˣ) :
    liftDegTwo hp hG B hadd_l hadd_r hSt (of p u * of p v) = B (Additive.ofMul u) (Additive.ofMul v) := by
  letI : Module (ZMod p) G := zmodModule hp hG
  simp only [liftDegTwo, AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_mul, of,
    RingQuot.lift_mkRingHom_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    TensorAlgebra.lift_ι_apply, AddMonoidHom.coe_toIntLinearMap]
  change (0 : ZMod p) • (0 : G) + (0 : ZMod p) • (0 : G) + B (Additive.ofMul u) (Additive.ofMul v) =
    B (Additive.ofMul u) (Additive.ofMul v)
  rw [zero_smul, zero_add, zero_add]

/-- Core Euclidean-Steinberg lemma for Milnor's Lemma 2.6:
if `f₁, f₂, g` have degree `< d = deg π` and `r = (f₁ * f₂) %ₘ π`, then
`of g * (of π * (of f₁ + of f₂ - of r)) ∈ L_{d-1}`. -/
theorem milnor_step_mul_mem {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {d : ℕ}
    (π : MonicIrred E) (hdeg : π.poly.natDegree = d + 1)
    {f₁ f₂ g : Polynomial E} (hf₁ : f₁ ≠ 0) (hf₂ : f₂ ≠ 0) (hg : g ≠ 0)
    (hd₁ : f₁.natDegree ≤ d) (hd₂ : f₂.natDegree ≤ d) (hdg : g.natDegree ≤ d)
    (hr : (f₁ * f₂) %ₘ π.poly ≠ 0) :
    of p (polyUnit g hg) *
      (of p (polyUnit π.poly π.ne_zero) *
        (of p (polyUnit f₁ hf₁) + of p (polyUnit f₂ hf₂) -
          of p (polyUnit ((f₁ * f₂) %ₘ π.poly) hr))) ∈ Lfilt E p d := by
  set r := (f₁ * f₂) %ₘ π.poly
  set q := (f₁ * f₂) /ₘ π.poly
  have hdiv : r + π.poly * q = f₁ * f₂ := Polynomial.modByMonic_add_div (f₁ * f₂) π.poly
  have hrdeg : r.natDegree ≤ d := by
    have hlt := Polynomial.natDegree_lt_natDegree hr (Polynomial.degree_modByMonic_lt (f₁ * f₂) π.monic)
    omega
  by_cases hq : q = 0
  · have hreq : r = f₁ * f₂ := by simpa [hq] using hdiv
    have hof : of p (polyUnit r hr) = of p (polyUnit f₁ hf₁) + of p (polyUnit f₂ hf₂) := by
      have : polyUnit r hr = polyUnit f₁ hf₁ * polyUnit f₂ hf₂ := by
        apply Units.ext; simp [polyUnit, hreq]
      rw [this, of_mul]
    rw [hof, sub_self, mul_zero, mul_zero]
    exact (Lfilt E p d).zero_mem
  · have hqdeg : q.natDegree ≤ d := by
      have hqp : (π.poly * q).natDegree = d + 1 + q.natDegree := by
        rw [Polynomial.natDegree_mul π.ne_zero hq, hdeg]
      have hsum : (r + π.poly * q).natDegree = d + 1 + q.natDegree := by
        rw [Polynomial.natDegree_add_eq_right_of_natDegree_lt (by omega), hqp]
      have hmul : (f₁ * f₂).natDegree ≤ d + d := by
        rw [Polynomial.natDegree_mul hf₁ hf₂]; omega
      rw [hdiv] at hsum
      omega
    set u₁ : (RatFunc E)ˣ :=
      polyUnit π.poly π.ne_zero * polyUnit q hq * (polyUnit f₁ hf₁ * polyUnit f₂ hf₂)⁻¹
    set u₂ : (RatFunc E)ˣ :=
      polyUnit r hr * (polyUnit f₁ hf₁ * polyUnit f₂ hf₂)⁻¹
    have hst : (u₁ : RatFunc E) + (u₂ : RatFunc E) = 1 := by
      simp only [u₁, u₂, Units.val_mul, Units.val_inv_eq_inv_val, val_polyUnit]
      have hf12 : algebraMap (Polynomial E) (RatFunc E) f₁ *
          algebraMap (Polynomial E) (RatFunc E) f₂ ≠ 0 := by
        rw [← map_mul]
        exact (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr (mul_ne_zero hf₁ hf₂)
      have hnum : algebraMap (Polynomial E) (RatFunc E) π.poly *
          algebraMap (Polynomial E) (RatFunc E) q +
          algebraMap (Polynomial E) (RatFunc E) r =
          algebraMap (Polynomial E) (RatFunc E) f₁ * algebraMap (Polynomial E) (RatFunc E) f₂ := by
        rw [← map_mul, ← map_add, ← map_mul, add_comm, hdiv]
      calc algebraMap (Polynomial E) (RatFunc E) π.poly * algebraMap (Polynomial E) (RatFunc E) q *
              (algebraMap (Polynomial E) (RatFunc E) f₁ * algebraMap (Polynomial E) (RatFunc E) f₂)⁻¹ +
            algebraMap (Polynomial E) (RatFunc E) r *
              (algebraMap (Polynomial E) (RatFunc E) f₁ * algebraMap (Polynomial E) (RatFunc E) f₂)⁻¹
          = (algebraMap (Polynomial E) (RatFunc E) π.poly * algebraMap (Polynomial E) (RatFunc E) q +
              algebraMap (Polynomial E) (RatFunc E) r) *
              (algebraMap (Polynomial E) (RatFunc E) f₁ * algebraMap (Polynomial E) (RatFunc E) f₂)⁻¹ := by
              rw [← add_mul]
        _ = 1 := by rw [hnum, mul_inv_cancel₀ hf12]
    have h0 := of_mul_of_eq_zero p u₁ u₂ hst
    set A := of p (polyUnit π.poly π.ne_zero)
    set Q := of p (polyUnit q hq)
    set R := of p (polyUnit r hr)
    set F1 := of p (polyUnit f₁ hf₁)
    set F2 := of p (polyUnit f₂ hf₂)
    set G := of p (polyUnit g hg)
    have hF12 : (F1 + F2) * (F1 + F2) = 0 := by
      rw [← of_mul]
      exact of_mul_self_odd hp hp2 _
    have hu1 : of p u₁ = A + Q - (F1 + F2) := by
      simp only [u₁, of_mul, of_inv, sub_eq_add_neg]; abel
    have hu2 : of p u₂ = R - (F1 + F2) := by
      simp only [u₂, of_mul, of_inv, sub_eq_add_neg]; rfl
    rw [hu1, hu2] at h0
    have hrel : A * (F1 + F2 - R) = Q * R - Q * F1 - Q * F2 - F1 * R - F2 * R := by
      have hexp : (A + Q - (F1 + F2)) * (R - (F1 + F2)) =
          -(A * (F1 + F2 - R)) + (Q * R - Q * F1 - Q * F2 - F1 * R - F2 * R) +
            (F1 + F2) * (F1 + F2) := by
        simp only [sub_eq_add_neg, add_mul, mul_add, mk_neg_mul, mk_mul_neg, mk_neg_mul_neg,
          neg_add, neg_neg]
        abel
      rw [hexp, hF12, add_zero] at h0
      exact eq_of_neg_add_eq_zero h0
    rw [hrel]
    simp only [mul_sub, ← mul_assoc]
    refine (Lfilt E p d).sub_mem
      ((Lfilt E p d).sub_mem
        ((Lfilt E p d).sub_mem
          ((Lfilt E p d).sub_mem
            (mem_Lfilt_of_deg_le p d hg hq hr hdg hqdeg hrdeg)
            (mem_Lfilt_of_deg_le p d hg hq hf₁ hdg hqdeg hd₁))
          (mem_Lfilt_of_deg_le p d hg hq hf₂ hdg hqdeg hd₂))
        (mem_Lfilt_of_deg_le p d hg hf₁ hr hdg hd₁ hrdeg))
      (mem_Lfilt_of_deg_le p d hg hf₂ hr hdg hd₂ hrdeg)

/-- Milnor's homomorphism `h_π : MilnorK (AdjoinRoot π) p →+ MilnorK (RatFunc E) p ⧸ L_{d-1}`
for `deg π = d + 1`. -/
noncomputable def hPiHom {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {d : ℕ}
    (π : MonicIrred E) (hdeg : π.poly.natDegree = d + 1) :
    letI : Fact (Irreducible π.poly) := ⟨π.irred⟩
    MilnorK (AdjoinRoot π.poly) p →+ (MilnorK (RatFunc E) p ⧸ Lfilt E p d) := by
  letI : Fact (Irreducible π.poly) := ⟨π.irred⟩
  set q := QuotientAddGroup.mk' (Lfilt E p d)
  have hQ_p : ∀ x : MilnorK (RatFunc E) p ⧸ Lfilt E p d, p • x = 0 := by
    intro x
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective x
    rw [← QuotientAddGroup.mk_nsmul, p_nsmul_eq_zero, QuotientAddGroup.mk_zero]
  have hrep_mul : ∀ (u₁ u₂ : (AdjoinRoot π.poly)ˣ),
      repPi π (u₁ * u₂) = (repPi π u₁ * repPi π u₂) %ₘ π.poly := by
    intro u₁ u₂
    have hmk : AdjoinRoot.mk π.poly (repPi π (u₁ * u₂)) =
        AdjoinRoot.mk π.poly ((repPi π u₁ * repPi π u₂) %ₘ π.poly) := by
      have hdiv := Polynomial.modByMonic_add_div (repPi π u₁ * repPi π u₂) π.poly
      have h1 := congrArg (AdjoinRoot.mk π.poly) hdiv
      simp only [map_add, map_mul, AdjoinRoot.mk_self, zero_mul, add_zero] at h1
      rw [h1, repPi_mk, repPi_mk, repPi_mk]
      rfl
    have hdvd : π.poly ∣ repPi π (u₁ * u₂) - (repPi π u₁ * repPi π u₂) %ₘ π.poly := by
      rw [← AdjoinRoot.mk_eq_zero, map_sub, hmk, sub_self]
    have hlt1 : (repPi π (u₁ * u₂)).degree < π.poly.degree :=
      Polynomial.degree_modByMonic_lt _ π.monic
    have hlt2 : ((repPi π u₁ * repPi π u₂) %ₘ π.poly).degree < π.poly.degree :=
      Polynomial.degree_modByMonic_lt _ π.monic
    have hsub_lt : (repPi π (u₁ * u₂) - (repPi π u₁ * repPi π u₂) %ₘ π.poly).degree < π.poly.degree :=
      lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt hlt1 hlt2)
    exact sub_eq_zero.mp (Polynomial.eq_zero_of_dvd_of_degree_lt hdvd hsub_lt)
  have hrep_one : repPi π 1 = 1 := by
    have hmk : AdjoinRoot.mk π.poly (repPi π 1) = AdjoinRoot.mk π.poly 1 := by
      rw [repPi_mk, map_one]; rfl
    have hdvd : π.poly ∣ repPi π 1 - 1 := by
      rw [← AdjoinRoot.mk_eq_zero, map_sub, hmk, sub_self]
    have hlt1 : (repPi π 1).degree < π.poly.degree := Polynomial.degree_modByMonic_lt _ π.monic
    have hlt2 : (1 : Polynomial E).degree < π.poly.degree := by
      rw [Polynomial.degree_one, Polynomial.degree_eq_natDegree π.ne_zero, hdeg]
      exact_mod_cast Nat.succ_pos d
    exact sub_eq_zero.mp (Polynomial.eq_zero_of_dvd_of_degree_lt hdvd
      (lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt hlt1 hlt2)))
  have hadd_right : ∀ (u v₁ v₂ : (AdjoinRoot π.poly)ˣ),
      q (of p (polyUnit (repPi π u) (repPi_ne_zero π u)) *
          of p (polyUnit (repPi π (v₁ * v₂)) (repPi_ne_zero π _)) *
          of p (polyUnit π.poly π.ne_zero)) =
      q (of p (polyUnit (repPi π u) (repPi_ne_zero π u)) *
          of p (polyUnit (repPi π v₁) (repPi_ne_zero π v₁)) *
          of p (polyUnit π.poly π.ne_zero)) +
      q (of p (polyUnit (repPi π u) (repPi_ne_zero π u)) *
          of p (polyUnit (repPi π v₂) (repPi_ne_zero π v₂)) *
          of p (polyUnit π.poly π.ne_zero)) := by
    intro u v₁ v₂
    rw [← map_add, eq_comm, ← sub_eq_zero, ← map_sub]
    rw [show q = QuotientAddGroup.mk' (Lfilt E p d) from rfl, QuotientAddGroup.mk'_apply,
      QuotientAddGroup.eq_zero_iff]
    have hr0 : (repPi π v₁ * repPi π v₂) %ₘ π.poly ≠ 0 := by
      rw [← hrep_mul v₁ v₂]; exact repPi_ne_zero π _
    have hstep := milnor_step_mul_mem hp hp2 π hdeg (repPi_ne_zero π v₁) (repPi_ne_zero π v₂)
      (repPi_ne_zero π u) (by have := repPi_natDegree_lt π v₁; omega)
      (by have := repPi_natDegree_lt π v₂; omega) (by have := repPi_natDegree_lt π u; omega) hr0
    have hof_eq : of p (polyUnit (repPi π (v₁ * v₂)) (repPi_ne_zero π _)) =
        of p (polyUnit ((repPi π v₁ * repPi π v₂) %ₘ π.poly) hr0) := by
      congr 1; apply Units.ext; simp [polyUnit, hrep_mul]
    rw [hof_eq]
    have hcomm : of p (polyUnit (repPi π u) (repPi_ne_zero π u)) *
        of p (polyUnit (repPi π v₁) (repPi_ne_zero π v₁)) * of p (polyUnit π.poly π.ne_zero) +
        of p (polyUnit (repPi π u) (repPi_ne_zero π u)) *
        of p (polyUnit (repPi π v₂) (repPi_ne_zero π v₂)) * of p (polyUnit π.poly π.ne_zero) -
        of p (polyUnit (repPi π u) (repPi_ne_zero π u)) *
        of p (polyUnit ((repPi π v₁ * repPi π v₂) %ₘ π.poly) hr0) *
        of p (polyUnit π.poly π.ne_zero) =
        -(of p (polyUnit (repPi π u) (repPi_ne_zero π u)) *
          (of p (polyUnit π.poly π.ne_zero) *
            (of p (polyUnit (repPi π v₁) (repPi_ne_zero π v₁)) +
              of p (polyUnit (repPi π v₂) (repPi_ne_zero π v₂)) -
              of p (polyUnit ((repPi π v₁ * repPi π v₂) %ₘ π.poly) hr0)))) := by
      have ha1 := of_mul_anticomm hp hp2 (polyUnit (repPi π v₁) (repPi_ne_zero π v₁))
        (polyUnit π.poly π.ne_zero)
      have ha2 := of_mul_anticomm hp hp2 (polyUnit (repPi π v₂) (repPi_ne_zero π v₂))
        (polyUnit π.poly π.ne_zero)
      have har := of_mul_anticomm hp hp2 (polyUnit ((repPi π v₁ * repPi π v₂) %ₘ π.poly) hr0)
        (polyUnit π.poly π.ne_zero)
      calc of p (polyUnit (repPi π u) (repPi_ne_zero π u)) *
              of p (polyUnit (repPi π v₁) (repPi_ne_zero π v₁)) * of p (polyUnit π.poly π.ne_zero) +
            of p (polyUnit (repPi π u) (repPi_ne_zero π u)) *
              of p (polyUnit (repPi π v₂) (repPi_ne_zero π v₂)) * of p (polyUnit π.poly π.ne_zero) -
            of p (polyUnit (repPi π u) (repPi_ne_zero π u)) *
              of p (polyUnit ((repPi π v₁ * repPi π v₂) %ₘ π.poly) hr0) *
              of p (polyUnit π.poly π.ne_zero)
          = of p (polyUnit (repPi π u) (repPi_ne_zero π u)) *
              (of p (polyUnit (repPi π v₁) (repPi_ne_zero π v₁)) * of p (polyUnit π.poly π.ne_zero)) +
            of p (polyUnit (repPi π u) (repPi_ne_zero π u)) *
              (of p (polyUnit (repPi π v₂) (repPi_ne_zero π v₂)) * of p (polyUnit π.poly π.ne_zero)) -
            of p (polyUnit (repPi π u) (repPi_ne_zero π u)) *
              (of p (polyUnit ((repPi π v₁ * repPi π v₂) %ₘ π.poly) hr0) *
                of p (polyUnit π.poly π.ne_zero)) := by simp only [mul_assoc]
        _ = -(of p (polyUnit (repPi π u) (repPi_ne_zero π u)) *
              (of p (polyUnit π.poly π.ne_zero) *
                (of p (polyUnit (repPi π v₁) (repPi_ne_zero π v₁)) +
                  of p (polyUnit (repPi π v₂) (repPi_ne_zero π v₂)) -
                  of p (polyUnit ((repPi π v₁ * repPi π v₂) %ₘ π.poly) hr0)))) := by
              rw [ha1, ha2, har]
              simp only [sub_eq_add_neg, mul_add, mk_mul_neg, neg_add, neg_neg]
    rw [hcomm]
    exact (Lfilt E p d).neg_mem hstep
  have hanti : ∀ (u v : (AdjoinRoot π.poly)ˣ),
      q (of p (polyUnit (repPi π u) (repPi_ne_zero π u)) *
          of p (polyUnit (repPi π v) (repPi_ne_zero π v)) *
          of p (polyUnit π.poly π.ne_zero)) =
      -q (of p (polyUnit (repPi π v) (repPi_ne_zero π v)) *
          of p (polyUnit (repPi π u) (repPi_ne_zero π u)) *
          of p (polyUnit π.poly π.ne_zero)) := by
    intro u v
    rw [← map_neg]
    congr 1
    rw [of_mul_anticomm hp hp2 (polyUnit (repPi π u) _) (polyUnit (repPi π v) _), mk_neg_mul]
  let B : Additive (AdjoinRoot π.poly)ˣ → Additive (AdjoinRoot π.poly)ˣ →
      (MilnorK (RatFunc E) p ⧸ Lfilt E p d) := fun u v =>
    q (of p (polyUnit (repPi π u.toMul) (repPi_ne_zero π _)) *
      of p (polyUnit (repPi π v.toMul) (repPi_ne_zero π _)) *
      of p (polyUnit π.poly π.ne_zero))
  have hB_r : ∀ u v₁ v₂, B u (v₁ + v₂) = B u v₁ + B u v₂ := fun u v₁ v₂ =>
    hadd_right u.toMul v₁.toMul v₂.toMul
  have hB_l : ∀ u₁ u₂ v, B (u₁ + u₂) v = B u₁ v + B u₂ v := fun u₁ u₂ v => by
    change q (of p (polyUnit (repPi π (u₁.toMul * u₂.toMul)) _) * _ * _) =
      q (of p (polyUnit (repPi π u₁.toMul) _) * _ * _) +
      q (of p (polyUnit (repPi π u₂.toMul) _) * _ * _)
    rw [hanti (u₁.toMul * u₂.toMul) v.toMul, hadd_right v.toMul u₁.toMul u₂.toMul,
      hanti u₁.toMul v.toMul, hanti u₂.toMul v.toMul]
    abel
  refine liftDegTwo hp.pos hQ_p B hB_l hB_r ?_
  intro a b hab
  change q (of p (polyUnit (repPi π a) (repPi_ne_zero π a)) *
    of p (polyUnit (repPi π b) (repPi_ne_zero π b)) * of p (polyUnit π.poly π.ne_zero)) = 0
  have hsum1 : repPi π a + repPi π b = 1 := by
    have hmk : AdjoinRoot.mk π.poly (repPi π a + repPi π b - 1) = 0 := by
      rw [map_sub, map_add, map_one, repPi_mk, repPi_mk, hab, sub_self]
    have hdvd : π.poly ∣ repPi π a + repPi π b - 1 := AdjoinRoot.mk_eq_zero.mp hmk
    have hlt1 : (repPi π a).degree < π.poly.degree := Polynomial.degree_modByMonic_lt _ π.monic
    have hlt2 : (repPi π b).degree < π.poly.degree := Polynomial.degree_modByMonic_lt _ π.monic
    have hlt3 : (1 : Polynomial E).degree < π.poly.degree := by
      rw [Polynomial.degree_one, Polynomial.degree_eq_natDegree π.ne_zero, hdeg]
      exact_mod_cast Nat.succ_pos d
    have hlt : (repPi π a + repPi π b - 1).degree < π.poly.degree :=
      lt_of_le_of_lt (Polynomial.degree_sub_le _ _)
        (max_lt (lt_of_le_of_lt (Polynomial.degree_add_le _ _) (max_lt hlt1 hlt2)) hlt3)
    exact sub_eq_zero.mp (Polynomial.eq_zero_of_dvd_of_degree_lt hdvd hlt)
  have hst : (polyUnit (repPi π a) (repPi_ne_zero π a) : RatFunc E) +
      (polyUnit (repPi π b) (repPi_ne_zero π b) : RatFunc E) = 1 := by
    simp only [val_polyUnit, ← map_add, hsum1, map_one]
  rw [of_mul_of_eq_zero p _ _ hst, zero_mul, map_zero]

theorem hPiHom_of_mul_of {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {d : ℕ}
    (π : MonicIrred E) (hdeg : π.poly.natDegree = d + 1)
    (u v : letI : Fact (Irreducible π.poly) := ⟨π.irred⟩; (AdjoinRoot π.poly)ˣ) :
    letI : Fact (Irreducible π.poly) := ⟨π.irred⟩
    hPiHom hp hp2 π hdeg (of p u * of p v) =
      QuotientAddGroup.mk' (Lfilt E p d)
        (of p (polyUnit (repPi π u) (repPi_ne_zero π u)) *
          of p (polyUnit (repPi π v) (repPi_ne_zero π v)) *
          of p (polyUnit π.poly π.ne_zero)) := by
  letI : Fact (Irreducible π.poly) := ⟨π.irred⟩
  simp only [hPiHom, liftDegTwo_of_mul_of]
  rfl

/-- Helper: `repPi π (AdjoinRoot.mk π f) = f` when `f ≠ 0` and `f.natDegree ≤ d` (`deg π = d + 1`). -/
theorem repPi_of_deg_le {d : ℕ} (π : MonicIrred E) (hdeg : π.poly.natDegree = d + 1)
    {f : Polynomial E} (hf : f ≠ 0) (hdf : f.natDegree ≤ d) :
    letI : Fact (Irreducible π.poly) := ⟨π.irred⟩
    ∀ (u : (AdjoinRoot π.poly)ˣ), (u : AdjoinRoot π.poly) = AdjoinRoot.mk π.poly f →
      repPi π u = f := by
  letI : Fact (Irreducible π.poly) := ⟨π.irred⟩
  intro u hu
  have hmk : AdjoinRoot.mk π.poly (repPi π u - f) = 0 := by
    rw [map_sub, repPi_mk, hu, sub_self]
  have hdvd : π.poly ∣ repPi π u - f := AdjoinRoot.mk_eq_zero.mp hmk
  have hlt1 : (repPi π u).degree < π.poly.degree := Polynomial.degree_modByMonic_lt _ π.monic
  have hlt2 : f.degree < π.poly.degree := by
    rw [Polynomial.degree_eq_natDegree hf, Polynomial.degree_eq_natDegree π.ne_zero, hdeg]
    exact_mod_cast Nat.lt_succ_of_le hdf
  exact sub_eq_zero.mp (Polynomial.eq_zero_of_dvd_of_degree_lt hdvd
    (lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt hlt1 hlt2)))

/-- Milnor's Theorem 2.3 (exactness in degree 3):
if `x ∈ grade (RatFunc E) p 3` has `∂_π x = 0` for all monic irreducibles `π`, then `x ∈ L_0`. -/
theorem milnor_grade3_ker {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {x : MilnorK (RatFunc E) p} (hx : x ∈ grade (RatFunc E) p 3)
    (hvan : ∀ π : MonicIrred E,
      letI : Fact (Irreducible π.poly) := ⟨π.irred⟩
      (valPiData π).partialHom hp hp2 x = 0) :
    x ∈ Lfilt E p 0 := by
  obtain ⟨D, hxD⟩ := exists_Lfilt_of_mem_grade_three p hx
  induction D with
  | zero => exact hxD
  | succ d ih =>
    apply ih
    -- Show `x ∈ Lfilt E p d` by proving `q y = ∑_{deg π = d+1} h_π (∂_π y)` for all `y ∈ L_{d+1}`
    set q := QuotientAddGroup.mk' (Lfilt E p d)
    let S : MilnorK (RatFunc E) p →+ (MilnorK (RatFunc E) p ⧸ Lfilt E p d) :=
      { toFun := fun y =>
          ∑ᶠ π : {π : MonicIrred E // π.poly.natDegree = d + 1},
            (letI : Fact (Irreducible π.1.poly) := ⟨π.1.irred⟩
             hPiHom hp hp2 π.1 π.2 ((valPiData π.1).partialHom hp hp2 y))
        map_zero' := by simp
        map_add' := fun a b => by
          have hfin : ∀ y : MilnorK (RatFunc E) p,
              Function.HasFiniteSupport (fun π : {π : MonicIrred E // π.poly.natDegree = d + 1} =>
                letI : Fact (Irreducible π.1.poly) := ⟨π.1.irred⟩
                hPiHom hp hp2 π.1 π.2 ((valPiData π.1).partialHom hp hp2 y)) := by
            intro y
            change (Function.support _).Finite
            refine ((finite_support_partialPi hp hp2 y).preimage Subtype.val_injective.injOn).subset ?_
            intro π hπ h0
            letI : Fact (Irreducible π.1.poly) := ⟨π.1.irred⟩
            exact hπ (by simp [h0])
          have hadd : (fun π : {π : MonicIrred E // π.poly.natDegree = d + 1} =>
              letI : Fact (Irreducible π.1.poly) := ⟨π.1.irred⟩
              hPiHom hp hp2 π.1 π.2 ((valPiData π.1).partialHom hp hp2 (a + b))) =
            (fun π : {π : MonicIrred E // π.poly.natDegree = d + 1} =>
              (letI : Fact (Irreducible π.1.poly) := ⟨π.1.irred⟩
               hPiHom hp hp2 π.1 π.2 ((valPiData π.1).partialHom hp hp2 a)) +
              (letI : Fact (Irreducible π.1.poly) := ⟨π.1.irred⟩
               hPiHom hp hp2 π.1 π.2 ((valPiData π.1).partialHom hp hp2 b))) := by
            ext π
            letI : Fact (Irreducible π.1.poly) := ⟨π.1.irred⟩
            simp [map_add]
          rw [hadd, finsum_add_distrib (hfin a) (hfin b)] }
    -- Prove `q y = S y` for all `y ∈ L_{d+1}`
    have hqS : ∀ y ∈ Lfilt E p (d + 1), q y = S y := by
      -- First prove `q = S` on the three canonical generator shapes:
      -- (0) all three degrees ≤ d
      have h0 : ∀ {f₁ f₂ f₃ : Polynomial E} (h₁ : f₁ ≠ 0) (h₂ : f₂ ≠ 0) (h₃ : f₃ ≠ 0),
          f₁.natDegree ≤ d → f₂.natDegree ≤ d → f₃.natDegree ≤ d →
          q (of p (polyUnit f₁ h₁) * of p (polyUnit f₂ h₂) * of p (polyUnit f₃ h₃)) =
          S (of p (polyUnit f₁ h₁) * of p (polyUnit f₂ h₂) * of p (polyUnit f₃ h₃)) := by
        intro f₁ f₂ f₃ h₁ h₂ h₃ hd₁ hd₂ hd₃
        have hl : q (of p (polyUnit f₁ h₁) * of p (polyUnit f₂ h₂) * of p (polyUnit f₃ h₃)) = 0 := by
          rw [show q = QuotientAddGroup.mk' (Lfilt E p d) from rfl, QuotientAddGroup.mk'_apply,
            QuotientAddGroup.eq_zero_iff]
          exact mem_Lfilt_of_deg_le p d h₁ h₂ h₃ hd₁ hd₂ hd₃
        rw [hl, eq_comm]
        simp only [S, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
        rw [finsum_eq_zero_of_forall_eq_zero]
        rintro ⟨π, hdeg⟩
        letI : Fact (Irreducible π.poly) := ⟨π.irred⟩
        have hnd1 : ¬ π.poly ∣ f₁ := fun hd => by have := Polynomial.natDegree_le_of_dvd hd h₁; omega
        have hnd2 : ¬ π.poly ∣ f₂ := fun hd => by have := Polynomial.natDegree_le_of_dvd hd h₂; omega
        have hnd3 : ¬ π.poly ∣ f₃ := fun hd => by have := Polynomial.natDegree_le_of_dvd hd h₃; omega
        have hv1 := (valPiData_polyUnit_not_dvd π f₁ h₁ hnd1).1
        have hv2 := (valPiData_polyUnit_not_dvd π f₂ h₂ hnd2).1
        have hv3 := (valPiData_polyUnit_not_dvd π f₃ h₃ hnd3).1
        have hp0 : (valPiData π).partialHom hp hp2
            (of p (polyUnit f₁ h₁) * of p (polyUnit f₂ h₂) * of p (polyUnit f₃ h₃)) = 0 := by
          simp [DiscreteValData.partialHom, hv1, hv2, hv3]
        rw [hp0, map_zero]
      -- (1) two degrees ≤ d and one monic irreducible of degree d + 1
      have h1_right : ∀ {f₁ f₂ : Polynomial E} (h₁ : f₁ ≠ 0) (h₂ : f₂ ≠ 0)
          (π : MonicIrred E) (hdeg : π.poly.natDegree = d + 1),
          f₁.natDegree ≤ d → f₂.natDegree ≤ d →
          q (of p (polyUnit f₁ h₁) * of p (polyUnit f₂ h₂) * of p (polyUnit π.poly π.ne_zero)) =
          S (of p (polyUnit f₁ h₁) * of p (polyUnit f₂ h₂) * of p (polyUnit π.poly π.ne_zero)) := by
        intro f₁ f₂ h₁ h₂ π hdeg hd₁ hd₂
        simp only [S, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
        rw [finsum_eq_single _ ⟨π, hdeg⟩]
        · letI : Fact (Irreducible π.poly) := ⟨π.irred⟩
          have hnd1 : ¬ π.poly ∣ f₁ := fun hd => by have := Polynomial.natDegree_le_of_dvd hd h₁; omega
          have hnd2 : ¬ π.poly ∣ f₂ := fun hd => by have := Polynomial.natDegree_le_of_dvd hd h₂; omega
          have hv1 := valPiData_polyUnit_not_dvd π f₁ h₁ hnd1
          have hv2 := valPiData_polyUnit_not_dvd π f₂ h₂ hnd2
          have hv3 := valPiData_self π
          have hpart : (valPiData π).partialHom hp hp2
              (of p (polyUnit f₁ h₁) * of p (polyUnit f₂ h₂) * of p (polyUnit π.poly π.ne_zero)) =
              of p ((valPiData π).res (polyUnit f₁ h₁)) * of p ((valPiData π).res (polyUnit f₂ h₂)) := by
            simp [DiscreteValData.partialHom, hv1.1, hv2.1, hv3.1, hv3.2]
          rw [hpart, hPiHom_of_mul_of hp hp2 π hdeg]
          have hr1 : repPi π ((valPiData π).res (polyUnit f₁ h₁)) = f₁ :=
            repPi_of_deg_le π hdeg h₁ hd₁ _ hv1.2
          have hr2 : repPi π ((valPiData π).res (polyUnit f₂ h₂)) = f₂ :=
            repPi_of_deg_le π hdeg h₂ hd₂ _ hv2.2
          congr 1
          have hu1 : polyUnit (repPi π ((valPiData π).res (polyUnit f₁ h₁))) (repPi_ne_zero π _) =
              polyUnit f₁ h₁ := Units.ext (by
                change algebraMap (Polynomial E) (RatFunc E) _ = algebraMap _ _ f₁
                rw [hr1])
          have hu2 : polyUnit (repPi π ((valPiData π).res (polyUnit f₂ h₂))) (repPi_ne_zero π _) =
              polyUnit f₂ h₂ := Units.ext (by
                change algebraMap (Polynomial E) (RatFunc E) _ = algebraMap _ _ f₂
                rw [hr2])
          rw [hu1, hu2]
        · rintro ⟨π', hdeg'⟩ hne
          letI : Fact (Irreducible π'.poly) := ⟨π'.irred⟩
          have hne' : π' ≠ π := fun h => hne (Subtype.ext h)
          have hnd1 : ¬ π'.poly ∣ f₁ := fun hd => by have := Polynomial.natDegree_le_of_dvd hd h₁; omega
          have hnd2 : ¬ π'.poly ∣ f₂ := fun hd => by have := Polynomial.natDegree_le_of_dvd hd h₂; omega
          have hnd3 : ¬ π'.poly ∣ π.poly := MonicIrred.not_dvd_of_ne hne'
          have hv1 := (valPiData_polyUnit_not_dvd π' f₁ h₁ hnd1).1
          have hv2 := (valPiData_polyUnit_not_dvd π' f₂ h₂ hnd2).1
          have hv3 := (valPiData_polyUnit_not_dvd π' π.poly π.ne_zero hnd3).1
          have hp0 : (valPiData π').partialHom hp hp2
              (of p (polyUnit f₁ h₁) * of p (polyUnit f₂ h₂) * of p (polyUnit π.poly π.ne_zero)) = 0 := by
            simp [DiscreteValData.partialHom, hv1, hv2, hv3]
          rw [hp0, map_zero]
      -- Helper: `q x = S x` is closed under negation, addition, and permutation of factors
      have h_eq_ker : ∀ a b : MilnorK (RatFunc E) p, q a = S a → q b = S b →
          q (a + b) = S (a + b) := fun a b ha hb => by rw [map_add, map_add, ha, hb]
      have h_eq_sub : ∀ a b : MilnorK (RatFunc E) p, q a = S a → q b = S b →
          q (a - b) = S (a - b) := fun a b ha hb => by rw [map_sub, map_sub, ha, hb]
      have h_eq_neg : ∀ a : MilnorK (RatFunc E) p, q a = S a → q (-a) = S (-a) :=
        fun a ha => by rw [map_neg, map_neg, ha]
      -- Reduction of product of two monic irreducibles of degree d + 1:
      -- `of π₁ * of π₂ = of π₁ * of r - of π₂ * of r` where `r = π₂ - π₁` has deg ≤ d
      have h_two_irred : ∀ (π₁ π₂ : MonicIrred E) (h₁ : π₁.poly.natDegree = d + 1)
          (h₂ : π₂.poly.natDegree = d + 1),
          π₁ ≠ π₂ →
          ∃ (r : Polynomial E) (hr : r ≠ 0), r.natDegree ≤ d ∧
            of p (polyUnit π₁.poly π₁.ne_zero) * of p (polyUnit π₂.poly π₂.ne_zero) =
              of p (polyUnit π₁.poly π₁.ne_zero) * of p (polyUnit r hr) -
              of p (polyUnit π₂.poly π₂.ne_zero) * of p (polyUnit r hr) := by
        intro π₁ π₂ h₁ h₂ hne
        set r := π₂.poly - π₁.poly
        have hr0 : r ≠ 0 := by
          intro h
          apply hne
          have : π₁.poly = π₂.poly := (sub_eq_zero.mp h).symm
          cases π₁; cases π₂; simp_all
        have hrdeg : r.natDegree ≤ d := by
          by_contra hgt
          have hle : r.natDegree ≤ d + 1 :=
            (Polynomial.natDegree_sub_le _ _).trans (by omega)
          have heq : r.natDegree = d + 1 := by omega
          have hcoeff : r.coeff (d + 1) ≠ 0 := by
            rw [← heq]; exact Polynomial.leadingCoeff_ne_zero.mpr hr0
          apply hcoeff
          simp only [r, Polynomial.coeff_sub]
          have hc1 : π₁.poly.coeff (d + 1) = 1 := by rw [← h₁]; exact π₁.monic.coeff_natDegree
          have hc2 : π₂.poly.coeff (d + 1) = 1 := by rw [← h₂]; exact π₂.monic.coeff_natDegree
          rw [hc1, hc2, sub_self]
        refine ⟨r, hr0, hrdeg, ?_⟩
        set u₁ := polyUnit π₁.poly π₁.ne_zero * (polyUnit π₂.poly π₂.ne_zero)⁻¹
        set u₂ := polyUnit r hr0 * (polyUnit π₂.poly π₂.ne_zero)⁻¹
        have hst : (u₁ : RatFunc E) + (u₂ : RatFunc E) = 1 := by
          simp only [u₁, u₂, Units.val_mul, Units.val_inv_eq_inv_val, val_polyUnit]
          have h20 : algebraMap (Polynomial E) (RatFunc E) π₂.poly ≠ 0 :=
            (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr π₂.ne_zero
          rw [← add_mul, ← map_add, show π₁.poly + r = π₂.poly by simp [r], mul_inv_cancel₀ h20]
        have hst0 := of_mul_of_eq_zero p u₁ u₂ hst
        simp only [u₁, u₂, of_mul, of_inv] at hst0
        have hself := of_mul_self_odd hp hp2 (polyUnit π₂.poly π₂.ne_zero)
        have hanti := of_mul_anticomm hp hp2 (polyUnit π₁.poly π₁.ne_zero)
          (polyUnit π₂.poly π₂.ne_zero)
        have hexp : (of p (polyUnit π₁.poly π₁.ne_zero) + -of p (polyUnit π₂.poly π₂.ne_zero)) *
            (of p (polyUnit r hr0) + -of p (polyUnit π₂.poly π₂.ne_zero)) =
            of p (polyUnit π₁.poly π₁.ne_zero) * of p (polyUnit r hr0) -
            of p (polyUnit π₁.poly π₁.ne_zero) * of p (polyUnit π₂.poly π₂.ne_zero) -
            of p (polyUnit π₂.poly π₂.ne_zero) * of p (polyUnit r hr0) +
            of p (polyUnit π₂.poly π₂.ne_zero) * of p (polyUnit π₂.poly π₂.ne_zero) := by
          simp only [sub_eq_add_neg, add_mul, mul_add, mk_neg_mul, mk_mul_neg, mk_neg_mul_neg]
          abel
        rw [hexp, hself, add_zero] at hst0
        exact (sub_eq_zero.mp (by rw [← hst0]; abel)).symm
      -- Now prove `q = S` for any triple `(f₁, f₂, f₃)` where each `fᵢ` is either deg ≤ d or a monic irred of deg d + 1
      have h_base : ∀ (a b c : Polynomial E) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0),
          (a.natDegree ≤ d ∨ ∃ π : MonicIrred E, π.poly = a ∧ π.poly.natDegree = d + 1) →
          (b.natDegree ≤ d ∨ ∃ π : MonicIrred E, π.poly = b ∧ π.poly.natDegree = d + 1) →
          (c.natDegree ≤ d ∨ ∃ π : MonicIrred E, π.poly = c ∧ π.poly.natDegree = d + 1) →
          q (of p (polyUnit a ha) * of p (polyUnit b hb) * of p (polyUnit c hc)) =
          S (of p (polyUnit a ha) * of p (polyUnit b hb) * of p (polyUnit c hc)) := by
        -- Helper for 1 irred in any position
        have h1_any : ∀ (f₁ f₂ : Polynomial E) (hf₁ : f₁ ≠ 0) (hf₂ : f₂ ≠ 0)
            (π : MonicIrred E) (hdeg : π.poly.natDegree = d + 1),
            f₁.natDegree ≤ d → f₂.natDegree ≤ d →
            (q (of p (polyUnit f₁ hf₁) * of p (polyUnit π.poly π.ne_zero) * of p (polyUnit f₂ hf₂)) =
             S (of p (polyUnit f₁ hf₁) * of p (polyUnit π.poly π.ne_zero) * of p (polyUnit f₂ hf₂))) ∧
            (q (of p (polyUnit π.poly π.ne_zero) * of p (polyUnit f₁ hf₁) * of p (polyUnit f₂ hf₂)) =
             S (of p (polyUnit π.poly π.ne_zero) * of p (polyUnit f₁ hf₁) * of p (polyUnit f₂ hf₂))) := by
          intro f₁ f₂ hf₁ hf₂ π hdeg hd₁ hd₂
          constructor
          · have : of p (polyUnit f₁ hf₁) * of p (polyUnit π.poly π.ne_zero) * of p (polyUnit f₂ hf₂) =
                -(of p (polyUnit f₁ hf₁) * of p (polyUnit f₂ hf₂) * of p (polyUnit π.poly π.ne_zero)) := by
              rw [mul_assoc, of_mul_anticomm hp hp2 (polyUnit π.poly _) (polyUnit f₂ hf₂),
                mk_mul_neg, ← mul_assoc]
            rw [this]
            exact h_eq_neg _ (h1_right hf₁ hf₂ π hdeg hd₁ hd₂)
          · have : of p (polyUnit π.poly π.ne_zero) * of p (polyUnit f₁ hf₁) * of p (polyUnit f₂ hf₂) =
                of p (polyUnit f₁ hf₁) * of p (polyUnit f₂ hf₂) * of p (polyUnit π.poly π.ne_zero) := by
              rw [of_mul_anticomm hp hp2 (polyUnit π.poly _) (polyUnit f₁ hf₁), mk_neg_mul,
                mul_assoc, of_mul_anticomm hp hp2 (polyUnit π.poly _) (polyUnit f₂ hf₂),
                mk_mul_neg, neg_neg, ← mul_assoc]
            rw [this]
            exact h1_right hf₁ hf₂ π hdeg hd₁ hd₂
        -- Helper for 2 irreds + 1 small in any order: `(π₁, π₂, f)`
        have h2_left : ∀ (π₁ π₂ : MonicIrred E) (h₁ : π₁.poly.natDegree = d + 1)
            (h₂ : π₂.poly.natDegree = d + 1) (f : Polynomial E) (hf : f ≠ 0), f.natDegree ≤ d →
            q (of p (polyUnit π₁.poly π₁.ne_zero) * of p (polyUnit π₂.poly π₂.ne_zero) *
                of p (polyUnit f hf)) =
            S (of p (polyUnit π₁.poly π₁.ne_zero) * of p (polyUnit π₂.poly π₂.ne_zero) *
                of p (polyUnit f hf)) := by
          intro π₁ π₂ h₁ h₂ f hf hdf
          by_cases heq : π₁ = π₂
          · subst heq; rw [of_mul_self_odd hp hp2, zero_mul, map_zero, map_zero]
          · obtain ⟨r, hr, hrdeg, hred⟩ := h_two_irred π₁ π₂ h₁ h₂ heq
            rw [hred, sub_mul]
            exact h_eq_sub _ _
              ((h1_any r f hr hf π₁ h₁ hrdeg hdf).2)
              ((h1_any r f hr hf π₂ h₂ hrdeg hdf).2)
        intro a b c ha hb hc ha' hb' hc'
        rcases ha' with hda | ⟨π₁, rfl, h1⟩ <;>
        rcases hb' with hdb | ⟨π₂, rfl, h2⟩ <;>
        rcases hc' with hdc | ⟨π₃, rfl, h3⟩
        · exact h0 ha hb hc hda hdb hdc
        · exact h1_right ha hb π₃ h3 hda hdb
        · exact (h1_any a c ha hc π₂ h2 hda hdc).1
        · have : of p (polyUnit a ha) * of p (polyUnit π₂.poly hb) * of p (polyUnit π₃.poly hc) =
              of p (polyUnit π₂.poly hb) * of p (polyUnit π₃.poly hc) * of p (polyUnit a ha) := by
            rw [of_mul_anticomm hp hp2 (polyUnit a ha) (polyUnit π₂.poly hb), mk_neg_mul,
              mul_assoc, of_mul_anticomm hp hp2 (polyUnit a ha) (polyUnit π₃.poly hc),
              mk_mul_neg, neg_neg, ← mul_assoc]
          rw [this]
          exact h2_left π₂ π₃ h2 h3 a ha hda
        · exact (h1_any b c hb hc π₁ h1 hdb hdc).2
        · have : of p (polyUnit π₁.poly ha) * of p (polyUnit b hb) * of p (polyUnit π₃.poly hc) =
              -(of p (polyUnit π₁.poly ha) * of p (polyUnit π₃.poly hc) * of p (polyUnit b hb)) := by
            rw [mul_assoc, of_mul_anticomm hp hp2 (polyUnit b hb) (polyUnit π₃.poly hc),
              mk_mul_neg, ← mul_assoc]
          rw [this]
          exact h_eq_neg _ (h2_left π₁ π₃ h1 h3 b hb hdb)
        · exact h2_left π₁ π₂ h1 h2 c hc hdc
        · -- All three are monic irreducibles of degree d + 1
          by_cases heq : π₁ = π₂
          · subst heq; rw [of_mul_self_odd hp hp2, zero_mul, map_zero, map_zero]
          · obtain ⟨r, hr, hrdeg, hred⟩ := h_two_irred π₁ π₂ h1 h2 heq
            rw [hred, sub_mul]
            have hswap : ∀ (π : MonicIrred E) (hπ : π.poly.natDegree = d + 1),
                q (of p (polyUnit π.poly π.ne_zero) * of p (polyUnit r hr) *
                    of p (polyUnit π₃.poly hc)) =
                S (of p (polyUnit π.poly π.ne_zero) * of p (polyUnit r hr) *
                    of p (polyUnit π₃.poly hc)) := by
              intro π hπ
              have : of p (polyUnit π.poly π.ne_zero) * of p (polyUnit r hr) *
                    of p (polyUnit π₃.poly hc) =
                  -(of p (polyUnit π.poly π.ne_zero) * of p (polyUnit π₃.poly hc) *
                    of p (polyUnit r hr)) := by
                rw [mul_assoc, of_mul_anticomm hp hp2 (polyUnit r hr) (polyUnit π₃.poly hc),
                  mk_mul_neg, ← mul_assoc]
              rw [this]
              exact h_eq_neg _ (h2_left π π₃ hπ h3 r hr hrdeg)
            exact h_eq_sub _ _ (hswap π₁ h1) (hswap π₂ h2)
      -- Helper: every nonzero polynomial of degree ≤ d + 1 is a product of (deg ≤ d or monic irred deg d+1)
      have hfactor : ∀ (f : Polynomial E) (hf : f ≠ 0), f.natDegree ≤ d + 1 →
          (f.natDegree ≤ d ∨ ∃ π : MonicIrred E, π.poly = f ∧ π.poly.natDegree = d + 1) ∨
          (∃ (g₁ g₂ : Polynomial E) (hg₁ : g₁ ≠ 0) (hg₂ : g₂ ≠ 0),
            f = g₁ * g₂ ∧ g₁.natDegree ≤ d ∧
            (g₂.natDegree ≤ d ∨ ∃ π : MonicIrred E, π.poly = g₂ ∧ π.poly.natDegree = d + 1)) := by
        intro f hf hdf
        by_cases hle : f.natDegree ≤ d
        · exact Or.inl (Or.inl hle)
        have heq : f.natDegree = d + 1 := by omega
        have hlc : f.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hf
        set g := f * C f.leadingCoeff⁻¹
        have hg_monic : g.Monic := Polynomial.monic_mul_leadingCoeff_inv hf
        have hg_ne : g ≠ 0 := hg_monic.ne_zero
        have hg_deg : g.natDegree = d + 1 := by
          rw [show g = C f.leadingCoeff⁻¹ * f from mul_comm _ _,
            Polynomial.natDegree_C_mul (inv_ne_zero hlc), heq]
        have hfg : f = C f.leadingCoeff * g := by
          simp only [g]
          rw [mul_left_comm, ← map_mul, mul_inv_cancel₀ hlc, map_one, mul_one]
        by_cases hirr : Irreducible g
        · exact Or.inr ⟨C f.leadingCoeff, g, C_ne_zero.mpr hlc, hg_ne, hfg,
            by simp, Or.inr ⟨⟨g, hg_monic, hirr⟩, rfl, hg_deg⟩⟩
        · have hnotu : ¬ IsUnit g := by
            intro hu
            have := Polynomial.natDegree_eq_zero_of_isUnit hu
            omega
          obtain ⟨a, b, hab, ha_nu, hb_nu⟩ := exists_mul_of_not_irreducible hnotu hirr
          have ha0 : a ≠ 0 := left_ne_zero_of_mul (hab ▸ hg_ne)
          have hb0 : b ≠ 0 := right_ne_zero_of_mul (hab ▸ hg_ne)
          have ha_pos : 0 < a.natDegree := by
            by_contra h
            have h0 : a.natDegree = 0 := by omega
            have := Polynomial.eq_C_of_natDegree_eq_zero h0
            apply ha_nu; rw [this]
            exact Polynomial.isUnit_C.mpr (IsUnit.mk0 _ (by intro hc; apply ha0; rw [this, hc, map_zero]))
          have hb_pos : 0 < b.natDegree := by
            by_contra h
            have h0 : b.natDegree = 0 := by omega
            have := Polynomial.eq_C_of_natDegree_eq_zero h0
            apply hb_nu; rw [this]
            exact Polynomial.isUnit_C.mpr (IsUnit.mk0 _ (by intro hc; apply hb0; rw [this, hc, map_zero]))
          have hsum : a.natDegree + b.natDegree = d + 1 := by
            rw [← hg_deg, hab, Polynomial.natDegree_mul ha0 hb0]
          refine Or.inr ⟨C f.leadingCoeff * a, b, mul_ne_zero (C_ne_zero.mpr hlc) ha0, hb0, ?_, ?_, Or.inl (by omega)⟩
          · calc f = C f.leadingCoeff * g := hfg
              _ = C f.leadingCoeff * (a * b) := by rw [hab]
              _ = C f.leadingCoeff * a * b := (mul_assoc _ _ _).symm
          · rw [Polynomial.natDegree_C_mul hlc]; omega
      -- Now induct on `y ∈ Lfilt E p (d + 1)`
      intro y hy
      refine AddSubgroup.closure_induction ?_ ?_ ?_ ?_ hy
      · rintro _ ⟨f₁, f₂, f₃, h₁, h₂, h₃, hd₁, hd₂, hd₃, rfl⟩
        -- Expand each `fᵢ` using `hfactor`
        have hexp1 : ∀ (a b c : Polynomial E) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0),
            (a.natDegree ≤ d ∨ ∃ π : MonicIrred E, π.poly = a ∧ π.poly.natDegree = d + 1) →
            (b.natDegree ≤ d ∨ ∃ π : MonicIrred E, π.poly = b ∧ π.poly.natDegree = d + 1) →
            c.natDegree ≤ d + 1 →
            q (of p (polyUnit a ha) * of p (polyUnit b hb) * of p (polyUnit c hc)) =
            S (of p (polyUnit a ha) * of p (polyUnit b hb) * of p (polyUnit c hc)) := by
          intro a b c ha hb hc ha' hb' hdc
          rcases hfactor c hc hdc with hc' | ⟨g₁, g₂, hg₁, hg₂, rfl, hdg₁, hg₂'⟩
          · exact h_base a b c ha hb hc ha' hb' hc'
          · rw [polyUnit_mul g₁ g₂ hg₁ hg₂, of_mul, mul_add]
            exact h_eq_ker _ _ (h_base a b g₁ ha hb hg₁ ha' hb' (Or.inl hdg₁))
              (h_base a b g₂ ha hb hg₂ ha' hb' hg₂')
        have hexp2 : ∀ (a b c : Polynomial E) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0),
            (a.natDegree ≤ d ∨ ∃ π : MonicIrred E, π.poly = a ∧ π.poly.natDegree = d + 1) →
            b.natDegree ≤ d + 1 → c.natDegree ≤ d + 1 →
            q (of p (polyUnit a ha) * of p (polyUnit b hb) * of p (polyUnit c hc)) =
            S (of p (polyUnit a ha) * of p (polyUnit b hb) * of p (polyUnit c hc)) := by
          intro a b c ha hb hc ha' hdb hdc
          rcases hfactor b hb hdb with hb' | ⟨g₁, g₂, hg₁, hg₂, rfl, hdg₁, hg₂'⟩
          · exact hexp1 a b c ha hb hc ha' hb' hdc
          · rw [polyUnit_mul g₁ g₂ hg₁ hg₂, of_mul, mul_add, add_mul]
            exact h_eq_ker _ _ (hexp1 a g₁ c ha hg₁ hc ha' (Or.inl hdg₁) hdc)
              (hexp1 a g₂ c ha hg₂ hc ha' hg₂' hdc)
        rcases hfactor f₁ h₁ hd₁ with hf₁' | ⟨g₁, g₂, hg₁, hg₂, rfl, hdg₁, hg₂'⟩
        · exact hexp2 f₁ f₂ f₃ h₁ h₂ h₃ hf₁' hd₂ hd₃
        · rw [polyUnit_mul g₁ g₂ hg₁ hg₂, of_mul, add_mul, add_mul]
          exact h_eq_ker _ _ (hexp2 g₁ f₂ f₃ hg₁ h₂ h₃ (Or.inl hdg₁) hd₂ hd₃)
            (hexp2 g₂ f₂ f₃ hg₂ h₂ h₃ hg₂' hd₂ hd₃)
      · rw [map_zero, map_zero]
      · intro a b _ _ ha hb; rw [map_add, map_add, ha, hb]
      · intro a _ ha; rw [map_neg, map_neg, ha]
    have hqx : q x = 0 := by
      rw [hqS x hxD]
      simp only [S, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
      rw [finsum_eq_zero_of_forall_eq_zero]
      rintro ⟨π, hdeg⟩
      letI : Fact (Irreducible π.poly) := ⟨π.irred⟩
      rw [hvan π, map_zero]
    rw [show q = QuotientAddGroup.mk' (Lfilt E p d) from rfl, QuotientAddGroup.mk'_apply,
      QuotientAddGroup.eq_zero_iff] at hqx
    exact hqx

/-- Every element of `L_0` has `∂_∞ x = 0`. -/
theorem partialInfty_eq_zero_of_mem_Lfilt_zero {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {x : MilnorK (RatFunc E) p} (hx : x ∈ Lfilt E p 0) :
    (valInftyData E).partialHom hp hp2 x = 0 := by
  refine AddSubgroup.closure_induction ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨f₁, f₂, f₃, h₁, h₂, h₃, hd₁, hd₂, hd₃, rfl⟩
    have hv1 := (valInftyData_polyUnit f₁ h₁).1
    have hv2 := (valInftyData_polyUnit f₂ h₂).1
    have hv3 := (valInftyData_polyUnit f₃ h₃).1
    have h01 : f₁.natDegree = 0 := by omega
    have h02 : f₂.natDegree = 0 := by omega
    have h03 : f₃.natDegree = 0 := by omega
    simp only [h01, h02, h03, Nat.cast_zero, neg_zero] at hv1 hv2 hv3
    simp [DiscreteValData.partialHom, hv1, hv2, hv3]
  · exact map_zero _
  · intro a b _ _ ha hb; rw [map_add, ha, hb, add_zero]
  · intro a _ ha; rw [map_neg, ha, neg_zero]

end MilnorGradeThree

section NormSymbolVanishing

variable {E : Type*} [Field E] [CharZero E]

/-- Norm-symbol vanishing: for an odd prime `p`, `b ∈ Eˣ` with `X^p - C b` irreducible,
and any `z ∈ (AdjoinRoot (X^p - C b))ˣ`, we have `{b} * {N_{L/E}(z)} = 0` in `MilnorK E p`. -/
theorem of_mul_norm_eq_zero {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (b : Eˣ) (hirr : Irreducible (X ^ p - C (b : E)))
    (z : letI : Fact (Irreducible (X ^ p - C (b : E))) := ⟨hirr⟩
         (AdjoinRoot (X ^ p - C (b : E)))ˣ) :
    letI : Fact (Irreducible (X ^ p - C (b : E))) := ⟨hirr⟩
    of p b * of p (Units.map (Algebra.norm E : AdjoinRoot (X ^ p - C (b : E)) →* E) z) = 0 := by
  letI : Fact (Irreducible (X ^ p - C (b : E))) := ⟨hirr⟩
  have hmon : (X ^ p - C (b : E)).Monic :=
    Polynomial.monic_X_pow_sub_C (b : E) hp.ne_zero
  let π : MonicIrred E := ⟨X ^ p - C (b : E), hmon, hirr⟩
  obtain ⟨zTilde, hzTilde_mem, hzTilde_pi, hzTilde_other⟩ :=
    exists_grade2_lift (E := E) hp hp2 π.poly.natDegree π rfl z
  -- By Weil reciprocity on `zTilde`, `∂_∞ zTilde = - of p (N z)`
  have hweil := weilSum_grade_two (E := E) hp hp2 hzTilde_mem
  have hsum : (∑ᶠ π' : MonicIrred E,
      (letI : Fact (Irreducible π'.poly) := ⟨π'.irred⟩
       normK1 π' hp ((valPiData π').partialHom hp hp2 zTilde))) =
      of p (Units.map (Algebra.norm E : AdjoinRoot π.poly →* E) z) := by
    rw [finsum_eq_single _ π]
    · rw [hzTilde_pi, normK1_of]
    · intro π' hne
      letI : Fact (Irreducible π'.poly) := ⟨π'.irred⟩
      rw [hzTilde_other π' hne, map_zero]
  simp only [weilSum, AddMonoidHom.coe_mk, ZeroHom.coe_mk, hsum] at hweil
  have hinf_z : (valInftyData E).partialHom hp hp2 zTilde =
      -of p (Units.map (Algebra.norm E : AdjoinRoot π.poly →* E) z) :=
    eq_neg_of_add_eq_zero_right hweil
  -- Form `xTilde = of p (C b) * zTilde ∈ grade (RatFunc E) p 3`
  set cb := polyUnit (C (b : E)) (C_ne_zero.mpr b.ne_zero)
  set xTilde := of p cb * zTilde
  have hxTilde_mem : xTilde ∈ grade (RatFunc E) p 3 := by
    suffices ∀ w ∈ grade (RatFunc E) p 2, of p cb * w ∈ grade (RatFunc E) p 3 from
      this zTilde hzTilde_mem
    intro w hw
    refine AddSubgroup.closure_induction ?_ ?_ ?_ ?_ hw
    · rintro _ ⟨s, rfl⟩
      have : of p cb * symbol p s = symbol p (Fin.cons cb s) := by
        symm
        rw [symbol_succ]
        simp only [Fin.cons_zero, Fin.cons_succ]
      rw [this]
      exact symbol_mem_grade _ _ _
    · simp
    · intro u v _ _ hu hv; rw [mul_add]; exact (grade _ p 3).add_mem hu hv
    · intro u _ hu; rw [mk_mul_neg]; exact (grade _ p 3).neg_mem hu
  -- Every finite residue `∂_{π'} xTilde` vanishes!
  have hvan : ∀ π' : MonicIrred E,
      letI : Fact (Irreducible π'.poly) := ⟨π'.irred⟩
      (valPiData π').partialHom hp hp2 xTilde = 0 := by
    intro π'
    letI : Fact (Irreducible π'.poly) := ⟨π'.irred⟩
    have hnd : ¬ π'.poly ∣ C (b : E) := fun h =>
      π'.irred.not_isUnit (isUnit_of_dvd_unit h (Polynomial.isUnit_C.mpr (IsUnit.mk0 (b : E) b.ne_zero)))
    have hcb := valPiData_polyUnit_not_dvd π' (C (b : E)) (C_ne_zero.mpr b.ne_zero) hnd
    rw [show xTilde = of p cb * zTilde from rfl,
      (valPiData π').partialHom_of_mul_of_val_zero hp hp2 cb hcb.1 zTilde]
    by_cases heq : π' = π
    · subst heq
      -- In `L = AdjoinRoot (X^p - C b)`, `b = (root π)^p`, so `of p b = 0`!
      have hroot_ne : AdjoinRoot.root π.poly ≠ 0 := by
        intro h0
        have hev := AdjoinRoot.eval₂_root π.poly
        simp only [π, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C,
          h0, zero_pow hp.ne_zero, zero_sub, neg_eq_zero] at hev
        have hinj := (algebraMap E (AdjoinRoot π.poly)).injective
        exact b.ne_zero ((map_eq_zero_iff _ hinj).mp hev)
      have hpow : (valPiData π).res cb = (Units.mk0 (AdjoinRoot.root π.poly) hroot_ne) ^ p := by
        apply Units.ext
        rw [hcb.2]
        have hev := AdjoinRoot.eval₂_root π.poly
        simp only [π, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C] at hev
        have h1 : AdjoinRoot.mk π.poly (C (b : E)) = AdjoinRoot.root π.poly ^ p := by
          change algebraMap E (AdjoinRoot π.poly) (b : E) = _
          exact (sub_eq_zero.mp hev).symm
        simpa using h1
      rw [hpow, of_pow_p, zero_mul]
    · rw [hzTilde_other π' heq, mul_zero]
  -- By Milnor's Theorem 2.3 in degree 3, `xTilde ∈ L_0`, so `∂_∞ xTilde = 0`!
  have hxL0 : xTilde ∈ Lfilt E p 0 := milnor_grade3_ker hp hp2 hxTilde_mem hvan
  have hinf_x := partialInfty_eq_zero_of_mem_Lfilt_zero hp hp2 hxL0
  have hcb_inf := valInftyData_polyUnit (C (b : E)) (C_ne_zero.mpr b.ne_zero)
  have hcb_val : (valInftyData E).val (Additive.ofMul cb) = 0 := by
    simpa using hcb_inf.1
  have hcb_res : (valInftyData E).res cb = b := by
    apply Units.ext
    simpa using hcb_inf.2
  rw [show xTilde = of p cb * zTilde from rfl,
    (valInftyData E).partialHom_of_mul_of_val_zero hp hp2 cb hcb_val zTilde,
    hcb_res, hinf_z, mk_mul_neg, neg_eq_zero] at hinf_x
  exact hinf_x

end NormSymbolVanishing

section TsenAndFinal

/-- Kummer reducibility: if `E` is an algebra over `ℂ` and `X^p - C b` is reducible over `E`
for a prime `p`, then `b` is a `p`-th power in `Eˣ`. -/
theorem exists_pow_p_of_not_irreducible {E : Type*} [Field E] [Algebra ℂ E]
    {p : ℕ} (hp : p.Prime) (b : Eˣ) (hred : ¬ Irreducible (X ^ p - C (b : E))) :
    ∃ c : Eˣ, c ^ p = b := by
  set f : Polynomial E := X ^ p - C (b : E)
  have hf_monic : f.Monic := Polynomial.monic_X_pow_sub_C (b : E) hp.ne_zero
  have hf_deg : f.natDegree = p := Polynomial.natDegree_X_pow_sub_C
  have hf_ne : f ≠ 0 := hf_monic.ne_zero
  have hf_nu : ¬ IsUnit f := by
    intro hu
    have := Polynomial.natDegree_eq_zero_of_isUnit hu
    have := hp.one_lt
    omega
  obtain ⟨g, h, hgh, hg_nu, hh_nu⟩ := exists_mul_of_not_irreducible hf_nu hred
  have hg0 : g ≠ 0 := left_ne_zero_of_mul (hgh ▸ hf_ne)
  have hh0 : h ≠ 0 := right_ne_zero_of_mul (hgh ▸ hf_ne)
  have hg_pos : 0 < g.natDegree := by
    by_contra h0
    have hz : g.natDegree = 0 := by omega
    have hC := Polynomial.eq_C_of_natDegree_eq_zero hz
    apply hg_nu; rw [hC]
    exact Polynomial.isUnit_C.mpr (IsUnit.mk0 _ (by intro hc; apply hg0; rw [hC, hc, map_zero]))
  have hh_pos : 0 < h.natDegree := by
    by_contra h0
    have hz : h.natDegree = 0 := by omega
    have hC := Polynomial.eq_C_of_natDegree_eq_zero hz
    apply hh_nu; rw [hC]
    exact Polynomial.isUnit_C.mpr (IsUnit.mk0 _ (by intro hc; apply hh0; rw [hC, hc, map_zero]))
  have hsum : g.natDegree + h.natDegree = p := by
    rw [← hf_deg, hgh, Polynomial.natDegree_mul hg0 hh0]
  -- Normalize `g` to be monic
  set g1 := g * C g.leadingCoeff⁻¹
  have hg1_monic : g1.Monic := Polynomial.monic_mul_leadingCoeff_inv hg0
  have hg1_deg : g1.natDegree = g.natDegree := by
    rw [show g1 = C g.leadingCoeff⁻¹ * g from mul_comm _ _,
      Polynomial.natDegree_C_mul (inv_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hg0))]
  have hg1_dvd : g1 ∣ f := ⟨C g.leadingCoeff * h, by
    rw [hgh]
    simp only [g1]
    rw [mul_assoc g, ← mul_assoc (C g.leadingCoeff⁻¹), ← map_mul,
      inv_mul_cancel₀ (Polynomial.leadingCoeff_ne_zero.mpr hg0), map_one, one_mul]⟩
  -- Pass to `Ebar = AlgebraicClosure E`
  set Ebar := AlgebraicClosure E
  set ι : E →+* Ebar := algebraMap E Ebar
  have hsp : (g1.map ι).Splits := IsAlgClosed.splits _
  have hfac := hsp.eq_prod_roots_of_monic (hg1_monic.map ι)
  have hcard : (g1.map ι).roots.card = g.natDegree := by
    rw [← hsp.natDegree_eq_card_roots,
      Polynomial.natDegree_map_eq_of_injective ι.injective, hg1_deg]
  -- Every root `α` of `g1.map ι` satisfies `α^p = ι b`
  have hroot_pow : ∀ α ∈ (g1.map ι).roots, α ^ p = ι (b : E) := by
    intro α hα
    have h1 : (g1.map ι).eval α = 0 :=
      (Polynomial.mem_roots (Polynomial.map_ne_zero hg1_monic.ne_zero)).mp hα
    have hdvd_map : g1.map ι ∣ f.map ι := Polynomial.map_dvd ι hg1_dvd
    obtain ⟨q, hq⟩ := hdvd_map
    have h2 : (f.map ι).eval α = 0 := by rw [hq, Polynomial.eval_mul, h1, zero_mul]
    simp only [f, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C,
      Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C] at h2
    exact sub_eq_zero.mp h2
  -- Evaluate `g1` at `0`: `ι (g1.coeff 0) = (-1)^m * ∏ α ∈ roots, α`, so `(g1.coeff 0)^p = (±1)^p * b^m`
  have hconst : (g1.coeff 0) ^ p = ((-1 : E) ^ g.natDegree) ^ p * (b : E) ^ g.natDegree := by
    apply ι.injective
    have hev0 : ι (g1.coeff 0) = (g1.map ι).eval 0 := by
      rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_map]
    have hprod_pow : ∀ (s : Multiset Ebar), s.prod ^ p = (s.map (· ^ p)).prod := fun s =>
      Multiset.induction_on s (by simp) (fun a s ih => by simp [mul_pow, ih])
    rw [map_pow, hev0, hfac, Polynomial.eval_multiset_prod, Multiset.map_map]
    simp only [Function.comp_def, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, zero_sub]
    rw [hprod_pow, Multiset.map_map]
    have hmap : ((g1.map ι).roots.map ((fun x : Ebar => x ^ p) ∘ fun x => -x)) =
        Multiset.replicate g.natDegree ((-1 : Ebar) ^ p * ι (b : E)) := by
      refine Multiset.eq_replicate.mpr ⟨by simp [hcard], fun y hy => ?_⟩
      rcases Multiset.mem_map.mp hy with ⟨α, hα, rfl⟩
      simp only [Function.comp_def]
      rw [neg_eq_neg_one_mul, mul_pow, hroot_pow α hα]
    rw [hmap, Multiset.prod_replicate, mul_pow, ← pow_mul, mul_comm p g.natDegree, pow_mul]
    simp only [map_mul, map_pow, map_neg, map_one]
  set c0 := (-1 : E) ^ g.natDegree * g1.coeff 0
  have hc0_pow : c0 ^ p = (b : E) ^ g.natDegree := by
    rw [mul_pow, hconst, ← mul_assoc, ← mul_pow, ← pow_add,
      show g.natDegree + g.natDegree = 2 * g.natDegree by omega, pow_mul, neg_one_sq, one_pow,
      one_pow, one_mul]
  have hc0_ne : c0 ≠ 0 := by
    intro h0
    rw [h0, zero_pow hp.ne_zero] at hc0_pow
    exact (pow_ne_zero g.natDegree b.ne_zero) hc0_pow.symm
  have hcop : Nat.Coprime g.natDegree p := by
    refine (hp.coprime_iff_not_dvd.mpr ?_).symm
    intro hdvd
    have hle := Nat.le_of_dvd hg_pos hdvd
    omega
  set u := Nat.gcdA g.natDegree p
  set v := Nat.gcdB g.natDegree p
  have hbez : (g.natDegree : ℤ) * u + (p : ℤ) * v = 1 := by
    have h := Nat.gcd_eq_gcd_ab g.natDegree p
    rw [hcop.gcd_eq_one, Nat.cast_one] at h
    exact h.symm
  set cU : Eˣ := (Units.mk0 c0 hc0_ne) ^ u * b ^ v
  refine ⟨cU, ?_⟩
  have hc0_u : (Units.mk0 c0 hc0_ne) ^ p = b ^ g.natDegree := by
    apply Units.ext
    simpa using hc0_pow
  calc cU ^ p = ((Units.mk0 c0 hc0_ne) ^ u) ^ p * (b ^ v) ^ p := mul_pow _ _ _
    _ = ((Units.mk0 c0 hc0_ne) ^ p) ^ u * b ^ (v * (p : ℤ)) := by
        congr 1
        · rw [← zpow_natCast, ← zpow_mul, mul_comm u (p : ℤ), zpow_mul, zpow_natCast]
        · rw [← zpow_natCast, ← zpow_mul]
    _ = (b ^ g.natDegree) ^ u * b ^ (v * (p : ℤ)) := by rw [hc0_u]
    _ = b ^ ((g.natDegree : ℤ) * u + (p : ℤ) * v) := by
        rw [← zpow_natCast, ← zpow_mul, mul_comm v (p : ℤ), ← zpow_add]
    _ = b := by rw [hbez, zpow_one]

/-- Exact norm formula for `L = AdjoinRoot (X^p - C b)` as a `p × p` determinant. -/
theorem norm_adjoinRoot_X_pow_sub_C {E : Type*} [Field E] {p : ℕ} (hp : p.Prime)
    (b : E) (hirr : Irreducible (X ^ p - C b)) (c : Fin p → E) :
    letI : Fact (Irreducible (X ^ p - C b)) := ⟨hirr⟩
    Algebra.norm E (∑ j : Fin p, c j • (AdjoinRoot.root (X ^ p - C b)) ^ (j : ℕ)) =
      Matrix.det (Matrix.of fun i j : Fin p =>
        if h : (j : ℕ) ≤ (i : ℕ) then c ⟨(i : ℕ) - (j : ℕ), by omega⟩
        else b * c ⟨p + (i : ℕ) - (j : ℕ), by omega⟩) := by
  letI : Fact (Irreducible (X ^ p - C b)) := ⟨hirr⟩
  set π := X ^ p - C b
  have hπ0 : π ≠ 0 := hirr.ne_zero
  set pb := AdjoinRoot.powerBasis hπ0
  have hdim : pb.dim = p := by
    rw [AdjoinRoot.powerBasis_dim, Polynomial.natDegree_X_pow_sub_C]
  set β := AdjoinRoot.root π
  have hβp : β ^ p = algebraMap E (AdjoinRoot π) b := by
    have hev := AdjoinRoot.eval₂_root π
    simp only [π, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C] at hev
    exact sub_eq_zero.mp hev
  let e : Fin pb.dim ≃ Fin p := finCongr hdim
  let bas : Module.Basis (Fin p) E (AdjoinRoot π) := pb.basis.reindex e
  have hbas : ∀ j : Fin p, bas j = β ^ (j : ℕ) := by
    intro j
    simp [bas, pb, e, PowerBasis.basis_eq_pow, AdjoinRoot.powerBasis_gen, β]
  set z : AdjoinRoot π := ∑ j : Fin p, c j • β ^ (j : ℕ)
  rw [Algebra.norm_apply, ← LinearMap.det_toMatrix bas]
  congr 1
  ext i j
  rw [LinearMap.toMatrix_apply]
  change bas.repr (z * bas j) i = _
  rw [hbas j]
  have hmul : z * β ^ (j : ℕ) =
      ∑ r : Fin p, (if h : (j : ℕ) ≤ (r : ℕ) then c ⟨(r : ℕ) - (j : ℕ), by omega⟩
        else b * c ⟨p + (r : ℕ) - (j : ℕ), by omega⟩) • bas r := by
    simp only [z, Finset.sum_mul, smul_mul_assoc, ← pow_add, hbas]
    -- Reindex `k : Fin p` to `r = (k + j) % p : Fin p`
    let f : Fin p ≃ Fin p :=
      { toFun := fun k => ⟨((k : ℕ) + (j : ℕ)) % p, Nat.mod_lt _ hp.pos⟩
        invFun := fun r =>
          if h : (j : ℕ) ≤ (r : ℕ) then ⟨(r : ℕ) - (j : ℕ), by omega⟩
          else ⟨p + (r : ℕ) - (j : ℕ), by omega⟩
        left_inv := fun k => by
          ext
          dsimp
          split_ifs with h
          · change ((k : ℕ) + (j : ℕ)) % p - (j : ℕ) = (k : ℕ)
            have hlt : (k : ℕ) + (j : ℕ) < p := by
              by_contra hge
              have : ((k : ℕ) + (j : ℕ)) % p = (k : ℕ) + (j : ℕ) - p := by
                rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
              omega
            rw [Nat.mod_eq_of_lt hlt]; omega
          · change p + ((k : ℕ) + (j : ℕ)) % p - (j : ℕ) = (k : ℕ)
            have hge : p ≤ (k : ℕ) + (j : ℕ) := by
              by_contra hlt
              rw [Nat.mod_eq_of_lt (by omega)] at h
              omega
            rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)]
            omega
        right_inv := fun r => by
          ext
          dsimp
          split_ifs with h
          · rw [Nat.sub_add_cancel h, Nat.mod_eq_of_lt r.isLt]
          · have : p + (r : ℕ) - (j : ℕ) + (j : ℕ) = p + (r : ℕ) := by omega
            rw [this, Nat.add_mod_left, Nat.mod_eq_of_lt r.isLt] }
    refine Fintype.sum_equiv f _ _ (fun k => ?_)
    dsimp [f]
    split_ifs with h
    · have hklt := k.isLt
      have hjlt := j.isLt
      have hlt : (k : ℕ) + (j : ℕ) < p := by
        by_contra hge
        have : ((k : ℕ) + (j : ℕ)) % p = (k : ℕ) + (j : ℕ) - p := by
          rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
        omega
      have hmod_lt : ((k : ℕ) + (j : ℕ)) % p < p := Nat.mod_lt _ hp.pos
      have hk : (⟨((k : ℕ) + (j : ℕ)) % p - (j : ℕ), by omega⟩ : Fin p) = k := by
        ext; change ((k : ℕ) + (j : ℕ)) % p - (j : ℕ) = (k : ℕ)
        rw [Nat.mod_eq_of_lt hlt]; omega
      rw [hk, Nat.mod_eq_of_lt hlt]
    · have hklt := k.isLt
      have hjlt := j.isLt
      have hge : p ≤ (k : ℕ) + (j : ℕ) := by
        by_contra hlt
        rw [Nat.mod_eq_of_lt (by omega)] at h
        omega
      have hmod : ((k : ℕ) + (j : ℕ)) % p = (k : ℕ) + (j : ℕ) - p := by
        rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)]
      have hk : (⟨p + ((k : ℕ) + (j : ℕ)) % p - (j : ℕ), by omega⟩ : Fin p) = k := by
        ext; change p + ((k : ℕ) + (j : ℕ)) % p - (j : ℕ) = (k : ℕ); omega
      rw [hk, hmod]
      simp only [Algebra.smul_def, map_mul]
      rw [← hβp, mul_comm (β ^ p), mul_assoc, ← pow_add,
        show p + ((k : ℕ) + (j : ℕ) - p) = (k : ℕ) + (j : ℕ) by omega]
  rw [hmul, map_sum]
  simp only [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply,
    Finset.sum_apply', smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]
  rfl

/-- Generic `(n + 1)`-fold right-associated product under a binary operation `star`. -/
def foldStar {α : Type*} (star : α → α → α) : (n : ℕ) → (Fin (n + 1) → α) → α
  | 0, f => f 0
  | n + 1, f => star (f 0) (foldStar star n (fun i => f i.succ))

/-- Given a nontrivial solution `(c, w)` to `det M(c) = a * w^p` over an abstract field `E`
with `X^p - C b` irreducible, conclude `a` is a norm from `AdjoinRoot (X^p - C b)`. -/
private theorem tsen_norm_from_det {E : Type*} [Field E] {p : ℕ} (hp : p.Prime)
    (a b : Eˣ) (hirr : Irreducible (X ^ p - C (b : E)))
    (c : Fin p → E) (w : E)
    (hnorm_eq : Matrix.det (Matrix.of fun i j : Fin p =>
        if h : (j : ℕ) ≤ (i : ℕ) then c ⟨(i : ℕ) - (j : ℕ), by omega⟩
        else (b : E) * c ⟨p + (i : ℕ) - (j : ℕ), by omega⟩) = (a : E) * w ^ p)
    (hcw_nz : (∃ j : Fin p, c j ≠ 0) ∨ w ≠ 0) :
    letI : Fact (Irreducible (X ^ p - C (b : E))) := ⟨hirr⟩
    ∃ z : (AdjoinRoot (X ^ p - C (b : E)))ˣ,
      Algebra.norm E (z : AdjoinRoot (X ^ p - C (b : E))) = (a : E) := by
  letI : Fact (Irreducible (X ^ p - C (b : E))) := ⟨hirr⟩
  set zL : AdjoinRoot (X ^ p - C (b : E)) :=
    ∑ j : Fin p, c j • (AdjoinRoot.root (X ^ p - C (b : E))) ^ (j : ℕ)
  have hNz : Algebra.norm E zL = (a : E) * w ^ p := by
    rw [norm_adjoinRoot_X_pow_sub_C hp (b : E) hirr c, hnorm_eq]
  haveI : Module.Finite E (AdjoinRoot (X ^ p - C (b : E))) :=
    PowerBasis.finite (AdjoinRoot.powerBasis hirr.ne_zero)
  have hw_nz : w ≠ 0 := by
    intro hw0
    rw [hw0, zero_pow hp.ne_zero, mul_zero] at hNz
    have hzL0 : zL = 0 := (Algebra.norm_eq_zero_iff (R := E)).mp hNz
    rcases hcw_nz with ⟨j, hcj⟩ | hw'
    · apply hcj
      set pbL := AdjoinRoot.powerBasis hirr.ne_zero
      have hdimL : pbL.dim = p := by
        rw [AdjoinRoot.powerBasis_dim, Polynomial.natDegree_X_pow_sub_C]
      let basL := pbL.basis.reindex (finCongr hdimL)
      have hzL' : ∑ r : Fin p, c r • basL r = 0 := by
        convert hzL0 using 1
        refine Finset.sum_congr rfl fun r _ => ?_
        simp [basL, pbL, AdjoinRoot.powerBasis_gen]
      have := congrArg (fun x => basL.repr x j) hzL'
      simp only [map_sum, map_smul, Module.Basis.repr_self, Finsupp.smul_apply,
        Finsupp.single_apply, Finset.sum_apply', smul_eq_mul, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, ite_true, map_zero, Finsupp.zero_apply] at this
      exact this
    · exact hw' hw0
  set zFinal : AdjoinRoot (X ^ p - C (b : E)) := w⁻¹ • zL
  have hNfinal : Algebra.norm E zFinal = (a : E) := by
    rw [show zFinal = algebraMap E _ w⁻¹ * zL from Algebra.smul_def _ _, map_mul,
      Algebra.norm_algebraMap, hNz]
    have hfr : Module.finrank E (AdjoinRoot (X ^ p - C (b : E))) = p := by
      rw [Module.finrank_eq_card_basis (AdjoinRoot.powerBasis hirr.ne_zero).basis,
        Fintype.card_fin, AdjoinRoot.powerBasis_dim, Polynomial.natDegree_X_pow_sub_C]
    rw [hfr, inv_pow, mul_comm ((w : E) ^ p)⁻¹, mul_assoc,
      mul_inv_cancel₀ (pow_ne_zero p hw_nz), mul_one]
  have hzFinal_nz : zFinal ≠ 0 := by
    intro h0
    rw [h0, Algebra.norm_zero] at hNfinal
    exact a.ne_zero hNfinal.symm
  exact ⟨Units.mk0 zFinal hzFinal_nz, hNfinal⟩

/-- Tsen's theorem for a finite extension `E = AdjoinRoot π` of `RatFunc ℂ`:
if `X^p - C b` is irreducible over `E`, then `Algebra.norm E : Lˣ → Eˣ` is surjective. -/
theorem tsen_norm_surj {p : ℕ} (hp : p.Prime)
    (π : MonicIrred (RatFunc ℂ))
    (a b : letI : Fact (Irreducible π.poly) := ⟨π.irred⟩; (AdjoinRoot π.poly)ˣ)
    (hirr : letI : Fact (Irreducible π.poly) := ⟨π.irred⟩
            Irreducible (X ^ p - C (b : AdjoinRoot π.poly))) :
    letI : Fact (Irreducible π.poly) := ⟨π.irred⟩
    letI : Fact (Irreducible (X ^ p - C (b : AdjoinRoot π.poly))) := ⟨hirr⟩
    ∃ z : (AdjoinRoot (X ^ p - C (b : AdjoinRoot π.poly)))ˣ,
      Algebra.norm (AdjoinRoot π.poly) (z : AdjoinRoot (X ^ p - C (b : AdjoinRoot π.poly))) =
        (a : AdjoinRoot π.poly) := by
  classical
  letI : Fact (Irreducible π.poly) := ⟨π.irred⟩
  letI : Fact (Irreducible (X ^ p - C (b : AdjoinRoot π.poly))) := ⟨hirr⟩
  set E := AdjoinRoot π.poly
  set pb := AdjoinRoot.powerBasis π.ne_zero
  set k := pb.dim
  have hk_pos : 0 < k := by
    rw [show k = π.poly.natDegree from AdjoinRoot.powerBasis_dim π.ne_zero]
    exact π.natDegree_pos
  -- Clear denominators in `Polynomial ℂ` for structure constants, `a`, and `b`
  have hinj : Function.Injective (algebraMap (Polynomial ℂ) (RatFunc ℂ)) :=
    IsFractionRing.injective _ _
  let coord : E → Fin k → RatFunc ℂ := fun x m => pb.basis.repr x m
  -- Common denominator `q ∈ Polynomial ℂ` for all `coord (pb.basis r * pb.basis s) m`, `coord a m`, `coord b m`
  let allElts : Finset (RatFunc ℂ) :=
    (Finset.univ.image fun rsm : Fin k × Fin k × Fin k =>
      coord (pb.basis rsm.1 * pb.basis rsm.2.1) rsm.2.2) ∪
    (Finset.univ.image fun m : Fin k => coord (a : E) m) ∪
    (Finset.univ.image fun m : Fin k => coord (b : E) m)
  set q : Polynomial ℂ := ∏ x ∈ allElts, x.denom
  have hq0 : q ≠ 0 := Finset.prod_ne_zero_iff.mpr fun x _ => RatFunc.denom_ne_zero x
  have hq_mul : ∀ x ∈ allElts, ∃ f : Polynomial ℂ,
      algebraMap (Polynomial ℂ) (RatFunc ℂ) f =
        algebraMap (Polynomial ℂ) (RatFunc ℂ) q * x := by
    intro x hx
    set rest : Polynomial ℂ := ∏ y ∈ allElts.erase x, y.denom
    refine ⟨x.num * rest, ?_⟩
    have hq_split : q = x.denom * rest :=
      (Finset.mul_prod_erase allElts (fun y => y.denom) hx).symm
    have hd0 : algebraMap (Polynomial ℂ) (RatFunc ℂ) x.denom ≠ 0 :=
      (map_ne_zero_iff _ hinj).mpr (RatFunc.denom_ne_zero x)
    have hxnd : algebraMap (Polynomial ℂ) (RatFunc ℂ) x.denom * x =
        algebraMap (Polynomial ℂ) (RatFunc ℂ) x.num := by
      have h1 := RatFunc.num_div_denom x
      rw [div_eq_iff hd0] at h1
      rw [mul_comm, h1]
    calc algebraMap (Polynomial ℂ) (RatFunc ℂ) (x.num * rest)
        = algebraMap (Polynomial ℂ) (RatFunc ℂ) x.num * algebraMap _ _ rest := map_mul _ _ _
      _ = (algebraMap _ _ x.denom * x) * algebraMap _ _ rest := by rw [hxnd]
      _ = (algebraMap _ _ x.denom * algebraMap _ _ rest) * x := by ring
      _ = algebraMap (Polynomial ℂ) (RatFunc ℂ) q * x := by rw [← map_mul, ← hq_split]
  have hC_ex : ∀ r s m : Fin k, ∃ f : Polynomial ℂ,
      algebraMap (Polynomial ℂ) (RatFunc ℂ) f =
        algebraMap (Polynomial ℂ) (RatFunc ℂ) q * coord (pb.basis r * pb.basis s) m :=
    fun r s m => hq_mul _ (Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_image.mpr ⟨(r, s, m), Finset.mem_univ _, rfl⟩)))
  have ha_ex : ∀ m : Fin k, ∃ f : Polynomial ℂ,
      algebraMap (Polynomial ℂ) (RatFunc ℂ) f =
        algebraMap (Polynomial ℂ) (RatFunc ℂ) q * coord (a : E) m :=
    fun m => hq_mul _ (Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨m, Finset.mem_univ _, rfl⟩)))
  have hb_ex : ∀ m : Fin k, ∃ f : Polynomial ℂ,
      algebraMap (Polynomial ℂ) (RatFunc ℂ) f =
        algebraMap (Polynomial ℂ) (RatFunc ℂ) q * coord (b : E) m :=
    fun m => hq_mul _ (Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨m, Finset.mem_univ _, rfl⟩))
  choose Cpoly hCpoly using hC_ex
  choose apoly hapoly using ha_ex
  choose bpoly hbpoly using hb_ex
  -- Degree bound `B0` for `q`, `Cpoly`, `apoly`, `bpoly`
  set B0 : ℕ := q.natDegree +
    (∑ r : Fin k, ∑ s : Fin k, ∑ m : Fin k, (Cpoly r s m).natDegree) +
    (∑ m : Fin k, (apoly m).natDegree) +
    (∑ m : Fin k, (bpoly m).natDegree)
  have hq_deg : q.natDegree ≤ B0 := by omega
  have hC_deg : ∀ r s m : Fin k, (Cpoly r s m).natDegree ≤ B0 := by
    intro r s m
    have h1 : (Cpoly r s m).natDegree ≤ ∑ m' : Fin k, (Cpoly r s m').natDegree :=
      Finset.single_le_sum (f := fun m' : Fin k => (Cpoly r s m').natDegree)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ m)
    have h2 : (∑ m' : Fin k, (Cpoly r s m').natDegree) ≤
        ∑ s' : Fin k, ∑ m' : Fin k, (Cpoly r s' m').natDegree :=
      Finset.single_le_sum (f := fun s' : Fin k => ∑ m' : Fin k, (Cpoly r s' m').natDegree)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ s)
    have h3 : (∑ s' : Fin k, ∑ m' : Fin k, (Cpoly r s' m').natDegree) ≤
        ∑ r' : Fin k, ∑ s' : Fin k, ∑ m' : Fin k, (Cpoly r' s' m').natDegree :=
      Finset.single_le_sum
        (f := fun r' : Fin k => ∑ s' : Fin k, ∑ m' : Fin k, (Cpoly r' s' m').natDegree)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ r)
    omega
  have ha_deg : ∀ m : Fin k, (apoly m).natDegree ≤ B0 := by
    intro m
    have := Finset.single_le_sum (f := fun m' : Fin k => (apoly m').natDegree)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ m)
    omega
  have hb_deg : ∀ m : Fin k, (bpoly m).natDegree ≤ B0 := by
    intro m
    have := Finset.single_le_sum (f := fun m' : Fin k => (bpoly m').natDegree)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ m)
    omega
  set B : ℕ := 3 * p * B0 + 1
  set D : ℕ := B
  -- Unknowns `U = Fin (p + 1) × Fin k × Fin (D + 1)`
  let U := Fin (p + 1) × Fin k × Fin (D + 1)
  let A := MvPolynomial U ℂ
  let liftC : Polynomial ℂ →+* Polynomial A := Polynomial.mapRingHom MvPolynomial.C
  -- Scaled multiplication `⋆` on `Fin k → Polynomial A`
  let star : (Fin k → Polynomial A) → (Fin k → Polynomial A) → (Fin k → Polynomial A) :=
    fun v w m => ∑ r : Fin k, ∑ s : Fin k, liftC (Cpoly r s m) * v r * w s
  have hstar_deg : ∀ (v w : Fin k → Polynomial A) (dv dw : ℕ),
      (∀ m, (v m).natDegree ≤ dv) → (∀ m, (w m).natDegree ≤ dw) →
      ∀ m, (star v w m).natDegree ≤ B0 + dv + dw := by
    intro v w dv dw hv hw m
    refine (Polynomial.natDegree_sum_le _ _).trans (Finset.sup_le fun r _ => ?_)
    refine (Polynomial.natDegree_sum_le _ _).trans (Finset.sup_le fun s _ => ?_)
    refine (Polynomial.natDegree_mul_le).trans (add_le_add ?_ (hw s))
    refine (Polynomial.natDegree_mul_le).trans (add_le_add ?_ (hv r))
    exact Polynomial.natDegree_map_le.trans (hC_deg r s m)
  have hstar_eval : ∀ (t : U → ℂ) (v w : Fin k → Polynomial A),
      let ev : Polynomial A →+* RatFunc ℂ :=
        (algebraMap (Polynomial ℂ) (RatFunc ℂ)).comp (Polynomial.mapRingHom (MvPolynomial.eval t))
      let toE : (Fin k → Polynomial A) → E := fun u => ∑ m : Fin k, ev (u m) • pb.basis m
      toE (star v w) = algebraMap (Polynomial ℂ) (RatFunc ℂ) q • (toE v * toE w) := by
    intro t v w ev toE
    have hev_lift : ∀ f : Polynomial ℂ, ev (liftC f) = algebraMap (Polynomial ℂ) (RatFunc ℂ) f := by
      intro f
      simp only [ev, liftC, RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_map]
      have : (MvPolynomial.eval t).comp MvPolynomial.C = RingHom.id ℂ := by
        ext; simp
      rw [this, Polynomial.map_id]
    have hmul_basis : ∀ r s : Fin k,
        pb.basis r * pb.basis s = ∑ m : Fin k, coord (pb.basis r * pb.basis s) m • pb.basis m := by
      intro r s
      exact (pb.basis.sum_repr (pb.basis r * pb.basis s)).symm
    simp only [toE, star, map_sum, map_mul, hev_lift, hCpoly]
    calc ∑ m : Fin k, (∑ r : Fin k, ∑ s : Fin k,
            algebraMap (Polynomial ℂ) (RatFunc ℂ) q * coord (pb.basis r * pb.basis s) m *
              ev (v r) * ev (w s)) • pb.basis m
        = ∑ r : Fin k, ∑ s : Fin k,
            (algebraMap (Polynomial ℂ) (RatFunc ℂ) q * ev (v r) * ev (w s)) •
              (∑ m : Fin k, coord (pb.basis r * pb.basis s) m • pb.basis m) := by
            simp only [Finset.sum_smul, Finset.smul_sum, smul_smul]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun r _ => ?_
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun m _ => by
              congr 1; ring
      _ = algebraMap (Polynomial ℂ) (RatFunc ℂ) q •
            ((∑ r : Fin k, ev (v r) • pb.basis r) * (∑ s : Fin k, ev (w s) • pb.basis s)) := by
            simp_rw [← hmul_basis]
            rw [Finset.sum_mul, Finset.smul_sum]
            refine Finset.sum_congr rfl fun r _ => ?_
            rw [Finset.mul_sum, Finset.smul_sum]
            refine Finset.sum_congr rfl fun s _ => ?_
            simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
            congr 1; ring
  have hprodStar_deg : ∀ (n : ℕ) (f : Fin (n + 1) → (Fin k → Polynomial A)) (df : ℕ),
      (∀ i m, (f i m).natDegree ≤ df) →
      ∀ m, (foldStar star n f m).natDegree ≤ (n + 1) * df + n * B0 := by
    intro n
    induction n with
    | zero =>
      intro f df hf m
      simpa [foldStar] using hf 0 m
    | succ n ih =>
      intro f df hf m
      have h1 := hstar_deg (f 0) (foldStar star n (fun i => f i.succ)) df ((n + 1) * df + n * B0)
        (hf 0) (ih (fun i => f i.succ) df (fun i => hf i.succ)) m
      refine h1.trans ?_
      ring_nf
      omega
  have hprodStar_eval : ∀ (t : U → ℂ) (n : ℕ) (f : Fin (n + 1) → (Fin k → Polynomial A)),
      let ev : Polynomial A →+* RatFunc ℂ :=
        (algebraMap (Polynomial ℂ) (RatFunc ℂ)).comp (Polynomial.mapRingHom (MvPolynomial.eval t))
      let toE : (Fin k → Polynomial A) → E := fun u => ∑ m : Fin k, ev (u m) • pb.basis m
      toE (foldStar star n f) =
        (algebraMap (Polynomial ℂ) (RatFunc ℂ) q) ^ n • ∏ i : Fin (n + 1), toE (f i) := by
    intro t n
    induction n with
    | zero =>
      intro f
      simp [foldStar]
    | succ n ih =>
      intro f ev toE
      change toE (star (f 0) (foldStar star n (fun i => f i.succ))) = _
      have hst : toE (star (f 0) (foldStar star n (fun i => f i.succ))) =
          algebraMap (Polynomial ℂ) (RatFunc ℂ) q • (toE (f 0) * toE (foldStar star n (fun i => f i.succ))) :=
        hstar_eval t _ _
      have hih : toE (foldStar star n (fun i => f i.succ)) =
          (algebraMap (Polynomial ℂ) (RatFunc ℂ) q) ^ n • ∏ i : Fin (n + 1), toE (f i.succ) :=
        ih (fun i => f i.succ)
      rw [hst, hih, mul_smul_comm, smul_smul, ← pow_succ']
      congr 1
      exact (Fin.prod_univ_succ fun i => toE (f i)).symm
  -- Define formal polynomial vectors `V : Fin (p + 1) → Fin k → Polynomial A`
  let V : Fin (p + 1) → Fin k → Polynomial A := fun j m =>
    ∑ s : Fin (D + 1), Polynomial.monomial (s : ℕ) (MvPolynomial.X (j, m, s))
  have hV_deg : ∀ j m, (V j m).natDegree ≤ D := by
    intro j m
    refine (Polynomial.natDegree_sum_le _ _).trans (Finset.sup_le fun s _ => ?_)
    exact (Polynomial.natDegree_monomial_le _).trans (by omega)
  have hV_const : ∀ j m, Polynomial.map (MvPolynomial.constantCoeff : A →+* ℂ) (V j m) = 0 := by
    intro j m
    simp [V, Polynomial.map_sum, Polynomial.map_monomial]
  -- Define matrix entries `entry (i j : Fin p) : Fin k → Polynomial A`
  let bvec : Fin k → Polynomial A := fun m => liftC (bpoly m)
  let avec : Fin k → Polynomial A := fun m => liftC (apoly m)
  let qA : Polynomial A := liftC q
  let entry : Fin p → Fin p → (Fin k → Polynomial A) := fun i j =>
    if h : (j : ℕ) ≤ (i : ℕ) then
      fun m => qA ^ 2 * V ⟨(i : ℕ) - (j : ℕ), by omega⟩ m
    else
      star bvec (V ⟨p + (i : ℕ) - (j : ℕ), by omega⟩)
  have hentry_deg : ∀ i j m, (entry i j m).natDegree ≤ D + 2 * B0 := by
    intro i j m
    dsimp [entry]
    split_ifs with h
    · have h1 : (qA ^ 2 * V ⟨(i : ℕ) - (j : ℕ), by omega⟩ m).natDegree ≤
          (qA ^ 2).natDegree + (V ⟨(i : ℕ) - (j : ℕ), by omega⟩ m).natDegree :=
        Polynomial.natDegree_mul_le
      have h2 : (qA ^ 2).natDegree ≤ 2 * qA.natDegree := Polynomial.natDegree_pow_le
      have h3 : qA.natDegree ≤ B0 := Polynomial.natDegree_map_le.trans hq_deg
      have h4 := hV_deg ⟨(i : ℕ) - (j : ℕ), by omega⟩ m
      linarith
    · have hb_d : ∀ r, (bvec r).natDegree ≤ B0 :=
        fun r => Polynomial.natDegree_map_le.trans (hb_deg r)
      have h1 := hstar_deg bvec (V ⟨p + (i : ℕ) - (j : ℕ), by omega⟩) B0 D hb_d (hV_deg _) m
      omega
  have hentry_const : ∀ i j m,
      Polynomial.map (MvPolynomial.constantCoeff : A →+* ℂ) (entry i j m) = 0 := by
    intro i j m
    dsimp [entry]
    split_ifs with h
    · rw [Polynomial.map_mul, hV_const, mul_zero]
    · simp only [star, Polynomial.map_sum, Polynomial.map_mul, hV_const, mul_zero, Finset.sum_const_zero]
  -- Write `p = p' + 1` since `p` is prime
  obtain ⟨p', hp'⟩ : ∃ p', p = p' + 1 := Nat.exists_eq_add_one_of_ne_zero hp.ne_zero
  let fp : Fin (p' + 1) ≃ Fin p := finCongr hp'.symm
  -- Formal polynomial system `Q : Fin k → Polynomial A`
  let detPoly : Fin k → Polynomial A := fun m =>
    ∑ σ : Equiv.Perm (Fin p),
      ((Equiv.Perm.sign σ : ℤ) : Polynomial A) *
        foldStar star p' (fun i => entry (σ (fp i)) (fp i)) m
  let rhsPoly : Fin k → Polynomial A := fun m =>
    qA ^ (2 * p') * star avec (foldStar star p' (fun _ => V ⟨p, Nat.lt_succ_self p⟩)) m
  let Q : Fin k → Polynomial A := fun m => detPoly m - rhsPoly m
  have hQ_deg : ∀ m, (Q m).natDegree < p * D + B := by
    intro m
    have hdet : (detPoly m).natDegree ≤ p * D + (3 * p - 1) * B0 := by
      refine (Polynomial.natDegree_sum_le _ _).trans (Finset.sup_le fun σ _ => ?_)
      refine Polynomial.natDegree_mul_le.trans ?_
      have hsign : (((Equiv.Perm.sign σ : ℤ) : Polynomial A)).natDegree = 0 := by
        rw [← Polynomial.C_eq_intCast, Polynomial.natDegree_C]
      rw [hsign, zero_add]
      have h1 := hprodStar_deg p' (fun i => entry (σ (fp i)) (fp i)) (D + 2 * B0)
        (fun i r => hentry_deg _ _ r) m
      refine h1.trans ?_
      have h3p : 3 * p - 1 = 2 * p + p' := by omega
      rw [h3p, hp']
      nlinarith
    have hrhs' : (rhsPoly m).natDegree ≤ p * D + (3 * p - 1) * B0 := by
      refine Polynomial.natDegree_mul_le.trans ?_
      have h1 : (qA ^ (2 * p')).natDegree ≤ 2 * p' * B0 :=
        Polynomial.natDegree_pow_le.trans (Nat.mul_le_mul_left _
          (Polynomial.natDegree_map_le.trans hq_deg))
      have ha_d : ∀ r, (avec r).natDegree ≤ B0 :=
        fun r => Polynomial.natDegree_map_le.trans (ha_deg r)
      have hps := hprodStar_deg p' (fun _ => V ⟨p, Nat.lt_succ_self p⟩) D (fun _ r => hV_deg _ r)
      have h2 := hstar_deg avec (foldStar star p' (fun _ => V ⟨p, Nat.lt_succ_self p⟩)) B0
        ((p' + 1) * D + p' * B0) ha_d hps m
      have h3p : 3 * p - 1 = 3 * p' + 2 := by omega
      have hpeq : p = p' + 1 := hp'
      nlinarith
    have hsub := Polynomial.natDegree_sub_le (detPoly m) (rhsPoly m)
    have hmax : max (detPoly m).natDegree (rhsPoly m).natDegree ≤ p * D + (3 * p - 1) * B0 :=
      max_le hdet hrhs'
    have hlt : p * D + (3 * p - 1) * B0 < p * D + B := by
      dsimp only [B]
      have : (3 * p - 1) * B0 ≤ 3 * p * B0 := Nat.mul_le_mul_right B0 (Nat.sub_le _ _)
      omega
    exact lt_of_le_of_lt (hsub.trans hmax) hlt
  -- Constant term of `Q` vanishes
  have hprodStar_const : ∀ (n : ℕ) (f : Fin (n + 1) → (Fin k → Polynomial A)),
      (∀ i r, Polynomial.map (MvPolynomial.constantCoeff : A →+* ℂ) (f i r) = 0) →
      ∀ m, Polynomial.map (MvPolynomial.constantCoeff : A →+* ℂ) (foldStar star n f m) = 0 := by
    intro n
    induction n with
    | zero => intro f hf m; simpa [foldStar] using hf 0 m
    | succ n ih =>
      intro f hf m
      simp only [foldStar, star, Polynomial.map_sum, Polynomial.map_mul, hf 0, mul_zero, zero_mul,
        Finset.sum_const_zero]
  have hQ_const : ∀ m, Polynomial.map (MvPolynomial.constantCoeff : A →+* ℂ) (Q m) = 0 := by
    intro m
    simp only [Q, detPoly, rhsPoly, Polynomial.map_sub, Polynomial.map_sum, Polynomial.map_mul]
    have h1 : ∀ σ : Equiv.Perm (Fin p),
        Polynomial.map (MvPolynomial.constantCoeff : A →+* ℂ)
          (foldStar star p' (fun i => entry (σ (fp i)) (fp i)) m) = 0 :=
      fun σ => hprodStar_const p' _ (fun i r => hentry_const _ _ r) m
    have h2 : Polynomial.map (MvPolynomial.constantCoeff : A →+* ℂ)
        (star avec (foldStar star p' (fun _ => V ⟨p, Nat.lt_succ_self p⟩)) m) = 0 := by
      simp only [star, Polynomial.map_sum, Polynomial.map_mul,
        hprodStar_const p' _ (fun _ r => hV_const _ r), mul_zero, Finset.sum_const_zero]
    simp [h1, h2]
  -- Collect equations: coefficients `0 .. p * D + B - 1` of each `Q m`
  set M := p * D + B
  let eqs : Finset A :=
    (Finset.univ : Finset (Fin k × Fin M)).image fun mt => (Q mt.1).coeff (mt.2 : ℕ)
  have hcard : eqs.card < Fintype.card U := by
    refine lt_of_le_of_lt Finset.card_image_le ?_
    simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, U, M, D]
    have h1 : k * (p * B + B) = k * ((p + 1) * B) := by ring
    have h2 : (p + 1) * (k * (B + 1)) = k * ((p + 1) * B) + k * (p + 1) := by ring
    rw [h1, h2]
    have hpos : 0 < k * (p + 1) := Nat.mul_pos hk_pos (Nat.succ_pos p)
    omega
  have h0_eqs : ∀ f ∈ eqs, MvPolynomial.constantCoeff f = 0 := by
    intro f hf
    obtain ⟨mt, -, rfl⟩ := Finset.mem_image.mp hf
    have h := congrArg (fun P => P.coeff (mt.2 : ℕ)) (hQ_const mt.1)
    simpa [Polynomial.coeff_map] using h
  -- Apply `OMA.ZL.Artin2.exists_common_zero'`!
  obtain ⟨t, ht0, ht⟩ := OMA.ZL.Artin2.exists_common_zero' (k := ℂ) eqs hcard h0_eqs
  -- Evaluate at `t`
  set ev : Polynomial A →+* RatFunc ℂ :=
    (algebraMap (Polynomial ℂ) (RatFunc ℂ)).comp (Polynomial.mapRingHom (MvPolynomial.eval t))
  set toE : (Fin k → Polynomial A) → E := fun u => ∑ m : Fin k, ev (u m) • pb.basis m
  have hev_lift : ∀ f : Polynomial ℂ, ev (liftC f) = algebraMap (Polynomial ℂ) (RatFunc ℂ) f := by
    intro f
    simp only [ev, liftC, RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_map]
    have : (MvPolynomial.eval t).comp MvPolynomial.C = RingHom.id ℂ := by ext; simp
    rw [this, Polynomial.map_id]
  have hQ_eval : ∀ m, ev (Q m) = 0 := by
    intro m
    have hmap0 : Polynomial.map (MvPolynomial.eval t) (Q m) = 0 := by
      ext n
      rw [Polynomial.coeff_map, Polynomial.coeff_zero]
      by_cases hn : n < M
      · exact ht _ (Finset.mem_image.mpr ⟨(m, ⟨n, hn⟩), Finset.mem_univ _, rfl⟩)
      · have hlt := hQ_deg m
        rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), map_zero]
    simp [ev, hmap0]
  have htoE_Q : toE Q = 0 := by
    simp [toE, hQ_eval]
  -- Compute `toE detPoly` and `toE rhsPoly`
  set c : Fin p → E := fun j => toE (V ⟨j.1, by omega⟩)
  set w : E := toE (V ⟨p, Nat.lt_succ_self p⟩)
  have htoE_a : toE avec = algebraMap (Polynomial ℂ) (RatFunc ℂ) q • (a : E) := by
    simp only [toE, avec, hev_lift, hapoly, mul_smul, ← Finset.smul_sum]
    congr 1
    exact pb.basis.sum_repr (a : E)
  have htoE_b : toE bvec = algebraMap (Polynomial ℂ) (RatFunc ℂ) q • (b : E) := by
    simp only [toE, bvec, hev_lift, hbpoly, mul_smul, ← Finset.smul_sum]
    congr 1
    exact pb.basis.sum_repr (b : E)
  have htoE_star : ∀ v w, toE (star v w) = algebraMap (Polynomial ℂ) (RatFunc ℂ) q • (toE v * toE w) :=
    hstar_eval t
  have htoE_fold : ∀ (n : ℕ) (f : Fin (n + 1) → (Fin k → Polynomial A)),
      toE (foldStar star n f) =
        (algebraMap (Polynomial ℂ) (RatFunc ℂ) q) ^ n • ∏ i : Fin (n + 1), toE (f i) :=
    hprodStar_eval t
  have htoE_entry : ∀ i j : Fin p,
      toE (entry i j) = (algebraMap (Polynomial ℂ) (RatFunc ℂ) q) ^ 2 •
        (if h : (j : ℕ) ≤ (i : ℕ) then c ⟨(i : ℕ) - (j : ℕ), by omega⟩
         else (b : E) * c ⟨p + (i : ℕ) - (j : ℕ), by omega⟩) := by
    intro i j
    dsimp [entry]
    split_ifs with h
    · simp only [toE, qA, map_mul, map_pow, hev_lift, mul_smul, ← Finset.smul_sum]; rfl
    · rw [htoE_star, htoE_b, smul_mul_assoc, smul_smul, ← sq]
  set qF : RatFunc ℂ := algebraMap (Polynomial ℂ) (RatFunc ℂ) q
  have hqF0 : qF ≠ 0 := (map_ne_zero_iff _ hinj).mpr hq0
  have htoE_det : toE detPoly =
      (qF ^ (p' + 2 * p)) •
        Matrix.det (Matrix.of fun i j : Fin p =>
          if h : (j : ℕ) ≤ (i : ℕ) then c ⟨(i : ℕ) - (j : ℕ), by omega⟩
          else (b : E) * c ⟨p + (i : ℕ) - (j : ℕ), by omega⟩) := by
    rw [Matrix.det_apply]
    simp only [toE, detPoly, map_sum, map_mul, map_intCast, Finset.sum_smul]
    rw [Finset.sum_comm]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    have h1 : ∑ m : Fin k, (((Equiv.Perm.sign σ : ℤ) : RatFunc ℂ) *
          ev (foldStar star p' (fun i => entry (σ (fp i)) (fp i)) m)) • pb.basis m =
        ((Equiv.Perm.sign σ : ℤ) : RatFunc ℂ) •
          toE (foldStar star p' (fun i => entry (σ (fp i)) (fp i))) := by
      simp only [toE, Finset.smul_sum, mul_smul]
    rw [h1, htoE_fold]
    simp_rw [htoE_entry]
    have hprod_smul : ∏ i : Fin (p' + 1),
        (qF ^ 2 • (if h : ((fp i : Fin p) : ℕ) ≤ ((σ (fp i) : Fin p) : ℕ) then
            c ⟨((σ (fp i) : Fin p) : ℕ) - ((fp i : Fin p) : ℕ), by omega⟩
          else (b : E) * c ⟨p + ((σ (fp i) : Fin p) : ℕ) - ((fp i : Fin p) : ℕ), by omega⟩)) =
        (qF ^ (2 * p)) • ∏ i : Fin p,
          (if h : (i : ℕ) ≤ ((σ i : Fin p) : ℕ) then
              c ⟨((σ i : Fin p) : ℕ) - (i : ℕ), by omega⟩
            else (b : E) * c ⟨p + ((σ i : Fin p) : ℕ) - (i : ℕ), by omega⟩) := by
      rw [Finset.prod_smul, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul,
        show 2 * (p' + 1) = 2 * p by omega]
      congr 1
      exact Fintype.prod_equiv fp _ _ (fun _ => rfl)
    rw [hprod_smul, smul_smul, smul_smul,
      show ((Equiv.Perm.sign σ : ℤ) : RatFunc ℂ) * qF ^ p' * qF ^ (2 * p) =
        qF ^ (p' + 2 * p) * ((Equiv.Perm.sign σ : ℤ) : RatFunc ℂ) by rw [pow_add]; ring,
      ← smul_smul, Int.cast_smul_eq_zsmul]
    rfl
  have htoE_rhs : toE rhsPoly = (qF ^ (p' + 2 * p)) • ((a : E) * w ^ p) := by
    have h1 : toE rhsPoly = (qF ^ (2 * p')) • toE (star avec (foldStar star p' (fun _ => V ⟨p, Nat.lt_succ_self p⟩))) := by
      simp only [toE, rhsPoly, qA, qF, map_mul, map_pow, hev_lift, mul_smul, ← Finset.smul_sum]
    rw [h1, htoE_star, htoE_a, htoE_fold, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, ← hp']
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
    congr 1
    rw [show p' + 2 * p = 2 * p' + 1 + p' + 1 by omega]
    ring
  have htoE_sub : toE Q = toE detPoly - toE rhsPoly := by
    simp only [toE, Q, map_sub, sub_smul, Finset.sum_sub_distrib]
  rw [htoE_sub, htoE_det, htoE_rhs, ← smul_sub] at htoE_Q
  have hnorm_eq : Matrix.det (Matrix.of fun i j : Fin p =>
      if h : (j : ℕ) ≤ (i : ℕ) then c ⟨(i : ℕ) - (j : ℕ), by omega⟩
      else (b : E) * c ⟨p + (i : ℕ) - (j : ℕ), by omega⟩) = (a : E) * w ^ p := by
    have hqpow : qF ^ (p' + 2 * p) ≠ 0 := pow_ne_zero _ hqF0
    have h0 := (smul_eq_zero.mp htoE_Q).resolve_left hqpow
    exact sub_eq_zero.mp h0
  -- Not all `(c, w)` are zero since `t ≠ 0`
  have hcw_nz : (∃ j : Fin p, c j ≠ 0) ∨ w ≠ 0 := by
    obtain ⟨⟨j, m, s⟩, htu⟩ := Function.ne_iff.mp ht0
    have hVj : toE (V j) ≠ 0 := by
      intro h0
      apply htu
      have hcoord : ev (V j m) = 0 := by
        have := congrArg (fun x => pb.basis.repr x m) h0
        simp only [toE, map_sum, map_smul, Module.Basis.repr_self, Finsupp.smul_apply,
          Finsupp.single_apply, Finset.sum_apply', smul_eq_mul, mul_ite, mul_one, mul_zero,
          Finset.sum_ite_eq', Finset.mem_univ, ite_true, map_zero, Finsupp.zero_apply] at this
        exact this
      have hpoly0 : Polynomial.map (MvPolynomial.eval t) (V j m) = 0 :=
        (map_eq_zero_iff _ hinj).mp hcoord
      have hcoeff : (Polynomial.map (MvPolynomial.eval t) (V j m)).coeff (s : ℕ) = t (j, m, s) := by
        simp only [V, Polynomial.map_sum, Polynomial.map_monomial, MvPolynomial.eval_X,
          Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
        rw [Finset.sum_eq_single s]
        · simp
        · intro s' _ hne
          rw [if_neg (fun h => hne (Fin.ext h))]
        · intro h; exact absurd (Finset.mem_univ s) h
      rw [← hcoeff, hpoly0, Polynomial.coeff_zero]
      rfl
    by_cases hjp : (j : ℕ) < p
    · exact Or.inl ⟨⟨j.1, hjp⟩, hVj⟩
    · have hjlt := j.isLt
      have hjeq : j = ⟨p, Nat.lt_succ_self p⟩ := Fin.ext (by change (j : ℕ) = p; omega)
      exact Or.inr (by simpa [w, ← hjeq] using hVj)
  exact tsen_norm_from_det hp a b hirr c w hnorm_eq hcw_nz

/-- For every monic irreducible `π` over `RatFunc ℂ` and odd prime `p`,
`K_2^M(AdjoinRoot π.poly) / p = 0`. -/
theorem grade_two_adjoinRoot_eq_bot {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (π : MonicIrred (RatFunc ℂ)) :
    letI : Fact (Irreducible π.poly) := ⟨π.irred⟩
    MilnorK.grade (AdjoinRoot π.poly) p 2 = ⊥ := by
  letI : Fact (Irreducible π.poly) := ⟨π.irred⟩
  set E := AdjoinRoot π.poly
  letI : Algebra ℂ E := RingHom.toAlgebra ((algebraMap (RatFunc ℂ) E).comp
    ((algebraMap (Polynomial ℂ) (RatFunc ℂ)).comp Polynomial.C))
  haveI : CharZero E :=
    charZero_of_injective_algebraMap (algebraMap ℂ E).injective
  rw [eq_bot_iff, MilnorK.grade, AddSubgroup.closure_le]
  rintro _ ⟨s, rfl⟩
  rw [SetLike.mem_coe, AddSubgroup.mem_bot, symbol_succ, symbol_one]
  set b := s 0
  set a := s 1
  by_cases hirr : Irreducible (X ^ p - C (b : E))
  · obtain ⟨z, hz⟩ := tsen_norm_surj hp π a b hirr
    letI : Fact (Irreducible (X ^ p - C (b : E))) := ⟨hirr⟩
    have hvan := of_mul_norm_eq_zero (E := E) hp hp2 b hirr z
    have hu : Units.map (Algebra.norm E : AdjoinRoot (X ^ p - C (b : E)) →* E) z = a :=
      Units.ext hz
    rwa [hu] at hvan
  · obtain ⟨c, hc⟩ := exists_pow_p_of_not_irreducible hp b hirr
    rw [← hc, of_pow_p, zero_mul]

/-- Ring isomorphism `MvRatFunc (Fin 1) ℂ ≃+* RatFunc ℂ`. -/
noncomputable def mvRatFuncFin1Equiv : MvRatFunc (Fin 1) ℂ ≃+* RatFunc ℂ :=
  let ePoly : MvPolynomial (Fin 1) ℂ ≃+* Polynomial ℂ :=
    (MvPolynomial.finSuccEquiv ℂ 0).toRingEquiv.trans
      (Polynomial.mapEquiv (MvPolynomial.isEmptyRingEquiv ℂ (Fin 0)))
  IsFractionRing.ringEquivOfRingEquiv ePoly

/-- Ring isomorphism `MvRatFunc (Fin 2) ℂ ≃+* RatFunc (RatFunc ℂ)`. -/
noncomputable def mvRatFuncFin2Equiv : MvRatFunc (Fin 2) ℂ ≃+* RatFunc (RatFunc ℂ) := by
  let e1 : MvPolynomial (Fin 2) ℂ ≃+* Polynomial (MvPolynomial (Fin 1) ℂ) :=
    (MvPolynomial.finSuccEquiv ℂ 1).toRingEquiv
  let e1' : MvPolynomial (Fin 1) ℂ ≃+* Polynomial ℂ :=
    (MvPolynomial.finSuccEquiv ℂ 0).toRingEquiv.trans
      (Polynomial.mapEquiv (MvPolynomial.isEmptyRingEquiv ℂ (Fin 0)))
  let ePoly : MvPolynomial (Fin 2) ℂ ≃+* Polynomial (Polynomial ℂ) :=
    e1.trans (Polynomial.mapEquiv e1')
  -- Compose `ePoly` with `Polynomial.mapRingHom (algebraMap (Polynomial ℂ) (RatFunc ℂ))`
  let ι : Polynomial (Polynomial ℂ) →+* Polynomial (RatFunc ℂ) :=
    Polynomial.mapRingHom (algebraMap (Polynomial ℂ) (RatFunc ℂ))
  let φ : MvPolynomial (Fin 2) ℂ →+* RatFunc (RatFunc ℂ) :=
    (algebraMap (Polynomial (RatFunc ℂ)) (RatFunc (RatFunc ℂ))).comp (ι.comp ePoly.toRingHom)
  have hφ_inj : Function.Injective φ := by
    have h1 : Function.Injective (algebraMap (Polynomial (RatFunc ℂ)) (RatFunc (RatFunc ℂ))) :=
      IsFractionRing.injective _ _
    have h2 : Function.Injective ι :=
      Polynomial.map_injective _ (IsFractionRing.injective (Polynomial ℂ) (RatFunc ℂ))
    exact h1.comp (h2.comp ePoly.injective)
  let fwd : MvRatFunc (Fin 2) ℂ →+* RatFunc (RatFunc ℂ) :=
    IsFractionRing.lift hφ_inj
  have hfwd_inj : Function.Injective fwd := fwd.injective
  have hfwd_surj : Function.Surjective fwd := by
    intro y
    -- Write `y = P / Q` with `P, Q ∈ Polynomial (RatFunc ℂ)`, `Q ≠ 0`, and clear denominators in `Polynomial ℂ`
    have hclear : ∀ P : Polynomial (RatFunc ℂ), ∃ (d : Polynomial ℂ) (P' : Polynomial (Polynomial ℂ)),
        d ≠ 0 ∧ ι P' = Polynomial.C (algebraMap (Polynomial ℂ) (RatFunc ℂ) d) * P := by
      intro P
      set d : Polynomial ℂ := ∏ i ∈ P.support, (P.coeff i).denom
      have hd0 : d ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => RatFunc.denom_ne_zero _
      have hinj1 := IsFractionRing.injective (Polynomial ℂ) (RatFunc ℂ)
      let P' : Polynomial (Polynomial ℂ) :=
        ∑ i ∈ P.support, Polynomial.monomial i
          ((P.coeff i).num * ∏ j ∈ P.support.erase i, (P.coeff j).denom)
      refine ⟨d, P', hd0, ?_⟩
      ext n
      simp only [ι, Polynomial.coe_mapRingHom, Polynomial.coeff_map, Polynomial.coeff_C_mul]
      simp only [P', Polynomial.finset_sum_coeff, Polynomial.coeff_monomial, map_sum]
      by_cases hn : n ∈ P.support
      · rw [Finset.sum_eq_single n]
        · simp only [ite_true]
          have hd_split : d = (P.coeff n).denom * ∏ j ∈ P.support.erase n, (P.coeff j).denom :=
            (Finset.mul_prod_erase P.support (fun j => (P.coeff j).denom) hn).symm
          have hdn : algebraMap (Polynomial ℂ) (RatFunc ℂ) (P.coeff n).denom ≠ 0 :=
            (map_ne_zero_iff _ hinj1).mpr (RatFunc.denom_ne_zero _)
          have hxnd : algebraMap (Polynomial ℂ) (RatFunc ℂ) (P.coeff n).denom * P.coeff n =
              algebraMap (Polynomial ℂ) (RatFunc ℂ) (P.coeff n).num := by
            have h1 := RatFunc.num_div_denom (P.coeff n)
            rw [div_eq_iff hdn] at h1
            rw [mul_comm, h1]
          rw [hd_split, map_mul, map_mul]
          calc algebraMap (Polynomial ℂ) (RatFunc ℂ) (P.coeff n).num *
                algebraMap _ _ (∏ j ∈ P.support.erase n, (P.coeff j).denom)
              = (algebraMap _ _ (P.coeff n).denom * P.coeff n) *
                algebraMap _ _ (∏ j ∈ P.support.erase n, (P.coeff j).denom) := by rw [hxnd]
            _ = algebraMap _ _ (P.coeff n).denom *
                algebraMap _ _ (∏ j ∈ P.support.erase n, (P.coeff j).denom) * P.coeff n := by ring
        · intro i _ hne; rw [if_neg hne, map_zero]
        · intro h; exact absurd hn h
      · rw [Polynomial.notMem_support_iff.mp hn, mul_zero]
        refine Finset.sum_eq_zero fun i hi => ?_
        rw [if_neg (fun (h : i = n) => hn (h ▸ hi)), map_zero]
    obtain ⟨d1, P', hd1, hP'⟩ := hclear y.num
    obtain ⟨d2, Q', hd2, hQ'⟩ := hclear y.denom
    have hQ0 : y.denom ≠ 0 := RatFunc.denom_ne_zero y
    set numP : Polynomial (Polynomial ℂ) := Polynomial.C d2 * P'
    set denP : Polynomial (Polynomial ℂ) := Polynomial.C d1 * Q'
    have hden0 : denP ≠ 0 := by
      intro h0
      have h1 := congrArg ι h0
      rw [map_zero, show denP = Polynomial.C d1 * Q' from rfl, map_mul,
        show ι (Polynomial.C d1) = Polynomial.C (algebraMap (Polynomial ℂ) (RatFunc ℂ) d1) from
          Polynomial.map_C _, hQ', ← mul_assoc, ← map_mul] at h1
      have hprod0 : algebraMap (Polynomial ℂ) (RatFunc ℂ) d1 *
          algebraMap (Polynomial ℂ) (RatFunc ℂ) d2 ≠ 0 := by
        rw [← map_mul]
        exact (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr (mul_ne_zero hd1 hd2)
      have hC0 : Polynomial.C (algebraMap (Polynomial ℂ) (RatFunc ℂ) d1 *
          algebraMap (Polynomial ℂ) (RatFunc ℂ) d2) ≠ 0 := Polynomial.C_ne_zero.mpr hprod0
      exact (mul_eq_zero.mp h1).elim hC0 hQ0
    set a := ePoly.symm numP
    set b := ePoly.symm denP
    have hb0 : algebraMap (MvPolynomial (Fin 2) ℂ) (MvRatFunc (Fin 2) ℂ) b ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr (by
        intro h; apply hden0; simpa [b] using congrArg ePoly h)
    refine ⟨algebraMap _ (MvRatFunc (Fin 2) ℂ) a / algebraMap _ (MvRatFunc (Fin 2) ℂ) b, ?_⟩
    rw [map_div₀]
    have hfa : fwd (algebraMap _ (MvRatFunc (Fin 2) ℂ) a) = φ a := IsFractionRing.lift_algebraMap _ _
    have hfb : fwd (algebraMap _ (MvRatFunc (Fin 2) ℂ) b) = φ b := IsFractionRing.lift_algebraMap _ _
    rw [hfa, hfb]
    simp only [φ, RingHom.comp_apply, a, b, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      RingEquiv.apply_symm_apply, numP, denP, map_mul]
    have hC1 : ι (Polynomial.C d1) = Polynomial.C (algebraMap (Polynomial ℂ) (RatFunc ℂ) d1) :=
      Polynomial.map_C _
    have hC2 : ι (Polynomial.C d2) = Polynomial.C (algebraMap (Polynomial ℂ) (RatFunc ℂ) d2) :=
      Polynomial.map_C _
    simp only [hC1, hC2, hP', hQ', map_mul]
    conv_rhs => rw [← RatFunc.num_div_denom y]
    have h1 : algebraMap (Polynomial (RatFunc ℂ)) (RatFunc (RatFunc ℂ))
        (Polynomial.C (algebraMap (Polynomial ℂ) (RatFunc ℂ) d1)) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr
        (Polynomial.C_ne_zero.mpr ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hd1))
    have h2 : algebraMap (Polynomial (RatFunc ℂ)) (RatFunc (RatFunc ℂ))
        (Polynomial.C (algebraMap (Polynomial ℂ) (RatFunc ℂ) d2)) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr
        (Polynomial.C_ne_zero.mpr ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hd2))
    have h3 : algebraMap (Polynomial (RatFunc ℂ)) (RatFunc (RatFunc ℂ)) y.denom ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hQ0
    field_simp
  exact RingEquiv.ofBijective fwd ⟨hfwd_inj, hfwd_surj⟩

/-- `K_3^M(RatFunc (RatFunc ℂ)) / p = 0` for every odd prime `p`. -/
theorem grade_three_ratFunc_ratFunc_eq_bot {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    grade (RatFunc (RatFunc ℂ)) p 3 = ⊥ := by
  have hgrade2_C : grade (RatFunc ℂ) p 2 = ⊥ :=
    grade_eq_bot_of_ringEquiv p 2 mvRatFuncFin1Equiv.symm
      (OMA.ZL.One.grade_two_one_var p hp.pos)
  rw [eq_bot_iff]
  intro x hx
  have hvan : ∀ π : MonicIrred (RatFunc ℂ),
      letI : Fact (Irreducible π.poly) := ⟨π.irred⟩
      (valPiData π).partialHom hp hp2 x = 0 := by
    intro π
    letI : Fact (Irreducible π.poly) := ⟨π.irred⟩
    have hmem : (valPiData π).partialHom hp hp2 x ∈ grade (AdjoinRoot π.poly) p 2 :=
      (valPiData π).partialHom_grade_succ hp hp2 2 hx
    rw [grade_two_adjoinRoot_eq_bot hp hp2 π, AddSubgroup.mem_bot] at hmem
    exact hmem
  have hxL0 : x ∈ Lfilt (RatFunc ℂ) p 0 := milnor_grade3_ker hp hp2 hx hvan
  have hL0_bot : Lfilt (RatFunc ℂ) p 0 = ⊥ := by
    rw [eq_bot_iff, Lfilt, AddSubgroup.closure_le]
    rintro _ ⟨f₁, f₂, f₃, h₁, h₂, h₃, hd₁, hd₂, hd₃, rfl⟩
    rw [SetLike.mem_coe, AddSubgroup.mem_bot]
    have h01 : f₁.natDegree = 0 := by omega
    have h02 : f₂.natDegree = 0 := by omega
    have hf1 : f₁ = C (f₁.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero h01
    have hf2 : f₂ = C (f₂.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero h02
    have hc1 : f₁.coeff 0 ≠ 0 := fun h => h₁ (by rw [hf1, h, map_zero])
    have hc2 : f₂.coeff 0 ≠ 0 := fun h => h₂ (by rw [hf2, h, map_zero])
    set ιF : RatFunc ℂ →+* RatFunc (RatFunc ℂ) :=
      (algebraMap (Polynomial (RatFunc ℂ)) (RatFunc (RatFunc ℂ))).comp Polynomial.C
    have hu1 : polyUnit f₁ h₁ = Units.map ιF.toMonoidHom (Units.mk0 (f₁.coeff 0) hc1) := by
      apply Units.ext
      change algebraMap (Polynomial (RatFunc ℂ)) (RatFunc (RatFunc ℂ)) f₁ =
        algebraMap _ _ (C (f₁.coeff 0))
      exact congrArg _ hf1
    have hu2 : polyUnit f₂ h₂ = Units.map ιF.toMonoidHom (Units.mk0 (f₂.coeff 0) hc2) := by
      apply Units.ext
      change algebraMap (Polynomial (RatFunc ℂ)) (RatFunc (RatFunc ℂ)) f₂ =
        algebraMap _ _ (C (f₂.coeff 0))
      exact congrArg _ hf2
    have hprod0 : of p (Units.mk0 (f₁.coeff 0) hc1) * of p (Units.mk0 (f₂.coeff 0) hc2) = 0 := by
      have hmem : of p (Units.mk0 (f₁.coeff 0) hc1) * of p (Units.mk0 (f₂.coeff 0) hc2) ∈
          grade (RatFunc ℂ) p 2 := by
        rw [← symbol_pair]
        exact symbol_mem_grade _ _ _
      rwa [hgrade2_C, AddSubgroup.mem_bot] at hmem
    have hmap := congrArg (mapRingHom p ιF) hprod0
    rw [map_mul, mapRingHom_of, mapRingHom_of, map_zero] at hmap
    rw [hu1, hu2, hmap, zero_mul]
  rwa [hL0_bot] at hxL0

end TsenAndFinal

end OMA.H1Proof

theorem OMA.solution :
    OMA.R_SymbolLengthMilnorKTheory_symbol_length_problem_variants_zero_mem_of_lt_R1.H1 := by
  intro p hp hp2
  rw [MilnorK.zero_mem_symbolLengthBounds_iff]
  exact OMA.H1Proof.grade_eq_bot_of_ringEquiv p 3 OMA.H1Proof.mvRatFuncFin2Equiv
    (OMA.H1Proof.grade_three_ratFunc_ratFunc_eq_bot hp hp2)
